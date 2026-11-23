/* Loop-local derived addresses. Inputs must be private or actual array objects;
 * indirect stores therefore cannot change a cached base or invariant index.
 * Plans use expression identity, so independent side effects are never merged. */
static int affine_dependency(AffineLoop *loop, Symbol *symbol)
{
    unsigned i;

    if (!symbol->type.array &&
        (symbol->owner != cg.function->id || loop_escapes(cg.function->body, symbol)))
        return 0;

    for (i = 0; i < loop->dependency_count; ++i) {
        if (loop->dependencies[i] == symbol)
            return 1;
    }

    if (i == 32) {
        return 0;
    }

    loop->dependencies[loop->dependency_count++] = symbol;
    return 1;
}

static int affine_scalar(AffineLoop *loop, Expr *e, int *coefficient)
{
    int left, right;
    uint32_t factor;

    *coefficient = 0;
    if (!numeric(e->type) || e->type.base == TY_FLOAT || value_width(e->type) != 2)
        return 0;
    if (e->kind == EX_INT)
        return 1;
    if (e->kind == EX_OBJECT) {
        if (!affine_dependency(loop, e->symbol))
            return 0;

        *coefficient = e->symbol == loop->index;
        return 1;
    }

    /* Word signedness does not affect a near address computed modulo 65536 */
    if (e->kind == EX_CAST &&
        (same_value_representation(e->type, e->left->type) ||
         (e->type.base == TY_INT && e->left->type.base == TY_INT && !e->left->type.pointers &&
          !e->type.is_bool && !e->left->type.is_bool)))
        return affine_scalar(loop, e->left, coefficient);
    if (e->kind != EX_BINARY)
        return 0;

    if (e->op == '+' || e->op == '-') {
        if (!affine_scalar(loop, e->left, &left) || !affine_scalar(loop, e->right, &right))
            return 0;

        *coefficient =
            (int)(((unsigned)left + (e->op == '+' ? (unsigned)right : 0u - (unsigned)right)) &
                  65535);
        return 1;
    }

    if (e->op == '*' && integer_constant(e->left, &factor) &&
        affine_scalar(loop, e->right, &left)) {
        *coefficient = (int)(((unsigned)left * factor) & 65535);
        return 1;
    }
    if (((e->op == '*' && integer_constant(e->right, &factor)) ||
         word_left_shift_factor(e, &factor)) &&
        affine_scalar(loop, e->left, &left)) {
        *coefficient = (int)(((unsigned)left * factor) & 65535);
        return 1;
    }

    return 0;
}

static int affine_address(AffineLoop *loop, Expr *e, unsigned *stride, unsigned *levels)
{
    if (far_pointer(value_type(e->type)))
        return 0;

    int coefficient;

    unsigned scale;

    if (e->kind == EX_OBJECT && (e->type.array || e->type.pointers))
        return affine_dependency(loop, e->symbol);
    if (e->kind == EX_DEREF && e->type.array) {
        /* A direct row dereference uses offset zero */
        if (e->left->kind == EX_OBJECT && e->left->type.pointers)
            ++*levels;

        return affine_address(loop, e->left, stride, levels);
    }
    if (e->kind != EX_BINARY || (e->op != '+' && e->op != '-') ||
        !value_type(e->left->type).pointers || !affine_address(loop, e->left, stride, levels) ||
        !affine_scalar(loop, e->right, &coefficient))
        return 0;

    scale = width(pointed_type(value_type(e->left->type)));

    if (!scale || scale > 65534)
        return 0;

    *stride = (*stride + (e->op == '+' ? scale : 0u - scale) * (unsigned)coefficient) & 65535;
    if (!(e->left->kind != EX_DEREF && !pointed_type(value_type(e->left->type)).array &&
          e->right->kind == EX_INT))
        ++*levels;

    return 1;
}

static int affine_accesses(AffineLoop *loop, Expr *e)
{
    unsigned i, stride = 0, levels = 0;

    if (!e)
        return 1;
    if (e->kind == EX_CALL)
        return 0;

    if (e->kind == EX_DEREF && !e->type.array) {
        AffineLoop trial = *loop;

        if (affine_address(&trial, e->left, &stride, &levels) && stride && levels >= 2) {
            if (loop->count == 8)
                return 0;

            *loop = trial;
            loop->accesses[loop->count].address = e->left;
            loop->accesses[loop->count++].stride = (stride * (unsigned)loop->delta) & 65535;
            return 1;
        }
    }

    if (!affine_accesses(loop, e->left) || !affine_accesses(loop, e->right) ||
        !affine_accesses(loop, e->third))
        return 0;

    for (i = 0; i < e->arg_count; ++i) {
        if (!affine_accesses(loop, e->args[i]))
            return 0;
    }

    return 1;
}

static int affine_body(AffineLoop *loop, Statement *s)
{
    for (; s; s = s->next) {
        if (s->kind == ST_FOR || s->kind == ST_WHILE || s->kind == ST_DO || s->kind == ST_RETURN ||
            s->kind == ST_SWITCH || s->kind == ST_CASE)
            return 0;
        if (!affine_accesses(loop, s->expression) || !affine_body(loop, s->body) ||
            !affine_body(loop, s->alternate))
            return 0;
    }

    return 1;
}

static int affine_modified_expr(Expr *e, Symbol *symbol)
{
    if (!e)
        return 0;
    if (e->kind == EX_CALL)
        return 1;
    if ((e->kind == EX_ASSIGN || e->kind == EX_PRE || e->kind == EX_POST) &&
        e->left->kind == EX_OBJECT && e->left->symbol == symbol)
        return 1;

    return affine_modified_expr(e->left, symbol) || affine_modified_expr(e->right, symbol) ||
           affine_modified_expr(e->third, symbol);
}

static int affine_modified(Statement *s, Symbol *symbol)
{
    for (; s; s = s->next) {
        if (affine_modified_expr(s->expression, symbol) || affine_modified_expr(s->step, symbol) ||
            affine_modified(s->body, symbol) || affine_modified(s->alternate, symbol))
            return 1;
    }

    return 0;
}

/* Two constant stores at the same affine stride keep their near cursors.
 * The unsigned entry test establishes an exact, nonwrapping trip count. */
static int affine_pair_loop(Statement *s)
{
    AffineLoop plan = {0};
    Statement *body = s->body, *tail;
    Expr *test = s->expression, *step = s->step, *first, *second;

    unsigned strides[2] = {0, 0}, levels = 0, start, done;
    int coefficient;
    uint32_t value, other;
    Type compare;

    if (s->kind != ST_FOR || cg.parser->no_strength_reduction || cg.parser->no_register_loops ||
        cg.switch_depth || cg.function->jump_label_count || cg.stack_leaf || cg.scalar_leaf ||
        cg.scalar_first || cg.leaf_count || cg.retained_index || bound_state.cursor ||
        bound_state.pending || cg.affine_active || cg.scan_cursor || cg.dead_index_count ||
        cg.omitted_parameter_count || cg.function->symbol->interrupt || !test ||
        test->kind != EX_BINARY || test->op != '<' || test->left->kind != EX_OBJECT || !step ||
        (step->kind != EX_PRE && step->kind != EX_POST) || step->op != TOK_INC ||
        step->left->kind != EX_OBJECT || step->left->symbol != test->left->symbol ||
        volatile_statement(s))
        return 0;

    compare = common_type(test->left->type, test->right->type);
    plan.index = test->left->symbol;

    if (compare.base != TY_INT || compare.pointers || !compare.is_unsigned ||
        plan.index->type.base != TY_INT || plan.index->type.pointers || plan.index->type.is_bool ||
        !loop_private(plan.index) || loop_observed_outside(cg.function->body, s, plan.index) ||
        loop_mentions(test->right, plan.index) || !affine_scalar(&plan, test->right, &coefficient))
        return 0;
    if (body && body->kind == ST_BLOCK && !body->inline_callee)
        body = body->body;

    tail = body ? body->next : NULL;

    if (!tail || tail->next || body->kind != ST_EXPR || tail->kind != ST_EXPR)
        return 0;

    first = body->expression;
    second = tail->expression;

    if (first->kind != EX_ASSIGN || second->kind != EX_ASSIGN || first->op || second->op ||
        first->left->kind != EX_DEREF || second->left->kind != EX_DEREF ||
        first->left->type.base != TY_INT || second->left->type.base != TY_INT ||
        first->left->type.pointers || second->left->type.pointers || first->left->type.is_bool ||
        second->left->type.is_bool || !integer_constant(first->right, &value) ||
        !integer_constant(second->right, &other) || (uint16_t)value != (uint16_t)other ||
        !affine_address(&plan, first->left->left, &strides[0], &levels) ||
        !affine_address(&plan, second->left->left, &strides[1], &levels) || !strides[0] ||
        strides[0] != strides[1])
        return 0;

    start = ++cg.label;
    done = ++cg.label;
    code("; paired affine word stores: shared byte stride %u\n", strides[0]);
    emit_value(test->right);
    code("    sec\n    sbc ");
    array_operand(plan.index, 0);
    code("\n    bcc cg_%s_%u\n    beq cg_%s_%u\n    pha\n", cg.parser->unit, done, cg.parser->unit,
         done);
    emit_value(first->left->left);
    code("    pha\n");
    emit_value(second->left->left);
    code("    tax\n    pla\n    sta z:__arith_lhs\n"
         "    pla\n    sta z:__arith_lhs+2\n    phy\n    ldy z:__arith_lhs\n");

    if (strides[0] == 2)
        code("    lda #$%04X\n", value & 65535);

    label(start);

    if (strides[0] != 2)
        code("    lda #$%04X\n", value & 65535);

    code("    sta a:$0000,y\n    sta a:$0000,x\n");

    if (strides[0] == 2)
        code("    iny\n    iny\n    inx\n    inx\n");
    else
        code("    tya\n    clc\n    adc #$%04X\n    tay\n"
             "    txa\n    clc\n    adc #$%04X\n    tax\n",
             strides[0], strides[0]);

    code("    dec z:__arith_lhs+2\n    bne cg_%s_%u\n    ply\n", cg.parser->unit, start);
    label(done);
    divmod_state.available = 0;
    return 1;
}

static int affine_condition(Expr *e)
{
    if (!e)
        return 0;
    if (e->kind == EX_OBJECT || e->kind == EX_INT)
        return numeric(e->type) && e->type.base != TY_FLOAT && value_width(e->type) == 2;
    if (e->kind == EX_BINARY)
        return affine_condition(e->left) && affine_condition(e->right);

    return 0;
}

static int affine_plan(Statement *s, AffineLoop *loop)
{
    Expr *step = s->step;

    unsigned i;
    uint32_t delta;

    memset(loop, 0, sizeof *loop);
    loop->statement = s;

    if (volatile_statement(s) || s->kind != ST_FOR || !step || !affine_condition(s->expression))
        return 0;

    if (step->kind == EX_PRE || step->kind == EX_POST)
        loop->delta = step->op == TOK_INC ? 1 : -1;
    else if (step->kind == EX_ASSIGN && (step->op == '+' || step->op == '-') &&
             integer_constant(step->right, &delta) && delta && delta <= 32767)
        loop->delta = step->op == '+' ? (int)delta : -(int)delta;
    else
        return 0;

    if (step->left->kind != EX_OBJECT)
        return 0;

    loop->index = step->left->symbol;

    if (!numeric(loop->index->type) || loop->index->type.base != TY_INT ||
        !affine_dependency(loop, loop->index) || !affine_body(loop, s->body) || !loop->count)
        return 0;

    for (i = 0; i < loop->dependency_count; ++i) {
        if (affine_modified(s->body, loop->dependencies[i]))
            return 0;
    }

    return 1;
}

static Expr *affine_register_assignment(AffineLoop *loop)
{
    Statement *body = loop->statement->body;
    Expr *assignment, *condition = loop->statement->expression;

    while (body && body->kind == ST_BLOCK && !body->next) {
        body = body->body;
    }

    if (cg.parser->no_register_loops || loop->count != 1 || !body || body->next ||
        body->kind != ST_EXPR || loop->delta != 1 || condition->kind != EX_BINARY ||
        condition->op != '<' || condition->left->kind != EX_OBJECT ||
        condition->left->symbol != loop->index ||
        reg_width(common_type(condition->left->type, condition->right->type)) != 2 ||
        !direct_operand(condition->right,
                        common_type(condition->left->type, condition->right->type), 0, 0))
        return NULL;

    assignment = body->expression;

    if (assignment->kind != EX_ASSIGN || assignment->op || assignment->left->kind != EX_DEREF ||
        assignment->left->left != loop->accesses[0].address)
        return NULL;

    return assignment;
}

static Expr *affine_initial(AffineLoop *loop)
{
    Statement *initial = loop->statement->initial;
    Expr *e;
    uint32_t start;

    while (initial && initial->kind == ST_BLOCK && !initial->next) {
        initial = initial->body;
    }

    if (!initial || initial->next || initial->kind != ST_EXPR)
        return NULL;

    e = initial->expression;
    return e->kind == EX_ASSIGN && !e->op && e->left->kind == EX_OBJECT &&
                   e->left->symbol == loop->index && integer_constant(e->right, &start)
               ? e
               : NULL;
}

static int unroll_plan(AffineLoop *loop, Expr *assignment, UnrollPlan *plan);

static void affine_collect(Statement *s, Function *f)
{
    for (; s; s = s->next) {
        AffineLoop loop;

        unsigned i;

        /* Case labels may enter a loop past its initializer. Match emission */
        if (s->kind == ST_SWITCH)
            continue;

        if (cg.affine_count < 32 && affine_plan(s, &loop) && f->slots + loop.count * 2 + 4 <= 768) {
            Expr *assignment = affine_register_assignment(&loop);

            loop.unroll_selected = assignment && unroll_plan(&loop, assignment, &loop.unroll);

            if (!loop.unroll_selected)
                for (i = 0; i < loop.count; ++i) {
                    loop.accesses[i].offset = f->slots + 1;
                    f->slots += 2;
                }

            cg.affine[cg.affine_count++] = loop;
        }

        affine_collect(s->body, f);
        affine_collect(s->alternate, f);
        affine_collect(s->initial, f);
    }
}

static void affine_prepare(Function *f)
{
    cg.affine_count = 0;
    cg.affine_active = NULL;

    if (!cg.parser->no_strength_reduction)
        affine_collect(f->body, f);
    if (cg.affine_count)
        f->frame = f->slots + 4;
}

static AffineLoop *affine_find(Statement *s)
{
    unsigned i;

    for (i = 0; i < cg.affine_count; ++i) {
        if (cg.affine[i].statement == s)
            return &cg.affine[i];
    }

    return NULL;
}

static int affine_pointer(Expr *e, int in_x)
{
    AffineLoop *loop = cg.affine_active;

    unsigned i;

    if (!loop)
        return 0;

    for (i = 0; i < loop->count; ++i) {
        if (loop->accesses[i].address == e) {
            code("    %s %s\n", in_x ? "ldx" : "lda", frame_operand(loop->accesses[i].offset));
            return 1;
        }
    }

    return 0;
}

static void affine_initialize(AffineLoop *loop)
{
    unsigned i;
    AffineLoop *saved = cg.affine_active;

    cg.affine_active = NULL;
    code("; affine loop: %s, %u running address(es)\n", loop->index->name, loop->count);

    for (i = 0; i < loop->count; ++i) {
        emit_value(loop->accesses[i].address);
        code("    sta %s\n", frame_operand(loop->accesses[i].offset));
    }

    cg.affine_active = saved;
}

/* Only the address setup sees the proven entry value. Do not change the
 * symbol's home, body uses, final-index recovery or the shared expression tree. */
static int affine_entry_value(AffineLoop *loop, Expr *e, unsigned start, unsigned *value)
{
    uint32_t constant;

    unsigned left, right;

    if (integer_constant(e, &constant)) {
        *value = constant & 65535;
        return 1;
    }
    if (e->kind == EX_OBJECT && e->symbol == loop->index) {
        *value = start;
        return 1;
    }
    if (e->kind == EX_CAST && same_value_representation(e->type, e->left->type))
        return affine_entry_value(loop, e->left, start, value);
    if (word_left_shift_factor(e, &constant) && affine_entry_value(loop, e->left, start, &left)) {
        *value = (left * constant) & 65535;
        return 1;
    }
    if (e->kind != EX_BINARY || !affine_entry_value(loop, e->left, start, &left) ||
        !affine_entry_value(loop, e->right, start, &right))
        return 0;

    if (e->op == '+')
        *value = (left + right) & 65535;
    else if (e->op == '-')
        *value = (left - right) & 65535;
    else if (e->op == '*')
        *value = (left * right) & 65535;
    else
        return 0;

    return 1;
}

static void affine_entry_address(AffineLoop *loop, Expr *e, unsigned start)
{
    unsigned value, scale;

    if (strength_pointer(e, 0))
        return;
    if (e->kind == EX_DEREF && e->type.array) {
        affine_entry_address(loop, e->left, start);
        return;
    }
    if (e->kind != EX_BINARY) {
        emit_value(e);
        return;
    }

    affine_entry_address(loop, e->left, start);

    if (affine_entry_value(loop, e->right, start, &value)) {
        scale = width(pointed_type(value_type(e->left->type)));
        strength_adjust((e->op == '+' ? value * scale : 0u - value * scale) & 65535);
    } else
        binary_after_left(e->left, e->right, e->op);
}

static void affine_unroll_initialize(AffineLoop *loop, int in_x)
{
    Statement *initial = loop->statement->initial;
    Expr *e;
    uint32_t start;
    AffineLoop *saved = cg.affine_active;

    while (initial && initial->kind == ST_BLOCK && !initial->next) {
        initial = initial->body;
    }

    e = initial && initial->kind == ST_EXPR ? initial->expression : NULL;
    cg.affine_active = NULL;

    if (initial && !initial->next && e && e->kind == EX_ASSIGN && !e->op &&
        e->left->kind == EX_OBJECT && e->left->symbol == loop->index &&
        integer_constant(e->right, &start)) {
        code("; affine loop: %s, known initial index%s\n", loop->index->name,
             in_x ? ", direct X" : "");
        affine_entry_address(loop, loop->accesses[0].address, start & 65535);

        if (in_x)
            code("    tax\n");
        else
            code("    sta %s\n", frame_operand(loop->accesses[0].offset));
    } else if (in_x)
        emit_value_x(loop->accesses[0].address);
    else
        affine_initialize(loop);

    cg.affine_active = saved;
}

static void affine_advance(AffineLoop *loop)
{
    unsigned i;

    for (i = 0; i < loop->count; ++i) {
        code("    lda %s\n", frame_operand(loop->accesses[i].offset));
        strength_adjust(loop->accesses[i].stride);
        code("    sta %s\n", frame_operand(loop->accesses[i].offset));
    }
}

#include "loop_unroll.inc"

/* Mirror entry-address emission: a cached function cursor or a folded scalar
 * needs no induction home; a remaining dynamic scalar still may read it. */
static int affine_entry_reads_index(AffineLoop *loop, Expr *e, unsigned start)
{
    unsigned value, delta;

    if (strength_pointer_plan(e, &delta))
        return 0;
    if (e->kind == EX_DEREF && e->type.array)
        return affine_entry_reads_index(loop, e->left, start);
    if (e->kind != EX_BINARY)
        return loop_mentions(e, loop->index);

    return affine_entry_reads_index(loop, e->left, start) ||
           (!affine_entry_value(loop, e->right, start, &value) &&
            loop_mentions(e->right, loop->index));
}

static unsigned affine_compacted_offset(unsigned offset, unsigned *holes, unsigned count)
{
    unsigned i, result = offset;

    for (i = 0; i < count; ++i) {
        if (holes[i] < offset)
            result -= 2;
    }

    return result;
}

/* A selected affine region owns its entry address and never consumes the
 * function cursor inside its body. Keep a function cursor only if a remaining
 * expression actually consumes it. This also removes its synchronization. */
static int affine_function_cursor_use_expr(Expr *e, InductionCursor *cursor, int comparing)
{
    unsigned i, j, delta;

    if (!e)
        return 0;

    IndexedOperand operand;

    if ((e->kind == EX_MEMBER || e->kind == EX_DEREF) && indexed_operand(e, &operand))
        return affine_function_cursor_use_expr(operand.index, cursor, 0);
    if (e->kind == EX_ASSIGN && indexed_operand(e->left, &operand))
        return affine_function_cursor_use_expr(operand.index, cursor, 0) ||
               affine_function_cursor_use_expr(e->right, cursor, 0);

    for (i = 0; i < cg.affine_count; ++i) {
        if (cg.affine[i].unroll_selected)
            for (j = 0; j < cg.affine[i].count; ++j) {
                if (cg.affine[i].accesses[j].address == e)
                    return 0;
            }
    }

    if (strength_pointer_plan(e, &delta) == cursor)
        return 1;

    comparing = e->kind == EX_BINARY && comparison(e->op) &&
                word_integer(common_type(e->left->type, e->right->type));

    if (affine_function_cursor_use_expr(e->left, cursor, comparing) ||
        affine_function_cursor_use_expr(e->right, cursor, comparing) ||
        affine_function_cursor_use_expr(e->third, cursor, 0))
        return 1;

    for (i = 0; i < e->arg_count; ++i) {
        if (affine_function_cursor_use_expr(e->args[i], cursor, 0))
            return 1;
    }

    return 0;
}

static int affine_function_cursor_use(Statement *s, InductionCursor *cursor)
{
    for (; s; s = s->next) {
        if (affine_function_cursor_use_expr(s->expression, cursor, 0) ||
            affine_function_cursor_use_expr(s->step, cursor, 0) ||
            affine_function_cursor_use(s->initial, cursor) ||
            affine_function_cursor_use(s->body, cursor) ||
            affine_function_cursor_use(s->alternate, cursor))
            return 1;
    }

    return 0;
}

static void affine_prune_function_cursors(Function *f)
{
    unsigned i, j, n = 0, count = 0, holes[32];
    int keep[32];

    for (i = 0; i < cg.cursor_count; ++i) {
        keep[i] = affine_function_cursor_use(f->body, &cg.cursors[i]);

        if (!keep[i])
            holes[count++] = cg.cursors[i].offset;
    }

    if (!count)
        return;

    for (i = 0; i < cg.parser->symbol_count; ++i) {
        Symbol *v = &cg.parser->symbols[i];

        if (v->owner == f->id)
            v->offset = affine_compacted_offset(v->offset, holes, count);
    }

    for (i = 0; i < cg.affine_count; ++i) {
        for (j = 0; j < cg.affine[i].count; ++j) {
            cg.affine[i].accesses[j].offset =
                affine_compacted_offset(cg.affine[i].accesses[j].offset, holes, count);
        }
    }

    for (i = 0; i < cg.cursor_count; ++i) {
        if (keep[i]) {
            InductionCursor c = cg.cursors[i];

            c.offset = affine_compacted_offset(c.offset, holes, count);
            cg.cursors[n++] = c;
        }
    }

    cg.cursor_count = n;
    f->slots -= 2 * count;
    f->frame = f->slots ? f->slots + 4 : 0;
}

static void affine_compact_indices(Function *f)
{
    unsigned i, j, holes[32];

    for (i = 0; i < cg.affine_count; ++i) {
        AffineLoop *loop = &cg.affine[i];
        UnrollPlan *plan = &loop->unroll;
        Expr *initial;
        uint32_t start;

        if (!loop->unroll_selected || !plan->full || plan->counter.update_index ||
            plan->counter.recover_index || !loop->index->scope || !loop_private(loop->index) ||
            loop_observed_outside(f->body, loop->statement, loop->index))
            continue;

        initial = affine_initial(loop);

        if (!initial || !integer_constant(initial->right, &start) ||
            (plan->span &&
             affine_entry_reads_index(loop, loop->accesses[0].address, start & 65535)))
            continue;

        loop->dead_index = 1;
        holes[cg.dead_index_count] = loop->index->offset;
        cg.dead_indices[cg.dead_index_count++] = loop->index;
    }

    if (!cg.dead_index_count)
        return;

    for (i = 0; i < cg.parser->symbol_count; ++i) {
        Symbol *symbol = &cg.parser->symbols[i];

        if (symbol->owner != f->id)
            continue;

        for (j = 0; j < cg.dead_index_count; ++j) {
            if (cg.dead_indices[j] == symbol)
                break;
        }

        symbol->offset = j < cg.dead_index_count
                             ? 0
                             : affine_compacted_offset(symbol->offset, holes, cg.dead_index_count);
    }

    for (i = 0; i < cg.cursor_count; ++i) {
        cg.cursors[i].offset =
            affine_compacted_offset(cg.cursors[i].offset, holes, cg.dead_index_count);
    }

    for (i = 0; i < cg.affine_count; ++i) {
        for (j = 0; j < cg.affine[i].count; ++j) {
            cg.affine[i].accesses[j].offset = affine_compacted_offset(
                cg.affine[i].accesses[j].offset, holes, cg.dead_index_count);
        }
    }

    f->slots -= 2 * cg.dead_index_count;
    f->frame = f->slots ? f->slots + 4 : 0;
}

static void affine_initialize_dead_index(AffineLoop *loop)
{
    Expr literal = {0};
    uint32_t start;

    if (!loop->unroll.span)
        return;
    if (!integer_constant(affine_initial(loop)->right, &start))
        error_at(here(cg.parser), "internal nonconstant eliminated induction initializer");

    literal.kind = EX_INT;
    literal.type = loop->index->type;
    literal.value = start;
    strength_sync(loop->index, &literal);
}

/* An explicit private near pointer can use the same X store loop, with its
 * existing home supplying the initial address and receiving the final one. */
static Expr *affine_explicit_store(Statement *s, Symbol **cursor, unsigned *stride)
{
    Statement *body = s->body, *tail;
    Expr *store, *step, *address;
    uint32_t amount = 1;

    if (cg.parser->no_register_loops || cg.parser->no_register_cursors ||
        cg.function->jump_label_count || bound_state.cursor || bound_state.pending ||
        cg.retained_index || cg.retained_second || cg.scan_cursor || cg.affine_active ||
        volatile_statement(s))
        return NULL;

    while (body && body->kind == ST_BLOCK && !body->next && !body->inline_callee) {
        body = body->body;
    }

    if (!body || body->kind != ST_EXPR || body->inline_callee)
        return NULL;

    store = body->expression;
    tail = body->next;

    if (!store || store->kind != EX_ASSIGN || store->op || store->left->kind != EX_DEREF)
        return NULL;

    address = store->left->left;

    if (tail) {
        if (tail->kind != ST_EXPR || tail->next || tail->inline_callee ||
            !(step = tail->expression) || step->kind != EX_ASSIGN || step->op != '+' ||
            step->left->kind != EX_OBJECT || address->kind != EX_OBJECT ||
            step->left->symbol != address->symbol || !integer_constant(step->right, &amount) ||
            !amount || amount > 2)
            return NULL;
    } else {
        if (width(store->type) != 1 || address->kind != EX_POST || address->op != TOK_INC)
            return NULL;

        address = address->left;
    }

    if (address->kind != EX_OBJECT || far_pointer(address->type) || address->type.banked ||
        !loop_private(address->symbol) || loop_mentions(store->right, address->symbol))
        return NULL;

    *cursor = address->symbol;
    *stride = amount * width(store->left->type);
    return store;
}

/* A straight scalar store can retain its one cursor in X. General regions use
 * the frame cursor so branches, wide expressions and helper scratch stay safe. */
static int affine_register_loop(Statement *s, AffineLoop *loop)
{
    Symbol *cursor = NULL;
    Expr *assignment, *condition = s->expression;

    unsigned enter, start, end, done, stride = 0;
    DpCounter counter;
    int counted, byte_fill;
    uint32_t byte = 0;

    assignment =
        loop ? affine_register_assignment(loop) : affine_explicit_store(s, &cursor, &stride);

    if (!assignment)
        return 0;
    if (loop && unroll_loop(loop, assignment))
        return 1;

    byte_fill = cursor && stride == 1 && width(assignment->type) == 1 &&
                !assignment->type.is_bool && integer_constant(assignment->right, &byte);

    if (!byte_fill &&
        (width(assignment->type) != 2 ||
         !(assignment->right->kind == EX_INT ||
           (assignment->right->kind == EX_OBJECT && !assignment->right->type.array)) ||
         reg_width(assignment->right->type) != 2 || assignment->right->type.base == TY_FLOAT))
        return 0;

    counted = dp_counter_plan(s, loop, &counter);

    if (cursor && (!counted || counter.wide || counter.descending || counter.countdown ||
                   counter.update_index ||
                   (!byte_fill && !direct_operand(assignment->right, assignment->type, 0, 0))))
        return 0;

    enter = ++cg.label;
    start = ++cg.label;
    end = ++cg.label;
    done = counted ? ++cg.label : end;
    branch(condition, enter, done, enter);
    label(enter);

    if (loop) {
        affine_initialize(loop);
        stride = loop->accesses[0].stride;
    }

    if (counted)
        dp_counter_enter(&counter);

    code("; %s register cursor: X, stride %u\n", cursor ? "explicit" : "affine", stride);

    if (cursor) {
        load_symbol(cursor);
        code("    tax\n");
    } else
        code("    ldx %s\n", frame_operand(loop->accesses[0].offset));

    if (byte_fill) {
        code("; explicit register byte fill\n    phy\n    ldy z:$0000\n    sep #$20\n.a8\n    lda "
             "#$%02X\n",
             byte & 255);
        label(start);
        code("    sta a:$0000,x\n    inx\n    dey\n    bne cg_%s_%u\n    rep #$20\n.a16\n    ply\n "
             "   stz z:$0000\n",
             cg.parser->unit, start);
        code("    txa\n");
        store_symbol(cursor);
        dp_counter_exit(&counter);
        label(done);
        divmod_state.available = 0;
        return 1;
    }

    label(start);

    if (cursor) {
        code("    lda ");
        direct_operand(assignment->right, assignment->type, 0, 1);
        code("\n");
    } else
        emit_value(assignment->right);

    code("    sta a:$0000,x\n");

    if (stride <= (cursor ? 4u : 3u)) {
        unsigned i;

        for (i = 0; i < stride; ++i) {
            code("    inx\n");
        }
    } else {
        code("    txa\n");
        strength_adjust(stride);
        code("    tax\n");
    }

    if (!counted || counter.update_index) {
        load_symbol(loop->index);
        code("    inc a\n");
        store_symbol(loop->index);
    }

    if (counted) {
        code("    dec z:$0000\n    beq :+\n");
        jump(start);
        code(":\n");
    } else
        branch(condition, start, end, end);

    label(end);

    if (cursor) {
        code("    txa\n");
        store_symbol(cursor);
    }

    if (counted)
        dp_counter_exit(&counter);

    /* Deferred index updates must leave pre-existing function cursors coherent */
    if ((!counted || counter.update_index) &&
        loop_observed_outside(cg.function->body, s, loop->index))
        strength_sync(loop->index, NULL);
    if (counted)
        label(done);

    divmod_state.available = 0;
    return 1;
}
