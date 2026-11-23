// Loop lowering dispatcher, scaled-ring loops, shift scans, and fixed update folds

/* Emit one loop statement. Returns 0 when control cannot fall through */
/* A promoted region spans everything the loop statement emits: its
 * initializers and entry test as well, so every path to the end label,
 * including a zero-trip entry test, has copied the homes in. */
static int emit_loop_body(Statement *s, int select_copy);
static int bound_scan(void);
static int body_private(Symbol *v);
static int body_address_pure(Expr *e);
static int body_has_deref(Expr *e);

static Expr *guard_mismatch_call(Statement *body, Expr **comparison)
{
    Statement *guard = body_single(body), *failure;
    Expr *call;

    if (!guard || guard->next || guard->kind != ST_IF || guard->alternate ||
        !(*comparison = guard->expression) || (*comparison)->kind != EX_BINARY ||
        (*comparison)->op != TOK_NE ||
        !word_integer(common_type((*comparison)->left->type, (*comparison)->right->type)))
        return NULL;
    failure = body_single(guard->body);
    if (!failure || failure->next || failure->kind != ST_EXPR || !(call = failure->expression) ||
        call->kind != EX_CALL || !call->symbol || call->arg_count)
        return NULL;
    return call;
}

/* Keep the counter and byte width across matching elements. Only the
 * mismatch edge crosses the calling convention and needs to save X. */
static int counted_indexed_guard_loop(Statement *s)
{
    DpCounter counter;
    IndexedOperand operand;
    Statement *init;
    Expr *assignment, *comparison, *load, *expected, *call;
    uint32_t first, end, value;
    unsigned scale, offset, loop, next, mismatch, done;
    int in, out;
    if (cg.parser->no_register_loops || cg.parser->no_register_cursors ||
        cg.parser->no_loop_index_retention || cg.switch_depth || bound_state.cursor ||
        bound_state.pending || cg.stack_leaf || cg.scalar_leaf || cg.retained_index ||
        cg.retained_second || cg.scan_cursor || cg.affine_active || lftr_state.active ||
        cg.loop_y_borrowed || cg.function->symbol->interrupt ||
        !dp_counter_ascending(s, NULL, &counter, s->expression && s->expression->op == TOK_LE) ||
        counter.wide || !integer_constant(counter.bound, &end))
        return 0;
    end += counter.inclusive;
    init = body_single(s->initial);
    if (!init || init->next || init->kind != ST_EXPR || !(assignment = init->expression) ||
        assignment->kind != EX_ASSIGN || assignment->op || assignment->left->kind != EX_OBJECT ||
        assignment->left->symbol != counter.index || !integer_constant(assignment->right, &first) ||
        first >= end || end > (counter.index->type.is_unsigned ? 65535u : 32767u))
        return 0;
    if (!(call = guard_mismatch_call(s->body, &comparison)))
        return 0;
    load = comparison->left;
    expected = comparison->right;
    if (!integer_constant(expected, &value)) {
        load = comparison->right;
        expected = comparison->left;
    }
    if (load->kind == EX_CAST && word_integer(load->type) && !load->type.is_unsigned &&
        !load->left->type.pointers && load->left->type.base == TY_CHAR)
        load = load->left;
    if (load->type.pointers || load->type.base != TY_CHAR || load->type.is_bool ||
        !integer_constant(expected, &value) || value != initializer_cast(value, load->type) ||
        !indexed_operand(load, &operand) || operand.scale != 1 ||
        !retained_affine_for(operand.index, counter.index, &scale, &offset) || scale != 1 ||
        operand.offset + offset + end > width(operand.base->type))
        return 0;
    operand.offset += offset;
    operand.reg = 'x';
    loop = ++cg.label;
    next = ++cg.label;
    mismatch = ++cg.label;
    done = ++cg.label;
    code("    ldx #$%04X\n    sep #$20\n.a8\n", (unsigned)first);
    label(loop);
    code("    lda ");
    indexed_text(&operand);
    code("\n");
    if (value)
        code("    cmp #$%02X\n", (unsigned)value & 255);
    flag_branch("bne", "beq", mismatch, 0, 0);
    label(next);
    code("    inx\n    cpx #$%04X\n", (unsigned)end);
    flag_branch("bne", "beq", loop, 0, 0);
    code("    rep #$20\n.a16\n");
    region_home_liveness(cg.function, s, counter.index->offset, &in, &out);
    if (out) {
        code("    txa\n");
        store_symbol(counter.index);
        strength_sync(counter.index, NULL);
    }
    jump(done);
    label(mismatch);
    code("    rep #$20\n.a16\n    phx\n");
    emit_discarded(call);
    code("    plx\n    sep #$20\n.a8\n");
    jump(next);
    code(".a16\n");
    label(done);
    divmod_state.available = 0;
    return 1;
}

/* The mismatch call is the only edge that can clobber the cursor registers.
 * Keep the full promoted comparison unless its constant fits in a byte. */
static int counted_pointer_guard_loop(Statement *s)
{
    Statement *init;
    Statement shape = *s;
    Expr *step = s->step, *test = s->expression, *comparison, *load, *expected, *call, *zero;
    Symbol *cursor;

    DpCounter counter;
    Type count_type;
    unsigned loop, match, done;
    uint32_t value;
    int literal, byte, in, out;
    if (cg.parser->no_register_loops || cg.parser->no_register_cursors || cg.switch_depth ||
        bound_state.cursor || bound_state.pending || cg.stack_leaf || cg.scalar_leaf ||
        cg.retained_index || cg.scan_cursor || cg.affine_active || cg.loop_y_borrowed ||
        cg.function->symbol->interrupt || s->kind != ST_FOR || !step || step->kind != EX_COMMA ||
        !test || volatile_statement(s))
        return 0;
    shape.step = step->left;
    if (!dp_counter_shape(&shape, NULL, &counter)) {
        shape.step = step->right;
        if (!dp_counter_shape(&shape, NULL, &counter))
            return 0;
    }
    init = body_single(s->initial);
    if (!init || init->next || init->kind != ST_EXPR || !(zero = init->expression) ||
        zero->kind != EX_ASSIGN || zero->op || zero->left->kind != EX_OBJECT ||
        zero->left->symbol != counter.index || !integer_constant(zero->right, &value) || value)
        return 0;
    count_type = common_type(test->left->type, counter.bound->type);
    if (counter.wide || counter.index->type.is_bool ||
        (!counter.index->type.is_unsigned && count_type.is_unsigned &&
         (!integer_constant(counter.bound, &value) || value > 32767)))
        return 0;
    if (!(call = guard_mismatch_call(s->body, &comparison)))
        return 0;
    load = comparison->left;
    expected = comparison->right;
    if (load->kind == EX_CAST && load->type.base == TY_INT && !load->type.is_unsigned)
        load = load->left;
    if (load->kind != EX_DEREF) {
        load = comparison->right;
        expected = comparison->left;
        if (load->kind == EX_CAST && load->type.base == TY_INT && !load->type.is_unsigned)
            load = load->left;
    }
    if (load->kind != EX_DEREF || load->type.pointers || load->type.base != TY_CHAR ||
        load->type.is_bool || load->left->kind != EX_OBJECT || far_pointer(load->left->type))
        return 0;
    cursor = load->left->symbol;
    if (!body_private(cursor) ||
        body_step_direction(shape.step == step->left ? step->right : step->left, cursor) != 1 ||
        increment_step(cursor->type) != 1)
        return 0;
    literal = integer_constant(expected, &value);
    if (!literal && (expected->kind != EX_OBJECT || !known_integer(expected->type) ||
                     !body_private(expected->symbol) || expected->symbol == counter.index))
        return 0;
    byte = literal && (load->type.is_unsigned ? value <= 255
                                              : (int32_t)value >= -128 && (int32_t)value <= 127);
    loop = ++cg.label;
    match = ++cg.label;
    done = ++cg.label;
    emit_value(counter.bound);
    flag_branch("beq", "bne", done, 0, 0);
    if (!count_type.is_unsigned)
        flag_branch("bmi", "bpl", done, 0, 0);
    code("    phy\n    pha\n");
    if (!literal) {
        emit_value(expected);
        code("    pha\n");
    }
    emit_value_x(load->left);
    code("    lda %u,s\n    tay\n", literal ? 1u : 3u);
    if (byte)
        code("    sep #$20\n.a8\n");
    label(loop);
    code("    lda a:$0000,x\n");
    if (!byte)
        narrow_char(load->type);
    if (literal)
        code("    cmp #$%0*X\n", byte ? 2 : 4, value & (byte ? 255u : 65535u));
    else
        code("    cmp 1,s\n");
    flag_branch("beq", "bne", match, 0, 0);
    if (byte)
        code("    rep #$20\n.a16\n");
    code("    phx\n    phy\n");
    emit_discarded(call);
    code("    ply\n    plx\n");
    if (byte)
        code("    sep #$20\n.a8\n");
    label(match);
    code("    inx\n    dey\n");
    flag_branch("bne", "beq", loop, 0, 0);
    if (byte)
        code("    rep #$20\n.a16\n");
    if (!literal)
        code("    pla\n");
    code("    pla\n    ply\n");
    region_home_liveness(cg.function, s, counter.index->offset, &in, &out);
    if (out)
        store_symbol(counter.index);
    region_home_liveness(cg.function, s, cursor->offset, &in, &out);
    if (out) {
        code("    txa\n");
        store_symbol(cursor);
    }
    label(done);
    divmod_state.available = 0;
    return 1;
}

/* A private near cursor can stay in X while testing each element. A returning
 * call on a hit saves X; a return from the function uses the normal home.
 * Trial emission rejects predicates that need X for any other purpose. */
static int pointer_scan_loop(Statement *s)
{
    Expr *test = s->expression, *end, *advance;
    Statement *guard, *hit;
    Symbol *cursor;

    CodegenCheckpoint *saved;
    unsigned start, done, match, next, stride, in_range = 0;
    int call_hit;
    if (cg.parser->no_register_loops || cg.parser->no_register_cursors || cg.switch_depth ||
        bound_state.pending || bound_state.cursor || cg.scan_cursor || cg.scalar_leaf ||
        (s->kind != ST_WHILE && s->kind != ST_FOR) || !test || test->kind != EX_BINARY ||
        (test->op != TOK_NE && test->op != '<' && test->op != TOK_LE) ||
        test->left->kind != EX_OBJECT)
        return 0;
    cursor = test->left->symbol;
    end = test->right;
    if (!cursor->type.pointers || far_pointer(cursor->type) || !body_private(cursor) ||
        end->kind != EX_OBJECT || end->symbol == cursor || end->type.array || !end->type.pointers ||
        far_pointer(end->type) || object_volatile(end->type) ||
        (end->symbol->owner && !compare_memory_operand(end, 0)))
        return 0;
    guard = body_single(s->body);
    if (!guard || guard->kind != ST_IF || guard->alternate || body_effect(guard->expression))
        return 0;
    if (s->kind == ST_FOR) {
        if (guard->next)
            return 0;
        advance = s->step;
    } else {
        Statement *step = guard->next;
        if (!step || step->next || step->kind != ST_EXPR)
            return 0;
        advance = step->expression;
    }
    if (!advance || body_step_direction(advance, cursor) != 1)
        return 0;
    hit = body_single(guard->body);
    call_hit = hit && hit->kind == ST_EXPR && !hit->next && hit->expression &&
               hit->expression->kind == EX_CALL && hit->expression->symbol &&
               !statement_references(guard->body, cursor);
    if (!call_hit) {
        for (; hit && hit->kind == ST_EXPR; hit = hit->next) {
        }
        if (!hit || hit->kind != ST_RETURN || hit->next)
            return 0;
    }
    stride = increment_step(cursor->type);
    if (!stride || stride > 65535)
        return 0;

    saved = allocate(sizeof *saved);
    cg_checkpoint_save(saved);
    start = ++cg.label;
    done = ++cg.label;
    match = ++cg.label;
    next = ++cg.label;
    if (test->op == TOK_LE)
        in_range = ++cg.label;
    code("; register pointer scan\n");
    emit_value_x(test->left);
    label(start);
    if (end->symbol->owner || end->symbol->type.banked)
        code("    txa\n    cmp ");
    else
        code("    cpx ");
    array_operand(end->symbol, 0);
    code("\n");
    if (in_range)
        code("    beq cg_%s_%u\n", cg.parser->unit, in_range);
    if (test->op == TOK_NE)
        flag_branch("beq", "bne", done, 0, 0);
    else
        flag_branch("bcs", "bcc", done, 0, 0);
    if (in_range)
        label(in_range);
    divmod_state.available = 0;
    cg.scan_cursor = cursor;
    cg.scan_failed = 0;
    bound_state.start = cg.length;
    bound_state.mark_count = 0;
    branch(guard->expression, match, next, next);
    bound_state.end = cg.length;
    if (cg.scan_failed || !bound_scan()) {
        cg_checkpoint_restore_length(saved);
        free(saved);
        return 0;
    }

    cg.scan_cursor = NULL;
    bound_state.start = saved->bound.start;
    bound_state.end = saved->bound.end;
    bound_state.mark_count = saved->bound.mark_count;
    free(saved);
    label(next);
    if (stride <= 3) {
        unsigned i;
        for (i = 0; i < stride; ++i)
            code("    inx\n");
    } else
        code("    txa\n    clc\n    adc #$%04X\n    tax\n", stride);
    jump(start);
    label(match);
    divmod_state.available = 0;
    if (call_hit) {
        code("    phx\n");
        if (cg.stack_leaf)
            cg.stack_bias += 2;
        emit_discarded(hit->expression);
        if (cg.stack_leaf)
            cg.stack_bias -= 2;
        code("    plx\n");
        jump(next);
    } else {
        code("    txa\n");
        store_symbol(cursor);
        emit_statements(guard->body);
    }
    label(done);
    divmod_state.available = 0;
    code("    txa\n");
    store_symbol(cursor);
    return 1;
}

#include "index_retention.inc"

typedef struct {
    Symbol *index, *array;
    unsigned mask, updates, accesses;
} ScaledRing;

typedef struct {
    ScaledRing rings[4];
    unsigned count, edits, casts;
    Expr cast[16];

    struct {
        Expr *node, original, replacement;
    } edit[48];
} RingLoop;

static Expr *ring_step(Expr *e, Symbol **index, unsigned *mask)
{
    Expr *rhs, *step;
    uint32_t bits, one;

    if (!e || e->kind != EX_ASSIGN || e->op || e->left->kind != EX_OBJECT ||
        e->left->type.base != TY_INT || e->left->type.pointers || !e->left->type.is_unsigned ||
        !body_private(e->left->symbol))
        return NULL;
    rhs = word_bits(e->right);
    if (rhs->kind != EX_BINARY || rhs->op != '&' || !integer_constant(rhs->right, &bits) || !bits ||
        bits >= 0x8000 || ((bits + 1) & bits))
        return NULL;
    step = word_bits(rhs->left);
    if (step->kind != EX_BINARY || step->op != '+' ||
        !lftr_object(word_bits(step->left), e->left->symbol) ||
        !integer_constant(step->right, &one) || one != 1)
        return NULL;
    *index = e->left->symbol;
    *mask = (unsigned)bits;
    return rhs;
}

static ScaledRing *ring_find(RingLoop *p, Symbol *index)
{
    unsigned i;

    for (i = 0; i < p->count; ++i)
        if (p->rings[i].index == index)
            return &p->rings[i];
    return NULL;
}

static int ring_collect(RingLoop *p, Statement *s)
{
    for (; s; s = s->next) {
        Symbol *index;
        unsigned mask;
        if (s->kind != ST_BLOCK && s->kind != ST_EXPR && s->kind != ST_IF && s->kind != ST_EMPTY &&
            s->kind != ST_BREAK && s->kind != ST_CONTINUE && s->kind != ST_RETURN)
            return 0;
        if (s->kind == ST_EXPR && ring_step(s->expression, &index, &mask)) {
            ScaledRing *r = ring_find(p, index);
            if (!r) {
                if (p->count == sizeof p->rings / sizeof *p->rings)
                    return 0;
                r = &p->rings[p->count++];
                r->index = index;
                r->mask = mask;
            } else if (r->mask != mask)
                return 0;
        }
        if (!ring_collect(p, s->body) || !ring_collect(p, s->alternate))
            return 0;
    }
    return 1;
}

static int ring_edit(RingLoop *p, Expr *node, Expr replacement)
{
    unsigned i;

    for (i = 0; i < p->edits; ++i)
        if (p->edit[i].node == node)
            return 0;
    if (p->edits == sizeof p->edit / sizeof *p->edit)
        return 0;
    p->edit[i].node = node;
    p->edit[i].original = *node;
    p->edit[i].replacement = replacement;
    ++p->edits;
    return 1;
}

/* Only recurrence updates, equality between encoded indices, and indexed
 * accesses to fixed two-byte arrays observe the representation. A valid
 * subscript in those arrays has bit 15 clear. Rotating the word on entry
 * retains that bit for an equality check or an exit without an access. */
static int ring_uses(RingLoop *p, Expr *e, int discarded)
{
    ScaledRing *r;
    Symbol *index;
    unsigned mask, i;
    Expr *rhs, *a, *b;
    if (!e)
        return 1;
    if (discarded && (rhs = ring_step(e, &index, &mask)) != NULL &&
        (r = ring_find(p, index)) != NULL) {
        Expr *step = word_bits(rhs->left);
        Expr two = *step->right, scaled_mask = *rhs->right;
        if (two.kind != EX_INT || scaled_mask.kind != EX_INT)
            return 0;
        two.value = 2;
        scaled_mask.value = mask * 2;
        ++r->updates;
        return ring_edit(p, step->right, two) && ring_edit(p, rhs->right, scaled_mask);
    }
    if (e->kind == EX_BINARY && (e->op == TOK_EQ || e->op == TOK_NE)) {
        a = word_bits(e->left);
        b = word_bits(e->right);
        if (a->kind == EX_OBJECT && b->kind == EX_OBJECT && ring_find(p, a->symbol) &&
            ring_find(p, b->symbol))
            return 1;
    }
    if (e->kind == EX_DEREF && e->left->kind == EX_BINARY && e->left->op == '+') {
        Expr *address = e->left, *base = address->left, *subscript = word_bits(address->right);
        if (subscript->kind == EX_OBJECT && (r = ring_find(p, subscript->symbol)) != NULL) {
            Expr byte_base = {0}, byte_address = *address;
            if (base->kind != EX_OBJECT || !base->type.array || base->symbol->owner ||
                !base->symbol->defined || base->symbol->dpage || base->type.banked ||
                width(base->type) > 65536 || width(pointed_type(value_type(base->type))) != 2 ||
                width(e->type) != 2 || width(base->type) < (r->mask + 1) * 2 ||
                (r->array && r->array != base->symbol))
                return 0;
            r->array = base->symbol;
            ++r->accesses;
            byte_base.kind = EX_CAST;
            byte_base.type = type(TY_CHAR, 1);
            byte_base.left = base;
            byte_base.location = base->location;
            if (p->casts == sizeof p->cast / sizeof *p->cast)
                return 0;
            p->cast[p->casts] = byte_base;
            byte_address.type = byte_base.type;
            byte_address.left = &p->cast[p->casts++];
            return ring_edit(p, address, byte_address);
        }
    }
    if (e->kind == EX_CALL || (e->kind == EX_OBJECT && ring_find(p, e->symbol)))
        return 0;
    if (!ring_uses(p, e->left, 0) || !ring_uses(p, e->right, 0) || !ring_uses(p, e->third, 0))
        return 0;

    for (i = 0; i < e->arg_count; ++i)
        if (!ring_uses(p, e->args[i], 0))
            return 0;
    return 1;
}

static int ring_check_body(RingLoop *p, Statement *s)
{
    for (; s; s = s->next)
        if (s->kind == ST_FOR || s->kind == ST_WHILE || s->kind == ST_DO ||
            !ring_uses(p, s->expression, s->kind == ST_EXPR) || !ring_check_body(p, s->body) ||
            !ring_check_body(p, s->alternate))
            return 0;
    return 1;
}

static int guard_loop_y_operand(Expr *e)
{
    unsigned i;

    if (!e)
        return 1;
    if (e->kind == EX_CALL)
        return 0;
    if (e->kind == EX_OBJECT && e->symbol->owner &&
        (e->type.array || reg_width(e->type) > 2 || !guard_dp_home(e->symbol)))
        return 0;
    if (!guard_loop_y_operand(e->left) || !guard_loop_y_operand(e->right) ||
        !guard_loop_y_operand(e->third))
        return 0;

    for (i = 0; i < e->arg_count; ++i)
        if (!guard_loop_y_operand(e->args[i]))
            return 0;
    return 1;
}

static int guard_loop_y_region(Statement *s, int *has_group)
{
    for (; s; s = s->next) {
        ByteGuardGroup group;
        switch (s->kind) {
        case ST_EMPTY:
        case ST_BLOCK:
        case ST_IF:
        case ST_EXPR:
        case ST_BREAK:
        case ST_CONTINUE:
            break;
        default:
            return 0;
        }
        if (!guard_loop_y_operand(s->expression) || !guard_loop_y_region(s->body, has_group) ||
            !guard_loop_y_region(s->alternate, has_group))
            return 0;
        if (!*has_group && s->kind == ST_IF && plan_byte_guard_group(s, &group))
            *has_group = 1;
    }
    return 1;
}

/* An innermost guard region can save the caller's Y once. The ordinary
 * loop end handles both the test and break exits before restoring it. */
static int emit_guard_y_loop(Statement *s, int *result)
{
    int has_group = 0;

    if (!dp_state.homes || cg.loop_y_borrowed || cg.cursor_count || cg.switch_depth ||
        cg.function->jump_label_count || cg.parser->no_register_cursors ||
        cg.parser->no_strength_reduction || cg.parser->no_indexed_operands ||
        volatile_statement(s) || statement_inline_markers(s) ||
        !guard_loop_y_operand(s->expression) || !guard_loop_y_operand(s->step) ||
        !guard_loop_y_region(s->initial, &has_group) || !guard_loop_y_region(s->body, &has_group) ||
        !has_group)
        return 0;
    code("; borrow Y across near byte guard loop\n    phy\n");
    cg.loop_y_borrowed = 1;
    *result = emit_loop_body(s, 1);
    cg.loop_y_borrowed = 0;
    code("    ply\n");
    return 1;
}

static Symbol *find_guard_ring_tail(Statement *s)
{
    for (; s; s = s->next) {
        ByteGuardGroup group;
        GuardRingTail tail = {0};
        if (s->kind == ST_IF && plan_byte_guard_group(s, &group) &&
            fixed_guard_displacements(&group) && guard_ring_tail(&group, &tail))
            return tail.index;
        if (s->kind == ST_BLOCK) {
            Symbol *nested = find_guard_ring_tail(s->body);
            if (nested)
                return nested;
        }
    }
    return NULL;
}

static int carried_ring_home_unused(size_t start, const char *home)
{
    const char *line = cg.assembly + start;
    int owned = 0;

    while (*line) {
        const char *end = strchr(line, '\n'), *use;
        if (!end)
            end = line + strlen(line);
        if (!strncmp(line, "; retained scratch begin\n", 25))
            owned = 1;
        else if (!strncmp(line, "; retained scratch end\n", 23))
            owned = 0;
        else if (!owned && *line == ' ' && (use = strstr(line, home)) != NULL && use < end)
            return 0;
        line = *end ? end + 1 : end;
    }
    return 1;
}

/* Y addresses the popped element and its byte guards. X holds the tail
 * until a wrapping path needs both registers. Validate the remaining loop
 * before committing the binding, including all exits and continue edges */
static int emit_carried_ring_loop(Statement *s, RingLoop *rings, int *result)
{
    Symbol *tail, *head;

    CodegenCheckpoint *saved;
    Statement *previous = loop_previous, *current = loop_current;
    size_t start = cg.length, body;
    unsigned slot, home;
    char operand[32];
    int kept;
    if (rings->count != 2 || cg.scaled_ring_tail || body_asm_statements(s->body) ||
        !(tail = find_guard_ring_tail(s->body)))
        return 0;
    head = rings->rings[rings->rings[0].index == tail ? 1 : 0].index;
    slot = (tail->offset - 1) / 2;
    home = dp_state.map[slot];

    for (unsigned i = 0; i < dp_state.words; ++i)
        if (i != slot && dp_state.map[i] == home)
            return 0;
    snprintf(operand, sizeof operand, "%s", frame_operand(tail->offset));
    saved = allocate(sizeof *saved);
    cg_checkpoint_save(saved);
    cg.scaled_ring_head = head;
    cg.scaled_ring_tail = tail;
    cg.scaled_ring_x_guards = cg.scaled_ring_x_tests = 0;
    code("; keep scaled ring tail in X across loop\n    ldx %s\n", operand);
    body = cg.length;
    kept = emit_guard_y_loop(s, result) && cg.scaled_ring_x_guards == 1 && cg.scaled_ring_x_tests &&
           retained_scan(body, cg.length, 0, 0) && carried_ring_home_unused(body, operand);
    loop_previous = previous;
    loop_current = current;
    if (kept) {
        code("    stx %s\n", operand);
        cg.scaled_ring_head = cg.scaled_ring_tail = NULL;
        cg.scaled_ring_x_guards = cg.scaled_ring_x_tests = 0;
    } else {
        cg_checkpoint_restore(saved, start);
    }
    free(saved);
    return kept;
}

static int emit_scaled_ring_loop(Statement *s, int *result)
{
    RingLoop p = {0};
    unsigned i;
    if (s->kind != ST_DO || !dp_state.homes || cg.parser->no_strength_reduction ||
        cg.parser->no_indexed_operands || bound_state.cursor || cg.affine_active ||
        cg.retained_index || cg.switch_depth || cg.function->jump_label_count ||
        volatile_statement(s) || !ring_collect(&p, s->body) || !p.count ||
        !ring_check_body(&p, s->body) || !ring_uses(&p, s->expression, 0))
        return 0;

    for (i = 0; i < p.count; ++i) {
        ScaledRing *r = &p.rings[i];
        unsigned offset = r->index->offset;
        if (!r->updates || !r->accesses || !offset || !(offset & 1) ||
            (offset - 1) / 2 >= dp_state.words || !dp_state.map[(offset - 1) / 2])
            return 0;
    }

    for (i = 0; i < p.edits; ++i)
        *p.edit[i].node = p.edit[i].replacement;
    code("; scaled ring indices within loop\n");

    for (i = 0; i < p.count; ++i) {
        load_symbol(p.rings[i].index);
        code("    asl a\n    adc #$0000\n");
        store_symbol(p.rings[i].index);
    }

    for (i = 0; i < p.count; ++i)
        cg.scaled_ring_indices[i] = p.rings[i].index;
    if (!emit_carried_ring_loop(s, &p, result) && !emit_guard_y_loop(s, result))
        *result = emit_loop_body(s, 1);
    memset(cg.scaled_ring_indices, 0, sizeof cg.scaled_ring_indices);

    for (i = 0; i < p.count; ++i) {
        load_symbol(p.rings[i].index);
        code("    lsr a\n    bcc :+\n    ora #$8000\n:\n");
        store_symbol(p.rings[i].index);
    }

    for (i = p.edits; i; --i)
        *p.edit[i - 1].node = p.edit[i - 1].original;
    return 1;
}

static int while_peel_cost(const Expr *e, int *budget)
{
    if (!e)
        return 1;
    if (--(*budget) < 0 || e->kind == EX_CALL || e->kind == EX_ASSIGN || e->kind == EX_PRE ||
        e->kind == EX_POST || (e->type.base == TY_LONG && !e->type.pointers) ||
        e->type.base == TY_FLOAT || e->type.base == TY_DOUBLE)
        return 0;
    if (!while_peel_cost(e->left, budget) || !while_peel_cost(e->right, budget) ||
        !while_peel_cost(e->third, budget))
        return 0;

    for (unsigned i = 0; i < e->arg_count; ++i)
        if (!while_peel_cost(e->args[i], budget))
            return 0;
    return 1;
}

static int while_peel_entry(Expr *e)
{
    int budget = 16;

    return e && !volatile_expression(e) && while_peel_cost(e, &budget);
}

static int while_entry_true(Statement *previous, Expr *test)
{
    unsigned o1, o2;
    Symbol *s1, *s2;

    if (!previous || previous->kind != ST_EXPR || !previous->expression ||
        previous->expression->kind != EX_ASSIGN || previous->expression->op ||
        previous->expression->left->kind != EX_OBJECT)
        return 0;
    if (!test || test->kind != EX_BINARY || (test->op != TOK_NE && test->op != TOK_EQ) ||
        test->left->kind != EX_OBJECT || test->left->symbol != previous->expression->left->symbol)
        return 0;
    s1 = near_object_address(previous->expression->right, &o1);
    s2 = near_object_address(test->right, &o2);
    if (!s1 || s1 != s2)
        return 0;
    return test->op == TOK_NE ? (o1 != o2) : (o1 == o2);
}

static int emit_loop(Statement *s)
{
    int result;

    region_enter(s);
    if (emit_scaled_ring_loop(s, &result))
        code("; loop lowering: scaled ring indices\n");
    else if (!emit_guard_y_loop(s, &result))
        result = emit_loop_body(s, 1);
    region_exit(s);
    return result;
}

static int reduction_statements(Statement *s, Statement **out, unsigned *count, unsigned limit);
static int reduction_object(Expr *e, Symbol *s);
static int reduction_zero(Expr *e);

typedef struct {
    Expr *word, *count;
    Symbol *home;
    unsigned mask, shift, offset;
    int op, direction, while_zero, byte;
} WordShiftScan;

static int word_shift_scan_plan(Statement *s, WordShiftScan *scan)
{
    Statement *parts[2];
    Expr *test = s->expression, *update, *step, *value;
    uint32_t mask, shift;
    unsigned n = 0;
    int direction;

    if (cg.parser->no_strength_reduction || cg.parser->no_register_cursors ||
        cg.parser->no_body_optimizations || s->kind != ST_WHILE || !test || volatile_statement(s) ||
        !reduction_statements(s->body, parts, &n, 2) || n != 2 || parts[0]->kind != ST_EXPR ||
        parts[1]->kind != ST_EXPR)
        return 0;
    update = parts[0]->expression;
    step = parts[1]->expression;
    if (update->kind != EX_ASSIGN || (update->op != TOK_SHR && update->op != TOK_SHL)) {
        update = parts[1]->expression;
        step = parts[0]->expression;
    }
    if (update->kind != EX_ASSIGN || (update->op != TOK_SHR && update->op != TOK_SHL) ||
        !integer_constant(update->right, &shift) || !shift || shift > 4 || !step->left ||
        step->left->kind != EX_OBJECT || !word_integer(step->left->type) ||
        !(direction = body_step_direction(step, step->left->symbol)))
        return 0;
    scan->while_zero = 0;
    if (test->kind == EX_UNARY && test->op == '!') {
        test = test->left;
        scan->while_zero = 1;
    } else if (test->kind == EX_BINARY && (test->op == TOK_EQ || test->op == TOK_NE)) {
        scan->while_zero = test->op == TOK_EQ;
        if (reduction_zero(test->right))
            test = test->left;
        else if (reduction_zero(test->left))
            test = test->right;
        else
            return 0;
    }
    if (test->kind != EX_BINARY || test->op != '&' || reg_width(test->type) != 2)
        return 0;
    value = test->left;
    if (!integer_constant(test->right, &mask)) {
        if (!integer_constant(test->left, &mask))
            return 0;
        value = test->right;
    }
    if (!body_equal(word_uncast(word_bits(value)), update->left) ||
        !compare_memory_operand(step->left, 0) || !(mask & 65535))
        return 0;
    scan->byte = update->left->type.base == TY_CHAR;
    if (scan->byte) {
        if ((mask & 65535) > 255 ||
            !(scan->home = fixed_byte_home(update->left, 0, &scan->offset)) ||
            scan->home->type.banked)
            return 0;
    } else if (!word_integer(update->left->type) || !compare_memory_operand(update->left, 0) ||
               !(scan->home = direct_memory_object(update->left, &scan->offset)))
        return 0;
    if (scan->home == step->left->symbol)
        return 0;
    scan->word = update->left;
    scan->count = step->left;
    scan->mask = mask & 65535;
    scan->shift = shift;
    scan->op = update->op;
    scan->direction = direction;
    return 1;
}

static void emit_word_shift_scan(WordShiftScan *scan)
{
    unsigned start = ++cg.label, done = ++cg.label;

    code(scan->byte ? "    bit #$%02X\n" : "    bit #$%04X\n", scan->mask);
    flag_branch(scan->while_zero ? "bne" : "beq", scan->while_zero ? "beq" : "bne", done, 0, 0);
    label(start);

    for (unsigned i = 0; i < scan->shift; ++i) {
        if (scan->op == TOK_SHL)
            code("    asl a\n");
        else if (scan->word->type.is_unsigned)
            code("    lsr a\n");
        else
            code(scan->byte ? "    cmp #$80\n    ror a\n" : "    cmp #$8000\n    ror a\n");
    }
    code("    %s\n", scan->direction > 0 ? "inx" : "dex");
    code(scan->byte ? "    bit #$%02X\n" : "    bit #$%04X\n", scan->mask);
    flag_branch(scan->while_zero ? "beq" : "bne", scan->while_zero ? "bne" : "beq", start, done,
                done);
    label(done);
    divmod_state.available = 0;
}

static int word_shift_scan_loop(Statement *s)
{
    WordShiftScan scan;
    if (cg.switch_depth || cg.retained_index || cg.retained_second || cg.affine_active ||
        cg.scan_cursor || bound_state.cursor || bound_state.pending || cg.numeric_index ||
        lftr_state.active || !word_shift_scan_plan(s, &scan))
        return 0;
    code("; register word shift scan\n");
    emit_value_x(scan.count);
    if (scan.byte)
        code("    sep #$20\n.a8\n");
    code("    lda ");
    array_operand(scan.home, scan.offset);
    code("\n");
    emit_word_shift_scan(&scan);
    code("    sta ");
    array_operand(scan.home, scan.offset);
    code("\n");
    if (scan.byte)
        code("    rep #$20\n.a16\n");
    code("    txa\n");
    store_symbol(scan.count->symbol);
    return 1;
}

static int word_shift_scan_leaf(Function *f)
{
    WordShiftScan scan;
    Statement *parts[4];
    Symbol *arg, *count;
    Expr *word_init, *count_init, *seed;
    uint32_t initial;
    unsigned n = 0;
    if (f->symbol->param_count != 1 || !word_integer(f->symbol->type) ||
        !reduction_statements(f->body, parts, &n, 4) || n != 4 || parts[0]->kind != ST_EXPR ||
        parts[1]->kind != ST_EXPR || parts[3]->kind != ST_RETURN ||
        !word_shift_scan_plan(parts[2], &scan))
        return 0;
    count = scan.count->symbol;
    arg = leaf_parameter(f, 0);
    word_init = parts[0]->expression;
    count_init = parts[1]->expression;
    if (word_init->kind != EX_ASSIGN || word_init->op || count_init->kind != EX_ASSIGN ||
        count_init->op)
        return 0;
    if (reduction_object(word_init->left, count)) {
        Expr *swap = word_init;
        word_init = count_init;
        count_init = swap;
    }
    seed = word_bits(word_init->right);
    if (scan.byte && seed->kind == EX_CAST && seed->type.base == TY_CHAR && !seed->type.is_bool &&
        !seed->type.pointers)
        seed = word_bits(seed->left);
    if (!arg || arg == count || !word_integer(arg->type) || !register_parameter(0, arg->type) ||
        !body_private(count) || scan.home->owner != f->id || loop_escapes(f->body, scan.home) ||
        !body_equal(word_init->left, scan.word) || !reduction_object(seed, arg) ||
        !reduction_object(count_init->left, count) ||
        !integer_constant(count_init->right, &initial) ||
        !reduction_object(word_bits(parts[3]->expression), count))
        return 0;
    code(".segment \"CODE\"\n.export _%s\n_%s:\n; frameless word shift scan\n    txa\n    ldx "
         "#$%04X\n",
         f->symbol->asm_name, f->symbol->asm_name, initial & 65535);
    if (scan.byte)
        code("    sep #$20\n.a8\n");
    emit_word_shift_scan(&scan);
    if (scan.byte)
        code("    rep #$20\n.a16\n");
    code("    txa\n    rts\n__size_%s = * - _%s\n", f->symbol->asm_name, f->symbol->asm_name);
    f->frame = 0;
    return 1;
}

/* An unobserved fixed-word shift recurrence and its termination counter
 * can live in A and X for the whole loop. Publish both final values. */
static int fixed_shift_loop(Statement *s)
{
    Statement *body = s->body;
    Expr *test = s->expression, *update, *step, *value, *operand, *literal;
    Symbol *data, *counter;
    uint32_t shift, limit;
    unsigned at = 0, index = 0, again, done, i;

    if (cg.parser->no_register_cursors || cg.parser->no_strength_reduction || cg.switch_depth ||
        cg.retained_index || cg.retained_second || cg.affine_active || cg.scan_cursor ||
        s->kind != ST_DO || !test || test->kind != EX_BINARY || test->op != TOK_NE ||
        volatile_expression(test))
        return 0;
    operand = test->left;
    literal = test->right;
    if (!integer_constant(literal, &limit)) {
        if (!integer_constant(operand, &limit))
            return 0;
        operand = test->right;
        literal = test->left;
    }

    while (body && body->kind == ST_BLOCK && !body->next && !body->inline_callee)
        body = body->body;
    if (!body || body->kind != ST_EXPR || body->inline_callee)
        return 0;
    step = operand;
    if (body->next) {
        Statement *tail = body->next;
        if (tail->kind != ST_EXPR || tail->next || tail->inline_callee)
            return 0;
        step = tail->expression;
        if (!step || (step->kind != EX_PRE && step->kind != EX_POST) ||
            !body_equal(step->left, operand) || volatile_expression(step))
            return 0;
    } else if (step->kind != EX_PRE)
        return 0;
    if ((step->op != TOK_INC && step->op != TOK_DEC) || width(step->type) != 2 ||
        step->type.base != TY_INT || step->type.pointers)
        return 0;
    update = body->expression;
    if (!update || update->kind != EX_ASSIGN || (update->op != TOK_SHR && update->op != TOK_SHL) ||
        !integer_constant(update->right, &shift) || !shift || shift > 4 ||
        volatile_expression(update))
        return 0;
    value = update->left;
    if (width(value->type) != 2 || value->type.base != TY_INT || value->type.pointers ||
        !value->type.is_unsigned)
        return 0;
    data = value->kind == EX_OBJECT ? value->symbol : fixed_memory_object(value, &at);
    counter = step->left->kind == EX_OBJECT ? step->left->symbol
                                            : fixed_memory_object(step->left, &index);
    if (!data || !counter || data->owner || counter->owner || data->type.banked ||
        counter->type.banked || (data == counter && at < index + 2 && index < at + 2) ||
        reg_width(common_type(operand->type, literal->type)) != 2)
        return 0;
    again = ++cg.label;
    done = ++cg.label;
    code("; register-resident fixed word shift loop\n    lda ");
    array_operand(data, at);
    code("\n    ldx ");
    array_operand(counter, index);
    code("\n");
    label(again);

    for (i = 0; i < shift; ++i)
        code("    %s a\n", update->op == TOK_SHR ? "lsr" : "asl");
    code("    %s\n    cpx #$%04X\n", step->op == TOK_INC ? "inx" : "dex", limit & 65535);
    flag_branch("bne", "beq", again, done, done);
    label(done);
    code("    sta ");
    array_operand(data, at);
    code("\n    stx ");
    array_operand(counter, index);
    code("\n");
    divmod_state.available = 0;
    return 1;
}

static int empty_loop_body(Statement *s)
{
    for (; s; s = s->next) {
        if (s->kind == ST_EMPTY)
            continue;
        if (s->kind == ST_CONTINUE && !s->next)
            return 1;
        if (s->kind == ST_IF) {
            Expr *test = s->expression;
            if (test->kind != EX_BINARY || !comparison(test->op) || test->left->kind != EX_OBJECT ||
                !known_integer(test->left->type) || test->right->kind != EX_INT ||
                !known_integer(test->right->type) || volatile_expression(test) ||
                !empty_loop_body(s->body) || !empty_loop_body(s->alternate))
                return 0;
            continue;
        }
        if (s->kind != ST_BLOCK || !empty_loop_body(s->body))
            return 0;
    }
    return 1;
}

static int fold_fixed_update_loop(Statement *s)
{
    Statement *initial = body_single(s->initial), *body = body_single(s->body);
    Expr *test = s->expression, *step = s->step, *init, *update;
    unsigned off, init_off, step_off, update_off, width_bits;
    uint32_t begin, end, delta = 1, limit;
    int op;
    Symbol *index, *value;

    if (cg.parser->no_strength_reduction || cg.parser->no_loop_unroll ||
        cg.function->jump_label_count || s->kind != ST_FOR || !initial ||
        initial->kind != ST_EXPR || initial->next || !step || !test || test->kind != EX_BINARY ||
        test->op != '<' || (step->kind != EX_PRE && step->kind != EX_POST) || step->op != TOK_INC ||
        !word_integer(test->left->type) || width(test->left->type) != 2 || volatile_statement(s))
        return 0;
    init = initial->expression;
    if (!init || init->kind != EX_ASSIGN || init->op ||
        !(index = fixed_byte_home(test->left, 0, &off)) ||
        fixed_byte_home(init->left, 0, &init_off) != index || init_off != off ||
        fixed_byte_home(step->left, 0, &step_off) != index || step_off != off ||
        !same_type(test->left->type, init->left->type) ||
        !same_type(test->left->type, step->left->type) || !integer_constant(init->right, &begin) ||
        !integer_constant(test->right, &end))
        return 0;
    limit = test->left->type.is_unsigned ? 65535u : 32767u;
    if (begin >= end || end - begin < 2 || end > limit)
        return 0;
    if (!empty_loop_body(s->body)) {
        if (!body || body->kind != ST_EXPR || body->next || !(update = body->expression))
            return 0;
        if (update->kind == EX_PRE || update->kind == EX_POST)
            op = update->op == TOK_INC ? '+' : '-';
        else if (update->kind == EX_ASSIGN && (update->op == '+' || update->op == '-') &&
                 integer_constant(update->right, &delta))
            op = update->op;
        else
            return 0;
        if (!known_integer(update->type) || !update->type.is_unsigned || update->type.is_bool ||
            !(value = fixed_byte_home(update->left, 0, &update_off)) || value == index)
            return 0;
        width_bits = width(update->type) * 8;
        delta = (delta * (end - begin)) & ((1u << width_bits) - 1);
        if (delta) {
            if (width_bits == 8)
                code("    sep #$20\n.a8\n");
            code("    lda ");
            array_operand(value, update_off);
            code("\n    %s\n    %s ", op == '+' ? "clc" : "sec", op == '+' ? "adc" : "sbc");
            code(width_bits == 8 ? "#$%02X\n" : "#$%04X\n", delta);
            code("    sta ");
            array_operand(value, update_off);
            code("\n");
            if (width_bits == 8)
                code("    rep #$20\n.a16\n");
        }
    }
    code("    lda #$%04X\n    sta ", end);
    array_operand(index, off);
    code("\n");
    divmod_state.available = 0;
    return 1;
}

#include "shift_recurrence.inc"

static int emit_loop_body(Statement *s, int select_copy)
{
    unsigned start, end, body, step;
    int a, infinite, counted, rotated_while;

    DpCounter counter = {0};
    unsigned done;
    AffineLoop *affine, *saved_affine;
    Statement *previous = loop_previous;
    if (fold_fixed_update_loop(s)) {
        code("; loop lowering: folded fixed update\n");
        return 1;
    }
    if (unroll_far_doubling_sum(s)) {
        code("; loop lowering: unrolled far doubling sum\n");
        return 1;
    }
    if (far_sentinel_doubling_loop(s)) {
        code("; loop lowering: far sentinel doubling sum\n");
        return 1;
    }
    if (shift_recurrence_loop(s) || low_bit_sum_loop(s))
        return 1;
    if (select_copy && counted_byte_copy_loop(s))
        return 1;
    if (fixed_byte_sum_loop(s))
        return 1;
    if (runtime_byte_sum_loop(s))
        return 1;
    if (strided_byte_store_loop(s))
        return 1;
    if (packed_byte_mask_loop(s))
        return 1;
    affine = cg.switch_depth ? NULL : affine_find(s);
    if (!cg.function->jump_label_count && !affine && counted_indexed_guard_loop(s)) {
        code("; loop lowering: counted indexed byte guard\n");
        return 1;
    }
    if (!affine && !cg.switch_depth && s->kind == ST_FOR && s->initial && !s->initial->next &&
        s->initial->kind == ST_EXPR && retained_countdown_for_loop(s, 1)) {
        code("; loop lowering: register countdown\n");
        return 1;
    }
    if (affine && affine->dead_index) {
        code("; eliminated induction home: %s\n", affine->index->name);
        affine_initialize_dead_index(affine);
    } else if (s->initial)
        emit_statements(s->initial);
    if (fixed_byte_copy_loop(s)) {
        code("; loop lowering: fixed byte copy\n");
        return 1;
    }
    if (affine_pair_loop(s)) {
        code("; loop lowering: paired affine stores\n");
        return 1;
    }
    if (!cg.switch_depth && affine_register_loop(s, affine)) {
        code("; loop lowering: %s register cursor\n", affine ? "affine" : "explicit");
        return 1;
    }
    if (!cg.function->jump_label_count && fixed_shift_loop(s)) {
        code("; loop lowering: fixed word shift\n");
        return 1;
    }
    if (!cg.function->jump_label_count && word_shift_scan_loop(s)) {
        code("; loop lowering: word shift scan\n");
        return 1;
    }
    if (!cg.switch_depth && !volatile_statement(s) && register_loop(s)) {
        code("; loop lowering: register loop\n");
        return 1;
    }
    if (!affine && retained_countdown_loop(s)) {
        code("; loop lowering: register countdown\n");
        return 1;
    }
    if (!cg.function->jump_label_count && !affine && counted_pointer_guard_loop(s)) {
        code("; loop lowering: counted pointer guard\n");
        return 1;
    }
    if (!cg.function->jump_label_count && !affine && pointer_scan_loop(s)) {
        code("; loop lowering: register pointer scan\n");
        return 1;
    }
    if (!cg.switch_depth && numeric_loop(s)) {
        code("; loop lowering: numeric loop\n");
        return 1;
    }
    if (structured_byte_loop(s)) {
        code("; loop lowering: structured byte loop\n");
        return 1;
    }
    if (!(affine && affine->dead_index) && retained_loop(s)) {
        code("; loop lowering: retained index\n");
        return 1;
    }
    if (!affine && dp_counter_word_fill(s)) {
        code("; loop lowering: fixed-array DP word fill\n");
        return 1;
    }
    if (!cg.switch_depth && s->kind != ST_DO && s->expression && s->expression->kind == EX_INT &&
        !s->expression->value) {
        code("; loop lowering: zero-trip elimination\n");
        return 1;
    }
    counted = (!cg.switch_depth ||
               (cg.switch_depth == 1 && cg.function->jump_label_count &&
                !dp_counter_has_jump_edge(s->initial) && !dp_counter_has_jump_edge(s->body))) &&
              !volatile_statement(s) && dp_counter_plan(s, affine, &counter);
    rotated_while = !counted && !affine && s->kind == ST_WHILE && s->expression &&
                    s->expression->kind != EX_INT && !divmod_test_produces(s->expression);
    code("; loop lowering: %s\n", counted ? (affine ? "affine cursor and DP counter" : "DP counter")
                                  : affine              ? "affine frame cursor"
                                  : bound_state.pending ? "bound register cursor"
                                                        : "generic fallback");
    start = ++cg.label;
    body = ++cg.label;
    end = ++cg.label;
    done = counted ? ++cg.label : end;
    step = s->kind == ST_WHILE ? start : ++cg.label;
    if (cg.loop_count == 64)
        error_at(s->location, "too many nested loops");
    cg.loop_start[cg.loop_count] = step;
    cg.loop_end[cg.loop_count++] = end;
    if (counted) {
        if (!counter.countdown) {
            unsigned enter = ++cg.label;
            Expr entry = *s->expression, zero = {0};
            counter.starts_zero = !affine && dp_counter_starts_zero(s, &counter, previous);
            if (counter.starts_zero) {
                zero.kind = EX_INT;
                zero.type = counter.index->type;
                zero.location = entry.location;
                entry.left = &zero;
                if (counter.bound->kind == EX_INT) {
                    entry.value = initializer_constant(&entry, 1);
                    entry.kind = EX_INT;
                }
            }
            if (counter.starts_zero && counter.bound->kind != EX_INT &&
                !body_effect(counter.bound) && !counter.wide) {
                /* The successful entry test already leaves the trip count in A */
                Type compare = common_type(entry.left->type, counter.bound->type);
                truth(counter.bound);
                flag_branch("beq", "bne", done, 0, 0);
                if (!compare.is_unsigned)
                    flag_branch("bmi", "bpl", done, 0, 0);
                counter.bound_loaded = 1;
            } else
                branch(&entry, enter, done, enter);
            label(enter);
        } else if (counter.entry_test) {
            unsigned enter = ++cg.label;
            branch(s->expression, enter, done, enter);
            label(enter);
        }
        if (affine)
            affine_initialize(affine);
        dp_counter_enter(&counter);
        bound_enter();
        if (!counter.countdown || counter.entry_test)
            jump(body);
    } else if (affine) {
        unsigned enter = ++cg.label;
        branch(s->expression, enter, end, enter);
        label(enter);
        affine_initialize(affine);
        bound_enter();
        jump(body);
    }
    if (!counted && !affine)
        bound_enter();
    divmod_state.available = 0;
    if (rotated_while) {
        if (!while_entry_true(previous, s->expression)) {
            if (while_peel_entry(s->expression)) {
                branch(s->expression, body, end, body);
                divmod_state.available = 0;
            } else
                jump(start);
        }
    } else {
        label(start);
        if (!counted) {
            if (s->kind != ST_DO && s->expression && s->expression->kind != EX_INT)
                branch(s->expression, body, end, body);
            else if (s->kind != ST_DO && s->expression && !s->expression->value)
                jump(end);
        }
    }
    label(body);
    saved_affine = cg.affine_active;
    if (affine)
        cg.affine_active = affine;
    a = emit_statements(s->body);
    if (s->kind != ST_WHILE) {
        divmod_state.available = 0;
        label(step);
    }
    if (s->step) {
        if (counted && !counter.update_index) {
            strength_update_cursors_only(s->step);
        } else if (!strength_update(s->step, 0)) {
            if (scalar_home_update(s->step, 0) ||
                (!volatile_expression(s->step) && discarded_far_update(s->step)))
                divmod_written(s->step->left);
            else
                emit_discarded(s->step);
        }
    }
    if (affine)
        affine_advance(affine);
    cg.affine_active = saved_affine;
    if (counted) {
        if (!affine && !counter.countdown && !counter.descending && !counter.wide &&
            !counter.recover_index && s->expression->left->type.is_unsigned &&
            !cg.parser->no_line_passes && !cg.parser->no_index_elimination &&
            !cg.function->jump_label_count && dp_counter_word_prefix(s->body, counter.index))
            code("; word-array loop distance fits 32768\n");
        dp_counter_step(&counter, body);
    } else if (s->kind == ST_DO)
        branch(s->expression, start, end, end);
    else if (rotated_while) {
        divmod_state.available = 0;
        label(start);
        branch(s->expression, body, end, end);
    } else if (a || s->kind == ST_FOR)
        jump(start);
    --cg.loop_count;
    divmod_state.available = 0;
    label(end);
    bound_exit();
    if (counted) {
        dp_counter_exit(&counter);
        label(done);
    }
    infinite = s->kind != ST_DO &&
               (!s->expression || (s->expression->kind == EX_INT && s->expression->value));
    if (infinite && !contains_break(s->body) && !cg.switch_depth)
        return 0;
    return 1;
}

#include "bound_cursors.inc"
#include "region_homes.inc"

/* A leading scalar guard can return without ever allocating a frame. Limit
 * inputs to one word parameter in X and a constant so the continuation keeps
 * all incoming arguments intact and no local initializer is bypassed. */
static void entry_guard(Function *f, Statement **body)
{
    Statement *s = *body, *ret;
    Expr *e, *value;
    Symbol *parameter;
    unsigned yes, no;

    if (f->symbol->param_count != 1 || f->symbol->params[0].base != TY_INT ||
        f->symbol->params[0].pointers || f->symbol->type.base != TY_INT || f->symbol->type.pointers)
        return;

    while (s && (s->kind == ST_EMPTY || (s->kind == ST_BLOCK && !s->body)))
        s = s->next;
    if (!s || s->kind != ST_IF || s->alternate || !word_comparison(s->expression))
        return;
    e = s->expression;
    parameter = leaf_parameter(f, 0);
    if (e->left->kind != EX_OBJECT || e->left->symbol != parameter || e->right->kind != EX_INT)
        return;
    ret = s->body;
    if (ret && ret->kind == ST_BLOCK)
        ret = ret->body;
    if (!ret || ret->next || ret->kind != ST_RETURN || !ret->expression)
        return;
    value = ret->expression;
    if (value->kind != EX_INT && (value->kind != EX_OBJECT || value->symbol != parameter))
        return;
    if (reg_width(value->type) != 2)
        return;
    yes = ++cg.label;
    no = ++cg.label;
    code("; entry guard before frame allocation\n    txa\n");
    word_compare_loaded(e, yes, no, yes);
    label(yes);
    if (value->kind == EX_INT)
        emit_value(value);
    else
        code("    txa\n");
    code("    rts\n");
    label(no);
    *body = s->next;
}
