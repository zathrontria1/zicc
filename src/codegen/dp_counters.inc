/* $0000-$0001 are compiler-owned and never contain a C object's home. Every
 * borrowing region saves the incoming word, including regions in handlers.
 * This permits nested regions, recursive callees and asynchronous interrupts
 * without adding $00 to the handler-wide arithmetic-scratch mask. */
static int dp_counter_modified_expr(Expr *e, Symbol *symbol)
{
    unsigned i;

    if (!e)
        return 0;
    if ((e->kind == EX_ASSIGN || e->kind == EX_PRE || e->kind == EX_POST) &&
        e->left->kind == EX_OBJECT && e->left->symbol == symbol)
        return 1;
    if (dp_counter_modified_expr(e->left, symbol) || dp_counter_modified_expr(e->right, symbol) ||
        dp_counter_modified_expr(e->third, symbol))
        return 1;

    for (i = 0; i < e->arg_count; ++i) {
        if (dp_counter_modified_expr(e->args[i], symbol))
            return 1;
    }

    return 0;
}

static int dp_counter_modified(Statement *s, Symbol *symbol)
{
    for (; s; s = s->next) {
        /* Return would bypass the region's local restore. Ordinary calls are
         * safe: callees which borrow the word obey this same save contract. */
        if (s->kind == ST_RETURN || dp_counter_modified_expr(s->expression, symbol) ||
            dp_counter_modified_expr(s->step, symbol) || dp_counter_modified(s->initial, symbol) ||
            dp_counter_modified(s->body, symbol) || dp_counter_modified(s->alternate, symbol))
            return 1;
    }

    return 0;
}

/* A named label can enter the loop without saving $00. A goto can bypass
 * its restore. Ordinary structured breaks and continues use the loop exits. */
static int dp_counter_has_jump_edge(Statement *s)
{
    for (; s; s = s->next) {
        if (s->kind == ST_GOTO || s->kind == ST_LABEL || s->kind == ST_CASE ||
            dp_counter_has_jump_edge(s->initial) || dp_counter_has_jump_edge(s->body) ||
            dp_counter_has_jump_edge(s->alternate))
            return 1;
    }

    return 0;
}

static int dp_counter_observes_expr(Expr *e, Symbol *index, AffineLoop *affine)
{
    unsigned i, delta;
    InductionCursor *cursor;

    if (!e)
        return 0;

    if (affine)
        for (i = 0; i < affine->count; ++i) {
            if (e == affine->accesses[i].address)
                return 0;
        }

    cursor = strength_pointer_plan(e, &delta);

    if (cursor && cursor->index == index && cursor->base->owner && cursor->base->type.array)
        return 0;
    if (e->kind == EX_OBJECT && e->symbol == index)
        return 1;
    if (dp_counter_observes_expr(e->left, index, affine) ||
        dp_counter_observes_expr(e->right, index, affine) ||
        dp_counter_observes_expr(e->third, index, affine))
        return 1;

    for (i = 0; i < e->arg_count; ++i) {
        if (dp_counter_observes_expr(e->args[i], index, affine))
            return 1;
    }

    return 0;
}

static int dp_counter_observes(Statement *s, Symbol *index, AffineLoop *affine)
{
    for (; s; s = s->next) {
        if (dp_counter_observes_expr(s->expression, index, affine) ||
            dp_counter_observes_expr(s->step, index, affine) ||
            dp_counter_observes(s->initial, index, affine) ||
            dp_counter_observes(s->body, index, affine) ||
            dp_counter_observes(s->alternate, index, affine))
            return 1;
    }

    return 0;
}

static int dp_counter_invariant_bound(Statement *s, Expr *e)
{
    if (!e || volatile_expression(e) || body_effect(e) || body_has_deref(e) || e->type.pointers ||
        e->type.array || e->type.base == TY_FLOAT || reg_width(e->type) > 2)
        return 0;
    if (e->kind == EX_INT)
        return 1;
    if (e->kind == EX_OBJECT)
        return loop_private(e->symbol) && !object_volatile(e->symbol->type) &&
               !scalar_writes(s->body, e->symbol) && !scalar_writes_expr(s->step, e->symbol);
    if (e->kind == EX_CAST || e->kind == EX_UNARY)
        return dp_counter_invariant_bound(s, e->left);
    if (e->kind != EX_BINARY || e->arg_count)
        return 0;

    return (basic_integer_op(e->op) || e->op == '*' || e->op == '/' || e->op == '%' ||
            e->op == TOK_SHL || e->op == TOK_SHR) &&
           dp_counter_invariant_bound(s, e->left) && dp_counter_invariant_bound(s, e->right);
}

static int dp_counter_ascending(Statement *s, AffineLoop *affine, DpCounter *counter, int inclusive)
{
    Expr *condition = s->expression, *step = s->step;
    Type t;
    uint32_t delta;

    memset(counter, 0, sizeof *counter);

    if (cg.parser->no_dp_counters || cg.parser->no_strength_reduction || s->kind != ST_FOR ||
        !step || !condition || condition->kind != EX_BINARY ||
        condition->op != (inclusive ? TOK_LE : '<') || condition->left->kind != EX_OBJECT)
        return 0;
    if (!((step->kind == EX_POST || step->kind == EX_PRE) && step->op == TOK_INC) &&
        !(step->kind == EX_ASSIGN && step->op == '+' && integer_constant(step->right, &delta) &&
          delta == 1))
        return 0;

    counter->index = condition->left->symbol;
    counter->bound = condition->right;
    t = common_type(condition->left->type, condition->right->type);
    counter->wide = t.base == TY_LONG && t.is_unsigned && counter->index->type.base == TY_LONG &&
                    counter->index->type.is_unsigned;

    if (t.pointers || (inclusive && counter->wide) ||
        (!counter->wide && (t.base != TY_INT || counter->index->type.base != TY_INT)) ||
        step->left->kind != EX_OBJECT || step->left->symbol != counter->index ||
        !loop_private(counter->index) || dp_counter_modified(s->body, counter->index))
        return 0;

    if (counter->bound->kind == EX_OBJECT) {
        Symbol *bound = counter->bound->symbol;

        if ((bound->type.base != TY_INT && (!counter->wide || bound->type.base != TY_LONG)) ||
            bound->type.pointers || (inclusive && bound == counter->index) ||
            !loop_private(bound) || dp_counter_modified(s->body, bound))
            return 0;
    } else if (counter->bound->kind != EX_INT) {
        if (counter->wide || !dp_counter_invariant_bound(s, counter->bound) ||
            loop_mentions(counter->bound, counter->index))
            return 0;
    }

    counter->update_index = dp_counter_observes(s->body, counter->index, affine);
    counter->recover_index =
        !counter->update_index && loop_accessed_outside(cg.function->body, s, counter->index, 1);

    if (counter->wide &&
        (affine || cg.function->jump_label_count || cg.stack_leaf || counter->update_index ||
         counter->recover_index || !direct_operand(condition->left, t, 1, 0)))
        return 0;

    counter->inclusive = inclusive;
    counter->wrap_at_limit = inclusive;
    return 1;
}

static int dp_counter_shape(Statement *s, AffineLoop *affine, DpCounter *counter)
{
    return dp_counter_ascending(s, affine, counter, 0);
}

static Symbol *post_test_countdown(Statement *s)
{
    Expr *step = s->expression;
    Symbol *index;
    uint32_t zero;

    if (s->kind != ST_DO || !step || cg.function->jump_label_count)
        return NULL;
    if (step->kind == EX_BINARY && (step->op == TOK_NE || step->op == '>') &&
        integer_constant(step->right, &zero) && !zero)
        step = step->left;
    if (step->kind == EX_CAST && word_integer(step->type) && step->left->type.base == TY_CHAR &&
        step->left->type.is_unsigned && !step->left->type.pointers)
        step = step->left;
    if (step->kind != EX_PRE || step->op != TOK_DEC || step->left->kind != EX_OBJECT)
        return NULL;

    index = step->left->symbol;

    if ((index->type.base != TY_INT && index->type.base != TY_CHAR) || !index->type.is_unsigned ||
        index->type.is_bool || index->type.pointers || object_volatile(index->type) ||
        !loop_private(index) || statement_references(s->body, index) ||
        dp_counter_modified(s->body, index))
        return NULL;

    return index;
}

static int for_countdown_nonneg_init(Statement *s, Symbol *index)
{
    Statement *init = body_single(s->initial);
    Expr *e = init && !init->next && init->kind == ST_EXPR ? init->expression : NULL;
    uint32_t v;

    if (!e || e->kind != EX_ASSIGN || e->op || e->left->kind != EX_OBJECT ||
        e->left->symbol != index)
        return 0;
    if (integer_constant(e->right, &v))
        return v <= 32767u;

    return e->right->known.valid && e->right->known.min >= 0;
}

static Symbol *for_countdown_index(Statement *s, int *signed_gt_zero)
{
    Expr *test = s->expression, *step = s->step;
    Symbol *index;
    uint32_t zero, delta;
    int gt_zero = 0;

    if (signed_gt_zero)
        *signed_gt_zero = 0;
    if (s->kind != ST_FOR || !test || !step || cg.function->jump_label_count)
        return NULL;

    if (test->kind == EX_BINARY && (test->op == TOK_NE || test->op == '>') &&
        integer_constant(test->right, &zero) && !zero) {
        if (test->op == '>')
            gt_zero = 1;

        test = test->left;
    }

    while (test->kind == EX_CAST && word_integer(test->type) &&
           (test->left->type.base == TY_CHAR || test->left->type.base == TY_INT) &&
           !test->left->type.pointers) {
        test = test->left;
    }

    if (test->kind != EX_OBJECT)
        return NULL;

    index = test->symbol;

    if (!(((step->kind == EX_PRE || step->kind == EX_POST) && step->op == TOK_DEC) ||
          (step->kind == EX_ASSIGN && step->op == '-' && integer_constant(step->right, &delta) &&
           delta == 1)) ||
        step->left->kind != EX_OBJECT || step->left->symbol != index)
        return NULL;
    if ((index->type.base != TY_INT && index->type.base != TY_CHAR) || index->type.is_bool ||
        index->type.pointers || object_volatile(index->type) || !loop_private(index) ||
        statement_references(s->body, index) || dp_counter_modified(s->body, index))
        return NULL;
    if (!index->type.is_unsigned && !gt_zero &&
        !(s->expression->known.valid && s->expression->known.min >= 0) &&
        !for_countdown_nonneg_init(s, index))
        return NULL;
    if (signed_gt_zero)
        *signed_gt_zero = gt_zero && !index->type.is_unsigned;

    return index;
}

static int dp_counter_countdown(Statement *s, AffineLoop *affine, DpCounter *counter)
{
    Symbol *index;
    int signed_gt_zero = 0;

    if (cg.parser->no_dp_counters || cg.parser->no_strength_reduction || affine)
        return 0;

    if ((index = post_test_countdown(s)) != NULL) {
        if (index->type.base != TY_INT)
            return 0;

        counter->index = index;
        counter->countdown = 1;
        counter->recover_index = loop_accessed_outside(cg.function->body, s, index, 1);
        return 1;
    }

    if ((index = for_countdown_index(s, &signed_gt_zero)) != NULL && !signed_gt_zero) {
        counter->index = index;
        counter->countdown = 1;
        counter->entry_test = 1;
        counter->recover_index = loop_accessed_outside(cg.function->body, s, index, 1);
        return 1;
    }

    return 0;
}

/* Count the distance to a signed lower bound once. For an inclusive
 * INT_MIN bound the original word loop wraps and keeps running. */
static int dp_counter_descending(Statement *s, AffineLoop *affine, DpCounter *counter)
{
    Expr *test = s->expression, *step = s->step, *bound;
    Symbol *index;
    Type t;
    uint32_t delta;

    if (cg.parser->no_dp_counters || cg.parser->no_strength_reduction ||
        cg.function->jump_label_count || s->kind != ST_FOR || !step || !test ||
        test->kind != EX_BINARY || (test->op != '>' && test->op != TOK_GE) ||
        test->left->kind != EX_OBJECT)
        return 0;
    if (!((step->kind == EX_POST || step->kind == EX_PRE) && step->op == TOK_DEC) &&
        !(step->kind == EX_ASSIGN && step->op == '-' && integer_constant(step->right, &delta) &&
          delta == 1))
        return 0;

    index = test->left->symbol;
    bound = test->right;
    t = common_type(test->left->type, bound->type);

    if (t.base != TY_INT || t.is_unsigned || t.pointers || index->type.base != TY_INT ||
        index->type.is_unsigned || index->type.pointers || step->left->kind != EX_OBJECT ||
        step->left->symbol != index || lftr_dead(index) || !loop_private(index) ||
        dp_counter_modified(s->body, index))
        return 0;

    if (bound->kind == EX_OBJECT) {
        if (bound->symbol == index || bound->type.base != TY_INT || bound->type.pointers ||
            !loop_private(bound->symbol) || dp_counter_modified(s->body, bound->symbol))
            return 0;
    } else if (bound->kind != EX_INT)
        return 0;

    if (!direct_operand(bound, t, 0, 0))
        return 0;

    counter->index = index;
    counter->bound = bound;
    counter->descending = 1;
    counter->inclusive = test->op == TOK_GE;
    counter->wrap_at_limit =
        counter->inclusive && (!bound->known.valid || bound->known.min <= -32768);
    counter->update_index = dp_counter_observes(s->body, index, affine);

    /* A retained signed index already supplies the test against zero */
    if (counter->update_index && !affine && counter->inclusive && bound->kind == EX_INT &&
        !bound->value)
        return 0;

    counter->recover_index =
        !counter->update_index && loop_accessed_outside(cg.function->body, s, index, 1);
    return 1;
}

static int dp_counter_plan(Statement *s, AffineLoop *affine, DpCounter *counter)
{
    Expr *condition = s->expression;
    Type t;

    if (s->kind == ST_DO)
        return dp_counter_countdown(s, affine, counter);
    if (dp_counter_countdown(s, affine, counter))
        return 1;
    if (dp_counter_descending(s, affine, counter))
        return 1;
    if (!dp_counter_shape(s, affine, counter))
        return 0;

    t = common_type(condition->left->type, condition->right->type);

    /* A discarded step leaves the updated index in A for a following CMP.
     * When C still needs that index and ordering is unsigned, replacing the
     * immediate test with a second memory counter costs more every trip. */
    if (!counter->wide && counter->update_index && !cg.parser->no_line_passes &&
        counter->bound->kind == EX_INT &&
        (t.is_unsigned || (condition->left->known.valid && condition->left->known.min >= 0 &&
                           condition->right->known.valid && condition->right->known.min >= 0)))
        return 0;

    /* A body exit can leave the setup and restore cost unamortized */
    if (!affine && !counter->wide && counter->update_index && contains_break(s->body))
        return 0;

    /* A plain DP-home step/test also beats save/setup/restore on short loops */
    if (dp_state.homes && s->initial && region_trips(s) <= 3)
        return 0;

    return 1;
}

static int dp_counter_word_access(Expr *e, Symbol *index)
{
    if (!e || e->kind == EX_ADDRESS)
        return 0;

    if (e->kind == EX_DEREF) {
        Expr *address = e->left;

        if (address->kind == EX_BINARY && address->op == '+' && address->left->type.array &&
            address->left->type.array <= 32768 &&
            width(pointed_type(value_type(address->left->type))) == 2 &&
            address->right->kind == EX_OBJECT && address->right->symbol == index)
            return 1;
    }

    if (dp_counter_word_access(e->left, index))
        return 1;
    if (e->kind == EX_CHOOSE || (e->kind == EX_BINARY && (e->op == TOK_LAND || e->op == TOK_LOR)))
        return 0;

    return dp_counter_word_access(e->right, index);
}

static int dp_counter_word_prefix(Statement *s, Symbol *index)
{
    /* Find an access each continuing iteration has to evaluate */
    for (; s; s = s->next) {
        if (s->kind == ST_BLOCK)
            return dp_counter_word_prefix(s->body, index);
        if (s->kind != ST_EXPR && s->kind != ST_EMPTY)
            return 0;
        if (dp_counter_word_access(s->expression, index))
            return 1;
    }

    return 0;
}

/* The entry comparison has proved bound > index in unsigned long arithmetic.
 * The low word counts the first chunk (zero represents 65536). The stacked
 * high word counts the full chunks after it. Only a chunk boundary needs to
 * inspect the high word, including when a signed bound widened to $FFFFxxxx. */
static void dp_counter_enter_wide(DpCounter *counter, Expr *index)
{
    Type t = index->type;

    convert_registers(counter->bound->type, t);
    code("    sec\n    sbc ");
    direct_operand(index, t, 0, 1);
    code("\n    sta z:$0000\n    txa\n    sbc ");
    direct_operand(index, t, 1, 1);
    code("\n    tax\n    lda z:$0000\n    bne :+\n    dex\n:\n    phx\n");
}

static int dp_counter_starts_zero(Statement *s, DpCounter *counter, Statement *previous)
{
    Statement *initial = body_single(s->initial);
    Expr *store;
    uint32_t value;

    if (!initial && previous && previous->next == s)
        initial = previous;

    store = initial ? initial->expression : NULL;
    return !counter->wide && !counter->descending && initial &&
           (!initial->next || initial == previous) && initial->kind == ST_EXPR && store &&
           store->kind == EX_ASSIGN && !store->op && store->left->kind == EX_OBJECT &&
           store->left->symbol == counter->index && integer_constant(store->right, &value) &&
           !value;
}

static void dp_counter_enter(DpCounter *counter)
{
    Expr index = {0};

    index.kind = EX_OBJECT;
    index.symbol = counter->index;
    index.type = counter->index->type;
    code("; saved %sDP counter: %s, %s C index\n", counter->wide ? "wide " : "",
         counter->index->name,
         counter->update_index    ? "maintained"
         : counter->recover_index ? "recoverable"
                                  : "dead");
    code("    pei ($00)\n");

    if (cg.stack_leaf)
        cg.stack_bias += 2;
    if (counter->countdown) {
        load_symbol(counter->index);
        code("    sta z:$0000\n");
        return;
    }

    if (counter->descending) {
        load_symbol(counter->index);
        code("    sec\n    sbc ");

        if (!direct_operand(counter->bound, index.type, 0, 1))
            error_at(here(cg.parser), "DP counter requires a bound operand");

        code("\n");

        if (counter->inclusive)
            code("    inc a\n");

        code("    sta z:$0000\n");
        return;
    }

    if (!counter->bound_loaded)
        emit_value(counter->bound);
    if (counter->wide) {
        dp_counter_enter_wide(counter, &index);
        return;
    }

    if (!counter->starts_zero) {
        code("    sec\n    sbc ");

        if (!direct_operand(&index, index.type, 0, 1))
            error_at(here(cg.parser), "DP counter requires an index home");

        code("\n");
    }

    if (counter->inclusive)
        code("    inc a\n");

    code("    sta z:$0000\n");
}

static void dp_counter_step(DpCounter *counter, unsigned body)
{
    code("    dec z:$0000\n    beq :+\n");
    jump(body);
    code(":\n");

    if (counter->wide) {
        code("    lda 1,s\n    beq :+\n    dec a\n    sta 1,s\n");
        jump(body);
        code(":\n");
    }

    if (counter->wrap_at_limit) {
        Type compare = common_type(counter->index->type, counter->bound->type);

        unsigned limit = counter->descending ? 0x8000 : compare.is_unsigned ? 0xffff : 0x7fff;
        emit_value(counter->bound);
        code("    cmp #$%04X\n    bne :+\n", limit);
        jump(body);
        code(":\n");
    }
}

static void dp_counter_exit(DpCounter *counter)
{
    if (counter->wide)
        code("    pla\n");

    if (counter->recover_index) {
        if (counter->countdown)
            code("    lda z:$0000\n");
        else if (counter->descending) {
            emit_value(counter->bound);
            code("    clc\n    adc z:$0000\n");

            if (counter->inclusive)
                code("    dec a\n");
        } else {
            emit_value(counter->bound);
            code("    sec\n    sbc z:$0000\n");

            if (counter->inclusive)
                code("    inc a\n");
        }

        store_symbol(counter->index);
        strength_sync(counter->index, NULL);
    }

    code("    pla\n    sta z:$0000\n");

    if (cg.stack_leaf)
        cg.stack_bias -= 2;
}

/* A single fixed-array word store can use X for the byte displacement
 * and the saved DP word for the trip count. No subscript rebuild is needed. */
static int dp_counter_word_fill(Statement *s)
{
    Statement *body = s->body;
    Expr *test = s->expression, *assignment;
    DpCounter counter;
    IndexedOperand operand;

    unsigned scale, offset, enter, loop, done;
    uint32_t value;

    if (s->kind != ST_FOR || !test || cg.switch_depth || cg.stack_leaf || bound_state.cursor ||
        bound_state.pending || cg.retained_index || cg.parser->no_body_optimizations ||
        cg.parser->no_register_loops || cg.parser->no_register_cursors || volatile_statement(s))
        return 0;

    while (body && body->kind == ST_BLOCK && !body->next && !body->inline_callee) {
        body = body->body;
    }

    if (!body || body->kind != ST_EXPR || body->next)
        return 0;

    assignment = body->expression;

    if (!assignment || assignment->kind != EX_ASSIGN || assignment->op ||
        width(assignment->left->type) != 2 || !integer_constant(assignment->right, &value) ||
        !indexed_operand(assignment->left, &operand) || operand.scale != 2 ||
        !dp_counter_ascending(s, NULL, &counter, test->kind == EX_BINARY && test->op == TOK_LE) ||
        counter.wide || lftr_dead(counter.index) ||
        !retained_affine_for(operand.index, counter.index, &scale, &offset) || scale != 1 ||
        offset || !direct_operand(test->left, counter.index->type, 0, 0))
        return 0;

    counter.update_index = 0;
    counter.recover_index = loop_accessed_outside(cg.function->body, s, counter.index, 1);
    enter = ++cg.label;
    loop = ++cg.label;
    done = ++cg.label;
    branch(test, enter, done, enter);
    label(enter);
    dp_counter_enter(&counter);
    code("; fixed-array word fill\n");
    load_symbol(counter.index);
    code("    asl a\n    tax\n");
    label(loop);

    if (value & 65535)
        code("    lda #$%04X\n    sta ", (unsigned)value & 65535);
    else
        code("    stz ");

    indexed_text(&operand);
    code("\n    inx\n    inx\n");
    dp_counter_step(&counter, loop);
    dp_counter_exit(&counter);
    label(done);
    divmod_state.available = 0;
    return 1;
}
