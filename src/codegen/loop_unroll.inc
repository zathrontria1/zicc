/* Costed straight-line affine regions. All costs are estimates in SNES master
 * clocks with FastROM fetches and WRAM data; final selection remains bounded by
 * code size. The scalar path preserves ordering for aliased, reloadable values. */
enum {
    UNROLL_BYTE_BUDGET = 128,
    UNROLL_FULL_LIMIT = 32,
    UNROLL_RUNTIME_TRIPS = 32,
    UNROLL_SIZE_WEIGHT = 2,
    UNROLL_MIN_GAIN = 5
};

static int unroll_value(Expr *e, int *hoist, Symbol *index)
{
    if (e->kind == EX_INT) {
        *hoist = 1;
        return 1;
    }
    if (e->kind == EX_OBJECT && !e->type.array) {
        *hoist = e->symbol != index && loop_private(e->symbol);
        return 1;
    }
    if (e->kind == EX_CAST && numeric(e->type) && numeric(e->left->type) &&
        e->type.base != TY_FLOAT && e->left->type.base != TY_FLOAT)
        return unroll_value(e->left, hoist, index);

    return 0;
}

static int unroll_span(AffineLoop *loop, unsigned *span)
{
    Statement *initial = loop->statement->initial;
    Expr *e;
    uint32_t start, end;
    Type t;

    while (initial && initial->kind == ST_BLOCK && !initial->next) {
        initial = initial->body;
    }

    if (!initial || initial->next || initial->kind != ST_EXPR)
        return 0;

    e = initial->expression;

    if (e->kind != EX_ASSIGN || e->op || e->left->kind != EX_OBJECT ||
        e->left->symbol != loop->index || !integer_constant(e->right, &start) ||
        !integer_constant(loop->statement->expression->right, &end))
        return 0;

    t = common_type(loop->statement->expression->left->type,
                    loop->statement->expression->right->type);

    if (t.is_unsigned)
        *span = (uint16_t)start < (uint16_t)end ? (uint16_t)end - (uint16_t)start : 0;
    else
        *span = (int16_t)start < (int16_t)end ? (unsigned)((int16_t)end - (int16_t)start) : 0;

    return 1;
}

static unsigned unroll_advance_cost(unsigned stride)
{
    return stride <= 3 ? 12 * stride : 54;
}

static unsigned unroll_load_cost(Expr *e, unsigned width)
{
    unsigned cost = e->kind == EX_INT ? (width == 4 ? 36 : 18) : (width == 4 ? 100 : 40);

    if (e->kind == EX_CAST)
        cost += 24;

    return width == 4 ? cost + 100 : cost;
}

static int unroll_plan(AffineLoop *loop, Expr *assignment, UnrollPlan *plan)
{
    unsigned factor, n, store, load, index, advance, body_bytes, best, score, bytes, cost, groups,
        tail, casts = 0, value_bytes, rolled_bytes;
    Expr *value = assignment->right;
    UnrollPlan candidate;
    int hoist;

    memset(plan, 0, sizeof *plan);

    /* Unrolling removes the countdown: its eligibility must not depend on
     * whether a runtime DP counter beats an ordinary step-and-test. */
    if (cg.parser->no_loop_unroll || !dp_counter_shape(loop->statement, loop, &plan->counter) ||
        !unroll_value(assignment->right, &hoist, loop->index))
        return 0;

    while (value->kind == EX_CAST) {
        if (++casts > 4)
            return 0;

        value = value->left;
    }

    plan->width = width(assignment->type);
    plan->stride = loop->accesses[0].stride;
    plan->hoist = hoist;

    if ((plan->width != 1 && plan->width != 2 && plan->width != 4) || !plan->stride ||
        plan->stride > 32767)
        return 0;

    plan->known = unroll_span(loop, &plan->span);

    if (plan->known && !plan->span) {
        plan->full = 1;
        return 1;
    }

    n = plan->known ? plan->span : UNROLL_RUNTIME_TRIPS;
    store = plan->width == 4 ? 160 : plan->width == 1 ? 32 : 40;
    load = unroll_load_cost(value, plan->width) + 24 * casts;
    value_bytes = 3 + 8 * casts;
    index = plan->counter.update_index ? 94 : 0;
    advance = unroll_advance_cost(plan->stride);
    body_bytes = (plan->width == 4 ? 12 : 3) + (plan->counter.update_index ? 7 : 0);
    /* Borrowing, the scalar tail, split/shift handling and long branches are
     * charged explicitly. Two clocks per extra byte discourage marginal growth. */
    plan->rolled = 160 + n * (load + store + index + advance + 50);

    if (plan->width == 1)
        plan->rolled += n * 48;

    rolled_bytes = (plan->width == 4   ? 80
                    : plan->width == 1 ? 40
                                       : 32) +
                   (plan->counter.update_index ? 7 : 0);
    best = plan->rolled + UNROLL_SIZE_WEIGHT * rolled_bytes;
    candidate = *plan;

    for (factor = 2; factor <= 16; factor *= 2) {
        if (plan->known && factor > n)
            break;
        if (factor * plan->stride > 65534)
            continue;

        groups = n / factor;
        tail = n % factor;
        bytes = 56 + factor * body_bytes + (plan->hoist ? value_bytes : value_bytes * factor) +
                (plan->width == 4 ? 30 : 16);

        if (plan->width == 1)
            bytes += 8;
        if (bytes > UNROLL_BYTE_BUDGET)
            continue;

        cost =
            360 +
            groups * (factor * (store + index) + (plan->hoist ? load : factor * load) + 54 + 50) +
            tail * (load + store + index + advance + 50);

        if (plan->width == 1)
            cost += groups * 48 + tail * 48;
        if (factor * body_bytes > 100)
            cost += groups * 18;

        score = cost + UNROLL_SIZE_WEIGHT * bytes;

        if (score < best && cost < plan->rolled - plan->rolled * UNROLL_MIN_GAIN / 100) {
            candidate = *plan;
            candidate.factor = factor;
            candidate.bytes = bytes;
            candidate.cost = cost;
            best = score;
        }
    }

    if (plan->known && n <= UNROLL_FULL_LIMIT && (n - 1) * plan->stride + plan->width <= 65535) {
        bytes = n * body_bytes + (plan->hoist ? value_bytes : value_bytes * n) +
                (plan->width == 4 ? 20 : 8);
        cost = n * (store + index) + (plan->hoist ? load : n * load) + (plan->width == 1 ? 48 : 0);
        score = cost + UNROLL_SIZE_WEIGHT * bytes;

        if (bytes <= UNROLL_BYTE_BUDGET && score < best) {
            candidate = *plan;
            candidate.full = 1;
            candidate.factor = n;
            candidate.bytes = bytes;
            candidate.cost = cost;
            best = score;
        }
    }

    if (!candidate.factor)
        return 0;

    *plan = candidate;
    return 1;
}

static void unroll_stage_value(Expr *value, unsigned width)
{
    if (width == 4) {
        code("    phx\n");
        emit_value(value);
        stage(0, value->type);
        code("    plx\n");
    } else
        emit_value(value);
}

static void unroll_copies(UnrollPlan *plan, Expr *value, unsigned count)
{
    unsigned i, offset;
    int byte_region = plan->width == 1 && plan->hoist && !plan->counter.update_index;

    if (plan->hoist)
        unroll_stage_value(value, plan->width);
    if (byte_region)
        code("    sep #$20\n.a8\n");

    for (i = 0; i < count; ++i) {
        offset = i * plan->stride;

        if (!plan->hoist)
            unroll_stage_value(value, plan->width);

        if (plan->width == 4) {
            code("    lda z:__arith_lhs\n    sta a:$%04X,x\n    lda z:__arith_lhs+2\n    sta "
                 "a:$%04X,x\n",
                 offset, offset + 2);
        } else {
            if (plan->width == 1 && !byte_region)
                code("    sep #$20\n.a8\n");

            code("    sta a:$%04X,x\n", offset);

            if (plan->width == 1 && !byte_region)
                code("    rep #$20\n.a16\n");
        }

        if (plan->counter.update_index) {
            load_symbol(plan->counter.index);
            code("    inc a\n");
            store_symbol(plan->counter.index);
        }
    }

    if (byte_region)
        code("    rep #$20\n.a16\n");
}

static void unroll_advance(unsigned stride)
{
    unsigned i;

    if (stride <= 3) {
        for (i = 0; i < stride; ++i) {
            code("    inx\n");
        }
    } else {
        code("    txa\n");
        strength_adjust(stride);
        code("    tax\n");
    }
}

static int unroll_loop(AffineLoop *loop, Expr *assignment)
{
    UnrollPlan plan;

    unsigned enter, done, group, scalar, scalar_body, finish, factor;

    if (!loop->unroll_selected)
        return 0;

    plan = loop->unroll;

    if (plan.full && !plan.span) {
        code("; cost unroll: empty constant span\n");
        divmod_state.available = 0;
        return 1;
    }

    code("; cost unroll: %s, factor %u, %s span, estimated clocks %u vs %u, bytes %u\n",
         plan.full ? "full" : "partial", plan.factor, plan.known ? "constant" : "runtime",
         plan.cost, plan.rolled, plan.bytes);
    enter = ++cg.label;
    done = ++cg.label;

    if (!plan.full) {
        branch(loop->statement->expression, enter, done, enter);
        label(enter);
    }

    if (!plan.full)
        dp_counter_enter(&plan.counter);

    affine_unroll_initialize(loop, 1);
    code("; affine register cursor: X, stride %u\n", plan.stride);

    if (plan.full) {
        unroll_copies(&plan, assignment->right, plan.span);

        if (plan.counter.recover_index) {
            emit_value(plan.counter.bound);
            store_symbol(plan.counter.index);
        }
    } else {
        code("    lda z:$0000\n");
        group = ++cg.label;
        scalar = ++cg.label;
        scalar_body = ++cg.label;
        finish = ++cg.label;
        factor = plan.factor;
        code("    cmp #$%04X\n    bcs :+\n", factor);
        jump(scalar);
        code(":\n");
        code("    and #$%04X\n    pha\n    lda z:$0000\n", factor - 1);

        while (factor > 1) {
            code("    lsr a\n");
            factor >>= 1;
        }

        code("    sta z:$0000\n");
        label(group);
        unroll_copies(&plan, assignment->right, plan.factor);
        unroll_advance(plan.factor * plan.stride);
        code("    dec z:$0000\n    beq :+\n");
        jump(group);
        code(":\n    pla\n    sta z:$0000\n    bne :+\n");
        jump(finish);
        code(":\n");
        label(scalar);

        if (plan.hoist && plan.width <= 2 && plan.stride <= 3 && !plan.counter.update_index) {
            emit_value(assignment->right);
            label(scalar_body);

            if (plan.width == 1)
                code("    sep #$20\n.a8\n");

            code("    sta a:$0000,x\n");

            if (plan.width == 1)
                code("    rep #$20\n.a16\n");
        } else {
            label(scalar_body);
            unroll_copies(&plan, assignment->right, 1);
        }

        unroll_advance(plan.stride);
        code("    dec z:$0000\n    beq :+\n");
        jump(scalar_body);
        code(":\n");
        label(finish);
        dp_counter_exit(&plan.counter);
    }

    if ((plan.counter.update_index || (plan.full && plan.counter.recover_index)) &&
        loop_observed_outside(cg.function->body, loop->statement, loop->index))
        strength_sync(loop->index, NULL);

    label(done);
    divmod_state.available = 0;
    return 1;
}
