/* A whole-function leaf consumes X/A once to form a near cursor. Eligibility
 * comes from the selected full-unroll region, never names or array dimensions.
 * All arithmetic is modulo the near-pointer width and uses the word selector. */
static Statement *entry_cursor_skip_empty(Statement *s)
{
    while (s && (s->kind == ST_EMPTY || (s->kind == ST_BLOCK && !s->body))) {
        s = s->next;
    }

    return s;
}

static int entry_cursor_scalar(AffineLoop *loop, Expr *e, Symbol *scalar, unsigned start,
                               Symbol *outer, unsigned outer_start, unsigned *coefficient,
                               unsigned *constant)
{
    unsigned lc, lv, rc, rv;
    uint32_t value;

    if (integer_constant(e, &value)) {
        *coefficient = 0;
        *constant = value & 65535;
        return 1;
    }
    if (e->kind == EX_OBJECT && e->symbol == outer) {
        *coefficient = 0;
        *constant = outer_start;
        return 1;
    }
    if (e->kind == EX_OBJECT && (e->symbol == loop->index || e->symbol == scalar)) {
        *coefficient = e->symbol == scalar;
        *constant = e->symbol == loop->index ? start : 0;
        return 1;
    }
    if (e->kind == EX_CAST && same_value_representation(e->type, e->left->type))
        return entry_cursor_scalar(loop, e->left, scalar, start, outer, outer_start, coefficient,
                                   constant);
    if (word_left_shift_factor(e, &value) &&
        entry_cursor_scalar(loop, e->left, scalar, start, outer, outer_start, &lc, &lv)) {
        *coefficient = (lc * value) & 65535;
        *constant = (lv * value) & 65535;
        return 1;
    }
    if (e->kind != EX_BINARY ||
        !entry_cursor_scalar(loop, e->left, scalar, start, outer, outer_start, &lc, &lv) ||
        !entry_cursor_scalar(loop, e->right, scalar, start, outer, outer_start, &rc, &rv))
        return 0;
    if (e->op == '+' || e->op == '-') {
        *coefficient = (lc + (e->op == '+' ? rc : 0u - rc)) & 65535;
        *constant = (lv + (e->op == '+' ? rv : 0u - rv)) & 65535;
        return 1;
    }
    if (e->op == '*' && (!lc || !rc)) {
        *coefficient = (lc * rv + rc * lv) & 65535;
        *constant = (lv * rv) & 65535;
        return 1;
    }

    return 0;
}

static int entry_cursor_address(AffineLoop *loop, Expr *e, Symbol *base, Symbol *scalar,
                                unsigned start, Symbol *outer, unsigned outer_start,
                                unsigned *coefficient, unsigned *constant)
{
    unsigned c, v, scale;

    if (far_pointer(value_type(e->type)))
        return 0;
    if (e->kind == EX_OBJECT && e->symbol == base)
        return 1;
    if (e->kind == EX_DEREF && e->type.array)
        return entry_cursor_address(loop, e->left, base, scalar, start, outer, outer_start,
                                    coefficient, constant);
    if (e->kind != EX_BINARY || (e->op != '+' && e->op != '-') ||
        !value_type(e->left->type).pointers ||
        !entry_cursor_address(loop, e->left, base, scalar, start, outer, outer_start, coefficient,
                              constant) ||
        !entry_cursor_scalar(loop, e->right, scalar, start, outer, outer_start, &c, &v))
        return 0;

    scale = width(pointed_type(value_type(e->left->type)));

    if (!scale || scale > 65534)
        return 0;
    if (e->op == '-')
        scale = 0u - scale;

    *coefficient = (*coefficient + c * scale) & 65535;
    *constant = (*constant + v * scale) & 65535;
    return 1;
}

/* kind: immediate, incoming stack object, or A (formal 1). No helper may
 * run between preserving the incoming value and forming the cursor. */
static int entry_cursor_value(Function *f, Expr *e, unsigned size, unsigned *offset,
                              unsigned *literal, int *kind)
{
    uint32_t value;
    int parameter;

    unsigned i;

    if (integer_constant(e, &value)) {
        *literal = value;
        *kind = 1;
        return 1;
    }

    while (e->kind == EX_CAST && numeric(e->type) && numeric(e->left->type) &&
           e->type.base != TY_FLOAT && e->left->type.base != TY_FLOAT && width(e->type) >= size &&
           width(e->left->type) >= size) {
        e = e->left;
    }

    if (e->kind != EX_OBJECT || !numeric(e->type) || e->type.base == TY_FLOAT || e->type.pointers ||
        width(e->type) < size || (parameter = loop_parameter(f, e->symbol)) < 1 ||
        !loop_private(e->symbol))
        return 0;
    if (parameter == 1 && register_parameter(parameter, e->type)) {
        if (reg_width(e->type) != 2 || size == 4)
            return 0;

        *kind = 2;
        return 1;
    }

    *offset = 3;
    *kind = 0;
    for (i = 0; i < (unsigned)parameter; ++i) {
        if (!register_parameter(i, f->symbol->params[i]))
            *offset += reg_width(f->symbol->params[i]);
    }

    return *offset + size - 1 <= 255;
}

static void entry_cursor_load(unsigned offset, unsigned literal, int kind, unsigned high)
{
    if (kind == 1)
        code("    lda #$%04X\n", (literal >> (high * 8)) & 65535);
    else if (kind == 2)
        code("    lda z:__arith_lhs\n");
    else
        code("    lda %u,s\n", offset + high);
}

static int entry_cursor_leaf(Function *f)
{
    Statement *s = f->body, *tail;
    Symbol *fn = f->symbol, *base, *scalar;
    AffineLoop *loop;
    Expr *assignment, *initial;
    uint32_t start;
    WordScale scale;
    WordScaleEmission emission = {0};

    unsigned coefficient = 0, constant = 0, offset = 0, literal = 0, i, size;
    int immediate = 0, returns_index = 0;

    if (fn->interrupt || fn->variadic || (fn->type.base != TY_VOID && fn->type.base != TY_INT) ||
        fn->type.pointers || fn->param_count < 2)
        return 0;
    if (s->kind == ST_BLOCK)
        s = s->body;

    s = entry_cursor_skip_empty(s);

    if (!s || s->kind != ST_FOR)
        return 0;

    tail = entry_cursor_skip_empty(s->next);

    if (tail && (tail->kind != ST_RETURN || entry_cursor_skip_empty(tail->next)))
        return 0;

    loop = affine_find(s);

    if (fn->type.base == TY_INT) {
        if (!loop || !tail || !tail->expression || tail->expression->kind != EX_OBJECT ||
            tail->expression->symbol != loop->index)
            return 0;

        returns_index = 1;
    } else if (tail && tail->expression)
        return 0;

    if (!loop || !loop->unroll_selected || !loop->unroll.full || !loop->unroll.hoist ||
        loop->unroll.counter.update_index ||
        (loop->unroll.counter.recover_index && !returns_index) || !loop->index->scope ||
        !(assignment = affine_register_assignment(loop)) || !numeric(assignment->type) ||
        assignment->type.base == TY_FLOAT || assignment->type.pointers ||
        assignment->left->type.banked || !(initial = affine_initial(loop)) ||
        !integer_constant(initial->right, &start))
        return 0;

    base = leaf_parameter(f, 0);
    scalar = leaf_parameter(f, 1);

    if (!base || !scalar || !base->type.pointers || far_pointer(base->type) ||
        reg_width(base->type) != 2 || scalar->type.base != TY_INT || scalar->type.pointers ||
        width(scalar->type) != 2 || !loop_private(base) || !loop_private(scalar) ||
        !entry_cursor_address(loop, loop->accesses[0].address, base, scalar, start & 65535, NULL, 0,
                              &coefficient, &constant) ||
        !entry_cursor_value(f, assignment->right, loop->unroll.width, &offset, &literal,
                            &immediate) ||
        (coefficient && !word_scale_plan(coefficient, 1, &scale)))
        return 0;

    code(".segment \"CODE\"\n.export _%s\n_%s:\n", fn->asm_name, fn->asm_name);
    code("; entry-only cursor leaf: no frame, X base + A * %u + %u\n", coefficient, constant);
    code("; eliminated induction home: %s\n", loop->index->name);
    code("; cost unroll: full, factor %u, constant span, bytes %u\n", loop->unroll.span,
         loop->unroll.bytes);

    if (loop->unroll.span) {
        size = loop->unroll.width;

        if (immediate == 2) {
            cg.arithmetic = 1;
            code("    sta z:__arith_lhs\n");
        }

        if (coefficient) {
            cg.arithmetic = 1;

            if (word_scale_needs_base(&scale))
                code("    sta z:__arith_rhs\n");

            emission.scratch = 1;
            word_scale_steps(&scale, word_scale_emit, &emission);
            code("    stx z:__arith_rhs\n    clc\n    adc z:__arith_rhs\n");
        } else if (constant)
            code("    txa\n");

        if (coefficient || constant) {
            strength_adjust(constant);
            code("    tax\n");
        }

        code("; affine loop: %s, known initial index, direct X\n", loop->index->name);
        code("; affine register cursor: X, stride %u\n", loop->unroll.stride);

        if (size != 4)
            entry_cursor_load(offset, literal, immediate, 0);
        if (size == 1)
            code("    sep #$20\n.a8\n");

        for (i = 0; i < loop->unroll.span; ++i) {
            if (size == 4)
                entry_cursor_load(offset, literal, immediate, 0);

            code("    sta a:$%04X,x\n", i * loop->unroll.stride);

            if (size == 4) {
                entry_cursor_load(offset, literal, immediate, 2);
                code("    sta a:$%04X,x\n", i * loop->unroll.stride + 2);
            }
        }

        if (size == 1)
            code("    rep #$20\n.a16\n");
    }

    if (returns_index)
        code("; visible final index: constant recovery\n    lda #$%04X\n",
             (start + loop->unroll.span) & 65535);

    code("    rts\n__size_%s = * - _%s\n", fn->asm_name, fn->asm_name);
    return 1;
}

/* Bounded rectangular regions retain source iteration order. The inner loop
 * has already passed affine, alias, width and full-unroll selection. */
static int entry_cursor_nested_leaf(Function *f)
{
    Statement *outer = f->body, *inner, *tail;
    Symbol *fn = f->symbol, *base;
    AffineLoop *loop, shape;
    DpCounter counter;
    Expr *assignment, *initial;
    uint32_t outer_start, inner_start;

    unsigned rows, offset = 0, literal = 0, size, bytes, r, i, c, constants[32];
    int kind = 0;

    if (fn->interrupt || fn->variadic || fn->type.base != TY_VOID || fn->type.pointers ||
        fn->param_count < 2)
        return 0;
    if (outer->kind == ST_BLOCK)
        outer = outer->body;

    outer = entry_cursor_skip_empty(outer);

    if (!outer || outer->kind != ST_FOR)
        return 0;

    tail = entry_cursor_skip_empty(outer->next);

    if (tail &&
        (tail->kind != ST_RETURN || tail->expression || entry_cursor_skip_empty(tail->next)))
        return 0;

    inner = outer->body;

    while (inner && inner->kind == ST_BLOCK && !inner->next) {
        inner = inner->body;
    }

    if (!inner || inner->next || !(loop = affine_find(inner)) || !loop->unroll_selected ||
        !loop->unroll.full || !loop->unroll.hoist || loop->unroll.counter.update_index ||
        loop->unroll.counter.recover_index || !(assignment = affine_register_assignment(loop)) ||
        !numeric(assignment->type) || assignment->type.base == TY_FLOAT ||
        assignment->type.pointers || assignment->left->type.banked || !loop->index->scope ||
        !dp_counter_shape(outer, NULL, &counter) || counter.wide || !counter.index->scope ||
        loop_observed_outside(f->body, outer, counter.index))
        return 0;

    memset(&shape, 0, sizeof shape);
    shape.statement = outer;
    shape.index = counter.index;

    if (!unroll_span(&shape, &rows) || rows > 32 || !(initial = affine_initial(&shape)) ||
        !integer_constant(initial->right, &outer_start) || !(initial = affine_initial(loop)) ||
        !integer_constant(initial->right, &inner_start))
        return 0;

    size = loop->unroll.width;
    bytes = rows * (12 + loop->unroll.span * (size == 4 ? 12 : 3) + (size == 1 ? 4 : 0)) + 8;

    if (rows * loop->unroll.span > UNROLL_FULL_LIMIT || bytes > UNROLL_BYTE_BUDGET)
        return 0;

    base = leaf_parameter(f, 0);

    if (!base || !base->type.pointers || far_pointer(base->type) || reg_width(base->type) != 2 ||
        !loop_private(base) ||
        !entry_cursor_value(f, assignment->right, size, &offset, &literal, &kind))
        return 0;

    for (r = 0; r < rows; ++r) {
        c = constants[r] = 0;

        if (!entry_cursor_address(loop, loop->accesses[0].address, base, NULL, inner_start & 65535,
                                  counter.index, (outer_start + r) & 65535, &c, &constants[r]) ||
            c)
            return 0;
    }

    code(".segment \"CODE\"\n.export _%s\n_%s:\n", fn->asm_name, fn->asm_name);
    code("; entry-only cursor leaf: no frame, nested region\n");
    code("; eliminated induction home: %s, %s\n", counter.index->name, loop->index->name);
    code("; cost unroll: full, factor %u, rectangular span, bytes %u\n", rows * loop->unroll.span,
         bytes);
    code("; affine loop: %s, known initial index, direct X\n", loop->index->name);
    code("; affine register cursor: X, stride %u\n", loop->unroll.stride);

    if (rows && loop->unroll.span) {
        if (kind == 2) {
            cg.arithmetic = 1;
            code("    sta z:__arith_lhs\n");
        }

        for (r = 0; r < rows; ++r) {
            unsigned delta = (constants[r] - (r ? constants[r - 1] : 0)) & 65535;

            if (delta) {
                code("    txa\n");
                strength_adjust(delta);
                code("    tax\n");
            }

            if (size != 4)
                entry_cursor_load(offset, literal, kind, 0);
            if (size == 1)
                code("    sep #$20\n.a8\n");

            for (i = 0; i < loop->unroll.span; ++i) {
                if (size == 4)
                    entry_cursor_load(offset, literal, kind, 0);

                code("    sta a:$%04X,x\n", i * loop->unroll.stride);

                if (size == 4) {
                    entry_cursor_load(offset, literal, kind, 2);
                    code("    sta a:$%04X,x\n", i * loop->unroll.stride + 2);
                }
            }

            if (size == 1)
                code("    rep #$20\n.a16\n");
        }
    }

    code("    rts\n__size_%s = * - _%s\n", fn->asm_name, fn->asm_name);
    return 1;
}
