/* Reuse a pure scalar /,% pair only when its producer dominates this use.
 * Results belong to the invocation's frame, not caller-clobbered scratch.
 * Codegen intersects availability at branches and clears it at loop entries,
 * and calls. Stores invalidate pairs when they can change an operand. */
static int divmod_pure(Expr *e)
{
    if (volatile_expression(e) || e->type.pointers || e->type.array || e->type.base == TY_FLOAT)
        return 0;
    if (e->kind == EX_INT || e->kind == EX_OBJECT)
        return 1;
    return e->kind == EX_CAST && divmod_pure(e->left);
}

static int divmod_same(Expr *a, Expr *b)
{
    if (a->kind != b->kind || !same_type(a->type, b->type))
        return 0;
    if (a->kind == EX_OBJECT)
        return a->symbol == b->symbol;
    if (a->kind == EX_INT)
        return a->value == b->value;
    return a->kind == EX_CAST && divmod_same(a->left, b->left);
}

static int divmod_operation(Expr *e)
{
    unsigned bits;
    int negative;

    Type t;
    if ((e->op != '/' && e->op != '%') ||
        (e->kind != EX_BINARY && (e->kind != EX_ASSIGN || e->left->kind != EX_OBJECT)) ||
        !divmod_pure(e->left) || !divmod_pure(e->right))
        return 0;
    t = binary_operands(e->left, e->right, e->op);
    return (t.base == TY_INT || t.base == TY_LONG) && !power_divisor(e->right, t, &bits, &negative);
}

static DivmodCache *divmod_find(Expr *e)
{
    unsigned i;

    if (!divmod_state.count || !divmod_operation(e))
        return NULL;

    for (i = 0; i < divmod_state.count; ++i) {
        Expr *other = divmod_state.entries[i].expression;
        if (divmod_same(e->left, other->left) && divmod_same(e->right, other->right))
            return &divmod_state.entries[i];
    }
    return NULL;
}

/* A top-tested loop can carry this producer directly into its body */
static int divmod_test_produces(Expr *e)
{
    if (!e)
        return 0;
    return (e->kind == EX_BINARY && divmod_find(e) != NULL) || divmod_test_produces(e->left) ||
           divmod_test_produces(e->right) || divmod_test_produces(e->third);
}

static int divmod_unaddressed(Expr *e)
{
    if (e->kind == EX_INT)
        return 1;
    if (e->kind == EX_CAST)
        return divmod_unaddressed(e->left);
    return e->symbol->owner == cg.function->id && !e->symbol->address_taken &&
           !loop_escapes(cg.function->body, e->symbol);
}

static void divmod_collect_expr(Expr *e)
{
    unsigned i;

    DivmodCache *c;
    if (!e)
        return;
    if (divmod_operation(e)) {
        c = divmod_find(e);
        if (!c && divmod_state.count < 16) {
            c = &divmod_state.entries[divmod_state.count++];
            *c = (DivmodCache){.expression = e,
                               .survives_indirect =
                                   divmod_unaddressed(e->left) && divmod_unaddressed(e->right)};
        }
        if (c)
            c->operations |= e->op == '/' ? 1u : 2u;
    }
    divmod_collect_expr(e->left);
    divmod_collect_expr(e->right);
    divmod_collect_expr(e->third);

    for (i = 0; i < e->arg_count; ++i)
        divmod_collect_expr(e->args[i]);
}

static void divmod_collect(Statement *s)
{
    for (; s; s = s->next) {
        divmod_collect_expr(s->expression);
        divmod_collect_expr(s->step);
        divmod_collect(s->initial);
        divmod_collect(s->body);
        divmod_collect(s->alternate);
    }
}

static int emit_statements(Statement *s);

static void divmod_prepare(Function *f)
{
    unsigned i, n = 0, slots = f->slots;
    size_t length;
    unsigned label_count, helper_count;
    int arithmetic;

    divmod_state.count = 0;
    divmod_state.available = 0;
    if (cg.parser->no_divmod_reuse)
        return;
    divmod_collect(f->body);

    for (i = 0; i < divmod_state.count; ++i) {
        DivmodCache c = divmod_state.entries[i];
        Expr *e = c.expression;
        unsigned bytes = 2 * reg_width(binary_operands(e->left, e->right, e->op));
        if (c.operations != 3 || f->slots + bytes + 4 > 768)
            continue;
        c.offset = f->slots + 1;
        f->slots += bytes;
        divmod_state.entries[n++] = c;
    }
    divmod_state.count = n;
    if (n)
        f->frame = f->slots + 4;
    if (!n)
        return;

    /* Use the emitter's actual control-flow/invalidation rules to discover
     * which candidates have a dominated reuse. Discard the trial text, labels
     * and imports, then reserve storage only for those profitable candidates.
     * No AST or C storage layout is changed by emitting a statement. */
    length = cg.length;
    label_count = cg.label;
    helper_count = cg.helper_count;
    arithmetic = cg.arithmetic;
    emit_statements(f->body);
    cg.length = length;
    cg.assembly[length] = 0;
    cg.label = label_count;
    cg.helper_count = helper_count;
    cg.arithmetic = arithmetic;
    cg.loop_count = 0;
    cg.switch_depth = 0;
    n = 0;
    f->slots = slots;

    for (i = 0; i < divmod_state.count; ++i)
        if (divmod_state.entries[i].reused) {
            DivmodCache c = divmod_state.entries[i];
            Expr *e = c.expression;
            c.offset = f->slots + 1;
            f->slots += 2 * reg_width(binary_operands(e->left, e->right, e->op));
            divmod_state.entries[n++] = c;
        }
    divmod_state.count = n;
    divmod_state.available = 0;
    f->frame = f->slots ? f->slots + 4 : 0;
}

static int divmod_reads(Expr *e, Symbol *s)
{
    if (e->kind == EX_OBJECT)
        return e->symbol == s;
    return e->kind == EX_CAST && divmod_reads(e->left, s);
}

static void divmod_written(Expr *destination)
{
    unsigned i;

    for (i = 0; i < divmod_state.count; ++i) {
        DivmodCache *c = &divmod_state.entries[i];
        Expr *e = c->expression;
        if (destination->kind != EX_OBJECT ? !c->survives_indirect
                                           : divmod_reads(e->left, destination->symbol) ||
                                                 divmod_reads(e->right, destination->symbol))
            divmod_state.available &= ~(1u << i);
    }
}

/* Start a 16/8 divide with the divisor in A and the dividend already
 * written to WRDIV. Leave the same two results as the paired helper. */
static void divmod_hardware_results(void)
{
    /* REP, five NOPs and the long load cover the divider latency */
    code("    sep #$20\n.a8\n    sta f:$004206\n    rep #$20\n.a16\n"
         "    nop\n    nop\n    nop\n    nop\n    nop\n"
         "    lda f:$004216\n    sta z:__arith_lhs+8\n"
         "    lda f:$004214\n    sta z:__arith_lhs+0\n");
    cg.arithmetic = 1;
}

static void divmod_hardware_pair(Expr *e, Type t, int guard)
{
    unsigned wide = 0, done = 0;

    emit_value(e->left);
    convert_registers(e->left->type, t);
    if (guard)
        stage(0, t);
    else
        code("    sta f:$004204\n");
    emit_value(e->right);
    if (guard) {
        wide = ++cg.label;
        done = ++cg.label;
        code("    cmp #$0100\n    bcs cg_%s_%u\n", cg.parser->unit, wide);
        code("    tax\n    lda z:__arith_lhs\n    sta f:$004204\n    txa\n");
    }
    divmod_hardware_results();
    if (guard) {
        jump(done);
        label(wide);
        stage(1, t);
        helper("__udiv16");
        label(done);
    }
}

static int divmod_byte_guard(Expr *e, Type t)
{
    KnownValue divisor = e->right->known;
    return reg_width(t) == 2 && t.is_unsigned && divisor.valid && divisor.min > 0 &&
           divisor.min <= 255 && divisor.max > 255 && divisor.max < 65535;
}

static void divmod_emit_cached(Expr *e, DivmodCache *c)
{
    unsigned bit, offset, w;

    Type t;
    t = binary_operands(e->left, e->right, e->op);
    w = reg_width(t);
    bit = 1u << (unsigned)(c - divmod_state.entries);
    offset = c->offset;
    if (!(divmod_state.available & bit)) {
        code("; divmod produce, frame $%04X\n", offset);
        int byte = arithmetic_byte_inputs(e->op, t, e->left, e->right);
        int guard = divmod_byte_guard(e, t);
        if (guard && divmod_state.version && e->right->kind == EX_OBJECT &&
            e->right->symbol == divmod_state.version) {
            byte = !divmod_state.wide_version;
            guard = 0;
        }
        if (w == 2 && cg.loop_count && !cg.function->symbol->interrupt &&
            !cg.parser->no_strength_reduction && (byte || guard))
            divmod_hardware_pair(e, t, !byte);
        else {
            if (!stage_expression(e->left, t, 0, 1)) {
                emit_value(e->left);
                convert_registers(e->left->type, t);
                stage(0, t);
            }
            if (!stage_expression(e->right, t, 1, 1)) {
                emit_value(e->right);
                convert_registers(e->right->type, t);
                stage(1, t);
            }
            helper(w == 4          ? (t.is_unsigned ? "__udiv32" : "__sdivmod32")
                   : byte          ? "__udiv8"
                   : t.is_unsigned ? "__udiv16"
                                   : "__sdivmod16");
        }
        code("    sta %s\n", frame_operand(offset));
        if (w == 4)
            code("    txa\n    sta %s\n", frame_operand(offset + 2));
        code("    lda z:__arith_lhs+8\n    sta %s\n", frame_operand(offset + w));
        if (w == 4)
            code("    lda z:__arith_lhs+10\n    sta %s\n", frame_operand(offset + 6));
        divmod_state.available |= bit;
    } else {
        c->reused = 1;
        code("; divmod reuse, frame $%04X\n", offset);
    }
    if (e->op == '%')
        offset += w;
    if (w == 4)
        code("    lda %s\n    tax\n", frame_operand(offset + 2));
    code("    lda %s\n", frame_operand(offset));
}

static int divmod_emit(Expr *e)
{
    DivmodCache *c = divmod_find(e);
    if (!c)
        return 0;
    divmod_emit_cached(e, c);
    return 1;
}

static int divmod_assignment(Expr *e)
{
    DivmodCache *c;
    if (e->kind != EX_ASSIGN || !divmod_state.available)
        return 0;
    c = divmod_find(e);
    if (!c || !(divmod_state.available & (1u << (unsigned)(c - divmod_state.entries))))
        return 0;
    divmod_emit_cached(e, c);
    convert_registers(binary_operands(e->left, e->right, e->op), e->type);
    store_symbol(e->left->symbol);
    divmod_written(e->left);
    return 1;
}
