/* Frameless scans of near record arrays with unsigned modular range tests.
 * A plan verifies the complete function before emitting the loop. */
typedef struct {
    unsigned offset, origin, extent;
} RangeProbe;

typedef struct {
    Symbol *base, *end, *calls[4];
    RangeProbe probes[2];
    unsigned count, call_count, stride;
    uint32_t found, missing;
} RangeScan;

static int scan_parameter(Expr *e, Function *f)
{
    int i;

    for (i = 0; i < f->symbol->param_count; ++i) {
        if (reduction_object(word_bits(e), leaf_parameter(f, (unsigned)i)))
            return i;
    }

    return -1;
}

static int scan_probe(Expr *e, Function *f, Symbol *cursor, RangeScan *scan)
{
    Expr *difference, *field, *root;
    int pointer, origin, extent;

    unsigned offset;
    Type t;

    if (e->kind == EX_BINARY && e->op == TOK_LAND)
        return scan_probe(e->left, f, cursor, scan) && scan_probe(e->right, f, cursor, scan);
    if (scan->count == 2 || e->kind != EX_BINARY || e->op != '<')
        return 0;

    t = common_type(e->left->type, e->right->type);
    difference = word_bits(e->left);

    if (!reduction_type(t, TY_INT, 1) || difference->kind != EX_BINARY || difference->op != '-' ||
        reg_width(difference->type) != 2)
        return 0;

    field = word_bits(difference->left);

    if (field->kind != EX_MEMBER || width(field->type) != 2 || field->type.pointers)
        return 0;

    root = member_root(field, &offset, &pointer);

    if (!pointer) {
        if (root->kind != EX_DEREF)
            return 0;

        root = root->left;
    }

    origin = scan_parameter(difference->right, f);
    extent = scan_parameter(e->right, f);

    if (!reduction_object(root, cursor) || origin < 0 || extent < 0 || offset + 2 > scan->stride)
        return 0;

    scan->probes[scan->count++] = (RangeProbe){offset, (unsigned)origin, (unsigned)extent};
    return 1;
}

static int scan_plan(Function *f, RangeScan *scan)
{
    Symbol *s = f->symbol, *cursor;
    Statement *parts[3], *body[2], *hit[5];
    Expr *init, *test, *step;

    unsigned n = 0, nb = 0, nh = 0, i, offset;

    if (cg.parser->no_register_loops || cg.parser->no_register_cursors || cg.parser->no_dp_homes ||
        cg.parser->no_strength_reduction || s->variadic || s->param_count < 2 ||
        s->param_count > 4 || s->type.pointers ||
        (s->type.base != TY_INT && s->type.base != TY_CHAR) || !strcmp(s->name, "main") ||
        !reduction_statements(f->body, parts, &n, 3) || n != 3 || parts[0]->kind != ST_EXPR ||
        parts[1]->kind != ST_WHILE || parts[2]->kind != ST_RETURN || !parts[2]->expression ||
        !integer_constant(parts[2]->expression, &scan->missing))
        return 0;

    for (i = 0; i < (unsigned)s->param_count; ++i) {
        Symbol *arg = leaf_parameter(f, i);

        if (!arg || !reduction_type(arg->type, TY_INT, 1) || arg->type.is_bool)
            return 0;
    }

    init = parts[0]->expression;
    test = parts[1]->expression;

    if (init->kind != EX_ASSIGN || init->op || init->left->kind != EX_OBJECT || !test ||
        test->kind != EX_BINARY || test->op != TOK_NE || test->right->kind != EX_OBJECT)
        return 0;

    cursor = init->left->symbol;
    scan->end = test->right->symbol;

    if (cursor->owner != f->id || !body_private(cursor) || !cursor->type.pointers ||
        far_pointer(cursor->type) || !reduction_object(test->left, cursor) || scan->end->owner ||
        scan->end->type.banked ||
        !same_type(unqualified_value(cursor->type), unqualified_value(scan->end->type)))
        return 0;

    scan->base = near_object_address(init->right, &offset);
    scan->stride = increment_step(cursor->type);

    if (!scan->base || scan->base->owner || !scan->base->type.array || offset ||
        !same_type(unqualified_value(value_type(scan->base->type)),
                   unqualified_value(cursor->type)) ||
        !scan->stride || scan->stride > 65535 ||
        !reduction_statements(parts[1]->body, body, &nb, 2) || nb != 2 || body[0]->kind != ST_IF ||
        body[0]->alternate || body[1]->kind != ST_EXPR)
        return 0;

    step = body[1]->expression;

    if ((step->kind != EX_POST && step->kind != EX_PRE) || step->op != TOK_INC ||
        !reduction_object(step->left, cursor) ||
        !scan_probe(body[0]->expression, f, cursor, scan) ||
        !reduction_statements(body[0]->body, hit, &nh, 5) || !nh ||
        hit[nh - 1]->kind != ST_RETURN || !hit[nh - 1]->expression ||
        !integer_constant(hit[nh - 1]->expression, &scan->found))
        return 0;

    for (i = 0; i + 1 < nh; ++i) {
        Expr *call = hit[i]->expression;

        if (hit[i]->kind != ST_EXPR || !call || call->kind != EX_CALL || call->string ||
            !call->symbol || call->arg_count != 1 || !reduction_object(call->args[0], cursor) ||
            !register_argument(call->symbol, 0, call->args[0]))
            return 0;

        scan->calls[scan->call_count++] = call->symbol;
    }

    return 1;
}

static void scan_test(RangeScan *scan, unsigned displacement, unsigned reject, unsigned found)
{
    unsigned i;

    for (i = 0; i < scan->count; ++i) {
        RangeProbe *probe = &scan->probes[i];

        code("    lda a:$%04X,x\n", probe->offset + displacement);

        if (i)
            code("    adc z:__arith_lhs+8\n");
        else
            code("    sec\n    sbc z:__arith_lhs+%u\n", 2 * probe->origin);

        code("    cmp z:__arith_lhs+%u\n", 2 * probe->extent);

        if (i + 1 == scan->count)
            flag_branch("bcc", "bcs", found, reject, reject);
        else
            code("    bcs cg_%s_%u\n", cg.parser->unit, reject);
    }
}

static int range_scan_leaf(Function *f)
{
    RangeScan scan = {0};
    Symbol *s = f->symbol;

    unsigned i, loop, miss, hit, next, predicate_bytes, compact_bytes, used = 0;
    int unroll;

    if (!scan_plan(f, &scan))
        return 0;

    /* Score the relaxed 65816 forms, including the scalar tail and the
     * hit-path calls. Large bodies and short pools keep the compact loop. */
    predicate_bytes = 10 + 9 * (scan.count - 1);
    compact_bytes = 26 + 4 * ((unsigned)s->param_count - 2) + 8 * (scan.count - 1) +
                    predicate_bytes + scan.call_count * 6;
    unroll = !cg.parser->no_loop_unroll && scan.stride <= 8 && scan.base->type.array != ~0u &&
             scan.base->type.array >= 8 && compact_bytes + 36 + 2 * predicate_bytes <= 148;
    cg.arithmetic = 1;
    scan.base->used = 1;
    code(".segment \"CODE\"\n.export _%s\n_%s:\n; frameless unsigned range scan%s\n", s->asm_name,
         s->asm_name, unroll ? ", two candidates per iteration" : "");

    for (i = 0; i < scan.count; ++i) {
        used |= 1u << scan.probes[i].extent;

        if (!i || scan.probes[i].origin != 1)
            used |= 1u << scan.probes[i].origin;
    }

    if (used & 1)
        code("    stx z:__arith_lhs\n");
    if (used & 2)
        code("    sta z:__arith_lhs+2\n");
    if (scan.count == 2 && scan.probes[1].origin == 1)
        code("    eor #$FFFF\n    inc a\n    sta z:__arith_lhs+8\n");

    for (i = 2; i < (unsigned)s->param_count; ++i) {
        if (used & (1u << i))
            code("    lda %u,s\n    sta z:__arith_lhs+%u\n", 2 * i - 1 + cg.parser->long_return,
                 2 * i);
    }

    if (scan.count == 2 && scan.probes[1].origin != 1)
        code("    lda z:__arith_lhs+%u\n    eor #$FFFF\n    inc a\n    sta z:__arith_lhs+8\n",
             2 * scan.probes[1].origin);

    code("    ldx #.loword(_%s)\n", scan.base->asm_name);
    loop = ++cg.label;
    miss = ++cg.label;
    hit = ++cg.label;
    next = ++cg.label;

    if (unroll) {
        unsigned pair = ++cg.label, second = ++cg.label, advance = ++cg.label,
                 hit_second = ++cg.label;
        code("    lda ");
        array_operand(scan.end, 0);
        code("\n    sec\n    sbc #$%04X\n", scan.stride);
        flag_branch("bcc", "bcs", loop, 0, 0);
        code("    sta z:__arith_lhs+10\n");
        label(pair);
        code("    cpx z:__arith_lhs+10\n");
        flag_branch("bcs", "bcc", loop, 0, 0);
        scan_test(&scan, 0, second, hit);
        label(second);
        scan_test(&scan, scan.stride, advance, hit_second);
        label(advance);
        code("    txa\n    adc #$%04X\n    tax\n", 2 * scan.stride - 1);
        jump(pair);
        label(hit_second);
        code("    txa\n    clc\n    adc #$%04X\n    tax\n", scan.stride);
        jump(hit);
    }

    label(loop);
    code("    cpx ");
    array_operand(scan.end, 0);
    code("\n");
    flag_branch("beq", "bne", miss, 0, 0);
    scan_test(&scan, 0, next, hit);
    label(next);
    code("    txa\n    adc #$%04X\n    tax\n", scan.stride - 1);
    jump(loop);
    label(hit);

    for (i = 0; i < scan.call_count; ++i) {
        char name[132];

        if (i + 1 < scan.call_count)
            code("    phx\n");

        scan.calls[i]->used = 1;
        snprintf(name, sizeof name, "_%s", scan.calls[i]->asm_name);
        call_entry(name);

        if (i + 1 < scan.call_count)
            code("    plx\n");
    }

    code("    lda #$%04X\n    rts\n", initializer_cast(scan.found, s->type) & 65535);
    label(miss);
    code("    lda #$%04X\n    rts\n__size_%s = * - _%s\n",
         initializer_cast(scan.missing, s->type) & 65535, s->asm_name, s->asm_name);
    return 1;
}
