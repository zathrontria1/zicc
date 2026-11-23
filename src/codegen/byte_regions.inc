/* Rebind scaled loop indices once for byte copies and sign tests. Regions
 * contain only validated byte operations and internal conditional branches;
 * no call, external entry, address escape or frame access sees the bindings. */
static int byte_region_operand(Expr *e, IndexedOperand *operand, int *indexed)
{
    if (width(e->type) != 1 || e->type.is_bool || volatile_expression(e))
        return 0;

    *indexed = indexed_operand(e, operand) && indexed_retained(operand, 1);
    if (*indexed)
        return 1;
    if (e->kind != EX_OBJECT || !loop_private(e->symbol) || e->symbol == cg.retained_index ||
        e->symbol == cg.retained_second || !dp_state.homes || !e->symbol->offset ||
        (e->symbol->offset - 1) / 2 >= dp_state.words || !dp_state.map[(e->symbol->offset - 1) / 2])
        return 0;

    return 1;
}

static int byte_region_copy(Expr *e, int emit)
{
    Expr *rhs;
    IndexedOperand to = {0}, from = {0};
    int ti, fi, negative = 0;

    if (!e || e->kind != EX_ASSIGN || e->op || width(e->type) != 1 || e->type.is_bool ||
        volatile_expression(e))
        return 0;

    rhs = e->right;

    while (rhs->kind == EX_CAST && reg_width(rhs->type) == 2 && !rhs->type.is_bool) {
        rhs = rhs->left;
    }

    if (rhs->kind == EX_UNARY && rhs->op == '-') {
        negative = 1;
        rhs = rhs->left;

        while (rhs->kind == EX_CAST && reg_width(rhs->type) == 2 && !rhs->type.is_bool) {
            rhs = rhs->left;
        }
    }

    if (!byte_region_operand(e->left, &to, &ti) || !byte_region_operand(rhs, &from, &fi) ||
        (!ti && !fi))
        return 0;
    if (!emit)
        return 1;

    code("    lda ");

    if (fi)
        indexed_text(&from);
    else
        array_operand(rhs->symbol, 0);

    code("\n");

    if (negative)
        code("    eor #$FF\n    inc a\n");

    code("    sta ");

    if (ti)
        indexed_text(&to);
    else
        array_operand(e->left->symbol, 0);

    code("\n");
    divmod_written(e->left);
    return 1;
}

static int byte_region_statement(Statement *s, int emit)
{
    Expr *test, *source;
    Statement *arm;
    IndexedOperand operand = {0};
    int indexed;

    unsigned done;

    if (s->kind == ST_EXPR)
        return byte_region_copy(s->expression, emit);
    if (s->kind != ST_IF || s->alternate || s->inline_callee)
        return 0;

    test = s->expression;

    if (!test || test->kind != EX_BINARY || test->right->kind != EX_INT || test->right->value ||
        (test->op != '<' && test->op != '>' && test->op != TOK_LE && test->op != TOK_GE &&
         test->op != TOK_EQ && test->op != TOK_NE) ||
        common_type(test->left->type, test->right->type).is_unsigned)
        return 0;

    source = test->left;

    while (source->kind == EX_CAST && width(source->type) == 2) {
        source = source->left;
    }

    if (source->type.is_unsigned || !byte_region_operand(source, &operand, &indexed))
        return 0;

    arm = s->body;

    while (arm && arm->kind == ST_BLOCK && !arm->next && !arm->inline_callee) {
        arm = arm->body;
    }

    if (!arm || arm->next || arm->kind != ST_EXPR || arm->inline_callee ||
        !byte_region_copy(arm->expression, 0))
        return 0;
    if (!emit)
        return 1;

    done = ++cg.label;
    code("    lda ");

    if (indexed)
        indexed_text(&operand);
    else
        array_operand(source->symbol, 0);

    code("\n");

    if (test->op == '>')
        code("    beq cg_%s_%u\n", cg.parser->unit, done);

    if (test->op == TOK_LE) {
        unsigned take = ++cg.label;
        code("    beq cg_%s_%u\n    bpl cg_%s_%u\n", cg.parser->unit, take, cg.parser->unit, done);
        label(take);
    } else
        code("    %s cg_%s_%u\n",
             test->op == '<'                         ? "bpl"
             : test->op == '>' || test->op == TOK_GE ? "bmi"
             : test->op == TOK_EQ                    ? "bne"
                                                     : "beq",
             cg.parser->unit, done);

    byte_region_copy(arm->expression, 1);
    label(done);
    return 1;
}

static Statement *byte_index_region(Statement *s)
{
    Statement *p, *last = NULL;

    unsigned x = cg.retained_scale, y = cg.retained_second_scale, n = 0, j;

    if (cg.parser->no_body_optimizations || !cg.retained_index || !cg.retained_second ||
        cg.retained_scratch || cg.retained_y < 2 || !x || x > 8 || (x & (x - 1)) || !y || y > 8 ||
        (y & (y - 1)))
        return NULL;

    cg.retained_scale = cg.retained_second_scale = 1;

    for (p = s; p && n < 16 && !p->inline_callee && byte_region_statement(p, 0); p = p->next) {
        last = p;
        ++n;
    }

    cg.retained_scale = x;
    cg.retained_second_scale = y;

    if (n < 2 || (x == 1 && y == 1))
        return NULL;

    code("; retained byte indices begin\n    phx\n    phy\n");

    if (x > 1) {
        code("    txa\n");

        for (j = x; j > 1; j >>= 1) {
            code("    lsr a\n");
        }

        code("    tax\n");
    }

    if (y > 1) {
        code("    tya\n");

        for (j = y; j > 1; j >>= 1) {
            code("    lsr a\n");
        }

        code("    tay\n");
    }

    cg.retained_scale = cg.retained_second_scale = 1;
    code("    sep #$20\n.a8\n");

    for (p = s;; p = p->next) {
        byte_region_statement(p, 1);

        if (p == last)
            break;
    }

    code("    rep #$20\n.a16\n    ply\n    plx\n; retained byte indices end\n");
    cg.retained_scale = x;
    cg.retained_second_scale = y;
    return last;
}
