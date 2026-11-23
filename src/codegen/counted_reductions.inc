/* Use a countdown only when the function sets up its own variables, runs
 * one counting loop, and returns the sum. Otherwise use the normal emitter
 * so calls, writes through pointers, and later uses of the index still work. */
static int reduction_statements(Statement *s, Statement **out, unsigned *count, unsigned limit)
{
    for (; s; s = s->next) {
        if (s->kind == ST_BLOCK) {
            if (!reduction_statements(s->body, out, count, limit))
                return 0;
        } else if (s->kind != ST_EMPTY) {
            if (*count == limit)
                return 0;

            out[(*count)++] = s;
        }
    }

    return 1;
}

static int reduction_object(Expr *e, Symbol *s)
{
    return e && e->kind == EX_OBJECT && e->symbol == s;
}

static int reduction_type(Type t, int base, int is_unsigned)
{
    return !t.pointers && !t.array && t.base == base && t.is_unsigned == is_unsigned;
}

static int reduction_zero(Expr *e)
{
    uint32_t value;

    return e && integer_constant(e, &value) && !value;
}

static void far_counted_reduction(Function *f, unsigned stride, unsigned lo, unsigned ro)
{
    unsigned empty = ++cg.label, loop = ++cg.label, positive = ++cg.label, done = ++cg.label;
    f->frame = 6;
    cg.arithmetic = 1;
    code(".segment \"CODE\"\n.export _%s\n_%s:\n; far counted reduction: stride %u, frame 6\n",
         f->symbol->asm_name, f->symbol->asm_name, stride);
    code("    cmp #0\n    beq cg_%s_%u\n    bmi cg_%s_%u\n", cg.parser->unit, empty,
         cg.parser->unit, empty);
    /* Sum at 1/3,Y, remaining at 5,Y. Arithmetic scratch is call-clobbered.
     * __mul16x32 uses scratch offsets 0-11; the private cursor occupies 16-19. */
    code("    phy\n    pha\n    lda %u,s\n    and #$00FF\n    sta z:__arith_lhs+18\n    lda %u,s\n "
         "   sta z:__arith_lhs+16\n    pea $0000\n    pea $0000\n    tsc\n    tay\n",
         9 + cg.parser->long_return, 7 + cg.parser->long_return);
    label(loop);
    code("    stz z:__arith_lhs+2\n    phy\n    ldy #$%04X\n    lda [__arith_lhs+16],y\n    sta "
         "z:__arith_lhs\n    bpl cg_%s_%u\n    dec z:__arith_lhs+2\n",
         lo, cg.parser->unit, positive);
    label(positive);
    code("    ldy #$%04X\n    lda [__arith_lhs+16],y\n    sta z:__arith_rhs\n    iny\n    iny\n    "
         "lda [__arith_lhs+16],y\n    sta z:__arith_rhs+2\n    ply\n",
         ro);
    helper("__mul16x32");
    code("    clc\n    adc a:$0001,y\n    sta a:$0001,y\n    txa\n    adc a:$0003,y\n    sta "
         "a:$0003,y\n");
    code("    lda a:$0005,y\n    dec a\n    sta a:$0005,y\n    beq cg_%s_%u\n    lda "
         "z:__arith_lhs+16\n    clc\n    adc #$%04X\n    sta z:__arith_lhs+16\n    bcc cg_%s_%u\n  "
         "  inc z:__arith_lhs+18\n    lda z:__arith_lhs+18\n    and #$00FF\n    sta "
         "z:__arith_lhs+18\n",
         cg.parser->unit, done, stride, cg.parser->unit, loop);
    jump(loop);
    label(done);
    code("    ldx a:$0003,y\n    lda a:$0001,y\n    sta a:$0005,y\n    tya\n    clc\n    adc "
         "#$0004\n    tcs\n    pla\n    ply\n    rts\n");
    label(empty);
    code("    lda #0\n    ldx #0\n    rts\n__size_%s = * - _%s\n", f->symbol->asm_name,
         f->symbol->asm_name);
}

typedef struct {
    unsigned stride, lo, ro;
    Symbol *base, *bound;
} ReductionPlan;

static int reduction_plan(Function *f, ReductionPlan *plan)
{
    Statement *statements[3], *initial[1], *body[1];

    unsigned n = 0, ni = 0, nb = 0, lo, ro, stride, j;
    Expr *init, *condition, *step, *update, *product, *left, *right, *a, *b;
    Symbol *base, *bound, *sum, *index;

    if (cg.parser->no_strength_reduction || cg.parser->no_register_loops ||
        f->symbol->param_count != 2 || f->symbol->variadic || !strcmp(f->symbol->name, "main") ||
        !reduction_type(f->symbol->type, TY_LONG, 1) ||
        !reduction_statements(f->body, statements, &n, 3) || n != 3 ||
        statements[0]->kind != ST_EXPR || statements[1]->kind != ST_FOR ||
        statements[2]->kind != ST_RETURN)
        return 0;

    base = leaf_parameter(f, 0);
    bound = leaf_parameter(f, 1);

    if (!base || !bound || base->type.base != TY_STRUCT || base->type.pointers != 1 ||
        base->type.array || !reduction_type(bound->type, TY_INT, 0))
        return 0;

    init = statements[0]->expression;

    if (init->kind != EX_ASSIGN || init->op || init->left->kind != EX_OBJECT ||
        !reduction_zero(init->right))
        return 0;

    sum = init->left->symbol;

    if (sum->owner != f->id || !sum->scope || !reduction_type(sum->type, TY_LONG, 1) ||
        !reduction_object(statements[2]->expression, sum))
        return 0;
    if (!reduction_statements(statements[1]->initial, initial, &ni, 1) || ni != 1 ||
        initial[0]->kind != ST_EXPR || !reduction_statements(statements[1]->body, body, &nb, 1) ||
        nb != 1 || body[0]->kind != ST_EXPR)
        return 0;

    init = initial[0]->expression;
    condition = statements[1]->expression;
    step = statements[1]->step;

    if (init->kind != EX_ASSIGN || init->op || init->left->kind != EX_OBJECT ||
        !reduction_zero(init->right))
        return 0;

    index = init->left->symbol;

    if (index->owner != f->id || !index->scope || !reduction_type(index->type, TY_INT, 0) ||
        !condition || condition->kind != EX_BINARY || condition->op != '<' ||
        !reduction_object(condition->left, index) || !reduction_object(condition->right, bound) ||
        !step || (step->kind != EX_PRE && step->kind != EX_POST) || step->op != TOK_INC ||
        !reduction_object(step->left, index))
        return 0;

    update = body[0]->expression;

    if (update->kind != EX_ASSIGN || update->op != '+' || !reduction_object(update->left, sum))
        return 0;

    product = update->right;

    if (product->kind != EX_BINARY || product->op != '*' ||
        !reduction_type(product->type, TY_LONG, 1))
        return 0;

    left = element_member(product->left, &a, &lo);
    right = element_member(product->right, &b, &ro);

    /* Accept exactly a signed word widened to unsigned long, times an
     * unsigned-long field. Arbitrary cast chains can truncate or re-sign. */
    if (!left || !right || product->left->kind != EX_CAST || product->left->left != left ||
        product->right != right || !reduction_type(product->left->type, TY_LONG, 1) ||
        !reduction_type(left->type, TY_INT, 0) || !reduction_type(right->type, TY_LONG, 1) ||
        !same_element_address(a, b) || a->kind != EX_BINARY || a->op != '+' ||
        !reduction_object(a->left, base) || !reduction_object(a->right, index))
        return 0;

    stride = increment_step(base->type);

    if (!stride || lo + 2 > stride || ro + 4 > stride || statement_references(f->body, sum) != 3 ||
        statement_references(f->body, index) != 5 || statement_references(f->body, base) != 2 ||
        statement_references(f->body, bound) != 1)
        return 0;

    /* Uninitialized extra homes are harmless, but declining keeps this first
     * selector's ownership contract explicit and leaves their layout alone. */
    for (j = 0; j < cg.parser->symbol_count; ++j) {
        Symbol *s = &cg.parser->symbols[j];

        if (s->owner == f->id && s != base && s != bound && s != sum && s != index)
            return 0;
    }

    plan->base = base;
    plan->bound = bound;
    plan->stride = stride;
    plan->lo = lo;
    plan->ro = ro;
    return 1;
}

static void bank_reference(Expr *e);

static void reduction_load(unsigned offset, Expr *bank)
{
    if (bank) {
        code("    lda f:.bankbyte(");
        bank_reference(bank);
        code(")*$10000+$%04X,x\n", offset);
    } else
        code("    lda a:$%04X,x\n", offset);
}

static void near_counted_reduction(ReductionPlan *plan, const char *entry, Expr *bank)
{
    unsigned empty = ++cg.label, loop = ++cg.label, positive = ++cg.label, done = ++cg.label;
    unsigned stride = plan->stride, lo = plan->lo, ro = plan->ro;
    cg.arithmetic = 1;
    code(".segment \"CODE\"\n.export %s\n%s:\n; %scounted reduction: stride %u, frame 8\n", entry,
         entry, bank ? "ROM bank " : "", stride);
    code("    cmp #$0000\n    beq cg_%s_%u\n    bmi cg_%s_%u\n", cg.parser->unit, empty,
         cg.parser->unit, empty);
    /* Y+1/3 sum, Y+5 cursor, Y+7 remaining; saved Y follows the frame.
     * Guard first, then push incoming registers and known zero words. */
    code("    phy\n    pha\n    phx\n    pea $0000\n    pea $0000\n    tsc\n    tay\n");
    label(loop);
    code("    ldx a:$0005,y\n    stz z:__arith_lhs+2\n");
    reduction_load(lo, bank);
    code("    sta z:__arith_lhs\n    bpl cg_%s_%u\n    dec z:__arith_lhs+2\n", cg.parser->unit,
         positive);
    label(positive);
    reduction_load(ro, bank);
    code("    sta z:__arith_rhs\n");
    reduction_load(ro + 2, bank);
    code("    sta z:__arith_rhs+2\n");
    helper("__mul16x32");
    code("    clc\n    adc a:$0001,y\n    sta a:$0001,y\n    txa\n    adc a:$0003,y\n    sta "
         "a:$0003,y\n");
    code("    lda a:$0007,y\n    dec a\n    sta a:$0007,y\n    beq cg_%s_%u\n    lda a:$0005,y\n   "
         " clc\n    adc #$%04X\n    sta a:$0005,y\n    bra cg_%s_%u\n",
         cg.parser->unit, done, stride, cg.parser->unit, loop);
    label(done);
    code("    ldx a:$0003,y\n    lda a:$0001,y\n    sta a:$0007,y\n    tya\n    clc\n    adc "
         "#$0006\n    tcs\n    pla\n    ply\n    rts\n");
    label(empty);
    code("    lda #$0000\n    ldx #$0000\n    rts\n__size_%s = * - %s\n", entry + 1, entry);
}

static int counted_reduction(Function *f)
{
    ReductionPlan plan;
    char entry[132];

    if (!reduction_plan(f, &plan))
        return 0;

    if (far_pointer(plan.base->type))
        far_counted_reduction(f, plan.stride, plan.lo, plan.ro);
    else {
        f->frame = 8;
        snprintf(entry, sizeof entry, "_%s", f->symbol->asm_name);
        near_counted_reduction(&plan, entry, NULL);
    }

    return 1;
}
