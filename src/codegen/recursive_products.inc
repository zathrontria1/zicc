/* Return a widened word times a direct self-call, with one hardware-stack
 * save for the live argument. The child and the helper use the public ABI. */
static Expr *recursive_product_call(Function *f, Statement **arm, unsigned count, Symbol *parameter)
{
    Expr *product, *factor, *result, *assignment;
    Symbol *temporary = NULL;

    if (!count || arm[count - 1]->kind != ST_RETURN || !(product = arm[count - 1]->expression) ||
        product->kind != EX_BINARY || product->op != '*' ||
        !reduction_type(product->type, TY_LONG, 1))
        return NULL;

    factor = product->left;
    result = product->right;

    if (!reduction_object(widened_word(factor), parameter)) {
        factor = product->right;
        result = product->left;
    }

    if (!reduction_object(widened_word(factor), parameter))
        return NULL;

    if (count == 2) {
        if (arm[0]->kind != ST_EXPR || !(assignment = arm[0]->expression) ||
            assignment->kind != EX_ASSIGN || assignment->op || result->kind != EX_OBJECT ||
            !reduction_object(assignment->left, temporary = result->symbol) ||
            !loop_private(temporary) || temporary->address_taken ||
            !reduction_type(temporary->type, TY_LONG, 1))
            return NULL;

        result = assignment->right;
    }

    return result->kind == EX_CALL && !result->left && !result->string &&
                   result->symbol == f->symbol && result->arg_count == 1
               ? result
               : NULL;
}

static int recursive_word_product(Function *f)
{
    Statement *top[3], *yes[2], *no[2], *guard, *base;

    unsigned n = 0, ny = 0, nn = 0, target, threshold;
    Symbol *s = f->symbol, *parameter;
    Expr *condition, *child, *argument;
    uint32_t bound, value, step;
    int op, recursive_when_true = 1;
    char entry[256];

    if (cg.parser->no_stack_frames || cg.parser->no_private_regions ||
        cg.parser->no_body_optimizations || cg.parser->no_strength_reduction || s->interrupt ||
        s->param_count != 1 || s->variadic || s->old_style ||
        !reduction_type(s->type, TY_LONG, 1) || !reduction_type(s->params[0], TY_INT, 1) ||
        !register_parameter(0, s->params[0]) || statement_inline_markers(f->body) ||
        volatile_statements(f->body) || !(parameter = leaf_parameter(f, 0)) ||
        parameter->address_taken || !reduction_statements(f->body, top, &n, 3) || !n ||
        top[0]->kind != ST_IF)
        return 0;

    guard = top[0];
    condition = guard->expression;

    if (condition->kind != EX_BINARY || !reduction_object(word_bits(condition->left), parameter) ||
        !integer_constant(condition->right, &bound) || bound > 65535 ||
        !reduction_type(common_type(condition->left->type, condition->right->type), TY_INT, 1) ||
        !reduction_statements(guard->body, yes, &ny, 2))
        return 0;

    if (guard->alternate) {
        if (n != 1 || !reduction_statements(guard->alternate, no, &nn, 2))
            return 0;
    } else {
        if (n < 2)
            return 0;

        while (nn + 1 < n) {
            no[nn] = top[nn + 1];
            ++nn;
        }
    }

    child = recursive_product_call(f, yes, ny, parameter);

    if (child) {
        if (nn != 1)
            return 0;

        base = no[0];
    } else {
        if (ny != 1 || !(child = recursive_product_call(f, no, nn, parameter)))
            return 0;

        base = yes[0];
        recursive_when_true = 0;
    }

    if (base->kind != ST_RETURN || !base->expression || !integer_constant(base->expression, &value))
        return 0;

    argument = word_bits(child->args[0]);

    if (argument->kind != EX_BINARY || argument->op != '-' || reg_width(argument->type) != 2 ||
        !reduction_object(word_bits(argument->left), parameter) ||
        !integer_constant(argument->right, &step) || !step || step > 65535)
        return 0;

    op = condition->op;

    if (op != '<' && op != TOK_LE && op != '>' && op != TOK_GE)
        return 0;

    threshold = (unsigned)bound + (op == TOK_LE || op == '>');

    if (!threshold || threshold > 65535)
        return 0;
    if (op == '<' || op == TOK_LE)
        recursive_when_true = !recursive_when_true;

    target = ++cg.label;
    f->frame = 0;
    code(".segment \"%s\"\n.export _%s\n_%s:\n; compact recursive word product frame\n",
         code_segment(), s->asm_name, s->asm_name);
    code("    cpx #$%04X\n", threshold);

    if (recursive_when_true)
        flag_branch("bcc", "bcs", target, 0, 0);
    else
        flag_branch("bcs", "bcc", target, 0, 0);

    code("    phx\n");

    if (step <= 4)
        for (unsigned i = 0; i < step; ++i) {
            code("    dex\n");
        }
    else
        code("    txa\n    sec\n    sbc #$%04X\n    tax\n", (unsigned)step);

    snprintf(entry, sizeof entry, "_%s", s->asm_name);
    call_entry(entry);
    code("    sta z:__arith_rhs\n    stx z:__arith_rhs+2\n    pla\n"
         "    sta z:__arith_lhs\n    stz z:__arith_lhs+2\n");
    helper("__mul16x32");
    code("    rts\n");
    label(target);
    code("    lda #$%04X\n    ldx #$%04X\n    rts\n__size_%s = * - _%s\n",
         (unsigned)(value & 65535), (unsigned)(value >> 16), s->asm_name, s->asm_name);
    return 1;
}
