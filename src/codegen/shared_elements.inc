/* Expression-local sharing needs no persistent cache or alias invalidation.
 * Only scalar/array names, integer literals and pure arithmetic form addresses.
 * In particular calls, dereferences, assignments and increments are barriers. */
static int element_address_pure(Expr *e)
{
    if (!e || e->type.base == TY_FLOAT)
        return 0;
    if (e->kind == EX_OBJECT)
        return !e->symbol->function;
    if (e->kind == EX_INT)
        return 1;
    if (e->kind == EX_CAST)
        return element_address_pure(e->left);
    if (e->kind == EX_UNARY && (e->op == '+' || e->op == '-' || e->op == '~' || e->op == '!'))
        return element_address_pure(e->left);

    return e->kind == EX_BINARY && element_address_pure(e->left) && element_address_pure(e->right);
}

static int same_element_address(Expr *a, Expr *b)
{
    if (a->kind != b->kind || !same_type(a->type, b->type))
        return 0;
    if (a->kind == EX_OBJECT)
        return a->symbol == b->symbol;
    if (a->kind == EX_INT)
        return a->value == b->value;
    if (a->kind == EX_CAST)
        return same_element_address(a->left, b->left);
    if (a->kind == EX_UNARY)
        return a->op == b->op && same_element_address(a->left, b->left);

    return a->kind == EX_BINARY && a->op == b->op && same_element_address(a->left, b->left) &&
           same_element_address(a->right, b->right);
}

static Expr *element_member(Expr *e, Expr **address, unsigned *offset)
{
    int pointer;
    Expr *root;

    while (e->kind == EX_CAST) {
        if (!numeric(e->type) || e->type.base == TY_FLOAT)
            return NULL;

        e = e->left;
    }

    if (e->kind != EX_MEMBER || !numeric(e->type) || e->type.base == TY_FLOAT)
        return NULL;

    root = member_root(e, offset, &pointer);

    if (!pointer) {
        if (root->kind != EX_DEREF)
            return NULL;

        root = root->left;
    }

    if (root->type.base != TY_STRUCT || value_type(root->type).pointers != 1 ||
        !element_address_pure(root))
        return NULL;

    *address = root;
    return e;
}

static void shared_member_value(Expr *e, unsigned offset)
{
    if (e->kind == EX_CAST) {
        shared_member_value(e->left, offset);
        convert_registers(e->left->type, e->type);
    } else
        load_indirect_at(e->type, 0, offset);
}

static void far_shared_member_value(Expr *e, unsigned offset)
{
    if (e->kind == EX_CAST) {
        far_shared_member_value(e->left, offset);
        convert_registers(e->left->type, e->type);
        return;
    }

    code("    phy\n");

    if (reg_width(e->type) == 4)
        code("    ldy #$%04X\n    lda [__arith_lhs+24],y\n    tax\n", offset + 2);

    code("    ldy #$%04X\n", offset);

    if (width(e->type) == 1)
        code("    sep #$20\n.a8\n");

    code("    lda [__arith_lhs+24],y\n");

    if (width(e->type) == 1)
        code("    rep #$20\n.a16\n");

    code("    ply\n");
    narrow_char(e->type);
}

/* Adjacent fields in the same computed record need just one index. Keep
 * the source ordering of the first field, its unit adjustment and the second. */
static int shared_adjusted_members(Expr *e)
{
    Expr *step = e->left, *right = e->right;

    unsigned lo, ro;
    int lp, rp;

    if (cg.parser->no_indexed_operands || cg.parser->no_strength_reduction || cg.retained_index ||
        cg.retained_second || cg.scan_cursor || cg.numeric_index || !word_integer(e->type) ||
        (e->op != '-' && e->op != '+') || step->kind != EX_BINARY ||
        (step->op != '+' && step->op != '-') || !word_integer(step->type) ||
        step->right->kind != EX_INT || step->right->value != 1 || step->left->kind != EX_MEMBER ||
        right->kind != EX_MEMBER || !word_integer(step->left->type) || !word_integer(right->type) ||
        volatile_expression(e))
        return 0;

    Expr *a = member_root(step->left, &lo, &lp), *b = member_root(right, &ro, &rp);

    if (lp || rp || a->kind != EX_DEREF || b->kind != EX_DEREF ||
        far_pointer(value_type(a->left->type)) || !body_equal(a->left, b->left) ||
        body_effect(a->left) || lo > 65534 || ro > 65534)
        return 0;

    emit_value_x(a->left);
    code("    lda a:$%04X,x\n    %s a\n    %s\n    %s a:$%04X,x\n", lo,
         step->op == '+' ? "inc" : "dec", e->op == '+' ? "clc" : "sec",
         e->op == '+' ? "adc" : "sbc", ro);
    return 1;
}

static int shared_word_member(Expr *e, Expr *member)
{
    while (e != member) {
        if (!e || e->kind != EX_CAST || !word_integer(e->type))
            return 0;

        e = e->left;
    }

    return word_integer(member->type);
}

static int shared_element_binary(Expr *e)
{
    Expr *left, *right, *a, *b;
    Type t;

    unsigned lo, ro, unused;
    int word_left, word_right, swap;

    if (cg.stack_leaf || cg.leaf_count || e->kind != EX_BINARY ||
        (!basic_integer_op(e->op) && e->op != '*' && e->op != '/' && e->op != '%'))
        return 0;

    left = element_member(e->left, &a, &lo);
    right = element_member(e->right, &b, &ro);

    if (!left || !right || !same_element_address(a, b))
        return 0;
    if (fixed_memory_object(left, &unused) && fixed_memory_object(right, &unused))
        return 0;

    t = binary_operands(e->left, e->right, e->op);

    if (t.pointers || t.base == TY_FLOAT)
        return 0;

    if (!far_pointer(value_type(a->type)) && !volatile_expression(e) && reg_width(t) == 2 &&
        !t.pointers && t.base == TY_INT &&
        (e->op == '+' || e->op == '-' || e->op == '&' || e->op == '|' || e->op == '^') &&
        lo <= 65534 && ro <= 65534 && shared_word_member(e->left, left) &&
        shared_word_member(e->right, right)) {
        const char *op = e->op == '+'   ? "adc"
                         : e->op == '-' ? "sbc"
                         : e->op == '&' ? "and"
                         : e->op == '|' ? "ora"
                                        : "eor";
        code("; shared element address\n");
        emit_value_x(a);
        code("    lda a:$%04X,x\n", lo);

        if (e->op == '+')
            code("    clc\n");
        else if (e->op == '-')
            code("    sec\n");

        code("    %s a:$%04X,x\n", op, ro);
        return 1;
    }

    word_left = e->op == '*' && t.base == TY_LONG && widened_word(e->left) != NULL;
    word_right = e->op == '*' && t.base == TY_LONG && widened_word(e->right) != NULL;
    swap = word_right && !word_left;

    /* X must survive the first load/conversion: wide values and sign extension
     * use X for their high word. Stage that value before restoring the base. */
    if (far_pointer(value_type(a->type))) {
        code("; shared far element address\n");
        emit_value(a);
        cg.arithmetic = 1;
        code("    sta z:__arith_lhs+24\n    stx z:__arith_lhs+26\n");
        far_shared_member_value(e->left, lo);
        convert_registers(e->left->type, t);
        stage(swap ? 1 : 0, t);
        far_shared_member_value(e->right, ro);
        convert_registers(e->right->type, t);
        stage(swap ? 0 : 1, t);
    } else {
        code("; shared element address\n");
        emit_value_x(a);
        code("    phx\n");
        shared_member_value(e->left, lo);
        convert_registers(e->left->type, t);
        stage(swap ? 1 : 0, t);
        code("    plx\n");
        shared_member_value(e->right, ro);
        convert_registers(e->right->type, t);
        stage(swap ? 0 : 1, t);
    }

    if (word_left && word_right)
        helper("__mul16wide");
    else if (word_left || word_right)
        helper("__mul16x32");
    else
        binary_loaded(e->op, t, arithmetic_byte_inputs(e->op, t, e->left, e->right));

    return 1;
}
