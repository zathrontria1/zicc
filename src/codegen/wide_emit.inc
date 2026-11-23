// 64-bit integer and binary64 wide value lowering

static void emit_wide_value(Expr *e);
static void emit_wide_assignment(Expr *e, int discarded);
static void emit_wide_update(Expr *e, int discarded);

static void emit_wide_literal(Expr *e, unsigned offset)
{
    uint64_t value = initializer_cast64(((uint64_t)e->value_high << 32) | e->value, e->type);

    unsigned i, loaded = 0;

    for (i = 0; i < 8; i += 2) {
        unsigned word = (unsigned)(value >> (8 * i)) & 65535;

        if (!word)
            code("    stz z:__arith_lhs+%u\n", offset + i);
        else {
            if (loaded != word)
                code("    lda #$%04X\n", word);

            code("    sta z:__arith_lhs+%u\n", offset + i);
            loaded = word;
        }
    }
}

static void emit_wide_operand(Expr *e)
{
    unsigned i;

    Type source = value_type(e->type), word = type(TY_LONG, 0);

    cg.arithmetic = 1;

    if (wide_scalar(source)) {
        emit_wide_value(e);
        return;
    }
    if (e->kind == EX_INT) {
        emit_wide_literal(e, 0);
        return;
    }

    word.is_unsigned = source.is_unsigned;
    emit_value(e);
    convert_registers(source, word);
    code("    sta z:__arith_lhs\n    stx z:__arith_lhs+2\n");

    if (source.is_unsigned)
        code("    lda #0\n");
    else
        code("    txa\n    cmp #$8000\n    lda #0\n    bcc :+\n    lda #$FFFF\n:\n");

    for (i = 4; i < 8; i += 2) {
        code("    sta z:__arith_lhs+%u\n", i);
    }
}

static void emit_wide_as(Expr *e, Type target)
{
    if (target.base == TY_DOUBLE && value_type(e->type).base != TY_DOUBLE) {
        Expr cast = {0};

        cast.kind = EX_CAST;
        cast.type = target;
        cast.left = e;
        cast.location = e->location;
        emit_wide_value(&cast);
    } else
        emit_wide_operand(e);
}

static void emit_wide_rhs(Expr *right, Type target)
{
    unsigned i, offset;
    Symbol *home;
    int same = target.base != TY_DOUBLE || value_type(right->type).base == TY_DOUBLE;

    if (same && right->kind == EX_INT) {
        emit_wide_literal(right, 8);
        return;
    }

    if (same && wide_scalar(value_type(right->type)) &&
        (home = wide_fixed_home(right, &offset)) != NULL) {
        for (i = 0; i < 8; i += 2) {
            code("    lda ");
            array_operand(home, offset + i);
            code("\n    sta z:__arith_lhs+%u\n", i + 8);
        }

        return;
    }

    for (i = 8; i; i -= 2) {
        code("    lda z:__arith_lhs+%u\n    pha\n", i - 2);
    }

    emit_wide_as(right, target);

    for (i = 0; i < 8; i += 2) {
        code("    lda z:__arith_lhs+%u\n    sta z:__arith_lhs+%u\n", i, i + 8);
    }

    for (i = 0; i < 8; i += 2) {
        code("    pla\n    sta z:__arith_lhs+%u\n", i);
    }
}

static void emit_wide_pair(Expr *left, Expr *right, Type target)
{
    emit_wide_as(left, target);
    emit_wide_rhs(right, target);
}

static void wide_word_bounds(Expr *e, int *low, int *high)
{
    Type t = value_type(e->type);

    unsigned bits = width(t) * 8;
    int a, b;

    *high = t.is_bool ? 1 : (int)((1u << (bits - !t.is_unsigned)) - 1);
    *low = t.is_unsigned || t.is_bool ? 0 : -*high - 1;
    if (e->kind == EX_INT) {
        *low = *high = (int32_t)initializer_cast(e->value, t);
        return;
    }
    if ((e->kind != EX_CAST && (e->kind != EX_UNARY || e->op != '~')) ||
        !known_integer(value_type(e->left->type)))
        return;

    wide_word_bounds(e->left, &a, &b);

    if (a < *low || b > *high)
        return;

    if (e->kind == EX_UNARY) {
        int complement = t.is_unsigned ? *high : -1;

        a = complement - a;
        b = complement - b;
        *low = b;
        *high = a;
    } else {
        *low = a;
        *high = b;
    }
}

static Expr *wide_word_source(Expr *e)
{
    while (e->kind == EX_CAST && e->type.base == TY_LONGLONG && !e->type.pointers) {
        e = e->left;
    }

    return known_integer(value_type(e->type)) && wide_address_safe(e) ? e : NULL;
}

static int wide_integer_literal(Expr *e)
{
    return e->kind == EX_INT && numeric(e->type) && e->type.base != TY_FLOAT &&
           e->type.base != TY_DOUBLE;
}

static int wide_mask_zero_flags(Expr *left, Expr *right)
{
    Symbol *home;
    uint64_t bits;

    unsigned offset, i, end = 0;
    int have = 0;

    if (wide_integer_literal(left)) {
        Expr *swap = left;

        left = right;
        right = swap;
    }

    if (!wide_integer_literal(right) || value_type(left->type).base != TY_LONGLONG ||
        !wide_scalar(value_type(left->type)) || volatile_expression(left) ||
        !(home = wide_fixed_home(left, &offset)))
        return 0;

    bits = initializer_cast64(((uint64_t)right->value_high << 32) | right->value, right->type);

    for (i = 0; i < 8; i += 2) {
        unsigned word = (unsigned)(bits >> (8 * i)) & 65535;

        if (!word)
            continue;

        if (have && word != 65535) {
            if (!end)
                end = ++cg.label;

            code("    bne cg_%s_%u\n", cg.parser->unit, end);
            have = 0;
        }

        code(have ? "    ora " : "    lda ");
        array_operand(home, offset + i);
        code("\n");

        if (word != 65535)
            code("    and #$%04X\n", word);

        have = 1;
    }

    if (!have)
        code("    lda #0\n");
    if (end)
        label(end);

    return 1;
}

/* Widening these operands preserves their low word. A range strictly
 * between the adjacent multiples of 65536 makes its zero test sufficient. */
static int wide_word_zero_flags(Expr *e)
{
    Expr *left, *right;
    int lmin, lmax, rmin, rmax, low, high;

    if (cg.parser->no_strength_reduction || e->kind != EX_BINARY || e->type.base != TY_LONGLONG ||
        e->type.pointers)
        return 0;
    if (e->op == '&')
        return wide_mask_zero_flags(e->left, e->right);
    if (e->op != '+' && e->op != '-')
        return 0;

    left = wide_word_source(e->left);
    right = wide_word_source(e->right);

    if (!left || !right)
        return 0;

    wide_word_bounds(left, &lmin, &lmax);
    wide_word_bounds(right, &rmin, &rmax);
    low = e->op == '+' ? lmin + rmin : lmin - rmax;
    high = e->op == '+' ? lmax + rmax : lmax - rmin;

    if (low <= -65536 || high >= 65536)
        return 0;

    code("; word zero test of widened arithmetic\n");
    emit_value(left);
    binary_after_left(left, right, e->op);
    code("    cmp #0\n");
    return 1;
}

static int wide_zero_compare(Expr *e, Type t, unsigned yes, unsigned no, unsigned fallthrough)
{
    Expr *value = e->left, *zero = e->right;
    int op = e->op, equality = op == TOK_EQ || op == TOK_NE;

    unsigned offset = 0, middle;
    Symbol *home;

    if (cg.parser->no_strength_reduction)
        return 0;

    if (zero->kind != EX_INT && value->kind == EX_INT) {
        zero = e->left;
        value = e->right;

        if (!equality)
            op = reverse_order(op);
    }

    if (zero->kind != EX_INT || zero->value || zero->value_high)
        return 0;

    if (equality || (t.is_unsigned && (op == '>' || op == TOK_LE))) {
        if (op == TOK_EQ || op == TOK_LE) {
            unsigned swap = yes;
            yes = no;
            no = swap;
        }

        branch(value, yes, no, fallthrough);
        return 1;
    }

    if (t.is_unsigned) {
        unsigned target = op == TOK_GE ? yes : no;

        if (body_effect(value))
            emit_discarded(value);
        if (target != fallthrough)
            jump(target);

        return 1;
    }

    if (op == '<' || op == TOK_GE) {
        Expr *word = wide_word_source(value);

        if (word) {
            if (word->type.is_unsigned) {
                unsigned target = op == TOK_GE ? yes : no;

                if (!literal_integer_tree(word))
                    emit_value(word);
                if (target != fallthrough)
                    jump(target);
            } else {
                emit_value(word);

                if (!accumulator_zero_flags())
                    code("    cmp #0\n");

                integer_relation_flags(op, 1, yes, no, fallthrough);
            }

            return 1;
        }
    }

    /* A sign test may skip the lower words of an ordinary memory operand */
    home = volatile_expression(value) ? NULL : wide_fixed_home(value, &offset);

    if (home && value_type(value->type).base != TY_LONGLONG)
        home = NULL;

    if (home) {
        code("    lda ");
        array_operand(home, offset + 6);
        code("\n");
    } else {
        emit_wide_as(value, t);
        code("    lda z:__arith_lhs+6\n");
    }

    if (op == '<' || op == TOK_GE) {
        integer_relation_flags(op, 1, yes, no, fallthrough);
        return 1;
    }

    if (op == TOK_LE) {
        unsigned swap = yes;
        yes = no;
        no = swap;
    }

    middle = ++cg.label;
    flag_branch("bmi", "bpl", no, middle, middle);
    label(middle);

    for (unsigned i = 0; i < 6; i += 2) {
        code("    ora ");

        if (home)
            array_operand(home, offset + i);
        else
            code("z:__arith_lhs+%u", i);

        code("\n");
    }

    flag_branch("bne", "beq", yes, no, fallthrough);
    return 1;
}

static int mixed_wide_equality(Expr *e, Type t, unsigned yes, unsigned no, unsigned fallthrough)
{
    Expr *lhs = e->left, *rhs = e->right;

    Type narrow = value_type(rhs->type);

    unsigned i, offset, left_offset, bytes, done;
    Symbol *left, *right;

    if (cg.parser->no_strength_reduction || value_type(lhs->type).base != TY_LONGLONG ||
        !wide_scalar(value_type(lhs->type)) || narrow.pointers ||
        (narrow.base != TY_INT && narrow.base != TY_LONG) || volatile_expression(e) ||
        !(right = wide_fixed_home(rhs, &offset)))
        return 0;

    left = wide_fixed_home(lhs, &left_offset);

    if (!left)
        emit_wide_as(lhs, t);

    bytes = width(narrow);
    done = ++cg.label;

    if (!narrow.is_unsigned) {
        code("    ldx #0\n    lda ");
        array_operand(right, offset + bytes - 2);
        code("\n    bpl :+\n    dex\n:\n");
    }

    for (i = 8; i; i -= 2) {
        unsigned part = i - 2;
        int sign = part >= bytes && !narrow.is_unsigned;

        code(sign ? "    txa\n    cmp " : "    lda ");

        if (left)
            array_operand(left, left_offset + part);
        else
            code("z:__arith_lhs+%u", part);

        code("\n");

        if (part < bytes) {
            code("    cmp ");
            array_operand(right, offset + part);
            code("\n");
        }

        if (part)
            code("    bne cg_%s_%u\n", cg.parser->unit, done);
    }

    label(done);
    flag_branch(e->op == TOK_EQ ? "beq" : "bne", e->op == TOK_EQ ? "bne" : "beq", yes, no,
                fallthrough);
    return 1;
}

static Expr *wide_word_magnitude_source(Expr *e)
{
    Expr *test, *negative, *positive, *word, *other;

    while (e->kind == EX_CAST && e->type.base == TY_LONGLONG && !e->type.pointers) {
        e = e->left;
    }

    if (e->kind != EX_CHOOSE)
        return NULL;

    test = e->left;
    negative = e->right;
    positive = e->third;

    if (cg.parser->no_strength_reduction || e->type.base != TY_LONGLONG ||
        test->kind != EX_BINARY || test->op != '<' || test->right->kind != EX_INT ||
        test->right->value || test->right->value_high ||
        common_type(test->left->type, test->right->type).is_unsigned ||
        !(word = wide_word_source(test->left)) || !literal_integer_tree(word))
        return NULL;

    while (negative->kind == EX_CAST && negative->type.base == TY_LONGLONG &&
           !negative->type.pointers) {
        negative = negative->left;
    }

    if (negative->kind != EX_UNARY || negative->op != '-' || negative->type.base != TY_LONGLONG ||
        !(other = wide_word_source(negative->left)) || !body_equal(word, other) ||
        !(other = wide_word_source(positive)) || !body_equal(word, other))
        return NULL;

    return word;
}

static void emit_word_magnitude(Expr *word)
{
    emit_value(word);

    if (!word->type.is_unsigned) {
        if (!accumulator_zero_flags())
            code("    cmp #0\n");

        code("    bpl :+\n    eor #$FFFF\n    inc a\n:\n");
    }
}

static int wide_word_magnitude_equal(Expr *value, Expr *other, int op, unsigned yes, unsigned no,
                                     unsigned fallthrough)
{
    Expr *source = wide_word_magnitude_source(value), *input;

    Type word = type(TY_INT, 0);

    if (!source)
        return 0;

    word.is_unsigned = 1;
    input = wide_word_source(other);

    if (!input && wide_integer_literal(other))
        input = other;

    if (input && input->kind == EX_INT &&
        initializer_cast64(((uint64_t)input->value_high << 32) | input->value, input->type) >
            65535u) {
        unsigned different = op == TOK_EQ ? no : yes;

        if (different != fallthrough)
            jump(different);

        return 1;
    }

    if (!input || !direct_operand(input, word, 0, 0))
        return 0;

    if (input->kind != EX_INT && !input->type.is_unsigned) {
        unsigned nonnegative = ++cg.label;
        code("    lda ");
        direct_operand(input, word, 0, 1);
        code("\n");
        flag_branch("bmi", "bpl", op == TOK_EQ ? no : yes, nonnegative, nonnegative);
        label(nonnegative);
    }

    emit_word_magnitude(source);
    code("    cmp ");
    direct_operand(input, word, 0, 1);
    code("\n");
    flag_branch(op == TOK_EQ ? "beq" : "bne", op == TOK_EQ ? "bne" : "beq", yes, no, fallthrough);
    return 1;
}

static int fixed_wide_compare(Expr *e, unsigned yes, unsigned no, unsigned fallthrough)
{
    Expr *lhs = e->left, *rhs = e->right;

    Type t = common_type(lhs->type, rhs->type);

    unsigned offset = 0, left_offset = 0, i;
    uint64_t bits = 0;
    Symbol *home = NULL, *left = NULL;
    int op = e->op, equality = op == TOK_EQ || op == TOK_NE;

    if (t.base != TY_LONGLONG)
        return 0;
    if (wide_zero_compare(e, t, yes, no, fallthrough))
        return 1;
    if (equality && (wide_word_magnitude_equal(lhs, rhs, op, yes, no, fallthrough) ||
                     wide_word_magnitude_equal(rhs, lhs, op, yes, no, fallthrough)))
        return 1;
    if (equality && mixed_wide_equality(e, t, yes, no, fallthrough))
        return 1;

    if (!cg.parser->no_strength_reduction && lhs->kind == EX_INT && rhs->kind != EX_INT) {
        lhs = e->right;
        rhs = e->left;

        if (!equality)
            op = reverse_order(op);
    }

    if (!cg.parser->no_strength_reduction && rhs->kind == EX_INT)
        bits = initializer_cast64(((uint64_t)rhs->value_high << 32) | rhs->value, rhs->type);
    else if (value_type(rhs->type).base != TY_LONGLONG || !(home = wide_fixed_home(rhs, &offset)))
        return 0;

    if (equality && !cg.parser->no_strength_reduction && wide_integer_literal(rhs)) {
        Expr *input = lhs;

        while (input->kind == EX_CAST && input->type.base == TY_LONGLONG && !input->type.pointers) {
            input = input->left;
        }

        Type narrow = value_type(input->type);

        if (numeric(narrow) && narrow.base != TY_FLOAT && !wide_scalar(narrow)) {
            if (initializer_cast64(bits, narrow) != bits) {
                unsigned different = op == TOK_EQ ? no : yes;

                if (body_discard_effect(input))
                    emit_discarded(input);
                if (different != fallthrough)
                    jump(different);
            } else {
                Expr literal = {0}, test = *e;

                literal.kind = EX_INT;
                literal.type = narrow;
                literal.value = (uint32_t)bits;
                test.left = input;
                test.right = &literal;
                test.op = op;
                branch(&test, yes, no, fallthrough);
            }

            return 1;
        }
    }

    if (!cg.parser->no_strength_reduction && value_type(lhs->type).base == TY_LONGLONG &&
        !volatile_expression(e))
        left = wide_fixed_home(lhs, &left_offset);
    if (!left)
        emit_wide_as(lhs, t);

    if (equality && (left || !home)) {
        unsigned different = op == TOK_EQ ? no : yes;

        for (i = 8; i; i -= 2) {
            code("    lda ");

            if (left)
                array_operand(left, left_offset + i - 2);
            else
                code("z:__arith_lhs+%u", i - 2);

            code("\n    cmp ");

            if (home)
                array_operand(home, offset + i - 2);
            else
                code("#$%04X", (unsigned)(bits >> (8 * (i - 2))) & 65535);

            code("\n");

            if (i > 2) {
                unsigned same = ++cg.label;
                flag_branch("bne", "beq", different, same, same);
                label(same);
            }
        }

        flag_branch(op == TOK_EQ ? "beq" : "bne", op == TOK_EQ ? "bne" : "beq", yes, no,
                    fallthrough);
        return 1;
    }

    if (!equality && left && home) {
        unsigned ordered = ++cg.label;

        if (op == '>' || op == TOK_LE) {
            Symbol *swap = left;

            unsigned at = left_offset;
            left = home;
            left_offset = offset;
            home = swap;
            offset = at;
            op = reverse_order(op);
        }

        i = 8;

        if (!t.is_unsigned) {
            unsigned low = ++cg.label;
            code("    sec\n    lda ");
            array_operand(left, left_offset + 6);
            code("\n    sbc ");
            array_operand(home, offset + 6);
            code("\n    beq cg_%s_%u\n    bvc :+\n    eor #$8000\n:\n", cg.parser->unit, low);
            integer_relation_flags(op, 1, yes, no, 0);
            label(low);
            i = 6;
        }

        for (; i; i -= 2) {
            code("    lda ");
            array_operand(left, left_offset + i - 2);
            code("\n    cmp ");
            array_operand(home, offset + i - 2);
            code("\n");

            if (i > 2)
                code("    bne cg_%s_%u\n", cg.parser->unit, ordered);
        }

        label(ordered);
        integer_relation_flags(op, 0, yes, no, fallthrough);
        return 1;
    }

    i = 0;

    if (!equality) {
        int borrow = op == '>' || op == TOK_LE;

        if (left && !home) {
            /* Zero with carry set, or all ones with carry clear, preserves carry */
            unsigned neutral = borrow ? 65535 : 0;

            while (i < 6 && ((bits >> (8 * i)) & 65535) == neutral) {
                i += 2;
            }
        }

        code(borrow ? "    clc\n" : "    sec\n");
    }

    for (; i < 8; i += 2) {
        code("    lda ");

        if (left)
            array_operand(left, left_offset + i);
        else
            code("z:__arith_lhs+%u", i);

        code("\n    %s ", equality ? "eor" : "sbc");

        if (home)
            array_operand(home, offset + i);
        else
            code("#$%04X", (unsigned)(bits >> (8 * i)) & 65535);

        code("\n");

        if (equality && i)
            code("    ora z:__arith_lhs\n");
        if (equality && i < 6)
            code("    sta z:__arith_lhs\n");
    }

    if (equality)
        flag_branch(op == TOK_EQ ? "beq" : "bne", op == TOK_EQ ? "bne" : "beq", yes, no,
                    fallthrough);
    else {
        if (!t.is_unsigned)
            code("    bvc :+\n    eor #$8000\n:\n");

        integer_relation_flags(op, !t.is_unsigned, yes, no, fallthrough);
    }

    return 1;
}

static void emit_wide_compare(Expr *e)
{
    Type t = common_type(e->left->type, e->right->type);

    unsigned yes = ++cg.label, no = ++cg.label, end = ++cg.label;

    if (fixed_wide_compare(e, yes, no, yes)) {
        label(yes);
        code("    lda #1\n");
        jump(end);
        label(no);
        code("    lda #0\n");
        label(end);
        return;
    }

    emit_wide_pair(e->left, e->right, t);

    if (t.base == TY_DOUBLE)
        helper(e->op == TOK_EQ || e->op == TOK_NE ? "__dcmp" : "__dcmp_signal");
    else
        helper(t.is_unsigned ? "__ucmp64" : "__scmp64");

    boolean_from_compare(e->op);
}

static const char *wide_word_instruction(int op)
{
    return op == '+' ? "adc" : op == '-' ? "sbc" : op == '&' ? "and" : op == '|' ? "ora" : "eor";
}

static void emit_wide_immediate_operation(int op, Expr *literal)
{
    uint64_t bits =
        initializer_cast64(((uint64_t)literal->value_high << 32) | literal->value, literal->type);
    unsigned i = 0;
    int carry = op == '+' || op == '-';

    if (carry) {
        if (!bits)
            return;

        while (!((bits >> (8 * i)) & 65535)) {
            i += 2;
        }

        code(op == '+' ? "    clc\n" : "    sec\n");
    }

    for (; i < 8; i += 2) {
        unsigned word = (unsigned)(bits >> (8 * i)) & 65535;

        if (!carry && word == (op == '&' ? 65535u : 0u))
            continue;
        if (op == '&' && !word) {
            code("    stz z:__arith_lhs+%u\n", i);
            continue;
        }

        if (op == '|' && word == 65535u)
            code("    lda #$FFFF\n");
        else
            code("    lda z:__arith_lhs+%u\n    %s #$%04X\n", i, wide_word_instruction(op), word);

        code("    sta z:__arith_lhs+%u\n", i);
    }
}

static void emit_wide_word_operation(int op, Symbol *left, unsigned left_offset, Symbol *right,
                                     unsigned offset)
{
    unsigned i;

    if (op == '+' || op == '-')
        code(op == '+' ? "    clc\n" : "    sec\n");

    for (i = 0; i < 8; i += 2) {
        code("    lda ");

        if (left)
            array_operand(left, left_offset + i);
        else
            code("z:__arith_lhs+%u", i);

        code("\n    %s ", wide_word_instruction(op));

        if (right)
            array_operand(right, offset + i);
        else
            code("z:__arith_lhs+%u", i + 8);

        code("\n    sta z:__arith_lhs+%u\n", i);
    }
}

static void emit_wide_operation(Type t, int op)
{
    if (t.base == TY_DOUBLE) {
        helper(op == '+' ? "__dadd" : op == '-' ? "__dsub" : op == '*' ? "__dmul" : "__ddiv");
        return;
    }

    if (op == '*' || op == '/' || op == '%' || op == TOK_SHL || op == TOK_SHR) {
        const char *name = op == '*'       ? "__mul64"
                           : op == '/'     ? (t.is_unsigned ? "__uquot64" : "__sdiv64")
                           : op == '%'     ? (t.is_unsigned ? "__umod64" : "__smod64")
                           : op == TOK_SHL ? "__shl64"
                           : t.is_unsigned ? "__ushr64"
                                           : "__sshr64";
        helper(name);
        return;
    }

    emit_wide_word_operation(op, NULL, 0, NULL, 0);
}

static int wide_word_shift_bytes(Type t, int op, Expr *right)
{
    unsigned count;

    if (cg.parser->no_strength_reduction || t.base != TY_LONGLONG ||
        (op != TOK_SHL && op != TOK_SHR) || !integer_constant(right, &count))
        return -1;

    count &= 63;
    return count % 16 ? -1 : (int)(count / 8);
}

static void wide_shift_slot(Symbol *home, unsigned offset, unsigned part)
{
    if (home)
        array_operand(home, offset + part);
    else
        code("z:__arith_lhs+%u", part);
}

static void emit_wide_word_shift(Type t, int op, unsigned bytes, Symbol *home, unsigned offset)
{
    unsigned i, first, end;
    int sign_fill = op == TOK_SHR && !t.is_unsigned;
    int stz = !sign_fill && (!home || (!home->owner && !home->type.banked));

    if (!bytes)
        return;

    if (op == TOK_SHL) {
        for (i = 8; i > bytes; i -= 2) {
            code("    lda ");
            wide_shift_slot(home, offset, i - bytes - 2);
            code("\n    sta ");
            wide_shift_slot(home, offset, i - 2);
            code("\n");
        }

        first = 0;
        end = bytes;
    } else {
        for (i = 0; i < 8 - bytes; i += 2) {
            code("    lda ");
            wide_shift_slot(home, offset, i + bytes);
            code("\n    sta ");
            wide_shift_slot(home, offset, i);
            code("\n");
        }

        first = i;
        end = 8;
    }

    if (sign_fill)
        code("    bmi :+\n    lda #0\n    bra :++\n:\n    lda #$FFFF\n:\n");
    else if (!stz)
        code("    lda #0\n");

    for (i = first; i < end; i += 2) {
        code(stz ? "    stz " : "    sta ");
        wide_shift_slot(home, offset, i);
        code("\n");
    }
}

static int wide_power_divisor(Expr *e, Expr **shift)
{
    uint64_t bits;
    int count = 0;

    *shift = NULL;
    if (e->kind == EX_BINARY && e->op == TOK_SHL && e->type.is_unsigned &&
        wide_address_safe(e->right)) {
        *shift = e->right;
        e = e->left;
    }

    if (e->kind != EX_INT)
        return -1;

    bits = initializer_cast64(((uint64_t)e->value_high << 32) | e->value, e->type);

    if (!bits || (bits & (bits - 1)))
        return -1;

    while (bits >>= 1) {
        ++count;
    }

    return count;
}

static unsigned wide_unsigned_size(Expr *e)
{
    Type t;

    while (e->kind == EX_CAST && !e->type.pointers && e->type.base == TY_LONGLONG) {
        e = e->left;
    }

    t = value_type(e->type);

    if (!numeric(t) || t.pointers || t.base == TY_FLOAT || t.base == TY_DOUBLE)
        return 0;
    if (e->kind == EX_INT) {
        uint64_t bits = initializer_cast64(((uint64_t)e->value_high << 32) | e->value, t);

        return bits <= 65535 ? 2 : bits <= UINT32_MAX ? 4 : 0;
    }

    return (t.is_unsigned || t.is_bool) && width(t) <= 4 ? reg_width(t) : 0;
}

static Expr *wide_signed_long_source(Expr *e)
{
    while (e->kind == EX_CAST && e->type.base == TY_LONGLONG && !e->type.pointers) {
        e = e->left;
    }

    return e->type.base == TY_LONG && !e->type.pointers && !e->type.array && !e->type.is_unsigned
               ? e
               : NULL;
}

static int emit_wide_signed_long_product(Expr *left, Expr *right)
{
    Type t = type(TY_LONG, 0);

    left = wide_signed_long_source(left);
    right = wide_signed_long_source(right);

    if (!left || !right)
        return 0;

    emit_value(left);
    push_value(t);
    emit_value(right);
    code("    sta z:__arith_lhs+8\n    stx z:__arith_lhs+10\n");
    pop_value(t);
    code("    sta z:__arith_lhs\n    stx z:__arith_lhs+2\n");
    helper("__smul32wide");
    return 1;
}

static int emit_wide_narrow_product(Expr *left, Expr *right, Type t)
{
    unsigned l = wide_unsigned_size(left), r = wide_unsigned_size(right);

    if (!l || !r || (l != 2 && r != 2))
        return 0;

    emit_wide_pair(left, right, t);

    /* The word helper leaves its inputs intact, with its product in A/X */
    if (l == 4) {
        code("    lda z:__arith_lhs+2\n    sta z:__arith_lhs+12\n"
             "    lda z:__arith_lhs\n    sta z:__arith_rhs\n"
             "    lda z:__arith_lhs+8\n    sta z:__arith_lhs\n");
    } else {
        if (r == 4)
            code("    lda z:__arith_lhs+10\n    sta z:__arith_lhs+12\n");

        code("    lda z:__arith_lhs+8\n    sta z:__arith_rhs\n");
    }

    code("    stz z:__arith_lhs+2\n    stz z:__arith_rhs+2\n");
    helper("__mul16wide");

    if (l == 2 && r == 2) {
        code("    sta z:__arith_lhs\n    stx z:__arith_lhs+2\n    stz z:__arith_lhs+4\n");
    } else {
        code("    sta z:__arith_lhs+14\n    stx z:__arith_lhs+16\n"
             "    lda z:__arith_lhs+12\n    sta z:__arith_rhs\n");
        helper("__mul16wide");
        code("    clc\n    adc z:__arith_lhs+16\n    sta z:__arith_lhs+2\n"
             "    txa\n    adc #0\n    sta z:__arith_lhs+4\n"
             "    lda z:__arith_lhs+14\n    sta z:__arith_lhs\n");
    }

    code("    stz z:__arith_lhs+6\n");
    return 1;
}

static int emit_wide_word_factor(Expr *left, Expr *right)
{
    while (right->kind == EX_CAST && right->type.base == TY_LONGLONG && !right->type.pointers) {
        right = right->left;
    }

    Type source = value_type(right->type);

    if (!word_integer(source) || width(source) != 2 || !compare_memory_operand(right, 0))
        return 0;

    emit_wide_operand(left);
    code("    lda ");
    compare_memory_operand(right, 1);
    code("\n");
    helper(source.is_unsigned ? "__umul64_word" : "__smul64_word");
    return 1;
}

static int emit_wide_add_unsigned_word(Expr *left, Expr *right)
{
    Expr *input = right;

    while (input->kind == EX_CAST && input->type.base == TY_LONGLONG && !input->type.pointers) {
        input = input->left;
    }

    Type t = value_type(input->type);

    if (!wide_scalar(value_type(left->type)) || !known_integer(t) || !t.is_unsigned ||
        input->kind == EX_INT || body_effect(left) || body_effect(input))
        return 0;

    emit_value(input);
    push_value(t);
    emit_wide_operand(left);
    pop_value(t);
    code("    clc\n    adc z:__arith_lhs\n    sta z:__arith_lhs\n    bcc :+\n"
         "    inc z:__arith_lhs+2\n    bne :+\n"
         "    inc z:__arith_lhs+4\n    bne :+\n    inc z:__arith_lhs+6\n:\n");
    return 1;
}

static void emit_wide_shift_count(Expr *right, Type t)
{
    uint32_t count;

    unsigned i, offset;
    Symbol *home;

    if (integer_constant(right, &count)) {
        code("    lda #$%04X\n    sta z:__arith_lhs+8\n", count & 65535u);
        return;
    }
    if (compare_memory_operand(right, 0)) {
        code("    lda ");
        compare_memory_operand(right, 1);
        code("\n    sta z:__arith_lhs+8\n");
        return;
    }

    if (wide_scalar(value_type(right->type))) {
        if (!(home = wide_fixed_home(right, &offset))) {
            emit_wide_rhs(right, t);
            return;
        }

        code("    lda ");
        array_operand(home, offset);
        code("\n    sta z:__arith_lhs+8\n");

        if (volatile_expression(right))
            for (i = 2; i < 8; i += 2) {
                code("    lda ");
                array_operand(home, offset + i);
                code("\n");
            }

        return;
    }

    /* The shift helper consumes only the low word of the count */
    for (i = 8; i; i -= 2) {
        code("    lda z:__arith_lhs+%u\n    pha\n", i - 2);
    }

    emit_value(right);
    code("    sta z:__arith_lhs+8\n");

    for (i = 0; i < 8; i += 2) {
        code("    pla\n    sta z:__arith_lhs+%u\n", i);
    }
}

static int emit_wide_rotate(Expr *left, Expr *right)
{
    Symbol *home;

    unsigned offset, other, i, shift, words;
    int bits;

    if (left->kind != EX_BINARY || right->kind != EX_BINARY)
        return 0;

    if (left->op == TOK_SHL) {
        Expr *swap = left;

        left = right;
        right = swap;
    }

    if (left->op != TOK_SHR || right->op != TOK_SHL || left->type.base != TY_LONGLONG ||
        right->type.base != TY_LONGLONG || left->right->kind != EX_INT ||
        right->right->kind != EX_INT || left->right->value_high || right->right->value_high ||
        !(shift = left->right->value) || shift >= 64 || right->right->value != 64 - shift ||
        volatile_expression(left) || volatile_expression(right) ||
        !(home = wide_fixed_home(left->left, &offset)) ||
        wide_fixed_home(right->left, &other) != home || offset != other)
        return 0;

    words = (shift + 8) / 16;
    bits = (int)shift - (int)words * 16;

    for (i = 0; i < 8; i += 2) {
        code("    lda ");
        array_operand(home, offset + (i + 2 * words) % 8);
        code("\n    sta z:__arith_lhs+%u\n", i);
    }

    if (bits) {
        unsigned count = (unsigned)(bits > 0 ? bits : -bits);

        if (count > 1)
            code("    ldx #%u\n:\n", count);

        if (bits > 0) {
            code("    lda z:__arith_lhs\n    lsr a\n");

            for (i = 8; i; i -= 2) {
                code("    ror z:__arith_lhs+%u\n", i - 2);
            }
        } else {
            code("    lda z:__arith_lhs+6\n    asl a\n");

            for (i = 0; i < 8; i += 2) {
                code("    rol z:__arith_lhs+%u\n", i);
            }
        }

        if (count > 1)
            code("    dex\n    bne :-\n");
    }

    if (!left->type.is_unsigned) {
        /* The original sign now sits immediately below the sign-fill bits */
        unsigned sign = 63 - shift, mask = 1u << (sign % 16);
        i = 2 * (sign / 16);
        code("    lda z:__arith_lhs+%u\n    bit #$%04X\n    beq :+\n", i, mask);

        if (mask != 0x8000)
            code("    ora #$%04X\n    sta z:__arith_lhs+%u\n", (0u - 2 * mask) & 65535u, i);

        if (i < 6) {
            code("    lda #$FFFF\n");

            for (i += 2; i < 8; i += 2) {
                code("    sta z:__arith_lhs+%u\n", i);
            }
        }

        code(":\n");
    }

    return 1;
}

static void emit_wide_binary(Expr *left, Expr *right, int op)
{
    int shift = op == TOK_SHL || op == TOK_SHR;

    Type t = shift ? promoted(left->type) : common_type(left->type, right->type);
    int bytes = wide_word_shift_bytes(t, op, right);

    unsigned offset;
    Symbol *home;

    if (!cg.parser->no_strength_reduction && op == '|' && t.base == TY_LONGLONG &&
        emit_wide_rotate(left, right))
        return;
    if (!cg.parser->no_strength_reduction && !cg.function->symbol->interrupt &&
        t.base == TY_LONGLONG && op == '*' &&
        (emit_wide_signed_long_product(left, right) || emit_wide_narrow_product(left, right, t) ||
         emit_wide_word_factor(left, right)))
        return;
    if (!cg.parser->no_strength_reduction && t.base == TY_LONGLONG && op == '+' &&
        (emit_wide_add_unsigned_word(left, right) || emit_wide_add_unsigned_word(right, left)))
        return;

    if (!cg.parser->no_strength_reduction && op == '/' && t.base == TY_LONGLONG && t.is_unsigned) {
        Expr *shift_count;
        int power = wide_power_divisor(right, &shift_count);

        if (power >= 0) {
            Expr count = {0}, sum = {0}, input = {0};

            count.kind = EX_INT;
            count.type = type(TY_INT, 1);
            count.value = (unsigned)power;
            input.kind = EX_CAST;
            input.type = t;
            input.left = left;
            sum.kind = EX_BINARY;
            sum.op = '+';
            sum.left = shift_count;
            sum.right = &count;

            if (shift_count)
                sum.type = common_type(shift_count->type, count.type);

            emit_wide_binary(&input, shift_count ? (power ? &sum : shift_count) : &count, TOK_SHR);
            return;
        }
    }

    if (bytes >= 0) {
        emit_wide_as(left, t);
        emit_wide_word_shift(t, op, (unsigned)bytes, NULL, 0);
        return;
    }
    if (shift) {
        emit_wide_as(left, t);
        emit_wide_shift_count(right, t);
        emit_wide_operation(t, op);
        return;
    }

    if (!cg.parser->no_strength_reduction && t.base == TY_LONGLONG && basic_integer_op(op)) {
        if (op != '-' && wide_integer_literal(left)) {
            Expr *swap = left;

            left = right;
            right = swap;
        }

        if (wide_integer_literal(right)) {
            emit_wide_as(left, t);
            emit_wide_immediate_operation(op, right);
            return;
        }
    }

    if (t.base == TY_LONGLONG && value_type(right->type).base == TY_LONGLONG &&
        basic_integer_op(op) && (home = wide_fixed_home(right, &offset)) != NULL) {
        Symbol *left_home = NULL;

        unsigned left_offset = 0;

        if (!cg.parser->no_strength_reduction && value_type(left->type).base == TY_LONGLONG &&
            !volatile_expression(left) && !volatile_expression(right))
            left_home = wide_fixed_home(left, &left_offset);
        if (!left_home)
            emit_wide_as(left, t);

        emit_wide_word_operation(op, left_home, left_offset, home, offset);
        return;
    }

    emit_wide_pair(left, right, t);
    emit_wide_operation(t, op);
}

/* A/X contain the already-read narrow destination. Compute at the usual
 * wide arithmetic type, then convert the result back to that destination. */
static void emit_narrow_wide_operation_loaded(Expr *e)
{
    Type source = value_type(e->left->type), word = type(TY_LONG, 0);
    Type common = common_type(e->left->type, e->right->type);

    unsigned i;
    cg.arithmetic = 1;
    word.is_unsigned = source.is_unsigned;
    convert_registers(source, word);
    code("    sta z:__arith_lhs\n    stx z:__arith_lhs+2\n");

    if (source.is_unsigned)
        code("    lda #0\n");
    else
        code("    txa\n    cmp #$8000\n    lda #0\n    bcc :+\n    lda #$FFFF\n:\n");

    for (i = 4; i < 8; i += 2) {
        code("    sta z:__arith_lhs+%u\n", i);
    }

    if (common.base == TY_DOUBLE)
        helper(source.is_unsigned ? "__ufloat64_64" : "__sfloat64_64");

    emit_wide_rhs(e->right, common);
    emit_wide_operation(common, e->op);

    if (common.base == TY_DOUBLE)
        helper(e->type.is_unsigned ? "__ufix64_32" : "__fix64_32");

    code("    lda z:__arith_lhs\n");

    if (reg_width(e->type) == 4)
        code("    ldx z:__arith_lhs+2\n");

    narrow_char(e->type);
}

static void emit_narrow_wide_compound(Expr *e)
{
    int far = e->left->type.banked;
    int wram = e->left->kind == EX_DEREF && strength_wram_pointer(e->left->left);

    emit_address(e->left);

    if (far) {
        Type address = far_type(type(TY_CHAR, 1));

        push_value(address);
        far_load(e->left->type);
    } else {
        code("    pha\n    tax\n");
        load_indirect(e->left->type, wram);
    }

    emit_narrow_wide_operation_loaded(e);

    if (far) {
        far_store(e->type, 0);
        cleanup(4, e->type);
    } else
        store_saved_address(e->type, wram, 0);

    divmod_written(e->left);
}

/* Address is in A (near) or A/X (far). Transfer four words without
 * borrowing Y across expression evaluation or overlapping the value slot. */
static void emit_wide_indirect_load(int far)
{
    unsigned i;

    cg.arithmetic = 1;

    if (far) {
        code("    sta z:__arith_lhs+28\n    stx z:__arith_lhs+30\n    phy\n");

        for (i = 0; i < 8; i += 2) {
            code("    ldy #$%04X\n    lda [__arith_lhs+28],y\n    sta z:__arith_lhs+%u\n", i, i);
        }

        code("    ply\n");
    } else {
        code("    tax\n");

        for (i = 0; i < 8; i += 2) {
            code("    lda a:$%04X,x\n    sta z:__arith_lhs+%u\n", i, i);
        }
    }
}

static void emit_wide_save_address(Expr *e)
{
    emit_address(e);

    if (e->type.banked)
        code("    phx\n");

    code("    pha\n");
}

static void emit_wide_store_saved(int far)
{
    unsigned i;

    if (far) {
        code("    pla\n    sta z:__arith_lhs+28\n    pla\n    sta z:__arith_lhs+30\n    phy\n");

        for (i = 0; i < 8; i += 2) {
            code("    ldy #$%04X\n    lda z:__arith_lhs+%u\n    sta [__arith_lhs+28],y\n", i, i);
        }

        code("    ply\n");
    } else {
        code("    plx\n");

        for (i = 0; i < 8; i += 2) {
            code("    lda z:__arith_lhs+%u\n    sta a:$%04X,x\n", i, i);
        }
    }
}

static void emit_wide_value(Expr *e)
{
    unsigned i, offset;
    Symbol *home;

    if (!wide_scalar(value_type(e->type))) {
        emit_wide_operand(e);
        return;
    }

    cg.arithmetic = 1;

    switch (e->kind) {
    case EX_INT:
        emit_wide_literal(e, 0);
        return;
    case EX_OBJECT:
    case EX_MEMBER:
    case EX_DEREF:
        home = wide_fixed_home(e, &offset);

        if (!home) {
            emit_address(e);
            emit_wide_indirect_load(e->type.banked);
            return;
        }

        for (i = 0; i < 8; i += 2) {
            code("    lda ");
            array_operand(home, offset + i);
            code("\n    sta z:__arith_lhs+%u\n", i);
        }

        return;
    case EX_CAST: {
        Type source = value_type(e->left->type);

        if (e->type.base == TY_LONGLONG && source.pointers) {
            emit_value(e->left);
            code("    sta z:__arith_lhs\n");

            if (far_pointer(source))
                code("    stx z:__arith_lhs+2\n");
            else
                code("    stz z:__arith_lhs+2\n");

            code("    stz z:__arith_lhs+4\n    stz z:__arith_lhs+6\n");
            return;
        }

        if (e->type.base == TY_LONGLONG && source.base == TY_FLOAT) {
            emit_value(e->left);
            code("    sta z:__arith_lhs\n    stx z:__arith_lhs+2\n");
            helper("__fext32_64");
            helper(e->type.is_unsigned ? "__ufix64_64" : "__fix64_64");
            return;
        }

        if (e->type.base == TY_DOUBLE && source.base == TY_FLOAT) {
            emit_value(e->left);
            code("    sta z:__arith_lhs\n    stx z:__arith_lhs+2\n");
            helper("__fext32_64");
            return;
        }

        if (e->type.base == TY_DOUBLE && source.base != TY_DOUBLE) {
            if (wide_scalar(source)) {
                emit_wide_operand(e->left);
                helper(source.is_unsigned ? "__ufloat64_64" : "__sfloat64_64");
            } else {
                Type word = type(TY_LONG, 0);

                word.is_unsigned = source.is_unsigned;
                emit_value(e->left);
                convert_registers(source, word);
                code("    sta z:__arith_lhs\n    stx z:__arith_lhs+2\n");
                helper(source.is_unsigned ? "__ufloat64_32" : "__sfloat64_32");
            }

            return;
        }

        emit_wide_operand(e->left);

        if (source.base == TY_DOUBLE && e->type.base == TY_LONGLONG)
            helper(e->type.is_unsigned ? "__ufix64_64" : "__fix64_64");

        return;
    }
    case EX_CALL:
        emit_call(e, 1);
        return;
    case EX_ASSIGN:
        emit_wide_assignment(e, 0);
        return;
    case EX_PRE:
    case EX_POST:
        emit_wide_update(e, 0);
        return;
    case EX_CHOOSE: {
        Expr *word = wide_word_magnitude_source(e);

        if (word) {
            emit_word_magnitude(word);
            code("    sta z:__arith_lhs\n    stz z:__arith_lhs+2\n    stz z:__arith_lhs+4\n    stz "
                 "z:__arith_lhs+6\n");
            return;
        }

        unsigned yes = ++cg.label, no = ++cg.label, end = ++cg.label;
        branch(e->left, yes, no, yes);
        label(yes);
        emit_wide_operand(e->right);
        jump(end);
        label(no);
        emit_wide_operand(e->third);
        label(end);
        return;
    }
    case EX_COMMA:
        emit_discarded(e->left);
        emit_wide_operand(e->right);
        return;
    case EX_UNARY:
        if (!cg.parser->no_strength_reduction && e->type.base == TY_LONGLONG && e->op == '-') {
            Expr *word = wide_word_source(e->left);

            if (word) {
                emit_value(word);
                code("    tax\n    lda #0\n    cpx #1\n    bcc :+\n");

                if (!word->type.is_unsigned)
                    code("    cpx #$8000\n    bcs :+\n");

                code("    dec a\n:\n    sta z:__arith_lhs+2\n    sta z:__arith_lhs+4\n"
                     "    sta z:__arith_lhs+6\n    txa\n    eor #$FFFF\n    inc a\n    sta "
                     "z:__arith_lhs\n");
                return;
            }
        }

        if (!cg.parser->no_strength_reduction && e->type.base == TY_LONGLONG && e->op != '+' &&
            !volatile_expression(e->left) && (home = wide_fixed_home(e->left, &offset)) != NULL) {
            if (e->op == '-')
                code("    sec\n");

            for (i = 0; i < 8; i += 2) {
                code(e->op == '-' ? "    lda #0\n    sbc " : "    lda ");
                array_operand(home, offset + i);
                code("\n");

                if (e->op == '~')
                    code("    eor #$FFFF\n");

                code("    sta z:__arith_lhs+%u\n", i);
            }

            return;
        }

        emit_wide_operand(e->left);

        if (e->op == '+')
            return;
        if (e->type.base == TY_DOUBLE) {
            code("    lda z:__arith_lhs+6\n    eor #$8000\n    sta z:__arith_lhs+6\n");
            return;
        }
        if (e->op == '-')
            code("    sec\n");

        for (i = 0; i < 8; i += 2) {
            if (e->op == '-')
                code("    lda #0\n    sbc z:__arith_lhs+%u\n", i);
            else
                code("    lda z:__arith_lhs+%u\n    eor #$FFFF\n", i);

            code("    sta z:__arith_lhs+%u\n", i);
        }

        return;
    case EX_BINARY:
        emit_wide_binary(e->left, e->right, e->op);
        return;
    default:
        error_at(e->location, "unsupported 64-bit runtime expression");
    }
}

/* The left operand is already in the wide result slot. Compound assignment
 * performs the usual arithmetic conversions before converting back. */
static void emit_wide_compound_loaded(Expr *e)
{
    Type t = (e->op == TOK_SHL || e->op == TOK_SHR) ? promoted(e->left->type)
                                                    : common_type(e->left->type, e->right->type);
    int integer_destination = e->type.base == TY_LONGLONG;
    int bytes = wide_word_shift_bytes(t, e->op, e->right);

    if (integer_destination && t.base == TY_FLOAT) {
        Type single = type(TY_FLOAT, 0);

        helper(e->type.is_unsigned ? "__ufloat32_64" : "__sfloat32_64");
        code("    lda z:__arith_lhs\n    ldx z:__arith_lhs+2\n");
        push_value(single);
        emit_value(e->right);
        stage(1, single);
        pop_value(single);
        stage(0, single);
        binary_loaded(e->op, single, 0);
        code("    sta z:__arith_lhs\n    stx z:__arith_lhs+2\n");
        helper("__fext32_64");
        helper(e->type.is_unsigned ? "__ufix64_64" : "__fix64_64");
        return;
    }

    if (integer_destination && t.base == TY_DOUBLE)
        helper(e->type.is_unsigned ? "__ufloat64_64" : "__sfloat64_64");
    if (bytes >= 0) {
        emit_wide_word_shift(t, e->op, (unsigned)bytes, NULL, 0);
        return;
    }
    if (!cg.parser->no_strength_reduction && t.base == TY_LONGLONG && basic_integer_op(e->op) &&
        wide_integer_literal(e->right)) {
        emit_wide_immediate_operation(e->op, e->right);
        return;
    }

    if (e->op == TOK_SHL || e->op == TOK_SHR)
        emit_wide_shift_count(e->right, t);
    else
        emit_wide_rhs(e->right, t);

    emit_wide_operation(t, e->op);

    if (integer_destination && t.base == TY_DOUBLE)
        helper(e->type.is_unsigned ? "__ufix64_64" : "__fix64_64");
}

static Symbol *vr_base(Expr *e);

static int add_fixed_wide_shift(Expr *e, Symbol *home, unsigned offset)
{
    Expr *shift = e->right, *input;

    Type source;
    int bytes;

    if ((e->op != '+' && e->op != '-') || e->type.base != TY_LONGLONG || volatile_expression(e) ||
        shift->kind != EX_BINARY || shift->op != TOK_SHL ||
        (bytes = wide_word_shift_bytes(shift->type, shift->op, shift->right)) <= 0 ||
        body_effect(shift->left))
        return 0;

    input = shift->left;

    while (input->kind == EX_CAST && input->type.base == TY_LONGLONG && !input->type.pointers) {
        input = input->left;
    }

    source = value_type(input->type);

    if (bytes >= 4 && numeric(source) && source.base != TY_FLOAT && !wide_scalar(source)) {
        Type retained = type(bytes == 6 ? TY_INT : TY_LONG, source.is_unsigned);

        cg.arithmetic = 1;
        emit_value(input);
        convert_registers(source, retained);
        code("    sta z:__arith_lhs\n");

        if (bytes == 4)
            code("    stx z:__arith_lhs+2\n");
    } else
        emit_wide_operand(shift->left);

    code(e->op == '+' ? "    clc\n" : "    sec\n");

    for (unsigned i = (unsigned)bytes; i < 8; i += 2) {
        code("    lda ");
        array_operand(home, offset + i);
        code("\n    %s z:__arith_lhs+%u\n    sta ", wide_word_instruction(e->op),
             i - (unsigned)bytes);
        array_operand(home, offset + i);
        code("\n");
    }

    return 1;
}

static int update_fixed_wide_mask(Expr *e, Symbol *home, unsigned offset)
{
    Expr *literal = e->right;
    uint64_t bits;

    unsigned i, source_offset;
    int op = e->op;

    if (cg.parser->no_strength_reduction || e->type.base != TY_LONGLONG || volatile_expression(e))
        return 0;
    if (!op && literal->kind == EX_CAST && literal->left->type.base == TY_LONGLONG &&
        wide_scalar(value_type(literal->left->type)))
        literal = literal->left;

    if (!op && literal->kind == EX_BINARY &&
        wide_fixed_home(literal->left, &source_offset) == home && source_offset == offset) {
        op = literal->op;
        literal = literal->right;
    }

    if ((op != '&' && op != '|' && op != '^') || !wide_integer_literal(literal))
        return 0;

    bits =
        initializer_cast64(((uint64_t)literal->value_high << 32) | literal->value, literal->type);

    for (i = 0; i < 8; i += 2) {
        unsigned word = (unsigned)(bits >> (8 * i)) & 65535;

        if (word == (op == '&' ? 65535u : 0u))
            continue;
        if (op == '&' && !word && !home->owner && !home->type.banked) {
            code("    stz ");
            array_operand(home, offset + i);
            code("\n");
            continue;
        }

        if ((op == '&' && !word) || (op == '|' && word == 65535u))
            code("    lda #$%04X\n", word);
        else {
            code("    lda ");
            array_operand(home, offset + i);
            code("\n    %s #$%04X\n", wide_word_instruction(op), word);
        }

        code("    sta ");
        array_operand(home, offset + i);
        code("\n");
    }

    return 1;
}

enum { WIDEN_FULL, WIDEN_HIGH, WIDEN_LOW };

static int store_widened_integer(Expr *e, Symbol *home, unsigned offset, int part)
{
    Expr *input = e->right;

    Type source, word = type(TY_LONG, 0);

    unsigned i, start = part == WIDEN_HIGH ? 4 : 0;

    if (cg.parser->no_strength_reduction || e->op || e->type.base != TY_LONGLONG ||
        volatile_expression(e))
        return 0;

    while (input->kind == EX_CAST && input->type.base == TY_LONGLONG && !input->type.pointers) {
        input = input->left;
    }

    source = value_type(input->type);

    if (!numeric(source) || source.base == TY_FLOAT || wide_scalar(source))
        return 0;

    word.is_unsigned = source.is_unsigned;
    emit_value(input);
    convert_registers(source, word);
    code("    sta ");
    array_operand(home, offset + start);
    code("\n    txa\n    sta ");
    array_operand(home, offset + start + 2);
    code("\n");

    if (part != WIDEN_FULL || source.is_unsigned)
        code("    lda #0\n");
    else
        code("    asl a\n    lda #0\n    bcc :+\n    dec a\n:\n");

    for (i = 0; i < 4; i += 2) {
        code("    sta ");
        array_operand(home, offset + 4 - start + i);
        code("\n");
    }

    return 1;
}

static int adjacent_widened_store(Statement *s)
{
    Expr *store = s->expression, *update;
    Symbol *home;

    unsigned offset;
    int part;
    uint64_t value;

    if (cg.parser->no_strength_reduction || !store || store->kind != EX_ASSIGN || store->op ||
        store->type.base != TY_LONGLONG || !store->type.is_unsigned || store->type.pointers ||
        !s->next || s->next->kind != ST_EXPR || !(update = s->next->expression) ||
        update->kind != EX_ASSIGN || !wide_integer_literal(update->right) ||
        !body_equal(store->left, update->left) || !(home = wide_fixed_home(store->left, &offset)))
        return 0;

    value = initializer_cast64(((uint64_t)update->right->value_high << 32) | update->right->value,
                               update->right->type);

    if (update->op == TOK_SHL && value == 32)
        part = WIDEN_HIGH;
    else if (update->op == '&' && value == UINT32_MAX)
        part = WIDEN_LOW;
    else
        return 0;

    if (!store_widened_integer(store, home, offset, part))
        return 0;

    divmod_written(store->left);
    return 1;
}

static int copy_disjoint_wide_assignment(Expr *e, Symbol *home, unsigned offset)
{
    Expr *input = e->right;

    unsigned i, source_offset;
    Symbol *source;

    if (cg.parser->no_strength_reduction || e->op || input->type.base != e->type.base ||
        !wide_scalar(value_type(input->type)) || volatile_expression(e))
        return 0;

    source = wide_fixed_home(input, &source_offset);

    if (source == home)
        return 0;

    if (!source) {
        Symbol *base;

        if (input->kind != EX_DEREF || far_pointer(value_type(input->left->type)) ||
            !(base = vr_base(input->left)) || base == home)
            return 0;

        emit_address_x(input);
    }

    for (i = 0; i < 8; i += 2) {
        code("    lda ");

        if (source)
            array_operand(source, source_offset + i);
        else
            code("a:$%04X,x", i);

        code("\n    sta ");
        array_operand(home, offset + i);
        code("\n");
    }

    return 1;
}

static int discarded_fixed_wide_assignment(Expr *e, Symbol *home, unsigned offset)
{
    Expr *value = e->right, *input = value;
    Symbol *source, *right = NULL;

    unsigned i, source_offset, right_offset = 0;
    int base = e->left->type.base, unary = 0;

    if (e->op || home->owner || home->type.banked || value->type.base != base ||
        !wide_scalar(value_type(value->type)))
        return 0;

    if (value->kind == EX_UNARY && (value->op == '-' || value->op == '~')) {
        unary = value->op;
        input = value->left;
    } else if (value->kind == EX_BINARY && base == TY_LONGLONG && basic_integer_op(value->op)) {
        if (value->right->type.base != base || !wide_scalar(value_type(value->right->type)) ||
            !(right = wide_fixed_home(value->right, &right_offset)))
            return 0;

        input = value->left;
    }

    if (!wide_scalar(value_type(input->type)) || input->type.base != base ||
        !(source = wide_fixed_home(input, &source_offset)))
        return 0;

    /* Keep all reads in operand order before any destination writes.
     * The last result word stays in A while X stores the first three. */
    cg.arithmetic = 1;

    if (unary == '-' && base == TY_LONGLONG)
        code("    sec\n");

    for (i = 0; i < 8; i += 2) {
        if (unary == '-' && base == TY_LONGLONG)
            code("    lda #0\n    sbc ");
        else if (right && i == 6 && !source->owner && !source->type.banked)
            code("    ldx ");
        else
            code("    lda ");

        array_operand(source, source_offset + i);
        code("\n");

        if (unary == '~')
            code("    eor #$FFFF\n");
        if (unary == '-' && base == TY_DOUBLE && i == 6)
            code("    eor #$8000\n");

        if (i < 6)
            code("    sta z:__arith_lhs+%u\n", i);
        else if (right && (source->owner || source->type.banked))
            code("    tax\n");
    }

    if (right) {
        if (value->op == '+' || value->op == '-')
            code(value->op == '+' ? "    clc\n" : "    sec\n");

        for (i = 0; i < 8; i += 2) {
            if (i < 6)
                code("    lda z:__arith_lhs+%u\n", i);
            else
                code("    txa\n");

            code("    %s ", wide_word_instruction(value->op));
            array_operand(right, right_offset + i);
            code("\n");

            if (i < 6)
                code("    sta z:__arith_lhs+%u\n", i);
        }
    }

    for (i = 0; i < 6; i += 2) {
        code("    ldx z:__arith_lhs+%u\n    stx ", i);
        array_operand(home, offset + i);
        code("\n");
    }

    code("    sta ");
    array_operand(home, offset + 6);
    code("\n");
    return 1;
}

static int store_wide_integer_literal(Expr *e, Symbol *home, unsigned offset)
{
    Expr *literal = e->right;

    unsigned loaded = 65536;
    uint64_t bits;

    if (cg.parser->no_strength_reduction || e->op || e->type.base != TY_LONGLONG ||
        !wide_integer_literal(literal) || volatile_expression(e))
        return 0;

    if (!home) {
        if (e->left->type.banked)
            return 0;

        emit_address_x(e->left);
    }

    bits =
        initializer_cast64(((uint64_t)literal->value_high << 32) | literal->value, literal->type);

    for (unsigned i = 0; i < 8; i += 2) {
        unsigned word = (unsigned)(bits >> (8 * i)) & 65535;

        if (!word && (!home || (!home->owner && !home->type.banked)))
            code("    stz ");
        else {
            if (word != loaded) {
                code("    lda #$%04X\n", word);
                loaded = word;
            }

            code("    sta ");
        }

        if (home) {
            array_operand(home, offset + i);
            code("\n");
        } else
            code("a:$%04X,x\n", i);
    }

    return 1;
}

static void emit_wide_assignment(Expr *e, int discarded)
{
    unsigned i, offset;
    Symbol *home = wide_fixed_home(e->left, &offset);

    if (!home) {
        if (discarded && store_wide_integer_literal(e, NULL, 0))
            return;

        if (discarded && !cg.parser->no_strength_reduction && !e->op && e->left->kind == EX_DEREF &&
            !e->left->type.banked && e->left->left->kind == EX_OBJECT && !volatile_expression(e) &&
            !body_effect(e->right)) {
            emit_wide_as(e->right, e->type);
            emit_address_x(e->left);

            for (i = 0; i < 8; i += 2) {
                code("    lda z:__arith_lhs+%u\n    sta a:$%04X,x\n", i, i);
            }

            return;
        }

        emit_wide_save_address(e->left);

        if (e->op) {
            emit_wide_indirect_load(e->left->type.banked);
            emit_wide_compound_loaded(e);
        } else
            emit_wide_as(e->right, e->type);

        emit_wide_store_saved(e->left->type.banked);
        return;
    }

    if (discarded && !volatile_expression(e)) {
        Type t = promoted(e->type);
        int bytes = wide_word_shift_bytes(t, e->op, e->right);

        if (bytes >= 0) {
            emit_wide_word_shift(t, e->op, (unsigned)bytes, home, offset);
            return;
        }
    }

    if (discarded &&
        (add_fixed_wide_shift(e, home, offset) || update_fixed_wide_mask(e, home, offset) ||
         store_wide_integer_literal(e, home, offset) ||
         copy_disjoint_wide_assignment(e, home, offset) ||
         store_widened_integer(e, home, offset, WIDEN_FULL) ||
         discarded_fixed_wide_assignment(e, home, offset)))
        return;

    if (e->op) {
        emit_wide_operand(e->left);
        emit_wide_compound_loaded(e);
    } else
        emit_wide_as(e->right, e->type);

    for (i = 0; i < 8; i += 2) {
        code("    lda z:__arith_lhs+%u\n    sta ", i);
        array_operand(home, offset + i);
        code("\n");
    }
}

static void emit_wide_update(Expr *e, int discarded)
{
    unsigned i, offset;
    Symbol *home = wide_fixed_home(e->left, &offset);

    if (!cg.parser->no_strength_reduction && home && e->type.base == TY_LONGLONG &&
        !volatile_expression(e->left)) {
        int inc = e->op == TOK_INC, post = e->kind == EX_POST;

        unsigned done = discarded ? ++cg.label : 0;

        if (!discarded)
            cg.arithmetic = 1;

        code(inc ? "    clc\n" : "    sec\n");

        for (i = 0; i < 8; i += 2) {
            code("    lda ");
            array_operand(home, offset + i);
            code("\n");

            if (!discarded && post)
                code("    sta z:__arith_lhs+%u\n", i);

            code("    %s #$%04X\n    sta ", inc ? "adc" : "sbc", i ? 0 : 1);
            array_operand(home, offset + i);
            code("\n");

            if (!discarded && !post)
                code("    sta z:__arith_lhs+%u\n", i);
            if (discarded && i < 6)
                code("    %s cg_%s_%u\n", inc ? "bcc" : "bcs", cg.parser->unit, done);
        }

        if (discarded)
            label(done);

        return;
    }

    if (home)
        emit_wide_operand(e->left);
    else {
        emit_wide_save_address(e->left);
        emit_wide_indirect_load(e->left->type.banked);
    }

    if (e->type.base == TY_DOUBLE) {
        int post = e->kind == EX_POST, far = e->left->type.banked;

        if (post)
            for (i = 8; i; i -= 2) {
                code("    lda z:__arith_lhs+%u\n    pha\n", i - 2);
            }

        code("    stz z:__arith_lhs+8\n    stz z:__arith_lhs+10\n"
             "    stz z:__arith_lhs+12\n    lda #$3FF0\n    sta z:__arith_lhs+14\n");
        helper(e->op == TOK_INC ? "__dadd" : "__dsub");

        if (home) {
            for (i = 0; i < 8; i += 2) {
                code("    lda z:__arith_lhs+%u\n    sta ", i);
                array_operand(home, offset + i);
                code("\n");
            }
        } else if (!post)
            emit_wide_store_saved(far);
        else if (far) {
            code("    lda 9,s\n    sta z:__arith_lhs+28\n    lda 11,s\n    sta z:__arith_lhs+30\n  "
                 "  phy\n");

            for (i = 0; i < 8; i += 2) {
                code("    ldy #$%04X\n    lda z:__arith_lhs+%u\n    sta [__arith_lhs+28],y\n", i,
                     i);
            }

            code("    ply\n");
        } else {
            code("    lda 9,s\n    tax\n");

            for (i = 0; i < 8; i += 2) {
                code("    lda z:__arith_lhs+%u\n    sta a:$%04X,x\n", i, i);
            }
        }

        if (post) {
            for (i = 0; i < 8; i += 2) {
                code("    pla\n    sta z:__arith_lhs+%u\n", i);
            }

            if (!home) {
                code("    plx\n");

                if (far)
                    code("    plx\n");
            }
        }

        return;
    }

    if (e->kind == EX_POST)
        for (i = 0; i < 8; i += 2) {
            code("    lda z:__arith_lhs+%u\n    sta z:__arith_lhs+%u\n", i, i + 8);
        }

    code(e->op == TOK_INC ? "    clc\n" : "    sec\n");

    for (i = 0; i < 8; i += 2) {
        code("    lda z:__arith_lhs+%u\n    %s #$%04X\n    sta z:__arith_lhs+%u\n", i,
             e->op == TOK_INC ? "adc" : "sbc", i ? 0 : 1, i);
    }

    if (!home)
        emit_wide_store_saved(e->left->type.banked);
    else
        for (i = 0; i < 8; i += 2) {
            code("    lda z:__arith_lhs+%u\n    sta ", i);
            array_operand(home, offset + i);
            code("\n");
        }

    if (e->kind == EX_POST)
        for (i = 0; i < 8; i += 2) {
            code("    lda z:__arith_lhs+%u\n    sta z:__arith_lhs+%u\n", i + 8, i);
        }
}

static void emit_wide_narrow(Expr *e)
{
    Expr *source = e->left;

    unsigned offset = 0;
    int bytes = -1, byte_result = !e->type.pointers && e->type.base == TY_CHAR;

    unsigned result_bytes = byte_result ? 1 : reg_width(e->type);
    uint32_t mask, needed = result_bytes == 4 ? UINT32_MAX : (1u << (8 * result_bytes)) - 1u;

    if (e->type.is_bool && !e->type.pointers) {
        unsigned yes = ++cg.label, no = ++cg.label, end = ++cg.label;
        branch(e->left, yes, no, yes);
        label(yes);
        code("    lda #1\n");
        jump(end);
        label(no);
        code("    lda #0\n");
        label(end);
        return;
    }

    if (!cg.parser->no_strength_reduction && !e->type.pointers && e->type.base != TY_FLOAT &&
        source->kind == EX_BINARY && source->op == '&' && integer_constant(source->right, &mask) &&
        (mask & needed) == needed)
        source = source->left;

    if (source->kind == EX_BINARY && source->op == TOK_SHR && e->type.base != TY_FLOAT) {
        Type t = promoted(source->left->type);

        bytes = wide_word_shift_bytes(t, TOK_SHR, source->right);

        if (bytes < 0 && !cg.parser->no_strength_reduction && !cg.parser->no_byte_shuffles &&
            t.base == TY_LONGLONG && integer_constant(source->right, &mask) && !(mask & 7))
            bytes = (int)((mask & 63) / 8);
    }

    if (bytes >= 0 && bytes + (int)result_bytes <= 8) {
        Expr *input = source->left;
        Symbol *home = volatile_expression(input) ? NULL : wide_fixed_home(input, &offset);
        int last_byte = byte_result && bytes == 7;

        offset += (unsigned)bytes;

        if (home) {
            if (reg_width(e->type) == 4) {
                code("    lda ");
                array_operand(home, offset + 2);
                code("\n    tax\n");
            }

            if (last_byte)
                code("    sep #$20\n.a8\n");

            code("    lda ");
            array_operand(home, offset);
            code("\n");
        } else {
            emit_wide_operand(input);

            if (last_byte)
                code("    sep #$20\n.a8\n");

            code("    lda z:__arith_lhs+%u\n", offset);

            if (reg_width(e->type) == 4)
                code("    ldx z:__arith_lhs+%u\n", offset + 2);
        }

        if (last_byte)
            code("    rep #$20\n.a16\n");
    } else {
        emit_wide_operand(source);

        if (source->type.base == TY_DOUBLE)
            helper(e->type.base == TY_FLOAT ? "__ftrunc64_32"
                   : e->type.is_unsigned    ? "__ufix64_32"
                                            : "__fix64_32");
        else if (!e->type.pointers && e->type.base == TY_FLOAT)
            helper(source->type.is_unsigned ? "__ufloat32_64" : "__sfloat32_64");

        code("    lda z:__arith_lhs\n");

        if (reg_width(e->type) == 4)
            code("    ldx z:__arith_lhs+2\n");
    }

    if (e->type.pointers && far_pointer(e->type))
        code("    pha\n    txa\n    and #$00FF\n    tax\n    pla\n");

    narrow_char(e->type);
}

static int narrow_statements(Statement *s, int allow_return)
{
    for (; s; s = s->next) {
        if ((s->kind == ST_RETURN && !allow_return) || !wide_address_safe(s->expression) ||
            !wide_address_safe(s->step) || !narrow_statements(s->initial, allow_return) ||
            !narrow_statements(s->body, allow_return) ||
            !narrow_statements(s->alternate, allow_return))
            return 0;
    }

    return 1;
}

static int body_step_direction(Expr *e, Symbol *v);
static int body_asm_statements(Statement *s);
static int body_direct_integer_stores(Statement *s, Symbol *index, int literals);

static Symbol *bounded_wide_induction(Statement *s, uint32_t *begin, uint32_t *end)
{
    Statement *initial = body_single(s->initial);
    Expr *test = s->expression, *init;
    Symbol *index;

    if (cg.parser->no_strength_reduction || cg.function->jump_label_count || cg.switch_depth ||
        s->kind != ST_FOR || !test || test->kind != EX_BINARY ||
        (test->op != '<' && test->op != TOK_LE) || test->left->kind != EX_OBJECT ||
        test->left->type.pointers || test->left->type.base != TY_LONGLONG || !initial ||
        initial->next || initial->kind != ST_EXPR || !(init = initial->expression) ||
        init->kind != EX_ASSIGN || init->op || !body_equal(init->left, test->left))
        return NULL;

    index = test->left->symbol;

    if (object_volatile(index->type) ||
        (!loop_private(index) &&
         (index->owner || !body_direct_integer_stores(s->body, index, 0))) ||
        body_step_direction(s->step, index) != 1 || dp_counter_modified(s->body, index) ||
        body_asm_statements(s->body) || wide_unsigned_size(init->right) != 2 ||
        !integer_constant(init->right, begin) || *begin > 65535 ||
        wide_unsigned_size(test->right) != 2 || !integer_constant(test->right, end) || *end > 65535)
        return NULL;

    *end += test->op == TOK_LE;
    return *end <= 65535 ? index : NULL;
}

static Expr *wide_loop_signed_count_bound(Statement *s)
{
    Statement *initial = body_single(s->initial);
    Expr *test = s->expression, *init;
    Symbol *index, *bound;
    uint32_t zero;

    if (cg.parser->no_strength_reduction || cg.parser->no_register_loops ||
        cg.function->jump_label_count || cg.switch_depth || cg.function->symbol->interrupt ||
        s->kind != ST_FOR || !test || test->kind != EX_BINARY || test->op != '<' ||
        test->left->kind != EX_OBJECT || test->right->kind != EX_OBJECT || !initial ||
        initial->next || initial->kind != ST_EXPR || !(init = initial->expression) ||
        init->kind != EX_ASSIGN || init->op || !body_equal(init->left, test->left) ||
        !integer_constant(init->right, &zero) || zero)
        return NULL;

    index = test->left->symbol;
    bound = test->right->symbol;

    if (index == bound || !word_integer(index->type) || !word_integer(bound->type) ||
        width(index->type) != 2 || width(bound->type) != 2 || index->type.is_unsigned ||
        bound->type.is_unsigned || object_volatile(index->type) || object_volatile(bound->type) ||
        !loop_private(index) || !loop_private(bound) || body_step_direction(s->step, index) != 1 ||
        dp_counter_modified(s->body, index) || dp_counter_modified(s->body, bound) ||
        body_asm_statements(s->body) || !compare_memory_operand(test->right, 0))
        return NULL;

    return test->right;
}

static int emit_wide_loop(Statement *s)
{
    /* Complete narrow loops have no live wide temporary at either boundary */
    if (!cg.function->jump_label_count && wide_address_safe(s->expression) &&
        wide_address_safe(s->step) && narrow_statements(s->initial, 0) &&
        narrow_statements(s->body, 0))
        return emit_loop_statement(s);

    unsigned start = ++cg.label, body = ++cg.label, end = ++cg.label, step;
    int falls;
    uint32_t begin, bound = 0;
    Symbol *index = bounded_wide_induction(s, &begin, &bound);
    Expr *signed_bound = wide_loop_signed_count_bound(s);

    if (s->initial)
        emit_statements(s->initial);

    step = s->kind == ST_WHILE ? start : ++cg.label;

    if (cg.loop_count == 64)
        error_at(s->location, "too many nested loops");

    cg.loop_start[cg.loop_count] = step;
    cg.loop_end[cg.loop_count++] = end;
    label(start);

    if (index) {
        code("; bounded wide induction: low word only\n    lda ");
        array_operand(index, 0);
        code("\n    cmp #$%04X\n", bound);
        flag_branch("bcc", "bcs", body, end, body);
    } else if (signed_bound) {
        unsigned nonzero = ++cg.label;
        code("; signed count with unsigned back edge\n");
        emit_value(signed_bound);

        if (!accumulator_zero_flags())
            code("    cmp #0\n");

        flag_branch("beq", "bne", end, nonzero, nonzero);
        label(nonzero);
        flag_branch("bmi", "bpl", end, body, body);
    } else if (s->kind != ST_DO && s->expression)
        branch(s->expression, body, end, body);

    label(body);
    falls = emit_statements(s->body);

    if (s->kind != ST_WHILE)
        label(step);

    if (index) {
        code("    lda ");
        array_operand(index, 0);
        code("\n    inc a\n    sta ");
        array_operand(index, 0);
        code("\n");
    } else if (signed_bound) {
        Symbol *counter = s->expression->left->symbol;

        load_symbol(counter);
        code("    inc a\n");
        store_symbol(counter);
        code("    cmp ");
        compare_memory_operand(signed_bound, 1);
        code("\n");
        flag_branch("bcc", "bcs", body, end, end);
    } else if (s->step) {
        if (wide_assignment_supported(s->step))
            emit_wide_assignment(s->step, 1);
        else if (wide_update_supported(s->step))
            emit_wide_update(s->step, 1);
        else if (wide_narrow_assignment(s->step)) {
            emit_wide_narrow(s->step->right);
            store_symbol(s->step->left->symbol);
        } else if (!volatile_expression(s->step) && strength_update(s->step, 0)) {
        } else
            emit_discarded(s->step);
    }

    if (s->kind == ST_DO)
        branch(s->expression, start, end, end);
    else if (!signed_bound && (falls || s->kind == ST_FOR))
        jump(start);

    --cg.loop_count;
    divmod_state.available = 0;
    label(end);

    if (s->kind != ST_DO && !s->expression && !contains_break(s->body) && !cg.switch_depth)
        return 0;

    return 1;
}

static int shifted_bit_update(Statement *s)
{
    Statement *a = body_single(s->body), *b = body_single(s->alternate);
    Expr *test = s->expression, *yes, *no, *value, *bits, *shift;
    uint32_t mask, count;
    int invert = 0;

    Type t;

    if (cg.parser->no_strength_reduction || cg.function->jump_label_count || !a || !b || a->next ||
        b->next || a->kind != ST_EXPR || b->kind != ST_EXPR || !(yes = a->expression) ||
        !(no = b->expression) || yes->kind != EX_ASSIGN || no->kind != EX_ASSIGN)
        return 0;

    if (test->kind == EX_BINARY && (test->op == TOK_EQ || test->op == TOK_NE) &&
        integer_constant(test->right, &mask) && !mask) {
        invert = test->op == TOK_EQ;
        test = test->left;
    }

    if (invert) {
        Expr *swap = yes;

        yes = no;
        no = swap;
    }

    value = yes->left;
    t = value_type(value->type);

    if (value->kind != EX_OBJECT || t.pointers || t.base != TY_LONG || !t.is_unsigned ||
        volatile_expression(value) || !body_equal(value, no->left) || test->kind != EX_BINARY ||
        test->op != '&' || !body_equal(test->left, value) ||
        !integer_constant(test->right, &mask) || mask != 1)
        return 0;

    bits = yes->right;

    if (yes->op || bits->kind != EX_BINARY || bits->op != '^' ||
        !integer_constant(bits->right, &mask))
        return 0;

    shift = bits->left;

    if (shift->kind != EX_BINARY || shift->op != TOK_SHR || !body_equal(shift->left, value) ||
        !integer_constant(shift->right, &count) || count != 1)
        return 0;

    if (no->op == TOK_SHR) {
        if (!integer_constant(no->right, &count) || count != 1)
            return 0;
    } else if (no->op || !body_equal(no->right, shift))
        return 0;

    code("; shift carry selects the XOR mask\n");

    if (direct_operand(value, t, 0, 0) && direct_operand(value, t, 1, 0)) {
        code("    lda ");
        direct_operand(value, t, 1, 1);
        code("\n    lsr a\n    tax\n    lda ");
        direct_operand(value, t, 0, 1);
        code("\n    ror a\n");

        if (mask >> 16) {
            if (mask & 65535u)
                code("    bcc :+\n    eor #$%04X\n:\n", mask & 65535u);

            code("    sta ");
            array_operand(value->symbol, 0);
            code("\n    txa\n    bcc :+\n    eor #$%04X\n:\n    sta ", mask >> 16);
            array_operand(value->symbol, 2);
            code("\n");
            divmod_state.available = 0;
            return 1;
        }
    } else {
        load_symbol(value->symbol);
        constant_shift32(TOK_SHR, t, 1);
    }

    if (mask) {
        code("    bcc :+\n");

        if (mask & 65535u)
            code("    eor #$%04X\n", mask & 65535u);
        if (mask >> 16)
            code("    pha\n    txa\n    eor #$%04X\n    tax\n    pla\n", mask >> 16);

        code(":\n");
    }

    store_symbol(value->symbol);
    divmod_state.available = 0;
    return 1;
}
