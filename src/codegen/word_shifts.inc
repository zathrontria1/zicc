/* Exact A16 byte shuffles, shared by expression plans and ordinary emission.
 * The final mask/shift always sets full-word N/Z; bare XBA sets byte flags. */
typedef struct {
    unsigned mask, steps;
    int left;
} WordShift;

/* Sign extension is (x XOR sign) - sign after the logical shift */
static unsigned word_shift_sign(Expr *value, int op, Type result, unsigned count)
{
    if (cg.parser->no_strength_reduction || op != TOK_SHR || result.is_unsigned ||
        result.pointers || result.base != TY_INT || count < 3 || count >= 16 ||
        (value->known.valid && value->known.min >= 0) || unsigned_byte_value(value))
        return 0;

    return 1u << (15 - count);
}

static int word_shift_plan(Expr *value, int op, Type result, unsigned count, WordShift *plan)
{
    unsigned zero = value->known.valid ? value->known.zero : 0, cost;
    int left = op == TOK_SHL;

    if (cg.parser->no_byte_shuffles || cg.parser->no_strength_reduction || result.pointers ||
        result.base != TY_INT || !count || count >= 16 || (op != TOK_SHL && op != TOK_SHR))
        return 0;
    if (value->type.base == TY_CHAR && !value->type.pointers && value->type.is_unsigned)
        zero |= 65280;
    if (!left && !result.is_unsigned && !(value->known.valid && value->known.min >= 0) &&
        !unsigned_byte_value(value))
        return 0;

    memset(plan, 0, sizeof *plan);

    if (count >= 8) {
        plan->left = left;
        plan->steps = count - 8;

        if (left) {
            if (count == 8 || (zero & 65280) != 65280)
                plan->mask = 65280;
        } else if (count == 8 || (zero & 255) != 255)
            plan->mask = 255;
    } else {
        unsigned need = left ? ((1u << (8 - count)) - 1u) << 8 : 255u;

        if (left && (zero & 65280) == 65280) {
            plan->left = 0;
            plan->steps = 8 - count;
        } else if (left && count >= 6 && (zero & need) == need) {
            plan->left = 0;
            plan->steps = 8 - count;
            plan->mask = 65280;
        } else if (!left && (zero & 255) == 255) {
            plan->left = 1;
            plan->steps = 8 - count;
        } else
            return 0;
    }

    cost = 3 + (plan->mask ? 3 : 0) + 2 * plan->steps;
    return cost < 2 * count;
}

static int word_shift_loaded(Expr *value, int op, Type result, unsigned count)
{
    WordShift p;

    unsigned i, sign = word_shift_sign(value, op, result, count);

    if (sign) {
        if (count >= 8 && !cg.parser->no_byte_shuffles) {
            code("    xba\n    and #$00FF\n");
            count -= 8;
        }

        while (count--) {
            code("    lsr a\n");
        }

        code("    eor #$%04X\n    sec\n    sbc #$%04X\n", sign, sign);
        return 1;
    }

    if (!word_shift_plan(value, op, result, count, &p))
        return 0;

    code("; byte-shuffle word shift\n    xba\n");

    if (p.mask)
        code("    and #$%04X\n", p.mask);

    for (i = 0; i < p.steps; ++i) {
        code(p.left ? "    asl a\n" : "    lsr a\n");
    }

    return 1;
}

/* Constant divisors are selected before divmod caching as well as from the
 * loaded-operand path (compound assignments and pointer differences). Signed
 * operations retain C's truncation toward zero, including negative remainders. */
static int power_divisor(Expr *right, Type t, unsigned *bits, int *negative)
{
    uint32_t value, mask = reg_width(t) == 2 ? 65535u : UINT32_MAX;

    if (cg.parser->no_strength_reduction || t.pointers || t.base == TY_FLOAT ||
        !integer_constant(right, &value))
        return 0;

    value &= mask;

    *negative = 0;
    *bits = 0;
    if (!t.is_unsigned && (value & (reg_width(t) == 2 ? 32768u : UINT32_C(0x80000000)))) {
        *negative = 1;
        value = (0u - value) & mask;
    }

    if (!value || (value & (value - 1)))
        return 0;

    while (value > 1) {
        value >>= 1;
        ++*bits;
    }

    return 1;
}

static void native_negate(Type t)
{
    if (reg_width(t) == 2) {
        code("    eor #$FFFF\n    inc a\n");
        return;
    }

    code("    eor #$FFFF\n    clc\n    adc #$0001\n    pha\n    txa\n"
         "    eor #$FFFF\n    adc #$0000\n    tax\n    pla\n");
}

static void power_unsigned(int op, Type t, unsigned bits)
{
    uint32_t mask = bits ? (UINT32_C(1) << bits) - 1 : 0;

    unsigned i;
    t.is_unsigned = 1;

    if (op == '/') {
        if (reg_width(t) == 4)
            constant_shift32(TOK_SHR, t, bits);
        else if (!word_shift_loaded(&(Expr){0}, TOK_SHR, t, bits))

            for (i = 0; i < bits; ++i) {
                code("    lsr a\n");
            }
    } else {
        if ((mask & 65535) != 65535)
            code("    and #$%04X\n", mask & 65535);

        if (reg_width(t) == 4) {
            if (!(mask >> 16))
                code("    ldx #$0000\n");
            else if ((mask >> 16) != 65535)
                code("    pha\n    txa\n    and #$%04X\n    tax\n    pla\n", mask >> 16);
        }
    }
}

static int power_divmod_loaded(Expr *left, Expr *right, int op, Type t)
{
    unsigned bits, positive, done;
    int negative;

    if ((op != '/' && op != '%') || !power_divisor(right, t, &bits, &negative))
        return 0;

    convert_registers(value_type(left->type), t);
    code("; native power-of-two %s\n", op == '/' ? "division" : "remainder");

    if (t.is_unsigned || !bits ||
        (left->known.valid && left->known.min >= 0 &&
         (reg_width(t) != 2 || left->known.max <= 32767))) {
        power_unsigned(op, t, bits);
    } else if (reg_width(t) == 2 && op == '/' && bits == 7) {
        positive = ++cg.label;
        code("    cmp #$8000\n    bcc cg_%s_%u\n    adc #$007E\n", cg.parser->unit, positive);
        label(positive);
        positive = ++cg.label;
        code("    asl a\n    xba\n    and #$00FF\n    bcc cg_%s_%u\n    ora #$FF00\n",
             cg.parser->unit, positive);
        label(positive);
    } else if (reg_width(t) == 2 && op == '/') {
        positive = ++cg.label;
        code("    cmp #$8000\n    bcc cg_%s_%u\n    adc #$%04X\n", cg.parser->unit, positive,
             (1u << bits) - 2);
        label(positive);
        /* Sign-bit reconstruction after a logical shift avoids a repeated
         * compare/rotate chain without using facts about the pre-biased input. */
        {
            unsigned i;

            for (i = 0; i < bits; ++i) {
                code("    lsr a\n");
            }
        }
        code("    eor #$%04X\n    sec\n    sbc #$%04X\n", 1u << (15 - bits), 1u << (15 - bits));
    } else {
        positive = ++cg.label;
        done = ++cg.label;
        code(reg_width(t) == 4 ? "    cpx #$8000\n" : "    cmp #$8000\n");
        code("    bcc cg_%s_%u\n", cg.parser->unit, positive);
        native_negate(t);
        power_unsigned(op, t, bits);
        native_negate(t);
        jump(done);
        label(positive);
        power_unsigned(op, t, bits);
        label(done);
    }

    if (op == '/' && negative)
        native_negate(t);

    return 1;
}

static int power_divmod(Expr *e)
{
    Type t;

    unsigned bits;
    int negative;

    if (e->kind != EX_BINARY || (e->op != '/' && e->op != '%'))
        return 0;

    t = common_type(e->left->type, e->right->type);

    if (!power_divisor(e->right, t, &bits, &negative))
        return 0;

    emit_value(e->left);
    return power_divmod_loaded(e->left, e->right, e->op, t);
}

/* Combine (x >> k) << m (or * 2^m) with m >= k into (x << (m - k)) & mask */
static int word_shift_combine(Expr *left, int op, Type result, unsigned count, Expr **inner,
                              unsigned *shift_left, unsigned *mask_after)
{
    uint32_t right_count;
    Expr *base;

    unsigned diff, after_mask, orig_cost, new_cost, i_sign;
    WordShift ws = {0};
    int have_ws = 0;

    if (cg.parser->no_strength_reduction || (op != TOK_SHL && op != '*') || result.pointers ||
        result.base != TY_INT || !count || count >= 16)
        return 0;

    base = left;

    while (base->kind == EX_CAST && width(base->type) == 2 && width(base->left->type) == 2) {
        base = base->left;
    }

    if (base->kind != EX_BINARY || base->op != TOK_SHR || width(base->type) != 2 ||
        reg_width(base->left->type) > 2)
        return 0;
    if (!integer_constant(base->right, &right_count) || !right_count || right_count >= 16 ||
        right_count > count)
        return 0;

    diff = count - (unsigned)right_count;
    after_mask = (65535u << count) & 65535u;

    if (base->left->known.valid &&
        (base->left->known.zero & ((1u << right_count) - 1u)) == ((1u << right_count) - 1u))
        after_mask = 65535u;

    i_sign =
        word_shift_sign(base->left, TOK_SHR, promoted(base->left->type), (unsigned)right_count);
    orig_cost = 2 * (unsigned)right_count + 2 * count + (i_sign ? 10u : 0u);

    if (diff) {
        have_ws = word_shift_plan(base->left, TOK_SHL, result, diff, &ws);
        new_cost = have_ws ? (3u + (ws.mask ? 3u : 0u) + 2u * ws.steps) : 2u * diff;
    } else
        new_cost = 0;

    if (after_mask != 65535u) {
        new_cost += 3u;

        if (diff >= 8 && have_ws && ws.mask == 65280u)
            new_cost -= 3u;
    }

    if (new_cost >= orig_cost)
        return 0;
    if (right_count == 1 && count == 1 && after_mask != 65535u && !i_sign)
        return 0;

    *inner = base->left;
    *shift_left = diff;
    *mask_after = after_mask;
    return 1;
}

static void word_shift_bits(Expr *value, int op, Type result, unsigned count, unsigned mask_after)
{
    unsigned i;
    WordShift p;

    if (op == TOK_SHL && mask_after != 65535u && count >= 8 &&
        word_shift_plan(value, TOK_SHL, result, count, &p)) {
        code("; byte-shuffle combined word shift\n    xba\n");

        for (i = 0; i < p.steps; ++i) {
            code(p.left ? "    asl a\n" : "    lsr a\n");
        }

        code("    and #$%04X\n", mask_after & 65535u);
        return;
    }

    if (count && !word_shift_loaded(value, op, result, count)) {
        for (i = 0; i < count; ++i) {
            code("    asl a\n");
        }
    }

    if (mask_after != 65535u)
        code("    and #$%04X\n", mask_after & 65535u);
}

static int word_shift_combined(Expr *e)
{
    Expr *inner, *shift;

    unsigned diff, mask_after;
    uint32_t count = 0;
    Type result;

    if (e->kind != EX_BINARY || (e->op != TOK_SHL && e->op != '*') || reg_width(e->type) != 2 ||
        e->type.pointers)
        return 0;

    shift = e->left;

    if (!integer_constant(e->right, &count)) {
        if (e->op != '*' || !integer_constant(e->left, &count))
            return 0;

        shift = e->right;
    }

    if (e->op == '*') {
        uint32_t v = count;

        if (!v || (v & (v - 1)))
            return 0;

        count = 0;

        while ((1u << count) != v && count < 31) {
            ++count;
        }
    }

    result = e->op == '*' ? e->type : promoted(shift->type);

    if (!word_shift_combine(shift, e->op, result, count, &inner, &diff, &mask_after))
        return 0;

    emit_value(inner);
    convert_registers(value_type(inner->type), result);
    word_shift_bits(inner, TOK_SHL, result, diff, mask_after);

    if (e->op != '*' && !same_type(result, e->type))
        convert_registers(result, e->type);

    return 1;
}

/* Variable shifts of a promoted word need only a word result. Evaluation of
 * the count may call; preserve the value on the invocation's own stack. */
typedef struct {
    Expr *input;
    unsigned mask, stride, offset;
} ShiftIndex;

static int shift_index(Expr *e, ShiftIndex *index)
{
    uint32_t n;
    Expr *value;
    ShiftIndex p;

    if (!e || e->type.pointers || e->type.array || reg_width(e->type) != 2 ||
        e->type.base == TY_FLOAT)
        return 0;
    if (e->kind == EX_CAST && width(e->type) == 2 && width(e->left->type) == 2)
        return shift_index(e->left, index);

    if (e->kind == EX_BINARY && (e->op == '+' || e->op == '*')) {
        value = e->left;

        if (!integer_constant(e->right, &n)) {
            value = e->right;

            if (!integer_constant(e->left, &n))
                return 0;
        }
        if (n > 15 || !shift_index(value, &p))
            return 0;

        if (e->op == '+')
            p.offset += n;
        else {
            p.offset *= n;
            p.stride *= n;
        }

        if (p.offset + p.mask * p.stride >= 16) {
            return 0;
        }

        *index = p;
        return 1;
    }

    if (e->kind != EX_BINARY)
        return 0;

    value = e->left;

    if (e->op == '&') {
        if (!integer_constant(e->right, &n)) {
            value = e->right;

            if (!integer_constant(e->left, &n))
                return 0;
        }
        if (n > 15)
            return 0;
    } else if (e->op == '%' && common_type(e->left->type, e->right->type).is_unsigned) {
        if (!integer_constant(e->right, &n) || !n || n > 16 || (n & (n - 1))) {
            return 0;
        }

        --n;
    } else
        return 0;

    if (value->type.pointers || reg_width(value->type) != 2 || value->type.base == TY_FLOAT)
        return 0;

    *index = (ShiftIndex){value, n, 1, 0};
    return 1;
}

/* A bounded constant shift is a small finite map. Select a byte/word ROM table
 * from the arithmetic, independently of names, pool sizes or source spelling. */
static int bounded_shift_values(Expr *left, Expr *right, int op, ShiftIndex *index,
                                uint32_t *values)
{
    Type t = promoted(left->type);
    uint32_t value;

    unsigned i;

    if (cg.parser->no_strength_reduction || cg.parser->no_body_optimizations ||
        (op != TOK_SHL && op != TOK_SHR) || t.pointers || t.base != TY_INT ||
        !integer_constant(left, &value) || !shift_index(right, index))
        return 0;

    value &= 65535;

    for (i = 0; i <= index->mask; ++i) {
        unsigned count = index->offset + i * index->stride;
        values[i] = op == TOK_SHL   ? (value << count) & 65535
                    : t.is_unsigned ? value >> count
                                    : (uint32_t)((int32_t)(int16_t)value >> count) & 65535;
    }

    return 1;
}

static int bounded_word_shift(Expr *left, Expr *right, int op)
{
    ShiftIndex index;
    uint32_t values[16];

    unsigned i, id, bytes = 1;

    if (!bounded_shift_values(left, right, op, &index, values))
        return 0;

    for (i = 0; i <= index.mask; ++i) {
        if (values[i] > 255)
            bytes = 2;
    }

    id = ++cg.label;
    code("; bounded word shift lookup\n");
    emit_value(index.input);
    code("    and #$%04X\n", index.mask);

    if (bytes == 2)
        code("    asl a\n");

    code("    tax\n    lda f:word_shift_%s_%u,x\n", cg.parser->unit, id);

    if (bytes == 1)
        code("    and #$00FF\n");

    code(".segment \"RODATA\"\nword_shift_%s_%u:\n    .%s ", cg.parser->unit, id,
         bytes == 1 ? "byte" : "word");

    for (i = 0; i <= index.mask; ++i) {
        code("%s$%04X", i ? "," : "", values[i]);
    }

    if (bytes == 1)
        code(",0"); /* A16's last read remains inside the table */

    code("\n.segment \"%s\"\n", code_segment());
    return 1;
}

typedef struct {
    Expr *input;
    unsigned min_v, max_v, mask;
    int bounded_by_mask, has_var_shift, ok;
} LutScan;

static void lut_scan(Expr *e, LutScan *s)
{
    ShiftIndex idx;
    uint32_t n;

    if (!e || !s->ok)
        return;
    if (e->kind == EX_INT) {
        if (reg_width(e->type) > 2 || e->type.pointers || e->type.base == TY_FLOAT)
            s->ok = 0;

        return;
    }

    if (shift_index(e, &idx) && idx.stride == 1 && !idx.offset && idx.mask <= 15) {
        if (!s->input) {
            s->input = idx.input;
            s->min_v = 0;
            s->max_v = idx.mask;
            s->mask = idx.mask;
            s->bounded_by_mask = 1;
        } else if (!s->bounded_by_mask || !body_equal(s->input, idx.input) || s->mask != idx.mask)
            s->ok = 0;

        return;
    }

    if (e->kind == EX_OBJECT) {
        if (reg_width(e->type) > 2 || e->type.pointers || e->type.array ||
            e->type.base == TY_FLOAT || !e->known.valid || e->known.min < 0 || e->known.max > 15) {
            s->ok = 0;
            return;
        }

        if (!s->input) {
            s->input = e;
            s->min_v = (unsigned)e->known.min;
            s->max_v = (unsigned)e->known.max;
        } else if (s->bounded_by_mask || !body_equal(s->input, e)) {
            s->ok = 0;
            return;
        } else {
            if ((unsigned)e->known.min > s->min_v)
                s->min_v = (unsigned)e->known.min;
            if ((unsigned)e->known.max < s->max_v)
                s->max_v = (unsigned)e->known.max;
        }

        return;
    }

    if (e->kind == EX_CAST) {
        if (reg_width(e->type) > 2 || e->type.pointers || e->type.base == TY_FLOAT) {
            s->ok = 0;
            return;
        }

        lut_scan(e->left, s);
        return;
    }

    if (e->kind == EX_UNARY && (e->op == '+' || e->op == '-' || e->op == '~')) {
        if (reg_width(e->type) > 2 || e->type.pointers || e->type.base == TY_FLOAT) {
            s->ok = 0;
            return;
        }

        lut_scan(e->left, s);
        return;
    }

    if (e->kind == EX_BINARY && reg_width(e->type) <= 2 && !e->type.pointers &&
        e->type.base != TY_FLOAT &&
        (e->op == '+' || e->op == '-' || e->op == '*' || e->op == '&' || e->op == '|' ||
         e->op == '^' || e->op == TOK_SHL || e->op == TOK_SHR)) {
        if ((e->op == TOK_SHL || e->op == TOK_SHR) && !integer_constant(e->right, &n))
            s->has_var_shift = 1;

        lut_scan(e->left, s);
        lut_scan(e->right, s);
        return;
    }

    s->ok = 0;
}

static uint32_t lut_cast(uint32_t v, Type t)
{
    if (t.is_bool)
        return (v & 65535u) != 0;
    if (t.base == TY_CHAR) {
        v &= 255u;
        return (!t.is_unsigned && (v & 128u)) ? (v | 0xFF00u) : v;
    }

    return v & 65535u;
}

static uint32_t lut_eval(Expr *e, const LutScan *s, unsigned v, int *ok)
{
    ShiftIndex idx;
    uint32_t a, b, r = 0;

    if (!*ok)
        return 0;
    if (e->kind == EX_INT)
        return lut_cast(e->value, e->type);
    if (s->bounded_by_mask && shift_index(e, &idx) && idx.stride == 1 && !idx.offset)
        return lut_cast(v, e->type);
    if (e->kind == EX_OBJECT)
        return lut_cast(v, e->type);
    if (e->kind == EX_CAST)
        return lut_cast(lut_eval(e->left, s, v, ok), e->type);
    if (e->kind == EX_UNARY) {
        a = lut_eval(e->left, s, v, ok);
        r = e->op == '+' ? a : e->op == '-' ? (0u - a) : ~a;
        return lut_cast(r, e->type);
    }

    a = lut_eval(e->left, s, v, ok);
    b = lut_eval(e->right, s, v, ok);

    if (!*ok)
        return 0;

    a &= 65535u;
    b &= 65535u;

    switch (e->op) {
    case '+':
        r = a + b;
        break;
    case '-':
        r = a - b;
        break;
    case '*':
        r = a * b;
        break;
    case '&':
        r = a & b;
        break;
    case '|':
        r = a | b;
        break;
    case '^':
        r = a ^ b;
        break;
    case TOK_SHL:
        if (b >= 16u) {
            *ok = 0;
            return 0;
        }

        r = a << b;
        break;
    case TOK_SHR: {
        Type pt = promoted(e->left->type);

        if (b >= 16u) {
            *ok = 0;
            return 0;
        }

        r = pt.is_unsigned ? (a >> b) : (uint32_t)((int32_t)(int16_t)a >> b);
        break;
    }
    default:
        *ok = 0;
        return 0;
    }

    return lut_cast(r, e->type);
}

static int bounded_expression_lut(Expr *e)
{
    LutScan s = {0};
    uint32_t values[16] = {0};

    unsigned i, id, bytes = 1;

    if (cg.parser->no_strength_reduction || cg.parser->no_body_optimizations || e->type.pointers ||
        e->type.array || e->type.base != TY_INT || volatile_expression(e) || body_effect(e))
        return 0;

    s.ok = 1;
    lut_scan(e, &s);

    if (!s.ok || !s.input || !s.has_var_shift || s.min_v > s.max_v || s.max_v > 15u)
        return 0;

    for (i = s.min_v; i <= s.max_v; ++i) {
        int ok = 1;

        values[i] = lut_eval(e, &s, i, &ok) & 65535u;

        if (!ok)
            return 0;
        if (values[i] > 255u)
            bytes = 2;
    }

    /* A pure expression with the same result at every feasible index
     * needs neither the lookup index nor a table. */
    for (i = s.min_v + 1; i <= s.max_v && values[i] == values[s.min_v]; ++i) {
    }

    if (i > s.max_v) {
        code("    lda #$%04X\n", (unsigned)values[s.min_v]);
        return 1;
    }

    id = ++cg.label;
    code("; bounded expression lookup\n");
    emit_value(s.input);

    if (s.bounded_by_mask)
        code("    and #$%04X\n", s.mask);
    if (bytes == 2)
        code("    asl a\n");

    code("    tax\n    lda f:word_lut_%s_%u,x\n", cg.parser->unit, id);

    if (bytes == 1)
        code("    and #$00FF\n");

    code(".segment \"RODATA\"\nword_lut_%s_%u:\n    .%s ", cg.parser->unit, id,
         bytes == 1 ? "byte" : "word");

    for (i = 0; i <= s.max_v; ++i) {
        code("%s$%04X", i ? "," : "", values[i]);
    }

    if (bytes == 1)
        code(",0");

    code("\n.segment \"%s\"\n", code_segment());
    return 1;
}

static int variable_word_shift(Expr *left, Expr *right, int op)
{
    Type t = promoted(left->type);
    uint32_t constant, sub_c;

    unsigned loop = 0, done = 0, min_shift = 0;
    int signed_right = op == TOK_SHR && !t.is_unsigned && !unsigned_byte_value(left);
    int shared, bounded_15 = right->known.valid && right->known.min >= 0 && right->known.max <= 15;

    if (cg.parser->no_strength_reduction || (op != TOK_SHL && op != TOK_SHR) || t.pointers ||
        t.base != TY_INT || integer_constant(right, &constant))
        return 0;
    if (bounded_word_shift(left, right, op))
        return 1;

    convert_registers(value_type(left->type), t);
    shared = !cg.parser->no_body_optimizations && body_equal(left, right) && !body_effect(left);

    if (bounded_15 && right->known.min > 0 && !shared && !(op == TOK_SHR && signed_right)) {
        min_shift = (unsigned)right->known.min;

        if (min_shift >= 8 && !cg.parser->no_byte_shuffles) {
            code("    xba\n    and #$%04X\n", op == TOK_SHL ? 0xFF00u : 0x00FFu);

            for (unsigned k = 8; k < min_shift; ++k) {
                code(op == TOK_SHL ? "    asl a\n" : "    lsr a\n");
            }
        } else {
            for (unsigned k = 0; k < min_shift; ++k) {
                code(op == TOK_SHL ? "    asl a\n" : "    lsr a\n");
            }
        }
    }

    if (shared) {
        /* A already holds the count; normalize only large counts */
        loop = ++cg.label;
        done = ++cg.label;
        code("    tax\n    beq cg_%s_%u\n    cpx #$0010\n    bcc cg_%s_%u\n"
             "    pha\n    and #$000F\n    tax\n    pla\n",
             cg.parser->unit, done, cg.parser->unit, loop);
    } else if (!min_shift && right->kind == EX_OBJECT && !right->symbol->owner &&
               compare_memory_operand(right, 0) && right->symbol != cg.leaf_count) {
        /* Index loads cannot use long or stack-relative addressing. A fixed
         * near word is read once, with A retained for the common count. */
        code("    ldx ");
        compare_memory_operand(right, 1);

        if (bounded_15) {
            code("\n");
        } else if (cg.parser->no_byte_shuffles) {
            code("\n    cpx #$0010\n    bcc :+\n    pha\n    txa\n    and #$000F\n    tax\n    "
                 "pla\n:\n");
        } else {
            /* Counts 8–15 share a byte shuffle. Out-of-range counts still
             * use the same modulo-16 behavior as the ordinary word loop. */
            code("\n    cpx #$0008\n    bcc :++\n    pha\n    txa\n    and #$000F\n"
                 "    cmp #$0008\n    bcc :+\n    and #$0007\n    tax\n    pla\n    xba\n");
            code(op == TOK_SHL ? "    and #$FF00\n" : "    and #$00FF\n");

            if (signed_right)
                code("    eor #$0080\n    sec\n    sbc #$0080\n");

            code("    bra :++\n:\n    tax\n    pla\n:\n");
        }
    } else if (!min_shift && !bounded_15 && right->kind == EX_OBJECT && dp_state.homes &&
               !cg.stack_leaf && right->symbol->owner == cg.function->id && right->symbol->offset &&
               !right->type.array && width(right->type) == 2 && right->symbol != cg.leaf_count &&
               !strncmp(frame_operand(right->symbol->offset), "z:", 2)) {
        code("    ldx %s\n", frame_operand(right->symbol->offset));

        if (cg.parser->no_byte_shuffles) {
            code("    cpx #$0010\n    bcc :+\n    pha\n    txa\n    and #$000F\n    tax\n    "
                 "pla\n:\n");
        } else {
            code("    cpx #$0008\n    bcc :++\n    pha\n    txa\n    and #$000F\n"
                 "    cmp #$0008\n    bcc :+\n    and #$0007\n    tax\n    pla\n    xba\n");
            code(op == TOK_SHL ? "    and #$FF00\n" : "    and #$00FF\n");

            if (signed_right)
                code("    eor #$0080\n    sec\n    sbc #$0080\n");

            code("    bra :++\n:\n    tax\n    pla\n:\n");
        }
    } else if (!min_shift && bounded_15 && right->kind == EX_OBJECT && dp_state.homes &&
               !cg.stack_leaf && right->symbol->owner == cg.function->id && right->symbol->offset &&
               !right->type.array && width(right->type) == 2 && right->symbol != cg.leaf_count &&
               !strncmp(frame_operand(right->symbol->offset), "z:", 2)) {
        code("    ldx %s\n", frame_operand(right->symbol->offset));
    } else if (min_shift && right->kind == EX_BINARY && right->op == '-' &&
               integer_constant(right->left, &sub_c) && sub_c >= min_shift) {
        push_value(t);

        if (sub_c == min_shift) {
            emit_value(right->right);
            code("    eor #$FFFF\n    inc a\n");
        } else if (direct_operand(right->right, promoted(right->right->type), 0, 0)) {
            code("    lda #$%04X\n    sec\n    sbc ", (unsigned)(sub_c - min_shift));
            direct_operand(right->right, promoted(right->right->type), 0, 1);
            code("\n");
        } else {
            emit_value(right->right);
            cg.arithmetic = 1;
            code("    sta z:__arith_rhs\n    lda #$%04X\n    sec\n    sbc z:__arith_rhs\n",
                 (unsigned)(sub_c - min_shift));
        }

        code("    tax\n");
        pop_value(t);
    } else {
        push_value(t);
        emit_value(right);

        if (min_shift)
            code("    sec\n    sbc #$%04X\n", min_shift);
        if (!bounded_15)
            code("    and #$000F\n");

        code("    tax\n");
        pop_value(t);
    }

    if (!shared) {
        loop = ++cg.label;
        done = ++cg.label;
    }

    code("; native variable word shift\n    cpx #$0000\n    beq cg_%s_%u\n", cg.parser->unit, done);
    label(loop);

    if (op == TOK_SHL)
        code("    asl a\n");
    else
        code(signed_right ? "    cmp #$8000\n    ror a\n" : "    lsr a\n");

    code("    dex\n    bne cg_%s_%u\n", cg.parser->unit, loop);
    label(done);
    return 1;
}
