/* Propagate dominating copies and single-use word computations from immutable,
 * unescaped private values. Keep conversions: a K&R incoming int is not a char. */
static unsigned scalar_writes_expr(Expr *e, Symbol *v)
{
    unsigned i, n = 0;

    if (!e)
        return 0;
    if ((e->kind == EX_ASSIGN || e->kind == EX_PRE || e->kind == EX_POST) &&
        e->left->kind == EX_OBJECT && e->left->symbol == v)
        ++n;

    n += scalar_writes_expr(e->left, v) + scalar_writes_expr(e->right, v) +
         scalar_writes_expr(e->third, v);

    for (i = 0; i < e->arg_count; ++i) {
        n += scalar_writes_expr(e->args[i], v);
    }

    return n;
}

static unsigned scalar_writes(Statement *s, Symbol *v)
{
    unsigned n = 0;

    for (; s; s = s->next) {
        n += scalar_writes_expr(s->expression, v) + scalar_writes_expr(s->step, v) +
             scalar_writes(s->initial, v) + scalar_writes(s->body, v) +
             scalar_writes(s->alternate, v);
    }

    return n;
}

static int scalar_copy_source(Function *f, Expr *e)
{
    if (e->type.array || structure_object(e->type) || volatile_expression(e))
        return 0;
    if (e->kind == EX_CAST)
        return scalar_copy_source(f, e->left);
    if (e->kind == EX_INT)
        return 1;

    return e->kind == EX_OBJECT && e->symbol->owner == f->id &&
           !scalar_writes(f->body, e->symbol) && !loop_escapes(f->body, e->symbol);
}

static Expr *scalar_clone(Expr *e)
{
    Expr *copy = allocate(sizeof *copy);

    *copy = *e;
    if (e->left)
        copy->left = scalar_clone(e->left);
    if (e->right)
        copy->right = scalar_clone(e->right);
    if (e->third)
        copy->third = scalar_clone(e->third);

    return copy;
}

/* Computed values are forwarded only once, into the next executable consumer.
 * This avoids duplicating work in loops or moving it across calls/stores. */
static int scalar_computed_source(Function *f, Expr *e)
{
    if (e->type.pointers || e->type.array || reg_width(e->type) != 2 ||
        (e->type.base != TY_INT && e->type.base != TY_CHAR))
        return 0;
    if (scalar_copy_source(f, e))
        return 1;
    if (e->kind == EX_CAST)
        return scalar_computed_source(f, e->left);
    if (e->kind == EX_UNARY && (e->op == '+' || e->op == '-' || e->op == '~'))
        return scalar_computed_source(f, e->left);

    return e->kind == EX_BINARY && basic_integer_op(e->op) && scalar_computed_source(f, e->left) &&
           scalar_computed_source(f, e->right);
}

static int scalar_has_call(Expr *e)
{
    unsigned i;

    if (!e)
        return 0;
    if (e->kind == EX_CALL)
        return 1;
    if (scalar_has_call(e->left) || scalar_has_call(e->right) || scalar_has_call(e->third))
        return 1;

    for (i = 0; i < e->arg_count; ++i) {
        if (scalar_has_call(e->args[i]))
            return 1;
    }

    return 0;
}

static int scalar_narrow_use(Expr *e, Symbol *v)
{
    if (!e)
        return 0;

    if (e->kind == EX_CAST && known_integer(e->type) && !e->type.is_bool) {
        Expr *source = e->left;

        while (source->kind == EX_CAST && !source->type.pointers && source->type.base == TY_LONG) {
            source = source->left;
        }

        if (source->kind == EX_OBJECT && source->symbol == v)
            return 1;
    }

    return scalar_narrow_use(e->left, v) || scalar_narrow_use(e->right, v) ||
           scalar_narrow_use(e->third, v);
}

static int scalar_next_use(Statement *s, Statement *definition, Symbol *v, int *seen,
                           int movable_load)
{
    for (; s; s = s->next) {
        int found;

        if (s == definition) {
            *seen = 1;
            continue;
        }
        if (s->kind == ST_EMPTY)
            continue;
        if (s->kind == ST_BLOCK) {
            found = scalar_next_use(s->body, definition, v, seen, movable_load);

            if (found)
                return found;

            continue;
        }

        if (*seen) {
            Expr *use = s->expression;

            if (s->kind != ST_EXPR && s->kind != ST_RETURN && s->kind != ST_IF)
                return -1;
            if (movable_load && s->kind == ST_EXPR && use && use->kind == EX_ASSIGN && !use->op &&
                use->left->kind == EX_OBJECT)
                use = use->right;

            return expression_references(use, v) == 1 &&
                           (movable_load ? (!body_effect(use) && scalar_narrow_use(use, v))
                                         : !scalar_has_call(use))
                       ? 1
                       : -1;
        }
    }

    return 0;
}

/* Forward a mutable long load only when the next use drops the high word */
static int scalar_movable_load(Expr *e)
{
    if (volatile_expression(e))
        return 0;

    while (e->kind == EX_CAST && !e->type.pointers && e->type.base == TY_LONG) {
        e = e->left;
    }

    return e->kind == EX_OBJECT && !e->type.pointers && !e->type.array && e->type.base == TY_LONG;
}

static void scalar_replace_expr(Expr **at, Symbol *v, Expr *value)
{
    Expr *e = *at;

    unsigned i;

    if (!e)
        return;
    if (e->kind == EX_OBJECT && e->symbol == v) {
        *at = scalar_clone(value);
        free(e);
        return;
    }

    scalar_replace_expr(&e->left, v, value);
    scalar_replace_expr(&e->right, v, value);
    scalar_replace_expr(&e->third, v, value);

    for (i = 0; i < e->arg_count; ++i) {
        scalar_replace_expr(&e->args[i], v, value);
    }
}

static void scalar_replace(Statement *s, Symbol *v, Expr *value)
{
    for (; s; s = s->next) {
        scalar_replace_expr(&s->expression, v, value);
        scalar_replace_expr(&s->step, v, value);
        scalar_replace(s->initial, v, value);
        scalar_replace(s->body, v, value);
        scalar_replace(s->alternate, v, value);
    }
}

/* Straight-line prefix statements that were not propagated. They run before
 * later candidates, so a candidate they reference is not replaced. */
static Statement *scalar_skipped[64];
static unsigned scalar_skipped_count;

static int scalar_skipped_reference(Symbol *v)
{
    unsigned i;

    for (i = 0; i < scalar_skipped_count; ++i) {
        if (expression_references(scalar_skipped[i]->expression, v))
            return 1;
    }

    return 0;
}

static int scalar_propagate_prefix(Function *f, Statement *s)
{
    unsigned i;

    for (; s; s = s->next) {
        Expr *e;
        Symbol *v;

        unsigned offset, bytes;
        int seen = 0, movable_load = 0;

        if (s->kind == ST_EMPTY)
            continue;
        if (s->kind == ST_BLOCK) {
            if (!scalar_propagate_prefix(f, s->body))
                return 0;

            continue;
        }
        if (s->kind != ST_EXPR || !s->expression)
            return 0;

        e = s->expression;

        if (e->kind == EX_ASSIGN && !e->op && e->left->kind == EX_OBJECT) {
            v = e->left->symbol;

            for (i = 0; i < (unsigned)(f->symbol->param_count < 0 ? 0 : f->symbol->param_count);
                 ++i) {
                if (v == leaf_parameter(f, i))
                    break;
            }

            if (i < (unsigned)(f->symbol->param_count < 0 ? 0 : f->symbol->param_count))
                v = NULL;
        } else
            v = NULL;

        if (!v || v->owner != f->id || v->type.array || structure_object(v->type) ||
            object_volatile(v->type) || loop_escapes(f->body, v) ||
            scalar_writes(f->body, v) != 1 || scalar_skipped_reference(v) ||
            !(scalar_copy_source(f, e->right) ||
              (statement_references(f->body, v) == 2 &&
               (scalar_computed_source(f, e->right) ||
                (movable_load = scalar_movable_load(e->right))) &&
               scalar_next_use(f->body, s, v, &seen, movable_load) == 1))) {
            /* An ordinary statement stays in place; the prefix continues */
            if (scalar_skipped_count == sizeof scalar_skipped / sizeof *scalar_skipped)
                return 0;

            scalar_skipped[scalar_skipped_count++] = s;
            continue;
        }

        /* The prefix dominates every replacement, including nested branches
         * and loops. Neither the copied source nor destination can alias. */
        /* Declaration initializers live in nested statement blocks. Earlier
         * prefix statements have already vanished; replace all remaining uses
         * outside this definition as well as those in its enclosing block. */
        s->expression = NULL;
        scalar_replace(f->body, v, e->right);
        offset = v->offset;
        bytes = (width(v->type) + 1) & ~1u;

        for (i = 0; i < cg.parser->symbol_count; ++i) {
            Symbol *other = &cg.parser->symbols[i];

            if (other->owner == f->id && other->offset > offset)
                other->offset -= bytes;
        }

        v->offset = 0;
        f->slots -= bytes;
        free_expression(e);
        s->expression = NULL;
        s->kind = ST_EMPTY;
    }

    return 1;
}

static Symbol *body_rom_home(Expr *e, int address, int64_t *offset);

/* Recover the target of an immutable function-pointer relocation without
 * depending on the final bank or on the linker's adapter address. */
static Symbol *scalar_function_target(Expr *e)
{
    if (e->kind == EX_ADDRESS && e->left->kind == EX_OBJECT && e->left->symbol->function)
        return e->left->symbol;
    if (e->kind == EX_OBJECT && e->symbol->function)
        return e->symbol;
    if (!function_pointer(e->type) || volatile_expression(e) || body_effect(e))
        return NULL;

    int64_t offset = 0;
    Symbol *home = body_rom_home(e, 1, &offset);

    if (!home || !home->defined || !home->type.banked || !object_constant(e->type) || offset < 0 ||
        (uint64_t)offset + width(e->type) > width(home->type))
        return NULL;

    for (Relocation *r = home->relocations; r; r = r->next) {
        if (r->offset == offset && r->size == width(e->type) && !r->addend && r->far_value &&
            r->symbol && r->symbol->function)
            return r->symbol;
    }

    return NULL;
}

static int same_fixed_address(Expr *a, Expr *b)
{
    unsigned first, second;
    Symbol *home;

    if (a->kind == EX_ADDRESS && a->left->kind == EX_OBJECT && body_equal(a, b))
        return 1;

    uint32_t left, right;
    Symbol *function = function_address_relocation(a, &left);

    if (function && function_address_relocation(b, &right) == function && left == right)
        return 1;
    if (function_pointer(value_type(a->type)) && function_pointer(value_type(b->type))) {
        Symbol *target = scalar_function_target(a);

        if (target && scalar_function_target(b) == target)
            return 1;
    }
    if (!value_type(a->type).pointers || !value_type(b->type).pointers ||
        far_pointer(value_type(a->type)) || far_pointer(value_type(b->type)) || body_effect(a) ||
        body_effect(b))
        return 0;

    home = near_object_address(a, &first);
    return home && near_object_address(b, &second) == home && first == second;
}

static Expr *bit_mask_operand(Expr *e, uint32_t *mask)
{
    if (integer_constant(e->right, mask))
        return e->left;
    if (integer_constant(e->left, mask))
        return e->right;

    return NULL;
}

static void scalar_combine_bit_masks(Expr *e)
{
    uint32_t outer, inner, sign, width_mask;
    Type t = common_type(e->left->type, e->right->type);
    Expr *nested, *value, *literal;

    if (t.pointers || (t.base != TY_INT && t.base != TY_LONG) || volatile_expression(e))
        return;

    if (e->op == '+' || e->op == '-') {
        sign = UINT32_C(1) << (width(t) * 8 - 1);
        width_mask = sign | (sign - 1);

        if ((integer_constant(e->right, &outer) && (outer & width_mask) == sign) ||
            (e->op == '+' && integer_constant(e->left, &outer) && (outer & width_mask) == sign))
            e->op = '^';
    }

    if (e->op != '&' && e->op != '|' && e->op != '^')
        return;

    nested = bit_mask_operand(e, &outer);

    if (e->op == '&' && nested && nested->kind == EX_BINARY && nested->op == TOK_SHR &&
        nested->type.is_unsigned && width(nested->type) == width(t) &&
        integer_constant(nested->right, &inner) && inner < 8 * width(t)) {
        uint32_t possible = UINT32_MAX >> (32 - 8 * width(t) + inner);

        if ((outer & possible) == possible) {
            Location location = e->location;

            free_expression(nested == e->left ? e->right : e->left);
            value = convert(nested, e->type);
            *e = *value;
            e->location = location;
            free(value);
            return;
        }
    }

    if (e->op == '&' && nested && nested->kind == EX_BINARY &&
        (nested->op == '^' || nested->op == '|') && nested->type.base == TY_LONG &&
        !nested->type.pointers && t.base == TY_LONG && outer <= 65535u) {
        Type word = type(TY_INT, 0);
        Expr *low = new_expr(EX_BINARY, e->location, word);

        word.is_unsigned = 1;
        nested->type = low->type = word;
        nested->left = convert(nested->left, word);
        nested->right = convert(nested->right, word);
        low->op = '&';
        low->left = nested;
        low->right = convert(nested == e->left ? e->right : e->left, word);
        value = convert(low, e->type);
        *e = *value;
        free(value);
        return;
    }

    if (!nested || nested->kind != EX_BINARY || nested->op != e->op ||
        width(nested->type) != width(t) || (value = bit_mask_operand(nested, &inner)) == NULL)
        return;

    literal = nested->left == value ? nested->right : nested->left;

    if (e->left == nested)
        free_expression(e->right);
    else
        free_expression(e->left);

    free_expression(literal);
    free(nested);
    e->left = value;
    e->right = new_expr(EX_INT, e->location, t);
    e->right->value = initializer_cast(e->op == '&'   ? outer & inner
                                       : e->op == '|' ? outer | inner
                                                      : outer ^ inner,
                                       t);
}

static void scalar_complement_mask(Expr *e)
{
    Expr * xor = e->left, *value;
    uint32_t mask;
    Type t = e->type;

    if (e->op != '~' || t.pointers || (t.base != TY_INT && t.base != TY_LONG) ||
        volatile_expression(e) || xor->kind != EX_BINARY || xor->op != '^' ||
        width(xor->type) != width(t) || !(value = bit_mask_operand(xor, &mask)))
        return;

    free_expression(xor->left == value ? xor->right : xor->left);
    free(xor);
    e->kind = EX_BINARY;
    e->op = '^';
    e->left = value;
    e->right = new_expr(EX_INT, e->location, t);
    e->right->value = initializer_cast(~mask, t);
}

static int scalar_literal_truth(Expr *e)
{
    if (e->kind != EX_INT || (!e->type.pointers && e->type.base == TY_DOUBLE))
        return -1;

    uint32_t bits = e->value;

    if (!e->type.pointers && e->type.base == TY_FLOAT)
        bits &= UINT32_C(0x7fffffff);

    return bits || e->value_high;
}

static int exact_binary32_wide_integer(uint32_t bits, int is_unsigned, uint64_t *result)
{
    int negative = (bits >> 31) != 0;
    uint32_t absolute = bits & UINT32_C(0x7fffffff);
    int exponent = (int)(absolute >> 23) - 127;
    uint64_t magnitude = (absolute & UINT32_C(0x7fffff)) | UINT32_C(0x800000);

    if (!absolute) {
        *result = 0;
        return 1;
    }
    if (exponent < 0 || exponent > 63 || (negative && is_unsigned))
        return 0;

    if (exponent < 23) {
        unsigned shift = (unsigned)(23 - exponent);

        if (magnitude & ((UINT64_C(1) << shift) - 1))
            return 0;

        magnitude >>= shift;
    } else
        magnitude <<= (unsigned)(exponent - 23);

    if (!is_unsigned && magnitude > (uint64_t)INT64_MAX + (unsigned)negative)
        return 0;

    *result = negative ? 0 - magnitude : magnitude;
    return 1;
}

/* Word-to-binary32 conversions are finite and exact. A signed zero is
 * interchangeable with positive zero once the result is cast to integer. */
static int binary32_zero_magnitude(Expr *e)
{
    if (wide_integer_literal(e))
        return !e->value && !e->value_high;
    if (e->type.base != TY_FLOAT || e->type.pointers)
        return 0;
    if (e->kind == EX_INT)
        return !(e->value & UINT32_C(0x7fffffff));
    if (e->kind != EX_BINARY)
        return 0;
    if (e->op == '/' && e->right->kind == EX_INT && e->right->type.base == TY_FLOAT) {
        unsigned exponent = (e->right->value >> 23) & 255;
        return exponent > 0 && exponent < 255 && binary32_zero_magnitude(e->left);
    }

    if (e->op == '*')
        for (unsigned i = 0; i < 2; ++i) {
            Expr *zero = i ? e->right : e->left, *other = i ? e->left : e->right;

            if (other->kind == EX_CAST && other->type.base == TY_FLOAT && !other->type.pointers &&
                word_integer(other->left->type) && other->left->kind == EX_OBJECT &&
                !volatile_expression(other->left) && binary32_zero_magnitude(zero))
                return 1;
        }

    return 0;
}

static Expr *scalar_string_base(Expr *e)
{
    while (e && e->kind == EX_CAST && far_pointer(e->type) && far_pointer(e->left->type)) {
        e = e->left;
    }

    return e;
}

static String *scalar_string_literal(Expr *e)
{
    e = scalar_string_base(e);
    return e && e->kind == EX_STRING ? e->string : NULL;
}

/* Resolve byte offsets in the literal's actual storage, including embedded
 * zeroes and its terminator. A one-past pointer is valid as an address. */
static String *scalar_string_address(Expr *e, unsigned *offset, int bounded)
{
    e = scalar_string_base(e);

    if (e->kind == EX_STRING) {
        *offset = 0;
        return e->string;
    }
    if (e->kind != EX_BINARY || e->op != '+' || !far_pointer(e->type))
        return NULL;

    Expr *base = e->left, *index = e->right;

    if (!far_pointer(value_type(base->type))) {
        base = e->right;
        index = e->left;
    }

    Type pointer = value_type(base->type);
    uint32_t n;

    if (!far_pointer(pointer) || width(pointed_type(pointer)) != 1 || !known_integer(index->type) ||
        !integer_constant(index, &n))
        return NULL;

    String *string = scalar_string_address(base, offset, bounded);

    if (!string || n > (bounded ? string->size : 65535u) - *offset ||
        (!bounded && !index->type.is_unsigned && n > 32767u))
        return NULL;

    *offset += (unsigned)n;
    return string;
}

static String *scalar_string_offset(Expr *e, unsigned *offset)
{
    return scalar_string_address(e, offset, 1);
}

/* A conversion to a target word keeps the relocation's low 16 bits.
 * Track word additions independently of far-pointer bank carry. */
static String *scalar_string_word(Expr *e, unsigned *offset)
{
    if (!word_integer(e->type))
        return NULL;
    if (e->kind == EX_CAST && far_pointer(value_type(e->left->type)))
        return scalar_string_offset(e->left, offset);
    if (e->kind != EX_BINARY || (e->op != '+' && e->op != '-') || e->right->kind != EX_INT ||
        !word_integer(e->right->type))
        return NULL;

    String *literal = scalar_string_word(e->left, offset);

    if (literal)
        *offset = (e->op == '+' ? *offset + e->right->value : *offset - e->right->value) & 65535u;

    return literal;
}

static Expr *scalar_string_search(Expr *e)
{
    Expr *call;
    Symbol *fn;

    if (e->kind != EX_BINARY || (e->op != TOK_EQ && e->op != TOK_NE))
        return NULL;

    if (null_pointer_operand(e->left))
        call = e->right;
    else if (null_pointer_operand(e->right))
        call = e->left;
    else
        return NULL;

    if (call->kind != EX_CALL || call->left || call->string || call->arg_count != 2 ||
        !(fn = call->symbol) || fn->defined || fn->internal || fn->old_style || fn->variadic ||
        fn->param_count != 2 || strcmp(fn->asm_name, "strchr") || fn->type.base != TY_CHAR ||
        fn->type.pointers != 1 || !far_pointer(fn->type) || fn->params[0].base != TY_CHAR ||
        fn->params[0].pointers != 1 || !far_pointer(fn->params[0]) || !word_integer(fn->params[1]))
        return NULL;

    return call;
}

static int scalar_string_contains(Expr *text, Expr *character)
{
    String *string = scalar_string_literal(text);
    uint32_t value;

    if (!string || !character || !integer_constant(character, &value))
        return -1;

    for (unsigned i = 0; i < string->size; ++i) {
        unsigned byte = string->bytes[i];

        if (byte == (unsigned char)value)
            return 1;
        if (!byte)
            break;
    }

    return 0;
}

static String *scalar_string_byte(Expr *e, Expr **index)
{
    Expr *base;

    *index = NULL;
    if (e->kind != EX_DEREF || e->type.base != TY_CHAR || e->type.pointers ||
        volatile_expression(e))
        return NULL;

    base = e->left;

    if (base->kind == EX_BINARY && base->op == '+' && far_pointer(base->type) &&
        pointed_type(value_type(base->type)).base == TY_CHAR &&
        known_integer(value_type(base->right->type)) && !body_discard_effect(base->right)) {
        *index = base->right;
        base = base->left;
    }

    return scalar_string_literal(base);
}

static int scalar_equal_string_bytes(Expr *a, Expr *b)
{
    Expr *left, *right;
    String *first = scalar_string_byte(a, &left), *second = scalar_string_byte(b, &right);

    return first && second && a->type.is_unsigned == b->type.is_unsigned &&
           body_equal(left, right) && first->size == second->size &&
           (first == second || !memcmp(first->bytes, second->bytes, first->size));
}

/* Equality to a wider literal is impossible if that literal cannot
 * round-trip through the narrower object's type under the usual conversions. */
static int scalar_unrepresentable_equality(Expr *e)
{
    if (e->op != TOK_EQ && e->op != TOK_NE)
        return 0;

    Expr *value = e->left, *literal = e->right;

    if (!wide_integer_literal(literal)) {
        value = e->right;
        literal = e->left;
    }

    if (!wide_integer_literal(literal) || !numeric(value->type) || value->type.base == TY_FLOAT ||
        value->type.base == TY_DOUBLE)
        return 0;

    Type common = common_type(value->type, literal->type);

    if (value->kind == EX_CAST &&
        same_type(unqualified_value(value->type), unqualified_value(common)) &&
        width(value->type) > width(value->left->type))
        value = value->left;
    if (value->kind != EX_OBJECT || !known_integer(value->type) || volatile_expression(value) ||
        width(common) <= width(value->type))
        return 0;

    uint64_t raw = ((uint64_t)literal->value_high << 32) | literal->value;
    uint64_t wanted = initializer_cast64(initializer_cast64(raw, literal->type), common);

    return wanted != initializer_cast64(initializer_cast64(wanted, value->type), common);
}

/* Re-fold literal operators exposed by propagation, bottom-up, with the
 * front end's semantics (casts to int/long/char, unary and binary operators). */
/* A byte projection through bitwise operators consumes only the low eight
 * product bits. Unsigned promotion keeps the full byte product defined. */
static void scalar_low_byte_products(Expr *e)
{
    if (e->kind != EX_BINARY || !word_integer(e->type))
        return;
    if (e->op == '&' || e->op == '|' || e->op == '^') {
        scalar_low_byte_products(e->left);
        scalar_low_byte_products(e->right);
        return;
    }
    if (e->op != '*' || e->left->kind != EX_OBJECT || e->right->kind != EX_OBJECT ||
        !word_integer(e->left->type) || !word_integer(e->right->type) || volatile_expression(e))
        return;

    Type byte = type(TY_CHAR, 0), word = type(TY_INT, 0);

    byte.is_unsigned = word.is_unsigned = 1;
    e->left = convert(convert(e->left, byte), word);
    e->right = convert(convert(e->right, byte), word);
    e->type = word;
}

/* An OR of comparisons to nonzero word literals already rejects zero.
 * Each leaf must read the same value; no other expression is speculated. */
static int scalar_nonzero_choices(Expr *e, Expr *tested)
{
    if (e->kind != EX_BINARY)
        return 0;
    if (e->op == TOK_LOR)
        return scalar_nonzero_choices(e->left, tested) && scalar_nonzero_choices(e->right, tested);
    if (e->op != TOK_EQ || !word_integer(common_type(e->left->type, e->right->type)))
        return 0;

    uint32_t value;
    Expr *operand = e->left;

    if (!integer_constant(e->right, &value)) {
        if (!integer_constant(e->left, &value))
            return 0;

        operand = e->right;
    }

    if (operand->kind == EX_CAST && word_integer(operand->type) && !operand->left->type.pointers &&
        operand->left->type.base == TY_CHAR)
        operand = operand->left;

    return (value & 65535u) && body_equal(operand, tested);
}

static void scalar_refold_expr(Expr *e)
{
    unsigned i;
    int taken;

    if (!e)
        return;

    scalar_refold_expr(e->left);
    scalar_refold_expr(e->right);
    scalar_refold_expr(e->third);

    for (i = 0; i < e->arg_count; ++i) {
        scalar_refold_expr(e->args[i]);
    }

    if (e->kind == EX_ADDRESS && e->left->kind == EX_MEMBER && e->type.pointers &&
        !far_pointer(e->type)) {
        int pointer;

        unsigned offset;
        Expr *base = member_root(e->left, &offset, &pointer);

        if (pointer && base->kind == EX_INT && base->type.pointers && !far_pointer(base->type)) {
            uint32_t address = (base->value + offset) & 65535u;

            free_expression(e->left);
            fold_literal(e, address);
            return;
        }
    }

    if (e->kind == EX_ASSIGN && e->op && !cg.parser->no_body_optimizations &&
        !cg.parser->no_strength_reduction && !e->type.pointers && !e->type.is_bool &&
        (e->type.base == TY_CHAR || e->type.base == TY_INT || e->type.base == TY_LONG) &&
        !volatile_expression(e)) {
        Expr binary = *e, *keep;

        binary.kind = EX_BINARY;

        if (identity_binary_operand(&binary, &keep) && keep == e->left) {
            Type result = e->type;
            Location at = e->location;

            free_expression(e->right);
            *e = *keep;
            e->type = result;
            e->location = at;
            free(keep);
            return;
        }
    }

    if (e->kind == EX_BINARY) {
        if (e->op == TOK_LAND && !cg.parser->no_body_optimizations &&
            !cg.parser->no_strength_reduction && !body_effect(e->left) &&
            !volatile_expression(e->left) && scalar_nonzero_choices(e->right, e->left)) {
            Expr *choice = e->right;

            free_expression(e->left);
            *e = *choice;
            free(choice);
            return;
        }

        if ((e->op == TOK_LAND || e->op == TOK_LOR) &&
            (taken = scalar_literal_truth(e->left)) >= 0 && taken == (e->op == TOK_LOR)) {
            free_expression(e->left);
            free_expression(e->right);
            fold_literal(e, taken);
            return;
        }

        if (!cg.parser->no_body_optimizations && !cg.parser->no_strength_reduction) {
            if (scalar_unrepresentable_equality(e)) {
                int result = e->op == TOK_NE;

                free_expression(e->left);
                free_expression(e->right);
                fold_literal(e, result);
                return;
            }

            if (e->op == TOK_EQ || e->op == TOK_NE) {
                if (word_integer(e->left->type) && word_integer(e->right->type)) {
                    unsigned left, right;
                    String *literal = scalar_string_word(e->left, &left);

                    if (literal && scalar_string_word(e->right, &right) == literal) {
                        int equal = (uint16_t)left == (uint16_t)right;

                        free_expression(e->left);
                        free_expression(e->right);
                        fold_literal(e, e->op == TOK_EQ ? equal : !equal);
                        return;
                    }
                }

                Expr *masked = e->left, *plain = e->right;

                if (plain->kind == EX_BINARY) {
                    masked = e->right;
                    plain = e->left;
                }

                if (plain->kind == EX_OBJECT && !volatile_expression(plain) &&
                    word_integer(plain->type) && masked->kind == EX_BINARY && masked->op == '&' &&
                    word_integer(masked->type)) {
                    Expr *mask = masked->right, *value = masked->left;

                    if (value->kind == EX_INT) {
                        mask = masked->left;
                        value = masked->right;
                    }

                    if (mask->kind == EX_INT && word_integer(mask->type) &&
                        body_equal(plain, value)) {
                        /* Compare the excluded bits with zero instead of reading x twice */
                        mask->value = (uint16_t)~mask->value;
                        fold_literal(plain, 0);
                    }
                }

                if (far_pointer(value_type(e->left->type)) &&
                    far_pointer(value_type(e->right->type))) {
                    unsigned left, right;
                    String *literal = scalar_string_offset(e->left, &left);

                    if (literal && scalar_string_offset(e->right, &right) == literal) {
                        int equal = left == right;

                        free_expression(e->left);
                        free_expression(e->right);
                        fold_literal(e, e->op == TOK_EQ ? equal : !equal);
                        return;
                    }
                }

                Expr *object = null_pointer_operand(e->right)  ? e->left
                               : null_pointer_operand(e->left) ? e->right
                                                               : NULL;

                if (object && object->kind == EX_ADDRESS && object->left->kind == EX_OBJECT &&
                    !object->left->symbol->function) {
                    int result = e->op == TOK_NE;

                    free_expression(e->left);
                    free_expression(e->right);
                    fold_literal(e, result);
                    return;
                }
            }

            Expr *search = scalar_string_search(e);

            if (search && (taken = scalar_string_contains(search->args[0], search->args[1])) >= 0) {
                free_expression(e->left);
                free_expression(e->right);
                fold_literal(e, taken == (e->op == TOK_NE));
                return;
            }

            if ((e->op == TOK_LAND || e->op == TOK_LOR) && wide_integer_literal(e->right) &&
                (taken = scalar_literal_truth(e->right)) == (e->op == TOK_LOR) &&
                literal_integer_tree(e->left)) {
                free_expression(e->left);
                free_expression(e->right);
                fold_literal(e, taken);
                return;
            }

            if ((basic_integer_op(e->op) || e->op == '*') && numeric(e->type) &&
                e->type.base != TY_FLOAT && e->type.base != TY_DOUBLE) {
                Expr *store = e->left, *constant = e->right;
                int left = store->kind == EX_ASSIGN;

                if (!left) {
                    store = e->right;
                    constant = e->left;
                }

                if (store->kind == EX_ASSIGN && !store->op && wide_integer_literal(store->right) &&
                    wide_integer_literal(constant) &&
                    same_type(unqualified_value(store->type),
                              unqualified_value(store->right->type))) {
                    Expr *a = left ? store->right : constant, *b = left ? constant : store->right;
                    uint64_t x =
                        initializer_cast64(((uint64_t)a->value_high << 32) | a->value, a->type);
                    uint64_t y =
                        initializer_cast64(((uint64_t)b->value_high << 32) | b->value, b->type);
                    uint64_t result;

                    if (!integer_binary_constant(e->op, common_type(a->type, b->type), x, y,
                                                 &result)) {
                        constant->type = e->type;
                        fold_literal(constant, result);
                        e->kind = EX_COMMA;
                        e->op = 0;
                        e->left = store;
                        e->right = constant;
                        return;
                    }
                }
            }

            if ((e->op == '|' || e->op == '&') && numeric(e->type)) {
                uint64_t mask = initializer_mask(8 * width(e->type)),
                         fixed = e->op == '|' ? mask : 0;

                for (unsigned side = 0; side < 2; ++side) {
                    Expr *constant = side ? e->right : e->left, *other = side ? e->left : e->right;

                    if (!wide_integer_literal(constant))
                        continue;

                    uint64_t bits = initializer_cast64(
                        ((uint64_t)constant->value_high << 32) | constant->value, constant->type);

                    if ((bits & mask) != fixed)
                        continue;

                    if (body_discard_effect(other)) {
                        constant->type = e->type;
                        fold_literal(constant, fixed);
                        e->kind = EX_COMMA;
                        e->op = 0;
                        e->left = other;
                        e->right = constant;
                    } else {
                        free_expression(other);
                        free_expression(constant);
                        fold_literal(e, fixed);
                    }

                    return;
                }
            }

            if (comparison(e->op)) {
                Expr *sequence = e->left, *constant = e->right;
                int left = sequence->kind == EX_COMMA;

                if (!left) {
                    sequence = e->right;
                    constant = e->left;
                }

                if (sequence->kind == EX_COMMA && wide_integer_literal(sequence->right) &&
                    wide_integer_literal(constant)) {
                    Expr *a = left ? sequence->right : constant,
                         *b = left ? constant : sequence->right;
                    uint64_t x =
                        initializer_cast64(((uint64_t)a->value_high << 32) | a->value, a->type);
                    uint64_t y =
                        initializer_cast64(((uint64_t)b->value_high << 32) | b->value, b->type);
                    uint64_t result;

                    if (!integer_binary_constant(e->op, common_type(a->type, b->type), x, y,
                                                 &result)) {
                        free_expression(constant);
                        sequence->right->type = e->type;
                        fold_literal(sequence->right, result);
                        sequence->type = e->type;
                        *e = *sequence;
                        free(sequence);
                        return;
                    }
                }

                if (left && wide_integer_literal(sequence->right) && !body_effect(e->right)) {
                    Expr *test = allocate(sizeof *test);

                    *test = *e;
                    test->left = sequence->right;
                    sequence->type = e->type;
                    sequence->right = test;
                    *e = *sequence;
                    free(sequence);
                    return;
                }
            }

            scalar_combine_bit_masks(e);

            if (e->kind == EX_BINARY && (e->op == '-' || e->op == '^') &&
                e->left->kind == EX_OBJECT && e->right->kind == EX_OBJECT &&
                e->left->symbol == e->right->symbol && same_type(e->left->type, e->right->type) &&
                numeric(e->type) && e->type.base != TY_FLOAT && e->type.base != TY_DOUBLE &&
                !volatile_expression(e)) {
                free_expression(e->left);
                free_expression(e->right);
                fold_literal(e, 0);
                return;
            }
        }

        if ((e->op == TOK_EQ || e->op == TOK_NE) && e->left->kind == EX_INT &&
            e->right->kind == EX_INT && (e->left->type.pointers || e->right->type.pointers) &&
            (null_pointer_operand(e->left) || null_pointer_operand(e->right))) {
            int equal = null_pointer_operand(e->left) && null_pointer_operand(e->right);

            free_expression(e->left);
            free_expression(e->right);
            fold_literal(e, e->op == TOK_EQ ? equal : !equal);
            return;
        }

        if (!cg.parser->no_body_optimizations && !cg.parser->no_strength_reduction &&
            comparison(e->op) && e->left->kind == EX_INT && e->right->kind == EX_INT &&
            e->left->type.pointers && e->right->type.pointers &&
            far_pointer(e->left->type) == far_pointer(e->right->type)) {
            Type address = type(far_pointer(e->left->type) ? TY_LONG : TY_INT, 1);
            uint64_t result;

            if (!integer_binary_constant(e->op, address, e->left->value, e->right->value,
                                         &result)) {
                free_expression(e->left);
                free_expression(e->right);
                fold_literal(e, result);
                return;
            }
        }

        if (!cg.parser->no_body_optimizations && !cg.parser->no_strength_reduction &&
            (e->op == TOK_EQ || e->op == TOK_NE) &&
            (same_fixed_address(e->left, e->right) ||
             scalar_equal_string_bytes(e->left, e->right))) {
            free_expression(e->left);
            free_expression(e->right);
            e->left = e->right = NULL;
            fold_literal(e, e->op == TOK_EQ);
            return;
        }

        if (e->op == '/' && e->type.base == TY_FLOAT && !e->type.pointers) {
            float left, right;

            if (binary32_literal(e->left, &left, 1) && binary32_literal(e->right, &right, 1) &&
                right == 0) {
                uint32_t a, b;

                memcpy(&a, &left, sizeof a);
                memcpy(&b, &right, sizeof b);
                free_expression(e->left);
                free_expression(e->right);
                /* Use the quiet NaN bit pattern 0x7fc00000 for zero divided by zero */
                uint32_t result = left == 0
                                      ? UINT32_C(0x7fc00000)
                                      : UINT32_C(0x7f800000) | ((a ^ b) & UINT32_C(0x80000000));
                fold_literal(e, result);
                return;
            }
        }

        if ((e->op == '+' || e->op == '-') && e->type.pointers && !far_pointer(e->type) &&
            e->right->kind == EX_INT) {
            if (!e->right->value && !e->left->type.array &&
                same_type(value_type(e->type), value_type(e->left->type))) {
                Expr *keep = e->left;
                Type t = e->type;
                Location loc = e->location;

                free_expression(e->right);
                *e = *keep;
                e->type = t;
                e->location = loc;
                free(keep);
                return;
            }

            if (e->left->kind == EX_BINARY && (e->left->op == '+' || e->left->op == '-') &&
                e->left->type.pointers && !far_pointer(e->left->type) &&
                e->left->right->kind == EX_INT) {
                unsigned w1 = width(pointed_type(value_type(e->type)));
                unsigned w2 = width(pointed_type(value_type(e->left->type)));

                if (w1 && w1 == w2) {
                    int64_t c1 = (e->left->op == '-') ? -(int64_t)(uint32_t)e->left->right->value
                                                      : (int64_t)(uint32_t)e->left->right->value;
                    int64_t c2 = (e->op == '-') ? -(int64_t)(uint32_t)e->right->value
                                                : (int64_t)(uint32_t)e->right->value;
                    int64_t sum = c1 + c2;
                    Expr *base = e->left->left;

                    e->left->left = NULL;
                    free_expression(e->left);
                    e->left = base;

                    if (sum == 0 && !base->type.array &&
                        same_type(value_type(e->type), value_type(base->type))) {
                        Type t = e->type;
                        Location loc = e->location;

                        free_expression(e->right);
                        *e = *base;
                        e->type = t;
                        e->location = loc;
                        free(base);
                        return;
                    }

                    if (sum >= 0) {
                        e->op = '+';
                        fold_literal(e->right, (uint64_t)sum);
                    } else {
                        e->op = '-';
                        fold_literal(e->right, (uint64_t)(-sum));
                    }

                    return;
                }
            }
        }

        fold_runtime_binary(e);
        return;
    }

    if (fold_binary32_unary(e))
        return;

    if (e->kind == EX_CAST && e->left->kind == EX_CAST && !cg.parser->no_strength_reduction &&
        !cg.parser->no_body_optimizations && e->type.is_unsigned && !e->type.is_bool &&
        numeric(e->type) && e->type.base != TY_FLOAT && e->type.base != TY_DOUBLE &&
        numeric(e->left->type) && e->left->type.base == TY_LONGLONG &&
        numeric(e->left->left->type) && e->left->left->type.base != TY_FLOAT &&
        e->left->left->type.base != TY_DOUBLE && width(e->type) <= width(e->left->left->type)) {
        /* The unsigned destination takes its low bits directly from the
         * original integer, independently of the discarded extension. */
        Expr *wide = e->left;

        e->left = wide->left;
        free(wide);
    }

    if (e->kind == EX_CAST && !cg.parser->no_body_optimizations &&
        !cg.parser->no_strength_reduction && !e->type.pointers && !e->type.array &&
        e->type.base == TY_CHAR && !e->type.is_bool && cg.function &&
        !cg.function->symbol->interrupt)
        scalar_low_byte_products(e->left);

    if (e->kind == EX_CAST && !cg.parser->no_body_optimizations &&
        !cg.parser->no_strength_reduction && numeric(e->type) && e->type.base != TY_FLOAT &&
        e->type.base != TY_DOUBLE && e->left->kind == EX_COMMA &&
        wide_integer_literal(e->left->right)) {
        Expr *sequence = e->left, *literal = sequence->right;
        uint64_t bits = initializer_cast64(((uint64_t)literal->value_high << 32) | literal->value,
                                           literal->type);
        literal->type = sequence->type = e->type;
        fold_literal(literal, initializer_cast64(bits, e->type));
        *e = *sequence;
        free(sequence);
        return;
    }

    if (e->kind == EX_UNARY && !cg.parser->no_body_optimizations &&
        !cg.parser->no_strength_reduction)
        scalar_complement_mask(e);

    if (e->kind == EX_CHOOSE && (taken = scalar_literal_truth(e->left)) >= 0) {
        Expr *chosen = taken ? e->right : e->third;

        free_expression(chosen == e->right ? e->third : e->right);
        free_expression(e->left);
        Location at = e->location;

        *e = *chosen;
        e->location = at;
        free(chosen);
        return;
    }

    if (e->kind == EX_CHOOSE && !volatile_expression(e) && !body_discard_effect(e->left) &&
        !body_effect(e->right) && !body_effect(e->third)) {
        uint32_t rv, tv;

        if (numeric(e->type) && !wide_scalar(value_type(e->type)) && e->type.base != TY_FLOAT &&
            !e->type.is_bool && integer_constant(e->right, &rv) &&
            integer_constant(e->third, &tv) &&
            initializer_cast(rv, e->type) == initializer_cast(tv, e->type)) {
            uint32_t v = initializer_cast(rv, e->type);

            free_expression(e->left);
            free_expression(e->right);
            free_expression(e->third);
            e->left = e->right = e->third = NULL;
            fold_literal(e, width(e->type) <= 2 ? v & 0xFFFFu : v);
            return;
        }

        if (body_equal(e->right, e->third) && same_type(e->right->type, e->type)) {
            Expr *keep = e->right;
            Type t = e->type;
            Location loc = e->location;

            e->right = NULL;
            free_expression(e->left);
            free_expression(e->third);
            *e = *keep;
            e->type = t;
            e->location = loc;
            free(keep);
            return;
        }
    }

    if (e->kind == EX_UNARY && e->op == '!' && e->left->kind == EX_INT && e->left->type.pointers) {
        int zero = !e->left->value;

        free_expression(e->left);
        fold_literal(e, zero);
        return;
    }

    if (e->kind == EX_CAST && e->type.base == TY_FLOAT && !e->type.pointers &&
        wide_integer_literal(e->left) && e->left->type.base == TY_LONGLONG) {
        uint64_t raw = ((uint64_t)e->left->value_high << 32) | e->left->value;
        int negative = !e->left->type.is_unsigned && (raw >> 63);
        uint64_t magnitude = negative ? 0 - raw : raw;
        uint64_t significant = magnitude;

        /* Inexact casts can observe the target rounding mode and raise flags */
        while (significant > 0xffffffu && !(significant & 1)) {
            significant >>= 1;
        }

        if (significant <= 0xffffffu) {
            float value = (float)magnitude;
            uint32_t bits;

            if (negative)
                value = -value;

            memcpy(&bits, &value, sizeof bits);
            free_expression(e->left);
            fold_literal(e, bits);
            return;
        }
    }

    if (e->kind == EX_CAST && wide_integer_literal(e->left) && numeric(e->type) &&
        e->type.base != TY_DOUBLE && (e->type.base != TY_FLOAT || literal_operand(e->left))) {
        Expr *literal = convert(e->left, e->type);
        uint64_t bits = ((uint64_t)literal->value_high << 32) | literal->value;

        free_expression(literal);
        fold_literal(e, bits);
        return;
    }

    if (e->kind == EX_CAST) {
        uint32_t bits;
        uint64_t wide;
        Expr *input = e->left;

        if (!cg.parser->no_body_optimizations && !cg.parser->no_strength_reduction &&
            !e->type.is_bool && !e->type.pointers &&
            (e->type.base == TY_INT || e->type.base == TY_CHAR) && input->kind == EX_BINARY &&
            !input->type.pointers && input->type.base == TY_LONG &&
            (input->op == '+' || input->op == '-' || input->op == '&' || input->op == '|' ||
             input->op == '^') &&
            !volatile_expression(input)) {
            Type u16 = type(TY_INT, 0);

            u16.is_unsigned = 1;
            input->left = convert(input->left, u16);
            input->right = convert(input->right, u16);
            input->type = u16;
            scalar_refold_expr(input->left);
            scalar_refold_expr(input->right);
            return;
        }

        if (e->type.is_unsigned && !e->type.is_bool && !e->type.pointers &&
            (e->type.base == TY_CHAR || e->type.base == TY_INT || e->type.base == TY_LONG) &&
            input->kind == EX_BINARY && !input->type.pointers &&
            (input->type.base == TY_INT || input->type.base == TY_LONG) &&
            width(e->type) <= width(input->type) &&
            (input->op == '+' || input->op == '-' || input->op == '*') &&
            integer_constant(input->left, &bits)) {
            uint32_t rhs;

            if (integer_constant(input->right, &rhs)) {
                uint32_t result = input->op == '+'   ? bits + rhs
                                  : input->op == '-' ? bits - rhs
                                                     : bits * rhs;
                free_expression(input);
                fold_literal(e, initializer_cast(result, e->type));
                return;
            }
        }

        if (!cg.parser->no_body_optimizations && !cg.parser->no_strength_reduction &&
            numeric(e->type) && e->type.base != TY_FLOAT && e->type.base != TY_DOUBLE &&
            binary32_zero_magnitude(e->left)) {
            free_expression(e->left);
            fold_literal(e, 0);
            return;
        }

        if (e->type.base == TY_LONGLONG && !e->type.pointers && e->left->kind == EX_INT &&
            e->left->type.base == TY_FLOAT && !e->left->type.pointers &&
            exact_binary32_wide_integer(e->left->value, e->type.is_unsigned, &wide)) {
            free_expression(e->left);
            fold_literal(e, wide);
            return;
        }

        if (binary32_integer_literal_bits(e->left, e->type, &bits)) {
            free_expression(e->left);
            fold_literal(e, bits);
            return;
        }
    }

    if (!e->left || e->left->kind != EX_INT || !literal_operand(e->left) || !numeric(e->type) ||
        e->type.base == TY_FLOAT || e->type.is_bool)
        return;

    if (e->kind == EX_UNARY && (e->op == '-' || e->op == '~' || e->op == '+' || e->op == '!')) {
        Type t = e->left->type;
        int64_t x = t.is_unsigned ? (int64_t)literal_integer(e->left, t)
                                  : (int64_t)(int32_t)literal_integer(e->left, t),
                z;

        if (e->op == '!') {
            free(e->left);
            fold_literal(e, !x);
            return;
        }
        if (!same_type(unqualified_value(promoted(t)), unqualified_value(e->type)))
            return;

        z = e->op == '-' ? -x : e->op == '~' ? ~x : x;

        if (!t.is_unsigned && ((value_width(t) == 2 && (z < -32768 || z > 32767)) ||
                               (value_width(t) == 4 && (z < INT32_MIN || z > INT32_MAX))))
            return;

        free(e->left);
        fold_literal(e, initializer_cast((uint32_t)z, e->type));
    }
}

static void scalar_refold(Statement *s)
{
    for (; s; s = s->next) {
        scalar_refold_expr(s->expression);
        scalar_refold_expr(s->step);
        scalar_refold(s->initial);
        scalar_refold(s->body);
        scalar_refold(s->alternate);
    }
}

static void scalar_propagate(Function *f)
{
    scalar_skipped_count = 0;
    scalar_propagate_prefix(f, f->body);
    scalar_refold(f->body);
}

/* General scalar leaves use the public inputs directly or invocation-owned
 * stack homes when indirect accesses need X. Ordinary expression/branch/store
 * lowering handles near pointers without a Y frame, calls, or helpers. */
static int scalar_leaf_parameter(Function *f, Symbol *v)
{
    int i;

    for (i = 0; i < f->symbol->param_count; ++i) {
        if (v == leaf_parameter(f, (unsigned)i))
            return 1;
    }

    return 0;
}

static int scalar_leaf_expression(Expr *e, Function *f)
{
    if (!e)
        return 1;
    if (far_pointer(e->type) || e->type.array || reg_width(e->type) != 2 ||
        (!e->type.pointers && e->type.base != TY_INT && e->type.base != TY_CHAR) ||
        volatile_expression(e))
        return 0;

    switch (e->kind) {
    case EX_INT:
        return 1;
    case EX_OBJECT:
        return !e->symbol->owner || scalar_leaf_parameter(f, e->symbol);
    case EX_CAST:
        return scalar_leaf_expression(e->left, f);
    case EX_UNARY:
        return (e->op == '+' || e->op == '-' || e->op == '~' || e->op == '!') &&
               scalar_leaf_expression(e->left, f);
    case EX_BINARY:
        return !e->type.pointers &&
               (basic_integer_op(e->op) || comparison(e->op) || e->op == TOK_LAND ||
                e->op == TOK_LOR) &&
               scalar_leaf_expression(e->left, f) && scalar_leaf_expression(e->right, f);
    case EX_DEREF:
        return !e->type.banked && scalar_leaf_expression(e->left, f);
    case EX_CHOOSE:
        return scalar_leaf_expression(e->left, f) && scalar_leaf_expression(e->right, f) &&
               scalar_leaf_expression(e->third, f);
    default:
        return 0;
    }
}

static int scalar_leaf_statements(Statement *s, Function *f)
{
    for (; s; s = s->next) {
        Expr *e = s->expression;

        switch (s->kind) {
        case ST_EMPTY:
            break;
        case ST_BLOCK:
            if (!scalar_leaf_statements(s->body, f))
                return 0;

            break;
        case ST_RETURN:
            if (!scalar_leaf_expression(e, f))
                return 0;

            break;
        case ST_IF:
            if (!scalar_leaf_expression(e, f) || !scalar_leaf_statements(s->body, f) ||
                !scalar_leaf_statements(s->alternate, f))
                return 0;

            break;
        case ST_EXPR:
            if (!e || e->kind != EX_ASSIGN || e->op ||
                (e->left->kind != EX_DEREF &&
                 (e->left->kind != EX_OBJECT || e->left->symbol->owner)) ||
                !scalar_leaf_expression(e->left, f) || !scalar_leaf_expression(e->right, f))
                return 0;

            break;
        default:
            return 0;
        }
    }

    return 1;
}

static int scalar_indirect_expr(Expr *e, int dynamic_only)
{
    unsigned offset;

    if (!e)
        return 0;
    if (e->kind == EX_DEREF)
        return !dynamic_only || !fixed_memory_object(e, &offset);

    return scalar_indirect_expr(e->left, dynamic_only) ||
           scalar_indirect_expr(e->right, dynamic_only) ||
           scalar_indirect_expr(e->third, dynamic_only);
}

static int scalar_indirect(Statement *s, int dynamic_only)
{
    for (; s; s = s->next) {
        if (scalar_indirect_expr(s->expression, dynamic_only) ||
            scalar_indirect(s->body, dynamic_only) || scalar_indirect(s->alternate, dynamic_only))
            return 1;
    }

    return 0;
}

/* Reuse the word expression planner for a complete pure store. All numeric
 * inputs stay in their public ABI locations; only the final pointer transfer
 * may need a temporary push. The destination is a private immutable parameter. */
static int scalar_store_leaf(Function *f)
{
    Statement *s[2];
    Expr *store, *address;
    WordPlan *plan;
    Symbol *pointer;

    unsigned n = 0, i, which = 0, offset = 3 + cg.parser->long_return, saved[8];
    int spill;
    uint32_t result;

    if (!reduction_statements(f->body, s, &n, 2) || !n || s[0]->kind != ST_EXPR)
        return 0;
    if (n == 2 && (s[1]->kind != ST_RETURN ||
                   (s[1]->expression && (!integer_constant(s[1]->expression, &result) || result))))
        return 0;

    store = s[0]->expression;

    if (store->kind != EX_ASSIGN || store->op || store->left->kind != EX_DEREF ||
        store->type.pointers || store->type.base != TY_INT || volatile_expression(store))
        return 0;

    address = store->left->left;

    if (address->kind != EX_OBJECT)
        return 0;

    pointer = address->symbol;

    if (!scalar_leaf_parameter(f, pointer) || far_pointer(pointer->type))
        return 0;

    for (i = 0; i < (unsigned)f->symbol->param_count; ++i) {
        if (leaf_parameter(f, i) == pointer) {
            which = i;
            break;
        }
    }

    plan = word_plan(store->right, f, 1);

    if (!plan)
        return 0;

    for (i = 0; i < (unsigned)f->symbol->param_count; ++i) {
        Symbol *v = leaf_parameter(f, i);

        saved[i] = v->offset;

        if (i >= 2) {
            v->offset = offset;
            offset += 2;
        }
    }

    spill = which == 1;
    cg.stack_leaf = 1;
    cg.stack_bias = 0;
    code(".segment \"CODE\"\n.export _%s\n_%s:\n; native word store leaf\n", f->symbol->asm_name,
         f->symbol->asm_name);

    if (spill) {
        code("    pha\n");
        cg.stack_bias = 2;
    }

    word_emit_plan(plan);

    if (which) {
        code("    pha\n");
        cg.stack_bias += 2;
        code("    lda %u,s\n    tax\n    pla\n", spill ? 3 : pointer->offset + cg.stack_bias);
        cg.stack_bias -= 2;
    }

    code("    sta a:$0000,x\n");

    if (spill) {
        code("    plx\n");
        cg.stack_bias -= 2;
    }

    code("    lda #0\n    rts\n__size_%s = * - _%s\n", f->symbol->asm_name, f->symbol->asm_name);
    cg.stack_leaf = 0;
    f->frame = 0;

    for (i = 0; i < (unsigned)f->symbol->param_count; ++i) {
        leaf_parameter(f, i)->offset = saved[i];
    }

    free(plan);
    return 1;
}

static int scalar_leaf(Function *f)
{
    unsigned i, saved[8];
    int falls, stack_inputs;
    Symbol *fn = f->symbol, *second = NULL;

    if (fn->interrupt || !strcmp(fn->name, "main") || fn->variadic || fn->param_count < 0 ||
        fn->param_count > 8 ||
        (fn->type.base != TY_INT && fn->type.base != TY_CHAR && fn->type.base != TY_VOID) ||
        fn->type.pointers || f->slots != (unsigned)fn->param_count * 2)
        return 0;

    for (i = 0; i < (unsigned)fn->param_count; ++i) {
        Symbol *v = leaf_parameter(f, i);

        if ((!v->type.pointers && v->type.base != TY_INT && v->type.base != TY_CHAR) ||
            far_pointer(v->type) || reg_width(v->type) != 2 || object_volatile(v->type) ||
            scalar_writes(f->body, v) || loop_escapes(f->body, v))
            return 0;
    }

    if (!scalar_leaf_statements(f->body, f))
        return 0;
    if (scalar_store_leaf(f))
        return 1;

    stack_inputs = fn->param_count > 2 || scalar_indirect(f->body, 0);
    cg.scalar_first = !stack_inputs && fn->param_count ? leaf_parameter(f, 0) : NULL;
    cg.scalar_leaf = 1;
    cg.scalar_spill = 0;
    cg.stack_leaf = 1;
    cg.stack_bias = 0;
    code(".segment \"CODE\"\n.export _%s\n_%s:\n; scalar leaf without Y frame\n", fn->asm_name,
         fn->asm_name);

    for (i = 0; i < (unsigned)fn->param_count; ++i) {
        saved[i] = leaf_parameter(f, i)->offset;
    }

    if (stack_inputs) {
        int index;

        for (index = fn->param_count > 1 ? 1 : 0; index >= 0; --index) {
            Symbol *v = leaf_parameter(f, (unsigned)index);

            if (v && statement_references(f->body, v)) {
                code("    %s\n", index ? "pha" : "phx");
                ++cg.scalar_spill;
            }
        }

        for (i = 0; i < (unsigned)fn->param_count; ++i) {
            Symbol *v = leaf_parameter(f, i);

            if (i < 2)
                v->offset = 1 + (i && statement_references(f->body, leaf_parameter(f, 0)) ? 2 : 0);
            else
                v->offset =
                    3 + cg.parser->long_return + (unsigned)cg.scalar_spill * 2 + (i - 2) * 2;
        }
    } else if (fn->param_count > 1) {
        second = leaf_parameter(f, 1);

        if (statement_references(f->body, second)) {
            code("    pha\n");
            second->offset = 1;
            cg.scalar_spill = 1;
        }
    }

    falls = emit_statements(f->body);

    if (falls) {
        code("    lda #0\n");

        for (i = 0; i < (unsigned)cg.scalar_spill; ++i) {
            code("    plx\n");
        }

        code("    rts\n");
    }

    code("__size_%s = * - _%s\n", fn->asm_name, fn->asm_name);
    cg.scalar_first = NULL;
    cg.scalar_leaf = cg.scalar_spill = cg.stack_leaf = 0;
    f->frame = 0;

    for (i = 0; i < (unsigned)fn->param_count; ++i) {
        leaf_parameter(f, i)->offset = saved[i];
    }

    return 1;
}
