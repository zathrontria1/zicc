/* Plan the complete leaf before emitting or changing any layout. Only a private
 * signed word, one sign guard, and a write back to the same field are accepted;
 * their values remain in incoming A/X throughout. Other functions fall back. */
static int guarded_field(Expr *e, Symbol *base, unsigned *offset)
{
    Expr *root;
    int pointer;

    if (!e || e->kind != EX_MEMBER || !reduction_type(e->type, TY_INT, 0))
        return 0;

    root = member_root(e, offset, &pointer);

    if (!pointer) {
        if (root->kind != EX_DEREF)
            return 0;

        root = root->left;
    }

    return reduction_object(root, base);
}

static int guarded_return(Statement *s, uint32_t expected)
{
    Statement *one[1];

    unsigned count = 0;
    uint32_t value;

    return reduction_statements(s, one, &count, 1) && count == 1 && one[0]->kind == ST_RETURN &&
           one[0]->expression && integer_constant(one[0]->expression, &value) && value == expected;
}

static int guarded_update_leaf(Function *f)
{
    Statement *s[4];

    unsigned count = 0, offset, store_offset, i, rejected;
    Expr *init, *sum, *field, *change, *guard, *store;
    Symbol *base, *delta, *temporary;

    if (!strcmp(f->symbol->name, "main") || f->symbol->param_count != 2 || f->symbol->variadic ||
        !reduction_type(f->symbol->type, TY_INT, 0) ||
        !reduction_statements(f->body, s, &count, 4) || count != 4 || s[0]->kind != ST_EXPR ||
        s[1]->kind != ST_IF || s[1]->alternate || s[2]->kind != ST_EXPR ||
        !guarded_return(s[1]->body, 0) || !guarded_return(s[3], 1))
        return 0;

    base = leaf_parameter(f, 0);
    delta = leaf_parameter(f, 1);

    if (!base || !delta || far_pointer(base->type) || base->type.base != TY_STRUCT ||
        base->type.pointers != 1 || base->type.array || !reduction_type(delta->type, TY_INT, 0))
        return 0;

    init = s[0]->expression;

    if (init->kind != EX_ASSIGN || init->op || init->left->kind != EX_OBJECT)
        return 0;

    temporary = init->left->symbol;

    if (temporary->owner != f->id || !temporary->scope ||
        !reduction_type(temporary->type, TY_INT, 0))
        return 0;

    sum = init->right;

    while (sum->kind == EX_CAST && reduction_type(sum->type, TY_INT, 0) &&
           reduction_type(sum->left->type, TY_INT, 0)) {
        sum = sum->left;
    }

    if (sum->kind != EX_BINARY || sum->op != '+' || !reduction_type(sum->type, TY_INT, 0))
        return 0;

    field = sum->left;
    change = sum->right;

    if (!guarded_field(field, base, &offset)) {
        field = sum->right;
        change = sum->left;
    }

    if (!guarded_field(field, base, &offset) || !reduction_object(change, delta))
        return 0;

    guard = s[1]->expression;
    store = s[2]->expression;

    if (!guard || guard->kind != EX_BINARY || guard->op != '<' ||
        !reduction_object(guard->left, temporary) || !reduction_zero(guard->right) ||
        !reduction_type(guard->right->type, TY_INT, 0) || store->kind != EX_ASSIGN || store->op ||
        !guarded_field(store->left, base, &store_offset) || store_offset != offset ||
        !reduction_object(store->right, temporary) || statement_references(f->body, base) != 2 ||
        statement_references(f->body, delta) != 1 || statement_references(f->body, temporary) != 3)
        return 0;

    for (i = 0; i < cg.parser->symbol_count; ++i) {
        Symbol *v = &cg.parser->symbols[i];

        if (v->owner == f->id && v != base && v != delta && v != temporary)
            return 0;
    }

    rejected = ++cg.label;
    f->frame = 0;
    code(".segment \"CODE\"\n.export _%s\n_%s:\n; guarded word update leaf\n", f->symbol->asm_name,
         f->symbol->asm_name);
    /* ADC's full-word N is the sign of the narrowed value. V is irrelevant
     * to this guard; no compare or signed-subtraction correction is needed. */
    code("    clc\n    adc a:$%04X,x\n    bmi cg_%s_%u\n    sta a:$%04X,x\n    lda #$0001\n    "
         "rts\n",
         offset, cg.parser->unit, rejected, offset);
    label(rejected);
    code("    lda #$0000\n    rts\n__size_%s = * - _%s\n", f->symbol->asm_name,
         f->symbol->asm_name);
    return 1;
}

/* Prove that the path with two zero arguments only writes unchanged,
 * nonvolatile fields. Unknown conditions, calls, and escaping locals end
 * the proof. All other paths execute the original body. */
typedef struct {
    unsigned kind, offset;
    uint32_t bits;
} ZeroPathValue;

enum { ZERO_UNKNOWN, ZERO_INTEGER, ZERO_FIELD };

typedef struct {
    Function *function;
    Symbol *base;
    ZeroPathValue *values;
    unsigned stores;
    int returned, want_zero;
    Symbol *input;
    unsigned input_offset, mask;
} ZeroPath;

static int zero_argument_proof(Function *f);

/* A masked or shifted word can be known zero without assuming its other
 * bits are zero. Track the same fixed nonvolatile object across the body. */
static Symbol *zero_mask_source(Expr *e, unsigned *offset, unsigned *shift)
{
    Symbol *s;
    uint32_t count;

    while (e->kind == EX_CAST && known_integer(e->type) && width(e->type) == 2 &&
           width(e->left->type) == 2) {
        e = e->left;
    }

    if (e->kind == EX_BINARY && e->op == TOK_SHR && integer_constant(e->right, &count) &&
        count < 16) {
        *shift += (unsigned)count;
        return *shift < 16 ? zero_mask_source(e->left, offset, shift) : NULL;
    }
    if (width(e->type) != 2 || !known_integer(e->type) || volatile_expression(e))
        return NULL;

    s = e->kind == EX_OBJECT ? e->symbol : fixed_memory_object(e, offset);
    return s && !s->owner && !s->type.banked && !object_volatile(s->type) ? s : NULL;
}

static void zero_collect_mask(ZeroPath *path, Expr *e)
{
    unsigned i;

    if (!e)
        return;

    if (e->kind == EX_BINARY && e->op == '&') {
        uint32_t bits;

        unsigned offset = 0, shift = 0;

        if (integer_constant(e->right, &bits) && bits && bits <= 65535) {
            Symbol *s = zero_mask_source(e->left, &offset, &shift);

            if (s && bits <= (65535u >> shift)) {
                if (!path->input) {
                    path->input = s;
                    path->input_offset = offset;
                }

                if (s == path->input && offset == path->input_offset)
                    path->mask |= bits << shift;
            }
        }
    }

    zero_collect_mask(path, e->left);
    zero_collect_mask(path, e->right);
    zero_collect_mask(path, e->third);

    for (i = 0; i < e->arg_count; ++i) {
        zero_collect_mask(path, e->args[i]);
    }
}

static void zero_collect_masks(ZeroPath *path, Statement *s)
{
    for (; s; s = s->next) {
        zero_collect_mask(path, s->expression);
        zero_collect_masks(path, s->body);
        zero_collect_masks(path, s->alternate);
    }
}

static int zero_path_field(ZeroPath *path, Expr *e, unsigned *offset)
{
    Expr *root;
    int pointer;

    if (e->kind != EX_MEMBER || e->type.banked || e->type.pointers || e->type.base != TY_INT ||
        width(e->type) != 2 || volatile_expression(e))
        return 0;

    root = member_root(e, offset, &pointer);

    if (!pointer) {
        if (root->kind != EX_DEREF)
            return 0;

        root = root->left;
    }

    return root->kind == EX_OBJECT && root->symbol == path->base;
}

static ZeroPathValue zero_path_integer(uint32_t bits)
{
    ZeroPathValue value = {ZERO_INTEGER, 0, bits & 65535};

    return value;
}

static ZeroPathValue zero_path_value(ZeroPath *path, Expr *e)
{
    ZeroPathValue unknown = {0}, left, right;

    unsigned offset;
    uint32_t bits;

    if (!e)
        return unknown;
    if (integer_constant(e, &bits) && reg_width(e->type) == 2)
        return zero_path_integer(bits);

    if (path->input && e->kind == EX_BINARY && e->op == '&' && integer_constant(e->right, &bits)) {
        unsigned off = 0, shift = 0;
        Symbol *input = zero_mask_source(e->left, &off, &shift);

        if (input == path->input && off == path->input_offset &&
            (bits & ~(path->mask >> shift)) == 0)
            return zero_path_integer(0);
    }

    if (path->input && e->kind == EX_DEREF && e->left->kind == EX_BINARY && e->left->op == '+' &&
        e->left->left->kind == EX_OBJECT && e->left->left->symbol->type.array &&
        !volatile_expression(e) && known_integer(e->type) && width(e->type) <= 2) {
        Symbol *s = e->left->left->symbol;

        unsigned w = width(e->type);
        ZeroPathValue index = zero_path_value(path, e->left->right);

        if (vr_immutable(s) && s->initializer && !s->relocations && index.kind == ZERO_INTEGER &&
            w == width(pointed_type(value_type(s->type))) && index.bits < width(s->type) / w) {
            unsigned at = index.bits * w;
            bits = s->initializer[at];

            if (w == 2)
                bits |= (uint32_t)s->initializer[at + 1] << 8;

            return zero_path_integer(bits);
        }
    }

    if (e->kind == EX_OBJECT && !e->type.pointers &&
        (width(e->type) == 2 || (path->input && width(e->type) == 1)))
        return path->values[e->symbol - cg.parser->symbols];
    if (zero_path_field(path, e, &offset)) {
        ZeroPathValue field = {ZERO_FIELD, offset, 0};

        return field;
    }
    if (e->kind == EX_CAST && !e->type.pointers && e->type.base == TY_INT && width(e->type) == 2 &&
        !e->left->type.pointers &&
        (width(e->left->type) == 2 || (path->input && e->left->type.is_unsigned)))
        return zero_path_value(path, e->left);
    if (path->input && e->kind == EX_UNARY && e->op == '!') {
        left = zero_path_value(path, e->left);

        if (left.kind == ZERO_INTEGER)
            return zero_path_integer(!left.bits);
    }
    if (e->kind != EX_BINARY || e->type.pointers || e->type.base == TY_FLOAT ||
        reg_width(e->type) != 2)
        return unknown;

    left = zero_path_value(path, e->left);

    if (e->op == TOK_LAND || e->op == TOK_LOR) {
        if (left.kind != ZERO_INTEGER)
            return unknown;
        if ((e->op == TOK_LAND && !left.bits) || (e->op == TOK_LOR && left.bits))
            return zero_path_integer(!!left.bits);
    }

    right = zero_path_value(path, e->right);

    if ((e->op == '+' || e->op == '-') && right.kind == ZERO_INTEGER && !right.bits)
        return left;
    if (e->op == '+' && left.kind == ZERO_INTEGER && !left.bits)
        return right;
    if (left.kind != ZERO_INTEGER || right.kind != ZERO_INTEGER)
        return unknown;

    switch (e->op) {
    case '+':
        return zero_path_integer(left.bits + right.bits);
    case '-':
        return zero_path_integer(left.bits - right.bits);
    case TOK_EQ:
        return zero_path_integer(left.bits == right.bits);
    case TOK_NE:
        return zero_path_integer(left.bits != right.bits);
    case TOK_LAND:
    case TOK_LOR:
        return zero_path_integer(!!right.bits);
    default:
        return unknown;
    }
}

static int zero_path_statements(ZeroPath *path, Statement *s)
{
    for (; s && !path->returned; s = s->next) {
        Expr *e = s->expression;
        ZeroPathValue value;

        unsigned offset;

        switch (s->kind) {
        case ST_EMPTY:
            break;
        case ST_BLOCK:
            if (!zero_path_statements(path, s->body))
                return 0;

            break;
        case ST_IF:
            if (path->input && body_effect(e))
                return 0;

            value = zero_path_value(path, e);

            if (value.kind != ZERO_INTEGER ||
                !zero_path_statements(path, value.bits ? s->body : s->alternate))
                return 0;

            break;
        case ST_RETURN:
            if (path->want_zero) {
                if (!e || body_effect(e))
                    return 0;

                value = zero_path_value(path, e);

                if (value.kind != ZERO_INTEGER || value.bits)
                    return 0;
            } else if (e)
                return 0;

            path->returned = 1;
            break;
        case ST_EXPR:
            if (path->input && e && e->kind == EX_CALL && e->symbol && e->arg_count >= 3 &&
                e->args[0]->kind == EX_OBJECT && e->args[0]->symbol == path->base) {
                Function *callee;

                unsigned i;

                for (i = 0; i < e->arg_count; ++i) {
                    if (body_effect(e->args[i]))
                        return 0;
                }

                for (i = 1; i <= 2; ++i) {
                    value = zero_path_value(path, e->args[i]);

                    if (value.kind != ZERO_INTEGER || value.bits)
                        return 0;
                }

                for (callee = cg.parser->functions;
                     callee && strcmp(callee->symbol->asm_name, e->symbol->asm_name);
                     callee = callee->next) {
                }

                if (!callee || !callee->symbol->internal ||
                    (!callee->symbol->zero_arguments_inert && !zero_argument_proof(callee)))
                    return 0;

                continue;
            }

            if (!e || e->kind != EX_ASSIGN || e->op)
                return 0;
            if (path->input && body_effect(e->right))
                return 0;

            value = zero_path_value(path, e->right);

            if (value.kind == ZERO_UNKNOWN && !path->input)
                return 0;

            if (e->left->kind == EX_OBJECT) {
                Symbol *v = e->left->symbol;

                if (v->owner != path->function->id || !v->scope || !body_private(v) ||
                    !known_integer(v->type) || v->type.pointers ||
                    (width(v->type) != 2 && (!path->input || width(v->type) != 1)))
                    return 0;
                if (path->input && value.kind == ZERO_INTEGER)
                    value.bits = initializer_cast(value.bits, v->type) & 65535u;

                path->values[v - cg.parser->symbols] = value;
            } else {
                if (!zero_path_field(path, e->left, &offset) || value.kind != ZERO_FIELD ||
                    value.offset != offset)
                    return 0;

                ++path->stores;
            }

            break;
        default:
            return 0;
        }
    }

    return 1;
}

static int zero_argument_proof(Function *f)
{
    Symbol *s = f->symbol, *p, *a, *b;
    ZeroPath path = {0};
    int safe;

    if (cg.parser->no_body_optimizations || cg.parser->no_strength_reduction ||
        s->param_count < 3 || s->variadic || s->type.base != TY_VOID || s->type.pointers ||
        statement_inline_markers(f->body) || volatile_statements(f->body))
        return 0;

    p = leaf_parameter(f, 0);
    a = leaf_parameter(f, 1);
    b = leaf_parameter(f, 2);

    if (!p || !a || !b || !p->type.pointers || far_pointer(p->type) || a->type.pointers ||
        a->type.base != TY_INT || width(a->type) != 2 || b->type.pointers ||
        b->type.base != TY_INT || width(b->type) != 2)
        return 0;
    if (!statement_references(f->body, a) || !statement_references(f->body, b))
        return 0;

    path.function = f;
    path.base = p;
    path.values = calloc(cg.parser->symbol_count, sizeof *path.values);

    if (!path.values) {
        fputs("out of memory proving zero-argument path\n", stderr);
        exit(EXIT_FAILURE);
    }

    path.values[a - cg.parser->symbols] = path.values[b - cg.parser->symbols] =
        zero_path_integer(0);
    safe = zero_path_statements(&path, f->body) && path.stores >= 2;
    free(path.values);
    return safe;
}

static void zero_argument_entry(Function *f)
{
    unsigned resume, restore;

    if (!zero_argument_proof(f))
        return;

    f->symbol->zero_arguments_inert = 1;
    resume = ++cg.label;
    restore = ++cg.label;
    code("; zero arguments leave fields unchanged\n    cmp #0\n    bne cg_%s_%u\n"
         "    lda %u,s\n    bne cg_%s_%u\n    rts\n",
         cg.parser->unit, resume, 3 + cg.parser->long_return, cg.parser->unit, restore);
    label(restore);
    code("    lda #0\n");
    label(resume);
}

/* Keep both incoming register arguments on the nonzero path. The proof
 * only permits a zero return and calls whose zero-argument path is inert. */
static void zero_mask_entry(Function *f)
{
    ZeroPath path = {0};
    Symbol *p;

    unsigned resume;
    int safe;

    if (cg.parser->no_body_optimizations || cg.parser->no_strength_reduction ||
        f->symbol->param_count != 2 || f->symbol->variadic || !f->symbol->type.is_bool ||
        statement_inline_markers(f->body))
        return;

    p = leaf_parameter(f, 0);

    if (!p || !p->type.pointers || far_pointer(p->type) ||
        !register_parameter(1, f->symbol->params[1]))
        return;

    path.function = f;
    path.base = p;
    path.want_zero = 1;
    zero_collect_masks(&path, f->body);

    if (!path.mask)
        return;

    path.values = allocate(cg.parser->symbol_count * sizeof *path.values);
    safe = zero_path_statements(&path, f->body) && path.returned;
    free(path.values);

    if (!safe)
        return;

    resume = ++cg.label;
    code("; masked input has a zero return before frame allocation\n    pha\n    lda ");
    array_operand(path.input, path.input_offset);
    code("\n    and #$%04X\n    bne cg_%s_%u\n    pla\n    lda #0\n    rts\n", path.mask,
         cg.parser->unit, resume);
    label(resume);
    code("    pla\n");
}

/* A guarded unsigned-byte lookup followed by subtraction can return the
 * byte directly. Its successful CMP already supplies subtraction carry. */
static int guarded_byte_lookup_leaf(Function *f)
{
    Statement *s[5];
    Expr *init, *load, *check, *value, *source;
    Symbol *index, *field, *byte, *global;
    uint32_t missing, limit, minus;

    unsigned count = 0, miss, bad;

    if (cg.parser->no_strength_reduction || cg.parser->no_body_optimizations ||
        f->symbol->param_count != 1 || f->symbol->variadic ||
        !reduction_type(f->symbol->type, TY_INT, 1) ||
        !reduction_statements(f->body, s, &count, 5) || count != 5 || s[0]->kind != ST_EXPR ||
        s[1]->kind != ST_IF || s[1]->alternate || s[2]->kind != ST_EXPR || s[3]->kind != ST_IF ||
        s[3]->alternate || s[4]->kind != ST_RETURN)
        return 0;

    index = leaf_parameter(f, 0);

    if (!index || !reduction_type(index->type, TY_INT, 1))
        return 0;

    init = s[0]->expression;

    if (init->kind != EX_ASSIGN || init->op || init->left->kind != EX_OBJECT ||
        init->right->kind != EX_OBJECT)
        return 0;

    field = init->left->symbol;
    global = init->right->symbol;

    if (!body_private(field) || !field->type.pointers || far_pointer(field->type) ||
        !global->type.pointers || far_pointer(global->type) || global->owner ||
        object_volatile(global->type) || width(pointed_type(field->type)) != 1)
        return 0;

    check = s[1]->expression;

    if (check->kind == EX_UNARY && check->op == '!') {
        if (!reduction_object(check->left, field))
            return 0;
    } else if (check->kind != EX_BINARY || check->op != TOK_EQ ||
               !reduction_object(check->left, field) || !reduction_zero(check->right))
        return 0;

    load = s[2]->expression;

    if (load->kind != EX_ASSIGN || load->op || load->left->kind != EX_OBJECT)
        return 0;

    byte = load->left->symbol;
    source = load->right;

    if (!body_private(byte) || byte->type.base != TY_CHAR || !byte->type.is_unsigned ||
        byte->type.is_bool || source->kind != EX_DEREF || source->type.base != TY_CHAR ||
        !source->type.is_unsigned || source->left->kind != EX_BINARY || source->left->op != '+' ||
        source->left->left->kind != EX_OBJECT || source->left->left->symbol != field ||
        !reduction_object(source->left->right, index))
        return 0;

    check = s[3]->expression;
    value = word_bits(s[4]->expression);

    if (check->kind != EX_BINARY || check->op != '<' || !reduction_object(check->left, byte) ||
        !integer_constant(check->right, &limit) || !limit || limit > 255 ||
        value->kind != EX_BINARY || value->op != '-' || !reduction_object(value->left, byte) ||
        !integer_constant(value->right, &minus) || minus != limit)
        return 0;

    {
        Statement *arm = s[1]->body;

        if (arm && arm->kind == ST_BLOCK)
            arm = arm->body;
        if (!arm || arm->next || arm->kind != ST_RETURN ||
            !integer_constant(arm->expression, &missing) || !guarded_return(s[3]->body, missing))
            return 0;
    }
    miss = ++cg.label;
    bad = ++cg.label;
    global->used = 1;
    f->frame = 0;
    code(".segment \"CODE\"\n.export _%s\n_%s:\n; guarded byte lookup leaf\n    lda ",
         f->symbol->asm_name, f->symbol->asm_name);
    array_operand(global, 0);
    code("\n    beq cg_%s_%u\n    txa\n    clc\n    adc ", cg.parser->unit, miss);
    array_operand(global, 0);
    code("\n    tax\n    sep #$20\n.a8\n    lda a:0,x\n    cmp #$%02X\n"
         "    bcc cg_%s_%u\n    sbc #$%02X\n    rep #$20\n.a16\n    and #$00FF\n    rts\n",
         limit, cg.parser->unit, bad, limit);
    label(bad);
    code(".a8\n    rep #$20\n.a16\n");
    label(miss);
    code("    lda #$%04X\n    rts\n__size_%s = * - _%s\n", missing & 65535u, f->symbol->asm_name,
         f->symbol->asm_name);
    return 1;
}
