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
