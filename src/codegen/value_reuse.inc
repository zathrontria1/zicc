/* Typed dominated value reuse. Bind at the original evaluation, never hoist a
 * mutable load across a loop or speculate a read onto a new path. */
typedef struct {
    unsigned char symbols[1024], bases[1024];
    int unknown;
} VrEffects;

typedef struct {
    Expr *pattern, *first, *sites[32];
    signed char site_negate[32];
    unsigned site_count;
    Symbol *temp;
    unsigned stamp, uses;
    int negate, comparison, scale_mode;
} VrGroup;

typedef struct {
    VrGroup *group[64];
    signed char known[64];
    unsigned count;
} VrEnv;

typedef struct {
    VrGroup groups[256];
    unsigned count, temps, stamp, folds, licm, subscripts_bound, retain_stride;
    int comparisons, subscripts;
    Symbol *index, *retain_index;
} VrContext;

static int vr_integer(Type t)
{
    return !t.pointers && !t.array && !object_volatile(t) &&
           (t.base == TY_INT || t.base == TY_CHAR);
}

static int vr_scalar_object(Symbol *s)
{
    return s && vr_integer(s->type) &&
           (body_private(s) || (!s->type.banked && !object_volatile(s->type)));
}

static int vr_scalar_pure(Expr *e)
{
    if (!e || !vr_integer(e->type))
        return 0;
    if (e->kind == EX_INT)
        return 1;
    if (e->kind == EX_OBJECT)
        return vr_scalar_object(e->symbol);
    if (e->kind == EX_CAST)
        return vr_scalar_pure(e->left);
    if (e->kind == EX_UNARY && (e->op == '+' || e->op == '-' || e->op == '~'))
        return vr_scalar_pure(e->left);

    return e->kind == EX_BINARY &&
           (basic_integer_op(e->op) || e->op == '*' || e->op == TOK_SHL || e->op == TOK_SHR) &&
           vr_scalar_pure(e->left) && vr_scalar_pure(e->right);
}

static int vr_index(Expr *e)
{
    if (!e || !vr_integer(e->type))
        return 0;
    if (e->kind == EX_INT)
        return 1;
    if (e->kind == EX_OBJECT)
        return body_private(e->symbol);
    if (e->kind == EX_CAST)
        return vr_index(e->left);

    return e->kind == EX_BINARY &&
           (basic_integer_op(e->op) || e->op == '*' || e->op == TOK_SHL || e->op == TOK_SHR) &&
           vr_index(e->left) && vr_index(e->right);
}

static Symbol *vr_base(Expr *e)
{
    unsigned offset = 0;

    if (!e)
        return NULL;
    if (e->kind == EX_OBJECT && e->type.array && !e->symbol->owner)
        return e->symbol;
    if (e->kind == EX_MEMBER && e->type.array) {
        Symbol *s = fixed_memory_object(e, &offset);

        return s && !s->owner ? s : NULL;
    }
    if (e->kind == EX_BINARY && (e->op == '+' || e->op == '-') &&
        value_type(e->left->type).pointers && vr_index(e->right))
        return vr_base(e->left);

    return NULL;
}

static Symbol *vr_load(Expr *e)
{
    Symbol *s;

    if (!e || e->kind != EX_DEREF || !vr_integer(e->type) || volatile_expression(e))
        return NULL;

    s = vr_base(e->left);
    return s && !object_volatile(s->type) ? s : NULL;
}

static int vr_binary32_truncation(Expr *e)
{
    if (e->kind != EX_CAST || e->type.pointers || e->type.is_bool ||
        (e->type.base != TY_INT && e->type.base != TY_LONG))
        return 0;

    Expr *value = e->left;

    return value->kind == EX_OBJECT && value->type.base == TY_FLOAT && !value->type.pointers &&
           !value->type.array && !volatile_expression(value);
}

static int vr_immutable(Symbol *s)
{
    return s && ((s->type.banked && !s->wram) || object_constant(s->type));
}

static int vr_pure(Expr *e)
{
    if (!e || !vr_integer(e->type))
        return 0;
    if (e->kind == EX_INT)
        return 1;
    if (e->kind == EX_OBJECT)
        return vr_scalar_object(e->symbol);
    if (vr_load(e))
        return 1;
    if (e->kind == EX_CAST)
        return vr_pure(e->left);
    if (e->kind == EX_UNARY && (e->op == '+' || e->op == '-' || e->op == '~'))
        return vr_pure(e->left);

    return e->kind == EX_BINARY &&
           (basic_integer_op(e->op) || e->op == '*' || e->op == TOK_SHL || e->op == TOK_SHR) &&
           vr_pure(e->left) && vr_pure(e->right);
}

static int vr_private_far(Symbol *v)
{
    return loop_private(v) && !object_volatile(v->type) && !structure_object(v->type) &&
           !v->type.array && far_pointer(value_type(v->type));
}

static int vr_private_binary32(Symbol *v)
{
    return v->type.base == TY_FLOAT && !v->type.pointers && !object_volatile(v->type) &&
           loop_private(v);
}

static Symbol *vr_array_base(Expr *e)
{
    unsigned offset = 0;
    Symbol *s;

    if (!e)
        return NULL;

    if (e->kind == EX_OBJECT && e->type.array && !e->symbol->owner)
        s = e->symbol;
    else if (e->kind == EX_MEMBER && e->type.array) {
        s = fixed_memory_object(e, &offset);

        if (!s || s->owner)
            return NULL;
    } else
        return NULL;

    if (object_volatile(s->type) || !width(s->type) || width(s->type) > 65536)
        return NULL;

    return s;
}

static void vr_effect_expr(VrEffects *effects, Expr *e)
{
    unsigned i;

    if (!e)
        return;
    if (e->kind == EX_CALL || volatile_expression(e))
        effects->unknown = 1;

    if (e->kind == EX_ASSIGN || e->kind == EX_PRE || e->kind == EX_POST) {
        Expr *target = e->left;
        Symbol *s = NULL;

        unsigned offset = 0;

        if (target->kind == EX_OBJECT)
            effects->symbols[body_symbol(target->symbol)] = 1;
        else if (target->kind == EX_DEREF)
            s = vr_base(target->left);
        else if (target->kind == EX_MEMBER)
            s = fixed_memory_object(target, &offset);

        if (s)
            effects->bases[body_symbol(s)] = 1;
        else if (target->kind != EX_OBJECT)
            effects->unknown = 1;
    }

    vr_effect_expr(effects, e->left);
    vr_effect_expr(effects, e->right);
    vr_effect_expr(effects, e->third);

    for (i = 0; i < e->arg_count; ++i) {
        vr_effect_expr(effects, e->args[i]);
    }
}

static void vr_effect_statements(VrEffects *effects, Statement *s)
{
    for (; s; s = s->next) {
        vr_effect_expr(effects, s->expression);
        vr_effect_expr(effects, s->step);
        vr_effect_statements(effects, s->initial);
        vr_effect_statements(effects, s->body);
        vr_effect_statements(effects, s->alternate);
    }
}

static int body_entry_loop(Statement *s, BodyFacts *facts)
{
    VrEffects effects = {0};
    Statement loop = *s;

    loop.next = NULL;
    vr_effect_statements(&effects, &loop);

    if (!effects.unknown)
        body_flow_until(s, s->next, facts, NULL);

    return !effects.unknown;
}

static int body_loop_preserves_global(Statement *s, Symbol *v)
{
    VrEffects effects = {0};

    unsigned i = body_symbol(v);
    vr_effect_statements(&effects, s);
    return !effects.unknown && !effects.symbols[i] && !effects.bases[i];
}

static int vr_invalid(Expr *e, VrEffects *effects)
{
    Symbol *s;

    if (!e)
        return 0;

    if (e->kind == EX_OBJECT) {
        if (effects->symbols[body_symbol(e->symbol)])
            return 1;
        if (!body_private(e->symbol) && !vr_private_far(e->symbol) &&
            !vr_private_binary32(e->symbol) && !vr_immutable(e->symbol) &&
            (effects->unknown || effects->bases[body_symbol(e->symbol)]))
            return 1;
    }

    s = vr_load(e);

    if (s && !vr_immutable(s) && (effects->unknown || effects->bases[body_symbol(s)]))
        return 1;

    return vr_invalid(e->left, effects) || vr_invalid(e->right, effects) ||
           vr_invalid(e->third, effects);
}

static int body_invariant_stores(Statement *s, Symbol *index, VrEffects *effects)
{
    for (; s; s = s->next) {
        if (s->kind == ST_BLOCK || s->kind == ST_IF) {
            if (s->kind == ST_IF &&
                (!literal_integer_tree(s->expression) || vr_invalid(s->expression, effects)))
                return 0;
            if (!body_invariant_stores(s->body, index, effects) ||
                !body_invariant_stores(s->alternate, index, effects))
                return 0;
        } else {
            Statement item = *s;

            item.next = NULL;

            if (!body_direct_integer_stores(&item, index, 0) ||
                (item.kind == ST_EXPR && vr_invalid(item.expression->right, effects)))
                return 0;
        }
    }

    return 1;
}

/* A bounded loop can retain one set of invariant stores or just its final index */
static Statement *body_fold_counted_stores(Statement *s, BodyFacts *facts)
{
    Expr *step = s->step, *test = s->expression, *bound = NULL;
    Statement *actions = s->body;

    if (cg.parser->no_loop_unroll || cg.function->jump_label_count || body_effect(test))
        return NULL;

    if (s->kind == ST_WHILE) {
        actions = body_single(actions);

        if (!actions || actions->kind != ST_EXPR)
            return NULL;

        step = actions->expression;
        actions = actions->next;
    } else if (s->kind != ST_FOR)
        return NULL;

    if (!step || !step->left || step->left->kind != EX_OBJECT)
        return NULL;

    Symbol *index = step->left->symbol;
    Type t = index->type;

    if (!word_integer(t) || t.is_bool || !body_private(index) || !body_unit_step(step, index))
        return NULL;

    Expr *value = facts->value[body_symbol(index)];
    uint32_t bits;

    if (!value || !integer_constant(value, &bits))
        return NULL;

    int32_t start = body_index_constant(bits, t), first = start,
            maximum = t.is_unsigned ? 65535 : 32767, limit = maximum + 1;

    if (s->kind == ST_FOR && !start && test && test->kind == EX_BINARY && test->op == '<' &&
        test->left->kind == EX_OBJECT && test->left->symbol == index &&
        test->right->kind == EX_OBJECT &&
        same_type(unqualified_value(test->right->type), unqualified_value(t)))
        bound = test->right;
    else if (!body_index_interval(test, index, &first, &limit) || first != start ||
             limit <= first || limit > maximum)
        return NULL;

    if (s->kind == ST_WHILE) {
        if (!body_effect_free_counted(actions, s, index, 1))
            return NULL;

        actions = NULL;
    } else {
        VrEffects effects = {0};

        vr_effect_statements(&effects, actions);
        effects.symbols[body_symbol(index)] = 1;

        if (effects.unknown || vr_invalid(bound, &effects) ||
            !body_invariant_stores(actions, index, &effects))
            return NULL;

        s->body = NULL;
    }

    Expr *store = new_expr(EX_ASSIGN, s->location, t);

    store->left = body_object(index, s->location);
    store->right = bound ? body_clone(bound) : body_literal(t, (uint32_t)limit, s->location);
    Statement *last = body_statement(ST_EXPR, s->location), **tail = &actions;

    last->expression = store;

    while (*tail) {
        tail = &(*tail)->next;
    }

    *tail = last;
    if (bound) {
        Statement *guard = body_statement(ST_IF, s->location);

        guard->expression = body_clone(test);
        free_expression(guard->expression->left);
        guard->expression->left = body_literal(t, 0, test->location);
        guard->body = actions;
        actions = guard;
    }

    return body_install_loop_actions(s, actions);
}

static void vr_kill(VrEnv *env, VrEffects *effects)
{
    unsigned i = 0;

    while (i < env->count) {
        if (vr_invalid(env->group[i]->pattern, effects)) {
            --env->count;
            env->group[i] = env->group[env->count];
            env->known[i] = env->known[env->count];
        } else
            ++i;
    }
}

static void vr_merge(VrEnv *env, VrEnv *other)
{
    unsigned i = 0, j;

    while (i < env->count) {
        for (j = 0; j < other->count && env->group[i] != other->group[j]; ++j) {
        }

        if (j == other->count) {
            --env->count;
            env->group[i] = env->group[env->count];
            env->known[i] = env->known[env->count];
        } else {
            if (env->known[i] != other->known[j])
                env->known[i] = -1;

            ++i;
        }
    }
}

static Expr *vr_comparison(Expr *e, int *negate)
{
    Expr *pattern, *swap;

    if (!e || e->kind != EX_BINARY || !comparison(e->op) || !vr_pure(e->left) ||
        !vr_pure(e->right) || reg_width(common_type(e->left->type, e->right->type)) != 2)
        return NULL;

    pattern = body_clone(e);

    *negate = 0;
    if (pattern->op == '>' || pattern->op == TOK_LE) {
        swap = pattern->left;
        pattern->left = pattern->right;
        pattern->right = swap;
        *negate = pattern->op == TOK_LE;
        pattern->op = '<';
    } else if (pattern->op == TOK_GE) {
        *negate = 1;
        pattern->op = '<';
    } else if (pattern->op == TOK_NE) {
        *negate = 1;
        pattern->op = TOK_EQ;
    }

    return pattern;
}

static Expr *vr_value(Symbol *temp, int negate, Location at)
{
    Expr *e = body_object(temp, at);

    if (negate) {
        Expr *n = new_expr(EX_UNARY, at, type(TY_INT, 0));

        n->op = '!';
        n->left = e;
        return n;
    }

    return e;
}

static void vr_replace(Expr *e, Expr *replacement)
{
    Expr old = *e;

    *e = *replacement;
    free(replacement);
    free_expression(old.left);
    free_expression(old.right);
    free_expression(old.third);
}

static Expr *vr_scale_mul(Expr *index, unsigned stride, Location at)
{
    Type u16 = type(TY_INT, 0);
    Expr *lhs, *rhs, *mul;

    u16.is_unsigned = 1;
    lhs = convert(body_clone(index), u16);
    rhs = body_literal(u16, stride, at);
    mul = new_expr(EX_BINARY, at, u16);
    mul->op = '*';
    mul->left = lhs;
    mul->right = rhs;
    return mul;
}

static void vr_scale_wrap(Expr *e, Expr *new_index, int free_old_right)
{
    Type orig_t = value_type(e->type);
    Type char_ptr = far_pointer(orig_t) ? far_type(type(TY_CHAR, 1)) : type(TY_CHAR, 1);
    Expr *add = allocate(sizeof *add), *cast;

    *add = *e;
    add->left = convert(e->left, char_ptr);

    if (free_old_right)
        free_expression(e->right);

    add->right = new_index;
    add->type = char_ptr;
    cast = convert(add, orig_t);
    *e = *cast;
    free(cast);
}

static Symbol *vr_new_temp(VrContext *ctx, const char *prefix, Type t, Location at)
{
    char name[64];
    Symbol *v;

    unsigned bytes = (width(t) + 1) & ~1u;

    if (!bytes)
        bytes = 2;
    if (ctx->temps == 16 || cg.parser->symbol_count == 1024 || cg.function->slots + bytes > 768)
        return NULL;

    t.banked = 0;
    snprintf(name, sizeof name, "%s_%u_%u", prefix, cg.function->id, ++ctx->temps);
    v = new_symbol(cg.parser, name, t, at);
    v->owner = cg.function->id;
    v->scope = 1;
    v->active = 1;
    v->internal = 1;
    v->offset = cg.function->slots + 1;
    cg.function->slots += bytes;
    return v;
}

static int vr_bind(VrContext *ctx, VrGroup *g)
{
    Symbol *v;
    Expr *value, *assignment, *result;
    Type t = unqualified_value(g->pattern->type);

    unsigned i;
    v = vr_new_temp(ctx, "__reuse", t, g->first->location);

    if (!v)
        return 0;

    value = body_clone(g->pattern);
    assignment = new_expr(EX_ASSIGN, g->first->location, v->type);
    assignment->left = body_object(v, g->first->location);
    assignment->right = value;

    if (g->scale_mode) {
        vr_scale_wrap(g->first, assignment, 1);
        g->temp = v;
        ++ctx->subscripts_bound;

        for (i = 0; i < g->site_count; ++i) {
            vr_scale_wrap(g->sites[i], body_object(v, g->sites[i]->location), 1);
        }

        g->site_count = 0;
        return 1;
    }

    result = assignment;

    if (g->negate) {
        result = new_expr(EX_UNARY, g->first->location, type(TY_INT, 0));
        result->op = '!';
        result->left = assignment;
    }

    vr_replace(g->first, result);
    g->temp = v;

    if (ctx->subscripts)
        ++ctx->subscripts_bound;

    /* These sites were each checked in their own effect environment, with
     * the original definition dominating them before capture became profitable.
     * Rewriting them later does not move an evaluation or cross a mutation. */
    for (i = 0; i < g->site_count; ++i) {
        vr_replace(g->sites[i], vr_value(v, g->site_negate[i], g->sites[i]->location));
    }

    g->site_count = 0;
    return 1;
}

static int vr_expensive_comparison(Expr *e)
{
    Type t = common_type(e->left->type, e->right->type);

    return vr_load(e->left) || vr_load(e->right) ||
           (e->op == '<' && !t.is_unsigned && e->left->kind != EX_INT && e->right->kind != EX_INT);
}

static Expr *vr_subscript_pattern(VrContext *ctx, Expr *e, int *scale_mode)
{
    Symbol *s;

    unsigned stride;

    *scale_mode = 0;
    if (!e || e->kind != EX_BINARY || e->op != '+')
        return NULL;
    if (!e->left || !e->right || e->right->kind == EX_INT || !vr_scalar_pure(e->right))
        return NULL;
    if (!value_type(e->left->type).pointers)
        return NULL;

    stride = width(pointed_type(value_type(e->left->type)));

    if (!stride || stride > 65535 || pointed_type(value_type(e->left->type)).array)
        return NULL;

    if ((s = vr_array_base(e->left)) != NULL) {
        if (stride <= 1 || !(stride & (stride - 1)))
            return NULL;

        if (ctx->retain_index && stride == ctx->retain_stride) {
            Expr *idx = e->right;

            while (idx->kind == EX_CAST && width(idx->type) == 2 &&
                   reg_width(idx->left->type) == 2) {
                idx = idx->left;
            }

            if (idx->kind == EX_OBJECT && idx->symbol == ctx->retain_index)
                return NULL;
        }

        *scale_mode = 1;
        return vr_scale_mul(e->right, stride, e->location);
    }

    if (e->left->kind == EX_OBJECT && vr_private_far(e->left->symbol) &&
        far_pointer(value_type(e->type))) {
        return body_clone(e);
    }

    return NULL;
}

static int vr_retain_expr_ok(Expr *e, Symbol *index, unsigned *strides, unsigned *uses,
                             unsigned *count)
{
    unsigned i;

    if (!e)
        return 1;
    if (e->kind == EX_OBJECT && structure_object(e->type) && !e->symbol->owner)
        return 1;
    if (e->kind == EX_CALL || (!e->type.array && !e->type.pointers && !structure_object(e->type) &&
                               reg_width(e->type) > 2))
        return 0;

    if (e->kind == EX_BINARY && e->op == '+' && value_type(e->left->type).pointers &&
        vr_array_base(e->left)) {
        unsigned stride = width(pointed_type(value_type(e->left->type)));
        Expr *idx = e->right;

        while (idx->kind == EX_CAST && width(idx->type) == 2 && reg_width(idx->left->type) == 2) {
            idx = idx->left;
        }

        if (idx->kind == EX_OBJECT && idx->symbol == index && stride > 1 && stride <= 65535) {
            for (i = 0; i < *count && strides[i] != stride; ++i) {
            }

            if (i == *count && i < 16) {
                strides[i] = stride;
                uses[i] = 0;
                ++*count;
            }

            if (i < 16)
                ++uses[i];
        }
    }

    return vr_retain_expr_ok(e->left, index, strides, uses, count) &&
           vr_retain_expr_ok(e->right, index, strides, uses, count) &&
           vr_retain_expr_ok(e->third, index, strides, uses, count);
}

static int vr_retain_stmts_ok(Statement *s, Symbol *index, unsigned *strides, unsigned *uses,
                              unsigned *count)
{
    for (; s; s = s->next) {
        if (s->kind != ST_BLOCK && s->kind != ST_EXPR && s->kind != ST_IF && s->kind != ST_EMPTY &&
            s->kind != ST_BREAK && s->kind != ST_CONTINUE)
            return 0;
        if (!vr_retain_expr_ok(s->expression, index, strides, uses, count) ||
            !vr_retain_stmts_ok(s->body, index, strides, uses, count) ||
            !vr_retain_stmts_ok(s->alternate, index, strides, uses, count))
            return 0;
    }

    return 1;
}

static void vr_retain_loop_info(Statement *s, Symbol **index_out, unsigned *stride_out)
{
    Expr *cond = s->expression, *step = s->step;
    Symbol *index;
    uint32_t n;

    unsigned strides[16] = {0}, uses[16] = {0}, count = 0, best = 0, best_stride = 0, i;

    *index_out = NULL;
    *stride_out = 0;
    if (cg.parser->no_loop_index_retention || cg.parser->no_indexed_operands ||
        cg.parser->no_register_cursors || cg.parser->no_body_optimizations ||
        cg.function->uses_wide || cg.function->jump_label_count || s->kind != ST_FOR || !cond ||
        cond->kind != EX_BINARY || (cond->op != '<' && cond->op != TOK_LE) ||
        cond->left->kind != EX_OBJECT || !integer_constant(cond->right, &n))
        return;

    index = cond->left->symbol;

    if (!loop_private(index) || index->type.pointers || index->type.array || index->type.is_bool ||
        reg_width(index->type) != 2 || object_volatile(index->type) || !step ||
        (step->kind != EX_PRE && step->kind != EX_POST) || step->op != TOK_INC ||
        step->left->kind != EX_OBJECT || step->left->symbol != index ||
        scalar_writes(s->body, index) || volatile_statement(s))
        return;
    if (cond->op == TOK_LE)
        ++n;
    if (!n || n > (width(index->type) == 1 ? (index->type.is_unsigned ? 255u : 127u)
                                           : (index->type.is_unsigned ? 65535u : 32767u)))
        return;

    if (!index->type.is_unsigned) {
        Statement *init = s->initial;
        Expr *e;
        uint32_t start;

        while (init && init->kind == ST_BLOCK && !init->next) {
            init = init->body;
        }

        e = init && init->kind == ST_EXPR && !init->next ? init->expression : NULL;

        if (!e || e->kind != EX_ASSIGN || e->op || e->left->kind != EX_OBJECT ||
            e->left->symbol != index || !integer_constant(e->right, &start) ||
            start > (width(index->type) == 1 ? 127u : 32767u))
            return;
    }

    if (!vr_retain_stmts_ok(s->body, index, strides, uses, &count))
        return;

    for (i = 0; i < count; ++i) {
        if (strides[i] <= 65535 / n && uses[i] > best) {
            best = uses[i];
            best_stride = strides[i];
        }
    }

    if (best_stride > 1 && (best_stride & (best_stride - 1))) {
        *index_out = index;
        *stride_out = best_stride;
    }
}

static void vr_candidate(VrContext *ctx, VrEnv *env, Expr *e, VrEffects *effects)
{
    Expr *pattern = NULL;
    Symbol *base;

    unsigned i, threshold = 2;
    int negate = 0, scale_mode = 0;

    if (ctx->comparisons) {
        pattern = vr_comparison(e, &negate);

        if (!pattern)
            return;

        threshold = 2;
    } else if (ctx->subscripts) {
        pattern = vr_subscript_pattern(ctx, e, &scale_mode);

        if (!pattern)
            return;

        threshold = scale_mode ? 2 : 3;
    } else if (vr_binary32_truncation(e))
        pattern = body_clone(e);
    else {
        base = vr_load(e);

        if (!base)
            return;

        /* Near byte reads keep their existing normalization. Fixed displacements
         * are already cheap; don't add a frame home just to cache them. */
        if (!vr_immutable(base) && width(e->type) != 2)
            return;
        if (e->left->kind != EX_BINARY || e->left->right->kind == EX_INT)
            return;

        pattern = body_clone(e);
        threshold = vr_immutable(base) ? 2 : 3;

        /* A simple current induction subscript is often already retained in
         * X/Y. Require more reuse before paying for another C home. */
        if (!vr_immutable(base) && ctx->index) {
            Expr *index = e->left->right;

            while (index->kind == EX_CAST && width(index->type) == 2 &&
                   width(index->left->type) == 2) {
                index = index->left;
            }

            if (index->kind == EX_OBJECT && index->symbol == ctx->index)
                threshold = 5;
        }
    }

    if (vr_invalid(pattern, effects)) {
        free_expression(pattern);
        return;
    }

    for (i = 0; i < env->count; ++i) {
        if (env->group[i]->scale_mode == scale_mode && body_equal(env->group[i]->pattern, pattern))
            break;
    }

    if (i < env->count) {
        VrGroup *g = env->group[i];

        free_expression(pattern);

        if (env->known[i] >= 0) {
            vr_replace(
                e, body_literal(type(TY_INT, 0), (unsigned)(env->known[i] ^ negate), e->location));
            ++ctx->folds;
            return;
        }

        /* A different full expression dominates this evaluation regardless of
         * the backend's operand order. Same-expression reads are not bound. */
        if (g->stamp == ctx->stamp)
            return;
        if (!g->temp && ++g->uses >= threshold &&
            (!ctx->comparisons || vr_expensive_comparison(g->pattern)))
            vr_bind(ctx, g);

        if (g->temp) {
            if (g->scale_mode)
                vr_scale_wrap(e, body_object(g->temp, e->location), 1);
            else
                vr_replace(e, vr_value(g->temp, negate, e->location));
        } else if (g->site_count < 32) {
            g->sites[g->site_count] = e;
            g->site_negate[g->site_count++] = (signed char)negate;
        }

        return;
    }

    if (env->count == 64 || ctx->count == 256) {
        free_expression(pattern);
        return;
    }

    {
        VrGroup *g = &ctx->groups[ctx->count++];

        g->pattern = pattern;
        g->first = e;
        g->stamp = ctx->stamp;
        g->uses = 1;
        g->negate = negate;
        g->comparison = ctx->comparisons;
        g->scale_mode = scale_mode;
        env->group[env->count] = g;
        env->known[env->count++] = -1;
    }
}

static void vr_refine(VrEnv *env, Expr *test, int truth)
{
    Expr *pattern;

    unsigned i;
    int negate;

    if (test && test->kind == EX_UNARY && test->op == '!') {
        vr_refine(env, test->left, !truth);
        return;
    }

    pattern = vr_comparison(test, &negate);

    if (!pattern)
        return;

    for (i = 0; i < env->count; ++i) {
        if (body_equal(env->group[i]->pattern, pattern)) {
            env->known[i] = (signed char)(truth ^ negate);
            break;
        }
    }

    free_expression(pattern);
}

static void vr_expression(VrContext *ctx, VrEnv *env, Expr *e, VrEffects *effects, int lvalue)
{
    unsigned i;

    if (!e)
        return;

    if (e->kind == EX_CHOOSE || (e->kind == EX_BINARY && (e->op == TOK_LAND || e->op == TOK_LOR))) {
        VrEnv other;

        vr_expression(ctx, env, e->left, effects, 0);
        other = *env;

        if (ctx->subscripts)
            ++ctx->stamp;

        if (ctx->comparisons) {
            vr_refine(env, e->left, e->kind == EX_CHOOSE || e->op == TOK_LAND);
            vr_refine(&other, e->left, e->kind != EX_CHOOSE && e->op == TOK_LOR);
        }

        vr_expression(ctx, env, e->right, effects, 0);

        if (e->kind == EX_CHOOSE)
            vr_expression(ctx, &other, e->third, effects, 0);

        vr_merge(env, &other);
        return;
    }

    vr_expression(ctx, env, e->left, effects,
                  e->kind == EX_ASSIGN || e->kind == EX_PRE || e->kind == EX_POST ||
                      e->kind == EX_ADDRESS);
    vr_expression(ctx, env, e->right, effects, 0);
    vr_expression(ctx, env, e->third, effects, 0);

    for (i = 0; i < e->arg_count; ++i) {
        vr_expression(ctx, env, e->args[i], effects, 0);
    }

    if (!lvalue)
        vr_candidate(ctx, env, e, effects);
}

static void vr_full_expression(VrContext *ctx, VrEnv *env, Expr *e)
{
    VrEffects effects = {0};
    Symbol *written = NULL;

    /* A direct assignment completes its store after evaluating the RHS.
     * Other mutations within the full expression still invalidate reuse. */
    if (e && e->kind == EX_ASSIGN && e->left->kind == EX_OBJECT && !object_volatile(e->left->type))
        written = e->left->symbol;

    vr_effect_expr(&effects, written ? e->right : e);
    vr_kill(env, &effects);
    ++ctx->stamp;
    vr_expression(ctx, env, e, &effects, 0);

    if (written)
        effects.symbols[body_symbol(written)] = 1;

    vr_kill(env, &effects);
}

static int vr_statements(VrContext *ctx, VrEnv *env, Statement *s)
{
    for (; s; s = s->next) {
        if (s->kind == ST_BLOCK) {
            if (!vr_statements(ctx, env, s->body))
                return 0;
        } else if (s->kind == ST_LABEL) {
            env->count = 0;

            if (!vr_statements(ctx, env, s->body))
                return 0;
        } else if (s->kind == ST_IF) {
            VrEnv other;
            int a, b;

            vr_full_expression(ctx, env, s->expression);
            other = *env;

            if (ctx->comparisons) {
                vr_refine(env, s->expression, 1);
                vr_refine(&other, s->expression, 0);
            }

            a = vr_statements(ctx, env, s->body);
            b = vr_statements(ctx, &other, s->alternate);

            if (!a && !b) {
                env->count = 0;
                return 0;
            }

            if (!a)
                *env = other;
            else if (b)
                vr_merge(env, &other);
        } else if (s->kind == ST_FOR || s->kind == ST_WHILE || s->kind == ST_DO) {
            VrEffects effects = {0};
            VrEnv inside, step;
            Symbol *previous = ctx->index, *prev_ret = ctx->retain_index;

            unsigned prev_stride = ctx->retain_stride;
            vr_statements(ctx, env, s->initial);
            vr_effect_statements(&effects, s->body);
            vr_effect_expr(&effects, s->expression);
            vr_effect_expr(&effects, s->step);
            vr_kill(env, &effects);
            inside = *env;
            step = *env;
            ctx->index = s->expression && s->expression->kind == EX_BINARY &&
                                 s->expression->left->kind == EX_OBJECT
                             ? s->expression->left->symbol
                             : NULL;

            if (ctx->subscripts)
                vr_retain_loop_info(s, &ctx->retain_index, &ctx->retain_stride);
            if (s->kind != ST_DO)
                vr_full_expression(ctx, &inside, s->expression);

            vr_statements(ctx, &inside, s->body);
            vr_full_expression(ctx, &step, s->step);

            if (s->kind == ST_DO)
                vr_full_expression(ctx, &step, s->expression);

            vr_kill(env, &effects);
            ctx->index = previous;
            ctx->retain_index = prev_ret;
            ctx->retain_stride = prev_stride;
        } else if (s->kind == ST_SWITCH || s->kind == ST_CASE) {
            env->count = 0;
        } else if (s->kind == ST_BREAK || s->kind == ST_CONTINUE) {
            env->count = 0;
            return 0;
        } else {
            vr_full_expression(ctx, env, s->expression);

            if (s->kind == ST_RETURN) {
                env->count = 0;
                return 0;
            }
        }
    }

    return 1;
}

static int vr_has_nonstructured(Statement *s)
{
    for (; s; s = s->next) {
        if (s->kind == ST_LABEL || s->kind == ST_SWITCH || s->kind == ST_CASE)
            return 1;
        if (vr_has_nonstructured(s->initial) || vr_has_nonstructured(s->body) ||
            vr_has_nonstructured(s->alternate))
            return 1;
    }

    return 0;
}

static int vr_loop_enters(Statement *s)
{
    Statement *init;
    Expr *assign, *cond, *rhs, *lhs;
    int64_t a, b;
    Type ct;
    int op;
    uint32_t c = 0, v0 = 0, v1 = 0;

    if (s->kind == ST_DO)
        return 1;
    if (s->kind == ST_WHILE)
        return s->expression && integer_constant(s->expression, &c) && c != 0;
    if (s->kind != ST_FOR || !s->expression || body_mutating(s->expression))
        return 0;

    init = s->initial;

    while (init && init->kind == ST_BLOCK) {
        init = init->body;
    }

    while (init && init->next) {
        init = init->next;
    }

    if (!init || init->kind != ST_EXPR || !init->expression)
        return 0;

    assign = init->expression;

    if (assign->kind != EX_ASSIGN || assign->op || !assign->left ||
        assign->left->kind != EX_OBJECT || !vr_integer(assign->left->type) || !assign->right ||
        !integer_constant(assign->right, &v0))
        return 0;

    cond = s->expression;

    if (cond->kind != EX_BINARY || !comparison(cond->op) || !cond->left || !cond->right)
        return 0;

    lhs = cond->left;
    rhs = cond->right;
    op = cond->op;

    if (lhs->kind == EX_OBJECT && lhs->symbol == assign->left->symbol &&
        integer_constant(rhs, &v1)) {
    } else if (rhs->kind == EX_OBJECT && rhs->symbol == assign->left->symbol &&
               integer_constant(lhs, &v1)) {
        Expr *tmp = lhs;

        lhs = rhs;
        rhs = tmp;

        if (op == '<')
            op = '>';
        else if (op == '>')
            op = '<';
        else if (op == TOK_LE)
            op = TOK_GE;
        else if (op == TOK_GE)
            op = TOK_LE;
    } else
        return 0;

    ct = common_type(lhs->type, rhs->type);
    a = width(ct) == 1       ? (ct.is_unsigned ? (int64_t)(uint8_t)v0 : (int64_t)(int8_t)v0)
        : reg_width(ct) == 4 ? (ct.is_unsigned ? (int64_t)v0 : (int64_t)(int32_t)v0)
                             : (ct.is_unsigned ? (int64_t)(uint16_t)v0 : (int64_t)(int16_t)v0);
    b = width(ct) == 1       ? (ct.is_unsigned ? (int64_t)(uint8_t)v1 : (int64_t)(int8_t)v1)
        : reg_width(ct) == 4 ? (ct.is_unsigned ? (int64_t)v1 : (int64_t)(int32_t)v1)
                             : (ct.is_unsigned ? (int64_t)(uint16_t)v1 : (int64_t)(int16_t)v1);

    switch (op) {
    case '<':
        return a < b;
    case '>':
        return a > b;
    case TOK_LE:
        return a <= b;
    case TOK_GE:
        return a >= b;
    case TOK_EQ:
        return a == b;
    case TOK_NE:
        return a != b;
    }

    return 0;
}

static int vr_pow2(uint32_t v)
{
    return v != 0 && (v & (v - 1)) == 0;
}

static int vr_licm_profitable(Expr *e)
{
    if (!e)
        return 0;

    if (e->kind == EX_BINARY) {
        if (e->op == '*' && (!e->left || e->left->kind != EX_INT || !vr_pow2(e->left->value)) &&
            (!e->right || e->right->kind != EX_INT || !vr_pow2(e->right->value)))
            return 1;
        if ((e->op == TOK_SHL || e->op == TOK_SHR) && e->right && e->right->kind != EX_INT)
            return 1;
    }

    return vr_licm_profitable(e->left) || vr_licm_profitable(e->right);
}

static void vr_licm_append(Statement **head, Statement ***tail, Symbol *v, Expr *rhs, Location at)
{
    Statement *st = body_statement(ST_EXPR, at);
    Expr *assign = new_expr(EX_ASSIGN, at, v->type);

    assign->left = body_object(v, at);
    assign->right = rhs;
    st->expression = assign;
    **tail = st;
    *tail = &st->next;
    (void)head;
}

static void vr_licm_expr(VrContext *ctx, VrEffects *effects, Expr *e, int lvalue, Statement **head,
                         Statement ***tail)
{
    unsigned i;

    if (!e)
        return;

    if (!lvalue && e->kind == EX_BINARY && e->op == '+') {
        Symbol *s = vr_array_base(e->left);

        if (s && e->right && e->right->kind != EX_INT && vr_scalar_pure(e->right) &&
            !vr_invalid(e->right, effects)) {
            unsigned stride = width(pointed_type(value_type(e->left->type)));

            if (stride > 1 && (stride & (stride - 1)) &&
                !pointed_type(value_type(e->left->type)).array) {
                Type u16 = type(TY_INT, 0);
                Symbol *v;
                Expr *mul;

                u16.is_unsigned = 1;
                v = vr_new_temp(ctx, "__licm", u16, e->location);

                if (v) {
                    mul = vr_scale_mul(e->right, stride, e->location);
                    vr_licm_append(head, tail, v, mul, e->location);
                    vr_scale_wrap(e, body_object(v, e->location), 1);
                    ++ctx->licm;
                    return;
                }
            }
        }
    }

    if (!lvalue && vr_scalar_pure(e) && vr_licm_profitable(e) && !vr_invalid(e, effects)) {
        Type t = unqualified_value(e->type);
        Symbol *v = vr_new_temp(ctx, "__licm", t, e->location);

        if (v) {
            vr_licm_append(head, tail, v, body_clone(e), e->location);
            vr_replace(e, body_object(v, e->location));
            ++ctx->licm;
            return;
        }
    }

    if (e->kind == EX_CHOOSE || (e->kind == EX_BINARY && (e->op == TOK_LAND || e->op == TOK_LOR))) {
        vr_licm_expr(ctx, effects, e->left, 0, head, tail);
        return;
    }

    vr_licm_expr(ctx, effects, e->left,
                 e->kind == EX_ASSIGN || e->kind == EX_PRE || e->kind == EX_POST ||
                     e->kind == EX_ADDRESS,
                 head, tail);
    vr_licm_expr(ctx, effects, e->right, 0, head, tail);
    vr_licm_expr(ctx, effects, e->third, 0, head, tail);

    for (i = 0; i < e->arg_count; ++i) {
        vr_licm_expr(ctx, effects, e->args[i], 0, head, tail);
    }
}

static int vr_licm_prefix(VrContext *ctx, VrEffects *effects, Statement *s, Statement **head,
                          Statement ***tail)
{
    for (; s; s = s->next) {
        if (s->kind == ST_EMPTY)
            continue;
        if (s->kind == ST_BLOCK) {
            if (!vr_licm_prefix(ctx, effects, s->body, head, tail))
                return 0;

            continue;
        }
        if (s->kind == ST_EXPR) {
            vr_licm_expr(ctx, effects, s->expression, 0, head, tail);
            continue;
        }
        if (s->kind == ST_IF || s->kind == ST_RETURN)
            vr_licm_expr(ctx, effects, s->expression, 0, head, tail);

        return 0;
    }

    return 1;
}

static void vr_licm_statements(VrContext *ctx, Statement *s)
{
    for (; s; s = s->next) {
        vr_licm_statements(ctx, s->initial);
        vr_licm_statements(ctx, s->body);
        vr_licm_statements(ctx, s->alternate);

        if ((s->kind == ST_FOR || s->kind == ST_WHILE || s->kind == ST_DO) &&
            !vr_has_nonstructured(s->body)) {
            VrEffects effects = {0};
            Statement *head = NULL, **tail = &head;

            vr_effect_statements(&effects, s->body);
            vr_effect_expr(&effects, s->expression);
            vr_effect_expr(&effects, s->step);

            if (s->kind != ST_DO)
                vr_licm_expr(ctx, &effects, s->expression, 0, &head, &tail);
            if (vr_loop_enters(s))
                vr_licm_prefix(ctx, &effects, s->body, &head, &tail);

            if (head) {
                if (s->kind == ST_FOR && s->initial) {
                    Statement **end = &s->initial;

                    while (*end) {
                        end = &(*end)->next;
                    }

                    *end = head;
                } else {
                    Statement *loop_copy = allocate(sizeof *loop_copy);
                    Statement *block = body_statement(ST_BLOCK, s->location);

                    *loop_copy = *s;
                    loop_copy->next = NULL;
                    *tail = loop_copy;
                    block->body = head;
                    block->next = s->next;
                    *s = *block;
                    free(block);
                }
            }
        }
    }
}

static void value_reuse_prepare(Function *f)
{
    VrContext *ctx;
    VrEnv env = {0};

    unsigned i, loads, subs;

    if (cg.parser->no_value_reuse || cg.parser->no_body_optimizations ||
        cg.parser->no_strength_reduction || f->symbol->interrupt || statement_has_case(f->body))
        return;

    ctx = allocate(sizeof *ctx);
    vr_licm_statements(ctx, f->body);
    ctx->subscripts = 1;
    vr_statements(ctx, &env, f->body);
    subs = ctx->subscripts_bound;

    for (i = 0; i < ctx->count; ++i) {
        free_expression(ctx->groups[i].pattern);
    }

    memset(ctx->groups, 0, sizeof ctx->groups);
    ctx->count = 0;
    ctx->subscripts = 0;
    env.count = 0;
    vr_statements(ctx, &env, f->body);
    loads = ctx->temps - ctx->licm - subs;

    for (i = 0; i < ctx->count; ++i) {
        free_expression(ctx->groups[i].pattern);
    }

    memset(ctx->groups, 0, sizeof ctx->groups);
    ctx->count = 0;
    ctx->comparisons = 1;
    env.count = 0;
    vr_statements(ctx, &env, f->body);

    for (i = 0; i < ctx->count; ++i) {
        free_expression(ctx->groups[i].pattern);
    }

    if (ctx->temps || ctx->folds)
        code("; typed value reuse: %u memory, %u predicates, %u proven comparisons, %u licm, %u "
             "subscripts\n",
             loads, ctx->temps - ctx->licm - subs - loads, ctx->folds, ctx->licm, subs);

    free(ctx);
}
