/* Adjacent counted loops may share a traversal only when their memory effects
 * commute across iterations. Actual array objects supply disjoint identities;
 * precise subranges allow independent fields/regions of one object as well.
 * Calls, escapes, volatile accesses and uncertain aliases reject fusion. */
typedef struct {
    Statement *loop;
    Symbol *index;
    Expr *first, *bound;
} FusionLoop;

typedef struct {
    Symbol *object;
    int64_t low, high;
    int write;
} FusionAccess;

typedef struct {
    FusionAccess access[128];
    unsigned count;
    int failed;
    Symbol *index;
    unsigned high;
} FusionEffects;

static Statement *fusion_single(Statement *s)
{
    while (s && s->kind == ST_BLOCK && !s->next && !s->inline_callee) {
        s = s->body;
    }

    while (s && s->kind == ST_EMPTY) {
        s = s->next;
    }

    return s;
}

static int fusion_shape(Statement *loop, FusionLoop *shape)
{
    Statement *initial;
    Expr *e, *step;
    uint32_t n;

    if (!loop || loop->kind != ST_FOR || !loop->expression || loop->expression->kind != EX_BINARY ||
        (loop->expression->op != '<' && loop->expression->op != TOK_NE) ||
        loop->expression->left->kind != EX_OBJECT)
        return 0;

    shape->loop = loop;
    shape->index = loop->expression->left->symbol;
    shape->bound = loop->expression->right;

    if (!shape->index->owner || shape->index->type.base != TY_INT || shape->index->type.pointers ||
        !shape->index->type.is_unsigned || width(shape->index->type) != 2 ||
        object_volatile(shape->index->type) ||
        reg_width(common_type(loop->expression->left->type, shape->bound->type)) != 2 ||
        !common_type(loop->expression->left->type, shape->bound->type).is_unsigned)
        return 0;

    initial = fusion_single(loop->initial);
    step = loop->step;
    e = initial && initial->kind == ST_EXPR && !initial->next ? initial->expression : NULL;

    if (!e || e->kind != EX_ASSIGN || e->op || e->left->kind != EX_OBJECT ||
        e->left->symbol != shape->index || !step || step->left->kind != EX_OBJECT ||
        step->left->symbol != shape->index ||
        !(((step->kind == EX_PRE || step->kind == EX_POST) && step->op == TOK_INC) ||
          (step->kind == EX_ASSIGN && step->op == '+' && integer_constant(step->right, &n) &&
           n == 1)))
        return 0;

    shape->first = e->right;
    return !body_effect(shape->first) && !body_effect(shape->bound) &&
           !loop_mentions(shape->first, shape->index) && !loop_mentions(shape->bound, shape->index);
}

static void fusion_domain_expr(Expr *e, Symbol *index, unsigned *high, int unconditional)
{
    IndexedOperand operand;

    unsigned n;
    Expr *at;

    if (!e)
        return;

    if (unconditional && indexed_operand(e, &operand)) {
        at = operand.index;

        while (at->kind == EX_CAST && same_value_representation(at->type, at->left->type)) {
            at = at->left;
        }

        if (at->kind == EX_OBJECT && at->symbol == index && operand.scale &&
            width(operand.base->type) > operand.offset) {
            n = (width(operand.base->type) - operand.offset - width(e->type)) / operand.scale;

            if (n < *high)
                *high = n;
        }
    }

    fusion_domain_expr(e->left, index, high, unconditional);
    fusion_domain_expr(e->right, index, high,
                       unconditional && e->kind != EX_CHOOSE &&
                           !(e->kind == EX_BINARY && (e->op == TOK_LAND || e->op == TOK_LOR)));
    fusion_domain_expr(e->third, index, high, 0);
}

static void fusion_domain(Statement *s, Symbol *index, unsigned *high, int unconditional)
{
    for (; s; s = s->next) {
        fusion_domain_expr(s->expression, index, high, unconditional);

        if (s->kind == ST_BLOCK)
            fusion_domain(s->body, index, high, unconditional);
        else {
            fusion_domain(s->body, index, high, 0);
            fusion_domain(s->alternate, index, high, 0);
        }
    }
}

static int fusion_range(Expr *e, Symbol *index, unsigned high, int64_t *low, int64_t *upper)
{
    uint32_t n;
    int64_t a, b, c, d;
    Type t = value_type(e->type);

    if (t.pointers || t.array || t.base == TY_FLOAT || reg_width(t) != 2)
        return 0;
    if (integer_constant(e, &n)) {
        *low = *upper = t.is_unsigned ? (int64_t)(n & 65535) : (int64_t)(int16_t)n;
        return 1;
    }
    if (e->kind == EX_OBJECT && e->symbol == index) {
        *low = 0;
        *upper = high;
        return 1;
    }

    if (e->kind == EX_CAST) {
        if (!fusion_range(e->left, index, high, &a, &b))
            return 0;
        if (a < (t.is_unsigned ? 0 : -32768) || b > (t.is_unsigned ? 65535 : 32767))
            return 0;

        *low = a;
        *upper = b;
        return 1;
    }

    if (e->kind != EX_BINARY)
        return 0;
    if (e->op == '&' && integer_constant(e->right, &n) && n <= 65535) {
        *low = 0;
        *upper = n;
        return 1;
    }
    if (!fusion_range(e->left, index, high, &a, &b) || !fusion_range(e->right, index, high, &c, &d))
        return 0;

    if (e->op == '+') {
        a += c;
        b += d;
    } else if (e->op == '-') {
        a -= d;
        b -= c;
    } else if (e->op == '*' && c == d && c >= 0) {
        a *= c;
        b *= c;
    } else if (e->op == '*' && a == b && a >= 0) {
        b *= d;
        a *= c;
    } else if (e->op == '/' && c == d && c > 0 && a >= 0) {
        a /= c;
        b /= c;
    } else if (e->op == '%' && c == d && c > 0 && a >= 0) {
        a = 0;
        b = c - 1;
    } else if (e->op == TOK_SHR && c == d && c >= 0 && c < 16 && a >= 0) {
        a >>= c;
        b >>= c;
    } else if (e->op == TOK_SHL && c == d && c >= 0 && c < 16 && a >= 0) {
        a <<= c;
        b <<= c;
    } else
        return 0;

    if (a < (t.is_unsigned ? 0 : -32768) || b > (t.is_unsigned ? 65535 : 32767))
        return 0;

    *low = a;
    *upper = b;
    return 1;
}

static void fusion_access(FusionEffects *effects, Expr *e, int write)
{
    Symbol *object = NULL;
    IndexedOperand operand;

    unsigned offset = 0;
    int64_t low = 0, high;

    if (e->kind == EX_OBJECT)
        object = e->symbol;
    else if (indexed_operand(e, &operand)) {
        object = operand.base;

        if (fusion_range(operand.index, effects->index, effects->high, &low, &high)) {
            low = low * operand.scale + operand.offset;
            high = high * operand.scale + operand.offset + width(e->type) - 1;

            if (low >= 0 && high < (int64_t)width(object->type))
                goto record;
        }

        low = 0;
    } else if (e->kind == EX_MEMBER) {
        object = fixed_memory_object(e, &offset);
        low = offset;
    }

    if (!object) {
        effects->failed = 1;
        return;
    }

    high = low + width(object->type) - 1;
record:
    if (object == effects->index)
        return;
    if (!width(object->type) || effects->count == 128) {
        effects->failed = 1;
        return;
    }

    effects->access[effects->count++] = (FusionAccess){object, low, high, write};
}

static void fusion_effect_expr(FusionEffects *effects, Expr *e, int lvalue)
{
    unsigned i;
    IndexedOperand operand;

    if (!e || effects->failed)
        return;
    if (volatile_expression(e) || e->kind == EX_CALL || e->kind == EX_ADDRESS ||
        e->kind == EX_VA_START) {
        effects->failed = 1;
        return;
    }

    if (e->kind == EX_ASSIGN) {
        fusion_access(effects, e->left, 1);

        if (e->op)
            fusion_access(effects, e->left, 0);

        fusion_effect_expr(effects, e->left, 1);
        fusion_effect_expr(effects, e->right, 0);
        return;
    }

    if (e->kind == EX_PRE || e->kind == EX_POST) {
        fusion_access(effects, e->left, 1);
        fusion_access(effects, e->left, 0);
        fusion_effect_expr(effects, e->left, 1);
        return;
    }

    if (indexed_operand(e, &operand)) {
        if (!lvalue) {
            fusion_access(effects, e, 0);
        }

        fusion_effect_expr(effects, operand.index, 0);
        return;
    }

    if (e->kind == EX_OBJECT) {
        if (!lvalue && !e->type.array && !e->symbol->function)
            fusion_access(effects, e, 0);

        return;
    }
    if (e->kind == EX_DEREF || e->kind == EX_MEMBER) {
        if (!lvalue) {
            fusion_access(effects, e, 0);
        }

        return;
    }

    fusion_effect_expr(effects, e->left, lvalue);
    fusion_effect_expr(effects, e->right, 0);
    fusion_effect_expr(effects, e->third, 0);

    for (i = 0; i < e->arg_count; ++i) {
        fusion_effect_expr(effects, e->args[i], 0);
    }
}

static void fusion_effects(FusionEffects *effects, Statement *s)
{
    for (; s && !effects->failed; s = s->next) {
        if (s->kind != ST_BLOCK && s->kind != ST_EXPR && s->kind != ST_IF && s->kind != ST_EMPTY) {
            effects->failed = 1;
            break;
        }

        fusion_effect_expr(effects, s->expression, 0);
        fusion_effects(effects, s->body);
        fusion_effects(effects, s->alternate);
    }
}

static int fusion_conflict(FusionEffects *a, FusionEffects *b, int both_writes)
{
    unsigned i, j;

    for (i = 0; i < a->count; ++i) {
        for (j = 0; j < b->count; ++j) {
            FusionAccess *x = &a->access[i], *y = &b->access[j];

            if (x->object == y->object && x->low <= y->high && y->low <= x->high &&
                (both_writes ? (x->write || y->write) : x->write))
                return 1;
        }
    }

    return a->failed || b->failed;
}

static int fusion_compatible(FusionLoop *a, FusionLoop *b)
{
    FusionEffects *x = allocate(sizeof *x), *y = allocate(sizeof *y);

    unsigned high = 65535;
    uint32_t n;
    int safe;

    if (a->loop->expression->op != b->loop->expression->op || !body_equal(a->first, b->first) ||
        !body_equal(a->bound, b->bound))
        safe = 0;
    else {
        if (a->loop->expression->op == '<' && integer_constant(a->bound, &n))
            high = (n & 65535) ? (n & 65535) - 1 : 0;

        fusion_domain(a->loop->body, a->index, &high, 1);
        fusion_domain(b->loop->body, b->index, &high, 1);
        x->index = a->index;
        y->index = b->index;
        x->high = y->high = high;
        fusion_effects(x, a->loop->body);
        fusion_effects(y, b->loop->body);
        fusion_effect_expr(x, a->first, 0);
        fusion_effect_expr(x, a->bound, 0);
        fusion_effect_expr(y, b->first, 0);
        fusion_effect_expr(y, b->bound, 0);
        safe = !fusion_conflict(x, y, 1);
    }

    free(x);
    free(y);
    return safe;
}

static void fusion_replace_expr(Expr **at, Symbol *symbol, Expr *value)
{
    Expr *e = *at;

    unsigned i;

    if (!e)
        return;
    if (e->kind == EX_OBJECT && e->symbol == symbol) {
        *at = body_clone(value);
        free_expression(e);
        return;
    }

    fusion_replace_expr(&e->left, symbol, value);
    fusion_replace_expr(&e->right, symbol, value);
    fusion_replace_expr(&e->third, symbol, value);

    for (i = 0; i < e->arg_count; ++i) {
        fusion_replace_expr(&e->args[i], symbol, value);
    }
}

static void fusion_replace(Statement *s, Symbol *symbol, Expr *value)
{
    for (; s; s = s->next) {
        fusion_replace_expr(&s->expression, symbol, value);
        fusion_replace_expr(&s->step, symbol, value);
        fusion_replace(s->initial, symbol, value);
        fusion_replace(s->body, symbol, value);
        fusion_replace(s->alternate, symbol, value);
    }
}

/* Inlining is profitable here because the caller exposes a proved compatible
 * traversal. Read-only scalar formals bind to stable private arguments. */
static int loop_fusion_call(Statement *site, Expr *call, Function *callee)
{
    Statement *source, *next, *copy;
    FusionLoop a, b;

    unsigned i;
    int safe = 0;

    if (cg.parser->no_inline || cg.parser->no_strength_reduction ||
        cg.parser->no_body_optimizations || cg.parser->no_indexed_operands || !site ||
        site->kind != ST_EXPR || site->expression != call || !callee->symbol->internal ||
        callee->symbol->type.base != TY_VOID || callee->symbol->type.pointers)
        return 0;

    source = fusion_single(callee->body);
    next = source ? fusion_single(source->next) : NULL;

    if (!fusion_shape(source, &a) ||
        (next && (next->kind != ST_RETURN || next->expression || next->next)) ||
        !fusion_shape(site->next, &b))
        return 0;

    for (i = 0; i < call->arg_count; ++i) {
        Expr *arg = call->args[i];
        Symbol *formal = leaf_parameter(callee, i);

        if (!formal || formal->type.pointers || formal->type.array || width(formal->type) != 2 ||
            scalar_writes(callee->body, formal) || loop_escapes(callee->body, formal) ||
            (arg->kind != EX_INT && (arg->kind != EX_OBJECT || !body_private(arg->symbol))))
            return 0;
    }

    copy = body_clone_statements(source);

    if (copy->next) {
        free_statements(copy->next);
        copy->next = NULL;
    }

    for (i = 0; i < call->arg_count; ++i) {
        fusion_replace(copy, leaf_parameter(callee, i), call->args[i]);
    }

    {
        Expr *counter = body_object(b.index, call->location);

        fusion_replace(copy, a.index, counter);
        free_expression(counter);
    }

    if (fusion_shape(copy, &a))
        safe = fusion_compatible(&a, &b);

    free_statements(copy);
    return safe;
}

static void fusion_guards(Statement **head, Symbol *index, unsigned high)
{
    Statement *s;

    *head = body_flatten(*head);
    for (s = *head; s; s = s->next) {
        Statement *next = s->next;
        FusionEffects *a, *b;

        if (s->kind != ST_IF || s->alternate || !next || next->kind != ST_IF || next->alternate ||
            s->inline_callee || next->inline_callee ||
            !body_equal(s->expression, next->expression) || body_effect(s->expression))
            continue;

        a = allocate(sizeof *a);
        b = allocate(sizeof *b);
        a->index = b->index = index;
        a->high = b->high = high;
        fusion_effects(a, s->body);
        fusion_effect_expr(b, s->expression, 0);

        if (!fusion_conflict(a, b, 0)) {
            Statement *tail = s->body;

            if (!tail)
                s->body = next->body;
            else {
                while (tail->next) {
                    tail = tail->next;
                }

                tail->next = next->body;
            }

            next->body = NULL;
            s->next = next->next;
            next->next = NULL;
            free_statements(next);
        }

        free(a);
        free(b);
    }
}

static void loop_fusion_regions(Function *f, Statement **head)
{
    Statement **at = head;

    while (*at) {
        Statement *s = *at, *next;
        FusionLoop a, b;

        loop_fusion_regions(f, &s->initial);
        loop_fusion_regions(f, &s->body);
        loop_fusion_regions(f, &s->alternate);

        if (s->kind == ST_BLOCK && s->inline_callee) {
            s->body = body_flatten(s->body);

            if (s->body && s->body->kind == ST_FOR && !s->body->next) {
                Statement *loop = s->body;

                s->body = NULL;
                loop->next = s->next;
                s->next = loop;
            }
        }

        next = s->next;

        if (fusion_shape(s, &a) && fusion_shape(next, &b) && !loop_escapes(f->body, a.index) &&
            !loop_escapes(f->body, b.index) && !scalar_writes(s->body, a.index) &&
            !scalar_writes(next->body, b.index) &&
            (a.index == b.index ||
             (!statement_references(s->body, b.index) &&
              !statement_references(next->body, a.index) &&
              statement_references(f->body, a.index) ==
                  statement_references(s, a.index) - statement_references(s->next, a.index) &&
              statement_references(f->body, b.index) ==
                  statement_references(next, b.index) -
                      statement_references(next->next, b.index))) &&
            fusion_compatible(&a, &b)) {
            Statement *tail = s->body;
            Expr *counter = body_object(a.index, s->location);

            unsigned high = 65535;
            uint32_t n;

            fusion_replace(next->body, b.index, counter);
            free_expression(counter);

            if (!tail)
                s->body = next->body;
            else {
                while (tail->next) {
                    tail = tail->next;
                }

                tail->next = next->body;
            }

            next->body = NULL;
            s->next = next->next;
            next->next = NULL;
            free_statements(next);

            if (integer_constant(a.bound, &n))
                high = (n & 65535) ? (n & 65535) - 1 : 0;

            fusion_domain(s->body, a.index, &high, 1);
            fusion_guards(&s->body, a.index, high);
            code("; fused independent counted loops\n");
            continue;
        }

        at = &s->next;
    }
}

static void loop_fusion_prepare(Function *f)
{
    if (cg.parser->no_strength_reduction || cg.parser->no_body_optimizations ||
        cg.parser->no_indexed_operands || f->symbol->interrupt || f->jump_label_count)
        return;

    loop_fusion_regions(f, &f->body);
}
