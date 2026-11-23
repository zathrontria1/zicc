/* Same-TU, typed-tree inlining. Expansion precedes allocation and preserves
 * conditional evaluation by lifting work into ordinary structured statements.
 * No allocated assembly, ABI homes or shared return labels are copied. */
typedef struct {
    Parser *p;
    Function *caller;
    Function *by_symbol[1024];
    unsigned char recursive[1024];
    unsigned calls[1024];
    Statement *site;
    int translation_complete;
    unsigned serial, growth, specialized_growth, depth, loop_depth;
    unsigned char active[1024];
} Inliner;

static Inliner inl;

static Statement *inl_statement(StatementKind k, Location at)
{
    Statement *s = allocate(sizeof *s);

    s->kind = k;
    s->location = at;
    return s;
}

static void inl_append(Statement **head, Statement *s)
{
    while (*head) {
        head = &(*head)->next;
    }

    *head = s;
}

static Expr *inl_object(Symbol *v, Location at)
{
    Expr *e = new_expr(EX_OBJECT, at, v->type);

    e->symbol = v;
    return e;
}

static Expr *inl_number(unsigned n, Location at)
{
    Expr *e = new_expr(EX_INT, at, type(TY_INT, 0));

    e->value = n;
    return e;
}

static Expr *inl_not(Expr *e)
{
    Expr *n = new_expr(EX_UNARY, e->location, type(TY_INT, 0));

    n->op = '!';
    n->left = e;
    return n;
}

static Expr *inl_boolean(Expr *e)
{
    return inl_not(inl_not(e));
}

static Statement *inl_store(Symbol *v, Expr *value, Location at)
{
    Statement *s = inl_statement(ST_EXPR, at);
    Expr *e = new_expr(EX_ASSIGN, at, v->type);

    e->left = inl_object(v, at);
    e->right = convert(value, unqualified_value(v->type));
    s->expression = e;
    return s;
}

static Statement *inl_branch_value(Symbol *v, Expr *value, Location at)
{
    if (v)
        return inl_store(v, value, at);

    {
        Statement *s = inl_statement(ST_EXPR, at);

        s->expression = value;
        return s;
    }
}

static Symbol *inl_temp(Type t, Location at, const char *suffix)
{
    char name[64];
    Symbol *v;

    unsigned bytes;
    t = unqualified_value(t);
    t.banked = 0;
    bytes = (width(t) + 1) & ~1u;

    if (!bytes || inl.p->symbol_count == 1024 || inl.caller->slots + bytes > 764)
        error_at(at, "inlining exceeds symbol/frame budget");

    snprintf(name, sizeof name, "__inl_%u_%.32s", ++inl.serial, suffix);
    v = new_symbol(inl.p, name, t, at);
    v->owner = inl.caller->id;
    v->scope = 1;
    v->active = 1;
    v->internal = 1;
    v->offset = inl.caller->slots + 1;
    inl.caller->slots += bytes;
    return v;
}

static Expr *inl_snapshot(Expr *e, Statement **pre)
{
    Symbol *v;

    if (e->kind == EX_INT || e->kind == EX_STRING)
        return e;
    if (e->type.base == TY_VOID && !e->type.pointers) {
        Statement *s = inl_statement(ST_EXPR, e->location);

        s->expression = e;
        inl_append(pre, s);
        return inl_number(0, e->location);
    }

    v = inl_temp(value_type(e->type), e->location, "value");
    inl_append(pre, inl_store(v, e, e->location));
    return inl_object(v, e->location);
}

enum { INL_CALL_COST = 12 };

static unsigned inl_expr_cost(Expr *e)
{
    unsigned i, n;

    if (!e)
        return 0;

    n = 1;

    if (e->kind == EX_CALL)
        n += INL_CALL_COST;
    if (e->kind == EX_BINARY && (e->op == '*' || e->op == '/' || e->op == '%'))
        n += 8;

    n += inl_expr_cost(e->left) + inl_expr_cost(e->right) + inl_expr_cost(e->third);

    for (i = 0; i < e->arg_count; ++i) {
        n += inl_expr_cost(e->args[i]);
    }

    return n;
}

static unsigned inl_cost(Statement *s, int *unsupported)
{
    unsigned n = 0;

    for (; s; s = s->next) {
        if (s->kind == ST_SWITCH || s->kind == ST_CASE)
            *unsupported = 1;

        n += 1 + inl_expr_cost(s->expression) + inl_expr_cost(s->step) +
             inl_cost(s->body, unsupported) + inl_cost(s->alternate, unsupported) +
             inl_cost(s->initial, unsupported);

        if (s->kind == ST_FOR || s->kind == ST_DO || s->kind == ST_WHILE)
            n += 32;
    }

    return n;
}

static void inl_edges_expr(Expr *e, unsigned char *edges, unsigned owner, unsigned stride)
{
    unsigned i;

    if (!e)
        return;

    if (e->kind == EX_CALL && e->symbol && inl.by_symbol[e->symbol - inl.p->symbols]) {
        Function *f = inl.by_symbol[e->symbol - inl.p->symbols];

        edges[owner * stride + f->id - 1] = 1;
        ++inl.calls[f->id - 1];
    }

    inl_edges_expr(e->left, edges, owner, stride);
    inl_edges_expr(e->right, edges, owner, stride);
    inl_edges_expr(e->third, edges, owner, stride);

    for (i = 0; i < e->arg_count; ++i) {
        inl_edges_expr(e->args[i], edges, owner, stride);
    }
}

static void inl_edges(Statement *s, unsigned char *edges, unsigned owner, unsigned stride)
{
    for (; s; s = s->next) {
        inl_edges_expr(s->expression, edges, owner, stride);
        inl_edges_expr(s->step, edges, owner, stride);
        inl_edges(s->body, edges, owner, stride);
        inl_edges(s->alternate, edges, owner, stride);
        inl_edges(s->initial, edges, owner, stride);
    }
}

static unsigned inl_private_words(Function *f)
{
    unsigned i, n = 0;

    for (i = 0; i < inl.p->symbol_count; ++i) {
        Symbol *v = &inl.p->symbols[i];

        if (v->owner == f->id && v->offset && !v->type.array && !structure_object(v->type))
            n += (width(v->type) + 1) / 2;
    }

    return n;
}

static int inl_tail_returns(Statement *s, int tail);

static unsigned inl_expansion_cost(Function *f, int *unsupported)
{
    /* Non-tail returns need a completion home, stores and guarded continuations.
     * Charging only the original tree understates that expansion substantially. */
    return inl_cost(f->body, unsupported) + (inl_tail_returns(f->body, 1) ? 0 : 32);
}

static int inl_compact_literal_guard(Function *f, Expr *test, Expr *yes, Expr *no)
{
    uint32_t value;

    return !f->slots && !f->symbol->noinline && f->symbol->param_count == 0 &&
           known_integer(f->symbol->type) && inl_expr_cost(test) <= 4 &&
           integer_constant(yes, &value) && integer_constant(no, &value);
}

/* Two tail returns have a single scalar result and no exit flag */
/* A terminal update of a private parameter needs only its expression value */
static void inl_drop_final_updates(Function *f)
{
    if (f->jump_label_count || body_asm_statements(f->body) || f->body->kind != ST_BLOCK)
        return;

    Statement *last = f->body->body;

    if (!last)
        return;

    while (last->next) {
        last = last->next;
    }

    if (last->kind != ST_EXPR && last->kind != ST_RETURN)
        return;

    for (unsigned i = 0; i < (unsigned)f->symbol->param_count; ++i) {
        Symbol *v = leaf_parameter(f, i);

        if (!v || far_pointer(v->type) || object_volatile(v->type) ||
            (!v->type.pointers && (last->kind != ST_RETURN || v->type.is_bool ||
                                   (v->type.base != TY_INT && v->type.base != TY_LONG))) ||
            loop_escapes(f->body, v) || expression_references(last->expression, v) != 1)
            continue;

        body_drop_private_update(&last->expression, v);
    }
}

/* Make call-only wrappers visibly empty for their own callers. Mixed
 * bodies keep the call sites until normal argument and address analysis. */
static int inl_inert_wrapper(const Statement *s, int *has_call)
{
    for (; s; s = s->next) {
        if (s->kind == ST_EMPTY)
            continue;
        if (s->kind == ST_BLOCK) {
            if (!inl_inert_wrapper(s->body, has_call))
                return 0;

            continue;
        }
        if (s->kind == ST_RETURN && !s->expression)
            continue;
        if (s->kind != ST_EXPR || !s->expression || s->expression->kind != EX_CALL ||
            body_discard_effect(s->expression))
            return 0;

        *has_call = 1;
    }

    return 1;
}

/* A final void return guard can guard the following call directly.
 * This exposes a bounded guarded-call specialization at local-address sites. */
static void inl_guard_final_call(Function *f)
{
    if (f->symbol->type.base != TY_VOID || f->symbol->type.pointers || f->jump_label_count ||
        f->body->kind != ST_BLOCK)
        return;

    for (Statement *s = f->body->body; s; s = s->next) {
        Statement *tail = s->next, *ret = s->body;

        if (s->kind != ST_IF || s->alternate || !tail || tail->next || tail->kind != ST_EXPR ||
            !tail->expression || tail->expression->kind != EX_CALL || !ret || ret->next)
            continue;
        if (ret->kind == ST_BLOCK)
            ret = ret->body;
        if (!ret || ret->kind != ST_RETURN || ret->expression || ret->next)
            continue;

        Expr *neg = new_expr(EX_UNARY, s->location, type(TY_INT, 0));

        neg->op = '!';
        neg->left = s->expression;
        s->expression = neg;
        free_statements(s->body);
        s->body = tail;
        s->next = NULL;
    }
}

static void inl_join_guarded_return(Function *f)
{
    Statement *guard = f->body, *yes, *no, *other;
    Expr *choose;
    uint32_t a, b;
    Type result = f->symbol->type;

    if (f->uses_wide || f->jump_label_count || result.pointers || result.array ||
        (result.base != TY_INT && result.base != TY_CHAR))
        return;
    if (guard && guard->kind == ST_BLOCK && !guard->next)
        guard = guard->body;
    if (!guard || guard->kind != ST_IF || !guard->expression || (guard->alternate && guard->next))
        return;

    other = guard->alternate ? guard->alternate : guard->next;
    no = body_single(other);
    yes = body_single(guard->body);

    if (!no || no->kind != ST_RETURN || no->next || !no->expression || !yes ||
        yes->kind != ST_RETURN || yes->next || !yes->expression || body_effect(yes->expression) ||
        body_effect(no->expression))
        return;

    int effect = body_effect(guard->expression);
    /* A small nullary selection can inline without binding any arguments */
    int compact = inl_compact_literal_guard(f, guard->expression, yes->expression, no->expression);

    if (!f->symbol->internal && !compact)
        return;

    /* Pure if/else can return directly from either arm in a scalar leaf */
    if (guard->alternate && !effect && !compact)
        return;
    if (effect && !compact &&
        !(integer_constant(yes->expression, &a) && integer_constant(no->expression, &b) && a <= 1 &&
          b <= 1 && a != b))
        return;

    choose = new_expr(EX_CHOOSE, guard->location, f->symbol->type);
    choose->left = guard->expression;
    choose->right = yes->expression;
    choose->third = no->expression;
    yes->expression = no->expression = NULL;
    free_statements(guard->body);
    free_statements(other);
    guard->kind = ST_RETURN;
    guard->expression = choose;
    guard->body = guard->alternate = guard->next = NULL;
}

static int inl_leaf_expression(Expr *e)
{
    if (!e)
        return 1;

    return e->kind != EX_CALL && !volatile_expression(e) && inl_leaf_expression(e->left) &&
           inl_leaf_expression(e->right) && inl_leaf_expression(e->third);
}

enum { INL_STRAIGHT, INL_FLAT_FOR, INL_CONTROL, INL_GUARDED, INL_GUARD_ARM };

static int inl_leaf_block(Statement *s, int control)
{
    for (; s; s = s->next) {
        int arm = control == INL_GUARDED && s->kind == ST_IF ? INL_GUARD_ARM : control;
        Expr *e = s->expression;

        if (s->kind != ST_BLOCK && s->kind != ST_EXPR && s->kind != ST_IF && s->kind != ST_RETURN &&
            s->kind != ST_EMPTY &&
            !(control == INL_FLAT_FOR && s->kind == ST_FOR && body_flat_cost(s->body) >= 0) &&
            !(control == INL_CONTROL &&
              (s->kind == ST_FOR || s->kind == ST_WHILE || s->kind == ST_DO ||
               s->kind == ST_BREAK || s->kind == ST_CONTINUE)))
            return 0;

        if (control == INL_GUARD_ARM && s->kind == ST_EXPR && e && e->kind == EX_CALL &&
            e->symbol) {
            for (unsigned i = 0; i < e->arg_count; ++i) {
                if (!inl_leaf_expression(e->args[i]))
                    return 0;
            }
        } else if (!inl_leaf_expression(e))
            return 0;

        if (!inl_leaf_expression(s->step) || !inl_leaf_block(s->body, arm) ||
            !inl_leaf_block(s->initial, INL_STRAIGHT) || !inl_leaf_block(s->alternate, arm))
            return 0;
    }

    return 1;
}

/* An invariant value can replace a read-only formal without a stack home.
 * Binding an object address does not assert that its contents are invariant. */
static int inl_fixed_argument(Expr *arg, Function *f, unsigned i)
{
    Symbol *formal = leaf_parameter(f, i);
    uint32_t constant;

    if (object_volatile(formal->type) || volatile_expression(arg))
        return 0;

    if (formal->type.pointers) {
        while (arg->kind == EX_CAST && value_type(arg->left->type).pointers) {
            arg = arg->left;
        }

        if (!null_pointer_operand(arg) && !(arg->kind == EX_OBJECT && arg->type.array) &&
            !(arg->kind == EX_ADDRESS && arg->left->kind == EX_OBJECT &&
              !arg->left->symbol->function))
            return 0;
    } else if (!integer_constant(arg, &constant))
        return 0;

    return !scalar_writes(f->body, formal) && !loop_escapes(f->body, formal);
}

static int inl_direct_uses(Expr *e, Symbol *formal)
{
    if (!e)
        return 1;

    if (e->kind == EX_DEREF) {
        Expr *base = e->left;
        uint32_t offset;

        if (width(e->type) == 1 && base->kind == EX_BINARY && base->op == '+' &&
            integer_constant(base->right, &offset) && offset < 8)
            base = base->left;
        if (base->kind == EX_OBJECT && base->symbol == formal)
            return 1;
    }

    if (e->kind == EX_OBJECT && e->symbol == formal)
        return 0;
    if (e->kind == EX_ADDRESS && loop_mentions(e->left, formal))
        return 0;
    if (!inl_direct_uses(e->left, formal) || !inl_direct_uses(e->right, formal) ||
        !inl_direct_uses(e->third, formal))
        return 0;

    for (unsigned i = 0; i < e->arg_count; ++i) {
        if (!inl_direct_uses(e->args[i], formal))
            return 0;
    }

    return 1;
}

static int inl_direct_parameter(Statement *s, Symbol *formal)
{
    for (; s; s = s->next) {
        if (!inl_direct_uses(s->expression, formal) || !inl_direct_uses(s->step, formal) ||
            !inl_direct_parameter(s->body, formal) || !inl_direct_parameter(s->alternate, formal) ||
            !inl_direct_parameter(s->initial, formal))
            return 0;
    }

    return 1;
}

/* The argument snapshot can move to the only read when the callee merely
 * copies it to fixed storage. Keep the snapshot for partial overlap. */
static int inl_aggregate_copy_argument(Expr *call, Function *f, Expr **replacement)
{
    Statement *body = body_single(f->body);
    Expr *copy = NULL, *arg, *address, *base;
    Expr assignment, destination, adjusted, index;
    Symbol *formal, *src, *dst;

    unsigned from, to, n, value_arg = 0;

    if (!call->arg_count || call->arg_count > 2 || f->symbol->type.base != TY_VOID ||
        f->symbol->type.pointers)
        return 0;

    for (; body; body = body->next) {
        if (body->kind == ST_EMPTY || (body->kind == ST_BLOCK && !body->body))
            continue;
        if (body->kind == ST_RETURN && !body->expression && !body->next)
            break;
        if (copy || body->kind != ST_EXPR)
            return 0;

        copy = body->expression;
    }

    if (!copy || copy->kind != EX_ASSIGN || copy->op || copy->right->kind != EX_OBJECT ||
        volatile_expression(copy))
        return 0;

    formal = copy->right->symbol;

    while (value_arg < call->arg_count && leaf_parameter(f, value_arg) != formal) {
        ++value_arg;
    }

    if (value_arg == call->arg_count)
        return 0;

    arg = call->args[value_arg];
    n = width(formal->type);

    if (!structure_object(formal->type) || n > 4 || volatile_expression(arg))
        return 0;

    src = direct_memory_object(arg, &from);

    if (!src)
        return 0;

    assignment = *copy;

    if (call->arg_count == 1) {
        dst = direct_memory_object(copy->left, &to);

        if (!dst || dst->owner)
            return 0;
    } else {
        Symbol *pointer = leaf_parameter(f, 1 - value_arg);
        Expr *actual = call->args[1 - value_arg];
        Type t = value_type(pointer->type);

        if (copy->left->kind != EX_DEREF || !t.pointers || far_pointer(t) || body_effect(actual) ||
            !same_type(unqualified_value(t), unqualified_value(value_type(actual->type))))
            return 0;

        destination = *copy->left;
        address = destination.left;
        index = (Expr){.kind = EX_INT, .type = type(TY_INT, 0), .location = address->location};

        if (address->kind == EX_PRE || address->kind == EX_POST) {
            base = address->left;

            if (address->kind == EX_PRE)
                index.value = address->op == TOK_INC ? 1 : UINT32_MAX;
        } else if (address->kind == EX_BINARY && address->op == '+' &&
                   address->right->kind == EX_INT) {
            base = address->left;
            index = *address->right;
        } else
            base = address;

        if (base->kind != EX_OBJECT || base->symbol != pointer)
            return 0;

        adjusted = (Expr){.kind = EX_BINARY,
                          .op = '+',
                          .type = t,
                          .location = address->location,
                          .left = actual,
                          .right = &index};
        destination.left = index.value || actual->type.array ? &adjusted : actual;
        assignment.left = &destination;
        dst = direct_memory_object(&destination, &to);

        if (!dst && !index.value)
            dst = near_object_address(actual, &to);
        if (!dst || to > width(dst->type) || n > width(dst->type) - to)
            return 0;
    }

    if (src == dst && from != to && (from < to ? to - from : from - to) < n)
        return 0;

    if (replacement) {
        assignment.right = arg;
        *replacement = body_clone(&assignment);
    }

    return 1;
}

/* A forwarding wrapper needs only the final copy of its by-value arguments.
 * Restrict a permutation to effect-free arguments so their order can change. */
static Expr *inl_aggregate_forward(Expr *call, Function *f, unsigned *source)
{
    Statement *body = body_single(f->body);
    Expr *target = body ? body->expression : NULL;
    unsigned char used[MAX_ARGUMENTS] = {0};

    if (!body || body->next || body->kind != ST_RETURN || !target || target->kind != EX_CALL ||
        !target->symbol || target->symbol->interrupt || target->arg_count != call->arg_count ||
        structure_object(target->type) || !same_type(target->type, call->type))
        return NULL;

    for (unsigned i = 0; i < call->arg_count; ++i) {
        Expr *actual = call->args[i], *arg = target->args[i];

        unsigned from = 0;

        if (body_effect(actual) || arg->kind != EX_OBJECT || volatile_type(arg->type))
            return NULL;

        while (from < call->arg_count && leaf_parameter(f, from) != arg->symbol) {
            ++from;
        }

        if (from == call->arg_count || used[from] ||
            !same_type(unqualified_value(call->args[from]->type), unqualified_value(arg->type)))
            return NULL;

        used[from] = 1;

        if (source)
            source[i] = from;
    }

    return target;
}

static Expr *inl_clone_expr(Expr *e, Symbol **map, Expr **values);

static int inl_projection_value(Expr *e, Function *f)
{
    unsigned offset;
    Symbol *home;

    if (!e || e->type.array || e->type.pointers || !known_integer(e->type) ||
        volatile_expression(e))
        return 0;

    switch (e->kind) {
    case EX_INT:
        return 1;
    case EX_OBJECT:
        for (unsigned i = 0; i < (unsigned)f->symbol->param_count; ++i) {
            if (e->symbol == leaf_parameter(f, i))
                return 1;
        }

        return 0;
    case EX_CAST:
    case EX_UNARY:
        return inl_projection_value(e->left, f);
    case EX_BINARY:
        return inl_projection_value(e->left, f) && inl_projection_value(e->right, f);
    case EX_CHOOSE:
        return inl_projection_value(e->left, f) && inl_projection_value(e->right, f) &&
               inl_projection_value(e->third, f);
    case EX_MEMBER:
    case EX_DEREF:
        home = fixed_memory_object(e, &offset);

        for (unsigned i = 0; home && i < (unsigned)f->symbol->param_count; ++i) {
            if (home == leaf_parameter(f, i))
                return offset <= width(home->type) && width(e->type) <= width(home->type) - offset;
        }

        return 0;
    default:
        return 0;
    }
}

/* Substitute scalar projections into a tail call. No argument evaluation
 * can change the named aggregate before the projected fields are read. */
static int inl_aggregate_projection_call(Expr *call, Function *f, Expr **replacement)
{
    Statement *body = body_single(f->body);
    Expr *target;
    int aggregate = 0;

    if (!body || body->next || !(target = body->expression) || target->kind != EX_CALL ||
        !target->symbol || target->symbol->interrupt || structure_object(target->type) ||
        !same_type(target->type, call->type) ||
        (body->kind != ST_RETURN &&
         (body->kind != ST_EXPR || call->type.base != TY_VOID || call->type.pointers)))
        return 0;

    for (unsigned i = 0; i < call->arg_count; ++i) {
        Symbol *formal = leaf_parameter(f, i);
        Expr *actual = call->args[i];

        if (body_effect(actual) || volatile_type(formal->type))
            return 0;

        if (structure_object(formal->type)) {
            if (actual->kind != EX_OBJECT || actual->type.banked ||
                !same_type(unqualified_value(actual->type), unqualified_value(formal->type)))
                return 0;

            aggregate = 1;
        } else if (!known_integer(formal->type))
            return 0;
    }

    if (!aggregate)
        return 0;

    for (unsigned i = 0; i < target->arg_count; ++i) {
        if (!inl_projection_value(target->args[i], f))
            return 0;
    }

    if (replacement) {
        Expr **values = allocate(1024 * sizeof *values);

        for (unsigned i = 0; i < call->arg_count; ++i) {
            values[leaf_parameter(f, i) - inl.p->symbols] = call->args[i];
        }

        *replacement = inl_clone_expr(target, NULL, values);
        free(values);
    }

    return 1;
}

/* Replace a field snapshot with its last exact literal write on the
 * straight-line prefix of a call statement. Partial writes invalidate it. */
static void inl_fold_record_guard(Expr *test, Expr *call)
{
    if (!inl.site || inl.site->kind != ST_EXPR || inl.site->expression != call ||
        inl.caller->jump_label_count)
        return;

    Expr **read = &test->left;

    while ((*read)->kind == EX_CAST) {
        read = &(*read)->left;
    }

    unsigned at, bytes = width((*read)->type);
    Symbol *home = direct_memory_object(*read, &at);

    if (home && home->owner == inl.caller->id && home->scope && bytes <= 4) {
        Expr *known = NULL;
        Statement *s = body_single(inl.caller->body);

        for (; s && s != inl.site; s = s->next) {
            if (s->kind == ST_EMPTY)
                continue;

            unsigned offset, size;
            Symbol *written = body_literal_store(s, &offset, &size);

            if (!written)
                known = NULL;
            else if (written == home && offset < at + bytes && at < offset + size) {
                known = NULL;

                if (offset == at && size == bytes &&
                    same_type(unqualified_value(s->expression->left->type),
                              unqualified_value((*read)->type)))
                    known = s->expression->right;
            }
        }

        if (s && known) {
            Expr *literal = body_literal((*read)->type, known->value, (*read)->location);

            free_expression(*read);
            *read = literal;
        }
    }

    scalar_refold_expr(test);
}

/* Project by-value records into scalar guard results before the first
 * callee action. A returning action may modify any original argument. */
static int inl_aggregate_guards(Expr *call, Function *f, Statement **pre, int constant_only)
{
    if (!f->aggregate_abi || f->symbol->type.base != TY_VOID || f->symbol->type.pointers ||
        f->uses_wide || f->uses_bitfields)
        return 0;

    unsigned records = 0, checks = 0;

    for (unsigned i = 0; i < call->arg_count; ++i) {
        Expr *arg = call->args[i];
        Type param = leaf_parameter(f, i)->type;

        if (volatile_type(param))
            return 0;

        if (structure_object(param)) {
            unsigned offset;
            Symbol *home = arg->kind == EX_OBJECT ? arg->symbol : fixed_memory_object(arg, &offset);

            if (!home || arg->type.banked || volatile_expression(arg) ||
                !same_type(unqualified_value(arg->type), unqualified_value(param)))
                return 0;

            ++records;
        } else if (!wide_integer_literal(arg) || param.pointers ||
                   (!known_integer(param) && param.base != TY_LONG))
            return 0;
    }

    if (!records)
        return 0;

    Statement *first = body_single(f->body);

    for (Statement *s = first; s; s = s->next) {
        Expr *test = s->expression;
        Statement *action = body_single(s->body);

        if (s->kind != ST_IF || s->alternate || !test || test->kind != EX_BINARY ||
            (test->op != TOK_EQ && test->op != TOK_NE) || !wide_integer_literal(test->right) ||
            !action || action->next || action->kind != ST_EXPR || !action->expression ||
            action->expression->kind != EX_CALL || action->expression->left ||
            !action->expression->symbol || action->expression->arg_count ||
            ++checks > (constant_only ? 24u : 8u))
            return 0;

        Expr *field = test->left;

        while (field->kind == EX_CAST && known_integer(field->type)) {
            field = field->left;
        }

        if (field->type.pointers || (!known_integer(field->type) && field->type.base != TY_LONG) ||
            volatile_expression(field))
            return 0;
        if (field->kind == EX_MEMBER && field->op == '.')
            field = field->left;
        if (field->kind != EX_OBJECT)
            return 0;

        unsigned i = 0;

        while (i < call->arg_count && leaf_parameter(f, i) != field->symbol) {
            ++i;
        }

        if (i == call->arg_count)
            return 0;
    }

    if (!checks || (!constant_only && !pre))
        return checks != 0;

    Expr **values = allocate(1024 * sizeof *values);

    for (unsigned i = 0; i < call->arg_count; ++i) {
        values[leaf_parameter(f, i) - inl.p->symbols] = call->args[i];
    }

    if (constant_only) {
        for (Statement *s = first; s; s = s->next) {
            Expr *test = inl_clone_expr(s->expression, NULL, values);

            inl_fold_record_guard(test, call);
            int omitted = test->kind == EX_INT && !test->value;

            free_expression(test);

            if (!omitted) {
                free(values);
                return 0;
            }
        }

        free(values);

        if (pre) {
            Statement *marker = inl_statement(ST_BLOCK, call->location);

            marker->inline_callee = f->symbol;
            inl_append(pre, marker);
        }

        return 1;
    }

    Statement *marker = inl_statement(ST_BLOCK, call->location), *guards = NULL;

    marker->inline_callee = f->symbol;

    for (Statement *s = first; s; s = s->next) {
        Statement *guard = inl_statement(ST_IF, s->location);
        Expr *test = inl_clone_expr(s->expression, NULL, values);

        guard->expression = inl_snapshot(test, &marker->body);
        guard->body = inl_statement(ST_EXPR, s->location);
        guard->body->expression = body_clone(body_single(s->body)->expression);
        inl_append(&guards, guard);
    }

    free(values);
    inl_append(&marker->body, guards);
    inl_append(pre, marker);
    return 1;
}

/* A scalar projection cannot distinguish the private copies from their
 * source objects. Every field read has a fixed offset and no address escapes. */
static int inl_aggregate_projection(Expr *call, Function *f, Expr **result)
{
    Statement *entry = body_single(f->body), *yes = entry, *no = NULL;
    Expr *test = NULL, **values;

    if (!entry || f->symbol->param_count < 0 ||
        (unsigned)f->symbol->param_count != call->arg_count || !known_integer(call->type) ||
        volatile_type(call->type))
        return 0;

    if (entry->kind == ST_IF) {
        if (entry->alternate && entry->next)
            return 0;

        test = entry->expression;
        yes = body_single(entry->body);
        no = body_single(entry->alternate ? entry->alternate : entry->next);

        if (!inl_projection_value(test, f) || !no || no->kind != ST_RETURN || no->next ||
            !inl_projection_value(no->expression, f))
            return 0;
    }

    if (!yes || yes->kind != ST_RETURN || yes->next || !yes->expression)
        return 0;

    int literal_indices = 0;

    for (unsigned i = 0; i < call->arg_count; ++i) {
        Expr *arg = call->args[i];
        Type formal = leaf_parameter(f, i)->type;

        if (!test && arg->kind == EX_INT && known_integer(formal) && !volatile_type(formal) &&
            same_type(unqualified_value(arg->type), unqualified_value(formal))) {
            literal_indices = 1;
            continue;
        }
        if (arg->kind != EX_OBJECT || !structure_object(formal) || volatile_type(formal) ||
            arg->type.banked || volatile_type(arg->type) ||
            !same_type(unqualified_value(arg->type), unqualified_value(formal)))
            return 0;
    }

    if (!inl_projection_value(yes->expression, f)) {
        if (!literal_indices || yes->expression->kind != EX_DEREF)
            return 0;

        Expr *indexed = body_clone(yes->expression);

        for (unsigned i = 0; i < call->arg_count; ++i) {
            if (call->args[i]->kind == EX_INT)
                scalar_replace_expr(&indexed, leaf_parameter(f, i), call->args[i]);
        }

        scalar_refold_expr(indexed);
        int valid = inl_projection_value(indexed, f);

        free_expression(indexed);

        if (!valid)
            return 0;
    }

    if (!result)
        return 1;

    values = allocate(1024 * sizeof *values);

    for (unsigned i = 0; i < call->arg_count; ++i) {
        values[leaf_parameter(f, i) - inl.p->symbols] = call->args[i];
    }

    if (test) {
        test = inl_clone_expr(test, NULL, values);

        if (test->kind == EX_BINARY && (test->op == TOK_EQ || test->op == TOK_NE) &&
            body_equal(test->left, test->right)) {
            if (test->op == TOK_NE)
                yes = no;

            free_expression(test);
            test = NULL;
        }
    }

    *result = convert(inl_clone_expr(yes->expression, NULL, values), unqualified_value(call->type));
    if (test) {
        Expr *select = new_expr(EX_CHOOSE, call->location, call->type);

        select->left = test;
        select->right = *result;
        select->third =
            convert(inl_clone_expr(no->expression, NULL, values), unqualified_value(call->type));
        *result = select;
    }

    free(values);
    return 1;
}

static int inl_dispatch_arm(Statement *s)
{
    s = body_single(s);
    return s && !s->next && s->kind == ST_EXPR && s->expression->kind == EX_CALL &&
           s->expression->symbol;
}

static int inl_void_dispatch(Function *f)
{
    Statement *body = body_single(f->body);

    return f->symbol->type.base == TY_VOID && !f->symbol->type.pointers && body && !body->next &&
           body->kind == ST_IF && inl_leaf_expression(body->expression) &&
           inl_dispatch_arm(body->body) && inl_dispatch_arm(body->alternate);
}

/* Charge the bounded expansion budget even when a known entry guard can
 * remove enough work to justify inlining a body that still has calls or loops. */
static int inl_literal_entry_guard(Expr *call, Function *f)
{
    Statement *entry = body_single(f->body);
    BodyFacts facts = {0};

    unsigned i;
    int taken, unsupported = 0, null_argument = 0;
    uint32_t value;

    while (entry && (entry->kind == ST_EMPTY ||
                     (entry->kind == ST_BLOCK && !entry->body && !entry->inline_callee))) {
        entry = entry->next;
    }

    if (!entry || entry->kind != ST_IF || body_effect(entry->expression))
        return 0;

    for (i = 0; i < call->arg_count; ++i) {
        Type t = leaf_parameter(f, i)->type;

        if (object_volatile(t))
            return 0;

        if (t.pointers) {
            if (!null_pointer_operand(call->args[i]) || !inl_fixed_argument(call->args[i], f, i))
                return 0;

            null_argument = 1;
        } else if ((!known_integer(t) && t.base != TY_LONG) ||
                   !integer_constant(call->args[i], &value))
            return 0;
    }

    for (i = 0; i < call->arg_count; ++i) {
        Symbol *formal = leaf_parameter(f, i);

        facts.value[body_symbol(formal)] =
            convert(body_clone(call->args[i]), unqualified_value(formal->type));
    }

    taken = body_known_test(entry->expression, &facts);
    body_clear(&facts);

    if (taken < 0)
        return 0;

    unsigned removed = inl_cost(taken ? entry->alternate : entry->body, &unsupported);
    return removed >= 16 || (null_argument && removed >= 4 && inl.calls[f->id - 1] == 1 &&
                             inl_cost(f->body, &unsupported) <= 96);
}

static int inl_fixed_bitfields(Expr *e)
{
    if (!e)
        return 1;
    if (e->kind == EX_BITFIELD) {
        unsigned offset;
        Symbol *storage = direct_memory_object(e->left, &offset);

        return storage && !storage->type.banked;
    }
    if (!inl_fixed_bitfields(e->left) || !inl_fixed_bitfields(e->right) ||
        !inl_fixed_bitfields(e->third))
        return 0;

    for (unsigned i = 0; i < e->arg_count; ++i) {
        if (!inl_fixed_bitfields(e->args[i]))
            return 0;
    }

    return 1;
}

static int inl_fixed_field_body(Statement *s, int fixed)
{
    for (; s; s = s->next) {
        if ((s->kind != ST_BLOCK && s->kind != ST_EXPR && s->kind != ST_IF &&
             s->kind != ST_RETURN && s->kind != ST_EMPTY) ||
            (fixed && !inl_fixed_bitfields(s->expression)) ||
            !inl_fixed_field_body(s->body, fixed) || !inl_fixed_field_body(s->alternate, fixed))
            return 0;
    }

    return 1;
}

static int inl_absolute_near(Expr *e);

static int inl_fixed_bitfield_argument(Expr *arg, Function *f, unsigned i)
{
    if (inl_fixed_argument(arg, f, i))
        return 1;

    Symbol *formal = leaf_parameter(f, i);

    return formal->type.pointers && !far_pointer(formal->type) && inl_absolute_near(arg) &&
           !object_volatile(formal->type) && !scalar_writes(f->body, formal) &&
           !loop_escapes(f->body, formal);
}

static void inl_resolve_bitfield_bases(Statement *s, BodyFacts *empty)
{
    for (; s; s = s->next) {
        body_replace(&s->expression, empty, 0);
        inl_resolve_bitfield_bases(s->body, empty);
        inl_resolve_bitfield_bases(s->alternate, empty);
    }
}

/* A bound pointer can give a bit-field operation a fixed backing object */
static int inl_fixed_bitfield_addresses(Expr *call, Function *f)
{
    unsigned pointers = 0;

    for (unsigned i = 0; i < call->arg_count; ++i) {
        pointers +=
            leaf_parameter(f, i)->type.pointers && inl_fixed_bitfield_argument(call->args[i], f, i);
    }

    if (!pointers || !inl_fixed_field_body(f->body, 0))
        return 0;

    Statement *copy = body_clone_statements(f->body);

    for (unsigned i = 0; i < call->arg_count; ++i) {
        if (!inl_fixed_bitfield_argument(call->args[i], f, i))
            continue;

        Symbol *formal = leaf_parameter(f, i);
        Expr *value = convert(body_clone(call->args[i]), unqualified_value(formal->type));

        scalar_replace(copy, formal, value);
        free_expression(value);
    }

    BodyFacts *empty = allocate(sizeof *empty);

    inl_resolve_bitfield_bases(copy, empty);
    free(empty);
    int fixed = inl_fixed_field_body(copy, 1);

    free_statements(copy);
    return fixed;
}

static unsigned inl_fixed_fields(Expr *e, Symbol *formal)
{
    unsigned count = 0;

    if (!e)
        return 0;

    if (e->kind == EX_MEMBER && !e->type.array && !structure_object(e->type)) {
        unsigned offset;
        int pointer;
        Expr *base = member_root(e, &offset, &pointer);

        while (base->kind == EX_CAST && base->type.pointers && base->left->type.pointers &&
               !far_pointer(base->type) && !far_pointer(base->left->type)) {
            base = base->left;
        }

        if (pointer && base->kind == EX_OBJECT && base->symbol == formal)
            ++count;
    }

    count += inl_fixed_fields(e->left, formal) + inl_fixed_fields(e->right, formal) +
             inl_fixed_fields(e->third, formal);

    for (unsigned i = 0; i < e->arg_count; ++i) {
        count += inl_fixed_fields(e->args[i], formal);
    }

    return count;
}

static unsigned inl_fixed_field_uses(Statement *s, Symbol *formal)
{
    unsigned count = 0;

    for (; s; s = s->next) {
        count += inl_fixed_fields(s->expression, formal) + inl_fixed_fields(s->step, formal) +
                 inl_fixed_field_uses(s->initial, formal) + inl_fixed_field_uses(s->body, formal) +
                 inl_fixed_field_uses(s->alternate, formal);
    }

    return count;
}

/* A discarded call with literal arguments can expose a short do-while.
 * Simulate its private counter facts and leave each actual store for expansion. */
static int inl_short_literal_loop(Expr *call, Function *f, unsigned cost)
{
    Statement *items[4];

    unsigned count = 0;

    if (inl.p->no_loop_unroll || inl.p->no_known_values || !inl.site || inl.site->kind != ST_EXPR ||
        inl.site->expression != call || !call->arg_count || call->arg_count > 2 || cost > 92 ||
        !inl_leaf_block(f->body, INL_CONTROL) || body_asm_statements(f->body) ||
        !reduction_statements(f->body, items, &count, 4) || count < 2 ||
        items[count - 1]->kind != ST_DO || body_flat_cost(items[count - 1]->body) < 0)
        return -1;

    Statement *loop = items[count - 1];

    /* Leave already-inlined loops available to the scalar effect evaluator.
     * This specialization recovers the indirect cases that it cannot fold. */
    if (!scalar_indirect(loop->body, 1) || body_has_inline_region(loop->body))
        return -1;

    for (unsigned i = 0; i < call->arg_count; ++i) {
        if (!known_integer(leaf_parameter(f, i)->type) || !inl_fixed_argument(call->args[i], f, i))
            return -1;
    }

    for (unsigned i = 0; i + 1 < count; ++i) {
        Expr *e = items[i]->expression;

        if (items[i]->kind != ST_EXPR || !e || e->kind != EX_ASSIGN || e->op ||
            e->left->kind != EX_OBJECT || e->left->symbol->owner != f->id ||
            !known_integer(e->left->type))
            return -1;
    }

    Function *caller = cg.function;

    cg.function = f;
    BodyFacts *facts = allocate(sizeof *facts);

    for (unsigned i = 0; i < call->arg_count; ++i) {
        Symbol *formal = leaf_parameter(f, i);

        facts->value[body_symbol(formal)] =
            convert(body_clone(call->args[i]), unqualified_value(formal->type));
    }

    for (unsigned i = 0; i + 1 < count; ++i) {
        Expr *e = body_clone(items[i]->expression);

        body_expr(&e, facts, 1);
        free_expression(e);
    }

    int trips = body_short_trips(loop, facts, 24, 1);

    body_clear(facts);
    free(facts);
    cg.function = caller;
    return trips;
}

static int inl_mask_uses(Expr *e, Symbol *formal)
{
    if (!e)
        return 0;
    if (e->kind == EX_BINARY && e->op == '&' && e->right->kind == EX_INT &&
        e->left->kind == EX_OBJECT && e->left->symbol == formal)
        return 1;

    return inl_mask_uses(e->left, formal) + inl_mask_uses(e->right, formal) +
           inl_mask_uses(e->third, formal);
}

static int inl_loop_mask_tests(Statement *s, Symbol *formal, int in_loop)
{
    int count = 0;

    for (; s; s = s->next) {
        int loop = s->kind == ST_FOR || s->kind == ST_WHILE || s->kind == ST_DO;

        if (in_loop && s->kind == ST_IF)
            count += inl_mask_uses(s->expression, formal);

        count += inl_loop_mask_tests(s->body, formal, in_loop || loop);
        count += inl_loop_mask_tests(s->alternate, formal, in_loop);
    }

    return count;
}

static void inl_trim_literal_guards(Statement *s)
{
    for (; s; s = s->next) {
        if (s->kind == ST_IF && s->expression && s->expression->kind == EX_INT) {
            int taken = s->expression->value != 0;

            free_statements(taken ? s->alternate : s->body);
            s->body = taken ? s->body : s->alternate;
            s->alternate = NULL;
            free_expression(s->expression);
            s->expression = NULL;
            s->kind = ST_BLOCK;
        }

        inl_trim_literal_guards(s->body);
        inl_trim_literal_guards(s->alternate);
    }
}

/* Measure the smaller body after binding the fixed mask, and keep the
 * public body available for callers with unknown masks. */
static unsigned inl_fixed_loop_mask_cost(Expr *call, Function *f, unsigned cost)
{
    if (inl.p->no_known_values || f->uses_bitfields || f->aggregate_abi ||
        !inl_tail_returns(f->body, 1) || cost > 384 || inl.calls[f->id - 1] != 1 || !inl.site ||
        inl.site->kind != ST_EXPR || inl.site->expression != call || volatile_statements(f->body) ||
        body_asm_statements(f->body))
        return 0;

    for (unsigned i = 0; i < call->arg_count; ++i) {
        Symbol *formal = leaf_parameter(f, i);

        if (known_integer(formal->type) && inl_fixed_argument(call->args[i], f, i) &&
            inl_loop_mask_tests(f->body, formal, 0) >= 3) {
            Statement *copy = body_clone_statements(f->body);
            Expr *value = convert(body_clone(call->args[i]), unqualified_value(formal->type));

            scalar_replace(copy, formal, value);
            free_expression(value);
            scalar_refold(copy);
            inl_trim_literal_guards(copy);
            int bad = 0;

            unsigned reduced = inl_cost(copy, &bad);
            free_statements(copy);

            if (!bad && reduced <= 224 && inl.specialized_growth + reduced <= 288)
                return reduced;
        }
    }

    return 0;
}

static int inl_readonly_field_use(Expr *e, Symbol *formal, int lvalue)
{
    if (!e)
        return 1;
    if (e->kind == EX_MEMBER && e->op == '.' && e->left->kind == EX_OBJECT &&
        e->left->symbol == formal)
        return !lvalue && !e->type.array && !structure_object(e->type) && !volatile_expression(e);
    if (e->kind == EX_OBJECT && e->symbol == formal)
        return 0;

    int writes =
        e->kind == EX_ASSIGN || e->kind == EX_PRE || e->kind == EX_POST || e->kind == EX_ADDRESS;

    if (!inl_readonly_field_use(e->left, formal,
                                writes || (lvalue && e->kind == EX_MEMBER && e->op == '.')) ||
        !inl_readonly_field_use(e->right, formal, 0) ||
        !inl_readonly_field_use(e->third, formal, 0))
        return 0;

    for (unsigned i = 0; i < e->arg_count; ++i) {
        if (!inl_readonly_field_use(e->args[i], formal, 0))
            return 0;
    }

    return 1;
}

static int inl_readonly_field_statements(Statement *s, Symbol *formal)
{
    for (; s; s = s->next) {
        if (!inl_readonly_field_use(s->expression, formal, 0) ||
            !inl_readonly_field_use(s->step, formal, 0) ||
            !inl_readonly_field_statements(s->initial, formal) ||
            !inl_readonly_field_statements(s->body, formal) ||
            !inl_readonly_field_statements(s->alternate, formal))
            return 0;
    }

    return 1;
}

/* The original automatic record is equivalent to its private argument
 * snapshot if only its fixed fields are read and its address never escapes. */
static int inl_readonly_local_record(Expr *call, Function *f, unsigned cost)
{
    if (inl.p->no_body_optimizations || inl.p->no_strength_reduction || cost > 112 ||
        call->arg_count != (unsigned)f->symbol->param_count || f->uses_bitfields || f->uses_wide ||
        structure_object(f->symbol->type) || body_asm_statements(f->body) ||
        body_asm_statements(inl.caller->body))
        return 0;

    int records = 0;

    for (unsigned i = 0; i < call->arg_count; ++i) {
        Symbol *formal = leaf_parameter(f, i);
        Expr *arg = call->args[i];

        if (!structure_object(formal->type)) {
            if (!inl_fixed_argument(arg, f, i))
                return 0;

            continue;
        }
        if (arg->kind != EX_OBJECT || arg->symbol->owner != inl.caller->id || !arg->symbol->scope ||
            arg->symbol->storage || arg->type.banked || volatile_type(arg->type) ||
            volatile_type(formal->type) ||
            !same_type(unqualified_value(arg->type), unqualified_value(formal->type)) ||
            loop_escapes(inl.caller->body, arg->symbol) ||
            !inl_readonly_field_statements(f->body, formal))
            return 0;

        for (Member *m = formal->type.structure->members; m; m = m->next) {
            if (m->type.array || structure_object(m->type) || volatile_type(m->type) ||
                m->bit_width)
                return 0;
        }

        ++records;
    }

    return records != 0;
}

static int inl_specialization(Expr *call, Function *f, unsigned cost)
{
    unsigned fixed = 0, scalars = 0, structures = 0, i;
    int direct_local = 0;

    if (!inl.p->no_body_optimizations && !inl.p->no_strength_reduction && cost <= 512 &&
        f->aggregate_abi && inl_aggregate_guards(call, f, NULL, 1))
        return 1;
    if (inl.p->no_body_optimizations || inl.p->no_strength_reduction || !call->arg_count)
        return 0;
    if (inl_fixed_loop_mask_cost(call, f, cost))
        return 1;
    if (cost > 224 || inl.specialized_growth + cost > 288)
        return 0;
    if (f->aggregate_abi && cost <= 96 &&
        (inl_aggregate_projection(call, f, NULL) || inl_aggregate_projection_call(call, f, NULL) ||
         inl_aggregate_guards(call, f, NULL, 0)))
        return 1;

    if (f->uses_bitfields) {
        if (cost > 128 || f->aggregate_abi || volatile_statements(f->body) ||
            body_asm_statements(f->body))
            return 0;
        if (inl_fixed_bitfield_addresses(call, f))
            return 1;
        if (!inl_fixed_field_body(f->body, 1))
            return 0;

        for (i = 0; i < call->arg_count; ++i) {
            if (leaf_parameter(f, i)->type.pointers || !inl_fixed_argument(call->args[i], f, i))
                return 0;
        }

        return 1;
    }

    if (!inl_tail_returns(f->body, 1))
        return 0;
    if (f->aggregate_abi)
        return inl_aggregate_copy_argument(call, f, NULL) || inl_aggregate_forward(call, f, NULL) ||
               inl_readonly_local_record(call, f, cost);
    if (inl_short_literal_loop(call, f, cost) > 0)
        return 1;

    for (i = 0; i < call->arg_count; ++i) {
        if (inl_fixed_argument(call->args[i], f, i)) {
            Expr *arg = call->args[i];
            Symbol *formal = leaf_parameter(f, i);

            ++fixed;

            if (!formal->type.pointers)
                ++scalars;
            else if (arg->kind == EX_OBJECT && arg->type.array &&
                     arg->symbol->owner == inl.caller->id && width(arg->type) <= 8 &&
                     width(pointed_type(formal->type)) == 1 &&
                     inl_direct_parameter(f->body, formal))
                direct_local = 1;
            else if (arg->kind == EX_ADDRESS &&
                     same_type(pointed_type(formal->type), arg->left->type)) {
                if (arg->left->symbol->owner == inl.caller->id &&
                    inl_direct_parameter(f->body, formal))
                    direct_local = 1;
                if (!far_pointer(formal->type) && !arg->left->type.banked &&
                    structure_object(arg->left->type))
                    ++structures;
            }
        }
    }

    /* Substituting a private home for a dereference can expose definitions
     * and their uses across the call, including around structured control. */
    if (direct_local && cost <= 112 &&
        (inl_leaf_block(f->body, INL_CONTROL) ||
         (cost <= 64 && inl_leaf_block(f->body, INL_GUARDED))))
        return 1;

    /* Require direct field uses to pay for expansion. Indexing through
     * array or pointer members still has address arithmetic after binding. */
    if (structures == call->arg_count && cost <= 144 && inl.calls[f->id - 1] == 1 &&
        !f->uses_wide && !volatile_statements(f->body) && !body_asm_statements(f->body)) {
        unsigned fields = 0;

        for (i = 0; i < call->arg_count; ++i) {
            fields += inl_fixed_field_uses(f->body, leaf_parameter(f, i));
        }

        if (fields >= 3)
            return 1;
    }

    if (cost > 32 && inl_literal_entry_guard(call, f))
        return 1;
    if (!fixed || fixed + 1 < call->arg_count || (!scalars && cost > 32))
        return 0;
    if (scalars && cost <= 48 && inl_void_dispatch(f))
        return 1;

    /* Partial scalar bindings alone don't override frame pressure outside
     * a loop, where a single call has less to gain from expansion. */
    if (fixed == scalars && fixed < call->arg_count && !inl.loop_depth)
        return 0;

    int flat_for = scalars && (fixed >= 3 || (!inl.p->no_loop_unroll && fixed == call->arg_count));

    return inl_leaf_block(f->body, flat_for ? INL_FLAT_FOR : INL_STRAIGHT);
}

static int inl_void_wrapper(Expr *call)
{
    Statement *body = inl.caller->body, *tail;

    if (inl.caller->symbol->type.base != TY_VOID || inl.caller->symbol->type.pointers)
        return 0;

    while (body && body->kind == ST_BLOCK && !body->next) {
        body = body->body;
    }

    tail = body ? body->next : NULL;
    return body && body->kind == ST_EXPR && body->expression == call &&
           (!tail || (tail->kind == ST_RETURN && !tail->expression && !tail->next));
}

/* Main's sole call can absorb a private helper just like a void wrapper.
 * There is no second call site that would keep a duplicate copy alive. */
static int inl_entry_wrapper(Expr *call)
{
    if (strcmp(inl.caller->symbol->name, "main") || call->type.pointers ||
        call->type.base != TY_VOID)
        return 0;

    Statement *first = body_single(inl.caller->body);

    if (!first || first->kind != ST_EXPR || first->expression != call)
        return 0;

    Statement *last = first->next;
    uint32_t result;

    return !last || (last->kind == ST_RETURN && !last->next && last->expression &&
                     integer_constant(last->expression, &result) && !result);
}

static int inl_loop_wrapper(Expr *call, Function *f, unsigned cost)
{
    Statement *steps[10];

    unsigned count = 0, calls = 0;
    uint32_t literal;

    if (inl.p->no_body_optimizations || f->uses_wide || !inl.loop_depth || !inl.site ||
        inl.site->kind != ST_EXPR || inl.site->expression != call || cost > 80 ||
        inl.growth + cost > 192 || body_asm_statements(f->body) ||
        !reduction_statements(f->body, steps, &count, 10))
        return 0;

    for (unsigned i = 0; i < count; ++i) {
        Statement *s = steps[i];
        Expr *e = s->expression;

        if (s->kind == ST_RETURN && i == count - 1 && (!e || integer_constant(e, &literal)))
            break;
        if (s->kind != ST_EXPR || !e)
            return 0;
        if (e->kind == EX_CALL && e->symbol) {
            if (++calls > 2)
                return 0;

            continue;
        }
        if (e->kind != EX_ASSIGN || e->left->kind != EX_OBJECT || e->left->symbol->owner != f->id ||
            !inl_leaf_expression(e))
            return 0;
    }

    return calls != 0;
}

/* Calls that only initialize the supplied scalar homes need no argument
 * snapshots. Keep the stores in source order when two arguments alias. */
static Expr *inl_output_stores(Expr *call, Function *f, Statement **pre)
{
    Statement *items[8];
    Expr *actual[8], *writes[8];

    unsigned count = 0;

    if (!call->arg_count || call->arg_count > 7 ||
        !reduction_statements(f->body, items, &count, 8) || count < 2)
        return NULL;

    Expr *result = items[count - 1]->expression;

    if (items[count - 1]->kind != ST_RETURN || !result || result->kind != EX_INT)
        return NULL;

    for (unsigned i = 0; i < call->arg_count; ++i) {
        Expr *arg = call->args[i];

        if (arg->kind != EX_ADDRESS || arg->left->kind != EX_OBJECT ||
            object_volatile(arg->left->type) || !arg->left->symbol->owner)
            return NULL;
    }

    for (unsigned i = 0; i + 1 < count; ++i) {
        Expr *store = items[i]->expression;

        if (items[i]->kind != ST_EXPR || !store || store->kind != EX_ASSIGN || store->op ||
            store->left->kind != EX_DEREF || store->left->left->kind != EX_OBJECT ||
            !store->right || store->right->kind != EX_INT || volatile_expression(store->left) ||
            structure_object(store->left->type))
            return NULL;

        unsigned arg = 0;

        while (arg < call->arg_count && leaf_parameter(f, arg) != store->left->left->symbol) {
            ++arg;
        }

        if (arg == call->arg_count || !same_type(unqualified_value(call->args[arg]->left->type),
                                                 unqualified_value(store->left->type)))
            return NULL;

        writes[i] = store;
        actual[i] = call->args[arg]->left;
    }

    if (pre) {
        Statement *region = inl_statement(ST_BLOCK, call->location);

        region->inline_callee = f->symbol;

        for (unsigned i = 0; i + 1 < count; ++i) {
            Expr *store = body_clone(writes[i]);

            free_expression(store->left);
            store->left = body_clone(actual[i]);
            Statement *item = inl_statement(ST_EXPR, writes[i]->location);

            item->expression = store;
            inl_append(&region->body, item);
        }

        inl_append(pre, region);
    }

    return result;
}

static Expr *inl_scalar_region(Expr *call, Function *f, int discard, Expr **stores);

static int inl_absolute_near(Expr *e)
{
    return e && e->kind == EX_INT && e->type.pointers && !far_pointer(e->type);
}

static int inl_literal_argument(Expr *e)
{
    unsigned offset;
    Symbol *object = near_object_address(e, &offset);

    return (e->kind == EX_INT && (numeric(e->type) || e->type.pointers)) ||
           (e->type.pointers && null_pointer_operand(e)) || scalar_string_literal(e) != NULL ||
           (object && !object->owner && !object->type.banked);
}

static int inl_snapshot_global_expr(Expr *e, Symbol *home)
{
    if (!e)
        return 1;
    if (volatile_expression(e))
        return 0;
    if (e->kind == EX_CALL && !body_termination_call(e))
        return 0;
    if (e->kind == EX_ADDRESS && loop_mentions(e->left, home))
        return 0;

    if (e->kind == EX_ASSIGN || e->kind == EX_PRE || e->kind == EX_POST) {
        unsigned offset;
        Symbol *written =
            e->left->kind == EX_OBJECT ? e->left->symbol : fixed_memory_object(e->left, &offset);

        if (!written || written == home)
            return 0;
    }

    if (!inl_snapshot_global_expr(e->left, home) || !inl_snapshot_global_expr(e->right, home) ||
        !inl_snapshot_global_expr(e->third, home))
        return 0;

    for (unsigned i = 0; i < e->arg_count; ++i) {
        if (!inl_snapshot_global_expr(e->args[i], home))
            return 0;
    }

    return 1;
}

static int inl_snapshot_global_statements(Statement *s, Symbol *home)
{
    for (; s; s = s->next) {
        if (s->kind != ST_BLOCK && s->kind != ST_EMPTY && s->kind != ST_EXPR && s->kind != ST_IF &&
            s->kind != ST_RETURN)
            return 0;
        if (!inl_snapshot_global_expr(s->expression, home) ||
            !inl_snapshot_global_statements(s->body, home) ||
            !inl_snapshot_global_statements(s->alternate, home))
            return 0;
    }

    return 1;
}

/* An adjacent assignment to a global can bind a nullary callee's read
 * when every callee write is to a separately identified object. */
static Expr *inl_snapshot_global(Expr *call, Function *f, unsigned cost)
{
    if (call->arg_count || f->uses_bitfields || f->aggregate_abi || cost > 96 ||
        inl.specialized_growth + cost > 160 || inl.p->no_body_optimizations ||
        inl.p->no_strength_reduction || inl.p->no_known_values || inl.calls[f->id - 1] != 1 ||
        inl.caller->jump_label_count || !inl.site || inl.site->kind != ST_EXPR ||
        inl.site->expression != call || body_asm_statements(f->body) ||
        body_asm_statements(inl.caller->body))
        return NULL;

    Statement *prev = NULL, *s = body_single(inl.caller->body);

    for (; s && s != inl.site; s = s->next) {
        if (s->kind != ST_EMPTY)
            prev = s;
    }

    Expr *store = prev && prev->kind == ST_EXPR ? prev->expression : NULL;

    if (!s || !store || store->kind != EX_ASSIGN || store->op || store->left->kind != EX_OBJECT ||
        store->left->symbol->owner || !word_integer(store->left->type) ||
        volatile_expression(store) || store->right->kind != EX_INT ||
        !statement_references(f->body, store->left->symbol) ||
        !inl_snapshot_global_statements(f->body, store->left->symbol))
        return NULL;

    return store;
}

static Function *inl_candidate(Expr *e, int diagnose)
{
    Symbol *v;
    Function *f;
    const char *reason = NULL;

    unsigned cost, words, pressure, benefit, i, extra = 0, count = 0;
    int bad = 0, loop_leaf, literal_args;

    if (!e || e->kind != EX_CALL || !e->symbol) {
        return NULL;
    }

    v = e->symbol;
    f = inl.by_symbol[v - inl.p->symbols];

    if (inl.caller->uses_bitfields) {
        Expr *site = inl.site ? inl.site->expression : NULL;

        if (!f || !site || inl.site->kind != ST_EXPR || site->kind != EX_ASSIGN || site->op ||
            site->left->kind != EX_OBJECT || site->right != e || !inl_output_stores(e, f, NULL))
            return NULL;
    }

    if (inl.caller->aggregate_abi &&
        (!f || !f->aggregate_abi || !inl.site ||
         (!(inl.site->kind == ST_RETURN && inl_aggregate_projection(e, f, NULL)) &&
          (inl.site->expression != e ||
           (inl.site->kind != ST_EXPR &&
            (inl.site->kind != ST_RETURN || !inl_aggregate_forward(e, f, NULL))))))) {
        int invalid = 0;

        if (!f || !f->aggregate_abi || !inl.site)
            return NULL;

        unsigned candidate = inl_expansion_cost(f, &invalid);

        if (invalid || !inl_readonly_local_record(e, f, candidate))
            return NULL;
    }

    if (v->noinline || (f && f->uses_wide) ||
        (!v->always_inline && (inl.p->no_inline || inl.caller->symbol->interrupt)))
        return NULL;

    if (!f)
        reason = inl.p->source_lto ? "definition is not available in source LTO inputs"
                                   : "definition is not available in this translation unit";
    else if (f->jump_label_count)
        reason = "function contains goto or labels";
    else if (inl.recursive[f->id - 1] || inl.active[f->id - 1])
        reason = "recursive expansion";
    else if (v->variadic || v->param_count < 0 || (unsigned)v->param_count != e->arg_count)
        reason = "variadic or unknown argument list";
    else if (v->interrupt || inl.caller->symbol->interrupt)
        reason = "interrupt boundary";
    else if (!strcmp(v->name, "main"))
        reason = "main is not an inline candidate";
    else if (inl.depth >= 8)
        reason = "inline depth limit";

    if (reason) {
        if (v->always_inline && diagnose)
            error_at(e->location, "cannot always_inline '%s': %s", v->name, reason);

        return NULL;
    }

    cost = inl_expansion_cost(f, &bad);

    for (i = 0; i < inl.p->symbol_count; ++i) {
        Symbol *s = &inl.p->symbols[i];

        if (s->owner == f->id && (s->offset || s->copy_temporary)) {
            extra += ((width(s->type) + 1) & ~1u) + (structure_object(s->type) ? 2 : 0);
            ++count;
        }
    }

    literal_args = e->arg_count && !inl.p->no_body_optimizations && !inl.p->no_strength_reduction;

    for (i = 0; i < e->arg_count && literal_args; ++i) {
        literal_args = inl_literal_argument(e->args[i]);
    }

    if (bad && literal_args && !v->always_inline) {
        Expr *value = inl_scalar_region(
            e, f, inl.site && inl.site->kind == ST_EXPR && inl.site->expression == e, NULL);
        int folded = value && value->kind == EX_INT;

        free_expression(value);

        if (folded)
            return f;
    }

    /* Reserve lifting/return temporaries as well as cloned locals. Forced
     * expansion bypasses profitability, never storage or structural limits. */
    if (bad)
        reason = "switch bodies are not supported for substitution";
    else if (cost > 2048 || inl.growth + inl.specialized_growth + cost > 4096)
        reason = "hard expansion budget";
    else if (inl.p->symbol_count + count + 32 >= 1024 || inl.caller->slots + extra + 64 > 764)
        reason = "symbol/frame budget";
    else if (f->uses_bitfields && !inl_specialization(e, f, cost))
        reason = "function uses bit-fields";
    else if (f->aggregate_abi && !inl_specialization(e, f, cost))
        reason = "function uses the aggregate ABI";

    if (reason) {
        if (v->always_inline && diagnose)
            error_at(e->location, "cannot always_inline '%s': %s", v->name, reason);

        return NULL;
    }
    if (v->always_inline)
        return f;
    if (inl.growth + cost <= 128 && inl_output_stores(e, f, NULL))
        return f;
    if (cost <= 224 && inl.specialized_growth + cost <= 288 && loop_fusion_call(inl.site, e, f))
        return f;
    if (inl_specialization(e, f, cost))
        return f;
    if (inl_snapshot_global(e, f, cost))
        return f;
    if (inl_loop_wrapper(e, f, cost))
        return f;

    /* A single-use private helper behind a void wrapper can disappear
     * entirely. This removes its call frame without duplicating the loop. */
    if (v->internal && !v->address_taken && inl.calls[f->id - 1] == 1 && cost <= 160 &&
        !inl.growth && inl_private_words(f) <= 12 && (inl_void_wrapper(e) || inl_entry_wrapper(e)))
        return f;

    loop_leaf = inl.loop_depth && v->type.base == TY_VOID && !v->type.pointers &&
                e->arg_count >= 2 && e->arg_count <= 4 && cost <= 96 &&
                inl_leaf_block(f->body, INL_GUARDED);
    words = inl_private_words(f);
    int small_scalar_leaf =
        !f->uses_wide && !f->uses_bitfields && !f->aggregate_abi && known_integer(v->type) &&
        !v->type.pointers && !v->type.array && words <= 3 &&
        inl_leaf_block(f->body, INL_STRAIGHT) && cost <= (inl.loop_depth ? 40u : 28u) &&
        inl.growth + cost <= (inl.loop_depth ? 192u : 128u) &&
        (inl.loop_depth || (v->internal && !v->address_taken && inl.calls[f->id - 1] == 1));

    if (small_scalar_leaf)
        return f;

    int literal_budget = literal_args && words <= 12 && !bound_contains_loop(f->body);

    pressure = inl_private_words(inl.caller) + words;
    pressure = pressure > 14 ? (pressure - 14) * 8 : 0;
    benefit = 18 + e->arg_count * 4 + (f->slots ? 6 : 0) + (v->inline_hint ? 16 : 0);

    for (i = 0; i < e->arg_count; ++i) {
        if (e->args[i]->kind == EX_INT)
            benefit += 4;
    }

    if (cost <= (v->inline_hint || loop_leaf || literal_budget ? 96u : 32u) &&
        inl.growth + cost <= (v->inline_hint                ? 384u
                              : loop_leaf || literal_budget ? 192u
                                                            : 128u) &&
        pressure + cost / 4 < benefit + (loop_leaf ? 12 : 0))
        return f;

    /* A nullary scalar body can also reduce to a literal. Charge ordinary
     * cloning at its usual cost, but permit proven constant substitution. */
    if (literal_args || (!e->arg_count && !v->param_count && numeric(v->type) &&
                         !inl.p->no_body_optimizations && !inl.p->no_strength_reduction)) {
        Expr *value = inl_scalar_region(
            e, f, inl.site && inl.site->kind == ST_EXPR && inl.site->expression == e, NULL);
        int folded = value && value->kind == EX_INT;

        free_expression(value);

        if (folded)
            return f;
    }

    return NULL;
}

static int inl_has(Expr *e)
{
    unsigned i;

    if (!e)
        return 0;
    if (inl_candidate(e, 1))
        return 1;
    if (inl_has(e->left) || inl_has(e->right) || inl_has(e->third))
        return 1;

    for (i = 0; i < e->arg_count; ++i) {
        if (inl_has(e->args[i])) {
            return 1;
        }
    }

    return 0;
}

/* A widening pointer conversion is redundant when every use is a scalar
 * member access. The near and far addresses agree for a valid access. */
static int inl_member_uses(Expr *e, Symbol *v)
{
    unsigned i;

    if (!e)
        return 1;
    if (e->kind == EX_MEMBER && e->op == TOK_ARROW && e->left->kind == EX_OBJECT &&
        e->left->symbol == v)
        return !e->type.array && !structure_object(e->type);

    if (e->kind == EX_DEREF && !e->type.array && !structure_object(e->type)) {
        Expr *base = e->left;

        if (base->kind == EX_OBJECT && base->symbol == v)
            return 1;
        if (base->kind == EX_BINARY && (base->op == '+' || base->op == '-')) {
            if (base->left->kind == EX_OBJECT && base->left->symbol == v)
                return inl_member_uses(base->right, v);
            if (base->op == '+' && base->right->kind == EX_OBJECT && base->right->symbol == v)
                return inl_member_uses(base->left, v);
        }
    }

    if (e->kind == EX_CAST && value_type(e->type).pointers && !far_pointer(value_type(e->type)) &&
        e->left->kind == EX_OBJECT && e->left->symbol == v)
        return 1;

    if (e->kind == EX_CAST && !e->type.pointers && !e->type.array && e->type.base != TY_FLOAT &&
        (e->type.is_bool || reg_width(e->type) <= 2)) {
        Expr *in = e->left;

        while (in->kind == EX_CAST && !in->type.pointers && !in->type.array &&
               in->type.base != TY_FLOAT && reg_width(in->type) == 4) {
            in = in->left;
        }

        if (in->kind == EX_OBJECT && in->symbol == v)
            return 1;
    }

    if (e->kind == EX_UNARY && e->op == '!' && e->left->kind == EX_OBJECT && e->left->symbol == v)
        return 1;

    if (e->kind == EX_BINARY && (e->op == TOK_EQ || e->op == TOK_NE)) {
        if (e->left->kind == EX_OBJECT && e->left->symbol == v && e->right->kind == EX_INT &&
            !e->right->value)
            return 1;
        if (e->right->kind == EX_OBJECT && e->right->symbol == v && e->left->kind == EX_INT &&
            !e->left->value)
            return 1;
    }

    if (e->kind == EX_OBJECT && e->symbol == v)
        return 0;
    if (e->kind == EX_ADDRESS && (e->left->kind == EX_MEMBER || e->left->kind == EX_DEREF))
        return 0;
    if (!inl_member_uses(e->left, v) || !inl_member_uses(e->right, v) ||
        !inl_member_uses(e->third, v))
        return 0;

    for (i = 0; i < e->arg_count; ++i) {
        if (!inl_member_uses(e->args[i], v))
            return 0;
    }

    return 1;
}

static int inl_member_condition(Expr *e, Symbol *v)
{
    if (!e)
        return 1;
    if (e->kind == EX_OBJECT && e->symbol == v)
        return 1;
    if (e->kind == EX_BINARY && (e->op == TOK_LAND || e->op == TOK_LOR))
        return inl_member_condition(e->left, v) && inl_member_condition(e->right, v);

    return inl_member_uses(e, v);
}

static int inl_member_statements(Statement *s, Symbol *v)
{
    for (; s; s = s->next) {
        int cond =
            (s->kind == ST_IF || s->kind == ST_WHILE || s->kind == ST_DO || s->kind == ST_FOR);

        if (!(cond ? inl_member_condition(s->expression, v) : inl_member_uses(s->expression, v)) ||
            !inl_member_uses(s->step, v) || !inl_member_statements(s->initial, v) ||
            !inl_member_statements(s->body, v) || !inl_member_statements(s->alternate, v))
            return 0;
    }

    return 1;
}

static Expr *inl_clone_expr(Expr *e, Symbol **map, Expr **values)
{
    Expr *n;

    unsigned i;

    if (!e)
        return NULL;
    if (e->kind == EX_OBJECT && values[e->symbol - inl.p->symbols])
        return body_clone(values[e->symbol - inl.p->symbols]);

    n = allocate(sizeof *n);

    *n = *e;
    if (e->symbol && map && map[e->symbol - inl.p->symbols]) {
        n->symbol = map[e->symbol - inl.p->symbols];

        if (e->kind == EX_OBJECT &&
            ((far_pointer(e->type) && !far_pointer(n->symbol->type)) ||
             (!e->type.pointers && e->type.base == TY_LONG && word_integer(n->symbol->type))))
            n->type = n->symbol->type;
    }

    n->left = inl_clone_expr(e->left, map, values);
    n->right = inl_clone_expr(e->right, map, values);
    n->third = inl_clone_expr(e->third, map, values);

    if (n->kind == EX_DEREF && n->left->kind == EX_ADDRESS && n->left->left->kind == EX_OBJECT &&
        same_type(n->type, n->left->left->type)) {
        Expr *object = n->left->left;

        n->left->left = NULL;
        free_expression(n);
        return object;
    }

    if (e->kind == EX_DEREF && far_pointer(value_type(e->left->type)) &&
        !far_pointer(value_type(n->left->type)))
        n->type.banked = 0;

    if (e->kind == EX_BINARY && (e->op == '+' || e->op == '-') && far_pointer(e->type)) {
        if (!far_pointer(value_type(n->left->type)) && value_type(n->left->type).pointers)
            n->type = value_type(n->left->type);
        else if (e->op == '+' && !far_pointer(value_type(n->right->type)) &&
                 value_type(n->right->type).pointers)
            n->type = value_type(n->right->type);
    }

    if (e->kind == EX_BINARY && (e->op == TOK_EQ || e->op == TOK_NE)) {
        if (n->left->kind == EX_INT && !n->left->value && far_pointer(n->left->type) &&
            value_type(n->right->type).pointers && !far_pointer(value_type(n->right->type)))
            n->left->type = value_type(n->right->type);
        if (n->right->kind == EX_INT && !n->right->value && far_pointer(n->right->type) &&
            value_type(n->left->type).pointers && !far_pointer(value_type(n->left->type)))
            n->right->type = value_type(n->left->type);
    }

    if (e->kind == EX_MEMBER && e->op == TOK_ARROW && far_pointer(value_type(e->left->type)) &&
        !far_pointer(value_type(n->left->type)))
        n->type.banked = 0;

    for (i = 0; i < e->arg_count; ++i) {
        n->args[i] = inl_clone_expr(e->args[i], map, values);
    }

    return n;
}

static Statement *inl_clone(Statement *s, Symbol **map, Expr **values)
{
    Statement *head = NULL, **tail = &head;

    for (; s; s = s->next) {
        Statement *n = allocate(sizeof *n);

        *n = *s;
        n->next = NULL;
        n->expression = inl_clone_expr(s->expression, map, values);
        n->step = inl_clone_expr(s->step, map, values);
        n->body = inl_clone(s->body, map, values);
        n->alternate = inl_clone(s->alternate, map, values);
        n->initial = inl_clone(s->initial, map, values);
        *tail = n;
        tail = &n->next;
    }

    return head;
}

static int inl_return_count(Statement *s)
{
    int n = 0;

    for (; s; s = s->next) {
        n += (s->kind == ST_RETURN) + inl_return_count(s->body) + inl_return_count(s->alternate) +
             inl_return_count(s->initial);
    }

    return n;
}

static int inl_definitely_returns(Statement *s)
{
    for (; s; s = s->next) {
        if (s->kind == ST_RETURN)
            return 1;
        if (s->kind == ST_BLOCK && inl_definitely_returns(s->body))
            return 1;
        if (s->kind == ST_IF && s->alternate && inl_definitely_returns(s->body) &&
            inl_definitely_returns(s->alternate))
            return 1;
    }

    return 0;
}

/* Tail trees need no synthetic exit flag. Other returns use a private flag
 * and structured guards, so nested loops cannot turn a return into a break. */
static int inl_tail_returns(Statement *s, int tail)
{
    for (; s; s = s->next) {
        int last = tail && !s->next;

        if (s->kind == ST_RETURN && !last)
            return 0;

        if (s->kind == ST_BLOCK) {
            if (!inl_tail_returns(s->body, last))
                return 0;
        } else if (s->kind == ST_IF) {
            if (!inl_tail_returns(s->body, last) || !inl_tail_returns(s->alternate, last))
                return 0;
        } else if (inl_return_count(s->body) || inl_return_count(s->initial))
            return 0;
    }

    return 1;
}

static Expr *inl_running(Symbol *done, Expr *condition, Location at)
{
    Expr *e = new_expr(EX_BINARY, at, type(TY_INT, 0));

    e->op = TOK_LAND;
    e->left = inl_not(inl_object(done, at));
    e->right = condition ? condition : inl_number(1, at);
    return e;
}

static void inl_returns(Statement *s, Symbol *done, Symbol *result)
{
    for (; s; s = s->next) {
        int exits =
            inl_return_count(s->body) || inl_return_count(s->alternate) || s->kind == ST_RETURN;

        if (s->kind == ST_RETURN) {
            Statement *body = NULL;

            if (s->expression) {
                if (result)
                    body = inl_store(result, s->expression, s->location);
                else if (body_effect(s->expression)) {
                    body = inl_statement(ST_EXPR, s->location);
                    body->expression = s->expression;
                } else
                    free_expression(s->expression);
            }

            s->expression = NULL;

            if (done)
                inl_append(&body, inl_store(done, inl_number(1, s->location), s->location));

            s->kind = ST_BLOCK;
            s->body = body;
        } else {
            inl_returns(s->body, done, result);
            inl_returns(s->alternate, done, result);
            inl_returns(s->initial, done, result);

            if (done && (s->kind == ST_FOR || s->kind == ST_WHILE || s->kind == ST_DO) && exits) {
                s->expression = inl_running(done, s->expression, s->location);

                if (s->step) {
                    Expr *q = new_expr(EX_CHOOSE, s->location, s->step->type);

                    q->left = inl_object(done, s->location);
                    q->right = inl_number(0, s->location);
                    q->third = s->step;
                    s->step = q;
                }
            }
        }

        if (done && exits && s->next) {
            Statement *rest = s->next, *guard = inl_statement(ST_IF, s->location);

            inl_returns(rest, done, result);
            guard->expression = inl_not(inl_object(done, s->location));
            guard->body = rest;
            s->next = guard;
            break;
        }
    }
}

static void inl_statements(Statement **head);
static Expr *inl_lower(Expr *e, Statement **pre);

/* Calls may change the pointed-to object, but they cannot change a private
 * caller pointer or index whose address has never escaped. */
static int inl_stable_address(Expr *e, Expr *later)
{
    if (!e || object_volatile(e->type))
        return 0;
    if (e->kind == EX_INT)
        return 1;

    if (e->kind == EX_OBJECT) {
        Symbol *v = e->symbol;

        if (e->type.array)
            return 1;

        return v->owner == inl.caller->id && !loop_escapes(inl.caller->body, v) &&
               !scalar_writes_expr(later, v);
    }

    if (e->kind == EX_CAST)
        return inl_stable_address(e->left, later);
    if (e->kind == EX_MEMBER && e->type.array)
        return inl_stable_address(e->left, later);

    return e->kind == EX_BINARY && (e->op == '+' || e->op == '-' || e->op == '*') &&
           inl_stable_address(e->left, later) && inl_stable_address(e->right, later);
}

static Expr *inl_lvalue(Expr *e, Statement **pre, Expr *later)
{
    if (e->kind == EX_OBJECT)
        return e;

    if (e->kind == EX_DEREF) {
        Expr *address = e->left;

        if (later && inl_stable_address(address, later))
            return e;

        if (!inl.p->no_indexed_operands && address->kind == EX_BINARY && address->op == '+' &&
            address->left->kind == EX_OBJECT && address->left->type.array &&
            !address->left->type.banked && !address->left->symbol->owner &&
            !address->left->symbol->dpage && known_integer(address->right->type))
            address->right = inl_snapshot(inl_lower(address->right, pre), pre);
        else
            e->left = inl_snapshot(inl_lower(address, pre), pre);
    } else if (e->kind == EX_MEMBER) {
        if (e->op == TOK_ARROW) {
            if (!later || !inl_stable_address(e->left, later))
                e->left = inl_snapshot(inl_lower(e->left, pre), pre);
        } else if (e->left->kind == EX_ASSIGN)
            e->left = inl_lower(e->left, pre);
        else
            e->left = inl_lvalue(e->left, pre, later);
    }

    return e;
}

/* Stores in a scalar region target only unescaped locals, so a fixed
 * nonvolatile load can follow its value through the local definitions. */
static Expr *inl_scalar_expr(Expr *e, Expr **values, Function *f, int single_return, int literals,
                             int *bad)
{
    Expr *n;

    if (!e || *bad)
        return NULL;

    if (literals && e->kind == EX_CAST && numeric(e->type) && e->type.base != TY_FLOAT &&
        e->type.base != TY_DOUBLE && !e->type.is_bool && reg_width(e->type) <= 4 &&
        e->left->kind == EX_OBJECT && e->left->symbol->owner == f->id &&
        !object_volatile(e->left->type)) {
        Expr *address = values[e->left->symbol - inl.p->symbols];

        if (inl_absolute_near(address))
            return convert(body_literal(type(TY_LONG, 0), (uint16_t)address->value, e->location),
                           e->type);
    }

    if (literals && e->kind == EX_BINARY && (e->op == TOK_EQ || e->op == TOK_NE) &&
        value_type(e->left->type).pointers && value_type(e->right->type).pointers) {
        Expr *a = e->left, *b = e->right;

        if (a->kind == EX_OBJECT && a->symbol->owner == f->id && !object_volatile(a->type))
            a = values[a->symbol - inl.p->symbols];
        if (b->kind == EX_OBJECT && b->symbol->owner == f->id && !object_volatile(b->type))
            b = values[b->symbol - inl.p->symbols];
        if (a && b && same_fixed_address(a, b))
            return body_literal(e->type, e->op == TOK_EQ, e->location);
    }

    Expr *search = literals ? scalar_string_search(e) : NULL;

    if (search) {
        Expr *text = scalar_string_base(search->args[0]);

        if (text->kind == EX_OBJECT && text->symbol->owner == f->id && !volatile_expression(text))
            text = values[text->symbol - inl.p->symbols];

        Expr *character = inl_scalar_expr(search->args[1], values, f, single_return, literals, bad);

        scalar_refold_expr(character);
        int found = scalar_string_contains(text, character);

        free_expression(character);

        if (found >= 0 && !*bad)
            return body_literal(e->type, found == (e->op == TOK_NE), e->location);

        *bad = 1;
        return NULL;
    }

    if (e->type.pointers || e->type.array || volatile_expression(e) ||
        (reg_width(e->type) != 2 && !(single_return && e->type.base == TY_LONG) &&
         (!literals || !numeric(e->type) ||
          (reg_width(e->type) != 4 && e->type.base != TY_LONGLONG)))) {
        *bad = 1;
        return NULL;
    }

    if (e->kind == EX_OBJECT) {
        if (!e->symbol->owner) {
            Expr *value = values[e->symbol - inl.p->symbols];

            return body_clone(value ? value : e);
        }
        if (e->symbol->owner != f->id || !values[e->symbol - inl.p->symbols]) {
            *bad = 1;
            return NULL;
        }

        return body_clone(values[e->symbol - inl.p->symbols]);
    }

    if (e->kind == EX_MEMBER || e->kind == EX_DEREF) {
        unsigned offset;
        Symbol *home = fixed_memory_object(e, &offset);

        if (home && !home->owner && offset <= width(home->type) &&
            width(e->type) <= width(home->type) - offset)
            return body_clone(e);
    }

    if (single_return && e->kind == EX_DEREF && e->left->kind == EX_OBJECT &&
        e->left->symbol->owner == f->id) {
        Expr *address = values[e->left->symbol - inl.p->symbols];

        if (address && address->kind == EX_ADDRESS && same_type(e->type, address->left->type) &&
            !volatile_expression(address->left))
            return body_clone(address->left);
    }

    if (e->kind != EX_INT && e->kind != EX_CAST && e->kind != EX_UNARY && e->kind != EX_BINARY &&
        e->kind != EX_CHOOSE) {
        *bad = 1;
        return NULL;
    }

    n = allocate(sizeof *n);
    *n = *e;
    n->left = inl_scalar_expr(e->left, values, f, single_return, literals, bad);
    n->right = inl_scalar_expr(e->right, values, f, single_return, literals, bad);
    n->third = inl_scalar_expr(e->third, values, f, single_return, literals, bad);

    if (inl_expr_cost(n) > 96)
        *bad = 1;

    return n;
}

static int inl_scalar_argument(Expr *e)
{
    if (!e || volatile_expression(e) || e->type.pointers || e->type.array ||
        reg_width(e->type) != 2)
        return 0;
    if (e->kind == EX_INT || e->kind == EX_OBJECT)
        return 1;
    if (e->kind == EX_CAST || e->kind == EX_UNARY)
        return inl_scalar_argument(e->left);

    return e->kind == EX_BINARY && inl_scalar_argument(e->left) && inl_scalar_argument(e->right);
}

static int literal_integer_tree(Expr *e);

static int inl_scalar_test(Expr *e, Expr **values, Function *f)
{
    int bad = 0, taken = -1;
    Expr *test = inl_scalar_expr(e, values, f, 0, 1, &bad);

    if (test && !bad) {
        scalar_refold_expr(test);
        taken = scalar_literal_truth(test);
    }

    free_expression(test);
    return taken;
}

enum InlScalarUpdate { INL_KEEP_EXPR, INL_NEED_LITERAL, INL_LOOP_UPDATE, INL_GLOBAL_STORE };

/* Preserve the conversions surrounding a nested literal assignment */
static Expr *inl_assignment_value(Expr *rhs, Expr *literal)
{
    if (rhs->kind != EX_CAST)
        return body_clone(literal);

    return convert(inl_assignment_value(rhs->left, literal), rhs->type);
}

static int inl_scalar_update(Expr *e, Expr **values, Function *f, int literals,
                             enum InlScalarUpdate kind)
{
    int bad = 0, op;
    Expr *v;

    unsigned i;

    if (!e ||
        (e->kind != EX_ASSIGN &&
         !(kind == INL_LOOP_UPDATE && (e->kind == EX_PRE || e->kind == EX_POST))) ||
        e->left->kind != EX_OBJECT || object_volatile(e->left->type))
        return 0;

    if (kind == INL_GLOBAL_STORE) {
        if (e->left->symbol->owner)
            return 0;
    } else if (e->left->symbol->owner != f->id || loop_escapes(f->body, e->left->symbol))
        return 0;

    if ((kind == INL_LOOP_UPDATE || kind == INL_GLOBAL_STORE) &&
        (!literal_integer_tree(e->left) || !literal_integer_tree(e->right)))
        return 0;

    i = (unsigned)(e->left->symbol - inl.p->symbols);
    op = e->op;
    Expr *inner = e->right;

    while (inner && inner->kind == EX_CAST && numeric(inner->type) &&
           inner->type.base != TY_FLOAT && inner->type.base != TY_DOUBLE) {
        inner = inner->left;
    }

    if (e->kind == EX_ASSIGN && !op && literals && inner->kind == EX_ASSIGN && !inner->op &&
        (kind == INL_KEEP_EXPR || kind == INL_NEED_LITERAL)) {
        /* The nested store converts before outer casts and assignment */
        if (!inl_scalar_update(inner, values, f, 1, INL_NEED_LITERAL))
            return 0;

        v = inl_assignment_value(e->right, values[inner->left->symbol - inl.p->symbols]);
    } else if (e->kind == EX_ASSIGN && !op && literals &&
               (kind == INL_KEEP_EXPR || kind == INL_NEED_LITERAL) &&
               (inner->kind == EX_PRE || inner->kind == EX_POST) &&
               inner->left->kind == EX_OBJECT) {
        unsigned index = (unsigned)(inner->left->symbol - inl.p->symbols);

        if (!values[index] || values[index]->kind != EX_INT)
            return 0;

        Expr *old = inner->kind == EX_POST ? body_clone(values[index]) : NULL;

        if (!inl_scalar_update(inner, values, f, 1, INL_LOOP_UPDATE)) {
            free_expression(old);
            return 0;
        }

        v = inl_assignment_value(e->right, old ? old : values[index]);
        free_expression(old);
    } else if (e->kind == EX_ASSIGN)
        v = inl_scalar_expr(e->right, values, f, 0, literals, &bad);
    else {
        if (!known_integer(e->left->type))
            return 0;

        op = e->op == TOK_INC ? '+' : '-';
        v = inl_number(1, e->location);
    }

    if (bad || (op && !values[i])) {
        free_expression(v);
        return 0;
    }

    if (op) {
        Expr *operation =
            new_expr(EX_BINARY, e->location,
                     op == TOK_SHL || op == TOK_SHR ? promoted(e->left->type)
                                                    : common_type(e->left->type, v->type));
        operation->op = op;
        operation->left = body_clone(values[i]);
        operation->right = v;
        v = operation;
    }

    if (v)
        v = convert(v, unqualified_value(e->left->type));

    free_expression(values[i]);
    values[i] = v;

    if (kind != INL_KEEP_EXPR && v) {
        scalar_refold_expr(v);
        return v->kind == EX_INT;
    }

    return 1;
}

typedef struct {
    Symbol *home;
    uint16_t sum;
} InlLoopSum;

static int inl_scalar_addend(Expr *e, Expr **values, Function *f, InlLoopSum *effect)
{
    if (!effect || !e || !e->left || e->left->kind != EX_OBJECT)
        return 0;

    Symbol *v = e->left->symbol;

    if (v->owner || !word_integer(v->type) || object_volatile(v->type) ||
        (effect->home && effect->home != v))
        return 0;
    if ((e->kind == EX_POST || e->kind == EX_PRE) && (e->op == TOK_INC || e->op == TOK_DEC)) {
        effect->home = v;
        effect->sum = (uint16_t)(effect->sum + (e->op == TOK_INC ? 1 : -1));
        return 1;
    }
    if (e->kind != EX_ASSIGN || e->op != '+' || !literal_integer_tree(e->right))
        return 0;

    int bad = 0;
    Expr *rhs = inl_scalar_expr(e->right, values, f, 0, 1, &bad);
    uint32_t n = 0;

    if (rhs && !bad)
        scalar_refold_expr(rhs);

    int literal = rhs && !bad && integer_constant(rhs, &n);

    free_expression(rhs);

    if (!literal)
        return 0;

    effect->home = v;
    effect->sum = (uint16_t)(effect->sum + n);
    return 1;
}

static int inl_scalar_actions(Statement *s, Expr **values, Function *f, unsigned *budget,
                              InlLoopSum *effect, Statement **returned);
static int inl_scalar_switch(Statement *s, Expr **values, Function *f, Statement **action);

static int inl_scalar_steps(Expr *e, Expr **values, Function *f, unsigned *budget)
{
    if (!e)
        return 0;
    if (e->kind != EX_COMMA)
        return inl_scalar_update(e, values, f, 1, INL_LOOP_UPDATE);
    if (!*budget)
        return 0;

    --*budget;
    return inl_scalar_steps(e->left, values, f, budget) &&
           inl_scalar_steps(e->right, values, f, budget);
}

/* Run only loops whose conditions and private scalar updates stay literal */
static int inl_scalar_loop(Statement *s, Expr **values, Function *f, unsigned *budget,
                           InlLoopSum *effect, Statement **returned)
{
    Expr *test = s->expression, *update = NULL, relation;

    if (test && test->kind == EX_BINARY && comparison(test->op) && test->left->kind == EX_PRE &&
        test->left->left->kind == EX_OBJECT) {
        update = test->left;
        relation = *test;
        relation.left = update->left;
        test = &relation;
    }

    int null_guard = test && test->kind == EX_OBJECT && value_type(test->type).pointers &&
                     test->symbol->owner == f->id && !volatile_expression(test);

    if ((!literal_integer_tree(test) && !null_guard) ||
        !inl_scalar_actions(s->initial, values, f, budget, effect, returned))
        return 0;
    if (*returned)
        return 1;
    if (null_guard) {
        Expr *value = values[test->symbol - inl.p->symbols];

        return s->kind != ST_DO && inl_absolute_near(value) && !value->value;
    }

    int first = s->kind == ST_DO;

    while (*budget) {
        --*budget;

        if (!first && update && !inl_scalar_update(update, values, f, 1, INL_LOOP_UPDATE))
            return 0;

        int taken = (first || !test) ? 1 : inl_scalar_test(test, values, f);

        first = 0;

        if (taken <= 0)
            return taken == 0;
        if (!inl_scalar_actions(s->body, values, f, budget, effect, returned))
            return 0;
        if (*returned) {
            if ((*returned)->kind == ST_BREAK)
                *returned = NULL;

            return 1;
        }
        if (s->step && !inl_scalar_steps(s->step, values, f, budget))
            return 0;
    }

    return 0;
}

static int inl_scalar_actions(Statement *s, Expr **values, Function *f, unsigned *budget,
                              InlLoopSum *effect, Statement **returned)
{
    for (; s; s = s->next) {
        if (!*budget)
            return 0;

        --*budget;

        if (s->kind == ST_EMPTY)
            continue;

        if (s->kind == ST_BLOCK) {
            if (!inl_scalar_actions(s->body, values, f, budget, effect, returned))
                return 0;
        } else if (s->kind == ST_IF && literal_integer_tree(s->expression)) {
            int taken = inl_scalar_test(s->expression, values, f);

            if (taken < 0 || !inl_scalar_actions(taken ? s->body : s->alternate, values, f, budget,
                                                 effect, returned))
                return 0;
        } else if (s->kind == ST_FOR || s->kind == ST_WHILE || s->kind == ST_DO) {
            if (!inl_scalar_loop(s, values, f, budget, effect, returned))
                return 0;
        } else if (s->kind == ST_RETURN || s->kind == ST_BREAK) {
            *returned = s;
        } else if (s->kind == ST_SWITCH) {
            if (!inl_scalar_switch(s, values, f, returned))
                return 0;
        } else if (s->kind != ST_EXPR || (!inl_scalar_addend(s->expression, values, f, effect) &&
                                          !inl_scalar_steps(s->expression, values, f, budget)))
            return 0;

        if (*returned)
            return 1;
    }

    return 1;
}

static int inl_scalar_switch(Statement *s, Expr **values, Function *f, Statement **action)
{
    int bad = 0;
    Expr *test = inl_scalar_expr(s->expression, values, f, 0, 1, &bad);

    if (test && !bad)
        scalar_refold_expr(test);
    if (bad || !test || !wide_integer_literal(test)) {
        free_expression(test);
        return 0;
    }

    Statement selection = *s;

    selection.expression = test;
    Statement *entry = switch_constant_case(&selection);

    free_expression(test);

    *action = NULL;
    if (!entry)
        return 1;

    Statement *body = s->body;

    if (body->kind == ST_BLOCK && !body->next)
        body = body->body;

    for (; body; body = body->next) {
        Statement *label = body;
        int entered = 0;

        while (label && label->kind == ST_CASE) {
            entered |= label == entry;
            label = label->body;
        }

        if (!entered)
            continue;
        if (!label || label->next)
            return 0;
        if (label->kind == ST_RETURN) {
            *action = label;
            return 1;
        }

        if (label->kind == ST_IF && literal_integer_tree(label->expression)) {
            int taken = inl_scalar_test(label->expression, values, f);

            if (taken >= 0) {
                Statement *branch = body_single(taken ? label->body : label->alternate);

                if (branch && !branch->next && branch->kind == ST_RETURN) {
                    *action = branch;
                    return 1;
                }
            }
        }

        return label->kind == ST_BREAK;
    }

    return 0;
}

static Expr *inl_scalar_region_pre(Expr *call, Function *f, int discard, Expr **stores,
                                   Statement **pre)
{
    Expr **values, *result = NULL;
    Statement *items[32], *s;

    unsigned i, count = 0, loop_budget = 128, store_budget = 6;
    int bad = 0, literals = !inl.p->no_body_optimizations && !inl.p->no_strength_reduction;
    unsigned char need_snapshot[MAX_ARGUMENTS] = {0};

    unsigned uses[MAX_ARGUMENTS] = {0};
    int any_effect = 0, snapshot_args = 0;

    if (!reduction_statements(f->body, items, &count, 32) || !count)
        return NULL;

    s = items[0];
    discard |= !call->type.pointers && call->type.base == TY_VOID;
    /* A single return has no earlier loads that must remain snapshots */
    int single_return = count == 1 && s->kind == ST_RETURN;

    if (!discard && single_return && s->expression && s->expression->kind == EX_CHOOSE &&
        inl_compact_literal_guard(f, s->expression->left, s->expression->right,
                                  s->expression->third))
        return convert(body_clone(s->expression), unqualified_value(call->type));

    for (i = 0; i < call->arg_count && literals; ++i) {
        Expr *arg = call->args[i];

        unsigned offset;
        /* A discarded read-only call may take the address of a local.
         * The evaluator must still reject effects through that address. */
        literals = inl_literal_argument(arg) || (discard && !stores && !body_discard_effect(arg) &&
                                                 near_object_address(arg, &offset));
    }

    if (discard && !literals)
        return NULL;

    if (pre && !discard && !stores && !literals && single_return && s->expression) {
        for (i = 0; i < call->arg_count; ++i) {
            Expr *arg = call->args[i];

            if (inl_has(arg) || body_effect(arg) || volatile_expression(arg))
                any_effect = 1;
        }
    }

    values = allocate(1024 * sizeof *values);

    for (i = 0; i < call->arg_count; ++i) {
        Expr *arg = call->args[i];
        Symbol *formal = leaf_parameter(f, i);

        if (stores && (!literal_integer_tree(arg) || object_volatile(formal->type))) {
            bad = 1;
            break;
        }

        if (!literals) {
            if (pre && !discard && !stores && single_return && s->expression) {
                uses[i] = (unsigned)body_count_expr_symbol(s->expression, formal);

                if (any_effect) {
                    if (arg->kind != EX_INT &&
                        !(arg->kind == EX_OBJECT && body_private(arg->symbol) &&
                          !body_effect(arg) && !volatile_expression(arg)))
                        need_snapshot[i] = 1;
                } else if (inl_scalar_argument(arg)) {
                    if (uses[i] > 1 && inl_expr_cost(arg) > 2)
                        need_snapshot[i] = 1;
                } else if (arg->kind == EX_ADDRESS && arg->left->kind == EX_DEREF &&
                           formal->type.pointers && !object_volatile(formal->type) &&
                           same_type(arg->type, formal->type) &&
                           inl_stable_address(arg->left->left, NULL)) {
                } else if (uses[i] == 1 && !arg->type.array && !structure_object(arg->type) &&
                           (known_integer(formal->type) ||
                            (formal->type.base == TY_LONG &&
                             direct_operand(arg, formal->type, 0, 0) &&
                             direct_operand(arg, formal->type, 1, 0))) &&
                           !formal->type.pointers &&
                           (reg_width(arg->type) == 2 || reg_width(arg->type) == 4)) {
                } else if (!arg->type.array && !structure_object(arg->type) &&
                           (known_integer(formal->type) || formal->type.pointers)) {
                    need_snapshot[i] = 1;
                } else {
                    bad = 1;
                    break;
                }

                if (need_snapshot[i]) {
                    if (object_volatile(formal->type) || formal->type.array ||
                        structure_object(formal->type) ||
                        inl.p->symbol_count + snapshot_args + 4 >= 1024 ||
                        inl.caller->slots + snapshot_args * 4 + 8 > 764) {
                        bad = 1;
                        break;
                    }

                    ++snapshot_args;
                    values[formal - inl.p->symbols] = inl_object(formal, call->location);
                    continue;
                }
            } else if (!inl_scalar_argument(arg) &&
                       !(single_return && arg->kind == EX_ADDRESS && arg->left->kind == EX_DEREF &&
                         formal->type.pointers && !object_volatile(formal->type) &&
                         same_type(arg->type, formal->type) &&
                         inl_stable_address(arg->left->left, NULL))) {
                bad = 1;
                break;
            }
        }

        values[formal - inl.p->symbols] = convert(body_clone(arg), unqualified_value(formal->type));

        if (discard) {
            scalar_refold_expr(values[formal - inl.p->symbols]);
            Expr *value = values[formal - inl.p->symbols];

            unsigned offset;

            if (object_volatile(formal->type) ||
                (value->kind != EX_INT && !near_object_address(value, &offset))) {
                bad = 1;
                break;
            }
        }
    }

    for (unsigned j = 0; j < count && !bad; ++j) {
        s = items[j];
        Expr *e = s->expression;

        if (literals && s->kind == ST_EXPR)
            while (e && e->kind == EX_COMMA && !body_discard_effect(e->right)) {
                e = e->left;
            }

        if (stores && s->kind != ST_EXPR && s->kind != ST_DO && s->kind != ST_WHILE &&
            s->kind != ST_FOR && !literal_integer_tree(e)) {
            bad = 1;
            break;
        }

        if (literals && s->kind == ST_SWITCH) {
            if (!inl_scalar_switch(s, values, f, &s)) {
                bad = 1;
                break;
            }
            if (!s)
                continue;

            e = s->expression;
        }

        if (literals && s->kind == ST_RETURN && discard && !body_discard_effect(e))
            break;
        if (s->kind == ST_RETURN && (literals || j + 1 == count) && e) {
            result = inl_scalar_expr(e, values, f, single_return, literals, &bad);
            break;
        }

        if (literals && s->kind == ST_IF) {
            int taken = inl_scalar_test(e, values, f);

            if (taken >= 0) {
                Statement *branch_items[32];

                unsigned added = 0;

                if (reduction_statements(taken ? s->body : s->alternate, branch_items, &added,
                                         32 - count)) {
                    memmove(items + j + 1 + added, items + j + 1, (count - j - 1) * sizeof *items);
                    memcpy(items + j + 1, branch_items, added * sizeof *items);
                    count += added;
                    continue;
                }
            }

            bad = 1;
            break;
        }

        if (literals && (s->kind == ST_FOR || s->kind == ST_WHILE || s->kind == ST_DO)) {
            InlLoopSum effect = {0};
            Statement *returned = NULL;
            int track = discard && stores && !*stores && j + 1 == count;

            if (!inl_scalar_loop(s, values, f, &loop_budget, track ? &effect : NULL, &returned))
                bad = 1;
            else if (effect.home) {
                /* Accumulate modulo one target word without introducing a
                 * signed overflowing addition that the source did not have. */
                Type u = type(TY_INT, 0);

                u.is_unsigned = 1;
                Expr *add = new_expr(EX_BINARY, s->location, u);

                add->op = '+';
                add->left = convert(body_object(effect.home, s->location), u);
                add->right = body_literal(u, effect.sum, s->location);
                Expr *set = new_expr(EX_ASSIGN, s->location, effect.home->type);

                set->left = body_object(effect.home, s->location);
                set->right = convert(add, effect.home->type);
                *stores = set;
            }

            if (!bad && returned) {
                Expr *value = returned->expression;

                if (value && (!discard || body_discard_effect(value)))
                    result = inl_scalar_expr(value, values, f, 0, literals, &bad);

                break;
            }

            continue;
        }

        if (s->kind == ST_EXPR && stores && literals && e &&
            (e->kind == EX_ASSIGN || e->kind == EX_PRE || e->kind == EX_POST) &&
            e->left->kind == EX_OBJECT && !e->left->symbol->owner && store_budget) {
            Expr *store;

            unsigned home = (unsigned)(e->left->symbol - inl.p->symbols);

            if (e->kind == EX_ASSIGN) {
                if (!inl_scalar_update(e, values, f, 1, INL_GLOBAL_STORE)) {
                    bad = 1;
                    break;
                }

                store = new_expr(EX_ASSIGN, e->location, e->type);
                store->left = body_clone(e->left);
                store->right = body_clone(values[home]);
            } else {
                if (!literal_integer_tree(e->left)) {
                    bad = 1;
                    break;
                }

                free_expression(values[home]);
                values[home] = NULL;
                store = body_clone(e);
            }

            Expr **last = *stores && (*stores)->kind == EX_COMMA ? &(*stores)->right : stores;

            if (e->kind == EX_ASSIGN && *last && (*last)->left->symbol == e->left->symbol) {
                free_expression(*last);
                *last = store;
            } else if (*stores) {
                Expr *sequence = new_expr(EX_COMMA, e->location, store->type);

                sequence->left = *stores;
                sequence->right = store;
                store = sequence;
                *stores = store;
            } else
                *stores = store;

            --store_budget;
            continue;
        }

        if (s->kind != ST_EXPR ||
            (stores && (!e || e->kind != EX_ASSIGN || !literal_integer_tree(e->left) ||
                        !literal_integer_tree(e->right))) ||
            !inl_scalar_update(e, values, f, literals,
                               (discard || stores) ? INL_NEED_LITERAL : INL_KEEP_EXPR))
            bad = 1;
    }

    for (i = 0; i < 1024; ++i) {
        free_expression(values[i]);
    }

    free(values);

    if (bad) {
        free_expression(result);
        return NULL;
    }

    if (!bad && snapshot_args && result) {
        for (i = call->arg_count; i; --i) {
            if (!need_snapshot[i - 1])
                continue;

            Symbol *formal = leaf_parameter(f, i - 1);
            Expr *arg = inl_lower(body_clone(call->args[i - 1]), pre);

            if (uses[i - 1]) {
                Symbol *copy = inl_temp(formal->type, call->location, formal->name);
                Expr *obj = inl_object(copy, call->location);

                inl_append(pre, inl_store(copy, arg, call->location));
                scalar_replace_expr(&result, formal, obj);
                free_expression(obj);
            } else {
                Statement *eval = inl_statement(ST_EXPR, call->location);

                eval->expression = arg;
                inl_append(pre, eval);
            }
        }
    }

    if (result) {
        result = convert(result, unqualified_value(call->type));

        if (literals)
            scalar_refold_expr(result);
    }

    if (discard) {
        int pure = !result || result->kind == EX_INT;

        free_expression(result);
        return pure ? inl_number(0, call->location) : NULL;
    }

    return result;
}

static Expr *inl_scalar_region(Expr *call, Function *f, int discard, Expr **stores)
{
    return inl_scalar_region_pre(call, f, discard, stores, NULL);
}

/* In a terminal void wrapper a private argument's home can become the
 * formal's home. Arguments still have their original evaluation order;
 * other arguments cannot mutate or share the selected home. */
static Symbol *inl_wrapper_argument(Expr *call, Function *f, unsigned index)
{
    Expr *arg = call->args[index];
    Symbol *formal = leaf_parameter(f, index), *home;

    unsigned i;

    if (!inl_void_wrapper(call) || arg->kind != EX_OBJECT || !arg->type.pointers ||
        !same_value_representation(formal->type, arg->type) || !loop_private(arg->symbol) ||
        object_volatile(arg->type) || loop_escapes(f->body, formal))
        return NULL;

    home = arg->symbol;

    for (i = 0; i < call->arg_count; ++i) {
        if (i != index &&
            (!element_address_pure(call->args[i]) || volatile_expression(call->args[i]) ||
             loop_mentions(call->args[i], home)))
            return NULL;
    }

    return home;
}

/* A cloned long parameter observed only after integer truncation can keep
 * just the low word. The incoming expression still runs at the call site. */
static int inl_low_word_expr(Expr *e, Symbol *v)
{
    if (!e)
        return 1;

    if (e->kind == EX_CAST && known_integer(e->type) && !e->type.is_bool) {
        Expr *source = e->left;

        while (source->kind == EX_CAST && source->type.base == TY_LONG && !source->type.pointers) {
            source = source->left;
        }

        if (source->kind == EX_OBJECT && source->symbol == v)
            return 1;
    }

    if (e->kind == EX_OBJECT && e->symbol == v)
        return 0;
    if (!inl_low_word_expr(e->left, v) || !inl_low_word_expr(e->right, v) ||
        !inl_low_word_expr(e->third, v))
        return 0;

    for (unsigned i = 0; i < e->arg_count; ++i) {
        if (!inl_low_word_expr(e->args[i], v))
            return 0;
    }

    return 1;
}

static int inl_low_word_uses(Statement *s, Symbol *v)
{
    for (; s; s = s->next) {
        if (!inl_low_word_expr(s->expression, v) || !inl_low_word_expr(s->step, v) ||
            !inl_low_word_uses(s->initial, v) || !inl_low_word_uses(s->body, v) ||
            !inl_low_word_uses(s->alternate, v))
            return 0;
    }

    return 1;
}

static Expr *inl_expand(Expr *e, Function *f, Statement **pre, int needed)
{
    unsigned source[MAX_ARGUMENTS];
    Expr *fixed_copy;
    Expr *output = inl_output_stores(e, f, pre);

    if (output) {
        int bad = 0;

        inl.growth += inl_expansion_cost(f, &bad);
        Expr *result = body_clone(output);

        ++f->symbol->inline_instances;
        free_expression(e);
        return result;
    }

    if (f->aggregate_abi && e->arg_count == 2 && inl_aggregate_copy_argument(e, f, &fixed_copy)) {
        int bad = 0;
        Statement *marker = inl_statement(ST_BLOCK, e->location);
        Expr *result = inl_number(0, e->location);

        marker->inline_callee = f->symbol;
        marker->body = inl_statement(ST_EXPR, e->location);
        marker->body->expression = fixed_copy;
        inl_append(pre, marker);
        inl.specialized_growth += inl_expansion_cost(f, &bad);
        ++f->symbol->inline_instances;
        free_expression(e);
        return result;
    }

    Expr *forward = f->aggregate_abi ? inl_aggregate_forward(e, f, source) : NULL;

    if (forward) {
        Expr *call = new_expr(EX_CALL, e->location, e->type);
        Statement *marker = inl_statement(ST_BLOCK, e->location);

        call->symbol = forward->symbol;
        call->arg_count = e->arg_count;

        for (unsigned i = 0; i < call->arg_count; ++i) {
            call->args[i] = e->args[source[i]];
            e->args[source[i]] = NULL;
        }

        marker->inline_callee = f->symbol;
        inl_append(pre, marker);
        ++f->symbol->inline_instances;
        free_expression(e);
        return call;
    }

    if (f->aggregate_abi && inl_aggregate_guards(e, f, pre, 1)) {
        Expr *result = inl_number(0, e->location);

        ++f->symbol->inline_instances;
        free_expression(e);
        return result;
    }

    if (f->aggregate_abi && inl_aggregate_guards(e, f, pre, 0)) {
        int bad = 0;
        Expr *result = inl_number(0, e->location);

        inl.specialized_growth += inl_expansion_cost(f, &bad);
        ++f->symbol->inline_instances;
        free_expression(e);
        return result;
    }

    Expr *projected_call;

    if (f->aggregate_abi && inl_aggregate_projection_call(e, f, &projected_call)) {
        int bad = 0;
        Statement *marker = inl_statement(ST_BLOCK, e->location);

        marker->inline_callee = f->symbol;
        inl_append(pre, marker);
        inl.specialized_growth += inl_expansion_cost(f, &bad);
        ++f->symbol->inline_instances;
        free_expression(e);
        return projected_call;
    }

    Expr *scalar = NULL;
    Statement *scalar_setup = NULL;

    if (f->aggregate_abi && inl_aggregate_projection(e, f, &scalar)) {
        int bad = 0;

        inl.specialized_growth += inl_expansion_cost(f, &bad);

        if (!needed) {
            free_expression(scalar);
            scalar = inl_number(0, e->location);
        }
    } else
        scalar = inl_scalar_region_pre(e, f, !needed, NULL, &scalar_setup);

    if (scalar) {
        /* Scalar substitution emits just the result and any argument snapshots */
        if (!f->aggregate_abi && !f->symbol->always_inline) {
            int bad = 0;

            inl.growth += inl_expr_cost(scalar) + inl_cost(scalar_setup, &bad);
        }

        if (scalar_setup)
            inl_append(pre, scalar_setup);

        Statement *marker = inl_statement(ST_BLOCK, e->location);

        marker->inline_callee = f->symbol;
        inl_append(pre, marker);
        ++f->symbol->inline_instances;
        free_expression(e);
        return scalar;
    }

    Symbol **map = allocate(1024 * sizeof *map), *result = NULL, *done = NULL;
    Statement *body, *entry;
    Expr **values = allocate(1024 * sizeof *values);

    unsigned i, original = inl.p->symbol_count, cost;
    int bad = 0, specialized, loop_wrapper;

    cost = inl_expansion_cost(f, &bad);
    loop_wrapper = inl_loop_wrapper(e, f, cost);
    Expr *snapshot = inl_snapshot_global(e, f, cost);

    specialized = inl_specialization(e, f, cost) || loop_fusion_call(inl.site, e, f) || snapshot;
    int loop_trips = specialized && !inl.p->no_body_optimizations && !inl.p->no_strength_reduction
                         ? inl_short_literal_loop(e, f, cost)
                         : -1;
    unsigned mask_cost =
        specialized && !inl.p->no_body_optimizations && !inl.p->no_strength_reduction
            ? inl_fixed_loop_mask_cost(e, f, cost)
            : 0;

    if (mask_cost)
        cost = mask_cost;

    inl.caller->uses_bitfields |= f->uses_bitfields;

    /* The enclosing expansion already paid for a nested call instruction.
     * Replacing it removes that instruction while retaining argument costs. */
    if (inl.depth && cost >= INL_CALL_COST)
        cost -= INL_CALL_COST;

    if (specialized)
        inl.specialized_growth += cost;
    else
        inl.growth += cost;

    ++f->symbol->inline_instances;

    for (i = 0; i < e->arg_count; ++i) {
        Symbol *formal = leaf_parameter(f, i);

        unsigned index = (unsigned)(formal - inl.p->symbols);

        if (specialized && f->aggregate_abi)
            values[index] = body_clone(e->args[i]);
        else if (specialized &&
                 (inl_fixed_argument(e->args[i], f, i) ||
                  (f->uses_bitfields && inl_fixed_bitfield_argument(e->args[i], f, i)) ||
                  loop_fusion_call(inl.site, e, f)))
            values[index] = convert(body_clone(e->args[i]), unqualified_value(formal->type));
        else if (!inl.p->no_body_optimizations && !inl.p->no_strength_reduction &&
                 formal->type.base == TY_LONG && !formal->type.pointers &&
                 !object_volatile(formal->type) && e->args[i]->kind == EX_CAST &&
                 known_integer(e->args[i]->left->type) && !body_asm_statements(f->body) &&
                 inl_low_word_uses(f->body, formal))
            map[index] = inl_temp(type(TY_INT, 0), e->location, formal->name);
        else
            map[index] = inl_wrapper_argument(e, f, i);
    }

    for (i = 0; i < original; ++i) {
        Symbol *v = &inl.p->symbols[i];

        if (v->owner == f->id && (v->offset || v->copy_temporary) && !map[i] && !values[i]) {
            Symbol *copy = inl_temp(v->type, e->location, v->name);

            if (v->type.array)
                inl.caller->slots += ((width(v->type) + 1) & ~1u) - 2;

            if (structure_object(v->type)) {
                ++copy->offset;
                inl.caller->slots += 2;
            }

            copy->type = v->type;
            copy->type.banked = 0;
            copy->copy_temporary = v->copy_temporary;
            map[i] = copy;
        }
    }

    for (i = e->arg_count; i; --i) {
        Symbol *v = leaf_parameter(f, i - 1), *copy = map[v - inl.p->symbols];
        Expr *arg = e->args[i - 1];

        e->args[i - 1] = NULL;

        if (values[v - inl.p->symbols]) {
            free_expression(arg);
            continue;
        }
        if (copy->owner == inl.caller->id && arg->kind == EX_OBJECT && copy == arg->symbol) {
            free_expression(arg);
            continue;
        }

        if (arg->kind == EX_CAST && far_pointer(copy->type) && arg->left->type.pointers &&
            !far_pointer(arg->left->type) && !object_volatile(copy->type) &&
            inl_member_statements(f->body, v)) {
            Expr *wide = arg;

            copy->type.far_pointers &= ~pointer_bit(copy->type.pointers);
            arg = wide->left;
            free(wide);
        }

        arg = inl_lower(arg, pre);
        inl_append(pre, inl_store(copy, arg, e->location));
    }

    body = inl_clone(f->body, map, values);
    free(map);

    if (snapshot) {
        Expr *value = convert(body_clone(snapshot->right), unqualified_value(snapshot->left->type));

        scalar_replace(body, snapshot->left->symbol, value);
        free_expression(value);
        scalar_refold(body);
        inl_trim_literal_guards(body);
    }

    if (mask_cost) {
        scalar_refold(body);
        inl_trim_literal_guards(body);
    }

    if (loop_trips > 0) {
        Statement *items[4];

        unsigned count = 0;

        if (reduction_statements(body, items, &count, 4) && count &&
            items[count - 1]->kind == ST_DO)
            body_expand_loop(items[count - 1], (unsigned)loop_trips);
    }

    if (loop_wrapper && !cg.parser->no_strength_reduction)
        body_terminal_xor_swaps(body);

    for (i = 0; i < e->arg_count; ++i) {
        free_expression(values[leaf_parameter(f, i) - inl.p->symbols]);
    }

    free(values);

    if (needed && (e->type.base != TY_VOID || e->type.pointers)) {
        result = inl_temp(e->type, e->location, "result");

        if (!inl_definitely_returns(body))
            inl_append(pre, inl_store(result, inl_number(0, e->location), e->location));
    }

    /* Both paths return. Put the final return on the false edge so a cloned
     * guard needs no completion flag or guarded continuation. */
    for (Statement *guard = body && body->kind == ST_BLOCK ? body->body : body; guard;
         guard = guard->next) {
        Statement *tail = guard->next;

        if (guard->kind == ST_IF && !guard->alternate && tail && tail->kind == ST_RETURN &&
            !tail->next) {
            Statement *arm = body_single(guard->body);

            if (arm && arm->kind == ST_RETURN && !arm->next) {
                guard->alternate = tail;
                guard->next = NULL;
            }
        }
    }

    if (!inl_tail_returns(body, 1)) {
        done = inl_temp(type(TY_INT, 0), e->location, "returned");
        inl_append(pre, inl_store(done, inl_number(0, e->location), e->location));
    }

    inl_returns(body, done, result);
    inl.active[f->id - 1] = 1;
    ++inl.depth;
    inl_statements(&body);
    --inl.depth;
    inl.active[f->id - 1] = 0;
    entry = inl_statement(ST_BLOCK, e->location);
    entry->body = body;
    entry->inline_callee = f->symbol;
    inl_append(pre, entry);
    {
        Expr *value = result ? inl_object(result, e->location) : inl_number(0, e->location);

        free_expression(e);
        return value;
    }
}

/* Match the existing emitter: ordinary operands and assignment destinations
 * first, call arguments right-to-left. Capture values before later work can
 * mutate their source. Aggregates stay address-valued, never scalar snapshots. */
static int inl_repeatable_predicate(Expr *e)
{
    unsigned offset;

    if (!e)
        return 1;
    if (e->type.pointers || !numeric(e->type) || e->type.base == TY_FLOAT ||
        e->type.base == TY_DOUBLE || volatile_expression(e))
        return 0;
    if (e->kind == EX_INT || e->kind == EX_OBJECT)
        return 1;
    if (e->kind == EX_DEREF)
        return fixed_memory_object(e, &offset) != NULL;
    if (e->kind != EX_CAST && e->kind != EX_UNARY && e->kind != EX_BINARY)
        return 0;

    return inl_repeatable_predicate(e->left) && inl_repeatable_predicate(e->right);
}

static Expr *inl_conditional_operand(Expr *rhs, Statement **pre, Expr *condition, int taken)
{
    rhs = inl_lower(rhs, pre);

    if (!inl.p->no_body_optimizations && body_equal(condition, rhs) &&
        inl_repeatable_predicate(rhs)) {
        Statement *s = *pre;

        while (s && s->kind == ST_BLOCK && s->inline_callee && !s->body) {
            s = s->next;
        }

        if (!s) {
            Expr *v = inl_number(taken, rhs->location);

            free_expression(rhs);
            return v;
        }
    }

    return inl_boolean(rhs);
}

static Expr *inl_lower(Expr *e, Statement **pre)
{
    unsigned i;
    Function *f;

    if (!e || !inl_has(e))
        return e;

    if (e->kind == EX_COMMA) {
        Statement *left = inl_statement(ST_EXPR, e->location);
        Expr *right = e->right;

        left->expression = inl_lower(e->left, pre);
        inl_append(pre, left);
        e->left = e->right = NULL;
        free_expression(e);
        return inl_lower(right, pre);
    }

    if ((f = inl_candidate(e, 1)))
        return inl_expand(e, f, pre, 1);

    /* Only a conditional operand that needs statements requires a join home */
    if (e->kind == EX_BINARY && (e->op == TOK_LAND || e->op == TOK_LOR) && !inl_has(e->right)) {
        e->left = inl_lower(e->left, pre);
        return e;
    }
    if (e->kind == EX_CHOOSE && !inl_has(e->right) && !inl_has(e->third)) {
        e->left = inl_lower(e->left, pre);
        return e;
    }

    if (e->kind == EX_CHOOSE || (e->kind == EX_BINARY && (e->op == TOK_LAND || e->op == TOK_LOR))) {
        int choose = e->kind == EX_CHOOSE;
        Statement *branch = inl_statement(ST_IF, e->location), *yes = NULL, *no = NULL;
        Symbol *value =
            choose && e->type.base == TY_VOID && !e->type.pointers
                ? NULL
                : inl_temp(choose ? e->type : type(TY_INT, 0), e->location, "condition");
        Expr *condition;

        condition = inl_lower(e->left, pre);
        e->left = NULL;
        branch->expression = condition;

        if (choose) {
            Expr *a = e->right, *b = e->third;

            e->right = e->third = NULL;
            a = inl_lower(a, &yes);
            b = inl_lower(b, &no);
            inl_append(&yes, inl_branch_value(value, a, e->location));
            inl_append(&no, inl_branch_value(value, b, e->location));
        } else {
            Expr *rhs = e->right, *v;

            e->right = NULL;

            if (e->op == TOK_LAND) {
                v = inl_conditional_operand(rhs, &yes, condition, 1);
                inl_append(&yes, inl_store(value, v, e->location));
                no = inl_store(value, inl_number(0, e->location), e->location);
            } else {
                yes = inl_store(value, inl_number(1, e->location), e->location);
                v = inl_conditional_operand(rhs, &no, condition, 0);
                inl_append(&no, inl_store(value, v, e->location));
            }
        }

        branch->body = yes;
        branch->alternate = no;
        inl_append(pre, branch);
        {
            Expr *result = value ? inl_object(value, e->location) : inl_number(0, e->location);

            free_expression(e);
            return result;
        }
    }

    if (e->kind == EX_CALL) {
        int literals =
            e->arg_count && !inl.p->no_body_optimizations && !inl.p->no_strength_reduction;

        for (i = e->arg_count; i; --i) {
            Expr *arg = inl_snapshot(inl_lower(e->args[i - 1], pre), pre);

            e->args[i - 1] = arg;
            literals &= arg->kind == EX_INT && numeric(arg->type);
        }

        if (e->left)
            e->left = inl_lower(e->left, pre);

        if (literals && !e->left && e->symbol && !e->symbol->noinline && !e->symbol->interrupt &&
            !e->symbol->variadic && e->arg_count == (unsigned)e->symbol->param_count &&
            (f = inl.by_symbol[e->symbol - inl.p->symbols]) && !f->uses_wide &&
            !f->jump_label_count) {
            Expr *value = inl_scalar_region(e, f, 0, NULL);

            if (value && value->kind == EX_INT) {
                ++f->symbol->inline_instances;
                free_expression(e);
                return value;
            }

            free_expression(value);
        }

        return e;
    }

    if (e->kind == EX_ASSIGN) {
        Expr *old = NULL;

        e->left = inl_lvalue(e->left, pre, e->op ? NULL : e->right);

        if (e->op)
            old = inl_snapshot(body_clone(e->left), pre);

        e->right = inl_lower(e->right, pre);

        if (old) {
            Expr *operation =
                new_expr(EX_BINARY, e->location, binary_operands(old, e->right, e->op));
            operation->op = e->op;
            operation->left = old;
            operation->right = e->right;
            e->op = 0;
            e->right = convert(operation, e->type);
        }

        return e;
    }

    if (e->kind == EX_ADDRESS || e->kind == EX_PRE || e->kind == EX_POST) {
        e->left = inl_lvalue(e->left, pre, NULL);
        return e;
    }
    if (e->kind == EX_MEMBER) {
        e = inl_lvalue(e, pre, NULL);
        return e;
    }

    if (e->left) {
        e->left = inl_lower(e->left, pre);

        /* An immediate needs no staging. Computed operands can use the
         * snapshot as a direct ALU operand instead of spilling both sides. */
        if (e->right && e->right->kind != EX_INT)
            e->left = inl_snapshot(e->left, pre);
    }

    if (e->right)
        e->right = inl_lower(e->right, pre);

    return e;
}

static Statement *inl_exit_unless(Expr *condition, Location at)
{
    Statement *test = inl_statement(ST_IF, at);

    test->expression = inl_not(condition);
    test->body = inl_statement(ST_BREAK, at);
    return test;
}

static void inl_statements(Statement **head)
{
    Statement **at = head;

    while (*at) {
        Statement *s = *at, *pre = NULL;
        int condition, step;

        inl.site = s;
        condition = inl_has(s->expression);
        step = inl_has(s->step);
        int loop = s->kind == ST_WHILE || s->kind == ST_FOR || s->kind == ST_DO;

        inl_statements(&s->initial);
        inl.loop_depth += loop;
        inl_statements(&s->body);
        inl.loop_depth -= loop;
        inl_statements(&s->alternate);

        if (s->kind == ST_WHILE && condition) {
            Expr *test = inl_lower(s->expression, &pre);

            inl_append(&pre, inl_exit_unless(test, s->location));
            inl_append(&pre, s->body);
            s->body = pre;
            s->expression = inl_number(1, s->location);
            pre = NULL;
        } else if ((s->kind == ST_FOR && step) || (s->kind == ST_DO && condition)) {
            /* Continue reaches the next test/step. First-entry state avoids
             * copying a step body into each continue or changing break scope. */
            Symbol *first = inl_temp(type(TY_INT, 0), s->location, "first");
            Statement *top = inl_statement(ST_IF, s->location), *next = NULL;

            inl_append(&pre, s->initial);
            s->initial = NULL;
            inl_append(&pre, inl_store(first, inl_number(1, s->location), s->location));
            top->expression = inl_object(first, s->location);
            top->body = inl_store(first, inl_number(0, s->location), s->location);

            if (s->kind == ST_FOR) {
                Expr *value = inl_lower(s->step, &next);
                Statement *action = inl_statement(ST_EXPR, s->location);

                action->expression = value;
                inl_append(&next, action);
                s->step = NULL;
            } else {
                Expr *test = inl_lower(s->expression, &next);

                inl_append(&next, inl_exit_unless(test, s->location));
                s->expression = NULL;
            }

            top->alternate = next;
            next = NULL;
            inl_append(&next, top);

            if (s->kind == ST_FOR && s->expression) {
                Statement *test_pre = NULL;
                Expr *test = inl_lower(s->expression, &test_pre);

                inl_append(&next, test_pre);
                inl_append(&next, inl_exit_unless(test, s->location));
            }

            inl_append(&next, s->body);
            s->kind = ST_WHILE;
            s->body = next;
            s->expression = inl_number(1, s->location);
        } else if (s->kind == ST_FOR && condition) {
            Expr *test = inl_lower(s->expression, &pre);

            inl_append(&pre, inl_exit_unless(test, s->location));
            inl_append(&pre, s->body);
            s->body = pre;
            s->expression = NULL;
            pre = NULL;
        } else if (condition) {
            Function *f;

            inl.site = s;
            f = s->kind == ST_EXPR ? inl_candidate(s->expression, 1) : NULL;
            s->expression =
                f ? inl_expand(s->expression, f, &pre, 0) : inl_lower(s->expression, &pre);
        }

        if (s->kind == ST_EXPR && s->expression && s->expression->kind == EX_INT &&
            !s->inline_callee) {
            free_expression(s->expression);
            s->expression = NULL;
            s->kind = ST_EMPTY;
        }

        if (pre) {
            Statement *block = inl_statement(ST_BLOCK, s->location);
            Statement *next = s->next;

            s->next = NULL;
            inl_append(&pre, s);
            block->body = pre;
            block->next = next;
            *at = block;
            at = &block->next;
        } else
            at = &s->next;
    }
}

static int inl_has_statements(Statement *s)
{
    for (; s; s = s->next) {
        int loop = s->kind == ST_WHILE || s->kind == ST_FOR || s->kind == ST_DO, found;

        inl.site = s;

        if (inl_has(s->expression) || inl_has(s->step) || inl_has_statements(s->alternate) ||
            inl_has_statements(s->initial))
            return 1;

        inl.loop_depth += loop;
        found = inl_has_statements(s->body);
        inl.loop_depth -= loop;

        if (found)
            return 1;
    }

    return 0;
}

static int literal_integer_tree(Expr *e)
{
    if (!e)
        return 1;
    if (!numeric(e->type) || e->type.base == TY_FLOAT || e->type.base == TY_DOUBLE ||
        volatile_expression(e))
        return 0;
    if (e->kind == EX_INT || e->kind == EX_OBJECT)
        return 1;
    if (e->kind != EX_CAST && e->kind != EX_UNARY && e->kind != EX_BINARY && e->kind != EX_CHOOSE)
        return 0;

    return literal_integer_tree(e->left) && literal_integer_tree(e->right) &&
           literal_integer_tree(e->third);
}

static int fold_literal_call(Expr *call, Function *f, int unused, int allow_stores)
{

    Expr literal_call = *call;
    Expr *value, *stores = NULL, *effect = NULL;

    unsigned i;
    int is_void = call->type.base == TY_VOID && !call->type.pointers;
    int discard = is_void || unused;

    if ((!is_void && !numeric(call->type)) ||
        !same_type(unqualified_value(call->type), unqualified_value(f->symbol->type)))
        return 0;

    for (i = 0; i < call->arg_count; ++i) {
        Expr *arg = call->args[i];

        fold_binary32_unary(arg);

        if (arg->kind == EX_BINARY || arg->kind == EX_CAST)
            scalar_refold_expr(arg);

        if (arg->kind == EX_COMMA && !effect && wide_integer_literal(arg->right)) {
            effect = arg->left;
            arg = arg->right;
        }

        unsigned offset;
        Type formal = f->symbol->params[i];
        int address = value_type(arg->type).pointers && formal.pointers && !far_pointer(formal) &&
                      !far_pointer(value_type(arg->type)) &&
                      (inl_absolute_near(arg) || near_object_address(arg, &offset));

        if ((!address &&
             (arg->kind != EX_INT || !numeric(arg->type) || arg->type.base == TY_DOUBLE)) ||
            argument_width(value_type(arg->type)) != argument_width(formal))
            return 0;

        literal_call.args[i] = arg;
    }

    value = inl_scalar_region(&literal_call, f, discard, NULL);

    if (allow_stores && (!value || value->kind != EX_INT)) {
        free_expression(value);
        value = inl_scalar_region(&literal_call, f, discard, &stores);
    }

    if (!value || value->kind != EX_INT || !numeric(value->type) || value->type.base == TY_DOUBLE) {
        free_expression(value);
        free_expression(stores);
        return 0;
    }
    if (discard)
        value = convert(value, call->type);

    if (stores) {
        Expr *sequence = new_expr(EX_COMMA, call->location, value->type);

        sequence->left = stores;
        sequence->right = value;
        value = sequence;
    }

    if (effect) {
        Expr *sequence = new_expr(EX_COMMA, call->location, value->type);

        sequence->left = body_clone(effect);
        sequence->right = value;
        value = sequence;
    }

    ++f->symbol->inline_instances;

    for (i = 0; i < call->arg_count; ++i) {
        free_expression(call->args[i]);
    }

    *call = *value;
    free(value);
    return 1;
}

static void body_fold_literal_arguments(Expr *call, int unused)
{
    Symbol *symbol = call->symbol;

    if (cg.parser->no_inline || cg.parser->no_body_optimizations ||
        cg.parser->no_strength_reduction || cg.function->symbol->interrupt || symbol->noinline ||
        symbol->always_inline || symbol->interrupt || symbol->variadic ||
        call->arg_count != (unsigned)symbol->param_count)
        return;

    Function *f = inl.by_symbol[symbol - cg.parser->symbols];

    /* Ordinary inlining can expose updates to subsequent caller analysis.
     * Save the fallback for used nullary calls until that opportunity has passed. */
    if (f && !f->jump_label_count)
        fold_literal_call(call, f, unused,
                          unused || (inl.translation_complete && !call->arg_count));
}

/* A directly preceding store provides the input of a pure no-argument
 * predicate without assuming anything about other calls or global state. */
static void body_global_predicate(Statement *s)
{
    Expr *store = s->expression, *test, *call;
    Statement *next = s->next;

    if (!next || next->kind != ST_IF || cg.parser->no_inline || cg.parser->no_known_values ||
        cg.parser->no_strength_reduction || cg.function->jump_label_count ||
        cg.function->symbol->interrupt || !store || store->kind != EX_ASSIGN || store->op ||
        store->left->kind != EX_OBJECT || store->left->symbol->owner ||
        object_volatile(store->left->type) || !word_integer(store->left->type) ||
        store->right->kind != EX_INT)
        return;

    test = next->expression;
    call = test;

    if (test->kind == EX_BINARY && comparison(test->op) && test->right->kind == EX_INT)
        call = test->left;
    if (call->kind != EX_CALL || call->left || call->arg_count || !call->symbol ||
        call->symbol->noinline || call->symbol->always_inline || call->symbol->interrupt ||
        call->symbol->variadic || !word_integer(call->type))
        return;

    Function *f = inl.by_symbol[body_symbol(call->symbol)];
    Statement *entry = f ? body_single(f->body) : NULL;

    if (!entry || entry->next || f->jump_label_count || !literal_integer_tree(entry->expression) ||
        !loop_mentions(entry->expression, store->left->symbol))
        return;
    if (entry->kind != ST_IF && entry->kind != ST_RETURN)
        return;

    Expr *replacement = body_clone(entry->expression);

    scalar_replace_expr(&replacement, store->left->symbol, store->right);
    scalar_refold_expr(replacement);

    if (entry->kind == ST_IF) {
        int taken = scalar_literal_truth(replacement);

        free_expression(replacement);
        Statement *arm = taken < 0 ? NULL : body_single(taken ? entry->body : entry->alternate);

        if (!arm || arm->kind != ST_RETURN || arm->next || !arm->expression ||
            arm->expression->kind != EX_INT)
            return;

        replacement = body_clone(arm->expression);
    }

    if (replacement->kind == EX_INT) {
        replacement = convert(replacement, unqualified_value(call->type));
        ++f->symbol->inline_instances;
        *call = *replacement;
        free(replacement);
    } else
        free_expression(replacement);
}

static int inline_wide_conversion_call(Expr *call, Function *f, Statement *body)
{
    Symbol *used = NULL;
    Expr *actual = NULL, *value, **values;

    if (body->kind != ST_RETURN || body->next || !numeric(call->type) ||
        !literal_integer_tree(body->expression) || inl_expr_cost(body->expression) > 12)
        return 0;

    for (unsigned i = 0; i < call->arg_count; ++i) {
        Symbol *formal = leaf_parameter(f, i);
        Expr *arg = call->args[i];

        if (!formal || object_volatile(formal->type))
            return 0;
        if (!expression_references(body->expression, formal)) {
            if (body_discard_effect(arg))
                return 0;

            continue;
        }
        if (used || !numeric(formal->type) ||
            !same_type(unqualified_value(arg->type), unqualified_value(formal->type)) ||
            inl_expr_cost(arg) > 3 || !literal_integer_tree(arg))
            return 0;

        used = formal;
        actual = arg;
    }

    values = allocate(1024 * sizeof *values);

    if (used)
        values[used - inl.p->symbols] = actual;

    value = convert(inl_clone_expr(body->expression, NULL, values), unqualified_value(call->type));
    free(values);

    for (unsigned i = 0; i < call->arg_count; ++i) {
        free_expression(call->args[i]);
    }

    ++f->symbol->inline_instances;
    *call = *value;
    free(value);
    return 1;
}

static int rewrite_wide_calls(Expr *e)
{
    Function *f;
    Statement *first, *yes, *no;
    Expr *test, *a, *b, *comparison;
    Symbol *parameters[2];

    unsigned i, offset;
    int folded;

    if (!e)
        return 0;

    folded = rewrite_wide_calls(e->left);
    folded |= rewrite_wide_calls(e->right);
    folded |= rewrite_wide_calls(e->third);

    for (i = 0; i < e->arg_count; ++i) {
        folded |= rewrite_wide_calls(e->args[i]);
    }

    if (e->kind != EX_CALL || !e->symbol || e->symbol->noinline || e->symbol->interrupt ||
        e->arg_count != (unsigned)e->symbol->param_count || e->symbol->variadic)
        return folded;

    f = inl.by_symbol[e->symbol - inl.p->symbols];

    if (!f || f->jump_label_count)
        return folded;

    if (!f->uses_wide) {
        /* A literal self-call can take a base case before any recursive edge.
         * Evaluate that path before computing the call graph for inlining. */
        if (f == cg.function && !e->symbol->always_inline && e->arg_count &&
            fold_literal_call(e, f, 0, 1))
            return 1;

        for (i = 0; i < e->arg_count; ++i) {
            Expr *arg = e->args[i];

            if (arg->kind == EX_COMMA ||
                (arg->kind == EX_BINARY &&
                 (arg->left->kind == EX_ASSIGN || arg->right->kind == EX_ASSIGN)))
                return fold_literal_call(e, f, 0, 1) || folded;
        }

        return folded;
    }

    if (fold_literal_call(e, f, 0, 1))
        return 1;

    first = body_single(f->body);

    if (!first || !(test = first->expression))
        return folded;
    if (inline_wide_conversion_call(e, f, first))
        return 1;
    if (e->arg_count != 2 || !word_integer(e->type))
        return folded;

    for (i = 0; i < 2; ++i) {
        a = e->args[i];
        parameters[i] = leaf_parameter(f, i);

        if (!parameters[i] || a->type.base != TY_LONGLONG || !wide_scalar(value_type(a->type)) ||
            parameters[i]->type.base != TY_LONGLONG ||
            !wide_scalar(value_type(parameters[i]->type)) || volatile_expression(a) ||
            (a->kind != EX_INT && !wide_fixed_home(a, &offset)))
            return folded;
    }

    yes = no = NULL;

    if (first->kind == ST_IF) {
        if (first->alternate && first->next)
            return folded;

        yes = body_single(first->body);
        no = body_single(first->alternate ? first->alternate : first->next);

        if (!yes || !no || yes->kind != ST_RETURN || no->kind != ST_RETURN || yes->next ||
            no->next || !yes->expression || !no->expression || yes->expression->kind != EX_INT ||
            no->expression->kind != EX_INT)
            return folded;
    } else if (first->kind != ST_RETURN || first->next || !same_type(test->type, e->type))
        return folded;

    if (!wide_compare_supported(test) || volatile_expression(test) ||
        test->left->kind != EX_OBJECT || test->right->kind != EX_OBJECT)
        return folded;

    a = test->left;
    b = test->right;

    if (a->symbol == parameters[1])
        i = 1;
    else if (a->symbol == parameters[0])
        i = 0;
    else
        return folded;

    if (b->symbol != parameters[1 - i])
        return folded;

    comparison = new_expr(EX_BINARY, e->location, test->type);
    comparison->op = test->op;
    comparison->left = convert(e->args[i], value_type(a->type));
    comparison->right = convert(e->args[1 - i], value_type(b->type));

    if (yes) {
        e->kind = EX_CHOOSE;
        e->left = comparison;
        e->right = body_clone(yes->expression);
        e->third = body_clone(no->expression);
    } else {
        *e = *comparison;
        free(comparison);
        return folded;
    }

    e->arg_count = 0;
    e->symbol = NULL;
    return folded;
}

/* A fully initialized one-field record can be assigned by its scalar field */
static int inl_fold_record_assignment(Expr *assign)
{
    if (!assign || assign->kind != EX_ASSIGN || assign->op || !structure_object(assign->type) ||
        assign->left->kind != EX_OBJECT || volatile_expression(assign))
        return 0;

    Type t = assign->type;
    Member *member = t.structure->members;

    if (t.banked || volatile_type(t) || t.structure->is_union || !member || member->next ||
        member->bit_width || member->offset || !numeric(member->type) ||
        width(member->type) != width(t))
        return 0;

    Expr *call = assign->right;

    if (call->kind != EX_CALL || call->left || !call->symbol || call->symbol->noinline ||
        call->symbol->interrupt || call->symbol->variadic ||
        call->arg_count != (unsigned)call->symbol->param_count)
        return 0;

    Function *f = inl.by_symbol[call->symbol - inl.p->symbols];
    Statement *items[2];

    unsigned count = 0, offset;

    if (!f || !f->aggregate_abi || f->uses_wide || f->jump_label_count ||
        !reduction_statements(f->body, items, &count, 2) || count != 2 ||
        items[0]->kind != ST_EXPR || items[1]->kind != ST_RETURN)
        return 0;

    Expr *store = items[0]->expression, *result = items[1]->expression;

    if (!result || result->kind != EX_ASSIGN || result->right->kind != EX_OBJECT || !store ||
        store->kind != EX_ASSIGN || store->op || store->left->kind != EX_MEMBER ||
        fixed_memory_object(store->left, &offset) != result->right->symbol || offset ||
        result->right->symbol->owner != f->id || !result->right->symbol->scope ||
        !same_type(unqualified_value(store->left->type), unqualified_value(member->type)))
        return 0;

    Expr *values[1024] = {0};

    for (unsigned i = 0; i < call->arg_count; ++i) {
        Symbol *formal = leaf_parameter(f, i);

        if (!formal || object_volatile(formal->type) || call->args[i]->kind != EX_INT ||
            !numeric(call->args[i]->type))
            return 0;

        values[formal - inl.p->symbols] = call->args[i];
    }

    int bad = 0;
    Expr *value = inl_scalar_expr(store->right, values, f, 1, 1, &bad);

    if (value && !bad)
        scalar_refold_expr(value);
    if (!value || bad || value->kind != EX_INT) {
        free_expression(value);
        return 0;
    }

    Expr *field = new_expr(EX_MEMBER, assign->location, member->type);

    field->op = '.';
    field->left = assign->left;
    ++f->symbol->inline_instances;
    free_expression(call);
    assign->left = field;
    assign->type = member->type;
    assign->right = convert(value, unqualified_value(member->type));
    return 1;
}

static int inline_wide_calls(Statement *s)
{
    int changed = 0;

    for (; s; s = s->next) {
        if (s->kind == ST_EXPR && inl_fold_record_assignment(s->expression))
            changed = 1;
        else if (rewrite_wide_calls(s->expression)) {
            scalar_refold_expr(s->expression);
            changed = 1;
        }

        if (rewrite_wide_calls(s->step)) {
            scalar_refold_expr(s->step);
            changed = 1;
        }

        changed |= inline_wide_calls(s->initial);
        changed |= inline_wide_calls(s->body);
        changed |= inline_wide_calls(s->alternate);
    }

    return changed;
}

static void inl_termination_wrappers(Statement *s)
{
    for (; s; s = s->next) {
        Expr *e = s->expression;

        if (s->kind == ST_EXPR && e && e->kind == EX_CALL && !e->left && e->symbol &&
            !e->arg_count && !e->symbol->param_count && !e->symbol->noinline &&
            !e->symbol->interrupt && same_type(e->symbol->type, type(TY_VOID, 0))) {
            Function *f = inl.by_symbol[e->symbol - inl.p->symbols];
            Statement *only = f ? body_single(f->body) : NULL;

            if (only && !only->next && only->kind == ST_EXPR &&
                body_termination_call(only->expression) &&
                (!only->expression->arg_count || only->expression->args[0]->kind == EX_INT)) {
                s->expression = body_clone(only->expression);
                ++e->symbol->inline_instances;
                free_expression(e);
            }
        }

        inl_termination_wrappers(s->initial);
        inl_termination_wrappers(s->body);
        inl_termination_wrappers(s->alternate);
    }
}

/* A jump to a terminating statement can execute it at the jump site.
 * Restrict this to functions where every label has a top-level terminator,
 * so removing their labels restores ordinary structured control flow. */
static void inl_replace_return_jumps(Statement *s, Statement **targets)
{
    for (; s; s = s->next) {
        if (s->kind == ST_GOTO) {
            Statement *target = targets[s->jump_label];

            s->kind = target->kind;
            s->expression = body_clone(target->expression);
            s->jump_label = 0;
            continue;
        }

        inl_replace_return_jumps(s->initial, targets);
        inl_replace_return_jumps(s->body, targets);
        inl_replace_return_jumps(s->alternate, targets);
    }
}

static void inl_literal_return_labels(Function *f)
{
    if (!f->jump_label_count || f->body->kind != ST_BLOCK || body_asm_statements(f->body))
        return;

    unsigned count = 0;

    for (Statement *s = f->body->body; s; s = s->next) {
        if (s->kind == ST_LABEL && s->body && !s->body->next && s->body->expression &&
            ((s->body->kind == ST_RETURN && s->body->expression->kind == EX_INT) ||
             (s->body->kind == ST_EXPR && body_termination_call(s->body->expression))))
            ++count;
    }

    if (count != f->jump_label_count)
        return;

    Statement **targets = allocate((count + 1) * sizeof *targets);

    for (Statement *s = f->body->body; s; s = s->next) {
        if (s->kind == ST_LABEL)
            targets[s->jump_label] = s->body;
    }

    inl_replace_return_jumps(f->body, targets);

    for (Statement *s = f->body->body; s; s = s->next) {
        if (s->kind == ST_LABEL) {
            s->kind = ST_BLOCK;
            s->jump_label = 0;
        }
    }

    free(targets);
    f->jump_label_count = 0;
}

static int inl_labels_without_jumps(Statement *s, int remove)
{
    for (; s; s = s->next) {
        if (s->kind == ST_GOTO)
            return 0;
        if (!inl_labels_without_jumps(s->initial, remove) ||
            !inl_labels_without_jumps(s->body, remove) ||
            !inl_labels_without_jumps(s->alternate, remove))
            return 0;

        if (remove && s->kind == ST_LABEL) {
            s->kind = ST_BLOCK;
            s->jump_label = 0;
        }
    }

    return 1;
}

/* A trailing jump to the next label can fall through enclosing blocks
 * and conditional arms. A loop or switch has its own continuation. */
static void inl_drop_fallthrough_jumps(Statement *s, unsigned following)
{
    for (; s; s = s->next) {
        Statement *next = s->next;

        while (next && next->kind == ST_EMPTY) {
            next = next->next;
        }

        unsigned label = next ? (next->kind == ST_LABEL ? next->jump_label : 0) : following;

        if (s->kind == ST_GOTO && s->jump_label == label) {
            s->kind = ST_EMPTY;
            s->jump_label = 0;
            continue;
        }

        int falls_through = s->kind == ST_BLOCK || s->kind == ST_IF || s->kind == ST_LABEL;

        inl_drop_fallthrough_jumps(s->initial, 0);
        inl_drop_fallthrough_jumps(s->body, falls_through ? label : 0);
        inl_drop_fallthrough_jumps(s->alternate, falls_through ? label : 0);
    }
}

/* Recover a pretested loop from an entry jump and a guarded backedge */
static void inl_recover_pretested_loop(Function *f)
{
    Statement *entry = body_single(f->body), *loop, *test, *guard, *back;

    if (f->jump_label_count != 2 || !entry || entry->kind != ST_GOTO)
        return;

    loop = entry->next;
    test = loop ? loop->next : NULL;

    if (!test || test->next || loop->kind != ST_LABEL || test->kind != ST_LABEL ||
        entry->jump_label != test->jump_label || !inl_labels_without_jumps(loop->body, 0))
        return;

    guard = body_single(test->body);
    back = guard ? body_single(guard->body) : NULL;

    if (!guard || guard->next || guard->kind != ST_IF || guard->alternate || !back || back->next ||
        back->kind != ST_GOTO || back->jump_label != loop->jump_label)
        return;

    entry->kind = ST_WHILE;
    entry->expression = guard->expression;
    entry->body = loop->body;
    entry->jump_label = 0;
    entry->next = NULL;
    guard->expression = NULL;
    loop->body = NULL;
    free_statements(loop);
    f->jump_label_count = 0;
}

static Expr **inl_offset_post_dereference(Expr **at, Symbol *cursor)
{
    Expr *e = *at;

    if (!e || volatile_expression(e) || e->type.pointers || !numeric(e->type) ||
        e->type.base == TY_FLOAT || e->type.base == TY_DOUBLE)
        return NULL;
    if (e->kind == EX_DEREF && e->left->kind == EX_POST && e->left->op == TOK_INC &&
        e->left->left->kind == EX_OBJECT && e->left->left->symbol == cursor)
        return &e->left;
    if (e->kind == EX_CAST)
        return inl_offset_post_dereference(&e->left, cursor);

    uint32_t amount;

    if (e->kind == EX_BINARY && (e->op == TOK_SHL || e->op == TOK_SHR) &&
        integer_constant(e->right, &amount))
        return inl_offset_post_dereference(&e->left, cursor);

    return NULL;
}

/* Read through the original private cursor and form its advanced value
 * separately. The shifted temporary is only used as a near offset. */
static int inl_forward_post_offset(Function *f, Expr *store, Statement *last)
{
    Expr *result = last->expression;
    Symbol *temp = store->left->symbol;

    if (result->kind != EX_BINARY || result->op != '+' || !result->type.pointers ||
        far_pointer(result->type) || result->left->kind != EX_OBJECT)
        return 0;

    Expr *offset = result->right;

    while (offset->kind == EX_CAST && !offset->type.pointers && numeric(offset->type) &&
           offset->type.base != TY_FLOAT && offset->type.base != TY_DOUBLE) {
        offset = offset->left;
    }

    if (offset->kind != EX_OBJECT || offset->symbol != temp)
        return 0;

    Symbol *cursor = result->left->symbol;

    if (cursor->owner != f->id || !loop_private(cursor) || object_volatile(cursor->type) ||
        !cursor->type.pointers || far_pointer(cursor->type) || !width(pointed_type(cursor->type)))
        return 0;

    Expr *value = body_clone(store->right);
    Expr **at = inl_offset_post_dereference(&value, cursor);

    if (!at) {
        free_expression(value);
        return 0;
    }

    Expr *post = *at;

    *at = post->left;
    post->left = NULL;
    free_expression(post);
    Expr *advance = new_expr(EX_BINARY, result->location, result->left->type);

    advance->op = '+';
    advance->left = result->left;
    advance->right = inl_number(1, result->location);
    result->left = advance;
    value = convert(value, unqualified_value(temp->type));
    scalar_replace_expr(&result->right, temp, value);
    free_expression(value);
    return 1;
}

/* A two-statement pure return wrapper does not need a snapshot of a
 * private temporary used just once. Preserve the assignment conversion. */
static void inl_forward_return_temporary(Function *f)
{
    Statement *items[2];

    unsigned count = 0;

    if (!reduction_statements(f->body, items, &count, 2) || count != 2 ||
        items[0]->kind != ST_EXPR || items[1]->kind != ST_RETURN)
        return;

    Statement *first = items[0], *last = items[1];
    Expr *store = first->expression, *result = last->expression;

    if (!store || store->kind != EX_ASSIGN || store->op || store->left->kind != EX_OBJECT ||
        !result)
        return;

    Symbol *v = store->left->symbol;

    if (v->owner != f->id || !v->scope || v->storage || object_volatile(v->type) ||
        expression_references(result, v) != 1 || loop_mentions(store->right, v))
        return;

    if (literal_integer_tree(store->right) && literal_integer_tree(result)) {
        Expr *value = convert(body_clone(store->right), unqualified_value(v->type));

        scalar_replace_expr(&last->expression, v, value);
        free_expression(value);
    } else if (!inl_forward_post_offset(f, store, last))
        return;

    first->kind = ST_EMPTY;
    first->expression = NULL;
    free_expression(store);
}

/* A cloned call can prove that a private loop guard is cleared on
 * every path that reaches its next test. Preserve the initial test. */
static void inl_reduce_single_pass_loops(Statement *s)
{
    for (; s; s = s->next) {
        inl_reduce_single_pass_loops(s->body);
        inl_reduce_single_pass_loops(s->alternate);
        Expr *test = s->expression;

        if (s->kind != ST_WHILE || !test || test->kind != EX_OBJECT || !known_integer(test->type) ||
            !body_private(test->symbol) || !statement_inline_markers(s->body) ||
            contains_break(s->body) || body_has_continue(s->body) || statement_has_case(s->body))
            continue;

        BodyFacts *facts = allocate(sizeof *facts);
        Statement *copy = body_clone_statements(s->body);

        body_flow(copy, facts);

        if (body_known_test(test, facts) == 0)
            s->kind = ST_IF;

        free_statements(copy);
        body_clear(facts);
        free(facts);
    }
}

/* A contiguous set of identical assignment arms can use a single
 * unsigned range test before inlining binds the selector. */
static void inl_uniform_switch(Statement *s)
{
    Expr *control = s->expression, *assignment = NULL, *fallback = NULL;
    Statement *items = s->body;

    unsigned lo = 65535, hi = 0, count = 0;

    if (!control || !word_integer(control->type) || !items || items->kind != ST_BLOCK ||
        items->next || items->inline_callee)
        return;

    for (Statement *item = items->body; item; item = item->next) {
        Statement *arm = item->body;

        if (item->kind != ST_CASE || !arm || arm->next || arm->kind != ST_EXPR || !arm->expression)
            return;
        if (item->is_default) {
            if (item->next)
                return;

            fallback = arm->expression;
            continue;
        }

        Expr *action = arm->expression;

        if (action->kind != EX_ASSIGN || action->op || action->left->kind != EX_OBJECT ||
            action->left->symbol->owner != cg.function->id || !action->left->symbol->scope ||
            volatile_expression(action) || (assignment && !body_equal(action, assignment)) ||
            !item->next || item->next->kind != ST_BREAK)
            return;

        assignment = action;
        unsigned key = item->case_value & 65535;

        if (key < lo)
            lo = key;
        if (key > hi)
            hi = key;
        if (++count > 64)
            return;

        item = item->next;
    }

    if (count < 3 || hi - lo + 1 != count)
        return;

    Type u = type(TY_INT, 0);

    u.is_unsigned = 1;
    Expr *index = convert(control, u);

    if (lo) {
        Expr *offset = new_expr(EX_BINARY, s->location, u);

        offset->op = '-';
        offset->left = index;
        offset->right = body_literal(u, lo, s->location);
        index = offset;
    }

    Expr *test = new_expr(EX_BINARY, s->location, type(TY_INT, 0));

    test->op = '<';
    test->left = index;
    test->right = body_literal(u, count, s->location);
    s->kind = ST_IF;
    s->expression = test;
    s->cases = NULL;
    s->body = inl_statement(ST_EXPR, assignment->location);
    s->body->expression = body_clone(assignment);

    if (fallback) {
        s->alternate = inl_statement(ST_EXPR, fallback->location);
        s->alternate->expression = body_clone(fallback);
    }

    free_statements(items);
}

/* An inlined output store can make the next selector literal. Recognize
 * only a straight-line prefix of direct assignments and the switch itself. */
static int inl_fold_initialized_selector(Function *f)
{
    Statement *items[12];

    unsigned count = 0;

    if (!reduction_statements(f->body, items, &count, 12))
        return 0;

    unsigned selector = 0;

    while (selector < count && items[selector]->kind != ST_SWITCH) {
        ++selector;
    }

    if (selector == count || body_asm_statements(f->body))
        return 0;

    BodyFacts *facts = allocate(sizeof *facts);
    int changed = 0;

    for (unsigned i = 0; i < count; ++i) {
        Statement *item = items[i];
        Expr *e = item->expression;

        if (item->kind == ST_SWITCH) {
            Expr *control = body_clone(e);

            body_replace(&control, facts, 0);

            if (control->kind == EX_INT) {
                item->expression = control;
                body_fold_constant_switch(item);

                if (item->kind == ST_BLOCK) {
                    free_expression(e);
                    changed = 1;
                    break;
                }

                item->expression = e;
            }

            free_expression(control);
            break;
        }

        if (item->kind != ST_EXPR || !e || e->kind != EX_ASSIGN || e->op || body_effect(e->left) ||
            body_effect(e->right) || volatile_expression(e))
            break;

        Expr *store = body_clone(e);

        body_replace(&store->left, facts, 1);

        if (store->left->kind != EX_OBJECT || !body_fact_home(store->left->symbol)) {
            free_expression(store);
            break;
        }

        body_expr(&store, facts, 1);
        free_expression(store);
    }

    body_clear(facts);
    free(facts);
    return changed;
}

/* Dead local tables should not make a private, once-called leaf look
 * expensive to clone. A discarded table may expose another dead home. */
static void inl_prepare_local_tables(Function *f)
{
    if (!f->symbol->internal || f->symbol->address_taken || f->symbol->noinline ||
        f->symbol->interrupt || inl.calls[f->id - 1] != 1 || f->slots < 24 || f->jump_label_count ||
        f->uses_wide || f->aggregate_abi || f->uses_bitfields)
        return;

    for (unsigned i = 0; i < inl.p->symbol_count; ++i) {
        Symbol *s = &inl.p->symbols[i];

        if (s->owner != f->id || !s->offset || !s->scope ||
            !(s->type.array || structure_object(s->type)) || width(s->type) < 16)
            continue;

        cg.function = f;
        unsigned slots = f->slots;
        body_drop_unused_homes(f);

        if (f->slots < slots) {
            body_drop_unused_homes(f);
            scalar_propagate(f);
            body_optimize(f);
        }

        return;
    }
}

static void inline_translation_unit(Parser *p)
{
    Function *f;

    unsigned i, j, k, n = p->function_count;
    unsigned char *reach;

    memset(&inl, 0, sizeof inl);
    inl.p = p;

    for (f = p->functions; f; f = f->next) {
        inl.by_symbol[f->symbol - p->symbols] = f;
    }

    if (!p->no_inline && !p->no_strength_reduction && !p->no_body_optimizations)
        for (f = p->functions; f; f = f->next) {
            if (!f->symbol->interrupt && !body_asm_statements(f->body)) {
                inl_termination_wrappers(f->body);

                if (!f->jump_label_count)
                    continue;

                body_simplify_branches(f->body, f->symbol->type);
                inl_drop_fallthrough_jumps(f->body, 0);
                inl_recover_pretested_loop(f);
                inl_literal_return_labels(f);

                if (f->jump_label_count && inl_labels_without_jumps(f->body, 0)) {
                    inl_labels_without_jumps(f->body, 1);
                    f->jump_label_count = 0;
                }

                if (!f->jump_label_count && !statement_has_case(f->body))
                    body_trim_after_exit(f->body);
            }
        }

    if (!p->no_body_optimizations && !p->no_strength_reduction)
        for (f = p->functions; f; f = f->next) {
            if (!f->jump_label_count && !body_asm_statements(f->body)) {
                body_fold_constant_switches(f->body);

                if (!p->no_inline && !f->symbol->interrupt) {
                    cg.function = f;

                    for (Statement *s = body_single(f->body); s; s = s->next) {
                        if (s->kind == ST_SWITCH)
                            inl_uniform_switch(s);
                    }
                }

                if (!p->no_inline && !f->symbol->interrupt)
                    inl_forward_return_temporary(f);

                if (!p->no_inline && f->uses_bitfields && !f->uses_wide && !f->symbol->interrupt &&
                    inl_fixed_field_body(f->body, 0) && !volatile_statements(f->body)) {
                    BodyFacts *facts = allocate(sizeof *facts);

                    cg.function = f;
                    body_narrow_far_locals(f);
                    body_flow(f->body, facts);
                    body_clear(facts);
                    free(facts);
                }
            }
        }

    if (!p->no_inline && !p->no_body_optimizations)
        for (f = p->functions; f; f = f->next) {
            int has_call = 0;

            if (!p->no_strength_reduction && !f->symbol->interrupt && !f->jump_label_count &&
                f->body->kind == ST_BLOCK && inl_inert_wrapper(f->body, &has_call) && has_call) {
                free_statements(f->body->body);
                f->body->body = NULL;
            }

            if (f->symbol->param_count > 0)
                inl_drop_final_updates(f);

            inl_guard_final_call(f);
            inl_join_guarded_return(f);
        }

    if (!p->no_inline && !p->no_body_optimizations && !p->no_strength_reduction)
        for (f = p->functions; f; f = f->next) {
            if (!f->symbol->interrupt) {
                cg.function = f;

                if (inline_wide_calls(f->body) && f->uses_wide)
                    f->uses_wide = function_uses_wide(f);
            }
        }

    reach = allocate(n * n ? n * n : 1);

    for (f = p->functions; f; f = f->next) {
        inl_edges(f->body, reach, f->id - 1, n);
    }

    for (k = 0; k < n; ++k) {
        for (i = 0; i < n; ++i) {
            if (reach[i * n + k])
                for (j = 0; j < n; ++j) {
                    reach[i * n + j] |= reach[k * n + j];
                }
        }
    }

    for (i = 0; i < n; ++i) {
        inl.recursive[i] = reach[i * n + i];
    }

    free(reach);

    if (!p->no_inline && !p->no_body_optimizations && !p->no_strength_reduction)
        for (f = p->functions; f; f = f->next) {
            inl_prepare_local_tables(f);
        }

    /* Estimate a called fixed-trip loop after the existing bounded
     * transformations have had a chance to reduce it to fixed stores. */
    if (!p->no_inline && !p->no_body_optimizations && !p->no_strength_reduction &&
        !p->no_loop_unroll)

        for (f = p->functions; f; f = f->next) {
            Statement *items[2], *loop, *guarded;

            unsigned count = 0;
            uint32_t bound;

            if (!inl.calls[f->id - 1] || f->symbol->noinline || f->symbol->interrupt ||
                f->uses_wide || f->aggregate_abi || f->jump_label_count ||
                !reduction_statements(f->body, items, &count, 2) || !count ||
                body_asm_statements(f->body))
                continue;

            guarded = items[count - 1];

            if (guarded->kind == ST_IF && !guarded->alternate)
                guarded = body_single(guarded->body);

            if (!f->symbol->param_count && guarded && guarded->kind == ST_DO && !guarded->next &&
                guarded->expression && guarded->expression->kind == EX_BINARY &&
                integer_constant(guarded->expression->right, &bound) &&
                bound <= FIXED_STORE_TRIPS) {
                cg.function = f;
                scalar_propagate(f);
                body_optimize(f);
                continue;
            }

            if (count != 1)
                continue;

            loop = items[0];

            if (loop->kind != ST_FOR || !loop->expression)
                continue;

            if (!f->symbol->param_count && loop->expression->kind == EX_BINARY) {
                if (!integer_constant(loop->expression->right, &bound) || bound > FIXED_INDEX_TRIPS)
                    continue;
            } else {
                Statement *initial = body_single(loop->initial);
                Expr *set = initial ? initial->expression : NULL, *test = loop->expression;

                if (f->symbol->param_count != 1 || !f->symbol->params[0].pointers || loop->step ||
                    test->kind != EX_PRE || test->op != TOK_DEC || !initial || initial->next ||
                    initial->kind != ST_EXPR || !set || set->kind != EX_ASSIGN || set->op ||
                    set->left->kind != EX_OBJECT || !body_equal(set->left, test->left) ||
                    !integer_constant(set->right, &bound) || !bound ||
                    bound > FIXED_INDEX_TRIPS + 1)
                    continue;
            }

            cg.function = f;
            scalar_propagate(f);
            body_optimize(f);
        }

    for (f = p->functions; f; f = f->next) {
        inl.caller = f;
        inl.growth = 0;
        inl.specialized_growth = 0;
        cg.function = f;

        if (f->jump_label_count || f->uses_wide)
            continue;
        if (!inl_has_statements(f->body))
            continue;

        /* Expose existing structured facts before introducing call bindings.
         * --no-inline leaves the previous pipeline byte-for-byte available. */
        if (!p->no_inline && !f->aggregate_abi) {
            scalar_propagate(f);
            body_optimize(f);
        }

        inl_statements(&f->body);

        if (!p->no_body_optimizations && !p->no_strength_reduction && !p->no_known_values &&
            (inl.growth || inl.specialized_growth) && !f->aggregate_abi &&
            inl_fold_initialized_selector(f)) {
            scalar_propagate(f);
            body_optimize(f);
        }

        if (!p->no_body_optimizations && !p->no_strength_reduction && !p->no_loop_unroll &&
            !p->no_known_values && inl.growth && !body_asm_statements(f->body))
            inl_reduce_single_pass_loops(f->body);

        if (!p->no_inline && !f->aggregate_abi && inl.specialized_growth) {
            body_optimize(f);
            inl_statements(&f->body);
        }

        f->frame = f->slots ? f->slots + 4 : 0;
    }

    /* Keep callees of every body that will be emitted, including ordinary
     * static functions retained independently of inlining. */
    {
        unsigned char *alive = allocate(n ? n : 1);
        int changed = 1;

        reach = allocate(n * n ? n * n : 1);

        for (i = 0; i < p->symbol_count; ++i) {
            Relocation *r;

            for (r = p->symbols[i].relocations; r; r = r->next) {
                if (r->symbol) {
                    Function *rf = inl.by_symbol[r->symbol - p->symbols];

                    if (rf)
                        alive[rf->id - 1] = 1;
                }
            }
        }

        for (f = p->functions; f; f = f->next) {
            inl_edges(f->body, reach, f->id - 1, n);
            Symbol *s = f->symbol;

            if ((!s->internal && (!s->inline_hint || s->inline_external)) || s->interrupt ||
                (s->internal && (s->address_taken || (!s->inline_instances && !s->inline_hint))))
                alive[f->id - 1] = 1;
        }

        while (changed) {
            changed = 0;

            for (i = 0; i < n; ++i) {
                if (alive[i])
                    for (j = 0; j < n; ++j) {
                        if (reach[i * n + j] && !alive[j]) {
                            alive[j] = 1;
                            changed = 1;
                        }
                    }
            }
        }

        for (f = p->functions; f; f = f->next) {
            f->symbol->inline_omit = f->symbol->internal && !f->symbol->address_taken &&
                                     (f->symbol->inline_instances || f->symbol->inline_hint) &&
                                     !alive[f->id - 1];
        }

        free(reach);
        free(alive);
    }
    inl.translation_complete = 1;
}
