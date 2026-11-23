/* Index elimination after strength reduction (Phase C, linear-function test
 * replacement). A C index j whose every cursor already tracks base+s*j needs
 * no home of its own when its value is never observed except by "j > 0" or
 * "j != 0" tests. Those become cursor tests: with 0 <= j <= 32767 and s <= 2,
 * s*j mod 65536 is zero only for j == 0, so "cursor != base" is exact without
 * any pointer-validity assumption.
 *
 * j >= 0 is established syntactically. Every write to j must be one of:
 *   - "j = k" for a constant k >= 0, or "j = i" inside a for loop over i that
 *     starts at a constant >= 0, only increments by one, is bounded by
 *     "i < x" or "i <= x" and is written nowhere else (so 0 <= i <= 32767);
 *   - "--j" / "j--" / "j -= 1" as a statement directly in a while/for loop
 *     whose condition's leading conjunct is "j > 0" or "j != 0", at most once
 *     in that loop and outside any nested loop.
 * Any other observation of j is detected while emitting (its home is
 * touched) and the function is emitted again with j kept. */
static int lftr_object(Expr *e, Symbol *v)
{
    return e && e->kind == EX_OBJECT && e->symbol == v;
}

static int lftr_constant(Expr *e, int *value)
{
    while (e && e->kind == EX_CAST && value_width(e->type) == 2 &&
           value_width(e->left->type) == 2) {
        e = e->left;
    }

    if (!e || e->kind != EX_INT || e->type.base == TY_FLOAT || e->type.pointers)
        return 0;

    *value = (int)(int16_t)(e->value & 0xFFFF);
    return 1;
}

static unsigned lftr_writes_expr(Expr *e, Symbol *v)
{
    unsigned n = 0, i;

    if (!e)
        return 0;
    if ((e->kind == EX_ASSIGN || e->kind == EX_PRE || e->kind == EX_POST) &&
        lftr_object(e->left, v))
        ++n;

    n += lftr_writes_expr(e->left, v) + lftr_writes_expr(e->right, v) +
         lftr_writes_expr(e->third, v);

    for (i = 0; i < e->arg_count; ++i) {
        n += lftr_writes_expr(e->args[i], v);
    }

    return n;
}

static unsigned lftr_writes(Statement *s, Symbol *v)
{
    unsigned n = 0;

    for (; s; s = s->next) {
        n += lftr_writes_expr(s->expression, v) + lftr_writes_expr(s->step, v) +
             lftr_writes(s->initial, v) + lftr_writes(s->body, v) + lftr_writes(s->alternate, v);
    }

    return n;
}

static int lftr_unit_step(Expr *e, Symbol *v, int increment)
{
    int k;

    if (!e || !lftr_object(e->left, v))
        return 0;
    if (e->kind == EX_PRE || e->kind == EX_POST)
        return e->op == (increment ? TOK_INC : TOK_DEC);

    return e->kind == EX_ASSIGN && e->op == (increment ? '+' : '-') &&
           lftr_constant(e->right, &k) && k == 1;
}

/* "j > 0" or "j != 0": the tests lftr_branch rewrites */
static int lftr_positive_test(Expr *e, Symbol *v)
{
    int k;

    return e && e->kind == EX_BINARY && (e->op == '>' || e->op == TOK_NE) &&
           lftr_object(e->left, v) && lftr_constant(e->right, &k) && !k;
}

static int lftr_guarded(Expr *e, Symbol *v)
{
    if (lftr_positive_test(e, v))
        return 1;

    return e && e->kind == EX_BINARY && e->op == TOK_LAND && lftr_guarded(e->left, v);
}

/* i is a for loop index confined to 0..32767 inside the loop's body */
static int lftr_nonnegative_for(Function *f, Statement *loop, Symbol *i)
{
    Statement *init;
    int k, found = 0;
    Expr *c = loop->expression;

    if (loop->kind != ST_FOR || !lftr_unit_step(loop->step, i, 1) || !c || c->kind != EX_BINARY ||
        (c->op != '<' && c->op != TOK_LE) || !lftr_object(c->left, i) || i->type.base != TY_INT ||
        i->type.pointers || i->type.is_unsigned || width(i->type) != 2)
        return 0;

    for (init = loop->initial; init; init = init->next) {
        if (init->kind == ST_EXPR && init->expression && init->expression->kind == EX_ASSIGN &&
            !init->expression->op && lftr_object(init->expression->left, i) &&
            lftr_constant(init->expression->right, &k) && k >= 0)
            found = 1;
    }

    return found && lftr_writes(f->body, i) == 2;
}

typedef struct {
    Statement *loops[64];
    unsigned depth;
    Statement *decrement_loop[64];
    unsigned decrements;
    unsigned allowed;
    int bad;
} LftrWalk;

static void lftr_walk(Function *f, Statement *s, Symbol *j, LftrWalk *w)
{
    for (; s; s = s->next) {
        Expr *e = s->kind == ST_EXPR ? s->expression : NULL;

        if (e && e->kind == EX_ASSIGN && !e->op && lftr_object(e->left, j)) {
            int k;

            unsigned i, c;

            if (lftr_constant(e->right, &k) && k >= 0)
                ++w->allowed;
            else if (e->right->kind == EX_OBJECT) {
                Symbol *source = e->right->symbol;
                int ok = 0;

                for (i = 0; i < w->depth; ++i) {
                    if (lftr_nonnegative_for(f, w->loops[i], source))
                        ok = 1;
                }

                (void)c;

                if (ok)
                    ++w->allowed;
                else
                    w->bad = 1;
            } else
                w->bad = 1;
        } else if (e && lftr_unit_step(e, j, 0)) {
            Statement *loop = w->depth ? w->loops[w->depth - 1] : NULL;

            unsigned i;

            if (!loop || (loop->kind != ST_WHILE && loop->kind != ST_FOR) ||
                !lftr_guarded(loop->expression, j) ||
                lftr_writes(loop->body, j) + lftr_writes_expr(loop->step, j) +
                        lftr_writes_expr(loop->expression, j) !=
                    1)
                w->bad = 1;

            for (i = 0; i < w->decrements; ++i) {
                if (w->decrement_loop[i] == loop)
                    w->bad = 1;
            }

            if (w->decrements < 64)
                w->decrement_loop[w->decrements++] = loop;
            else
                w->bad = 1;

            ++w->allowed;
        }

        if (s->kind == ST_WHILE || s->kind == ST_FOR || s->kind == ST_DO) {
            lftr_walk(f, s->initial, j, w);

            if (w->depth == 64) {
                w->bad = 1;
                return;
            }

            w->loops[w->depth++] = s;

            if (s->kind == ST_FOR && lftr_unit_step(s->step, j, 0)) {
                unsigned i;

                if (!lftr_guarded(s->expression, j) ||
                    lftr_writes(s->body, j) + lftr_writes_expr(s->expression, j))
                    w->bad = 1;

                for (i = 0; i < w->decrements; ++i) {
                    if (w->decrement_loop[i] == s)
                        w->bad = 1;
                }

                if (w->decrements < 64)
                    w->decrement_loop[w->decrements++] = s;
                else
                    w->bad = 1;

                ++w->allowed;
            }

            lftr_walk(f, s->body, j, w);
            --w->depth;
        } else {
            lftr_walk(f, s->initial, j, w);
            lftr_walk(f, s->body, j, w);
            lftr_walk(f, s->alternate, j, w);
        }
    }
}

/* A for loop's own step that decrements j is legal only for that loop; one in
 * its body is counted separately above, so a loop has at most one. */
static void lftr_prepare(Function *f)
{
    unsigned i, k;

    lftr_state.count = 0;
    lftr_state.active = lftr_state.failed = 0;

    if (cg.parser->no_index_elimination || cg.parser->no_strength_reduction ||
        volatile_statements(f->body))
        return;

    for (i = 0; i < cg.cursor_count && lftr_state.count < 8; ++i) {
        Symbol *j = cg.cursors[i].index;
        LftrWalk w;
        int ok = 1;

        for (k = 0; k < lftr_state.count; ++k) {
            if (lftr_state.indices[k] == j)
                ok = 0;
        }

        if (!ok || j->owner != f->id || !j->scope || object_volatile(j->type) ||
            j->type.base != TY_INT || j->type.pointers || j->type.is_unsigned ||
            width(j->type) != 2)
            continue;

        for (k = 0; k < cg.cursor_count; ++k) {
            if (cg.cursors[k].index == j) {
                Symbol *base = cg.cursors[k].base;

                if (cg.cursors[k].scale > 2 || (base->type.array && base->owner) ||
                    base->type.banked)
                    ok = 0;
            }
        }

        if (!ok)
            continue;

        memset(&w, 0, sizeof w);
        lftr_walk(f, f->body, j, &w);

        if (!w.bad && w.allowed == lftr_writes(f->body, j) && w.decrements)
            lftr_state.indices[lftr_state.count++] = j;
    }
}

static int lftr_dead(Symbol *v)
{
    unsigned i;

    if (!lftr_state.active)
        return 0;

    for (i = 0; i < lftr_state.count; ++i) {
        if (lftr_state.indices[i] == v)
            return 1;
    }

    return 0;
}

/* "j > 0" / "j != 0" for an eliminated j: compare its first cursor with the
 * cursor's base. A bound cursor is read from X, which holds cursor+delta. */
static int lftr_branch(Expr *e, unsigned yes, unsigned no, unsigned fallthrough)
{
    unsigned i;

    InductionCursor *c = NULL;
    Symbol *base;

    if (!lftr_state.active || e->kind != EX_BINARY || !e->left || e->left->kind != EX_OBJECT ||
        !lftr_dead(e->left->symbol) || !lftr_positive_test(e, e->left->symbol))
        return 0;

    for (i = 0; i < cg.cursor_count && !c; ++i) {
        if (cg.cursors[i].index == e->left->symbol)
            c = &cg.cursors[i];
    }

    if (!c)
        return 0;

    base = c->base;
    base->used = 1;
    code("; eliminated index %s: %s > 0 as cursor %s[%s] != %s\n", e->left->symbol->name,
         e->left->symbol->name, base->name, c->index->name, base->name);

    if (c == bound_state.cursor)
        code("    txa\n");
    else
        code("    lda %s\n", frame_operand(c->offset));

    code("    sec\n");

    if (base->type.array)
        code("    sbc #.loword(_%s)\n", base->asm_name);
    else if (base->owner)
        code("    sbc %s\n", frame_operand(base->offset));
    else
        code("    sbc %s:_%s\n", base->dpage ? "z" : "a", base->asm_name);

    if (c == bound_state.cursor && bound_state.delta)
        code("    cmp #$%04X\n", bound_state.delta);

    flag_branch("bne", "beq", yes, no, fallthrough);
    return 1;
}
