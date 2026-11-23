/* Physical stack-slot coloring, leaving logical symbol offsets unchanged.
 * All CFG/DP/induction analyses continue to see distinct C homes. Addressed,
 * volatile, aggregate, parameter and hidden cursor storage stays pinned. */
typedef struct {
    Symbol *symbols[64];
    unsigned short offsets[64];
    unsigned count, budget;
    uint64_t edges[64];
    int failed;
} FramePacking;

static uint64_t frame_refs(FramePacking *p, Expr *e)
{
    uint64_t refs = 0;

    unsigned i;
    DotProduct *dp;

    if (!e)
        return 0;

    if ((dp = dot_match_expr(e)) != NULL) {
        unsigned k;

        for (i = 0; i < p->count; ++i) {
            if (p->symbols[i] == dp->bias_sym)
                refs |= UINT64_C(1) << i;

            for (k = 0; k < dp->term_count; ++k) {
                if (p->symbols[i] == dp->terms[k].pack_sym)
                    refs |= UINT64_C(1) << i;
            }
        }

        for (k = 0; k < dp->term_count; ++k) {
            refs |= frame_refs(p, dp->terms[k].value_expr);
        }

        return refs;
    }

    if (e->kind == EX_OBJECT)
        for (i = 0; i < p->count; ++i) {
            if (e->symbol == p->symbols[i])
                refs |= UINT64_C(1) << i;
        }

    refs |= frame_refs(p, e->left) | frame_refs(p, e->right) | frame_refs(p, e->third);

    for (i = 0; i < e->arg_count; ++i) {
        refs |= frame_refs(p, e->args[i]);
    }

    return refs;
}

static void frame_interference(FramePacking *p, uint64_t live)
{
    unsigned i;

    for (i = 0; i < p->count; ++i) {
        if (live & (UINT64_C(1) << i))
            p->edges[i] |= live & ~(UINT64_C(1) << i);
    }
}

static uint64_t frame_live_expr(FramePacking *p, Expr *e, uint64_t after)
{
    uint64_t before, definition = 0;

    unsigned i;

    if (!e)
        return after;

    if (e->kind == EX_ASSIGN && !e->op && e->left->kind == EX_OBJECT) {
        for (i = 0; i < p->count; ++i) {
            if (e->left->symbol == p->symbols[i])
                definition |= UINT64_C(1) << i;
        }
    }

    frame_interference(p, after | definition);
    before = (after & ~definition) | frame_refs(p, definition ? e->right : e);
    frame_interference(p, before);
    return before;
}

static uint64_t frame_live(FramePacking *p, Statement *s, uint64_t after, uint64_t breaking,
                           uint64_t continuing);
static uint64_t frame_live_one(FramePacking *p, Statement *s, uint64_t next, uint64_t breaking,
                               uint64_t continuing);

static uint64_t frame_live_switch(FramePacking *p, Statement *s, uint64_t after, uint64_t breaking,
                                  uint64_t continuing, uint64_t *entries, int *has_default)
{
    uint64_t next;

    if (!s)
        return after;
    if (!p->budget) {
        p->failed = 1;
        return UINT64_MAX;
    }

    --p->budget;
    next = frame_live_switch(p, s->next, after, breaking, continuing, entries, has_default);
    frame_interference(p, next);

    if (s->kind == ST_CASE) {
        Statement *leaf = s;
        uint64_t live;

        while (leaf && leaf->kind == ST_CASE) {
            if (leaf->is_default)
                *has_default = 1;

            leaf = leaf->body;
        }

        live =
            leaf && leaf->kind == ST_BLOCK && !leaf->inline_callee
                ? frame_live_switch(p, leaf->body, next, breaking, continuing, entries, has_default)
                : frame_live(p, leaf, next, breaking, continuing);
        frame_interference(p, live);
        *entries |= live;
        return live;
    }

    if (s->kind == ST_BLOCK && !s->inline_callee)
        return frame_live_switch(p, s->body, next, breaking, continuing, entries, has_default);

    return frame_live_one(p, s, next, breaking, continuing);
}

static uint64_t frame_live_one(FramePacking *p, Statement *s, uint64_t next, uint64_t breaking,
                               uint64_t continuing)
{
    uint64_t head, body, step, again;

    switch (s->kind) {
    case ST_EMPTY:
        return next;
    case ST_EXPR:
        return frame_live_expr(p, s->expression, next);
    case ST_RETURN:
        return frame_live_expr(p, s->expression, 0);
    case ST_BREAK:
        return breaking;
    case ST_CONTINUE:
        return continuing;
    case ST_BLOCK:
        return frame_live(p, s->body, next, breaking, continuing);
    case ST_IF:
        body = frame_live(p, s->body, next, breaking, continuing);
        step = frame_live(p, s->alternate, next, breaking, continuing);
        return frame_live_expr(p, s->expression, body | step);
    case ST_SWITCH:
        if (!known_structured_switch(s->body)) {
            p->failed = 1;
            return UINT64_MAX;
        }

        {
            uint64_t entries = 0, fall;
            int has_default = 0;
            Statement *first = s->body;

            fall = frame_live_switch(p, first, next, next, continuing, &entries, &has_default);

            if (!has_default)
                entries |= next;
            if (first && first->kind == ST_BLOCK && !first->inline_callee)
                first = first->body;
            if (first && first->kind != ST_CASE)
                entries |= fall;

            frame_interference(p, entries);
            return frame_live_expr(p, s->expression, entries);
        }
    case ST_FOR:
    case ST_WHILE:
    case ST_DO:
        head = 0;

        do {
            again = head;

            if (s->kind == ST_DO) {
                step = frame_live_expr(p, s->expression, next | head);
                head = frame_live(p, s->body, step, next, step);
            } else {
                step = frame_live_expr(p, s->step, head);
                body = frame_live(p, s->body, step, next, step);
                head = frame_live_expr(p, s->expression, next | body);
            }
        } while (head != again && !p->failed);

        head = frame_live(p, s->initial, head, breaking, continuing);
        {
            uint64_t setup_kill = 0, setup_gen = 0;

            unsigned d, k, idx;

            for (d = 0; d < dot_state.count; ++d) {
                if (dot_state.dots[d].loop == s)
                    for (idx = 0; idx < p->count; ++idx) {
                        if (p->symbols[idx] == dot_state.dots[d].bias_sym)
                            setup_kill |= UINT64_C(1) << idx;
                    }
            }

            for (k = 0; k < dot_state.pack_count; ++k) {
                if (dot_state.packs[k].loop == s) {
                    for (idx = 0; idx < p->count; ++idx) {
                        if (p->symbols[idx] == dot_state.packs[k].pack_sym)
                            setup_kill |= UINT64_C(1) << idx;
                        if (p->symbols[idx] == dot_state.packs[k].coeff_sym)
                            setup_gen |= UINT64_C(1) << idx;
                    }
                }
            }

            if (setup_kill || setup_gen) {
                /* Setup writes packs and biases between reads of coefficients */
                frame_interference(p, head | setup_kill | setup_gen);
                head = (head & ~setup_kill) | setup_gen;
                frame_interference(p, head);
            }
        }
        return head;
    default:
        p->failed = 1;
        return UINT64_MAX;
    }
}

static uint64_t frame_live(FramePacking *p, Statement *s, uint64_t after, uint64_t breaking,
                           uint64_t continuing)
{
    uint64_t next;

    if (!s)
        return after;
    if (!p->budget) {
        p->failed = 1;
        return UINT64_MAX;
    }

    --p->budget;
    next = frame_live(p, s->next, after, breaking, continuing);
    frame_interference(p, next);
    return frame_live_one(p, s, next, breaking, continuing);
}

static void pack_private_frame(Function *f)
{
    FramePacking p = {0};

    unsigned i, j, k, colors[64], palette[64], used[384], words = (f->slots + 1) / 2, high = 0;

    if (cg.parser->no_private_regions || cg.parser->no_body_optimizations ||
        cg.parser->no_stack_frames || f->symbol->interrupt || reg_width(f->symbol->type) > 2 ||
        words > 384 || statement_has_case(f->body))
        return;

    for (i = 0; i < cg.parser->symbol_count; ++i) {
        Symbol *v = &cg.parser->symbols[i];

        unsigned slots;

        if ((!v->scope && words <= 14) || v->owner != f->id || !v->offset || v->offset > f->slots ||
            !loop_private(v) || object_volatile(v->type) || structure_object(v->type) ||
            v->type.array)
            continue;

        slots = width(v->type);

        if (slots != 1 && slots != 2 &&
            !(words > 14 && slots == 4 && v->type.base == TY_LONG && !v->type.pointers))
            continue;

        for (j = 0; j < cg.cursor_count; ++j) {
            if (cg.cursors[j].base == v || cg.cursors[j].index == v)
                break;
        }

        if (j < cg.cursor_count)
            continue;

        {
            unsigned need = slots == 4 ? 2 : 1, w;

            if (p.count + need > 64)
                return;

            for (w = 0; w < need; ++w) {
                unsigned short off = (unsigned short)(v->offset + w * 2);

                for (j = p.count; j && p.offsets[j - 1] > off; --j) {
                    p.symbols[j] = p.symbols[j - 1];
                    p.offsets[j] = p.offsets[j - 1];
                }

                p.symbols[j] = v;
                p.offsets[j] = off;
                ++p.count;
            }
        }
    }

    if (p.count < 2)
        return;

    p.budget = 100000;
    {
        uint64_t entry = frame_live(&p, f->body, 0, 0, 0);

        for (i = 0; i < p.count; ++i) {
            if (!p.symbols[i]->scope)
                entry |= UINT64_C(1) << i;
        }

        frame_interference(&p, entry);
    }

    if (p.failed)
        return;

    for (i = 0; i < words; ++i) {
        used[i] = 1;
    }

    for (i = 0; i < p.count; ++i) {
        palette[i] = p.offsets[i];
        used[(palette[i] - 1) / 2] = 0;
    }

    for (i = 0; i < p.count; ++i) {
        if (width(p.symbols[i]->type) == 4 && i + 1 < p.count && p.symbols[i + 1] == p.symbols[i]) {
            uint64_t both = p.edges[i] | p.edges[i + 1];

            for (j = 0; j + 1 < i; ++j) {
                if (palette[j + 1] != palette[j] + 2)
                    continue;

                for (k = 0; k < i; ++k) {
                    if ((colors[k] == j || colors[k] == j + 1) && (both & (UINT64_C(1) << k)))
                        break;
                }

                if (k == i)
                    break;
            }

            if (j + 1 >= i) {
                colors[i] = i;
                colors[i + 1] = i + 1;
            } else {
                colors[i] = j;
                colors[i + 1] = j + 1;
            }

            cg.frame_map[(p.offsets[i] - 1) / 2] = (unsigned short)palette[colors[i]];
            cg.frame_map[(p.offsets[i + 1] - 1) / 2] = (unsigned short)palette[colors[i + 1]];
            used[(palette[colors[i]] - 1) / 2] = 1;
            used[(palette[colors[i + 1]] - 1) / 2] = 1;
            ++i;
            continue;
        }

        if (!p.symbols[i]->scope || width(p.symbols[i]->type) > 2) {
            j = i;
        } else
            for (j = 0; j < i; ++j) {
                for (k = 0; k < i; ++k) {
                    if (colors[k] == j && (p.edges[i] & (UINT64_C(1) << k)))
                        break;
                }

                if (k == i)
                    break;
            }

        colors[i] = j;
        cg.frame_map[(p.offsets[i] - 1) / 2] = (unsigned short)palette[j];
        used[(palette[j] - 1) / 2] = 1;
    }

    for (i = 0; i < words; ++i) {
        if (used[i])
            high = i + 1;
    }

    cg.frame_saved = f->slots - high * 2;

    if (cg.frame_saved)
        code("; packed private frame: %u -> %u bytes\n", f->slots, high * 2);
}
