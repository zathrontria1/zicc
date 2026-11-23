/* Extend private-home analysis into functions with volatile regions, without
 * changing the older passes' whole-function guards. Unknown memory effects
 * remain local barriers. Y provenance includes saved values across CFG joins. */
enum { PR_NONE, PR_WORK, PR_FRAME, PR_OTHER, PR_FENCE, PR_BARRIER };

static int pr_join(PrState *to, const PrState *from)
{
    PrState old = *to;

    unsigned i;

    if (!to->seen)
        *to = *from;
    else {
        to->frame &= from->frame;

        if (to->count > from->count)
            to->count = from->count;

        for (i = 0; i < to->count; ++i) {
            to->stack[i] &= from->stack[i];
        }
    }

    return memcmp(&old, to, sizeof old) != 0;
}

static void pr_push(PrState *s, unsigned bytes, int frame)
{
    unsigned i;

    if (s->count + bytes > 64)
        s->count = (unsigned char)(64 - bytes);

    memmove(s->stack + bytes, s->stack, s->count);

    for (i = 0; i < bytes; ++i) {
        s->stack[i] = (unsigned char)frame;
    }

    s->count += (unsigned char)bytes;
}

static void pr_pop(PrState *s, unsigned bytes)
{
    if (bytes > s->count)
        s->count = 0;
    else {
        s->count -= (unsigned char)bytes;
        memmove(s->stack, s->stack + bytes, s->count);
    }
}

static PrState *pr_states(LpUnit *u)
{
    PrState *states = calloc(u->count, sizeof *states);

    unsigned i;
    int entry = -1, again = 1;

    if (!states) {
        fputs("out of memory\n", stderr);
        exit(EXIT_FAILURE);
    }

    /* Only the ordinary leading frame prologue establishes the frame value.
     * Other TAYs, including retained counters and aggregate cursors, do not. */
    for (i = 0; i < u->count; ++i) {
        LpLine *l = &u->lines[i];
        int p;

        if (!l->op)
            continue;
        if (lp_branch(l) || l->call || l->ends)
            break;
        if (lp_is(l, "tay")) {
            p = lp_next(u, i, -1);

            if (p >= 0 && (lp_is(&u->lines[p], "tsc") || lp_is(&u->lines[p], "tcs")))
                entry = (int)i;

            break;
        }
    }

    states[0].seen = 1;

    while (again) {
        again = 0;

        for (i = 0; i < u->count; ++i) {
            LpLine *l = &u->lines[i];
            PrState s = states[i];
            int bytes;

            if (!s.seen)
                continue;

            if (l->op) {
                if ((int)i == entry) {
                    s.frame = 1;
                    s.count = 0;
                } else if (lp_is(l, "ply")) {
                    s.frame = !l->x8 && s.count >= 2 && s.stack[0] && s.stack[1];
                    pr_pop(&s, l->x8 ? 1 : 2);
                } else if (lp_is(l, "mvn") || lp_is(l, "mvp"))
                    s.frame = 0; /* The move leaves the saved stack entries in place */
                else {
                    if (lp_is(l, "phy"))
                        pr_push(&s, l->x8 ? 1 : 2, s.frame && !l->x8);
                    else {
                        bytes = assembly_stack_bytes(l->op, l->m8, l->x8);

                        if (bytes > 0)
                            pr_push(&s, (unsigned)bytes, 0);
                        else if (bytes < 0)
                            pr_pop(&s, (unsigned)-bytes);
                        else if (lp_is(l, "tcs") || lp_is(l, "txs"))
                            s.count = 0;
                    }

                    if ((l->def & LP_Y) || lp_is(l, "ldy") || lp_is(l, "tay") || lp_is(l, "txy") ||
                        lp_is(l, "iny") || lp_is(l, "dey") ||
                        (lp_is(l, "sep") && (lp_immediate(l) & 16)) || lp_is(l, "plp"))
                        s.frame = 0;

                    if (l->use == LP_ALL && !lp_is(l, "rep") && !lp_is(l, "sep")) {
                        s.frame = 0;
                        s.count = 0;
                    }
                }
            }

            if ((!l->op || !l->ends) && i + 1 < u->count)
                again |= pr_join(&states[i + 1], &s);
            if (l->target >= 0)
                again |= pr_join(&states[l->target], &s);
        }
    }

    return states;
}

static int pr_volatile(Type t)
{
    Member *m;

    if (object_volatile(t))
        return 1;

    if (!t.pointers && t.structure)
        for (m = t.structure->members; m; m = m->next) {
            if (pr_volatile(m->type))
                return 1;
        }

    return 0;
}

static int pr_named(const char *p, size_t n)
{
    size_t start = 0, k;

    unsigned i;

    if (n > 11 && !strncmp(p, "a:.loword(_", 11))
        start = 11;
    else if (n > 3 && (!strncmp(p, "a:_", 3) || !strncmp(p, "f:_", 3) || !strncmp(p, "z:_", 3)))
        start = 3;
    else
        return 0;

    for (k = start; k < n && (isalnum((unsigned char)p[k]) || p[k] == '_'); ++k) {
    }

    if (k == start)
        return 0;

    for (i = 0; i < lp_state.parser->symbol_count; ++i) {
        Symbol *v = &lp_state.parser->symbols[i];

        if (!v->owner && !v->function && strlen(v->asm_name) == k - start &&
            !strncmp(v->asm_name, p + start, k - start))
            return !pr_volatile(v->type);
    }

    return 0;
}

static int pr_memory(LpLine *l, PrState *s, Function *f, int *offset)
{
    size_t n;
    const char *p = lp_operand(l, &n);
    int w, width = lp_width(l), j;

    *offset = -1;
    if (l->call)
        return PR_BARRIER;
    if (l->use == LP_ALL && !lp_is(l, "rep") && !lp_is(l, "sep"))
        return PR_BARRIER;
    if (!lp_is(l, "lda") && !lp_is(l, "ldx") && !lp_is(l, "ldy") && !lp_store_op(l) &&
        !lp_is(l, "adc") && !lp_is(l, "sbc") && !lp_is(l, "cmp") && !lp_is(l, "cpx") &&
        !lp_is(l, "cpy") && !lp_is(l, "and") && !lp_is(l, "ora") && !lp_is(l, "eor") &&
        !lp_is(l, "bit") && !lp_is(l, "pei"))
        return PR_NONE;
    if (!n || p[0] == '#' || (n == 1 && p[0] == 'a'))
        return PR_NONE;

    w = lp_workspace_word(p, n);

    if (w >= 0 && w + width <= 32) {
        *offset = w;
        return PR_WORK;
    }

    if (n == 9 && !strncmp(p, "a:$", 3) && p[7] == ',' && p[8] == 'y' && s->seen && s->frame &&
        !l->x8) {
        w = (int)strtoul(p + 3, NULL, 16);

        if (w > 0 && w + width - 1 <= (int)f->slots) {
            for (j = 0; j < width; ++j) {
                if (!pv_frame_private(f, (unsigned)((w + j - 1) / 2 * 2 + 1), 0))
                    return PR_BARRIER;
            }

            *offset = w;
            return PR_FRAME;
        }
    }

    /* A fixed peripheral address cannot alias an unescaped stack object.
     * Keep it as a forwarding/workspace fence, preserving every MMIO access. */
    if (n == 9 && !strncmp(p, "f:$", 3)) {
        unsigned address = (unsigned)strtoul(p + 3, NULL, 16), bank = address >> 16,
                 low = address & 65535;

        if ((bank <= 63 || (bank >= 128 && bank <= 191)) && low >= 0x2100 &&
            low + (unsigned)width <= 0x4400)
            return PR_FENCE;
    }

    return pr_named(p, n) ? PR_OTHER : PR_BARRIER;
}

static void pr_key(int kind, int offset, char *key)
{
    if (kind == PR_WORK)
        snprintf(key, 128, "z:__arith_lhs+%d", offset);
    else
        snprintf(key, 128, "a:$%04X,y", offset);
}

static int pr_enabled(LpUnit *u)
{
    return !lp_state.parser->no_private_regions && !lp_state.parser->no_body_optimizations &&
           lp_state.is_volatile && !u->indirect;
}

static int lp_region_private_copies(LpUnit *u, Function *f, size_t at)
{
    struct {
        char key[128], value[128];
        int bytes;
    } copies[64];

    char a[128] = "";

    unsigned count = 0, i, j;
    int bytes = 0, changed = 0;
    PrState *states;

    (void)at;

    if (!pr_enabled(u)) {
        return 0;
    }

    states = pr_states(u);
    lp_liveness(u);

    for (i = 0; i < u->count; ++i) {
        LpLine *l = &u->lines[i];
        int offset, kind;
        char key[128];

        if (!l->op) {
            if (l->label) {
                count = 0;
                a[0] = 0;
                bytes = 0;
            }

            continue;
        }

        kind = pr_memory(l, &states[i], f, &offset);

        if (kind == PR_BARRIER || kind == PR_FENCE) {
            count = 0;
            a[0] = 0;
            bytes = 0;
            continue;
        }

        if (kind == PR_WORK || kind == PR_FRAME)
            pr_key(kind, offset, key);
        else
            key[0] = 0;

        if (lp_store_op(l) && kind != PR_NONE) {
            if (!key[0])
                continue; /* A named nonvolatile object cannot alias these homes */

            for (j = 0; j < count;) {
                if (pv_overlap(copies[j].key, key) || pv_overlap(copies[j].value, key))
                    copies[j] = copies[--count];
                else
                    ++j;
            }

            if (a[0] && pv_overlap(a, key) && strcmp(a, key)) {
                a[0] = 0;
                bytes = 0;
            }

            if (lp_is(l, "sta")) {
                if (a[0] && bytes >= lp_width(l) && strcmp(a, key) && count < 64) {
                    strcpy(copies[count].key, key);
                    strcpy(copies[count].value, a);
                    copies[count++].bytes = lp_width(l);
                }

                if (!a[0]) {
                    strcpy(a, key);
                    bytes = lp_width(l);
                }
            } else if (a[0] && pv_overlap(a, key)) {
                a[0] = 0;
                bytes = 0;
            }

            continue;
        }

        if (lp_is(l, "lda") && key[0]) {
            int need = lp_width(l);

            for (j = 0; j < count; ++j) {
                if (!strcmp(copies[j].key, key) && copies[j].bytes >= need) {
                    lp_set(l, "    lda %s", copies[j].value);
                    strcpy(key, copies[j].value);
                    ++changed;
                    break;
                }
            }

            if (a[0] && !strcmp(a, key) && bytes >= need && !(l->out & (LP_N | LP_Z))) {
                l->deleted = 1;
                ++changed;
            }

            strcpy(a, key);
            bytes = need;
            continue;
        }

        if (l->def & LP_Y || lp_is(l, "ply") || lp_is(l, "ldy") || lp_is(l, "tay") ||
            lp_is(l, "txy") || lp_is(l, "iny") || lp_is(l, "dey") ||
            (lp_is(l, "sep") && (lp_immediate(l) & 16))) {
            for (j = 0; j < count;) {
                if (copies[j].key[0] == 'a' || copies[j].value[0] == 'a')
                    copies[j] = copies[--count];
                else
                    ++j;
            }

            if (a[0] == 'a') {
                a[0] = 0;
                bytes = 0;
            }
        }

        if (l->def & LP_A || lp_is(l, "lda") || lp_is(l, "pla") || lp_is(l, "txa") ||
            lp_is(l, "tya") || lp_is(l, "xba") || lp_is(l, "adc") || lp_is(l, "sbc") ||
            lp_is(l, "and") || lp_is(l, "ora") || lp_is(l, "eor") || lp_is(l, "asl") ||
            lp_is(l, "lsr") || lp_is(l, "rol") || lp_is(l, "ror") || lp_is(l, "inc") ||
            lp_is(l, "dec")) {
            a[0] = 0;
            bytes = 0;
        }

        if (lp_branch(l) || l->ends) {
            count = 0;
            a[0] = 0;
            bytes = 0;
        }
    }

    free(states);
    return changed;
}

static int lp_region_dead_stores(LpUnit *u, Function *f, size_t at)
{
    PrState *states;

    unsigned word, i;
    unsigned char *use, *def, *live, *out;
    int changed = 0, *kind, *offset;

    (void)at;

    if (!pr_enabled(u)) {
        return 0;
    }

    states = pr_states(u);
    kind = calloc(u->count * 2, sizeof *kind);
    use = calloc(u->count * 4, 1);

    if (!kind || !use) {
        fputs("out of memory\n", stderr);
        exit(EXIT_FAILURE);
    }

    offset = kind + u->count;
    def = use + u->count;
    live = def + u->count;
    out = live + u->count;

    for (i = 0; i < u->count; ++i) {
        if (u->lines[i].op)
            kind[i] = pr_memory(&u->lines[i], &states[i], f, &offset[i]);
    }

    for (word = 0; word < 16 + (f->slots + 1) / 2; ++word) {
        int frame = word >= 16, base = frame ? (int)(word - 16) * 2 + 1 : (int)word * 2, again = 1;

        if (frame && !pv_frame_private(f, (unsigned)base, 0))
            continue;

        memset(use, 0, u->count * 4);

        for (i = 0; i < u->count; ++i) {
            LpLine *l = &u->lines[i];

            unsigned mask = 0, writes;
            int j, result;

            if (!l->op)
                continue;

            if (l->call) {
                if (!frame) {
                    if (pv_math(l, &writes, &result)) {
                        use[i] = (word == 0 || word == 2) ? 3 : 0;
                        def[i] = (writes & (1u << word)) ? 3 : 0;
                    } else
                        use[i] = 3;
                }

                continue; /* Unescaped private C homes are not callee inputs */
            }

            if (kind[i] == PR_BARRIER) {
                use[i] = 3;
                continue;
            }
            if (kind[i] == PR_FENCE) {
                if (!frame)
                    use[i] = 3;

                continue;
            }
            if (kind[i] != (frame ? PR_FRAME : PR_WORK))
                continue;

            for (j = 0; j < lp_width(l); ++j) {
                if (offset[i] + j >= base && offset[i] + j < base + 2)
                    mask |= 1u << (offset[i] + j - base);
            }

            if (lp_is(l, "sta") || lp_is(l, "stx") || lp_is(l, "sty") || lp_is(l, "stz"))
                def[i] = (unsigned char)mask;
            else {
                use[i] = (unsigned char)mask;

                if (lp_store_op(l))
                    def[i] = (unsigned char)mask;
            }
        }

        while (again) {
            again = 0;

            for (i = u->count; i-- > 0;) {
                LpLine *l = &u->lines[i];

                unsigned o = 0, v;

                if (!l->op || !l->ends)
                    o = i + 1 < u->count ? live[i + 1] : 0;

                if (l->target >= 0) {
                    o |= live[l->target];
                }

                v = use[i] | (o & ~def[i]);

                if (v != live[i] || o != out[i]) {
                    live[i] = (unsigned char)v;
                    out[i] = (unsigned char)o;
                    again = 1;
                }
            }
        }

        for (i = 0; i < u->count; ++i) {
            if (def[i] && !use[i] && !(def[i] & out[i]) && !u->lines[i].call &&
                (lp_width(&u->lines[i]) == 1 || def[i] == 3) && !u->lines[i].deleted) {
                u->lines[i].deleted = 1;
                ++changed;
            }
        }
    }

    free(states);
    free(kind);
    free(use);
    return changed;
}

typedef struct {
    int low, store_low, store_high, load, last;
    int offset, indexed;
} FarFrameLoad;

static int far_frame_word(LpLine *l, Function *f, PrState *frame)
{
    size_t n;
    const char *p = lp_operand(l, &n);

    unsigned offset, i, b;

    if (!frame->seen || !frame->frame || n != 9 || strncmp(p, "a:$", 3) || strncmp(p + 7, ",y", 2))
        return -1;

    offset = (unsigned)strtoul(p + 3, NULL, 16);

    if (!offset || offset + 1 > f->frame)
        return -1;

    for (i = 0; i < lp_state.parser->symbol_count; ++i) {
        Symbol *s = &lp_state.parser->symbols[i];

        if (s->owner != f->id || !s->offset)
            continue;

        for (b = 0; b < width(s->type); ++b) {
            unsigned byte = frame_offset(s->offset + b);

            if (byte >= offset && byte <= offset + 1 && (!loop_private(s) || pr_volatile(s->type)))
                return -1;
        }
    }

    return (int)offset;
}

/* Normalize incoming stack arguments to their entry offsets. Temporary pushes
 * move S but cannot overwrite arguments above the return address. */
static int far_frame_source(LpUnit *u, Function *f, PrState *frames, const int *depth, int i)
{
    size_t n, j;
    const char *p = lp_operand(&u->lines[i], &n);
    int offset = far_frame_word(&u->lines[i], f, &frames[i]);

    if (offset >= 0 || !depth || depth[i] < 0 || n < 3 || n > 5 || p[n - 2] != ',' ||
        p[n - 1] != 's')
        return offset;

    for (j = 0; j < n - 2; ++j) {
        if (!isdigit((unsigned char)p[j]))
            return -1;
    }

    offset = (int)strtol(p, NULL, 10) - depth[i];
    return offset > 2 + lp_state.parser->long_return && offset <= 255 ? (int)f->frame + offset : -1;
}

/* Recognize the complete word load so the staging registers and the old
 * workspace pointer are unobserved at the boundary of the replacement. */
static int far_frame_load(LpUnit *u, Function *f, PrState *frames, const int *depth, unsigned i,
                          FarFrameLoad *result)
{
    LpLine *line = &u->lines[i];
    int high, low, k, load, last, saved_y = 0, indexed = 0;

    if (line->m8 || line->x8 || (!lp_is(line, "lda") && !lp_is(line, "ldx")))
        return 0;

    k = lp_next(u, i, 1);

    if (lp_is(line, "lda") && k >= 0 && lp_line_is(&u->lines[k], "tax"))
        k = lp_next(u, (unsigned)k, 1);
    else if (!lp_is(line, "ldx"))
        return 0;

    if (k < 0 || !lp_is(&u->lines[k], "lda") || u->lines[k].m8)
        return 0;

    result->low = k;
    k = lp_next(u, (unsigned)k, 1);

    if (k < 0 || !lp_line_is(&u->lines[k], "sta z:__arith_lhs"))
        return 0;

    result->store_low = k;
    k = lp_next(u, (unsigned)k, 1);

    if (k < 0 || !lp_line_is(&u->lines[k], "stx z:__arith_lhs+2"))
        return 0;

    result->store_high = k;
    k = lp_next(u, (unsigned)k, 1);

    if (k >= 0 && lp_line_is(&u->lines[k], "phy")) {
        saved_y = 1;
        k = lp_next(u, (unsigned)k, 1);
    }

    if (k >= 0 && lp_is(&u->lines[k], "ldy") && !u->lines[k].x8 &&
        lp_immediate(&u->lines[k]) >= 0) {
        k = lp_next(u, (unsigned)k, 1);
        indexed = 1;
    }

    if (saved_y && !indexed)
        return 0;
    if (k < 0 || !lp_line_is(&u->lines[k], indexed ? "lda [__arith_lhs],y" : "lda [__arith_lhs]") ||
        u->lines[k].m8)
        return 0;

    load = k;
    last = saved_y ? lp_next(u, (unsigned)load, 1) : load;

    if (last < 0 || (saved_y && !lp_line_is(&u->lines[last], "ply")) || u->lines[last].out & LP_X)
        return 0;

    high = far_frame_source(u, f, frames, depth, (int)i);
    low = far_frame_source(u, f, frames, depth, result->low);

    if (low < 0 || high != low + 2 || (low <= (int)f->frame && high > (int)f->frame))
        return 0;

    result->load = load;
    result->last = last;
    result->offset = low;
    result->indexed = indexed;
    return 1;
}

/* Liveness of the four bytes in the ordinary far-address workspace.
 * An indirect operand observes the pointer, even when it writes its target. */
static unsigned char *far_workspace_live(LpUnit *u)
{
    unsigned i;
    int changed = 1;
    unsigned char *live = allocate(u->count * 3), *uses = live + u->count, *defs = uses + u->count;

    for (i = 0; i < u->count; ++i) {
        LpLine *l = &u->lines[i];
        size_t n;
        const char *p = lp_operand(l, &n);
        int word = lp_workspace_word(p, n);

        if (l->call && lp_register_call(l))
            defs[i] = 15;
        else if (l->call || (l->op && l->use == LP_ALL && !lp_is(l, "rep") && !lp_is(l, "sep")))
            uses[i] = 15;
        else if (word >= 0 && word < 4) {
            unsigned mask = (((1u << lp_width(l)) - 1u) << (unsigned)word) & 15;

            if (lp_is(l, "sta") || lp_is(l, "stx") || lp_is(l, "sty") || lp_is(l, "stz"))
                defs[i] = (unsigned char)mask;
            else
                uses[i] = (unsigned char)mask;
        } else if (n && (lp_text_words(p, p + n) & 3))
            uses[i] = 15;
    }

    while (changed) {
        changed = 0;

        for (i = u->count; i-- > 0;) {
            LpLine *l = &u->lines[i];

            unsigned out = i + 1 < u->count && (!l->op || !l->ends) ? live[i + 1] : 0;
            unsigned now;

            if (l->target >= 0)
                out |= live[l->target];

            now = uses[i] | (out & ~defs[i]);

            if (now != live[i]) {
                live[i] = (unsigned char)now;
                changed = 1;
            }
        }
    }

    return live;
}

static int far_frame_meet(signed char *to, int from)
{
    int prior = *to;

    if (prior < 0 || from < prior)
        *to = (signed char)from;

    return prior != *to;
}

/* Reuse a staged far frame pointer across branches. Calls invalidate the
 * cache, as do writes overlapping its source. Uncached paths still stage
 * the pointer into the reserved DP pair before dereferencing it. */
static int lp_far_frame_cache(LpUnit *u, Function *f, size_t at)
{
    FarFrameLoad *loads;
    PrState *frames;
    unsigned char *live;
    signed char *state;

    unsigned i, j, slot, used, best = 0, *counts;
    const char *stage;
    int *depth = NULL, offset = 0, again = 1, changed = 0;

    (void)at;

    if (u->indirect || lp_state.parser->no_dp_homes || lp_state.parser->no_private_regions ||
        !u->count)
        return 0;

    stage = strstr(u->text, "    stx z:__arith_lhs+2\n");

    if (!stage || !strstr(stage + 1, "    stx z:__arith_lhs+2\n"))
        return 0;

    for (i = 0; i < u->count; ++i) {
        if (lp_branch(&u->lines[i]) && u->lines[i].target < 0)
            return 0;
    }

    used = lp_text_words(u->text, u->text + strlen(u->text));

    for (slot = 0; slot < 15 && used & (3u << slot); ++slot) {
    }

    if (slot == 15)
        return 0;

    if (!lp_state.is_volatile && strcmp(f->symbol->name, "main")) {
        depth = allocate(u->count * sizeof *depth);

        if (!lp_stack_depths(u, 0, depth)) {
            free(depth);
            depth = NULL;
        }
    }

    loads = allocate(u->count * sizeof *loads);
    counts = allocate((f->frame + 256) * sizeof *counts);
    frames = pr_states(u);
    lp_liveness(u);
    live = far_workspace_live(u);

    for (i = 0; i < u->count; ++i) {
        FarFrameLoad load = {0};

        if (!far_frame_load(u, f, frames, depth, i, &load) || (unsigned)load.last + 1 >= u->count ||
            live[load.last + 1])
            continue;

        loads[i] = load;

        if (++counts[load.offset] > best) {
            best = counts[load.offset];
            offset = load.offset;
        }
    }

    free(live);
    free(counts);

    if (best < 2)
        goto done;

    state = allocate(u->count);
    memset(state, -1, u->count);
    state[0] = 0;

    while (again) {
        again = 0;

        for (i = 0; i < u->count; ++i) {
            LpLine *l = &u->lines[i];
            int here = state[i], address, kind;

            if (here < 0)
                continue;
            if (loads[i].offset == offset)
                here = 1;

            if (l->op) {
                kind = pr_memory(l, &frames[i], f, &address);

                if (l->call || lp_is(l, "tcd") || lp_is(l, "pld") ||
                    (l->use == LP_ALL && !lp_is(l, "rep") && !lp_is(l, "sep")) ||
                    (lp_store_op(l) &&
                     (kind == PR_BARRIER || (offset > (int)f->frame && kind != PR_WORK) ||
                      (kind == PR_FRAME && address < offset + 4 &&
                       address + lp_width(l) > offset))))
                    here = 0;
            }

            if ((!l->op || !l->ends) && i + 1 < u->count)
                again |= far_frame_meet(&state[i + 1], here);
            if (l->target >= 0)
                again |= far_frame_meet(&state[l->target], here);
        }
    }

    for (i = 0; i < u->count; ++i) {
        if (loads[i].offset == offset && state[i] > 0) {
            changed = 1;
            break;
        }
    }

    if (changed)
        for (i = 0; i < u->count; ++i) {
            FarFrameLoad *load = &loads[i];

            if (load->offset != offset || state[i] < 0)
                continue;

            if (state[i]) {
                for (j = i; j <= (unsigned)load->store_high; ++j) {
                    if (u->lines[j].op)
                        u->lines[j].deleted = 1;
                }
            } else {
                lp_set(&u->lines[load->store_low], "    sta z:__arith_lhs+%u", 2 * slot);
                lp_set(&u->lines[load->store_high], "    stx z:__arith_lhs+%u", 2 * slot + 2);
            }

            lp_set(&u->lines[load->load], "    lda [__arith_lhs+%u]%s", 2 * slot,
                   load->indexed ? ",y" : "");
        }

    free(state);
done:
    free(loads);
    free(frames);
    free(depth);
    return changed;
}
