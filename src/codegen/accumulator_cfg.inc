/* Must-availability of a full word in A or X, independent of N/Z provenance.
 * A memory key denotes equality with the memory at the current index bindings;
 * every index change, possible write and unmodelled effect invalidates it. */
typedef struct {
    char text[128];
    unsigned indices;
    int memory;
} AcKey;

typedef struct {
    int seen, key, nz;
} AcState;

static int ac_key(AcKey *keys, unsigned *count, const char *text, unsigned indices, int memory)
{
    unsigned i;

    for (i = 1; i <= *count; ++i)
        if (!strcmp(keys[i].text, text) && keys[i].indices == indices && keys[i].memory == memory)
            return (int)i;
    ++*count;
    snprintf(keys[*count].text, sizeof keys[*count].text, "%s", text);
    keys[*count].indices = indices;
    keys[*count].memory = memory;
    return (int)*count;
}

static int ac_join(AcState *to, AcState from)
{
    AcState old = *to;
    if (!to->seen)
        *to = from;
    else {
        if (to->key != from.key)
            to->key = 0;
        to->nz &= from.nz;
    }
    return old.seen != to->seen || old.key != to->key || old.nz != to->nz;
}

static int lp_cfg_register(LpUnit *u, Function *f, int index)
{
    AcState *states;
    AcKey *keys;
    PrState *frames;
    int *ids, *kinds, again = 1, changed = 0;
    unsigned i, count = 0;
    const char *load = index ? "ldx" : "lda", *store = index ? "stx" : "sta";
    unsigned reg = index ? LP_X : LP_A;
    if (!u->count || u->indirect || lp_state.parser->no_body_optimizations ||
        lp_state.parser->no_value_reuse || lp_state.parser->no_private_regions)
        return 0;
    states = calloc(u->count, sizeof *states);
    keys = calloc(u->count + 1, sizeof *keys);
    ids = calloc(u->count * 2, sizeof *ids);
    if (!states || !keys || !ids) {
        fputs("out of memory\n", stderr);
        exit(EXIT_FAILURE);
    }
    kinds = ids + u->count;
    frames = pr_states(u);
    lp_liveness(u);
    states[0].seen = 1;

    for (i = 0; i < u->count; ++i) {
        LpLine *l = &u->lines[i];
        char text[128];
        int offset;
        long immediate;
        size_t n;
        const char *p;

        /* Exported labels may be entered without executing their predecessor */
        if (l->label && l->length != 1 && strncmp(l->text, "cg_", 3) &&
            strncmp(l->text, "return_", 7))
            states[i].seen = 1;
        if (!l->op)
            continue;
        kinds[i] = pr_memory(l, &frames[i], f, &offset);
        p = lp_operand(l, &n);
        if ((lp_is(l, load) || lp_is(l, store) || (!index && lp_is(l, "ldx")) ||
             (index && (lp_is(l, "sta") || lp_is(l, "lda")) && !l->m8)) &&
            (index || !l->m8) && !l->x8) {
            if (lp_is(l, load) && (immediate = lp_immediate(l)) >= 0) {
                snprintf(text, sizeof text, "#$%04lX", immediate & 65535);
                ids[i] = ac_key(keys, &count, text, 0, 0);
            } else if (kinds[i] == PR_WORK || kinds[i] == PR_FRAME) {
                pr_key(kinds[i], offset, text);
                ids[i] = ac_key(keys, &count, text, kinds[i] == PR_FRAME ? LP_Y : 0, 1);
            } else if (kinds[i] == PR_OTHER && n < sizeof text) {
                memcpy(text, p, n);
                text[n] = 0;
                ids[i] = ac_key(keys, &count, text, lp_index_use(l), 1);
            }
        }
    }

    while (again) {
        again = 0;
        for (i = 0; i < u->count; ++i) {
            LpLine *l = &u->lines[i];
            AcState s = states[i];
            if (!s.seen)
                continue;
            if (l->op) {
                if (index && (lp_line_is(l, "sep #$20") ||
                              lp_line_is(l, "rep #$20"))) { /* X and its flags survive */
                } else if (l->call || l->use == LP_ALL || (!index && l->m8) || l->x8 ||
                           lp_is(l, "tcd") ||
                           ((kinds[i] == PR_BARRIER || kinds[i] == PR_FENCE) &&
                            (!index || lp_store_op(l))))
                    s.key = s.nz = 0;
                else {
                    if (s.key &&
                        ((keys[s.key].indices & l->def) || (keys[s.key].memory && lp_stack_op(l))))
                        s.key = 0;
                    if (lp_is(l, load)) {
                        s.key = ids[i];
                        s.nz = 1;
                    } else {
                        if (lp_store_op(l) && kinds[i] != PR_NONE) {
                            if (s.key && keys[s.key].memory) {
                                const char *key = keys[s.key].text;
                                if (!index || !lp_private(key, strlen(key)) ||
                                    lp_may_write(l, key, strlen(key), 2))
                                    s.key = 0;
                            }
                            if (lp_is(l, store))
                                s.key = ids[i];
                            if (index && lp_is(l, "sta") && ids[i]) {
                                int previous = lp_next(u, i, -1);
                                if (previous >= 0 && lp_line_is(&u->lines[previous], "txa") &&
                                    !u->lines[previous].m8)
                                    s.key = ids[i];
                            }
                        }
                        if ((l->def & reg) || (!index && lp_is(l, "xba"))) {
                            s.key = 0;
                            s.nz = (l->def & (reg | LP_N | LP_Z)) == (reg | LP_N | LP_Z);
                        } else if ((lp_is(l, index ? "cpx" : "cmp") && lp_immediate(l) == 0) ||
                                   lp_line_is(l, index ? "cpx #0" : "cmp #0") ||
                                   (index ? (lp_is(l, "txa") && !l->m8)
                                          : lp_is(l, "tax") || lp_is(l, "tay")))
                            s.nz = 1;
                        else if (l->def & (LP_N | LP_Z))
                            s.nz = 0;
                        if (index && lp_is(l, "tax") && !l->m8) {
                            int previous = lp_next(u, i, -1);
                            if (previous >= 0 && lp_line_is(&u->lines[previous], "txa") &&
                                !u->lines[previous].m8)
                                s.key = states[previous].key;
                            else if (previous >= 0 && lp_is(&u->lines[previous], "sta") &&
                                     ids[previous] && !(keys[ids[previous]].indices & LP_X))
                                s.key = ids[previous];
                        }
                    }
                }
            }
            if ((!l->op || !l->ends) && i + 1 < u->count)
                again |= ac_join(&states[i + 1], s);
            if (l->target >= 0)
                again |= ac_join(&states[l->target], s);
        }
    }

    for (i = 0; i < u->count; ++i) {
        LpLine *l = &u->lines[i];
        if (lp_is(l, index ? "lda" : "ldx") && !l->m8 && !l->x8 && ids[i] && states[i].seen &&
            states[i].key == ids[i] && (kinds[i] == PR_WORK || kinds[i] == PR_FRAME)) {
            lp_set(l, index ? "    txa" : "    tax");
            changed = 1;
            break;
        }
        if (lp_is(l, load) && ids[i] && states[i].seen && states[i].key == ids[i] &&
            (!(l->out & (LP_N | LP_Z)) || states[i].nz)) {
            /* Reanalyse after each deletion: removing a flags-dead load must
             * not lend its now-missing N/Z definition to another deletion. */
            l->deleted = 1;
            changed = 1;
            break;
        }
    }
    free(frames);
    free(states);
    free(keys);
    free(ids);
    return changed;
}

static int lp_cfg_accumulator(LpUnit *u, Function *f, size_t at)
{
    (void)at;
    return lp_cfg_register(u, f, 0);
}

static int lp_cfg_index(LpUnit *u, Function *f, size_t at)
{
    (void)at;
    return lp_cfg_register(u, f, 1);
}
