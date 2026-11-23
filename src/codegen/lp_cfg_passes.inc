// Control-flow and register-value line passes: Y promotion, branches, and AX reuse

/* Y as a loop register: in a function that leaves Y alone, the most used
 * in-loop workspace word moves to Y, saved at entry and restored at exits.
 * Y survives every call, so the word may live across them. */
static int lp_y_promote(LpUnit *u, Function *f, size_t at)
{
    unsigned i, word, best = 0, best_score = 0, *depth, first = 0;
    int entry = -1, *sd;
    (void)at;

    if (u->helpers || u->indirect || f->symbol->interrupt)
        return 0;

    for (i = 0; i < u->count; ++i) {
        LpLine *l = &u->lines[i];
        if (!l->op)
            continue;
        if (entry < 0)
            entry = (int)i;
        if (l->x8)
            return 0;
        if ((lp_index_use(l) & LP_Y) ||
            ((l->use & LP_Y) && !l->ends && !l->call && l->use != LP_ALL)) {
            return 0;
        }
        if (l->def & LP_Y || lp_is(l, "phy") || lp_is(l, "ply") || lp_is(l, "tsx") ||
            lp_is(l, "txs") || lp_is(l, "mvn") || lp_is(l, "mvp"))
            return 0;
        if (lp_is(l, "jml") || lp_is(l, "rti"))
            return 0;
        if (l->use == LP_ALL && !lp_is(l, "rep") && !lp_is(l, "sep"))
            return 0;
        if ((lp_is(l, "rep") || lp_is(l, "sep")) && strtoul(l->op + 6, NULL, 16) & 0x10)
            return 0;
        if (lp_is(l, "tsc")) {
            /* Allow frame allocation "tsc / sec / sbc #n / tcs" and cleanup "tsc / clc / adc #n / tcs" */
            int a = lp_next(u, i, 1), b = a >= 0 ? lp_next(u, (unsigned)a, 1) : -1,
                c = b >= 0 ? lp_next(u, (unsigned)b, 1) : -1;
            if (c < 0 || !lp_line_is(&u->lines[c], "tcs"))
                return 0;
            if (!((lp_line_is(&u->lines[a], "clc") && !strncmp(u->lines[b].op, "adc #", 5)) ||
                  (lp_line_is(&u->lines[a], "sec") && !strncmp(u->lines[b].op, "sbc #", 5))))
                return 0;
        } else if (lp_is(l, "tcs")) {
            int b = lp_next(u, i, -1);
            if (b < 0 ||
                (strncmp(u->lines[b].op, "adc #", 5) && strncmp(u->lines[b].op, "sbc #", 5)))
                return 0;
        }
        if (l->target >= 0) {
            unsigned t = (unsigned)l->target;
            while (t < u->count && !u->lines[t].op)
                ++t;
            if (entry >= 0 && t <= (unsigned)entry)
                return 0;
        }
        {
            size_t m;
            const char *p = lp_operand(l, &m);
            if (m >= 2 && p[m - 2] == ',' && p[m - 1] == 's' && strtoul(p, NULL, 10) + 2 > 255)
                return 0;
        }
    }
    if (entry < 0)
        return 0;
    first = (unsigned)entry;
    depth = malloc(u->count * sizeof *depth);
    if (!depth) {
        fputs("out of memory emitting assembly\n", stderr);
        exit(EXIT_FAILURE);
    }
    lp_depths(u, depth);
    lp_liveness(u);

    for (word = 0; word < 32; word += 2) {
        unsigned score = 0, loop_uses = 0;
        int ok = 1;
        for (i = 0; i < u->count && ok; ++i) {
            LpLine *l = &u->lines[i];
            size_t m;
            const char *p;
            int w, gain;
            if (!l->op)
                continue;
            p = lp_operand(l, &m);
            w = lp_workspace_word(p, m);
            if (w < 0 && (w = lp_workspace_pointer(p, m)) >= 0) {
                if (w == (int)word) {
                    if (!lp_accumulator_memory(l))
                        ok = 0;
                    if (depth[i]) {
                        ++loop_uses;
                        score += 5u << (3 * (depth[i] > 3 ? 3 : depth[i]));
                    }
                } else if (w + 1 == (int)word || w == (int)word + 1)
                    ok = 0;
                continue;
            }
            if (w < 0) {
                if (lp_text_words(p, p + m) & (1u << (word / 2)))
                    ok = 0;
                continue;
            }
            if (!lp_overlaps(l, w, (int)word))
                continue;
            if (w != (int)word) {
                ok = 0;
                break;
            }
            if ((lp_is(l, "lda") || lp_is(l, "sta") || lp_is(l, "stz")) && !l->m8)
                gain = 2;
            else if (lp_is(l, "ldx") || lp_is(l, "stx"))
                gain = 2;
            else if ((lp_is(l, "inc") || lp_is(l, "dec")) && !l->m8)
                gain = 5;
            else {
                ok = 0;
                break;
            }
            if ((lp_is(l, "sta") || lp_is(l, "stx") || lp_is(l, "stz")) && l->out & (LP_N | LP_Z)) {
                ok = 0;
                break;
            }
            if (depth[i]) {
                ++loop_uses;
                score += (unsigned)gain << (3 * (depth[i] > 3 ? 3 : depth[i]));
            }
        }
        if (ok && loop_uses >= 2 && score > best_score) {
            best_score = score;
            best = word;
        }
    }
    free(depth);
    if (!best_score)
        return 0;
    sd = malloc(u->count * sizeof *sd);
    if (!sd) {
        fputs("out of memory emitting assembly\n", stderr);
        exit(EXIT_FAILURE);
    }
    if (!lp_stack_depths(u, first, sd)) {
        free(sd);
        return 0;
    }

    for (i = 0; i < u->count; ++i) {
        size_t m;
        const char *p = lp_operand(&u->lines[i], &m);
        if (u->lines[i].op && m >= 2 && p[m - 2] == ',' && p[m - 1] == 's' &&
            (sd[i] < 0 ||
             (strtoul(p, NULL, 10) > (unsigned long)sd[i] && strtoul(p, NULL, 10) + 2 > 255))) {
            free(sd);
            return 0;
        }
    }

    for (i = 0; i < u->count; ++i) {
        LpLine *l = &u->lines[i];
        size_t m;
        const char *p;
        if (!l->op)
            continue;
        p = lp_operand(l, &m);
        if (lp_workspace_word(p, m) == (int)best) {
            if (lp_is(l, "lda"))
                lp_set(l, "    tya");
            else if (lp_is(l, "ldx"))
                lp_set(l, "    tyx");
            else if (lp_is(l, "sta"))
                lp_set(l, "    tay");
            else if (lp_is(l, "stx"))
                lp_set(l, "    txy");
            else if (lp_is(l, "stz"))
                lp_set(l, "    ldy #$0000");
            else if (lp_is(l, "inc"))
                lp_set(l, "    iny");
            else
                lp_set(l, "    dey");
        } else if (lp_workspace_pointer(p, m) == (int)best) {
            lp_set(l, "    %.3s a:$0000,y", l->op);
        } else if (m >= 2 && p[m - 2] == ',' && p[m - 1] == 's') {
            /* The saved Y sits below the entry stack, above this function's pushes */
            if (strtoul(p, NULL, 10) > (unsigned long)sd[i])
                lp_set(l, "    %.3s %lu,s", l->op, strtoul(p, NULL, 10) + 2);
        }
        if (l->ends && (lp_is(l, "rts") || lp_is(l, "rtl") || (l->call && l->target < 0)))
            lp_insert(l, "    ply\n");
    }
    {
        char text[96];
        snprintf(text, sizeof text, "; Y holds workspace word %u\n    phy\n", best);
        lp_insert(&u->lines[first], text);
    }
    free(sd);
    return 1;
}

static int lp_y_promote_split(LpUnit *u, Function *f, size_t at)
{
    unsigned i, word, best = 0, best_score = 0, *depth, first = 0, y_first = u->count, y_last = 0;
    int entry = -1, *sd, has_phy = 0;
    (void)at;

    if (u->helpers || u->indirect || f->symbol->interrupt)
        return 0;

    for (i = 0; i < u->count; ++i) {
        LpLine *l = &u->lines[i];
        if (!l->op)
            continue;
        if (entry < 0)
            entry = (int)i;
        if (l->x8)
            return 0;
        if (lp_is(l, "phy") || lp_is(l, "ply")) {
            has_phy = 1;
            continue;
        }
        if (lp_is(l, "tsx") || lp_is(l, "txs") || lp_is(l, "mvn") || lp_is(l, "mvp") ||
            lp_is(l, "jml") || lp_is(l, "rti") || lp_is(l, "tsc") || lp_is(l, "tcs"))
            return 0;
        if (l->use == LP_ALL && !lp_is(l, "rep") && !lp_is(l, "sep"))
            return 0;
        if ((lp_is(l, "rep") || lp_is(l, "sep")) && strtoul(l->op + 6, NULL, 16) & 0x10)
            return 0;
        if (l->target >= 0) {
            unsigned t = (unsigned)l->target;
            while (t < u->count && !u->lines[t].op)
                ++t;
            if (entry >= 0 && t <= (unsigned)entry)
                return 0;
        }
        {
            size_t m;
            const char *p = lp_operand(l, &m);
            if (m >= 2 && p[m - 2] == ',' && p[m - 1] == 's' && strtoul(p, NULL, 10) + 2 > 255)
                return 0;
        }
    }
    if (entry < 0)
        return 0;
    first = (unsigned)entry;
    depth = malloc(u->count * sizeof *depth);
    if (!depth) {
        fputs("out of memory emitting assembly\n", stderr);
        exit(EXIT_FAILURE);
    }
    lp_depths(u, depth);
    lp_liveness(u);

    for (i = 0; i < u->count; ++i) {
        LpLine *l = &u->lines[i];
        if (!l->op)
            continue;
        if ((lp_index_use(l) & LP_Y) ||
            (l->use & LP_Y && !l->ends && !l->call && l->use != LP_ALL) || (l->def & LP_Y) ||
            (l->live & LP_Y)) {
            if (i < y_first)
                y_first = i;
            y_last = i;
        }
    }
    if (y_first > y_last || y_last + 1 >= u->count) {
        free(depth);
        return 0;
    }

    for (i = 0; i < u->count; ++i) {
        LpLine *l = &u->lines[i];
        if (!l->op || l->target < 0)
            continue;
        if (i < y_first || i > y_last) {
            if ((unsigned)l->target > y_first && (unsigned)l->target <= y_last) {
                free(depth);
                return 0;
            }
        } else {
            if (l->ends && (lp_is(l, "rts") || lp_is(l, "rtl"))) {
                free(depth);
                return 0;
            }
            if ((unsigned)l->target < y_first || (unsigned)l->target > y_last + 1) {
                free(depth);
                return 0;
            }
        }
    }

    for (word = 0; word < 32; word += 2) {
        unsigned score = 0, loop_uses = 0;
        int ok = 1;
        for (i = 0; i < u->count && ok; ++i) {
            LpLine *l = &u->lines[i];
            size_t m;
            const char *p;
            int w, gain;
            if (!l->op)
                continue;
            p = lp_operand(l, &m);
            w = lp_workspace_word(p, m);
            if (i >= y_first && i <= y_last) {
                if (w >= 0 && lp_overlaps(l, w, (int)word)) {
                    ok = 0;
                    break;
                }
                if (w < 0 && (lp_workspace_pointer(p, m) == (int)word ||
                              (lp_text_words(p, p + m) & (1u << (word / 2))))) {
                    ok = 0;
                    break;
                }
                continue;
            }
            if (w < 0 && (w = lp_workspace_pointer(p, m)) >= 0) {
                if (w == (int)word) {
                    if (!lp_accumulator_memory(l))
                        ok = 0;
                    if (depth[i]) {
                        ++loop_uses;
                        score += 5u << (3 * (depth[i] > 3 ? 3 : depth[i]));
                    }
                } else if (w + 1 == (int)word || w == (int)word + 1)
                    ok = 0;
                continue;
            }
            if (w < 0) {
                if (lp_text_words(p, p + m) & (1u << (word / 2)))
                    ok = 0;
                continue;
            }
            if (!lp_overlaps(l, w, (int)word))
                continue;
            if (w != (int)word) {
                ok = 0;
                break;
            }
            if ((lp_is(l, "lda") || lp_is(l, "sta") || lp_is(l, "stz")) && !l->m8)
                gain = 2;
            else if (lp_is(l, "ldx") || lp_is(l, "stx"))
                gain = 2;
            else if ((lp_is(l, "inc") || lp_is(l, "dec")) && !l->m8)
                gain = 5;
            else {
                ok = 0;
                break;
            }
            if ((lp_is(l, "sta") || lp_is(l, "stx") || lp_is(l, "stz")) && l->out & (LP_N | LP_Z)) {
                ok = 0;
                break;
            }
            if (depth[i]) {
                ++loop_uses;
                score += (unsigned)gain << (3 * (depth[i] > 3 ? 3 : depth[i]));
            }
        }
        if (ok && loop_uses >= 2 && score > best_score) {
            best_score = score;
            best = word;
        }
    }
    free(depth);
    if (!best_score)
        return 0;
    sd = malloc(u->count * sizeof *sd);
    if (!sd) {
        fputs("out of memory emitting assembly\n", stderr);
        exit(EXIT_FAILURE);
    }
    if (!lp_stack_depths(u, first, sd)) {
        free(sd);
        return 0;
    }
    if (!has_phy) {
        for (i = 0; i < u->count; ++i) {
            size_t m;
            const char *p = lp_operand(&u->lines[i], &m);
            if (u->lines[i].op && m >= 2 && p[m - 2] == ',' && p[m - 1] == 's' &&
                (sd[i] < 0 ||
                 (strtoul(p, NULL, 10) > (unsigned long)sd[i] && strtoul(p, NULL, 10) + 2 > 255))) {
                free(sd);
                return 0;
            }
        }
    }

    for (i = 0; i < u->count; ++i) {
        LpLine *l = &u->lines[i];
        size_t m;
        const char *p;
        if (!l->op)
            continue;
        p = lp_operand(l, &m);
        if (i < y_first || i > y_last) {
            if (lp_workspace_word(p, m) == (int)best) {
                if (lp_is(l, "lda"))
                    lp_set(l, "    tya");
                else if (lp_is(l, "ldx"))
                    lp_set(l, "    tyx");
                else if (lp_is(l, "sta"))
                    lp_set(l, "    tay");
                else if (lp_is(l, "stx"))
                    lp_set(l, "    txy");
                else if (lp_is(l, "stz"))
                    lp_set(l, "    ldy #$0000");
                else if (lp_is(l, "inc"))
                    lp_set(l, "    iny");
                else
                    lp_set(l, "    dey");
            } else if (lp_workspace_pointer(p, m) == (int)best) {
                lp_set(l, "    %.3s a:$0000,y", l->op);
            } else if (!has_phy && m >= 2 && p[m - 2] == ',' && p[m - 1] == 's') {
                if (strtoul(p, NULL, 10) > (unsigned long)sd[i])
                    lp_set(l, "    %.3s %lu,s", l->op, strtoul(p, NULL, 10) + 2);
            }
        } else if (!has_phy && m >= 2 && p[m - 2] == ',' && p[m - 1] == 's') {
            if (strtoul(p, NULL, 10) > (unsigned long)sd[i])
                lp_set(l, "    %.3s %lu,s", l->op, strtoul(p, NULL, 10) + 2);
        }
        if (!has_phy && l->ends &&
            (lp_is(l, "rts") || lp_is(l, "rtl") || (l->call && l->target < 0)))
            lp_insert(l, "    ply\n");
    }
    {
        char sty[64], ldy[64];
        if (best) {
            snprintf(sty, sizeof sty, "    sty z:__arith_lhs+%u\n", best);
            snprintf(ldy, sizeof ldy, "    ldy z:__arith_lhs+%u\n", best);
        } else {
            snprintf(sty, sizeof sty, "    sty z:__arith_lhs\n");
            snprintf(ldy, sizeof ldy, "    ldy z:__arith_lhs\n");
        }
        lp_insert(&u->lines[y_first], sty);
        lp_insert(&u->lines[y_last + 1], ldy);
    }
    if (!has_phy) {
        char text[96];
        snprintf(text, sizeof text, "; Y holds workspace word %u (split)\n    phy\n", best);
        lp_insert(&u->lines[first], text);
    }
    free(sd);
    return 1;
}

/* Known accumulator constants: "lda #v" folds a following and/ora/eor #m,
 * and "lda #v / cmp #w" decides the branches that read only its flags. */
/* A compiler-local label every entry of which (branch or fallthrough) is a
 * chain line, or is preceded by a line control cannot fall out of. */
static int lp_chain_label(const LpUnit *u, unsigned t, const char *chain)
{
    const LpLine *l = &u->lines[t];
    unsigned j;
    int p;

    if (!(l->length == 1 && l->text[0] == ':') && strncmp(l->text, "cg_", 3))
        return 0;

    for (j = 0; j < u->count; ++j)
        if (u->lines[j].op && !u->lines[j].deleted && u->lines[j].target == (int)t && !chain[j])
            return 0;

    for (p = (int)t - 1;
         p >= 0 && (u->lines[p].deleted || !u->lines[p].length || u->lines[p].text[0] == ';');
         --p) {
    }
    if (p < 0)
        return 0;
    if (chain[p] || (u->lines[p].op && u->lines[p].ends && !u->lines[p].call))
        return 1;
    return 0;
}

/* Folds the branches that follow line k, whose flag results are known;
 * a negative c or v is unknown. Follows taken branches and fallthroughs into
 * labels entered only from the chain. Returns how many branches changed. */
static int lp_fold_branches(LpUnit *u, int k, int z, int c, int n, int v)
{
    int i = k, changed = 0, steps = 0;
    char *chain;

    if (u->indirect)
        return 0;
    chain = calloc(u->count, 1);
    if (!chain) {
        fputs("out of memory emitting assembly\n", stderr);
        exit(EXIT_FAILURE);
    }
    chain[k] = 1;

    while (++steps < 64) {
        unsigned t = (unsigned)i + 1;
        LpLine *br;
        int taken;
        while (t < u->count && u->lines[t].length &&
               (u->lines[t].text[0] == ';' || u->lines[t].deleted))
            ++t;
        if (t >= u->count || !u->lines[t].length)
            break;
        br = &u->lines[t];
        if (br->label) {
            if (!lp_chain_label(u, t, chain))
                break;
            chain[t] = 1;
            i = (int)t;
            continue;
        }
        if (!br->op || !lp_branch(br) || br->replace || lp_is(br, "brl") || lp_is(br, "jml"))
            break;
        if (lp_is(br, "bra"))
            taken = 1;
        else if (lp_is(br, "beq"))
            taken = z;
        else if (lp_is(br, "bne"))
            taken = !z;
        else if (c >= 0 && lp_is(br, "bcs"))
            taken = c;
        else if (c >= 0 && lp_is(br, "bcc"))
            taken = !c;
        else if (lp_is(br, "bmi"))
            taken = n;
        else if (lp_is(br, "bpl"))
            taken = !n;
        else if (v >= 0 && lp_is(br, "bvs"))
            taken = v;
        else if (v >= 0 && lp_is(br, "bvc"))
            taken = !v;
        else
            break;
        chain[t] = 1;
        if (!taken) {
            br->deleted = 1;
            ++changed;
            i = (int)t;
            continue;
        }
        if (!lp_is(br, "bra")) {
            size_t m;
            const char *p = lp_operand(br, &m);
            lp_set(br, "    bra %.*s", (int)m, p);
            ++changed;
        }

        /* Continue at a forward target only if nothing else enters it */
        if (br->target <= (int)t || !lp_chain_label(u, (unsigned)br->target, chain))
            break;
        chain[br->target] = 1;
        i = br->target;
    }
    free(chain);
    return changed;
}

static int lp_fallthrough_marker(const LpLine *l, unsigned j, const unsigned char *targets,
                                 int known_targets)
{
    if (l->op)
        return 0;
    if (!l->length || l->text[0] == ';')
        return 1;
    if (!strncmp(l->text, ".export __inlined_", 18))
        return 1;
    return known_targets && !targets[j] && lp_fallthrough_label(l);
}

/* Consecutive folded conversions can raise the same sticky flag.
 * A guard that only observes the rounding mode leaves that flag set. */
static int lp_repeated_inexact_raise(LpUnit *u, Function *f, size_t at)
{
    static const char raise[] = "tsb a:.loword(__fp_exceptions)";
    (void)at;

    if (u->indirect || body_asm_statements(f->body))
        return 0;
    int known;
    unsigned char *targets = lp_local_targets(u, &known);
    lp_liveness(u);

    for (unsigned i = 0; i < u->count; ++i) {
        LpLine *first = &u->lines[i];
        if (first->m8 || !lp_line_is(first, raise))
            continue;
        int literal = lp_next_fallthrough(u, i, -1, targets, known);
        if (literal < 0 || !lp_line_is(&u->lines[literal], "lda #$0010"))
            continue;
        int step = (int)i;
        for (unsigned n = 0; n < 5; ++n) {
            step = lp_next_fallthrough(u, (unsigned)step, 1, targets, known);
            if (step < 0)
                break;
            LpLine *next = &u->lines[step];
            if (next->m8)
                break;
            if (lp_line_is(next, "lda #$0010")) {
                int dup = lp_next_fallthrough(u, (unsigned)step, 1, targets, known);
                if (dup >= 0 && lp_line_is(&u->lines[dup], raise) &&
                    !(u->lines[dup].out & (LP_A | LP_N | LP_Z))) {
                    next->deleted = u->lines[dup].deleted = 1;
                    free(targets);
                    return 1;
                }
                break;
            }
            if (lp_line_is(next, "lda a:.loword(__fp_round_mode)") || lp_line_is(next, "lsr a") ||
                ((lp_is(next, "bit") || lp_is(next, "cmp")) && lp_immediate(next) >= 0))
                continue;
            int after;
            if (lp_cond_branch_target(u, step, &after) < 0)
                break;
            if (after != step &&
                (u->lines[after].first_incoming != step || next->next_incoming >= 0))
                break;
            step = after;
        }
    }
    free(targets);
    return 0;
}

/* Carry the value just written to a named object along a loop backedge.
 * A separate entry keeps the original load on every other predecessor. */
static int lp_forward_named_latch_load(LpUnit *u, Function *f, size_t at)
{
    (void)at;
    if (u->indirect || lp_state.parser->no_value_reuse || body_asm_statements(f->body))
        return 0;
    int known;
    unsigned char *targets = lp_local_targets(u, &known);
    lp_liveness(u);

    for (unsigned i = 1; i < u->count; ++i) {
        LpLine *edge = &u->lines[i];
        if ((!lp_is(edge, "bra") && !lp_is(edge, "jmp")) || edge->target < 0 ||
            (unsigned)edge->target >= i)
            continue;
        int store = lp_next_fallthrough(u, i, -1, targets, known);
        int load = lp_next_fallthrough(u, (unsigned)edge->target, 1, targets, known);
        if (store < 0 || load < 0 || load >= store || (unsigned)(load + 1) >= u->count)
            continue;
        LpLine *write = &u->lines[store], *read = &u->lines[load];
        if (!lp_is(write, "sta") || !lp_is(read, "lda") || write->m8 != read->m8 ||
            (read->out & (LP_N | LP_Z)))
            continue;
        size_t n;
        const char *home = lp_operand(write, &n);
        if (memchr(home, ',', n) || !pr_named(home, n) || !lp_operand_is(read, home, n))
            continue;
        unsigned id = lp_next_label();
        char label[48];
        snprintf(label, sizeof label, "cg_lp_%u:\n", id);
        lp_insert(&u->lines[load + 1], label);
        lp_set(edge, "    jmp .loword(cg_lp_%u)", id);
        free(targets);
        return 1;
    }
    free(targets);
    return 0;
}

/* Keep a named loop word in X while the loop test consumes A */
static int lp_named_counter_in_x(LpUnit *u, Function *f, size_t at)
{
    (void)at;
    if (u->indirect || lp_state.parser->no_value_reuse || body_asm_statements(f->body))
        return 0;
    int known, changed = 0;
    unsigned char *targets = lp_local_targets(u, &known);
    lp_liveness(u);

    for (unsigned i = 1; i < u->count && !changed; ++i) {
        LpLine *edge = &u->lines[i];
        int head = edge->target;
        if ((!lp_is(edge, "bra") && !lp_is(edge, "jmp")) || head < 0 || (unsigned)head >= i ||
            u->lines[head].first_incoming != (int)i || edge->next_incoming >= 0)
            continue;
        int store = lp_next_fallthrough(u, i, -1, targets, known);
        if (store < 0 || !lp_is(&u->lines[store], "sta") || u->lines[store].m8)
            continue;
        size_t n;
        const char *home = lp_operand(&u->lines[store], &n);
        if (n < 3 || strncmp(home, "a:", 2) || memchr(home, ',', n) || !pr_named(home, n))
            continue;
        int first = lp_next(u, (unsigned)store, -1), read = first;
        while (read >= 0 &&
               (lp_line_is(&u->lines[read], "inc a") || lp_line_is(&u->lines[read], "dec a")))
            read = lp_next(u, (unsigned)read, -1);
        if (read < 0 || read == first || !lp_is(&u->lines[read], "lda") ||
            !lp_operand_is(&u->lines[read], home, n))
            continue;
        int init = lp_next_fallthrough(u, (unsigned)head, -1, targets, known);
        int test = lp_next_fallthrough(u, (unsigned)head, 1, targets, known);
        if (init < 0 || test < 0 || test >= read || !lp_is(&u->lines[init], "lda") ||
            !lp_operand_is(&u->lines[init], home, n) || (u->lines[init].out & LP_X))
            continue;
        unsigned sites[8], entries;
        if (!lp_entries(u, (unsigned)head, i, sites, &entries) || entries != 1)
            continue;
        int valid = 1, uses_a = 0;
        for (unsigned j = (unsigned)init; j <= i && valid; ++j) {
            LpLine *l = &u->lines[j];
            if (!l->op)
                continue;
            if (l->m8 || l->x8 || l->call || (l->use | l->def) & LP_X ||
                (j < (unsigned)store && lp_may_write(l, home, n, 2)))
                valid = 0;
            if (j >= (unsigned)test && j < (unsigned)read && (l->use & LP_A))
                uses_a = 1;
        }
        if (!valid || !uses_a)
            continue;
        lp_set(&u->lines[init], "    ldx %.*s", (int)n, home);
        lp_insert(&u->lines[test], "    txa\n");
        u->lines[read].deleted = 1;
        for (int j = first; j != read; j = lp_next(u, (unsigned)j, -1))
            lp_set(&u->lines[j], "    %s", lp_line_is(&u->lines[j], "inc a") ? "inx" : "dex");
        lp_set(&u->lines[store], "    stx %.*s", (int)n, home);
        changed = 1;
    }
    free(targets);
    return changed;
}

/* Remove a direct stack or object store covered by another before any memory read,
 * control transfer, stack movement or potential entry into the sequence. */
static int lp_overwritten_stores(LpUnit *u, Function *f, size_t at)
{
    int known, changed = 0;
    (void)at;

    if (u->indirect || lp_state.frame_address || lp_state.is_volatile ||
        lp_state.parser->no_private_regions || body_asm_statements(f->body))
        return 0;
    unsigned char *targets = lp_local_targets(u, &known);

    for (unsigned i = 0; i < u->count; ++i) {
        LpLine *store = &u->lines[i];
        size_t n;
        const char *p = lp_operand(store, &n);
        int stack = n >= 3 && p[n - 1] == 's' && lp_private(p, n);
        int named = !stack && !memchr(p, ',', n) && pr_named(p, n);
        if ((!lp_is(store, "sta") && !lp_is(store, "stz")) || (!stack && !named))
            continue;
        for (unsigned j = i + 1; j < u->count; ++j) {
            LpLine *l = &u->lines[j];
            size_t m;
            const char *q = lp_operand(l, &m);
            if (lp_fallthrough_marker(l, j, targets, known))
                continue;
            if ((lp_is(l, "sta") || lp_is(l, "stz")) &&
                ((stack && m >= 3 && q[m - 1] == 's' && lp_private(q, m)) ||
                 (named && !memchr(q, ',', m) && pr_named(q, m)))) {
                if (lp_operand_is(l, p, n) && lp_width(l) >= lp_width(store)) {
                    store->deleted = 1;
                    ++changed;
                    break;
                }
                continue;
            }
            if (lp_line_is(l, "inc a") || lp_line_is(l, "dec a") ||
                ((lp_is(l, "lda") || lp_is(l, "ldx") || lp_is(l, "ldy")) && m && q[0] == '#'))
                continue;
            break;
        }
    }
    free(targets);
    return changed;
}

/* Push an outgoing register pair directly instead of spilling the low
 * word and fetching it again below the high-word argument. */
static int lp_push_register_pair(LpUnit *u, Function *f, size_t at)
{
    int known, changed = 0;
    unsigned char *targets = lp_local_targets(u, &known);
    (void)f;
    (void)at;

    lp_liveness(u);

    for (unsigned i = 0; i < u->count; ++i) {
        LpLine *save = &u->lines[i];
        size_t n;
        const char *slot = lp_operand(save, &n);
        if (!lp_is(save, "sta") || save->m8 || save->x8 || !lp_private(slot, n) ||
            slot[n - 1] != 's')
            continue;
        unsigned seq[4], count = 0, j = i + 1;
        for (; count < 4; ++count) {
            while (j < u->count && lp_fallthrough_marker(&u->lines[j], j, targets, known))
                ++j;
            if (j == u->count || !u->lines[j].op)
                break;
            seq[count] = j++;
        }
        if (count != 4 || !lp_line_is(&u->lines[seq[0]], "txa") ||
            !lp_line_is(&u->lines[seq[1]], "pha") || !lp_is(&u->lines[seq[2]], "lda") ||
            !lp_line_is(&u->lines[seq[3]], "pha") || (u->lines[seq[3]].out & (LP_N | LP_Z)))
            continue;
        const char *reload = lp_operand(&u->lines[seq[2]], &n);
        if (!lp_private(reload, n) || reload[n - 1] != 's' || atoi(reload) != atoi(slot) + 2)
            continue;
        u->lines[seq[0]].deleted = u->lines[seq[2]].deleted = 1;
        lp_set(&u->lines[seq[1]], "    phx");
        ++changed;
        i = seq[3];
    }
    free(targets);
    return changed;
}

/* Pulling and immediately pushing the same register leaves the stack
 * untouched. A known scalar return supplies A and a long return also
 * supplies X, even if their result is subsequently live. */
static int lp_cancel_pull_push(LpUnit *u, Function *f, size_t at)
{
    int known, changed = 0;
    unsigned char *targets = lp_local_targets(u, &known);
    (void)f;
    (void)at;

    lp_liveness(u);

    for (unsigned i = 0; i < u->count; ++i) {
        LpLine *pull = &u->lines[i];
        unsigned reg = lp_is(pull, "pla")   ? LP_A
                       : lp_is(pull, "plx") ? LP_X
                       : lp_is(pull, "ply") ? LP_Y
                                            : 0;
        if (!reg || pull->m8 || pull->x8)
            continue;
        unsigned j = i + 1;
        while (j < u->count && lp_fallthrough_marker(&u->lines[j], j, targets, known))
            ++j;
        if (j == u->count ||
            !lp_line_is(&u->lines[j], reg == LP_A   ? "pha"
                                      : reg == LP_X ? "phx"
                                                    : "phy") ||
            (u->lines[j].out & (LP_N | LP_Z)))
            continue;
        if (u->lines[j].out & reg) {
            int k = (int)j;
            while ((k = lp_next(u, (unsigned)k, 1)) >= 0) {
                LpLine *l = &u->lines[k];
                if (l->use & reg)
                    break;
                if (l->call) {
                    Symbol *callee = lp_callee(l);
                    if (callee && !callee->interrupt && !structure_object(callee->type) &&
                        (callee->type.pointers || callee->type.base != TY_VOID) &&
                        (reg == LP_A || (reg == LP_X && reg_width(callee->type) == 4)))
                        goto dead;
                    break;
                }
                if (l->target >= 0 || l->ends || lp_branch(l))
                    break;
            }
            continue;
        }
    dead:
        pull->deleted = u->lines[j].deleted = 1;
        ++changed;
        i = j;
    }
    free(targets);
    return changed;
}

/* Only edges from the already validated interval may enter a label */
static int lp_internal_path_marker(const LpUnit *u, unsigned j, unsigned start)
{
    const LpLine *l = &u->lines[j];

    if (!l->length || l->text[0] == ';' || !strncmp(l->text, ".export __inlined_", 18))
        return 1;
    if (!l->label || (!lp_fallthrough_label(l) && (l->length != 1 || l->text[0] != ':')))
        return 0;
    int incoming = l->first_incoming;

    while (incoming > (int)start && (unsigned)incoming < j)
        incoming = u->lines[incoming].next_incoming;
    return incoming < 0;
}

/* At a join every incoming path must retain the same byte read from
 * the far cursor, or the whole word loaded from or stored in a private home. A finite search rejects cycles and unknown control flow. */
static int lp_prior_home_value(const LpUnit *u, int pos, unsigned load, const char *home, size_t n,
                               int word, int flags, int *budget)
{
    for (; pos >= 0 && *budget > 0; --pos) {
        const LpLine *l = &u->lines[pos];
        --*budget;
        if ((unsigned)pos == load)
            return 0;
        if (l->op) {
            if (lp_is(l, "lda") || (word && lp_is(l, "sta"))) {
                if (l->m8 != !word || !lp_operand_is(l, home, n))
                    return 0;
                if (!flags || lp_is(l, "lda"))
                    return 1;
                int prev = lp_next(u, (unsigned)pos, -1);
                return prev >= 0 && !u->lines[prev].m8 &&
                       full_accumulator_flags(u->lines[prev].text, u->lines[prev].length);
            }
            size_t operand_length;
            const char *operand = lp_operand(l, &operand_length);
            if (lp_line_is(l, "rep #$20") || lp_line_is(l, "sep #$20") ||
                (!flags && (lp_is(l, "cmp") || lp_is(l, "cpx") || lp_is(l, "cpy")) &&
                 operand_length > 1 && operand[0] == '#') ||
                (l->target >= 0 && (lp_branch(l) || lp_is(l, "jmp"))))
                continue;
            return 0;
        }
        if (l->label) {
            if (!lp_fallthrough_label(l) && (l->length != 1 || l->text[0] != ':'))
                return 0;
            for (int j = l->first_incoming; j >= 0; j = u->lines[j].next_incoming)
                if (!lp_prior_home_value(u, j, load, home, n, word, flags, budget))
                    return 0;
            if (pos && u->lines[pos - 1].ends)
                return l->first_incoming >= 0;
        } else if (l->length && l->text[0] != ';' && strncmp(l->text, ".export __inlined_", 18) &&
                   !(l->length == 3 && !strncmp(l->text, ".a8", 3)) &&
                   !(l->length == 4 && !strncmp(l->text, ".a16", 4)))
            return 0;
    }
    return 0;
}

/* A unit increment sets Z exactly when the unsigned addition would
 * carry. Use it directly when the branch is the last consumer of C. */
static int lp_increment_wrap_test(LpUnit *u, Function *f, size_t at)
{
    int changed = 0;
    (void)at;

    if (body_asm_statements(f->body))
        return 0;
    lp_liveness(u);

    for (unsigned i = 0; i < u->count; ++i) {
        if (!lp_line_is(&u->lines[i], "clc"))
            continue;
        int add = lp_next(u, i, 1), branch = add < 0 ? -1 : lp_next(u, (unsigned)add, 1);
        if (branch < 0 || !lp_is(&u->lines[add], "adc") || lp_immediate(&u->lines[add]) != 1)
            continue;
        LpLine *edge = &u->lines[branch];
        size_t n;
        const char *target = lp_operand(edge, &n);
        if ((!lp_is(edge, "bcc") && !lp_is(edge, "bcs")) || edge->target < 0 ||
            (edge->out & (LP_C | LP_V)))
            continue;
        u->lines[i].deleted = 1;
        lp_set(&u->lines[add], "    inc a");
        lp_set(edge, "    %s %.*s", lp_is(edge, "bcc") ? "bne" : "beq", (int)n, target);
        ++changed;
    }
    return changed;
}

/* Testing a far byte and then consuming it on one path only needs the
 * first read. Width changes and branches preserve both A and its flags. */
static int lp_reuse_far_byte(LpUnit *u, Function *f, size_t at)
{
    (void)f;
    (void)at;
    if (lp_state.is_volatile || u->indirect || body_asm_statements(f->body))
        return 0;
    lp_liveness(u);

    for (unsigned i = 0; i < u->count; ++i) {
        LpLine *first = &u->lines[i];
        size_t n;
        const char *op = lp_operand(first, &n);
        if (!first->m8 && lp_is(first, "lda") && lp_private(op, n)) {
            int budget = 96;
            if (lp_prior_home_value(u, (int)i - 1, i, op, n, 1, first->out & (LP_N | LP_Z),
                                    &budget)) {
                first->deleted = 1;
                return 1;
            }
        }
        if (!first->m8 || !lp_is(first, "lda") || n < 13 || strncmp(op, "[__arith_", 9) ||
            op[n - 1] != ']')
            continue;
        int budget = 96;
        if (!(first->out & (LP_N | LP_Z)) &&
            lp_prior_home_value(u, (int)i - 1, i, op, n, 0, 0, &budget)) {
            first->deleted = 1;
            return 1;
        }
        for (unsigned j = i + 1; j < u->count; ++j) {
            LpLine *l = &u->lines[j];
            if (!l->op) {
                if (lp_internal_path_marker(u, j, i) ||
                    (l->length == 3 && !strncmp(l->text, ".a8", 3)) ||
                    (l->length == 4 && !strncmp(l->text, ".a16", 4)))
                    continue;
                break;
            }
            if (lp_line_is(l, "sep #$20") || lp_line_is(l, "rep #$20") ||
                (!l->call && l->target >= 0 && (lp_branch(l) || lp_is(l, "jmp"))))
                continue;
            if (l->m8 && lp_is(l, "lda") && lp_operand_is(l, op, n)) {
                l->deleted = 1;
                return 1;
            }
            break;
        }
    }
    return 0;
}

/* Unsigned A < its sign bit is the nonnegative half of the encoding.
 * A preceding load already supplied N at the comparison width. */
static int lp_sign_bit_order(LpUnit *u, Function *f, size_t at)
{
    int changed = 0;
    (void)f;
    (void)at;

    lp_liveness(u);

    for (unsigned i = 0; i < u->count; ++i) {
        LpLine *cmp = &u->lines[i];
        if (!lp_is(cmp, "cmp") || lp_immediate(cmp) != (cmp->m8 ? 128 : 32768))
            continue;
        int previous = (int)i - 1;
        while (previous >= 0 && !u->lines[previous].op &&
               (u->lines[previous].text[0] == ';' ||
                (u->lines[previous].length == 3 && !strncmp(u->lines[previous].text, ".a8", 3)) ||
                (u->lines[previous].length == 4 && !strncmp(u->lines[previous].text, ".a16", 4))))
            --previous;
        if (previous < 0 || u->lines[previous].m8 != cmp->m8 || !lp_is(&u->lines[previous], "lda"))
            continue;
        unsigned j = i + 1;
        while (j < u->count &&
               (u->lines[j].text[0] == ';' || lp_line_is(&u->lines[j], "rep #$20") ||
                (u->lines[j].length == 4 && !strncmp(u->lines[j].text, ".a16", 4))))
            ++j;
        if (j == u->count)
            continue;
        LpLine *br = &u->lines[j];
        if ((!lp_is(br, "bcc") && !lp_is(br, "bcs")) || (br->out & (LP_C | LP_N | LP_Z)))
            continue;
        size_t n;
        const char *target = lp_operand(br, &n);
        lp_set(br, "    %s %.*s", lp_is(br, "bcc") ? "bpl" : "bmi", (int)n, target);
        cmp->deleted = 1;
        ++changed;
    }
    return changed;
}

/* A zero-only mask test can preserve its source word for the next
 * test along the same path. Branches do not modify the frame or A. */
static int lp_keep_mask_source(LpUnit *u, Function *f, size_t at)
{
    (void)f;
    (void)at;
    if (u->indirect || lp_state.is_volatile)
        return 0;
    lp_liveness(u);

    for (unsigned i = u->count; i-- > 0;) {
        LpLine *load = &u->lines[i];
        size_t n;
        const char *home = lp_operand(load, &n);
        if (!lp_is(load, "lda") || load->m8 || !lp_private(home, n))
            continue;
        int next = lp_next(u, i, 1);
        if (next < 0)
            continue;
        LpLine *mask = &u->lines[next];
        long bits = lp_immediate(mask);
        if (!lp_is(mask, "and") || bits < 0)
            continue;
        int zero_only = !(mask->out & (LP_N | LP_A));
        for (unsigned j = (unsigned)next + 1; j < u->count; ++j) {
            LpLine *l = &u->lines[j];
            if (!l->op) {
                if (lp_internal_path_marker(u, j, (unsigned)next))
                    continue;
                break;
            }
            if (!l->call && l->target >= 0 && (lp_branch(l) || lp_is(l, "jmp")))
                continue;
            if (!zero_only && lp_is(l, "cmp") && lp_immediate(l) >= 0)
                continue;
            if (lp_is(l, "lda") && !l->m8 && lp_operand_is(l, home, n)) {
                if (zero_only && !(l->out & (LP_N | LP_Z))) {
                    lp_set(mask, "    bit #$%04lX", bits);
                    l->deleted = 1;
                    return 1;
                }
                int repeat = lp_next(u, j, 1);
                if (repeat >= 0 && lp_is(&u->lines[repeat], "and") &&
                    lp_immediate(&u->lines[repeat]) == bits &&
                    !(u->lines[repeat].out & (LP_N | LP_Z))) {
                    l->deleted = u->lines[repeat].deleted = 1;
                    return 1;
                }
            }
            break;
        }
    }
    return 0;
}

/* INC/DEC A supplies the same word and N/Z without fetching a
 * carry setup and immediate operand. Preserve observable C and V. */
static int lp_small_accumulator_steps(LpUnit *u, Function *f, size_t at)
{
    int changed = 0;
    (void)f;
    (void)at;

    lp_liveness(u);

    for (unsigned i = 0; i < u->count; ++i) {
        int sub = lp_line_is(&u->lines[i], "sec");
        if (!sub && !lp_line_is(&u->lines[i], "clc"))
            continue;
        int step = lp_next(u, i, 1);
        if (step < 0 || !lp_is(&u->lines[step], sub ? "sbc" : "adc") || u->lines[step].m8 ||
            (u->lines[step].out & (LP_C | LP_V)))
            continue;
        long n = lp_immediate(&u->lines[step]);
        int initial = -1;
        if (n < 0 && !sub) {
            initial = lp_next(u, i, -1);
            if (initial < 0 || !lp_is(&u->lines[initial], "lda") || u->lines[initial].m8)
                continue;
            n = lp_immediate(&u->lines[initial]);
        }
        if (n < 0 || n > 65535)
            continue;
        unsigned delta = (unsigned)(sub ? -n : n) & 65535u;
        if (delta != 1 && delta != 2 && delta != 65535 && delta != 65534)
            continue;
        const char *op = delta <= 2 ? "    inc a" : "    dec a";
        if (initial >= 0) {
            /* Addition commutes. Read the original memory operand once
             * into A, then apply the literal steps without a carry setup. */
            size_t length;
            const char *operand = lp_operand(&u->lines[step], &length);
            lp_set(&u->lines[initial], "    lda %.*s", (int)length, operand);
        }
        lp_set(&u->lines[step], "%s", op);
        if (delta == 2 || delta == 65534)
            lp_set(&u->lines[i], "%s", op);
        else
            u->lines[i].deleted = 1;
        changed = 1;
    }
    return changed;
}

/* Commit a high result while it is still in A, before pulling the low word.
 * Both destination words are compiler scratch, and X must die at the store. */
static int lp_store_pulled_pair(LpUnit *u, Function *f, size_t at)
{
    int changed = 0;
    (void)f;
    (void)at;

    lp_liveness(u);

    for (unsigned i = 0; i < u->count; ++i) {
        LpLine *transfer = &u->lines[i];
        if (!lp_line_is(transfer, "tax") || transfer->m8 || transfer->x8)
            continue;
        int pull = lp_next(u, i, 1), low = pull < 0 ? -1 : lp_next(u, (unsigned)pull, 1);
        int high = low < 0 ? -1 : lp_next(u, (unsigned)low, 1);
        if (high < 0 || !lp_line_is(&u->lines[pull], "pla") || !lp_is(&u->lines[low], "sta") ||
            !lp_is(&u->lines[high], "stx") || (u->lines[high].out & LP_X))
            continue;
        size_t n, m;
        const char *a = lp_operand(&u->lines[low], &n), *b = lp_operand(&u->lines[high], &m);
        int first = lp_workspace_word(a, n), second = lp_workspace_word(b, m);
        if (first < 0 || second < 0 || lp_overlaps(&u->lines[high], second, first))
            continue;
        lp_set(transfer, "    sta %.*s", (int)m, b);
        u->lines[high].deleted = 1;
        ++changed;
    }
    return changed;
}

/* A discarded wide assignment sometimes protects its low word only
 * while X is stored through S. Rebase that store after dropping the save. */
static int lp_dead_stack_word_save(LpUnit *u, Function *f, size_t at)
{
    int changed = 0;
    (void)f;
    (void)at;

    lp_liveness(u);

    for (unsigned i = 0; i < u->count; ++i) {
        LpLine *push = &u->lines[i];
        int k, pull = -1;
        if (push->deleted || push->replace || !lp_line_is(push, "pha") || push->m8 || push->x8)
            continue;
        for (k = lp_next(u, i, 1); k >= 0; k = lp_next(u, (unsigned)k, 1)) {
            LpLine *cur = &u->lines[k];
            size_t n;
            const char *operand;
            if (cur->deleted || cur->replace || cur->m8 || cur->x8)
                break;
            if (lp_line_is(cur, "pla")) {
                if (!(cur->out & (LP_A | LP_N | LP_Z)))
                    pull = k;
                break;
            }
            if (cur->ends || lp_branch(cur) || cur->call || lp_stack_op(cur) ||
                cur->use == LP_ALL || lp_is(cur, "sep") || lp_is(cur, "rep") || lp_is(cur, "tsx") ||
                lp_is(cur, "tsc"))
                break;
            operand = lp_operand(cur, &n);
            if (lp_operand_has_s(operand, n)) {
                char *end;
                long displacement = strtol(operand, &end, 10);
                if (n < 3 || end != operand + n - 2 || end[0] != ',' || end[1] != 's' ||
                    displacement < 3 || displacement > 255)
                    break;
            }
        }
        if (pull < 0)
            continue;
        for (k = lp_next(u, i, 1); k >= 0 && k < pull; k = lp_next(u, (unsigned)k, 1)) {
            LpLine *cur = &u->lines[k];
            size_t n;
            const char *operand = lp_operand(cur, &n);
            if (lp_operand_has_s(operand, n)) {
                long displacement = strtol(operand, NULL, 10);
                lp_set(cur, "    %.3s %ld,s", cur->op, displacement - 2);
            }
        }
        push->deleted = u->lines[pull].deleted = 1;
        changed = 1;
    }
    return changed;
}

/* Test the old index after an update by comparing the new index with
 * the value it has when the old one is zero. N and Z describe old A. */
static int lp_post_index_test(LpUnit *u, Function *f, size_t at)
{
    (void)f;
    (void)at;
    lp_liveness(u);

    for (unsigned i = 0; i < u->count; ++i) {
        LpLine *move = &u->lines[i];
        int x = lp_line_is(move, "txa");
        if ((!x && !lp_line_is(move, "tya")) || move->m8 || move->x8)
            continue;
        int change = lp_next(u, i, 1), save = change < 0 ? -1 : lp_next(u, (unsigned)change, 1);
        int restore = save < 0 ? -1 : lp_next(u, (unsigned)save, 1);
        int test = restore < 0 ? -1 : lp_next(u, (unsigned)restore, 1);
        if (test < 0 || !(lp_is(&u->lines[test], "beq") || lp_is(&u->lines[test], "bne")) ||
            (u->lines[test].out & (LP_A | LP_C)) || !lp_line_is(&u->lines[save], x ? "tax" : "tay"))
            continue;
        int inc = lp_line_is(&u->lines[change], "inc a");
        if ((!inc && !lp_line_is(&u->lines[change], "dec a")) ||
            !lp_line_is(&u->lines[restore], inc ? "dec a" : "inc a"))
            continue;
        lp_set(move, "    %s", inc ? (x ? "inx" : "iny") : (x ? "dex" : "dey"));
        lp_set(&u->lines[change], "    %s #$%04X", x ? "cpx" : "cpy", inc ? 1 : 65535);
        u->lines[save].deleted = u->lines[restore].deleted = 1;
        return 1;
    }
    return 0;
}

static int lp_literal_stack_slot(const LpLine *l)
{
    size_t n;
    const char *p = lp_operand(l, &n);
    char *end;
    long offset = strtol(p, &end, 10);

    return n >= 3 && n <= 5 && end == p + n - 2 && p[n - 2] == ',' && p[n - 1] == 's' &&
                   offset > 0 && offset <= 255
               ? (int)offset
               : -1;
}

/* Combine literal byte fields before copying their words to the outgoing
 * argument area. Each push rebases the next load by two bytes. */
static int lp_literal_stack_argument_bytes(LpUnit *u, Function *f, size_t at)
{
    (void)at;
    if (u->indirect || lp_state.is_volatile || lp_state.parser->no_value_reuse ||
        body_asm_statements(f->body))
        return 0;
    int changed = 0;

    for (unsigned i = 0; i < u->count; ++i) {
        if (!lp_line_is(&u->lines[i], "sep #$20"))
            continue;
        unsigned char known[256] = {0}, bytes[256];
        int prev = lp_next(u, i, -1), k = lp_next_mode(u, i);
        long literal =
            prev >= 0 && lp_is(&u->lines[prev], "lda") ? lp_immediate(&u->lines[prev]) : -1;
        unsigned stores = 0;
        while (k >= 0 && (unsigned)k <= i + 96 && !lp_line_is(&u->lines[k], "rep #$20")) {
            LpLine *line = &u->lines[k];
            if (!line->m8)
                break;
            if (lp_is(line, "lda") && lp_immediate(line) >= 0)
                literal = lp_immediate(line);
            else if (lp_is(line, "sta") && literal >= 0) {
                int offset = lp_literal_stack_slot(line);
                if (offset < 0)
                    break;
                bytes[offset] = (unsigned char)literal;
                known[offset] = 1;
                ++stores;
            } else
                break;
            k = lp_next_mode(u, (unsigned)k);
        }
        if (k < 0 || stores < 2 || !lp_line_is(&u->lines[k], "rep #$20"))
            continue;
        int pushed = 0;
        for (k = lp_next_mode(u, (unsigned)k); k >= 0; k = lp_next_mode(u, (unsigned)k)) {
            LpLine *load = &u->lines[k];
            if (!lp_is(load, "lda") || load->m8)
                break;
            int offset = lp_literal_stack_slot(load) - pushed;
            int push = lp_next_mode(u, (unsigned)k);
            if (offset < 1 || offset >= 255 || !known[offset] || !known[offset + 1] || push < 0 ||
                !lp_line_is(&u->lines[push], "pha") || u->lines[push].m8)
                break;
            unsigned value = (unsigned)bytes[offset] | ((unsigned)bytes[offset + 1] << 8);
            lp_set(load, "    lda #$%04X", value);
            pushed += 2;
            k = push;
            changed = 1;
        }
    }
    return changed;
}

/* A retained index can consume a literal directly once A is dead */
static int lp_literal_to_index(LpUnit *u, Function *f, size_t at)
{
    int changed = 0;
    (void)f;
    (void)at;

    lp_liveness(u);

    for (unsigned i = 0; i < u->count; ++i) {
        LpLine *load = &u->lines[i];
        if (!lp_is(load, "lda") || load->m8 || load->x8)
            continue;
        size_t n;
        const char *operand = lp_operand(load, &n);
        if (n < 2 || operand[0] != '#')
            continue;
        int next = lp_next(u, i, 1);
        if (next < 0 || (u->lines[next].out & LP_A))
            continue;
        int x = lp_line_is(&u->lines[next], "tax");
        if (!x && !lp_line_is(&u->lines[next], "tay"))
            continue;
        lp_set(load, "    %s %.*s", x ? "ldx" : "ldy", (int)n, operand);
        u->lines[next].deleted = 1;
        changed = 1;
    }
    return changed;
}

static int lp_push_immediate_word(LpUnit *u, Function *f, size_t at)
{
    int changed = 0;
    (void)f;
    (void)at;

    lp_liveness(u);

    for (unsigned i = 0; i < u->count; ++i) {
        LpLine *load = &u->lines[i];
        size_t n;
        const char *operand = lp_operand(load, &n);
        if (load->m8 || !lp_is(load, "lda") || n < 2 || operand[0] != '#')
            continue;
        int push = lp_next(u, i, 1);
        if (push < 0 || !lp_line_is(&u->lines[push], "pha"))
            continue;
        if (u->lines[push].out & (LP_A | LP_N | LP_Z)) {
            int next = lp_next(u, (unsigned)push, 1);
            if (next < 0)
                continue;
            LpLine *call = &u->lines[next];
            Symbol *callee = call->call && !call->ends ? lp_callee(call) : NULL;
            Function *body = callee ? inl.by_symbol[callee - lp_state.parser->symbols] : NULL;

            /* A known scalar result replaces A after a stack-only
             * argument. The call still gets exactly the same bytes. */
            if (!body || callee->interrupt || callee->variadic || structure_object(callee->type) ||
                reg_width(callee->type) != 2 || (call->use & LP_A) || (call->out & (LP_N | LP_Z)) ||
                body_asm_statements(body->body) || !inl_definitely_returns(body->body))
                continue;
        }
        lp_set(load, "    pea %.*s", (int)n - 1, operand + 1);
        u->lines[push].deleted = 1;
        ++changed;
    }
    return changed;
}

/* Delay an index literal past an independent store when its only purpose
 * is to load A for the next value. */
static int lp_delay_index_literal(LpUnit *u, Function *f, size_t at)
{
    (void)f;
    (void)at;
    lp_liveness(u);

    for (unsigned i = 0; i < u->count; ++i) {
        LpLine *load = &u->lines[i];
        int x = lp_is(load, "ldx");
        if ((!x && !lp_is(load, "ldy")) || load->m8 || load->x8)
            continue;
        long value = lp_immediate(load);
        if (value < 0 || value > 65535)
            continue;
        unsigned reg = x ? LP_X : LP_Y;
        int store = lp_next(u, i, 1);
        if (store < 0 || !lp_is(&u->lines[store], "sta") || (u->lines[store].use & reg))
            continue;
        int move = lp_next(u, (unsigned)store, 1);
        if (move < 0 || !lp_line_is(&u->lines[move], x ? "txa" : "tya") ||
            (u->lines[move].out & reg))
            continue;
        lp_set(&u->lines[move], "    lda #$%04lX", value);
        load->deleted = 1;
        return 1;
    }
    return 0;
}

/* A zero index on a named absolute load or store selects the same address
 * without index calculation. Keep the register setup if later code uses it. */
/* A published pointer to a byte inside the current stack frame can still
 * be read directly through its frame index. Preserve the publication. */
static int lp_published_frame_read(LpUnit *u, Function *f, size_t at)
{
    (void)at;
    if (u->indirect || lp_state.is_volatile || !f->slots || body_asm_statements(f->body))
        return 0;
    int known, changed = 0;
    unsigned char *targets = lp_local_targets(u, &known);
    lp_liveness(u);

    for (unsigned i = 0; i < u->count && !changed; ++i) {
        LpLine *load = &u->lines[i];
        if (!lp_line_is(load, "lda a:$0000,x") || load->m8 || load->x8 || (load->out & LP_X))
            continue;
        int transfer = lp_next_fallthrough(u, i, -1, targets, known);
        int store =
            transfer < 0 ? -1 : lp_next_fallthrough(u, (unsigned)transfer, -1, targets, known);
        if (store < 0 || !lp_line_is(&u->lines[transfer], "tax") || !lp_is(&u->lines[store], "sta"))
            continue;
        int pos = lp_next_fallthrough(u, (unsigned)store, -1, targets, known), offset = 0;
        while (pos >= 0 && lp_line_is(&u->lines[pos], "inc a")) {
            ++offset;
            pos = lp_next_fallthrough(u, (unsigned)pos, -1, targets, known);
        }
        if (pos < 0 || !offset || (unsigned)offset > f->slots || !lp_line_is(&u->lines[pos], "tya"))
            continue;
        do {
            pos = lp_next_fallthrough(u, (unsigned)pos, -1, targets, known);
        } while (pos >= 0 && !(u->lines[pos].def & LP_Y) && !u->lines[pos].call &&
                 !u->lines[pos].ends);
        if (pos < 0 || !lp_line_is(&u->lines[pos], "tay"))
            continue;
        pos = lp_next(u, (unsigned)pos, -1);
        if (pos < 0 || !lp_line_is(&u->lines[pos], "tsc"))
            continue;
        u->lines[transfer].deleted = 1;
        lp_set(load, "    lda a:$%04X,y", offset);
        changed = 1;
    }
    free(targets);
    return changed;
}

/* Testing a word index for zero needs only a transfer when A and the
 * carry produced by the comparison are dead. N and Z match exactly. */
static int lp_test_index(LpUnit *u, Function *f, size_t at)
{
    (void)f;
    (void)at;
    lp_liveness(u);
    int changed = 0;

    for (unsigned i = 0; i < u->count; ++i) {
        LpLine *l = &u->lines[i];
        if ((!lp_is(l, "cpx") && !lp_is(l, "cpy")) || l->m8 || l->x8 || lp_immediate(l) != 0 ||
            (l->out & (LP_A | LP_C)))
            continue;
        lp_set(l, "    %s", lp_is(l, "cpx") ? "txa" : "tya");
        ++changed;
    }
    return changed;
}

static int lp_zero_index_address(LpUnit *u, Function *f, size_t at)
{
    (void)f;
    (void)at;
    lp_liveness(u);

    for (unsigned i = 0; i < u->count; ++i) {
        LpLine *zero = &u->lines[i];
        int x = lp_is(zero, "ldx");
        if ((!x && !lp_is(zero, "ldy")) || zero->x8 || lp_immediate(zero) != 0)
            continue;
        int next = lp_next(u, i, 1);
        if (next < 0)
            continue;
        LpLine *access = &u->lines[next];
        if (!lp_is(access, "lda") && !lp_is(access, "sta"))
            continue;
        size_t n;
        const char *p = lp_operand(access, &n);
        if (n < 5 || p[0] != 'a' || p[1] != ':' || p[n - 2] != ',' || p[n - 1] != (x ? 'x' : 'y') ||
            !pr_named(p, n - 2))
            continue;
        lp_set(access, "    %.3s %.*s", access->op, (int)n - 2, p);
        unsigned needed = x ? LP_X : LP_Y;
        if (lp_is(access, "sta"))
            needed |= LP_N | LP_Z;
        if (!(access->out & needed))
            zero->deleted = 1;
        return 1;
    }
    return 0;
}

/* Taking a named near address through A and X need not hide the
 * identity of the subsequent zero-displacement load. */
static int lp_direct_relocated_read(LpUnit *u, Function *f, size_t at)
{
    (void)at;
    if (u->indirect || lp_state.is_volatile || lp_state.parser->no_indexed_operands ||
        lp_state.parser->no_value_reuse || body_asm_statements(f->body))
        return 0;
    lp_liveness(u);

    for (unsigned i = 0; i < u->count; ++i) {
        LpLine *load = &u->lines[i];
        if (load->m8 || load->x8 || !lp_is(load, "lda"))
            continue;
        size_t n;
        const char *operand = lp_operand(load, &n);
        if (n < 12 || n > 120 || strncmp(operand, "#.loword(_", 10) || operand[n - 1] != ')')
            continue;
        char direct[128];
        snprintf(direct, sizeof direct, "a:%.*s", (int)n - 1, operand + 1);
        if (!pr_named(direct, n + 1))
            continue;
        for (unsigned j = i + 1; j < u->count && j - i < 28; ++j) {
            LpLine *line = &u->lines[j];
            if (lp_internal_path_marker(u, j, i))
                continue;
            if (!line->op || line->m8 || line->x8)
                break;
            if (lp_line_is(line, "tax")) {
                int read = lp_next(u, j, 1);
                if (read < 0 || !lp_line_is(&u->lines[read], "lda a:$0000,x") ||
                    u->lines[read].m8 || u->lines[read].x8)
                    break;
                lp_set(&u->lines[read], "    lda %s", direct);
                if (!(u->lines[read].out & LP_X))
                    line->deleted = 1;
                return 1;
            }
            if (!lp_is(line, "sta") && !lp_is(line, "stx") && !lp_is(line, "sty") &&
                !lp_is(line, "stz"))
                break;
        }
    }
    return 0;
}

/* Move an adjusted index directly to X or Y when the intermediate
 * accumulator copy does not escape the transfer. */
static int lp_index_transfer_steps(LpUnit *u, Function *f, size_t at)
{
    (void)f;
    (void)at;
    lp_liveness(u);

    for (unsigned i = 0; i < u->count; ++i) {
        LpLine *start = &u->lines[i];
        int from_x = lp_line_is(start, "txa");
        if ((!from_x && !lp_line_is(start, "tya")) || start->m8 || start->x8)
            continue;
        int first = lp_next(u, i, 1), copy = -1;
        if (first >= 0 && lp_line_is(&u->lines[first], from_x ? "tay" : "tax")) {
            copy = first;
            first = lp_next(u, (unsigned)copy, 1);
        }
        int end = first;
        while (end >= 0 &&
               (lp_line_is(&u->lines[end], "inc a") || lp_line_is(&u->lines[end], "dec a")))
            end = lp_next(u, (unsigned)end, 1);
        if (end < 0 || end == first)
            continue;
        int to_x = lp_line_is(&u->lines[end], "tax");
        if (!to_x && !lp_line_is(&u->lines[end], "tay"))
            continue;
        int keep_a = (u->lines[end].out & LP_A) != 0;
        if ((keep_a || copy >= 0) && from_x != to_x)
            continue;
        if (copy >= 0)
            lp_set(&u->lines[copy], "    %s", from_x ? "txy" : "tyx");
        if (from_x == to_x)
            start->deleted = 1;
        else
            lp_set(start, "    %s", to_x ? "tyx" : "txy");
        for (int k = first; k != end; k = lp_next(u, (unsigned)k, 1)) {
            int inc = lp_line_is(&u->lines[k], "inc a");
            lp_set(&u->lines[k], "    %s", to_x ? (inc ? "inx" : "dex") : (inc ? "iny" : "dey"));
        }
        if (keep_a)
            lp_set(&u->lines[end], "    %s", to_x ? "txa" : "tya");
        else
            u->lines[end].deleted = 1;
        return 1;
    }
    return 0;
}

/* (A + c) * 2^k + d has one combined word displacement. Its final
 * carry and overflow differ from the two-add sequence and must be dead. */
static int lp_scaled_displacement(LpUnit *u, Function *f, size_t at)
{
    (void)f;
    (void)at;
    lp_liveness(u);

    for (unsigned i = 0; i < u->count; ++i) {
        if (!lp_line_is(&u->lines[i], "clc"))
            continue;
        int first = lp_next(u, i, 1);
        if (first < 0 || !lp_is(&u->lines[first], "adc") || u->lines[first].m8)
            continue;
        long add = lp_immediate(&u->lines[first]);
        if (add < 0 || add > 65535)
            continue;
        int k = lp_next(u, (unsigned)first, 1);
        unsigned shifts = 0;
        while (k >= 0 && lp_line_is(&u->lines[k], "asl a") && !u->lines[k].m8 && shifts < 15) {
            ++shifts;
            k = lp_next(u, (unsigned)k, 1);
        }
        if (!shifts || k < 0 || !lp_line_is(&u->lines[k], "clc"))
            continue;
        int last = lp_next(u, (unsigned)k, 1);
        if (last < 0 || !lp_is(&u->lines[last], "adc") || u->lines[last].m8 ||
            (u->lines[last].out & (LP_C | LP_V)))
            continue;
        long tail = lp_immediate(&u->lines[last]);
        if (tail < 0 || tail > 65535)
            continue;
        lp_set(&u->lines[last], "    adc #$%04X",
               (((unsigned)add << shifts) + (unsigned)tail) & 65535u);
        u->lines[i].deleted = u->lines[first].deleted = 1;
        return 1;
    }
    return 0;
}

/* The zero flag already represents both scalar truth values across an
 * inlined, effect-free arm. Keep marker paths and the original branch. */
static int lp_materialized_zero_flag(LpUnit *u, Function *f, size_t at)
{
    int known, changed = 0;
    unsigned char *targets = lp_local_targets(u, &known);
    (void)f;
    (void)at;

    if (!known) {
        free(targets);
        return 0;
    }
    lp_liveness(u);

    for (unsigned i = 0; i < u->count; ++i) {
        LpLine *br = &u->lines[i];
        if (!(lp_is(br, "beq") || lp_is(br, "bne")) || br->target != (int)i + 2 ||
            !lp_is(&u->lines[i + 1], "jmp") || u->lines[i + 1].target <= br->target ||
            targets[br->target] != 1 || targets[u->lines[i + 1].target] != 1)
            continue;
        unsigned branch = (unsigned)u->lines[i + 1].target, first = i + 3, second = branch + 1;
        while (first < branch && lp_fallthrough_marker(&u->lines[first], first, targets, known))
            ++first;
        if (first >= branch || !lp_is(&u->lines[first], "lda") || u->lines[first].m8)
            continue;
        long high = lp_immediate(&u->lines[first]);
        if (high < 0 || high > 65535)
            continue;
        int skip = lp_next(u, first, 1);
        if (skip < 0 || (unsigned)skip + 1 != branch || !lp_is(&u->lines[skip], "jmp") ||
            u->lines[skip].target <= (int)branch)
            continue;
        unsigned join = (unsigned)u->lines[skip].target;
        while (second < join && lp_fallthrough_marker(&u->lines[second], second, targets, known))
            ++second;
        if (second >= join || !lp_is(&u->lines[second], "lda") || u->lines[second].m8)
            continue;
        long low = lp_immediate(&u->lines[second]);
        if (low < 0 || low > 65535 || !!low == !!high)
            continue;
        unsigned end = second + 1;
        while (end < join && lp_fallthrough_marker(&u->lines[end], end, targets, known))
            ++end;
        int test = lp_next(u, join, 1);
        int compare = -1;
        if (test >= 0 && lp_is(&u->lines[test], "cmp") && !u->lines[test].m8) {
            long literal = lp_immediate(&u->lines[test]);
            if (literal < 0 || targets[join] != 1 || (low == literal) == (high == literal))
                continue;

            /* The consuming equality branch observes Z from the compare.
             * Treat an unequal arm as nonzero for the same flag proof. */
            compare = test;
            test = lp_next(u, (unsigned)test, 1);
            if (test >= 0 && end == join && (u->lines[test].out & LP_A) &&
                !(u->lines[test].out & (LP_N | LP_Z | LP_C)) &&
                (lp_is(&u->lines[test], "beq") || lp_is(&u->lines[test], "bne"))) {
                if ((high == 0) != (high == literal)) {
                    size_t n;
                    const char *target = lp_operand(&u->lines[test], &n);
                    lp_set(&u->lines[test], "    %s %.*s",
                           lp_is(&u->lines[test], "beq") ? "bne" : "beq", (int)n, target);
                }
                u->lines[compare].deleted = 1;
                changed = 1;
                continue;
            }
            high = high != literal;
        }
        if (end != join || test < 0 || (compare >= 0 && (u->lines[test].out & LP_C)) ||
            !(lp_is(&u->lines[test], "beq") || lp_is(&u->lines[test], "bne")) ||
            (u->lines[test].out & (LP_A | LP_N)))
            continue;
        if (!!high != lp_is(br, "bne")) {
            LpLine *consumer = &u->lines[test];
            size_t n;
            const char *target = lp_operand(consumer, &n);
            if (targets[join] != 1 || (consumer->out & LP_Z))
                continue;
            lp_set(consumer, "    %s %.*s", lp_is(consumer, "beq") ? "bne" : "beq", (int)n, target);
        }
        if (compare >= 0)
            u->lines[compare].deleted = 1;
        u->lines[first].deleted = u->lines[second].deleted = 1;
        changed = 1;
    }
    free(targets);
    return changed;
}

/* An A8 load preserves the hidden accumulator high byte */
static int lp_zero_high_across_byte_load(LpUnit *u, Function *f, size_t at)
{
    int zero_high = 0, low = -1, changed = 0;
    (void)f;
    (void)at;

    lp_liveness(u);

    for (unsigned i = 0; i < u->count; ++i) {
        LpLine *l = &u->lines[i];
        if (!l->op) {
            if (l->length && (l->text[0] == ';' || !strncmp(l->text, ".a8\n", 4) ||
                              !strncmp(l->text, ".a16\n", 5)))
                continue;
            zero_high = 0;
            low = -1;
            continue;
        }
        if (lp_is(l, "lda")) {
            long value = lp_immediate(l);
            if (l->m8 && value >= 0 && low == (int)(value & 255) &&
                !(lp_byte_live_out(u, i) & (LP_N | LP_Z))) {
                l->deleted = 1;
                ++changed;
                continue;
            }
            low = value < 0 ? -1 : (int)(value & 255);
        } else if (!(lp_line_is(l, "sep #$20") || lp_line_is(l, "rep #$20") || lp_is(l, "sta")))
            low = -1;
        if (!l->m8 && (lp_is(l, "lda") || lp_is(l, "and"))) {
            long value = lp_immediate(l);
            if (value == 255 && lp_is(l, "and") && zero_high && !(l->out & (LP_N | LP_Z))) {
                l->deleted = 1;
                changed = 1;
            }
            zero_high = value >= 0 && value <= 255;
        } else if (!(lp_line_is(l, "sep #$20") || lp_line_is(l, "rep #$20") || lp_is(l, "sta") ||
                     (l->m8 && lp_is(l, "lda"))))
            zero_high = 0;
    }
    return changed;
}

/* Fold a word shift sequence selected after source-level folding, such
 * as a byte exchange followed by shifts. XBA sets byte-sized N and Z. */
static int lp_literal_shifts(LpUnit *u, Function *f, size_t at)
{
    int changed = 0;
    (void)f;
    (void)at;

    lp_liveness(u);

    for (unsigned i = 0; i < u->count; ++i) {
        LpLine *load = &u->lines[i];
        long initial = lp_immediate(load);
        if (!lp_is(load, "lda") || load->m8 || initial < 0 || initial > 65535)
            continue;
        unsigned value = (unsigned)initial, final = value;
        int last = -1, k = (int)i, carry = 0;
        while ((k = lp_next(u, (unsigned)k, 1)) >= 0) {
            LpLine *l = &u->lines[k];
            int swap = lp_line_is(l, "xba");
            if (swap)
                value = ((value >> 8) | (value << 8)) & 65535;
            else if (lp_line_is(l, "asl a")) {
                value = (value << 1) & 65535;
                carry = 1;
            } else if (lp_line_is(l, "lsr a")) {
                value >>= 1;
                carry = 1;
            } else
                break;
            if ((!carry || !(l->out & LP_C)) && (!swap || !(l->out & (LP_N | LP_Z)))) {
                last = k;
                final = value;
            }
        }
        if (last < 0)
            continue;
        lp_set(load, "    lda #$%04X", final);
        for (k = (int)i; k != last;) {
            k = lp_next(u, (unsigned)k, 1);
            u->lines[k].deleted = 1;
        }
        ++changed;
        i = (unsigned)last;
    }
    return changed;
}

/* A literal low limb decides whether the known high limb is stepped.
 * Fold both modular words after checking that the arithmetic flags die. */
static int lp_literal_limb_carry(LpUnit *u, Function *f, size_t at)
{
    (void)at;
    if (u->indirect || f->symbol->interrupt || body_asm_statements(f->body))
        return 0;
    lp_liveness(u);

    for (unsigned i = 0; i < u->count; ++i) {
        int second = lp_next(u, i, 1);
        if (second < 0)
            continue;
        LpLine *low = &u->lines[i], *high = &u->lines[second];
        if (lp_is(low, "ldx")) {
            LpLine *swap = low;
            low = high;
            high = swap;
        }
        if (low->m8 || high->x8 || !lp_is(low, "lda") || !lp_is(high, "ldx"))
            continue;
        long a = lp_immediate(low), x = lp_immediate(high);
        if (a < 0 || a > 65535 || x < 0 || x > 65535)
            continue;
        int carry = lp_next(u, (unsigned)second, 1);
        int op = carry < 0 ? -1 : lp_next(u, (unsigned)carry, 1);
        int branch = op < 0 ? -1 : lp_next(u, (unsigned)op, 1);
        int step = branch < 0 ? -1 : lp_next(u, (unsigned)branch, 1);
        if (step < 0)
            continue;
        int subtract = lp_line_is(&u->lines[carry], "sec");
        if ((!subtract && !lp_line_is(&u->lines[carry], "clc")) || u->lines[op].m8 ||
            !lp_is(&u->lines[op], subtract ? "sbc" : "adc") ||
            !lp_is(&u->lines[branch], subtract ? "bcs" : "bcc") ||
            !lp_line_is(&u->lines[step], subtract ? "dex" : "inx") || u->lines[step].x8)
            continue;
        long operand = lp_immediate(&u->lines[op]);
        int join = u->lines[branch].target;
        if (operand < 0 || operand > 65535 || join <= step ||
            u->lines[join].first_incoming != branch || u->lines[branch].next_incoming >= 0 ||
            u->lines[join].live & LP_FLAGS)
            continue;
        int j = step + 1;
        while (j < join && u->lines[j].length && u->lines[j].text[0] == ';')
            ++j;
        if (j != join)
            continue;
        long value = subtract ? a - operand : a + operand;
        if (value < 0)
            --x;
        if (value > 65535)
            ++x;
        lp_set(low, "    lda #$%04X", (unsigned)value & 65535u);
        lp_set(high, "    ldx #$%04X", (unsigned)x & 65535u);
        u->lines[carry].deleted = u->lines[op].deleted = u->lines[branch].deleted =
            u->lines[step].deleted = 1;
        return 1;
    }
    return 0;
}

static int lp_const_branches(LpUnit *u, Function *f, size_t at)
{
    unsigned i;
    int changed = 0;
    (void)f;
    (void)at;
    int known_targets;
    int marker_literals =
        !body_asm_statements(f->body) && !find_symbol(lp_state.parser, "$basic_asm");
    unsigned char *targets = lp_local_targets(u, &known_targets);

    lp_liveness(u);

    for (i = 0; i < u->count; ++i) {
        LpLine *l = &u->lines[i];
        int k, j, s;
        long v, w;
        if (lp_is(l, "lda") && !l->replace && !l->deleted && (v = lp_immediate(l)) >= 0) {
            int last = (int)i;
            while ((k = lp_next_fallthrough(u, (unsigned)last, 1, targets, known_targets)) >= 0 &&
                   !u->lines[k].deleted && !u->lines[k].replace &&
                   (lp_is(&u->lines[k], "sta") || lp_is(&u->lines[k], "stx") ||
                    lp_is(&u->lines[k], "sty") || lp_is(&u->lines[k], "stz")))
                last = k;
            if (last != (int)i && k >= 0 && lp_branch(&u->lines[k])) {
                unsigned sign = l->m8 ? 128u : 32768u, value = (unsigned)v & (2 * sign - 1);
                changed += lp_fold_branches(u, last, value == 0, -1, (value & sign) != 0, -1);
            }
        }
        if (l->m8 && lp_is(l, "lda") && !l->replace && !l->deleted && (v = lp_immediate(l)) >= 0 &&
            (k = lp_next(u, i, 1)) >= 0 && lp_line_is(&u->lines[k], "rep #$20") &&
            (unsigned)k + 1 < u->count && u->lines[k + 1].length == 4 &&
            !strncmp(u->lines[k + 1].text, ".a16", 4)) {
            /* Restoring A16 leaves the byte load's N/Z unchanged */
            int branch = lp_next(u, (unsigned)k + 1, 1);
            if (branch >= 0 && lp_branch(&u->lines[branch]))
                changed += lp_fold_branches(u, k + 1, (v & 255) == 0, -1, (v & 128) != 0, -1);
        }
        if (l->m8 && lp_is(l, "lda") && !l->replace && !l->deleted && (v = lp_immediate(l)) >= 0 &&
            (k = lp_next(u, i, 1)) >= 0 && lp_is(&u->lines[k], "cmp") && u->lines[k].m8 &&
            !u->lines[k].replace && !u->lines[k].deleted && (w = lp_immediate(&u->lines[k])) >= 0) {
            int end = k, rep = lp_next(u, (unsigned)k, 1);
            if (rep >= 0 && lp_line_is(&u->lines[rep], "rep #$20") &&
                (unsigned)rep + 1 < u->count && u->lines[rep + 1].length == 4 &&
                !strncmp(u->lines[rep + 1].text, ".a16", 4))
                end = rep + 1;
            unsigned left = (unsigned)v & 255u, right = (unsigned)w & 255u;
            changed += lp_fold_branches(u, end, left == right, left >= right,
                                        ((left - right) & 128u) != 0, -1);
            continue;
        }
        if (!l->m8 && !l->x8 && !l->replace && !l->deleted &&
            (lp_is(l, "lda") || lp_is(l, "ldx") || lp_is(l, "ldy"))) {
            size_t n;
            const char *p = lp_operand(l, &n);
            size_t prefix = n > 10 && !strncmp(p, "#.loword(", 9)      ? 9
                            : n > 12 && !strncmp(p, "#.bankbyte(", 11) ? 11
                                                                       : 0;
            int relocated = 0;
            if (prefix && p[n - 1] == ')') {
                size_t h = prefix;
                while (h < n - 1 && (isalnum((unsigned char)p[h]) || p[h] == '_' || p[h] == '+' ||
                                     p[h] == '-' || p[h] == '$'))
                    ++h;
                relocated = h == n - 1;
            }
            long index = lp_immediate(l);
            if (lp_is(l, "lda") && !marker_literals)
                index = -1;
            int earlier = changed;
            if (relocated || index >= 0) {
                unsigned reg = lp_is(l, "lda") ? LP_A : lp_is(l, "ldx") ? LP_X : LP_Y;
                const char *compare = reg == LP_A ? "cmp" : reg == LP_X ? "cpx" : "cpy";
                for (k = (int)i;
                     (k = lp_next_fallthrough(u, (unsigned)k, 1, targets, known_targets)) >= 0;) {
                    LpLine *test = &u->lines[k];
                    if (test->deleted || test->replace || test->m8 || test->x8 || test->call ||
                        test->ends || lp_branch(test) || test->def & reg)
                        break;
                    if (!lp_is(test, compare))
                        continue;
                    if (relocated && lp_operand_is(test, p, n)) {
                        changed += lp_fold_branches(u, k, 1, 1, 0, -1);
                        break;
                    }
                    long right = lp_immediate(test);
                    if (index >= 0 && right >= 0) {
                        unsigned left = (unsigned)index & 65535u, value = (unsigned)right & 65535u;
                        changed += lp_fold_branches(u, k, left == value, left >= value,
                                                    ((left - value) & 32768u) != 0, -1);
                        break;
                    }
                }
            }
            if (changed != earlier)
                continue;
        }
        if (!lp_is(l, "lda") || l->m8 || l->replace || l->deleted || (v = lp_immediate(l)) < 0)
            continue;
        if ((k = lp_next(u, i, 1)) < 0)
            continue;
        if (u->lines[k].replace || u->lines[k].deleted)
            continue;
        if (!u->lines[k].m8 &&
            (lp_line_is(&u->lines[k], "inc a") || lp_line_is(&u->lines[k], "dec a"))) {
            /* Both forms set word N/Z and preserve incoming C/V */
            unsigned value = ((unsigned)v + (lp_is(&u->lines[k], "inc") ? 1u : 65535u)) & 65535;
            lp_set(l, "    lda #$%04X", value);
            u->lines[k].deleted = 1;
            ++changed;
            continue;
        }
        {
            int test = k;
            unsigned value = (unsigned)v;

            /* Stores and index-register setup leave the known A unchanged.
          * An immediate CMP supplies new N/Z/C before the branch. */
            while (test >= 0 && !u->lines[test].replace && !u->lines[test].deleted) {
                if (!u->lines[test].m8 && lp_line_is(&u->lines[test], "inc a"))
                    value = (value + 1) & 65535u;
                else if (!u->lines[test].m8 && lp_line_is(&u->lines[test], "dec a"))
                    value = (value - 1) & 65535u;
                else if (!(lp_is(&u->lines[test], "ldx") || lp_is(&u->lines[test], "ldy") ||
                           lp_is(&u->lines[test], "stx") || lp_is(&u->lines[test], "sty") ||
                           lp_is(&u->lines[test], "sta") || lp_is(&u->lines[test], "stz") ||
                           lp_line_is(&u->lines[test], "tax") ||
                           lp_line_is(&u->lines[test], "tay")))
                    break;
                do {
                    ++test;
                } while (
                    (unsigned)test < u->count &&
                    lp_fallthrough_marker(&u->lines[test], (unsigned)test, targets, known_targets));
                if ((unsigned)test == u->count)
                    test = -1;
            }
            if (test >= 0 && test != k && !u->lines[test].replace && !u->lines[test].deleted &&
                !u->lines[test].m8 && (w = lp_immediate(&u->lines[test])) >= 0 &&
                (lp_is(&u->lines[test], "and") || lp_is(&u->lines[test], "ora") ||
                 lp_is(&u->lines[test], "eor"))) {
                LpLine *bitwise = &u->lines[test];
                unsigned result = lp_is(bitwise, "and")   ? value & (unsigned)w
                                  : lp_is(bitwise, "ora") ? value | (unsigned)w
                                                          : value ^ (unsigned)w;
                lp_set(bitwise, "    lda #$%04X", result & 65535u);
                ++changed;
                continue;
            }
            if (test >= 0 && test != k && !u->lines[test].replace && !u->lines[test].deleted &&
                lp_is(&u->lines[test], "cmp") && !u->lines[test].m8 &&
                (w = lp_immediate(&u->lines[test])) >= 0) {
                unsigned diff = (value - (unsigned)w) & 65535u;
                changed += lp_fold_branches(u, test, diff == 0, value >= (unsigned)w,
                                            (diff >> 15) & 1, -1);
                continue;
            }
        }
        if ((lp_is(&u->lines[k], "and") || lp_is(&u->lines[k], "ora") ||
             lp_is(&u->lines[k], "eor")) &&
            !u->lines[k].m8 && (w = lp_immediate(&u->lines[k])) >= 0) {
            long r = lp_is(&u->lines[k], "and")   ? v & w
                     : lp_is(&u->lines[k], "ora") ? v | w
                                                  : v ^ w;
            lp_set(l, "    lda #$%04lX", r & 0xFFFF);
            u->lines[k].deleted = 1;
            ++changed;
            continue;
        }
        if (lp_is(&u->lines[k], "cmp") && !u->lines[k].m8 &&
            (w = lp_immediate(&u->lines[k])) >= 0) {
            unsigned diff = (unsigned)(v - w) & 0xFFFFu;
            changed += lp_fold_branches(u, k, diff == 0, v >= w, (diff >> 15) & 1, -1);
            continue;
        }
        if (lp_branch(&u->lines[k])) {
            changed += lp_fold_branches(u, (int)i, v == 0, -1, (int)(v >> 15) & 1, -1);
            continue;
        }

        /* A shifted constant: the carry out must be dead */
        if (lp_line_is(&u->lines[k], "asl a") && !u->lines[k].m8 && !(u->lines[k].out & LP_C)) {
            lp_set(l, "    lda #$%04lX", (v << 1) & 0xFFFF);
            u->lines[k].deleted = 1;
            ++changed;
            continue;
        }

        /* Copies and stores of the constant leave A, C and V alone */
        for (j = k; j >= 0 && !u->lines[j].replace && !u->lines[j].deleted &&
                    (lp_line_is(&u->lines[j], "tay") || lp_line_is(&u->lines[j], "tax") ||
                     (lp_is(&u->lines[j], "sta") && !u->lines[j].m8));)
            j = lp_next(u, (unsigned)j, 1);
        if (j < 0 || (!lp_line_is(&u->lines[j], "sec") && !lp_line_is(&u->lines[j], "clc")) ||
            u->lines[j].replace || u->lines[j].deleted)
            continue;
        if ((s = lp_next(u, (unsigned)j, 1)) < 0 || u->lines[s].replace || u->lines[s].deleted ||
            u->lines[s].m8)
            continue;
        {
            LpLine *o = &u->lines[s];
            int sub = lp_line_is(&u->lines[j], "sec");
            if (!(sub ? lp_is(o, "sbc") : lp_is(o, "adc")))
                continue;
            if ((w = lp_immediate(o)) >= 0) {
                long r = (sub ? v - w : v + w) & 0xFFFF;
                int c = sub ? v >= w : v + w > 0xFFFF,
                    ov = (int)(((sub ? (v ^ w) : ~(v ^ w)) & (v ^ r) & 0x8000) != 0), folded;
                folded = lp_fold_branches(u, s, r == 0, c, (int)(r >> 15) & 1, ov);
                if (folded) {
                    changed += folded;
                    continue;
                }
                if (j == k && !(o->out & (LP_C | LP_V))) {
                    lp_set(l, "    lda #$%04lX", r);
                    u->lines[j].deleted = 1;
                    o->deleted = 1;
                    ++changed;
                }
            } else if (!v && !sub && j == k && !(o->out & (LP_C | LP_V))) {
                /* 0 + M is M; LDA sets N and Z alike */
                size_t m;
                const char *p = lp_operand(o, &m);
                lp_set(l, "    lda %.*s", (int)m, p);
                u->lines[j].deleted = 1;
                o->deleted = 1;
                ++changed;
            }
        }
    }

    for (i = 0; i < u->count; ++i) {
        LpLine *l = &u->lines[i];
        unsigned t;
        if (l->deleted || l->replace || !l->op || l->call || (!lp_branch(l) && !lp_is(l, "jmp")) ||
            l->target < 0 || (unsigned)l->target <= i)
            continue;
        for (t = i + 1; t < u->count; ++t) {
            LpLine *m = &u->lines[t];
            if (t == (unsigned)l->target) {
                l->deleted = 1;
                ++changed;
                break;
            }
            if (!m->deleted && m->length && !m->label && m->text[0] != ';')
                break;
        }
    }
    free(targets);
    return changed;
}

/* Instructions no path from the entry reaches */
static int lp_unreachable(LpUnit *u, Function *f, size_t at)
{
    unsigned i, *work, top = 0, first = u->count;
    char *seen;
    int changed = 0;
    (void)f;
    (void)at;

    if (u->indirect)
        return 0;

    for (i = 0; i < u->count && first == u->count; ++i)
        if (u->lines[i].op)
            first = i;
    if (first == u->count)
        return 0;
    seen = calloc(u->count, 1);
    work = malloc((u->count + 1) * sizeof *work);
    if (!seen || !work) {
        fputs("out of memory emitting assembly\n", stderr);
        exit(EXIT_FAILURE);
    }
    work[top++] = 0;
    seen[0] = 1;

    /* Named labels other than compiler-local ones may be entered from outside */
    for (i = 0; i < u->count; ++i) {
        const LpLine *l = &u->lines[i];
        if (l->label && !(l->length == 1) && strncmp(l->text, "cg_", 3) &&
            strncmp(l->text, "return_", 7) && !seen[i]) {
            seen[i] = 1;
            work[top++] = i;
        }
    }

    while (top) {
        unsigned k = work[--top];
        for (; k < u->count; ++k) {
            const LpLine *l = &u->lines[k];
            seen[k] = 1;
            if (!l->op)
                continue;
            if (l->target >= 0 && !seen[l->target]) {
                seen[l->target] = 1;
                work[top++] = (unsigned)l->target;
            }
            if (l->ends)
                break;
            if (k + 1 < u->count && seen[k + 1])
                break;
        }
    }

    for (i = 0; i < u->count; ++i)
        if (u->lines[i].op && !seen[i] && !u->lines[i].deleted) {
            u->lines[i].deleted = 1;
            ++changed;
        }
    free(seen);
    free(work);
    return changed;
}

/* A == index + c before each line: -2 unreached, -1 unknown, else c */
static void lp_accumulator_offsets(const LpUnit *u, long *state, unsigned index)
{
    unsigned i;
    int changed = 1;
    const char *read = index == LP_X ? "txa" : "tya", *write = index == LP_X ? "tax" : "tay";
    const char *up = index == LP_X ? "inx" : "iny", *down = index == LP_X ? "dex" : "dey";

    for (i = 0; i < u->count; ++i)
        state[i] = -2;
    if (u->count)
        state[0] = -1;

    while (changed) {
        changed = 0;
        for (i = 0; i < u->count; ++i) {
            const LpLine *l = &u->lines[i];
            long in = state[i], out = in;
            if (in == -2)
                continue;
            if (l->op) {
                long k;
                int prev = lp_next(u, i, -1);
                if (l->call || l->use == LP_ALL)
                    out = -1;
                else if (lp_line_is(l, read) || lp_line_is(l, write))
                    out = l->m8 || l->x8 ? -1 : 0;
                else if (in >= 0 && lp_is(l, "sbc") && !l->m8 && (k = lp_immediate(l)) >= 0 &&
                         prev >= 0 && lp_line_is(&u->lines[prev], "sec"))
                    out = (in - k) & 0xFFFF;
                else if (in >= 0 && lp_is(l, "adc") && !l->m8 && (k = lp_immediate(l)) >= 0 &&
                         prev >= 0 && lp_line_is(&u->lines[prev], "clc"))
                    out = (in + k) & 0xFFFF;
                else if (in >= 0 && (lp_line_is(l, "inc a") || lp_line_is(l, "inc")) && !l->m8)
                    out = (in + 1) & 0xFFFF;
                else if (in >= 0 && (lp_line_is(l, "dec a") || lp_line_is(l, "dec")) && !l->m8)
                    out = (in - 1) & 0xFFFF;
                else if (in >= 0 && lp_line_is(l, up) && !l->x8)
                    out = (in - 1) & 0xFFFF;
                else if (in >= 0 && lp_line_is(l, down) && !l->x8)
                    out = (in + 1) & 0xFFFF;
                else if (l->def & (LP_A | index) || ((l->m8 || l->x8) && l->def))
                    out = -1;
                else if ((lp_is(l, "lda") || lp_is(l, "adc") || lp_is(l, "sbc") ||
                          lp_is(l, "and") || lp_is(l, "ora") || lp_is(l, "eor") ||
                          lp_is(l, "pla") || lp_is(l, "txa") || lp_is(l, "tya") ||
                          lp_is(l, "xba")) &&
                         l->m8)
                    out = -1;
            }

            /* Meet into successors */
            {
                unsigned s[2];
                int c = 0, j;
                if (!l->op || !l->ends) {
                    if (i + 1 < u->count)
                        s[c++] = i + 1;
                }
                if (l->op && l->target >= 0)
                    s[c++] = (unsigned)l->target;
                for (j = 0; j < c; ++j) {
                    long old = state[s[j]], nw = old == -2 ? out : old == out ? old : -1;
                    if (nw != old) {
                        state[s[j]] = nw;
                        changed = 1;
                    }
                }
            }
        }
    }
}

/* Read "lda n,s" plus its constant adjustment (SEC/SBC #k, CLC/ADC #k,
 * INC A, DEC A): sets *k and *end (last adjustment line). 0 if not. */
static int lp_adjusted_read(const LpUnit *u, unsigned i, long *k, int *end, int *cost)
{
    int j = (int)i, n;

    *k = 0;
    *end = (int)i;
    *cost = 0;
    while ((n = lp_next(u, (unsigned)j, 1)) >= 0) {
        const LpLine *a = &u->lines[n];
        int m;
        long v;
        if (a->m8 || a->replace || a->deleted)
            break;
        if (lp_line_is(a, "inc a") || lp_line_is(a, "inc")) {
            ++*k;
            *cost += 2;
            j = *end = n;
            continue;
        }
        if (lp_line_is(a, "dec a") || lp_line_is(a, "dec")) {
            --*k;
            *cost += 2;
            j = *end = n;
            continue;
        }
        if ((lp_line_is(a, "sec") || lp_line_is(a, "clc")) &&
            (m = lp_next(u, (unsigned)n, 1)) >= 0 &&
            lp_is(&u->lines[m], lp_line_is(a, "sec") ? "sbc" : "adc") && !u->lines[m].m8 &&
            (v = lp_immediate(&u->lines[m])) >= 0) {
            *k += lp_line_is(a, "sec") ? -v : v;
            *cost += 5;
            j = *end = m;
            continue;
        }
        break;
    }
    *k &= 0xFFFF;
    return 1;
}

/* Reuse the frame address already in A on every path to this calculation */
static int lp_redundant_y_offset(LpUnit *u, Function *f, size_t at)
{
    int changed = 0;
    (void)at;

    if (u->indirect || lp_state.parser->no_value_reuse || body_asm_statements(f->body))
        return 0;
    long *offsets = allocate(u->count * sizeof *offsets);
    lp_accumulator_offsets(u, offsets, LP_Y);
    lp_liveness(u);

    for (unsigned i = 0; i < u->count; ++i) {
        LpLine *base = &u->lines[i];
        long offset;
        int last, cost;
        if (offsets[i] < 0 || base->m8 || base->x8 || !lp_line_is(base, "tya"))
            continue;
        lp_adjusted_read(u, i, &offset, &last, &cost);
        if (cost && offset == offsets[i] && !(u->lines[last].out & LP_FLAGS)) {
            for (unsigned j = i; j <= (unsigned)last; ++j)
                if (u->lines[j].op)
                    u->lines[j].deleted = 1;
            changed = 1;
            break;
        }
    }
    free(offsets);
    return changed;
}

/* A direct call whose callee takes no stack arguments (at most two named
 * word parameters, not variadic), so it reads nothing of the caller's stack. */
static int lp_register_call(const LpLine *l)
{
    size_t n;
    const char *name = lp_operand(l, &n);
    unsigned i;

    if (n > 9 && !strncmp(name, ".loword(", 8) && name[n - 1] == ')') {
        name += 8;
        n -= 9;
    }
    if (n < 2 || name[0] != '_')
        return 0;
    ++name;
    --n;

    for (i = 0; i < lp_state.parser->symbol_count; ++i) {
        const Symbol *s = &lp_state.parser->symbols[i];
        unsigned k;
        if (!s->function || s->owner || strlen(s->asm_name) != n || strncmp(s->asm_name, name, n))
            continue;
        if (s->variadic || s->param_count < 0 || s->param_count > 2)
            return 0;
        for (k = 0; k < (unsigned)s->param_count; ++k)
            if (reg_width(s->params[k]) != 2)
                return 0;
        return 1;
    }
    return 0;
}

/* A pushed copy of X whose reads all add a constant: push A = X + c instead
 * and fold c into each read. A compare's subtraction (n - 2 for n < 2)
 * then serves the later n - 1 and n - 2. */
static int lp_push_offsets(LpUnit *u, Function *f, size_t at)
{
    unsigned i, first = u->count;
    long *ax;
    int *sd, changed = 0;
    char *region;
    (void)f;
    (void)at;

    if (u->indirect)
        return 0;

    for (i = 0; i < u->count && first == u->count; ++i)
        if (u->lines[i].op)
            first = i;
    if (first == u->count)
        return 0;
    ax = malloc(u->count * sizeof *ax);
    sd = malloc(u->count * sizeof *sd);
    region = malloc(u->count);
    if (!ax || !sd || !region) {
        fputs("out of memory emitting assembly\n", stderr);
        exit(EXIT_FAILURE);
    }
    lp_liveness(u);
    lp_accumulator_offsets(u, ax, LP_X);
    if (!lp_stack_depths(u, first, sd)) {
        free(ax);
        free(sd);
        free(region);
        return 0;
    }

    for (i = 0; i < u->count && !changed; ++i) {
        LpLine *p = &u->lines[i];
        unsigned j;
        int top, ok = 1, gain = 0, slot_depth;
        long c = ax[i];
        if (!lp_line_is(p, "phx") || p->m8 || p->x8 || c <= 0 || sd[i] < 0)
            continue;
        slot_depth = sd[i] + 2;

        /* The region where the slot is on the stack: forward from the push
         * until it is popped. */
        memset(region, 0, u->count);
        {
            unsigned *work = malloc((u->count + 1) * sizeof *work);
            top = 0;
            if (!work) {
                fputs("out of memory emitting assembly\n", stderr);
                exit(EXIT_FAILURE);
            }
            if (i + 1 < u->count) {
                work[top++] = i + 1;
            }
            while (top && ok) {
                unsigned k = work[--top];
                for (; k < u->count; ++k) {
                    const LpLine *l = &u->lines[k];
                    if (region[k])
                        break;
                    region[k] = 1;
                    if (!l->op)
                        continue;
                    if (sd[k] < slot_depth) {
                        ok = 0;
                        break;
                    }
                    if (l->ends && !l->call && l->target < 0) {
                        ok = 0;
                        break;
                    } /* return with the slot pushed */
                    if (l->target >= 0 && !region[l->target])
                        work[top++] = (unsigned)l->target;
                    if (l->ends)
                        break;
                    if (k + 1 < u->count && sd[k + 1] >= 0 && sd[k + 1] < slot_depth) {
                        /* This line pops the slot: a dead 16-bit pull, or the TSC/TCS cleanup */
                        if (!((lp_line_is(l, "plx") && !(l->out & LP_X)) ||
                              (lp_line_is(l, "pla") && !(l->out & LP_A)) ||
                              (lp_line_is(l, "ply") && !(l->out & LP_Y)) || lp_is(l, "tcs")) ||
                            l->m8 || l->x8) {
                            ok = 0;
                        }
                        break;
                    }
                }
            }
            free(work);
        }
        if (!ok)
            continue;

        /* Labels in the region are entered only from it */
        for (j = 0; j < u->count && ok; ++j) {
            const LpLine *l = &u->lines[j];
            if (l->op && l->target >= 0 && region[l->target] && !region[j] && j != i)
                ok = 0;
        }
        for (j = 0; j < u->count && ok; ++j)
            if (region[j] && u->lines[j].label && j && !region[j - 1] && j - 1 != i) {
                int prev = (int)j - 1;
                while (prev >= 0 && !u->lines[prev].op)
                    --prev;
                if (prev >= 0 && prev != (int)i && !region[prev] && !u->lines[prev].ends)
                    ok = 0;
            }

        /* Every access to the slot is an adjusted 16-bit read */
        for (j = 0; j < u->count && ok; ++j) {
            const LpLine *l = &u->lines[j];
            size_t m;
            const char *o = lp_operand(l, &m);
            long slot, n, k, nk;
            int end, cost, newcost;
            if (!region[j] || !l->op)
                continue;
            if (l->call && !lp_register_call(l)) {
                ok = 0;
                break;
            }
            if (!(m >= 3 && o[m - 2] == ',' && o[m - 1] == 's'))
                continue;
            slot = (long)sd[j] - slot_depth + 1;
            n = strtol(o, NULL, 10);
            if (n + lp_width(l) - 1 < slot || n > slot + 1)
                continue;
            if (!lp_is(l, "lda") || l->m8 || n != slot) {
                ok = 0;
                break;
            }
            lp_adjusted_read(u, j, &k, &end, &cost);
            nk = (k - c) & 0xFFFF;
            newcost = nk == 0                     ? 0
                      : (nk <= 2 || nk >= 0xFFFE) ? 2 * (nk <= 2 ? (int)nk : (int)(0x10000 - nk))
                                                  : 5;
            if (newcost > cost || (u->lines[end].out & (LP_C | LP_V) && cost != newcost)) {
                ok = 0;
                break;
            }
            gain += cost - newcost;
        }
        if (!ok || gain <= 0)
            continue;
        lp_set(p, "    pha");
        for (j = 0; j < u->count; ++j) {
            LpLine *l = &u->lines[j];
            size_t m;
            const char *o = lp_operand(l, &m);
            long slot, n, k, nk;
            int end, cost, e;
            char text[64];
            if (!region[j] || !l->op || !(m >= 3 && o[m - 2] == ',' && o[m - 1] == 's'))
                continue;
            slot = (long)sd[j] - slot_depth + 1;
            n = strtol(o, NULL, 10);
            if (n != slot || !lp_is(l, "lda"))
                continue;
            lp_adjusted_read(u, j, &k, &end, &cost);
            nk = (k - c) & 0xFFFF;
            for (e = (int)j + 1; e <= end; ++e)
                if (u->lines[e].op)
                    u->lines[e].deleted = 1;
            text[0] = 0;
            if (nk && (nk <= 2 || nk >= 0xFFFE)) {
                int s, count = nk <= 2 ? (int)nk : (int)(0x10000 - nk);
                for (s = 0; s < count; ++s)
                    strcat(text, nk <= 2 ? "\n    inc a" : "\n    dec a");
            } else if (nk)
                snprintf(text, sizeof text, "\n    clc\n    adc #$%04lX", nk);
            lp_set(l, "%.*s%s", (int)l->length, l->text, text);
        }
        ++changed;
    }
    free(ax);
    free(sd);
    free(region);
    return changed;
}

/* "txa / adjust by k" where A already holds X + c: adjust A by k - c instead */
static int lp_ax_reuse(LpUnit *u, Function *f, size_t at)
{
    unsigned i;
    long *ax;
    int changed = 0;
    (void)f;
    (void)at;

    ax = malloc((u->count + 1) * sizeof *ax);
    if (!ax) {
        fputs("out of memory emitting assembly\n", stderr);
        exit(EXIT_FAILURE);
    }
    lp_liveness(u);
    lp_accumulator_offsets(u, ax, LP_X);

    for (i = 0; i < u->count; ++i) {
        LpLine *l = &u->lines[i];
        long k, nk, c = ax[i];
        int end, cost, newcost, e;
        char text[64];

        /* A full-width round trip leaves the destination and N/Z unchanged
         * from the first transfer. Reanalyse before removing dead transfers. */
        const char *reverse = lp_line_is(l, "tax")   ? "txa"
                              : lp_line_is(l, "txa") ? "tax"
                              : lp_line_is(l, "tay") ? "tya"
                              : lp_line_is(l, "tya") ? "tay"
                                                     : NULL;
        if (reverse && !l->m8 && !l->x8) {
            e = lp_next(u, i, -1);
            while (e >= 0 && (lp_is(&u->lines[e], "sta") || lp_is(&u->lines[e], "stx") ||
                              lp_is(&u->lines[e], "sty") || lp_is(&u->lines[e], "stz")))
                e = lp_next(u, (unsigned)e, -1);
            if (e >= 0 && !u->lines[e].m8 && !u->lines[e].x8 && lp_line_is(&u->lines[e], reverse)) {
                if (changed)
                    break;
                l->deleted = 1;
                changed = 1;
                break;
            }
        }
        if (!lp_line_is(l, "txa") || l->m8 || l->x8 || c < 0 || l->replace || l->deleted)
            continue;
        lp_adjusted_read(u, i, &k, &end, &cost);
        nk = (k - c) & 0xFFFF;
        newcost = nk == 0                     ? 0
                  : (nk <= 2 || nk >= 0xFFFE) ? 2 * (nk <= 2 ? (int)nk : (int)(0x10000 - nk))
                                              : 5;
        if (newcost >= cost + 2)
            continue;

        /* N/Z must come out the same (no instruction left to set them), and C/V
         * may differ only where dead. */
        if ((!newcost && u->lines[end].out & (LP_N | LP_Z)) ||
            (u->lines[end].out & (LP_C | LP_V) && cost != newcost))
            continue;
        for (e = (int)i + 1; e <= end; ++e)
            if (u->lines[e].op)
                u->lines[e].deleted = 1;
        text[0] = 0;
        if (nk && (nk <= 2 || nk >= 0xFFFE)) {
            int s, count = nk <= 2 ? (int)nk : (int)(0x10000 - nk);
            for (s = 0; s < count; ++s)
                strcat(text, s ? (nk <= 2 ? "\n    inc a" : "\n    dec a")
                               : (nk <= 2 ? "    inc a" : "    dec a"));
        } else if (nk)
            snprintf(text, sizeof text, "    clc\n    adc #$%04lX", nk);
        if (text[0])
            lp_set(l, "%s", text);
        else
            l->deleted = 1;
        ++changed;
    }
    free(ax);
    return changed;
}

/* Commit the low word directly when the high half reads only C objects
 * and disjoint compiler scratch. It uses the carry from the low operation. */
static int lp_store_low_before_high(LpUnit *u, Function *f, size_t at)
{
    (void)at;
    if (u->indirect || lp_state.is_volatile || lp_state.parser->no_value_reuse ||
        body_asm_statements(f->body))
        return 0;
    lp_liveness(u);

    for (unsigned i = 0; i < u->count; ++i) {
        LpLine *push = &u->lines[i];
        if (!lp_line_is(push, "pha") || push->m8 || push->x8)
            continue;
        int load = lp_next(u, i, 1), operate = load < 0 ? -1 : lp_next(u, (unsigned)load, 1);
        int high = operate < 0 ? -1 : lp_next(u, (unsigned)operate, 1),
            pull = high < 0 ? -1 : lp_next(u, (unsigned)high, 1);
        int low = pull < 0 ? -1 : lp_next(u, (unsigned)pull, 1);
        if (low < 0 || !lp_is(&u->lines[load], "lda") ||
            (!lp_is(&u->lines[operate], "adc") && !lp_is(&u->lines[operate], "sbc")) ||
            !lp_is(&u->lines[high], "sta") || !lp_line_is(&u->lines[pull], "pla") ||
            !lp_is(&u->lines[low], "sta") || (u->lines[low].out & (LP_A | LP_N | LP_Z)))
            continue;
        size_t load_n, operate_n, high_n, low_n;
        const char *address = lp_operand(&u->lines[load], &load_n);
        const char *rhs = lp_operand(&u->lines[operate], &operate_n);
        const char *high_dst = lp_operand(&u->lines[high], &high_n);
        const char *low_dst = lp_operand(&u->lines[low], &low_n);
        int lo = lp_workspace_word(low_dst, low_n), hi = lp_workspace_word(high_dst, high_n);
        int other = lp_workspace_word(rhs, operate_n), source = lp_workspace_word(address, load_n);
        if (lo < 0 || hi < 0 || other < 0 || lp_overlaps(&u->lines[high], hi, lo) ||
            lp_overlaps(&u->lines[operate], other, lo))
            continue;
        if (source >= 0) {
            if (lp_overlaps(&u->lines[load], source, lo))
                continue;
        } else {
            char *end;
            if (load_n != 9 || strncmp(address, "a:$", 3) ||
                (memcmp(address + 7, ",x", 2) && memcmp(address + 7, ",y", 2)))
                continue;
            strtoul(address + 3, &end, 16);
            if (end != address + 7)
                continue;
        }
        lp_set(push, "    sta %.*s", (int)low_n, low_dst);
        u->lines[pull].deleted = u->lines[low].deleted = 1;
        return 1;
    }
    return 0;
}

/* A plain store changes neither A nor N/Z, even for volatile destinations.
 * Keep every store and reuse matching immediate loads within the same run. */
static int lp_reuse_store_immediates(LpUnit *u, Function *f, size_t at)
{
    long value = -1;
    int m8 = 0, changed = 0;
    unsigned i;
    (void)f;
    (void)at;

    for (i = 0; i < u->count; ++i) {
        LpLine *l = &u->lines[i];
        if (!l->op) {
            if (l->length && l->text[0] != ';')
                value = -1;
            continue;
        }
        if (lp_is(l, "sta") || lp_is(l, "stx") || lp_is(l, "sty") || lp_is(l, "stz"))
            continue;
        if (lp_is(l, "lda")) {
            long immediate = lp_immediate(l);
            if (immediate >= 0 && immediate == value && l->m8 == m8) {
                l->deleted = 1;
                changed = 1;
            }
            value = immediate;
            m8 = l->m8;
        } else
            value = -1;
    }
    return changed;
}

/* Compare a byte before restoring A16 when the widened value and N flag are
 * dead. CMP preserves Z/C for an unsigned byte and an in-range constant. */
static int lp_byte_compare(LpUnit *u, Function *f, size_t at)
{
    unsigned i;
    int changed = 0;
    (void)f;
    (void)at;

    lp_liveness(u);

    for (i = 0; i < u->count; ++i) {
        LpLine *load = &u->lines[i], *restore, *mask, *compare, *branch;
        int j, k, m, n;
        long value;
        if (!lp_is(load, "lda") || !load->m8 || load->deleted || load->replace)
            continue;
        j = lp_next(u, i, 1);
        if (j < 0 || !lp_line_is(&u->lines[j], "rep #$20"))
            continue;
        k = j + 1;
        while ((unsigned)k < u->count && !u->lines[k].op &&
               (!u->lines[k].length || u->lines[k].text[0] == ';' ||
                (u->lines[k].length == 4 && !strncmp(u->lines[k].text, ".a16", 4))))
            ++k;
        if ((unsigned)k >= u->count)
            continue;
        m = lp_next(u, (unsigned)k, 1);
        n = m >= 0 ? lp_next(u, (unsigned)m, 1) : -1;
        if (n < 0) {
            continue;
        }
        restore = &u->lines[j];
        mask = &u->lines[k];
        compare = &u->lines[m];
        branch = &u->lines[n];
        if (!lp_is(mask, "and") || lp_immediate(mask) != 255 || !lp_is(compare, "cmp") ||
            (value = lp_immediate(compare)) < 0 || value > 255 || !lp_branch(branch) ||
            (compare->out & (LP_A | LP_N)) || restore->deleted || mask->deleted || compare->deleted)
            continue;
        restore->deleted = 1;
        compare->deleted = 1;
        lp_set(mask, ".a8\n    cmp #$%02lX\n    rep #$20\n.a16", value);
        ++changed;
    }
    return changed;
}

/* Reuse an accumulator already related to two private stack words while
 * materializing a straight-line series of word sums into fixed globals. */
static int lp_stack_sum_series(LpUnit *u, Function *f, size_t at)
{
    unsigned i;
    int changed = 0;
    (void)f;
    (void)at;

    lp_liveness(u);

    for (i = 0; i < u->count; ++i) {
        LpLine *first = &u->lines[i], *second;
        size_t n1, n2;
        const char *slot1, *slot2;
        char *end1, *end2;
        long offset1, offset2;
        int clear, addition, save, pos;
        long delta, current;
        if (!lp_is(first, "sta") || first->m8 || first->deleted || first->replace)
            continue;
        slot1 = lp_operand(first, &n1);
        if (n1 < 3 || slot1[n1 - 2] != ',' || slot1[n1 - 1] != 's' ||
            !isdigit((unsigned char)slot1[0]))
            continue;
        clear = lp_next(u, i, 1);
        addition = clear >= 0 ? lp_next(u, (unsigned)clear, 1) : -1;
        save = addition >= 0 ? lp_next(u, (unsigned)addition, 1) : -1;
        if (save < 0 || !lp_line_is(&u->lines[clear], "clc") ||
            !lp_is(&u->lines[addition], "adc") || (delta = lp_immediate(&u->lines[addition])) < 0 ||
            !lp_is(&u->lines[save], "sta"))
            continue;
        second = &u->lines[save];
        slot2 = lp_operand(second, &n2);
        if (second->m8 || n2 < 3 || slot2[n2 - 2] != ',' || slot2[n2 - 1] != 's' ||
            !isdigit((unsigned char)slot2[0]))
            continue;
        offset1 = strtol(slot1, &end1, 10);
        offset2 = strtol(slot2, &end2, 10);
        if (end1 != slot1 + n1 - 2 || end2 != slot2 + n2 - 2 || offset1 < 1 || offset2 < 1 ||
            offset1 > 254 || offset2 > 254 || labs(offset1 - offset2) < 2)
            continue;
        current = delta;
        pos = lp_next(u, (unsigned)save, 1);
        while (pos >= 0) {
            LpLine *load = &u->lines[pos], *sum, *store;
            int c, a, t;
            long literal, desired, adjust;
            size_t m;
            const char *operand, *destination;
            if (!lp_is(load, "lda") || load->m8 || (literal = lp_immediate(load)) < 0 ||
                load->deleted || load->replace)
                break;
            c = lp_next(u, (unsigned)pos, 1);
            a = c >= 0 ? lp_next(u, (unsigned)c, 1) : -1;
            t = a >= 0 ? lp_next(u, (unsigned)a, 1) : -1;
            if (t < 0)
                break;
            sum = &u->lines[a];
            store = &u->lines[t];
            if (!lp_line_is(&u->lines[c], "clc") || !lp_is(sum, "adc") || !lp_is(store, "sta") ||
                sum->m8 || store->m8 || (sum->out & (LP_C | LP_V)) || sum->deleted ||
                sum->replace || store->deleted)
                break;
            operand = lp_operand(sum, &m);
            if (m == n1 && !strncmp(operand, slot1, n1))
                desired = literal;
            else if (m == n2 && !strncmp(operand, slot2, n2))
                desired = literal + delta;
            else
                break;
            destination = lp_operand(store, &m);
            if (m < 12 || strncmp(destination, "a:.loword(_", 11))
                break;
            adjust = (desired - current) & 65535;
            lp_set(load, "    clc\n    adc #$%04lX", adjust);
            u->lines[c].deleted = 1;
            sum->deleted = 1;
            current = desired;
            ++changed;
            pos = lp_next(u, (unsigned)t, 1);
        }
        if (changed)
            break;
    }
    return changed;
}

/* Reuse word values in A/X within a basic block. Private operands retain their
 * identity only while writes, stack movement and calls cannot invalidate it. */
static int lp_x_store_may_write_slot(const LpLine *l, const Function *f, const char *x, size_t xn,
                                     int y_is_frame)
{
    size_t m;
    const char *p = lp_operand(l, &m);

    if (!lp_may_write(l, x, xn, 2))
        return 0;
    if (l->call || lp_is(l, "mvn") || lp_is(l, "mvp") || l->use == LP_ALL || !lp_store_op(l))
        return 1;
    if (m < 2 || p[m - 2] != ',' || p[m - 1] != 'x')
        return 1;
    if (y_is_frame && xn == 9 && !strncmp(x, "a:$", 3) && x[7] == ',' && x[8] == 'y')
        return lp_frame_slot_escaped(f, (int)strtol(x + 3, NULL, 16), 2);
    if (xn >= 3 && x[xn - 2] == ',' && x[xn - 1] == 's' && !lp_state.frame_address && f &&
        !f->uses_varargs && !f->aggregate_abi)
        return 0;
    return 1;
}

static int lp_register_values(LpUnit *u, Function *f, size_t at)
{
    char a[128] = "", x[128] = "", a8[128] = "";
    unsigned i;
    int changed = 0, known_targets;
    unsigned char *targets = lp_local_targets(u, &known_targets);
    int y_is_frame = f && f->frame > 0 && !body_asm_statements(f->body);
    (void)at;

    if (y_is_frame) {
        int seen_tay = 0;
        for (i = 0; i < u->count; ++i) {
            const LpLine *l = &u->lines[i];
            if (!l->op || !(l->def & LP_Y) || lp_line_is(l, "ply"))
                continue;
            if (!seen_tay && lp_line_is(l, "tay")) {
                int prev = lp_next(u, i, -1);
                if (prev >= 0 &&
                    (lp_line_is(&u->lines[prev], "tsc") || lp_line_is(&u->lines[prev], "tcs"))) {
                    seen_tay = 1;
                    continue;
                }
            }
            y_is_frame = 0;
            break;
        }
    }

    for (i = 0; i < u->count; ++i)
        if (lp_line_is(&u->lines[i], "sep #$20") || lp_line_is(&u->lines[i], "rep #$20"))
            u->lines[i].use = 0;
    lp_liveness(u);

    for (i = 0; i < u->count; ++i) {
        LpLine *l = &u->lines[i];
        size_t n;
        const char *o = lp_operand(l, &n);
        int load_a = lp_is(l, "lda"), load_x = lp_is(l, "ldx");
        if (!l->op) {
            /* An untargeted internal label is just the fallthrough edge of
             * a predicate. Other labels may have an independent predecessor. */
            int fallthrough = known_targets && !targets[i] && lp_fallthrough_label(l);
            if ((l->length == 3 && !strncmp(l->text, ".a8", 3)) ||
                (l->length == 4 && !strncmp(l->text, ".a16", 4))) {
                a[0] = 0;
                a8[0] = 0;
            } else if (!fallthrough && l->length && l->text[0] != ';' &&
                       strncmp(l->text, ".export", 7))
                a[0] = x[0] = a8[0] = 0;
            continue;
        }
        if (l->call || l->x8 || l->use == LP_ALL) {
            a[0] = x[0] = a8[0] = 0;
            continue;
        }
        if (l->m8 || lp_line_is(l, "sep #$20") || lp_line_is(l, "rep #$20"))
            a[0] = 0;
        if (!l->m8 || lp_line_is(l, "sep #$20") || lp_line_is(l, "rep #$20"))
            a8[0] = 0;

        /* Y can become a promoted value/cursor. A frame operand's spelling
         * alone does not identify the same storage after its base changes. */
        if (l->def & LP_Y) {
            if (a[0] && a[strlen(a) - 1] == 'y')
                a[0] = 0;
            if (x[0] && x[strlen(x) - 1] == 'y')
                x[0] = 0;
            if (a8[0] && a8[strlen(a8) - 1] == 'y')
                a8[0] = 0;
        }
        if (a[0] &&
            (lp_may_write(l, a, strlen(a), 2) || (a[strlen(a) - 1] == 's' && lp_stack_op(l))))
            a[0] = 0;
        if (x[0] && (lp_x_store_may_write_slot(l, f, x, strlen(x), y_is_frame) ||
                     (x[strlen(x) - 1] == 's' && lp_stack_op(l))))
            x[0] = 0;
        if (a8[0] &&
            (lp_may_write(l, a8, strlen(a8), 1) || (a8[strlen(a8) - 1] == 's' && lp_stack_op(l))))
            a8[0] = 0;
        if (load_a && l->m8 && n < sizeof a8 && n && (o[0] == '#' || lp_private(o, n))) {
            if (strlen(a8) == n && !strncmp(a8, o, n) && !(l->out & (LP_N | LP_Z))) {
                l->deleted = 1;
                ++changed;
                continue;
            }
            memcpy(a8, o, n);
            a8[n] = 0;
            continue;
        }
        if (((load_a && !l->m8) || load_x) && n < sizeof a && n &&
            (o[0] == '#' || lp_private(o, n))) {
            char *key = load_a ? a : x;
            if (strlen(key) == n && !strncmp(key, o, n) && !(l->out & (LP_N | LP_Z))) {
                l->deleted = 1;
                ++changed;
                continue;
            }
            {
                const char *other = load_a ? x : a;
                if (strlen(other) == n && !strncmp(other, o, n)) {
                    lp_set(l, load_a ? "    txa" : "    tax");
                    free(targets);
                    return 1;
                }
            }
            memcpy(key, o, n);
            key[n] = 0;
            continue;
        }
        if (lp_is(l, "sta") && !l->m8 && n < sizeof a && n && lp_private(o, n)) {
            memcpy(a, o, n);
            a[n] = 0;
            continue;
        }
        if (lp_is(l, "sta") && l->m8 && n < sizeof a8 && n && lp_private(o, n)) {
            memcpy(a8, o, n);
            a8[n] = 0;
            continue;
        }
        if (lp_is(l, "stx") && !l->x8 && n < sizeof x && n && lp_private(o, n)) {
            memcpy(x, o, n);
            x[n] = 0;
            continue;
        }
        if (lp_is(l, "tax")) {
            memcpy(x, a, sizeof x);
            continue;
        }
        if (lp_is(l, "txa")) {
            if (!l->m8)
                memcpy(a, x, sizeof a);
            continue;
        }
        if (l->def & (LP_A | LP_AL)) {
            a[0] = 0;
            a8[0] = 0;
        }
        if (l->def & LP_X)
            x[0] = 0;
        if (l->ends)
            a[0] = x[0] = a8[0] = 0;
    }
    free(targets);
    return changed;
}

/* Discover the first scale when the load also supplies an entry test. The
 * fallthrough arm must have no other predecessor and keeps A unchanged.
 * The second scale is still removed only as a straight-line sequence. */
static int lp_scale_after_test(LpUnit *u, unsigned start, const unsigned char *targets)
{
    unsigned i;
    int test = -1;

    for (i = start + 1; i < u->count; ++i) {
        LpLine *l = &u->lines[i];
        if (l->length && l->text[0] == ';')
            continue;
        if (!targets[i] && lp_fallthrough_label(l))
            continue;
        if (test < 0 && l->target >= 0 && !l->ends && lp_branch(l)) {
            test = (int)i;
            continue;
        }

        /* Before relaxation, the inverted test can skip a long jump */
        if (test >= 0 && l->ends && l->target >= 0) {
            unsigned skip = (unsigned)u->lines[test].target;
            if (skip == i + 1 && targets[skip] == 1 && u->lines[skip].length == 1 &&
                u->lines[skip].text[0] == ':') {
                i = skip;
                continue;
            }
        }
        return test >= 0 && lp_line_is(l, "asl a") ? (int)i : -1;
    }
    return -1;
}

/* Keep a scaled array index in X while its source and X are unchanged.
 * Re-emitting TXA can recover the old A/N/Z result, but not ASL's carry. */
static int lp_reuse_scaled_index(LpUnit *u, Function *f, size_t at)
{
    const char *input = NULL;
    size_t input_length = 0;
    unsigned i, scale = 0, dependencies = 0;
    int known_targets;
    unsigned char *targets;
    (void)f;
    (void)at;

    if (lp_state.parser->no_value_reuse || u->indirect)
        return 0;
    targets = lp_local_targets(u, &known_targets);
    lp_liveness(u);

    for (i = 0; i < u->count; ++i) {
        LpLine *l = &u->lines[i];
        size_t length;
        const char *operand = lp_operand(l, &length);
        int from_y = lp_line_is(l, "tya");
        if (!l->op) {
            if (!lp_fallthrough_marker(l, i, targets, known_targets))
                input = NULL;
            continue;
        }
        int stored = lp_is(l, "sta");
        if (!l->m8 && !l->x8 &&
            (from_y || ((lp_is(l, "lda") || stored) && lp_private(operand, length)))) {
            int end = lp_next(u, i, 1), straight = end >= 0 && lp_line_is(&u->lines[end], "asl a");
            unsigned shifts = 0;
            if (!straight && known_targets && !stored)
                end = lp_scale_after_test(u, i, targets);
            while (end >= 0 && !u->lines[end].m8 && lp_line_is(&u->lines[end], "asl a")) {
                ++shifts;
                end = lp_next(u, (unsigned)end, 1);
            }
            if (shifts && end >= 0 && !u->lines[end].x8 && lp_line_is(&u->lines[end], "tax")) {
                if (!stored && straight && input && input_length == length && scale == shifts &&
                    !memcmp(input, operand, length) && !(u->lines[end].out & LP_C)) {
                    unsigned j;
                    if (u->lines[end].out & (LP_A | LP_N | LP_Z))
                        lp_set(l, "    txa");
                    else
                        l->deleted = 1;
                    for (j = i + 1; j <= (unsigned)end; ++j)
                        if (u->lines[j].op)
                            u->lines[j].deleted = 1;
                    free(targets);
                    return 1;
                }
                input = operand;
                input_length = length;
                scale = shifts;
                dependencies = from_y ? LP_Y : lp_index_use(l);
                i = (unsigned)end;
                continue;
            }
        }
        if (l->m8 || l->x8 || l->call || l->use == LP_ALL || l->ends || lp_branch(l) ||
            (l->def & (LP_X | dependencies)))
            input = NULL;
        else if (input && input_length &&
                 ((lp_may_write(l, input, input_length, 2) &&
                   !(input[input_length - 1] == 's' && !lp_state.frame_address && length > 13 &&
                     operand[length - 2] == ',' && operand[length - 1] == 'x' &&
                     !strncmp(operand, "a:.loword(_", 11) && pr_named(operand, length - 2))) ||
                  (input[input_length - 1] == 's' && lp_stack_op(l)) || lp_is(l, "tcd") ||
                  lp_is(l, "pld") || lp_is(l, "plb")))
            input = NULL;
    }
    free(targets);
    return 0;
}

/* Retain a word-array displacement in X when a loop already owns the
 * unscaled counter in Y. Updating both registers avoids scaling at each use. */
static int lp_loop_entry_jump(const LpUnit *u, unsigned entry, unsigned head)
{
    unsigned i;

    if (entry >= head || !u->lines[entry].ends || u->lines[entry].target != (int)head)
        return 0;

    for (i = entry + 1; i < head; ++i) {
        const LpLine *l = &u->lines[i];
        if (l->length && !l->label && l->text[0] != ';')
            return 0;
    }
    return 1;
}

static int lp_retain_word_index(LpUnit *u, Function *f, size_t at)
{
    unsigned latch;
    const unsigned clobbers = LP_A | LP_X | LP_N | LP_Z | LP_C;
    (void)f;
    (void)at;

    if (u->indirect || lp_state.parser->no_register_cursors ||
        lp_state.parser->no_index_elimination)
        return 0;
    lp_liveness(u);

    for (latch = 0; latch < u->count; ++latch) {
        LpLine *edge = &u->lines[latch], *head;
        int start = edge->target, entry = -1, step = -1, source = -1, shift = -1, save = -1,
            valid = 1;
        size_t slot_length = 0;
        const char *slot = NULL;
        unsigned i;
        if (start < 0 || (unsigned)start >= latch || edge->call || (edge->out & LP_X))
            continue;
        head = &u->lines[start];
        if (!lp_fallthrough_label(head) || head->m8 || head->x8 || (head->live & clobbers))
            continue;
        for (i = 0; i < u->count; ++i) {
            LpLine *l = &u->lines[i];
            if (i < (unsigned)start || i > latch) {
                if (l->target >= start && (unsigned)l->target <= latch) {
                    if (entry >= 0 || !lp_loop_entry_jump(u, i, (unsigned)start)) {
                        valid = 0;
                        break;
                    }
                    entry = (int)i;
                }
                continue;
            }
            if (!l->op) {
                if (l->label && l->length != 1 && !lp_fallthrough_label(l)) {
                    valid = 0;
                    break;
                }
                continue;
            }
            if (l->m8 || l->x8 || l->call || l->use == LP_ALL) {
                valid = 0;
                break;
            }
            if (!slot && (l->def & LP_Y)) {
                if (step >= 0 || (l->out & LP_X) ||
                    (!lp_line_is(l, "iny") && !lp_line_is(l, "dey"))) {
                    valid = 0;
                    break;
                }
                step = (int)i;
            }
            if ((l->def & LP_X) && i != (unsigned)save) {
                valid = 0;
                break;
            }
            if (source < 0 && (lp_line_is(l, "tya") || lp_is(l, "lda"))) {
                int a = lp_next(u, i, 1), x = a < 0 ? -1 : lp_next(u, (unsigned)a, 1);
                size_t length;
                const char *operand = lp_operand(l, &length);
                if (x >= 0 && (unsigned)x < latch && lp_line_is(&u->lines[a], "asl a") &&
                    lp_line_is(&u->lines[x], "tax") &&
                    (lp_line_is(l, "tya") || lp_workspace_word(operand, length) >= 0) &&
                    !(u->lines[x].out & (LP_A | LP_N | LP_Z | LP_C))) {
                    source = (int)i;
                    shift = a;
                    save = x;
                    if (length) {
                        slot = operand;
                        slot_length = length;
                    }
                }
            }
        }
        if (valid && slot) {
            if (step >= 0)
                continue;
            for (i = (unsigned)start; i < latch; ++i) {
                LpLine *l = &u->lines[i];
                if (!l->op)
                    continue;
                if ((source > (int)i && lp_branch(l)) || (l->target >= 0 && l->target <= start) ||
                    lp_is(l, "tcd") || lp_is(l, "pld")) {
                    valid = 0;
                    break;
                }
                if (!lp_may_write(l, slot, slot_length, 2))
                    continue;
                if (step >= 0 || i <= (unsigned)save || (l->out & LP_X) ||
                    (!lp_is(l, "inc") && !lp_is(l, "dec")) ||
                    !lp_operand_is(l, slot, slot_length)) {
                    valid = 0;
                    break;
                }
                step = (int)i;
            }
            if (step >= 0)
                for (i = (unsigned)start; i < (unsigned)step; ++i)
                    if (u->lines[i].target > step) {
                        valid = 0;
                        break;
                    }
        }
        if (!valid || save < 0 || step < 0)
            continue;

        /* Fall through the seed when the original entry skipped only labels */
        if (entry >= 0)
            u->lines[entry].deleted = 1;
        if (slot) {
            char seed[96];
            snprintf(seed, sizeof seed, "    lda %.*s\n    asl a\n    tax\n", (int)slot_length,
                     slot);
            lp_insert(head, seed);
        } else
            lp_insert(head, "    tya\n    asl a\n    tax\n");
        lp_insert(&u->lines[step], lp_is(&u->lines[step], "iny") || lp_is(&u->lines[step], "inc")
                                       ? "    inx\n    inx\n"
                                       : "    dex\n    dex\n");
        u->lines[source].deleted = u->lines[shift].deleted = u->lines[save].deleted = 1;
        return 1;
    }
    return 0;
}

/* Reassociate consecutive immediate adds/subs only when their intermediate carry
 * and final carry/overflow have no users. N/Z reflect the same modulo sum. */
static int lp_nz_matches_a16(const LpUnit *u, unsigned before)
{
    int prev = lp_next(u, before, -1);
    const LpLine *p;

    if (prev < 0)
        return 0;
    p = &u->lines[prev];
    return !p->m8 && !p->call && !lp_line_is(p, "xba") &&
           (p->def & (LP_A | LP_N | LP_Z)) == (LP_A | LP_N | LP_Z);
}

static int lp_add_constants(LpUnit *u, Function *f, size_t at)
{
    unsigned i;
    (void)f;
    (void)at;

    lp_liveness(u);

    for (i = 0; i < u->count; ++i) {
        int a, b, c, sub1, sub2;
        long x, y;
        LpLine *l = &u->lines[i];
        if (l->deleted || l->replace)
            continue;
        if (!l->m8 && !(l->out & (LP_N | LP_Z)) &&
            (((lp_is(l, "ora") || lp_is(l, "eor")) && lp_immediate(l) == 0) ||
             (lp_is(l, "and") && lp_immediate(l) == 65535))) {
            l->deleted = 1;
            return 1;
        }
        if (!l->m8 &&
            (((lp_is(l, "ora") || lp_is(l, "eor")) && lp_immediate(l) == 0) ||
             (lp_is(l, "and") && lp_immediate(l) == 65535)) &&
            lp_nz_matches_a16(u, i)) {
            l->deleted = 1;
            return 1;
        }
        sub1 = lp_line_is(l, "sec");
        if ((!sub1 && !lp_line_is(l, "clc")) || (a = lp_next(u, i, 1)) < 0 ||
            !lp_is(&u->lines[a], sub1 ? "sbc" : "adc") || u->lines[a].m8 ||
            (x = lp_immediate(&u->lines[a])) < 0)
            continue;
        if ((b = lp_next(u, (unsigned)a, 1)) >= 0 && (c = lp_next(u, (unsigned)b, 1)) >= 0) {
            sub2 = lp_line_is(&u->lines[b], "sec");
            if ((sub2 || lp_line_is(&u->lines[b], "clc")) &&
                lp_is(&u->lines[c], sub2 ? "sbc" : "adc") && !u->lines[c].m8 &&
                (y = lp_immediate(&u->lines[c])) >= 0 && !(u->lines[c].out & (LP_C | LP_V))) {
                unsigned delta = ((sub1 ? (unsigned)(-x) : (unsigned)x) +
                                  (sub2 ? (unsigned)(-y) : (unsigned)y)) &
                                 65535u;
                if (!delta) {
                    l->deleted = u->lines[b].deleted = u->lines[c].deleted = 1;
                    if (!(u->lines[c].out & (LP_N | LP_Z)) || lp_nz_matches_a16(u, i))
                        u->lines[a].deleted = 1;
                    else
                        lp_set(&u->lines[a], "    ora #$0000");
                    return 1;
                }
                if (delta >= 65534u || (sub1 && sub2 && delta >= 32768u)) {
                    lp_set(l, "    sec");
                    lp_set(&u->lines[a], "    sbc #$%04X", (65536u - delta) & 65535u);
                } else {
                    lp_set(l, "    clc");
                    lp_set(&u->lines[a], "    adc #$%04X", delta);
                }
                u->lines[b].deleted = u->lines[c].deleted = 1;
                return 1;
            }
        }
        if (!x && !(u->lines[a].out & (LP_C | LP_V))) {
            if (!(u->lines[a].out & (LP_N | LP_Z)) || lp_nz_matches_a16(u, i)) {
                l->deleted = u->lines[a].deleted = 1;
                return 1;
            }
            l->deleted = 1;
            lp_set(&u->lines[a], "    ora #$0000");
            return 1;
        }
    }
    return 0;
}

/* With carry-in clear, (a + b) modulo 65536 is below b exactly
 * when ADC sets carry. The repeated operand is compiler scratch. */
static int lp_add_overflow_branch(LpUnit *u, Function *f, size_t at)
{
    unsigned i;
    (void)f;
    (void)at;

    lp_liveness(u);

    for (i = 0; i < u->count; ++i) {
        LpLine *add = &u->lines[i], *compare, *branch;
        int clear, test, edge;
        size_t n;
        const char *operand = lp_operand(add, &n);
        if (!lp_is(add, "adc") || add->m8 || lp_workspace_word(operand, n) < 0 ||
            (clear = lp_next(u, i, -1)) < 0 || !lp_line_is(&u->lines[clear], "clc") ||
            (test = lp_next(u, i, 1)) < 0)
            continue;
        compare = &u->lines[test];
        if (!lp_is(compare, "cmp") || compare->m8 || !lp_operand_is(compare, operand, n) ||
            (compare->out & (LP_N | LP_Z)) || (edge = lp_next(u, (unsigned)test, 1)) < 0)
            continue;
        branch = &u->lines[edge];
        if (branch->target < 0 || (branch->out & LP_C) ||
            (!lp_is(branch, "bcc") && !lp_is(branch, "bcs")))
            continue;
        lp_set(branch, "    %s%.*s", lp_is(branch, "bcc") ? "bcs" : "bcc", (int)branch->length - 7,
               branch->op + 3);
        compare->deleted = 1;
        return 1;
    }
    return 0;
}
