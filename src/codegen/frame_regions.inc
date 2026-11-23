/* A complete frame may move to direct page when its locals do not escape
 * and only one word is live across ordinary calls. Y preserves that word;
 * incoming arguments remain on the stack. */
typedef struct {
    int offset;
    unsigned char erase;
    uint32_t use, def, live, out;
} FrHome;

static int fr_dp_operand(const LpLine *l)
{
    return lp_accumulator_memory(l) || lp_is(l, "ldx") || lp_is(l, "stx") || lp_is(l, "cpx") ||
           lp_is(l, "stz") || lp_is(l, "inc") || lp_is(l, "dec") || lp_is(l, "asl") ||
           lp_is(l, "lsr") || lp_is(l, "rol") || lp_is(l, "ror") || lp_is(l, "bit");
}

static int fr_store(const LpLine *l)
{
    return lp_is(l, "sta") || lp_is(l, "stx") || lp_is(l, "stz");
}

static int fr_release(LpUnit *u, FrHome *homes, unsigned i, unsigned size)
{
    int clc = lp_next(u, i, 1), add = clc < 0 ? -1 : lp_next(u, (unsigned)clc, 1);
    int tcs = add < 0 ? -1 : lp_next(u, (unsigned)add, 1),
        after = tcs < 0 ? -1 : lp_next(u, (unsigned)tcs, 1);
    int ret, save;

    if (after < 0 || u->lines[i].m8 || u->lines[i].x8 || !lp_line_is(&u->lines[clc], "clc") ||
        !lp_is(&u->lines[add], "adc") || lp_immediate(&u->lines[add]) != (long)size ||
        !lp_line_is(&u->lines[tcs], "tcs"))
        return 0;

    ret = after;
    save = -1;

    if (lp_line_is(&u->lines[after], "txa")) {
        save = lp_next(u, i, -1);

        if (save < 0 || !lp_line_is(&u->lines[save], "tax") || u->lines[save].m8)
            return 0;

        ret = lp_next(u, (unsigned)after, 1);
    }

    if (ret < 0 || !lp_line_is(&u->lines[ret], "ply") || (lp_state.value_result && save < 0))
        return 0;

    {
        int end = lp_next(u, (unsigned)ret, 1);

        if (end < 0 || (!lp_line_is(&u->lines[end], "rts") && !lp_line_is(&u->lines[end], "rtl")))
            return 0;
    }
    homes[i].erase = homes[clc].erase = homes[add].erase = homes[tcs].erase = 1;
    homes[ret].erase = 2;

    if (save >= 0)
        homes[save].erase = homes[after].erase = 1;

    return 1;
}

static int lp_call_frame_homes(LpUnit *u, Function *f, size_t at)
{
    FrHome *homes;
    LpLine *copy;
    LpUnit virtual_unit = *u;
    int phy = -1, setup[5], *depth, keep = -1, ok = 0, again, releases = 0;
    long size;

    unsigned i, j, used, mapped[12], references = 0;
    uint32_t across = 0;

    (void)at;

    if (lp_state.parser->no_dp_homes || lp_state.parser->no_stack_frames ||
        lp_state.parser->no_private_regions || lp_state.is_volatile || u->indirect || !u->calls ||
        reg_width(f->symbol->type) > 2 || !strcmp(f->symbol->name, "main"))
        return 0;

    for (i = 0; i < lp_state.parser->symbol_count; ++i) {
        Symbol *v = &lp_state.parser->symbols[i];

        if (v->owner == f->id && v->offset && loop_escapes(f->body, v))
            return 0;
    }

    for (i = 0; i < u->count; ++i) {
        LpLine *l = &u->lines[i];

        if (lp_line_is(l, "phy")) {
            phy = (int)i;
            break;
        }
        if (l->call || lp_branch(l) || l->ends || lp_stack_op(l) || (l->use | l->def) & LP_Y)
            return 0;
    }

    if (phy < 0 || u->lines[phy].x8 || u->lines[phy].m8)
        return 0;

    setup[0] = lp_next(u, (unsigned)phy, 1);

    for (i = 1; i < 5 && setup[i - 1] >= 0; ++i) {
        setup[i] = lp_next(u, (unsigned)setup[i - 1], 1);
    }

    for (i = 0; i < 5; ++i) {
        if (setup[i] < 0)
            return 0;
    }

    if (!lp_line_is(&u->lines[setup[0]], "tsc") || !lp_line_is(&u->lines[setup[1]], "sec") ||
        !lp_is(&u->lines[setup[2]], "sbc") || (size = lp_immediate(&u->lines[setup[2]])) <= 0 ||
        size > 24 || (size & 1) || !lp_line_is(&u->lines[setup[3]], "tcs") ||
        !lp_line_is(&u->lines[setup[4]], "tay"))
        return 0;

    for (i = 0; i < u->count; ++i) {
        LpLine *l = &u->lines[i];

        if (lp_line_is(l, "sep #$20") || lp_line_is(l, "rep #$20"))
            l->use = 0;
        if (l->target >= 0 && l->target <= setup[4])
            return 0;
    }

    lp_liveness(u);

    if (u->lines[setup[4]].out & (LP_A | LP_FLAGS))
        return 0;

    homes = allocate(u->count * sizeof *homes);
    depth = allocate(u->count * sizeof *depth);
    copy = allocate(u->count * sizeof *copy);

    for (i = 0; i < 5; ++i) {
        homes[setup[i]].erase = 1;
    }

    for (i = (unsigned)setup[4] + 1; i < u->count; ++i) {
        LpLine *l = &u->lines[i];
        size_t n;
        const char *p = lp_operand(l, &n);

        if (!l->op || homes[i].erase)
            continue;
        if (lp_line_is(l, "tya")) {
            if (!fr_release(u, homes, i, (unsigned)size))
                goto done;

            ++releases;
            continue;
        }
        if (lp_is(l, "rts") || lp_is(l, "rtl")) {
            int prev = lp_next(u, i, -1);

            if (prev < 0 || homes[prev].erase != 2)
                goto done;

            continue;
        }
        if (l->call) {
            Symbol *callee = lp_callee(l);

            if (l->ends || l->x8 || l->m8 || !callee || callee->interrupt)
                goto done;

            continue;
        }
        if (l->x8 || l->use == LP_ALL || lp_is(l, "tsc") || lp_is(l, "tsx") || lp_is(l, "phy") ||
            lp_is(l, "ply") || lp_is(l, "tcd") || lp_is(l, "pld") || lp_is(l, "plb") ||
            (n >= 2 && p[n - 2] == ',' && p[n - 1] == 's'))
            goto done;

        if (n == 9 && !strncmp(p, "a:$", 3) && p[7] == ',' && p[8] == 'y') {
            char *end;

            unsigned off = (unsigned)strtoul(p + 3, &end, 16), width = (unsigned)lp_width(l);
            uint32_t mask;

            if (end != p + 7 || !off || !fr_dp_operand(l) || width > 2)
                goto done;

            homes[i].offset = (int)off;

            if (off > (unsigned)size) {
                if (off < (unsigned)size + 5u + (unsigned)lp_state.parser->long_return ||
                    !lp_accumulator_memory(l))
                    goto done;

                continue;
            }
            if (off + width - 1 > (unsigned)size || ((off - 1) & 1) + width > 2)
                goto done;

            mask = ((1u << width) - 1) << (off - 1);

            if (lp_store_op(l))
                homes[i].def = mask;
            if (!fr_store(l))
                homes[i].use = mask;

            references |= 1u << ((off - 1) / 2);
        } else if ((l->use | l->def) & LP_Y)
            goto done;
    }

    if (!references || !releases)
        goto done;

    /* A call may overwrite all scratch DP. Only frame bytes read before
     * their next write on some successor path must stay in a saved home. */
    do {
        again = 0;

        for (i = u->count; i-- > 0;) {
            LpLine *l = &u->lines[i];
            uint32_t out = i + 1 < u->count && !l->ends ? homes[i + 1].live : 0, live;

            if (l->target >= 0)
                out |= homes[l->target].live;

            live = homes[i].use | (out & ~homes[i].def);

            if (live != homes[i].live || out != homes[i].out)
                again = 1;

            homes[i].live = live;
            homes[i].out = out;
        }
    } while (again);

    if (homes[0].live)
        goto done;

    for (i = 0; i < u->count; ++i) {
        if (u->lines[i].call)
            across |= homes[i].out;
    }

    for (i = 0; i < (unsigned)size / 2; ++i) {
        if (across & (3u << (2 * i))) {
            if (keep >= 0)
                goto done;

            keep = (int)i;
        }
    }

    used = lp_text_words(u->text, u->text + strlen(u->text));

    for (i = 0, j = 0; i < (unsigned)size / 2; ++i) {
        if ((references & (1u << i)) && (int)i != keep) {
            while (j < 16 && (used & (1u << j))) {
                ++j;
            }

            if (j == 16)
                goto done;

            mapped[i] = 2 * j++;
        }
    }

    /* Recompute stack depths without frame allocation. Argument pushes and
     * their cleanup remain, as does the saved Y when it holds a live word. */
    memcpy(copy, u->lines, u->count * sizeof *copy);
    virtual_unit.lines = copy;

    if (keep < 0)
        homes[phy].erase = 2;

    for (i = 0; i < u->count; ++i) {
        if (homes[i].erase == 1 || (homes[i].erase == 2 && keep < 0))
            copy[i].op = NULL;
    }

    if (!lp_stack_depths(&virtual_unit, 0, depth))
        goto done;

    for (i = 0; i < u->count; ++i) {
        if (homes[i].offset) {
            int offset = homes[i].offset;
            LpLine *l = &u->lines[i];

            if (offset > size) {
                int incoming = offset - (int)size - 2 + depth[i];

                if (depth[i] < 0 || incoming < 1 || incoming > 255)
                    goto done;
            } else if ((offset - 1) / 2 == keep) {
                if (!(offset & 1) || lp_width(l) != 2 ||
                    (!lp_is(l, "lda") && !lp_is(l, "ldx") && !lp_is(l, "sta") &&
                     !lp_is(l, "stx")) ||
                    (fr_store(l) && (l->out & (LP_N | LP_Z))))
                    goto done;
            }
        }
    }

    for (i = 0; i < u->count; ++i) {
        int offset = homes[i].offset;
        LpLine *l = &u->lines[i];

        if (homes[i].erase == 1 || (homes[i].erase == 2 && keep < 0))
            l->deleted = 1;
        if (!offset)
            continue;

        if (offset > size)
            lp_set(l, "    %.3s %d,s", l->op, offset - (int)size - 2 + depth[i]);
        else if ((offset - 1) / 2 == keep)
            lp_set(l, "    %s",
                   lp_is(l, "lda")   ? "tya"
                   : lp_is(l, "ldx") ? "tyx"
                   : lp_is(l, "sta") ? "tay"
                                     : "txy");
        else
            lp_set(l, "    %.3s z:__arith_lhs+%u", l->op,
                   mapped[(offset - 1) / 2] + ((offset - 1) & 1));
    }

    lp_mark_arithmetic();
    ok = 1;
done:
    free(copy);
    free(depth);
    free(homes);
    return ok;
}

/* Shrink a saved X-to-Y home to the call that clobbers X. The saved word
 * occupies the old PHY slot while arguments are on the stack, so the
 * callee sees exactly the original argument layout. */
static int lp_late_call_save(LpUnit *u, Function *f, size_t at)
{
    int save = -1, transfer = -1, call = -1, push = -1, restore = -1, last = -1, *depth;

    unsigned i;
    (void)f;
    (void)at;

    if (lp_state.is_volatile || u->indirect || u->calls != 1 || lp_state.parser->no_stack_frames)
        return 0;

    for (i = 0; i < u->count; ++i) {
        LpLine *l = &u->lines[i];

        if (!l->op)
            continue;
        if (l->x8 || lp_is(l, "tsc") || lp_is(l, "tsx"))
            return 0;
        if (lp_line_is(l, "rep #$20") || lp_line_is(l, "sep #$20"))
            l->use = 0;
        if (l->use == LP_ALL)
            return 0;

        if (lp_line_is(l, "phy")) {
            if (save >= 0)
                return 0;

            save = (int)i;
            transfer = lp_next(u, i, 1);

            if (transfer < 0 || !lp_line_is(&u->lines[transfer], "txy"))
                return 0;
        } else if ((int)i == transfer)
            continue;
        else if (l->call) {
            Symbol *callee = lp_callee(l);

            if (save < 0 || l->ends || !callee || callee->interrupt)
                return 0;

            call = (int)i;
        } else if (lp_line_is(l, "tyx")) {
            if (call < 0)
                return 0;

            last = (int)i;
        } else if (lp_line_is(l, "ply")) {
            int ret = lp_next(u, i, 1);

            if (save < 0 || ret < 0 ||
                (!lp_is(&u->lines[ret], "rts") && !lp_is(&u->lines[ret], "rtl")))
                return 0;
        } else if (lp_is(l, "rts") || lp_is(l, "rtl")) {
            int prev = lp_next(u, i, -1);

            if (prev < 0 || !lp_line_is(&u->lines[prev], "ply"))
                return 0;
        } else if ((l->use | l->def) & LP_Y)
            return 0;
    }

    if (last < 0)
        return 0;

    for (i = (unsigned)transfer + 1; i <= (unsigned)call; ++i) {
        LpLine *l = &u->lines[i];

        if (lp_stack_op(l)) {
            if ((int)i != call && !lp_is(l, "pha") && !lp_is(l, "phx") && !lp_is(l, "pea") &&
                !lp_is(l, "pei"))
                return 0;

            push = (int)i;
            break;
        }

        if (l->def & LP_X)
            return 0;
    }

    depth = allocate(u->count * sizeof *depth);

    if (!lp_stack_depths(u, 0, depth) || depth[push] != 2 || depth[call] < 2)
        goto fail;

    restore = lp_next(u, (unsigned)call, 1);

    while (restore >= 0 && depth[restore] > 2) {
        restore = lp_next(u, (unsigned)restore, 1);
    }

    if (restore < 0 || restore > last || depth[restore] != 2)
        goto fail;

    lp_liveness(u);

    if (u->lines[restore].live & (LP_X | LP_N | LP_Z))
        goto fail;

    for (i = 0; i < u->count; ++i) {
        LpLine *l = &u->lines[i];
        size_t n;
        const char *p = lp_operand(l, &n);

        if (l->target >= 0 &&
            (l->target <= transfer || ((int)i >= push && l->target <= push) ||
             (l->target >= push && l->target < restore) ||
             (l->target >= restore && l->target <= last && ((int)i < restore || (int)i > last))))
            goto fail;
        if ((int)i >= push && (int)i < restore && (lp_branch(l) || l->ends || l->label))
            goto fail;

        if ((int)i >= restore && (int)i <= last) {
            if (lp_is(l, "tyx")) {
                if (l->out & (LP_N | LP_Z))
                    goto fail;
            } else if (l->def & LP_X)
                goto fail;
        }

        if (n >= 2 && p[n - 2] == ',' && p[n - 1] == 's') {
            char *end;
            long offset = strtol(p, &end, 10);

            if (end != p + n - 2 || !lp_accumulator_memory(l) || depth[i] < 2 || offset <= depth[i])
                goto fail;
        }
    }

    for (i = 0; i < u->count; ++i) {
        LpLine *l = &u->lines[i];
        size_t n;
        const char *p = lp_operand(l, &n);

        if ((int)i == save || (int)i == transfer || lp_is(l, "ply") || lp_is(l, "tyx"))
            l->deleted = 1;
        if (((int)i < push || (int)i >= restore) && n >= 2 && p[n - 2] == ',' && p[n - 1] == 's')
            lp_set(l, "    %.3s %ld,s", l->op, strtol(p, NULL, 10) - 2);
    }

    lp_insert(&u->lines[push], "    phx\n");
    lp_insert(&u->lines[restore], "    plx\n");
    free(depth);
    return 1;
fail:
    free(depth);
    return 0;
}

/* Keep the incoming A value for a commutative operation instead of
 * reloading it through scratch. The original store remains for other uses. */
static int lp_commute_saved_word(LpUnit *u, Function *f, size_t at)
{
    unsigned i;
    (void)f;
    (void)at;

    if (lp_state.parser->no_private_regions || lp_state.is_volatile || u->indirect)
        return 0;

    for (i = 0; i < u->count; ++i) {
        LpLine *s = &u->lines[i], *load, *op;
        int j, k;
        size_t n, m;
        const char *slot = lp_operand(s, &n), *source;

        if (!lp_is(s, "sta") || s->m8 || lp_workspace_word(slot, n) < 0 ||
            (j = lp_next(u, i, 1)) < 0)
            continue;

        load = &u->lines[j];
        source = lp_operand(load, &m);

        if (!lp_is(load, "lda") || load->m8 || !m || (k = lp_next(u, (unsigned)j, 1)) < 0)
            continue;

        if (lp_line_is(&u->lines[k], "clc")) {
            k = lp_next(u, (unsigned)k, 1);

            if (k < 0 || !lp_is(&u->lines[k], "adc"))
                continue;
        } else if (!lp_is(&u->lines[k], "and") && !lp_is(&u->lines[k], "ora") &&
                   !lp_is(&u->lines[k], "eor"))
            continue;

        op = &u->lines[k];

        if (op->m8 || !lp_operand_is(op, slot, n))
            continue;

        lp_set(op, "    %.3s %.*s", op->op, (int)m, source);
        load->deleted = 1;
        return 1;
    }

    return 0;
}

/* Fold a snapshot of a named object into its consumers if every path from
 * the snapshot to a consumer is free of possible writes to that object. */
static int lp_forward_named_word(LpUnit *u, Function *f, size_t at)
{
    unsigned i;
    (void)f;
    (void)at;

    if (lp_state.parser->no_private_regions || lp_state.is_volatile || u->helpers || u->indirect)
        return 0;

    lp_liveness(u);

    for (i = 0; i < u->count; ++i) {
        LpLine *load = &u->lines[i];
        int store, word, refs[2], count = 0, valid = 1;

        unsigned j, limit;
        size_t n, m;
        const char *name = lp_operand(load, &n), *slot;

        if (!lp_is(load, "lda") || load->m8 || !pr_named(name, n) || memchr(name, ',', n) ||
            (store = lp_next(u, i, 1)) < 0 || !lp_is(&u->lines[store], "sta") ||
            u->lines[store].m8 || (u->lines[store].out & (LP_A | LP_N | LP_Z)))
            continue;

        slot = lp_operand(&u->lines[store], &m);
        word = lp_workspace_word(slot, m);

        if (word < 0 || (word & 1))
            continue;

        /* A lexical forward slice with no side entries, back edges, or
         * intervening memory effects that can change the original value. */
        for (limit = (unsigned)store + 1; limit < u->count; ++limit) {
            LpLine *l = &u->lines[limit];
            size_t len;
            const char *operand = lp_operand(l, &len);

            if (l->label && !lp_inner_label(u, limit, i, limit))
                break;
            if (!l->op)
                continue;
            if (l->call || l->use == LP_ALL || lp_is(l, "plb") || lp_is(l, "pld") ||
                lp_is(l, "tcd") || (l->target >= 0 && l->target <= (int)limit) ||
                (lp_store_op(l) && lp_workspace_word(operand, len) < 0))
                break;
        }

        for (j = 0; j < u->count; ++j) {
            LpLine *l = &u->lines[j];
            size_t len;
            const char *operand = lp_operand(l, &len);
            int offset = lp_workspace_word(operand, len);

            if (!l->op || j == (unsigned)store)
                continue;

            if (offset < 0) {
                if (lp_text_words(operand, operand + len) & (1u << (word / 2))) {
                    valid = 0;
                    break;
                }

                continue;
            }

            if (!lp_overlaps(l, offset, word))
                continue;
            if (j <= (unsigned)store || j >= limit || offset != word || l->m8 ||
                !lp_accumulator_memory(l) || lp_is(l, "sta") || count == 2) {
                valid = 0;
                break;
            }

            refs[count++] = (int)j;
        }

        if (!valid || !count)
            continue;

        for (j = 0; j < (unsigned)count; ++j) {
            LpLine *l = &u->lines[refs[j]];

            lp_set(l, "    %.3s %.*s", l->op, (int)n, name);
        }

        load->deleted = u->lines[store].deleted = 1;
        return 1;
    }

    return 0;
}

/* An immediate step is an accumulator increment or decrement when the
 * carry and overflow results are unused. */
static int lp_relocated_word_steps(LpUnit *u, Function *f, size_t at)
{
    unsigned i;
    (void)f;
    (void)at;

    lp_liveness(u);

    for (i = 0; i < u->count; ++i) {
        LpLine *carry = &u->lines[i], *step;
        int next, add = lp_line_is(carry, "clc");

        if ((!add && !lp_line_is(carry, "sec")) || (next = lp_next(u, i, 1)) < 0)
            continue;

        step = &u->lines[next];

        if (step->m8 || !lp_is(step, add ? "adc" : "sbc") || lp_immediate(step) != 1 ||
            (step->out & (LP_C | LP_V)))
            continue;

        lp_set(step, add ? "    inc a" : "    dec a");
        carry->deleted = 1;
        return 1;
    }

    return 0;
}

/* Testing the low byte of A just stored to scratch needs neither a reload
 * nor an A8 region when the high byte and the byte sign flag are dead. */
static int lp_test_saved_byte(LpUnit *u, Function *f, size_t at)
{
    unsigned i;
    (void)f;
    (void)at;

    if (lp_state.parser->no_private_regions || lp_state.is_volatile || u->indirect)
        return 0;

    for (i = 0; i < u->count; ++i) {
        if (lp_line_is(&u->lines[i], "sep #$20") || lp_line_is(&u->lines[i], "rep #$20"))
            u->lines[i].use = 0;
    }

    lp_liveness(u);

    for (i = 0; i < u->count; ++i) {
        LpLine *s = &u->lines[i];
        int sep, load, rep;
        size_t n;
        const char *slot = lp_operand(s, &n);

        if (!lp_is(s, "sta") || s->m8 || lp_workspace_word(slot, n) < 0 ||
            (sep = lp_next(u, i, 1)) < 0 || !lp_line_is(&u->lines[sep], "sep #$20") ||
            (unsigned)sep + 1 >= u->count || u->lines[sep + 1].length != 3 ||
            strncmp(u->lines[sep + 1].text, ".a8", 3))
            continue;

        load = lp_next(u, (unsigned)sep + 1, 1);

        if (load < 0 || !lp_is(&u->lines[load], "lda") ||
            !lp_operand_is(&u->lines[load], slot, n) || (rep = lp_next(u, (unsigned)load, 1)) < 0 ||
            !lp_line_is(&u->lines[rep], "rep #$20") || (unsigned)rep + 1 >= u->count ||
            u->lines[rep + 1].length != 4 || strncmp(u->lines[rep + 1].text, ".a16", 4) ||
            (u->lines[rep].out & (LP_A | LP_N)))
            continue;

        lp_set(&u->lines[sep], "    and #$00FF");
        u->lines[sep + 1].deleted = u->lines[load].deleted = u->lines[rep].deleted =
            u->lines[rep + 1].deleted = 1;
        return 1;
    }

    return 0;
}

/* Sink a stack word step to its first add. Require that the stack input
 * stays unchanged and that every use of the scratch word passes the new
 * definition, including across short-circuit branches. */
static int lp_sink_word_step(LpUnit *u, Function *f, size_t at)
{
    unsigned i;
    (void)f;
    (void)at;

    if (lp_state.is_volatile || u->helpers || u->indirect)
        return 0;

    lp_liveness(u);

    for (i = 0; i < u->count; ++i) {
        LpLine *load = &u->lines[i];
        int step, store, first = -1, last = -1, word, base, carry, valid = 1;

        unsigned j;
        size_t n, m, b;
        const char *source = lp_operand(load, &n), *slot, *operand;
        char *end;

        if (!lp_is(load, "lda") || load->m8 || n < 3 || source[n - 2] != ',' ||
            source[n - 1] != 's' || (step = lp_next(u, i, 1)) < 0 || u->lines[step].m8 ||
            (!lp_line_is(&u->lines[step], "inc a") && !lp_line_is(&u->lines[step], "dec a")) ||
            (store = lp_next(u, (unsigned)step, 1)) < 0 || !lp_is(&u->lines[store], "sta") ||
            u->lines[store].m8 || (u->lines[store].out & (LP_A | LP_N | LP_Z)))
            continue;
        if (strtol(source, &end, 10) < 1 || end != source + n - 2)
            continue;

        slot = lp_operand(&u->lines[store], &m);
        word = lp_workspace_word(slot, m);

        if (word < 0 || (word & 1))
            continue;

        for (j = 0; j < u->count; ++j) {
            LpLine *l = &u->lines[j];
            size_t len;
            const char *p = lp_operand(l, &len);
            int offset = lp_workspace_word(p, len);

            if (!l->op || j == (unsigned)store)
                continue;

            if (offset < 0) {
                if (lp_text_words(p, p + len) & (1u << (word / 2))) {
                    valid = 0;
                    break;
                }

                continue;
            }

            if (!lp_overlaps(l, offset, word))
                continue;
            if (j <= (unsigned)store || lp_store_op(l)) {
                valid = 0;
                break;
            }
            if (first < 0)
                first = (int)j;

            last = (int)j;
        }

        if (!valid || first < 0 || !lp_is(&u->lines[first], "adc") || u->lines[first].m8 ||
            !lp_operand_is(&u->lines[first], slot, m))
            continue;

        carry = lp_next(u, (unsigned)first, -1);
        base = carry < 0 ? -1 : lp_next(u, (unsigned)carry, -1);

        if (base <= store || !lp_line_is(&u->lines[carry], "clc") ||
            !lp_is(&u->lines[base], "lda") || u->lines[base].m8)
            continue;

        operand = lp_operand(&u->lines[base], &b);

        if (!pr_named(operand, b) || memchr(operand, ',', b))
            continue;

        for (j = (unsigned)store + 1; j <= (unsigned)last; ++j) {
            LpLine *l = &u->lines[j];
            size_t len;
            const char *p = lp_operand(l, &len);

            if (l->label &&
                !lp_inner_label(u, j, (int)j < base ? (unsigned)store + 1 : (unsigned)base, j)) {
                valid = 0;
                break;
            }
            if (!l->op)
                continue;
            if (lp_stack_op(l) || l->use == LP_ALL || lp_is(l, "pld") || lp_is(l, "tcd") ||
                (l->target >= 0 && l->target <= (int)j) ||
                (lp_store_op(l) && lp_workspace_word(p, len) < 0)) {
                valid = 0;
                break;
            }
        }

        if (!valid)
            continue;

        lp_set(&u->lines[base], "    lda %.*s\n    %.5s\n    sta %.*s", (int)n, source,
               u->lines[step].op, (int)m, slot);
        lp_set(&u->lines[first], "    adc %.*s", (int)b, operand);
        load->deleted = u->lines[step].deleted = u->lines[store].deleted = 1;
        return 1;
    }

    return 0;
}

/* When a zero test guards a region and the join only normalizes that same
 * byte to a boolean, the bypass already has A=0 and every other predecessor
 * has a nonzero value. Use the two facts instead of reloading the byte. */
static int lp_bool_return_epilogue(const LpUnit *u, int test, int *entry)
{
    int p = lp_next(u, (unsigned)test, 1);

    if (p < 0) {
        /* Early fallthrough-jump cleanup can leave just the return label */
        for (p = test + 1; (unsigned)p < u->count && !u->lines[p].op; ++p) {
            const LpLine *line = &u->lines[p];

            if (line->text[0] != ';' && (!line->label || strncmp(line->text, "return_", 7)))
                return 0;
        }

        if ((unsigned)p >= u->count)
            return 0;
    }

    *entry = p;
    if (p >= 0 && !u->lines[p].m8 && (lp_is(&u->lines[p], "jmp") || lp_is(&u->lines[p], "bra")) &&
        u->lines[p].target >= 0) {
        p = u->lines[p].target;

        while ((unsigned)p < u->count && (u->lines[p].deleted || !u->lines[p].op)) {
            ++p;
        }

        if ((unsigned)p >= u->count)
            return 0;
    }

    if (p < 0 || u->lines[p].m8)
        return 0;
    if (lp_line_is(&u->lines[p], "rts") || lp_line_is(&u->lines[p], "rtl"))
        return 1;

    if (lp_line_is(&u->lines[p], "ply")) {
        p = lp_next(u, (unsigned)p, 1);
        return p >= 0 && !u->lines[p].m8 &&
               (lp_line_is(&u->lines[p], "rts") || lp_line_is(&u->lines[p], "rtl"));
    }

    if (lp_line_is(&u->lines[p], "plx")) {
        p = lp_next(u, (unsigned)p, 1);

        if (p >= 0 && lp_line_is(&u->lines[p], "plx"))
            p = lp_next(u, (unsigned)p, 1);
        if (p >= 0 && lp_line_is(&u->lines[p], "ply"))
            p = lp_next(u, (unsigned)p, 1);

        return p >= 0 && !u->lines[p].m8 &&
               (lp_line_is(&u->lines[p], "rts") || lp_line_is(&u->lines[p], "rtl"));
    }

    if (lp_line_is(&u->lines[p], "tax")) {
        int a = lp_next(u, (unsigned)p, 1), b = a < 0 ? -1 : lp_next(u, (unsigned)a, 1),
            c = b < 0 ? -1 : lp_next(u, (unsigned)b, 1),
            d = c < 0 ? -1 : lp_next(u, (unsigned)c, 1),
            e = d < 0 ? -1 : lp_next(u, (unsigned)d, 1),
            f = e < 0 ? -1 : lp_next(u, (unsigned)e, 1),
            g = f < 0 ? -1 : lp_next(u, (unsigned)f, 1);
        return g >= 0 && !u->lines[g].m8 && lp_line_is(&u->lines[a], "tya") &&
               lp_line_is(&u->lines[b], "clc") && lp_is(&u->lines[c], "adc") &&
               lp_immediate(&u->lines[c]) >= 0 && lp_line_is(&u->lines[d], "tcs") &&
               lp_line_is(&u->lines[e], "txa") && lp_line_is(&u->lines[f], "ply") &&
               (lp_line_is(&u->lines[g], "rts") || lp_line_is(&u->lines[g], "rtl"));
    }

    return 0;
}

static int lp_boolean_join(LpUnit *u, Function *f, size_t at)
{
    unsigned i;
    (void)f;
    (void)at;

    if (lp_state.is_volatile || u->indirect)
        return 0;

    for (i = 0; i < u->count; ++i) {
        LpLine *save = &u->lines[i];
        int mask, gate, transfer, join, load, test, branch = -1, one, done, valid = 1,
                                                    direct_bool = 0;
        unsigned j, skip_label, done_label;
        size_t n;
        const char *slot = lp_operand(save, &n);

        if (!lp_is(save, "sta") || save->m8 || lp_workspace_word(slot, n) < 0 ||
            (mask = lp_next(u, i, 1)) < 0 || u->lines[mask].m8 ||
            !lp_line_is(&u->lines[mask], "and #$00FF") ||
            (gate = lp_next(u, (unsigned)mask, 1)) < 0)
            continue;

        transfer = gate;

        if (lp_is(&u->lines[gate], "bne")) {
            transfer = lp_next(u, (unsigned)gate, 1);

            if (transfer < 0 || !lp_is(&u->lines[transfer], "jmp") ||
                u->lines[gate].target != transfer + 1)
                continue;
        } else if (!lp_is(&u->lines[gate], "beq"))
            continue;

        join = u->lines[transfer].target;

        if (join <= transfer)
            continue;

        load = join;

        do {
            ++load;
        } while ((unsigned)load < u->count && !u->lines[load].op);

        if ((unsigned)load >= u->count || !lp_is(&u->lines[load], "lda") || u->lines[load].m8 ||
            !lp_operand_is(&u->lines[load], slot, n))
            continue;

        test = lp_next(u, (unsigned)load, 1);

        if (test >= 0 && !u->lines[test].m8 && lp_line_is(&u->lines[test], "and #$00FF")) {
            if ((branch = lp_next(u, (unsigned)test, 1)) >= 0 && lp_is(&u->lines[branch], "beq") &&
                (one = lp_next(u, (unsigned)branch, 1)) >= 0 && !u->lines[one].m8 &&
                lp_is(&u->lines[one], "lda") &&
                (lp_line_is(&u->lines[one], "lda #1") || lp_immediate(&u->lines[one]) == 1) &&
                (done = u->lines[branch].target) > one) {
                /* Both original outcomes meet at the next instruction after LDA #1 */
                for (j = (unsigned)one + 1; j < (unsigned)done && !u->lines[j].op; ++j) {
                }

                if (j != (unsigned)done)
                    continue;
            } else if (f->symbol->type.is_bool && !f->symbol->type.pointers &&
                       lp_bool_return_epilogue(u, test, &done)) {
                one = test;
                direct_bool = 1;
            } else
                continue;
        } else if (f->symbol->type.is_bool && !f->symbol->type.pointers &&
                   lp_bool_return_epilogue(u, load, &done)) {
            test = load;
            one = load;
            direct_bool = 1;
        } else
            continue;

        for (j = (unsigned)transfer + 1; j <= (unsigned)one; ++j) {
            LpLine *l = &u->lines[j];

            unsigned k;

            if (l->op &&
                ((l->target >= 0 && l->target <= (int)j) || l->call || lp_is(l, "pld") ||
                 lp_is(l, "tcd") ||
                 (l->use == LP_ALL && !lp_line_is(l, "sep #$20") && !lp_line_is(l, "rep #$20")) ||
                 lp_may_write(l, slot, n, 2))) {
                valid = 0;
                break;
            }

            if (!l->label)
                continue;

            for (k = 0; k < u->count; ++k) {
                if (u->lines[k].target == (int)j &&
                    (k <= (unsigned)transfer || k > (unsigned)one) &&
                    !(k == (unsigned)transfer && j == (unsigned)join) &&
                    !(transfer != gate && k == (unsigned)gate && j == (unsigned)transfer + 1)) {
                    valid = 0;
                    break;
                }
            }

            if (!valid)
                break;
        }

        if (!valid)
            continue;

        done_label = lp_next_label();

        if (transfer != gate)
            lp_set(&u->lines[transfer], "    jmp .loword(cg_%s_%u)", lp_state.parser->unit,
                   done_label);
        else {
            skip_label = lp_next_label();
            lp_set(&u->lines[gate], "    bne cg_%s_%u\n    jmp .loword(cg_%s_%u)\ncg_%s_%u = *",
                   lp_state.parser->unit, skip_label, lp_state.parser->unit, done_label,
                   lp_state.parser->unit, skip_label);
        }

        if (direct_bool) {
            if (test != load)
                u->lines[load].deleted = 1;

            lp_set(&u->lines[test], "    lda #1");
        } else
            u->lines[load].deleted = u->lines[test].deleted = u->lines[branch].deleted = 1;

        {
            char label_text[192];

            snprintf(label_text, sizeof label_text, "cg_%s_%u = *\n", lp_state.parser->unit,
                     done_label);
            lp_insert(&u->lines[done], label_text);
        }
        return 1;
    }

    return 0;
}

/* A leaf with no allocated locals can address its incoming stack words
 * without dedicating Y to the stack base. Keep the caller's saved Y if the
 * body uses Y for an indexed access. */
static int lp_leaf_stack_arguments(LpUnit *u, Function *f, size_t at)
{
    unsigned entry = 0, i;
    int base, ready, *depth, ok = 0;
    PrState *states;

    (void)f;
    (void)at;

    if (lp_state.parser->no_stack_frames || u->calls || u->indirect || lp_state.is_volatile)
        return 0;

    while (entry < u->count && !lp_line_is(&u->lines[entry], "phy")) {
        LpLine *l = &u->lines[entry];

        if (lp_stack_op(l) || lp_branch(l) || l->ends || (l->use | l->def) & LP_Y)
            return 0;

        ++entry;
    }

    if (entry == u->count || !lp_line_is(&u->lines[entry], "phy") || u->lines[entry].x8)
        return 0;

    base = lp_next(u, entry, 1);
    ready = base < 0 ? -1 : lp_next(u, (unsigned)base, 1);

    if (ready < 0 || !lp_line_is(&u->lines[base], "tsc") || !lp_line_is(&u->lines[ready], "tay"))
        return 0;

    depth = allocate(u->count * sizeof *depth);
    states = pr_states(u);

    if (!lp_stack_depths(u, entry, depth))
        goto done;

    for (i = (unsigned)ready + 1; i < u->count; ++i) {
        if (lp_line_is(&u->lines[i], "sep #$20") || lp_line_is(&u->lines[i], "rep #$20"))
            u->lines[i].use = 0;
    }

    lp_liveness(u);

    if (u->lines[ready].out & (LP_A | LP_N | LP_Z))
        goto done;

    for (i = (unsigned)ready + 1; i < u->count; ++i) {
        LpLine *l = &u->lines[i];
        size_t n;
        const char *p = lp_operand(l, &n);

        if (!l->op || depth[i] < 0)
            continue;
        if (l->use == LP_ALL || l->x8 || lp_is(l, "tsc") || lp_is(l, "tsx") ||
            (n >= 2 && p[n - 2] == ',' && p[n - 1] == 's') ||
            (l->target >= 0 && l->target <= ready))
            goto done;
        if (lp_is(l, "ply") && states[i].count >= 2 && states[i].stack[0] && states[i].stack[1] &&
            (l->out & (LP_N | LP_Z)))
            goto done;
        if (!(l->use & LP_Y) || !states[i].frame || lp_is(l, "phy"))
            continue;
        if (n != 9 || strncmp(p, "a:$", 3) || strncmp(p + 7, ",y", 2) || !lp_accumulator_memory(l))
            goto done;

        {
            char *end;
            long off = strtol(p + 3, &end, 16);

            if (end != p + 7 || off < 5 + lp_state.parser->long_return || off + depth[i] - 2 > 255)
                goto done;

            lp_set(l, "    %.3s %ld,s", l->op, off + depth[i] - 2);
        }
    }

    u->lines[base].deleted = u->lines[ready].deleted = 1;
    ok = 1;
done:
    free(states);
    free(depth);
    return ok;
}

/* An inner Y save is redundant when a surrounding save still restores the
 * caller's value and the inner pair protects no observed Y value. */
static int lp_dead_inner_y_save(LpUnit *u, Function *f, size_t at)
{
    unsigned i;
    (void)f;
    (void)at;

    if (u->indirect || lp_state.is_volatile || lp_state.parser->no_stack_frames)
        return 0;

    for (i = 0; i < u->count; ++i) {
        if (lp_line_is(&u->lines[i], "sep #$20") || lp_line_is(&u->lines[i], "rep #$20"))
            u->lines[i].use = 0;
    }

    lp_liveness(u);

    for (i = 0; i < u->count; ++i) {
        unsigned j;

        if (!lp_line_is(&u->lines[i], "phy") || u->lines[i].x8)
            continue;

        for (j = i + 1; j < u->count; ++j) {
            LpLine *l = &u->lines[j];
            size_t n;
            const char *p = lp_operand(l, &n);

            if (l->label || lp_branch(l) || l->ends || l->x8 || l->use == LP_ALL ||
                lp_is(l, "tsc") || lp_is(l, "tsx") ||
                (n >= 2 && p[n - 2] == ',' && p[n - 1] == 's'))
                break;
            if (lp_line_is(l, "ply") && !(l->out & (LP_Y | LP_N | LP_Z))) {
                u->lines[i].deleted = l->deleted = 1;
                return 1;
            }
            if (lp_stack_op(l))
                break;
        }
    }

    return 0;
}

/* Outgoing MVN needs Y as its destination cursor. A function with no
 * use of its local frame pointer need only preserve the caller's Y. */
static int lp_outgoing_move_frame(LpUnit *u, Function *f, size_t at)
{
    unsigned entry = 0, i;
    int base, ready, save = -1, restore = -1;

    (void)at;

    if (lp_state.parser->no_stack_frames || u->indirect || statement_inline_markers(f->body) ||
        body_asm_statements(f->body))
        return 0;

    while (entry < u->count && !u->lines[entry].op) {
        ++entry;
    }

    if (entry == u->count || !lp_line_is(&u->lines[entry], "phy") || u->lines[entry].x8)
        return 0;

    base = lp_next(u, entry, 1);
    ready = base < 0 ? -1 : lp_next(u, (unsigned)base, 1);

    if (ready < 0 || !lp_line_is(&u->lines[base], "tsc") || !lp_line_is(&u->lines[ready], "tay"))
        return 0;

    lp_liveness(u);

    if (u->lines[ready].out & (LP_A | LP_N | LP_Z))
        return 0;

    for (i = (unsigned)ready + 1; i < u->count; ++i) {
        LpLine *l = &u->lines[i];

        if (!l->op)
            continue;
        if (l->target >= 0 && l->target <= ready)
            return 0;
        if (l->call) {
            Symbol *callee = lp_callee(l);

            if (l->ends || !callee || callee->interrupt)
                return 0;

            continue;
        }
        if (lp_is(l, "rts") || lp_is(l, "rtl")) {
            int pull = lp_next(u, i, -1);

            if (pull < 0 || !lp_line_is(&u->lines[pull], "ply") || u->lines[pull].x8)
                return 0;

            continue;
        }
        if (lp_is(l, "ply"))
            continue;

        if (save < 0 && lp_line_is(l, "sty z:__arith_rhs") && !l->x8) {
            int op = lp_next(u, i, 1);
            static const char *const move[] = {"tsc", "sec", "sbc", "tcs", "inc",
                                               "tay", "phb", "lda", "mvn", "plb"};
            unsigned j;

            for (j = 0;
                 j < sizeof move / sizeof move[0] && op >= 0 && lp_is(&u->lines[op], move[j]);
                 ++j) {
                op = lp_next(u, (unsigned)op, 1);
            }

            if (j != sizeof move / sizeof move[0] || op < 0 ||
                !lp_line_is(&u->lines[op], "ldy z:__arith_rhs") ||
                (u->lines[op].out & (LP_N | LP_Z)))
                return 0;

            save = (int)i;
            restore = op;
            i = (unsigned)op;
            continue;
        }

        if ((l->use | l->def) & LP_Y || lp_is(l, "mvn") || lp_is(l, "mvp"))
            return 0;
    }

    if (save < 0)
        return 0;

    u->lines[base].deleted = u->lines[ready].deleted = u->lines[save].deleted =
        u->lines[restore].deleted = 1;
    return 1;
}

/* Keep an immutable incoming pointer in callee-saved Y. Rebase the other
 * frame homes on the hardware stack, accounting for outgoing arguments at
 * each access. The pointer's own stack word disappears. */
static int lp_pointer_frame_home(LpUnit *u, Function *f, size_t at)
{
    Symbol *p = leaf_parameter(f, 0);

    FrHome *homes;
    LpLine *copy;
    LpUnit virtual_unit = *u;
    int phy = -1, setup[5], transfer, save, *depth, ok = 0, releases = 0;
    long size;

    unsigned i;
    (void)at;

    if (lp_state.parser->no_stack_frames || lp_state.parser->no_private_regions ||
        lp_state.is_volatile || u->indirect || u->helpers || !u->calls ||
        reg_width(f->symbol->type) > 2 || !p || !p->type.pointers || far_pointer(p->type) ||
        loop_escapes(f->body, p))
        return 0;

    for (i = 0; i < u->count; ++i) {
        if (lp_line_is(&u->lines[i], "phy")) {
            phy = (int)i;
            break;
        }
    }

    if (phy < 0 || u->lines[phy].x8 || u->lines[phy].m8)
        return 0;

    setup[0] = lp_next(u, (unsigned)phy, 1);

    for (i = 1; i < 5 && setup[i - 1] >= 0; ++i) {
        setup[i] = lp_next(u, (unsigned)setup[i - 1], 1);
    }

    for (i = 0; i < 5; ++i) {
        if (setup[i] < 0)
            return 0;
    }

    if (!lp_line_is(&u->lines[setup[0]], "tsc") || !lp_line_is(&u->lines[setup[1]], "sec") ||
        !lp_is(&u->lines[setup[2]], "sbc") || (size = lp_immediate(&u->lines[setup[2]])) < 6 ||
        size > 64 || !lp_line_is(&u->lines[setup[3]], "tcs") ||
        !lp_line_is(&u->lines[setup[4]], "tay"))
        return 0;

    transfer = lp_next(u, (unsigned)setup[4], 1);
    save = transfer < 0 ? -1 : lp_next(u, (unsigned)transfer, 1);

    if (save < 0 || !lp_line_is(&u->lines[transfer], "txa") ||
        !lp_line_is(&u->lines[save], "sta a:$0001,y") || u->lines[save].m8)
        return 0;

    for (i = 0; i < u->count; ++i) {
        LpLine *l = &u->lines[i];

        if (lp_line_is(l, "sep #$20") || lp_line_is(l, "rep #$20"))
            l->use = 0;
        if (l->target > phy && l->target <= save)
            return 0;
    }

    lp_liveness(u);

    if (u->lines[save].out & LP_A)
        return 0;

    homes = allocate(u->count * sizeof *homes);
    depth = allocate(u->count * sizeof *depth);
    copy = allocate(u->count * sizeof *copy);

    for (i = (unsigned)save + 1; i < u->count; ++i) {
        LpLine *l = &u->lines[i];
        size_t n;
        const char *operand = lp_operand(l, &n);

        if (!l->op || homes[i].erase)
            continue;

        if (lp_line_is(l, "tya")) {
            if (!fr_release(u, homes, i, (unsigned)size))
                goto done;

            homes[i].offset = -1;
            ++releases;
            continue;
        }

        if (lp_is(l, "rts") || lp_is(l, "rtl")) {
            int prev = lp_next(u, i, -1);

            if (prev < 0 || homes[prev].erase != 2)
                goto done;

            continue;
        }
        if (l->call) {
            Symbol *callee = lp_callee(l);

            if (l->ends || !callee || callee->interrupt)
                goto done;

            continue;
        }
        if (l->use == LP_ALL || l->x8 || (l->def & LP_Y) || lp_is(l, "tsx") || lp_is(l, "phy") ||
            (n >= 2 && operand[n - 2] == ',' && operand[n - 1] == 's'))
            goto done;
        if (!(l->use & LP_Y))
            continue;

        if (n == 9 && !strncmp(operand, "a:$", 3) && !strncmp(operand + 7, ",y", 2)) {
            char *end;
            long off = strtol(operand + 3, &end, 16);

            if (end != operand + 7 || off < 1 || off == 2 || lp_width(l) > 2)
                goto done;

            if (off == 1) {
                if (!lp_is(l, "ldx") || l->x8)
                    goto done;
            } else if (!lp_accumulator_memory(l) &&
                       !(lp_is(l, "ldx") && !l->m8 &&
                         (!(l->out & LP_A) || !(l->out & (LP_N | LP_Z)))))
                goto done;

            homes[i].offset = (int)off;
        } else
            goto done;
    }

    if (!releases)
        goto done;

    memcpy(copy, u->lines, u->count * sizeof *copy);
    virtual_unit.lines = copy;
    copy[setup[3]].op = NULL;

    for (i = (unsigned)save + 1; i < u->count; ++i) {
        if (homes[i].erase == 1)
            copy[i].op = NULL;
    }

    if (!lp_stack_depths(&virtual_unit, 0, depth) || depth[save] != 2)
        goto done;

    for (i = (unsigned)save + 1; i < u->count; ++i) {
        int offset = homes[i].offset;

        if (offset == -1 && depth[i] != 2)
            goto done;
        if (offset > 2 &&
            (depth[i] < 2 ||
             offset + depth[i] - 4 +
                     (lp_is(&u->lines[i], "ldx") && (u->lines[i].out & LP_A) ? 2 : 0) >
                 255))
            goto done;
    }

    lp_set(&u->lines[setup[2]], "    sbc #$%04lX", size - 2);
    u->lines[setup[4]].deleted = u->lines[save].deleted = 1;
    lp_set(&u->lines[transfer], "    txy");

    for (i = (unsigned)save + 1; i < u->count; ++i) {
        int offset = homes[i].offset;
        LpLine *l = &u->lines[i];

        if (offset == -1) {
            int clc = lp_next(u, i, 1), add = lp_next(u, (unsigned)clc, 1);

            lp_set(l, "    tsc");
            lp_set(&u->lines[add], "    adc #$%04lX", size - 2);
        } else if (offset == 1)
            lp_set(l, "    tyx");
        else if (offset > 2) {
            if (lp_is(l, "ldx") && (l->out & LP_A))
                lp_set(l, "    pha\n    lda %d,s\n    tax\n    pla", offset + depth[i] - 2);
            else if (lp_is(l, "ldx"))
                lp_set(l, "    lda %d,s\n    tax", offset + depth[i] - 4);
            else
                lp_set(l, "    %.3s %d,s", l->op, offset + depth[i] - 4);
        }
    }

    ok = 1;
done:
    free(copy);
    free(depth);
    free(homes);
    return ok;
}

/* Preserve a repeated named word in a dead index register. Labels may
 * only enter from this slice, and writes outside private stack or scratch
 * homes end the slice because they could alias the original object. */
static int lp_snapshot_index(LpUnit *u, Function *f, size_t at)
{
    unsigned i;
    (void)f;
    (void)at;

    if (u->indirect || lp_state.is_volatile || lp_state.parser->no_private_regions)
        return 0;

    lp_liveness(u);

    for (i = 0; i < u->count; ++i) {
        LpLine *first = &u->lines[i];
        size_t n;
        const char *name = lp_operand(first, &n);

        unsigned j, count = 0;

        if (!lp_is(first, "lda") || first->m8 || first->x8 || first->out & LP_X ||
            !pr_named(name, n) || memchr(name, ',', n))
            continue;

        for (j = i + 1; j < u->count; ++j) {
            LpLine *l = &u->lines[j];
            size_t len;
            const char *p = lp_operand(l, &len);

            if (l->label && !lp_inner_label(u, j, i, j))
                break;
            if (!l->op)
                continue;
            if (l->call || l->use == LP_ALL || l->m8 || l->x8 || (l->use | l->def) & LP_X ||
                lp_is(l, "plb") || lp_is(l, "pld") || lp_is(l, "tcd") ||
                (l->target >= 0 && l->target <= (int)j))
                break;
            if (lp_store_op(l) && len && !(len == 1 && p[0] == 'a') &&
                lp_workspace_word(p, len) < 0 &&
                !(len >= 3 && p[len - 2] == ',' && p[len - 1] == 's' && lp_private(p, len)))
                break;
            if (lp_is(l, "lda") && lp_operand_is(l, name, n))
                ++count;
        }

        if (count >= 2) {
            unsigned k;
            lp_set(first, "    lda %.*s\n    tax", (int)n, name);

            for (k = i + 1; k < j; ++k) {
                if (lp_is(&u->lines[k], "lda") && lp_operand_is(&u->lines[k], name, n))
                    lp_set(&u->lines[k], "    txa");
            }

            return 1;
        }
    }

    return 0;
}

/* Delay a pure byte extraction until the other operand has acquired X.
 * This replaces a balanced push/pull pair and leaves the extracted word
 * in A, with the same N/Z and with the carry untouched. */
static int lp_delay_byte_extract(LpUnit *u, Function *f, size_t at)
{
    unsigned i;
    (void)f;
    (void)at;

    if (u->indirect || lp_state.is_volatile)
        return 0;

    for (i = 0; i < u->count; ++i) {
        LpLine *load = &u->lines[i];
        size_t n;
        const char *p = lp_operand(load, &n);
        int swap, mask, push, other, high, clear, scale, tax, pull;

        if (!lp_is(load, "lda") || load->m8 || lp_workspace_word(p, n) < 0)
            continue;

        swap = lp_next(u, i, 1);
        mask = swap < 0 ? -1 : lp_next(u, (unsigned)swap, 1);
        push = mask < 0 ? -1 : lp_next(u, (unsigned)mask, 1);
        other = push < 0 ? -1 : lp_next(u, (unsigned)push, 1);
        high = other < 0 ? -1 : lp_next(u, (unsigned)other, 1);
        clear = high < 0 ? -1 : lp_next(u, (unsigned)high, 1);
        scale = clear < 0 ? -1 : lp_next(u, (unsigned)clear, 1);
        tax = scale < 0 ? -1 : lp_next(u, (unsigned)scale, 1);
        pull = tax < 0 ? -1 : lp_next(u, (unsigned)tax, 1);

        if (pull < 0 || !lp_line_is(&u->lines[swap], "xba") ||
            !lp_line_is(&u->lines[mask], "and #$00FF") || !lp_line_is(&u->lines[push], "pha") ||
            !lp_is(&u->lines[other], "lda") || !lp_line_is(&u->lines[high], "xba") ||
            !lp_line_is(&u->lines[clear], "and #$00FF") || !lp_line_is(&u->lines[scale], "asl a") ||
            !lp_line_is(&u->lines[tax], "tax") || !lp_line_is(&u->lines[pull], "pla") ||
            u->lines[pull].m8 || u->lines[tax].x8)
            continue;

        {
            size_t len;
            const char *q = lp_operand(&u->lines[other], &len);

            if (lp_workspace_word(q, len) < 0)
                continue;
        }
        lp_set(&u->lines[pull], "    lda %.*s\n    xba\n    and #$00FF", (int)n, p);
        load->deleted = u->lines[swap].deleted = u->lines[mask].deleted = u->lines[push].deleted =
            1;
        return 1;
    }

    return 0;
}

/* For equality, compare a pure accumulator sum against the original word
 * directly. The old stack push only saved the operand for CMP. */
static int lp_equal_sum(LpUnit *u, Function *f, size_t at)
{
    unsigned i;
    (void)f;
    (void)at;

    if (u->indirect || lp_state.is_volatile || lp_state.parser->no_private_regions)
        return 0;

    lp_liveness(u);

    for (i = 0; i < u->count; ++i) {
        LpLine *value = &u->lines[i], *sum, *add, *store, *compare;
        size_t n, ns, na, m;
        const char *p = lp_operand(value, &n), *a, *b, *slot;
        int push, load, carry, adc, save, pull, cmp;
        long x, y;
        char *end;

        if (!lp_is(value, "lda") || value->m8 || n != 9 || strncmp(p, "a:$", 3) || p[7] != ',' ||
            (p[8] != 'x' && p[8] != 'y'))
            continue;

        push = lp_next(u, i, 1);
        load = push < 0 ? -1 : lp_next(u, (unsigned)push, 1);
        carry = load < 0 ? -1 : lp_next(u, (unsigned)load, 1);
        adc = carry < 0 ? -1 : lp_next(u, (unsigned)carry, 1);
        save = adc < 0 ? -1 : lp_next(u, (unsigned)adc, 1);
        pull = save < 0 ? -1 : lp_next(u, (unsigned)save, 1);
        cmp = pull < 0 ? -1 : lp_next(u, (unsigned)pull, 1);

        if (cmp < 0 || !lp_line_is(&u->lines[push], "pha") ||
            !lp_line_is(&u->lines[carry], "clc") || !lp_line_is(&u->lines[pull], "pla"))
            continue;

        sum = &u->lines[load];
        add = &u->lines[adc];
        store = &u->lines[save];
        compare = &u->lines[cmp];

        if (!lp_is(sum, "lda") || !lp_is(add, "adc") || !lp_is(store, "sta") ||
            !lp_is(compare, "cmp") || (compare->out & (LP_A | LP_N | LP_C)) ||
            !(compare->out & LP_Z) || sum->m8 || add->m8 || store->m8 || compare->m8)
            continue;

        a = lp_operand(sum, &ns);
        b = lp_operand(add, &na);
        slot = lp_operand(store, &m);

        if (ns < 3 || na < 3 || strncmp(a + ns - 2, ",s", 2) || strncmp(b + na - 2, ",s", 2) ||
            lp_workspace_word(slot, m) < 0 || !lp_operand_is(compare, slot, m))
            continue;

        x = strtol(a, &end, 10);

        if (end != a + ns - 2 || x < 3)
            continue;

        y = strtol(b, &end, 10);

        if (end != b + na - 2 || y < 3)
            continue;

        lp_set(sum, "    lda %ld,s", x - 2);
        lp_set(add, "    adc %ld,s", y - 2);
        lp_set(compare, "    cmp %.*s", (int)n, p);
        value->deleted = u->lines[push].deleted = u->lines[pull].deleted = 1;
        return 1;
    }

    return 0;
}

/* A saved incoming index is still available before its first clobber.
 * Keep the store only when another path or later use needs the home. */
static int lp_reload_saved_x(LpUnit *u, Function *f, size_t at)
{
    unsigned i;
    (void)f;
    (void)at;

    if (u->indirect || lp_state.is_volatile || lp_state.parser->no_private_regions)
        return 0;

    for (i = 0; i < u->count; ++i) {
        LpLine *save = &u->lines[i];
        size_t n;
        const char *slot = lp_operand(save, &n);
        int j;

        if (!lp_is(save, "stx") || save->x8 || lp_workspace_word(slot, n) < 0)
            continue;

        for (j = lp_next(u, i, 1); j >= 0; j = lp_next(u, (unsigned)j, 1)) {
            LpLine *l = &u->lines[j];

            if (l->x8 || l->m8 || l->def & LP_X || l->ends || lp_branch(l) || lp_is(l, "tcd") ||
                lp_is(l, "pld") || lp_may_write(l, slot, n, 2))
                break;
            if (lp_is(l, "lda") && lp_operand_is(l, slot, n)) {
                lp_set(l, "    txa");
                return 1;
            }
        }
    }

    return 0;
}

/* A pushed pointer stays in X across read-only field tests on the fallthrough
 * path. Skip reloads until a different entry, stack change or write. */
static int lp_pushed_index_checks(LpUnit *u, Function *f, size_t at)
{
    int changed = 0;

    (void)f;
    (void)at;

    if (u->indirect || lp_state.is_volatile)
        return 0;

    lp_liveness(u);

    for (unsigned i = 0; i < u->count; ++i) {
        if (!lp_line_is(&u->lines[i], "phx") || u->lines[i].x8)
            continue;

        int base = lp_next(u, i, 1);
        int frame = base < 0 ? -1 : lp_next(u, (unsigned)base, 1);

        if (frame >= 0 && lp_line_is(&u->lines[base], "tsc") &&
            lp_line_is(&u->lines[frame], "tay")) {
            for (int j = lp_next(u, (unsigned)frame, 1); j >= 0; j = lp_next(u, (unsigned)j, 1)) {
                LpLine *next = &u->lines[j];

                if (lp_line_is(next, "ldx a:$0001,y") && !next->x8 &&
                    !(next->out & (LP_N | LP_Z))) {
                    next->deleted = 1;
                    ++changed;
                    break;
                }
                if (next->use == LP_ALL || next->x8 || next->call || next->ends ||
                    lp_branch(next) || (next->def & (LP_X | LP_Y)) || lp_stack_op(next) ||
                    lp_store_op(next))
                    break;
            }
        }

        for (unsigned j = i + 1; j < u->count; ++j) {
            LpLine *l = &u->lines[j];

            if (l->length && l->text[0] == ';')
                continue;
            if (lp_fallthrough_label(l) && l->first_incoming < 0)
                continue;
            if (l->m8 || l->x8)
                break;

            if (lp_line_is(l, "lda 1,s")) {
                int k = lp_next(u, j, 1);

                if (k < 0 || !lp_line_is(&u->lines[k], "tax"))
                    break;

                if (u->lines[k].out & (LP_A | LP_N | LP_Z))
                    lp_set(l, "    txa");
                else
                    l->deleted = 1;

                u->lines[k].deleted = 1;
                j = (unsigned)k;
                ++changed;
            } else if (lp_branch(l)) {
                int after;

                if (lp_cond_branch_target(u, (int)j, &after) < 0)
                    break;
                if (after != (int)j &&
                    (u->lines[after].first_incoming != (int)j || l->next_incoming >= 0))
                    break;

                j = (unsigned)after;
            } else if (!lp_is(l, "lda") && !lp_is(l, "cmp"))
                break;
        }
    }

    return changed;
}

/* A fixed varargs slot can be addressed directly from S */
static int lp_varargs_stack_read(LpUnit *u, Function *f, size_t at)
{
    unsigned i;
    (void)at;

    if (!f->uses_varargs || u->indirect || lp_state.parser->no_private_regions ||
        body_asm_statements(f->body))
        return 0;

    for (i = 0; i < u->count; ++i) {
        if (lp_is(&u->lines[i], "plb") || lp_is(&u->lines[i], "mvn") || lp_is(&u->lines[i], "mvp"))
            return 0;
    }

    lp_liveness(u);

    for (i = 0; i < u->count; ++i) {
        int clear, add, index, load;
        long offset;

        if (!lp_line_is(&u->lines[i], "tsc") || u->lines[i].m8 || u->lines[i].x8)
            continue;

        clear = lp_next(u, i, 1);
        add = clear < 0 ? -1 : lp_next(u, (unsigned)clear, 1);
        index = add < 0 ? -1 : lp_next(u, (unsigned)add, 1);
        load = index < 0 ? -1 : lp_next(u, (unsigned)index, 1);

        if (load < 0 || !lp_line_is(&u->lines[clear], "clc") || !lp_is(&u->lines[add], "adc") ||
            !lp_line_is(&u->lines[index], "tax") || !lp_line_is(&u->lines[load], "lda a:$0000,x") ||
            (u->lines[load].out & (LP_X | LP_C | LP_V)))
            continue;

        offset = lp_immediate(&u->lines[add]);

        if (offset < 1 || offset > 255)
            continue;

        lp_set(&u->lines[load], "    lda %ld,s", offset);
        u->lines[i].deleted = u->lines[clear].deleted = u->lines[add].deleted =
            u->lines[index].deleted = 1;
        return 1;
    }

    return 0;
}

/* A pushed incoming X word remains available on paths that neither
 * clobber X nor overwrite its saved stack word. */
static int lp_saved_x_read(LpUnit *u, Function *f, size_t at)
{
    unsigned entry = 0;
    int push, *depth, saved, changed, matched = 0;
    unsigned char *state;

    (void)at;

    if (lp_state.frame_address || lp_state.is_volatile || u->indirect ||
        lp_state.parser->no_private_regions || body_asm_statements(f->body))
        return 0;

    while (entry < u->count && !u->lines[entry].op) {
        ++entry;
    }

    if (entry == u->count)
        return 0;

    push = lp_line_is(&u->lines[entry], "pha") ? lp_next(u, entry, 1) : (int)entry;

    if (push < 0 || (unsigned)push + 1 >= u->count || !lp_line_is(&u->lines[push], "phx") ||
        u->lines[push].x8)
        return 0;

    depth = allocate(u->count * sizeof *depth);

    if (!lp_stack_depths(u, entry, depth)) {
        free(depth);
        return 0;
    }

    saved = depth[push] + 2;
    state = allocate(u->count);
    state[push + 1] = 1;

    do {
        changed = 0;

        for (unsigned i = (unsigned)push + 1; i < u->count; ++i) {
            LpLine *l = &u->lines[i];
            unsigned char next = state[i];

            if (!next)
                continue;

            if (l->op) {
                if (l->x8 || l->call || l->use == LP_ALL || (l->def & LP_X) || depth[i] < saved)
                    next = 2;

                if (lp_store_op(l)) {
                    size_t n;
                    const char *o = lp_operand(l, &n);

                    if (n && !lp_operand_is(l, "a", 1) && lp_workspace_word(o, n) < 0) {
                        int offset = atoi(o), slot = depth[i] - saved + 1;

                        if (!lp_private(o, n) || o[n - 1] != 's' ||
                            (offset < slot + 2 && slot < offset + lp_width(l)))
                            next = 2;
                    }
                }
            }

            if (!l->ends && i + 1 < u->count && state[i + 1] < next) {
                state[i + 1] = next;
                changed = 1;
            }

            if (l->target > push && state[l->target] < next) {
                state[l->target] = next;
                changed = 1;
            }
        }
    } while (changed);

    lp_liveness(u);

    for (unsigned i = (unsigned)push + 1; i < u->count; ++i) {
        LpLine *load = &u->lines[i];
        char operand[16];
        int slot = depth[i] - saved + 1;

        if (state[i] != 1 || slot < 1 || slot > 255 || load->m8 || load->x8 || !lp_is(load, "lda"))
            continue;

        size_t n = (size_t)snprintf(operand, sizeof operand, "%d,s", slot);

        if (!lp_operand_is(load, operand, n))
            continue;

        lp_set(load, load->out & (LP_A | LP_C) ? "    txa" : "    cpx #$0000");
        matched = 1;
        break;
    }

    free(state);
    free(depth);
    return matched;
}

/* A variadic wrapper can forward a pointer to its incoming argument
 * block after dropping its own unopened temporary frame. */
static int lp_varargs_tail_call(LpUnit *u, Function *f, size_t at)
{
    static const char *const prologue[] = {"phy", "pha", "phx", "tsc", "tay", "clc", "adc"};
    const int long_return = lp_state.parser->long_return;
    int start = 0, i, add = -1, call, pull, ret;
    size_t n;
    const char *operand;
    Symbol *callee;

    (void)at;

    if (!f->uses_varargs || f->symbol->param_count != 1 ||
        !register_parameter(0, f->symbol->params[0]) || lp_state.parser->no_stack_frames ||
        u->calls != 1 || u->indirect || reg_width(f->symbol->type) != 2 ||
        body_asm_statements(f->body) || statement_inline_markers(f->body))
        return 0;

    while ((unsigned)start < u->count && !u->lines[start].op) {
        ++start;
    }

    if ((unsigned)start == u->count)
        return 0;

    i = start;

    for (unsigned part = 0; part < sizeof prologue / sizeof prologue[0]; ++part) {
        if (i < 0 || u->lines[i].m8 || u->lines[i].x8 || !lp_is(&u->lines[i], prologue[part]))
            return 0;

        add = i;
        i = lp_next(u, (unsigned)i, 1);
    }

    call = i;

    if (call < 0 || !lp_is(&u->lines[call], long_return ? "jsl" : "jsr") ||
        lp_immediate(&u->lines[add]) != 9 + long_return)
        return 0;

    callee = lp_callee(&u->lines[call]);

    if (!callee || callee->interrupt || callee->variadic || callee->param_count != 2 ||
        !same_type(callee->type, f->symbol->type) ||
        !same_type(callee->params[0], f->symbol->params[0]) || !callee->params[1].pointers ||
        !register_parameter(1, callee->params[1]))
        return 0;

    for (pull = call + 1; (unsigned)pull < u->count && !u->lines[pull].op; ++pull) {
        if (u->lines[pull].text[0] != ';' &&
            (!u->lines[pull].label || strncmp(u->lines[pull].text, "return_", 7)))
            return 0;
    }

    if ((unsigned)pull == u->count || !lp_line_is(&u->lines[pull], "plx") || u->lines[pull].x8)
        return 0;

    i = lp_next(u, (unsigned)pull, 1);

    if (i < 0 || !lp_line_is(&u->lines[i], "plx") || u->lines[i].x8)
        return 0;

    i = lp_next(u, (unsigned)i, 1);

    if (i < 0 || !lp_line_is(&u->lines[i], "ply") || u->lines[i].x8)
        return 0;

    ret = lp_next(u, (unsigned)i, 1);

    if (ret < 0 || !lp_line_is(&u->lines[ret], long_return ? "rtl" : "rts"))
        return 0;

    for (i = ret + 1; (unsigned)i < u->count; ++i) {
        if (u->lines[i].op)
            return 0;
    }

    operand = lp_operand(&u->lines[call], &n);

    for (i = start; i <= ret; ++i) {
        if (u->lines[i].op)
            u->lines[i].deleted = 1;
    }

    lp_set(&u->lines[call], "    tsc\n    clc\n    adc #$%04X\n    %s %.*s", 3 + long_return,
           long_return ? "jml" : "jmp", (int)n, operand);
    return 1;
}

/* Load an indexed word mask first, then apply a byte read directly to it
 * in A8. The previous zero extension and private byte spill were only
 * needed to put the operands in the opposite order. */
static int lp_test_indexed_mask(LpUnit *u, Function *f, size_t at)
{
    unsigned i;
    (void)f;
    (void)at;

    if (u->indirect || lp_state.is_volatile || lp_state.parser->no_private_regions)
        return 0;

    lp_liveness(u);

    for (i = 0; i + 1 < u->count; ++i) {
        int wrapped, load, rep = -1, zero, save, index, scale, tax, mask, test;
        LpLine *byte, *word;
        size_t n, m, b, w, k;
        const char *operand, *slot, *index_operand, *mask_operand;
        int slot_offset, index_offset;

        wrapped = lp_line_is(&u->lines[i], "sep #$20") && u->lines[i + 1].length == 3 &&
                  !strncmp(u->lines[i + 1].text, ".a8", 3);

        if (wrapped) {
            load = lp_next(u, i + 1, 1);
            rep = load < 0 ? -1 : lp_next(u, (unsigned)load, 1);

            if (rep < 0 || !lp_line_is(&u->lines[rep], "rep #$20") ||
                (unsigned)rep + 1 >= u->count || u->lines[rep + 1].length != 4 ||
                strncmp(u->lines[rep + 1].text, ".a16", 4))
                continue;

            zero = lp_next(u, (unsigned)rep + 1, 1);
        } else if (lp_is(&u->lines[i], "lda") && !u->lines[i].m8) {
            load = (int)i;
            zero = lp_next(u, i, 1);
        } else
            continue;

        save = zero < 0 ? -1 : lp_next(u, (unsigned)zero, 1);
        index = save < 0 ? -1 : lp_next(u, (unsigned)save, 1);
        scale = index < 0 ? -1 : lp_next(u, (unsigned)index, 1);
        tax = scale < 0 ? -1 : lp_next(u, (unsigned)scale, 1);
        mask = tax < 0 ? -1 : lp_next(u, (unsigned)tax, 1);
        test = mask < 0 ? -1 : lp_next(u, (unsigned)mask, 1);

        if (test < 0 || !lp_is(&u->lines[load], "lda") ||
            !lp_line_is(&u->lines[zero], "and #$00FF") || !lp_is(&u->lines[save], "sta") ||
            !lp_is(&u->lines[index], "lda") || !lp_line_is(&u->lines[scale], "asl a") ||
            !lp_line_is(&u->lines[tax], "tax") || !lp_is(&u->lines[mask], "lda") ||
            !lp_is(&u->lines[test], "and") || (u->lines[test].out & (LP_A | LP_N)))
            continue;

        byte = &u->lines[load];
        word = &u->lines[mask];
        operand = lp_operand(byte, &n);
        slot = lp_operand(&u->lines[save], &m);
        index_operand = lp_operand(&u->lines[index], &b);
        mask_operand = lp_operand(word, &w);
        slot_offset = lp_workspace_word(slot, m);
        index_offset = lp_workspace_word(index_operand, b);

        if (n < 5 || operand[0] != '[' || strncmp(operand + n - 3, "],y", 3) || slot_offset < 0 ||
            index_offset < 0 || lp_overlaps(&u->lines[save], slot_offset, index_offset) ||
            !lp_operand_is(&u->lines[test], slot, m) || w < 5 ||
            strncmp(mask_operand + w - 2, ",x", 2) || !pr_named(mask_operand, w))
            continue;

        /* Every other spelling or use of the old scratch word is a barrier,
         * except earlier references that precede the store. */
        for (k = (size_t)test + 1; k < u->count; ++k) {
            LpLine *l = &u->lines[k];
            size_t len;
            const char *p = lp_operand(l, &len);
            int off = lp_workspace_word(p, len);

            if ((l->target >= 0 && l->target <= test) || (lp_branch(l) && l->use == LP_ALL))
                break;
            if (off >= 0 && lp_overlaps(l, off, slot_offset))
                break;
            if (off < 0 && lp_text_words(p, p + len) & (1u << (slot_offset / 2)))
                break;
        }

        if (k != u->count || (slot_offset & 1))
            continue;

        if (wrapped) {
            lp_set(&u->lines[i], "    lda %.*s\n    asl a\n    tax\n    lda %.*s\n    sep #$20",
                   (int)b, index_operand, (int)w, mask_operand);
            lp_set(byte, "    and %.*s", (int)n, operand);
        } else {
            lp_set(byte,
                   "    lda %.*s\n    asl a\n    tax\n    lda %.*s\n    sep #$20\n.a8\n    and "
                   "%.*s\n    rep #$20\n.a16",
                   (int)b, index_operand, (int)w, mask_operand, (int)n, operand);
        }

        u->lines[zero].deleted = u->lines[save].deleted = u->lines[index].deleted = 1;
        u->lines[scale].deleted = u->lines[tax].deleted = word->deleted = u->lines[test].deleted =
            1;
        return 1;
    }

    return 0;
}

/* A small Y-held-pointer frame can reserve its slots with pushes. Push
 * the incoming accumulator through the lowest home in one operation. */
static int lp_push_parameter_frame(LpUnit *u, Function *f, size_t at)
{
    unsigned i;
    (void)f;
    (void)at;

    if (lp_state.parser->no_stack_frames || u->indirect || lp_state.is_volatile)
        return 0;

    for (i = 0; i < u->count; ++i) {
        if (lp_line_is(&u->lines[i], "sep #$20") || lp_line_is(&u->lines[i], "rep #$20"))
            u->lines[i].use = 0;
    }

    lp_liveness(u);

    for (i = 0; i < u->count; ++i) {
        int prior, base, carry, sub, ready, txy, load, save;
        long size;
        size_t n;
        const char *slot;

        if (!lp_line_is(&u->lines[i], "phy") || u->lines[i].m8 || u->lines[i].x8)
            continue;

        prior = lp_next(u, i, -1);
        base = lp_next(u, i, 1);
        carry = base < 0 ? -1 : lp_next(u, (unsigned)base, 1);
        sub = carry < 0 ? -1 : lp_next(u, (unsigned)carry, 1);
        ready = sub < 0 ? -1 : lp_next(u, (unsigned)sub, 1);
        txy = ready < 0 ? -1 : lp_next(u, (unsigned)ready, 1);
        load = txy < 0 ? -1 : lp_next(u, (unsigned)txy, 1);
        save = load < 0 ? -1 : lp_next(u, (unsigned)load, 1);

        if (prior < 0 || save < 0 || !lp_is(&u->lines[prior], "sta") ||
            !lp_line_is(&u->lines[base], "tsc") || !lp_line_is(&u->lines[carry], "sec") ||
            !lp_is(&u->lines[sub], "sbc") || !lp_line_is(&u->lines[ready], "tcs") ||
            !lp_line_is(&u->lines[txy], "txy") || !lp_is(&u->lines[load], "lda") ||
            !lp_line_is(&u->lines[save], "sta 1,s") || (u->lines[save].out & LP_FLAGS))
            continue;

        size = lp_immediate(&u->lines[sub]);

        if (size != 4 && size != 6 && size != 8)
            continue;

        slot = lp_operand(&u->lines[prior], &n);

        if (lp_workspace_word(slot, n) < 0 || !lp_operand_is(&u->lines[load], slot, n))
            continue;

        lp_set(&u->lines[base], "%s",
               size == 4   ? "    pha\n    pha"
               : size == 6 ? "    pha\n    pha\n    pha"
                           : "    pha\n    pha\n    pha\n    pha");
        u->lines[carry].deleted = u->lines[sub].deleted = u->lines[ready].deleted = 1;
        u->lines[load].deleted = u->lines[save].deleted = 1;
        return 1;
    }

    return 0;
}

/* Stage the indexed subtraction operand before a stack-only word sum.
 * The sum does not read the scratch word and the field does not use S,
 * so the push/pull protecting the sum is unnecessary. */
static int lp_stage_subtract_before_sum(LpUnit *u, Function *f, size_t at)
{
    unsigned i;
    (void)f;
    (void)at;

    if (u->indirect || lp_state.is_volatile || lp_state.parser->no_private_regions)
        return 0;

    for (i = 0; i < u->count; ++i) {
        LpLine *start = &u->lines[i];
        int carry, add, push, field, save, pull, sec, sub;
        size_t n, m, k, b;
        const char *p = lp_operand(start, &n), *q, *slot, *src;
        char moved[96];

        if (!lp_is(start, "lda") || start->m8 || n < 3 || strncmp(p + n - 2, ",s", 2))
            continue;

        carry = lp_next(u, i, 1);
        add = carry < 0 ? -1 : lp_next(u, (unsigned)carry, 1);
        push = add < 0 ? -1 : lp_next(u, (unsigned)add, 1);
        field = push < 0 ? -1 : lp_next(u, (unsigned)push, 1);
        save = field < 0 ? -1 : lp_next(u, (unsigned)field, 1);
        pull = save < 0 ? -1 : lp_next(u, (unsigned)save, 1);
        sec = pull < 0 ? -1 : lp_next(u, (unsigned)pull, 1);
        sub = sec < 0 ? -1 : lp_next(u, (unsigned)sec, 1);

        if (sub < 0 || !lp_line_is(&u->lines[carry], "clc") || !lp_is(&u->lines[add], "adc") ||
            !lp_line_is(&u->lines[push], "pha") || !lp_is(&u->lines[field], "lda") ||
            !lp_is(&u->lines[save], "sta") || !lp_line_is(&u->lines[pull], "pla") ||
            !lp_line_is(&u->lines[sec], "sec") || !lp_is(&u->lines[sub], "sbc"))
            continue;

        q = lp_operand(&u->lines[add], &m);
        src = lp_operand(&u->lines[field], &k);
        slot = lp_operand(&u->lines[save], &b);

        if (m < 3 || strncmp(q + m - 2, ",s", 2) || k != 9 || strncmp(src, "a:$", 3) ||
            src[7] != ',' || (src[8] != 'x' && src[8] != 'y') || lp_workspace_word(slot, b) < 0 ||
            !lp_operand_is(&u->lines[sub], slot, b))
            continue;

        snprintf(moved, sizeof moved, "    lda %.*s\n    sta %.*s\n", (int)k, src, (int)b, slot);
        lp_insert(start, moved);
        u->lines[push].deleted = u->lines[field].deleted = u->lines[save].deleted =
            u->lines[pull].deleted = 1;
        return 1;
    }

    return 0;
}

static int fr_arguments_above_frame(const LpLine *l, int available);

/* A word frame that has no remaining Y or S-relative references can
 * disappear even when the body still makes ordinary ABI calls. */
static int lp_unused_push_frame(LpUnit *u, Function *f, size_t at)
{
    unsigned first = 0, i, j, pushes = 0, returns = 0;
    int saves_y, frame_y = 0, frame_bytes, store_depths = 0, rebase_arguments = 0,
                 discarded_stores = 0;
    int next, ready, *depth, ok = 0;
    LpLine *copy;
    LpUnit trial = *u;

    (void)at;

    if (lp_state.parser->no_stack_frames || u->indirect || reg_width(f->symbol->type) > 2)
        return 0;

    while (first < u->count && !u->lines[first].op) {
        ++first;
    }

    if (first == u->count || u->lines[first].x8)
        return 0;

    saves_y = lp_line_is(&u->lines[first], "phy");
    next = saves_y ? lp_next(u, first, 1) : (int)first;
    ready = saves_y ? (int)first : -1;

    while (next >= 0 && lp_line_is(&u->lines[next], "pha") && !u->lines[next].m8 && pushes < 4) {
        ++pushes;
        ready = next;
        next = lp_next(u, (unsigned)next, 1);
    }

    if (saves_y) {
        int setup = next < 0 ? -1 : lp_next(u, (unsigned)next, 1);

        if (setup >= 0 && lp_line_is(&u->lines[next], "tsc") &&
            lp_line_is(&u->lines[setup], "tay")) {
            ready = setup;
            frame_y = 1;
        }
    } else if (!pushes)
        return 0;

    frame_bytes = 2 * ((int)pushes + saves_y);

    for (i = (unsigned)ready + 1; i < u->count; ++i) {
        if (lp_line_is(&u->lines[i], "sep #$20") || lp_line_is(&u->lines[i], "rep #$20"))
            u->lines[i].use = 0;
    }

    lp_liveness(u);

    if (frame_y && (u->lines[ready].out & (LP_A | LP_N | LP_Z)))
        return 0;

    copy = allocate(u->count * sizeof *copy);
    memcpy(copy, u->lines, u->count * sizeof *copy);
    trial.lines = copy;
    depth = allocate(u->count * sizeof *depth);

    for (i = first; i <= (unsigned)ready; ++i) {
        copy[i].op = NULL;
    }

    for (i = (unsigned)ready + 1; i < u->count; ++i) {
        LpLine *l = &u->lines[i];
        size_t n;
        const char *p = lp_operand(l, &n);

        if (!l->op || !copy[i].op)
            continue;
        if (l->target >= 0 && l->target <= ready)
            goto done;

        if (lp_is(l, "rts") || lp_is(l, "rtl")) {
            int prev = lp_next(u, i, -1);

            if (saves_y) {
                if (prev < 0 || !lp_line_is(&u->lines[prev], "ply"))
                    goto done;

                copy[prev].op = NULL;
                prev = lp_next(u, (unsigned)prev, -1);
            }

            for (j = 0; j < pushes; ++j) {
                if (prev < 0 || !lp_line_is(&u->lines[prev], "plx") || u->lines[prev].x8 ||
                    (u->lines[prev].out & (LP_X | LP_N | LP_Z)))
                    goto done;

                copy[prev].op = NULL;
                prev = lp_next(u, (unsigned)prev, -1);
            }

            ++returns;
            continue;
        }

        if (l->call) {
            Symbol *callee = lp_callee(l);

            if (l->ends || !callee || callee->interrupt)
                goto done;
        } else if (saves_y && lp_is(l, "ply")) {
            int ret = lp_next(u, i, 1);

            if (ret < 0 || (!lp_is(&u->lines[ret], "rts") && !lp_is(&u->lines[ret], "rtl")))
                goto done;
        } else if (saves_y && !lp_is(l, "plx") && ((l->use | l->def) & LP_Y))
            goto done;

        if (!frame_y && n >= 3 && p[n - 2] == ',' && p[n - 1] == 's' && !lp_state.is_volatile &&
            (!lp_state.frame_address || (f->uses_varargs && !u->calls)) &&
            !body_asm_statements(f->body)) {
            char *end;
            long offset = strtol(p, &end, 10);

            if (!store_depths) {
                if (!lp_stack_depths(u, first, depth))
                    goto done;

                store_depths = 1;
            }

            /* The operand is above the incoming return address; temporary
             * pushes still contribute their original depth after rebasing. */
            if (depth[i] >= frame_bytes && end == p + n - 2 &&
                offset > depth[i] + 2 + lp_state.parser->long_return && offset <= 255) {
                rebase_arguments = 1;
                continue;
            }
        }

        if ((lp_is(l, "sta") || lp_is(l, "lda")) && n >= 3 && p[n - 2] == ',' && p[n - 1] == 's') {
            char *end;
            long offset = strtol(p, &end, 10);
            int first_local;

            if (saves_y || lp_state.frame_address || lp_state.is_volatile ||
                lp_state.parser->no_private_regions || frame_address_visible(f->body) ||
                body_asm_statements(f->body) || end != p + n - 2 || offset < 1 || offset > 255)
                goto done;

            if (!store_depths) {
                if (!lp_stack_depths(u, first, depth))
                    goto done;

                store_depths = 1;
            }

            first_local = depth[i] - 2 * (int)pushes + 1;

            if (first_local < 1 || offset < first_local || offset + lp_width(l) - 1 > depth[i])
                goto done;

            if (lp_is(l, "lda")) {
                int mask = lp_next(u, i, 1), store = mask < 0 ? -1 : lp_next(u, (unsigned)mask, 1);

                if (store < 0 || !lp_is(&u->lines[store], "sta") ||
                    !lp_operand_is(&u->lines[store], p, n) || u->lines[mask].m8 != l->m8 ||
                    u->lines[store].m8 != l->m8 ||
                    (!lp_is(&u->lines[mask], "and") && !lp_is(&u->lines[mask], "ora") &&
                     !lp_is(&u->lines[mask], "eor")) ||
                    lp_immediate(&u->lines[mask]) < 0 ||
                    (u->lines[store].out & (LP_A | LP_N | LP_Z)))
                    goto done;

                copy[mask].op = copy[store].op = NULL;
            }

            copy[i].op = NULL;
            discarded_stores = 1;
            continue;
        }

        if (lp_is(l, "tsc") || lp_is(l, "tsx") || lp_is(l, "txs") || l->use == LP_ALL ||
            (n >= 2 && p[n - 2] == ',' && p[n - 1] == 's') ||
            (n >= 5 && p[n - 5] == ',' && p[n - 4] == 's' && p[n - 3] == ')'))
            goto done;
    }

    if (!returns || !lp_stack_depths(&trial, 0, depth))
        goto done;

    if (rebase_arguments || discarded_stores) {
        for (i = (unsigned)ready + 1; i < u->count; ++i) {
            if (u->lines[i].call && !fr_arguments_above_frame(&u->lines[i], depth[i]))
                goto done;
        }
    }

    if (rebase_arguments) {
        for (i = (unsigned)ready + 1; i < u->count; ++i) {
            if (copy[i].op) {
                size_t n;
                const char *p = lp_operand(&u->lines[i], &n);

                if (n >= 3 && p[n - 2] == ',' && p[n - 1] == 's')
                    lp_set(&u->lines[i], "    %.3s %d,s", u->lines[i].op, atoi(p) - frame_bytes);
            }
        }
    }

    for (i = first; i < u->count; ++i) {
        if (u->lines[i].op && !copy[i].op)
            u->lines[i].deleted = 1;
    }

    ok = 1;
done:
    free(depth);
    free(copy);
    return ok;
}

/* A wrapper can have an unread saved X below its outgoing argument block.
 * Recognize the call and exact caller cleanup before dropping the save.
 * The saved word is separate from the outgoing arguments at call entry. */
static int lp_unused_call_save(LpUnit *u, Function *f, size_t at)
{
    unsigned first = 0, i;
    int call = -1, read, clear, add, cleanup, pull, ret, arguments, *depth, ok = 0;

    (void)at;

    if (lp_state.parser->no_stack_frames || u->indirect || u->calls != 1 ||
        frame_address_visible(f->body) || statement_inline_markers(f->body))
        return 0;

    while (first < u->count && !u->lines[first].op) {
        ++first;
    }

    if (first == u->count || !lp_line_is(&u->lines[first], "phx") || u->lines[first].x8)
        return 0;

    for (i = first + 1; i < u->count; ++i) {
        if (u->lines[i].call) {
            call = (int)i;
            break;
        }
    }

    if (call < 0 || u->lines[call].ends || !lp_callee(&u->lines[call]))
        return 0;

    read = lp_next(u, (unsigned)call, 1);
    clear = read < 0 ? -1 : lp_next(u, (unsigned)read, 1);
    add = clear < 0 ? -1 : lp_next(u, (unsigned)clear, 1);
    cleanup = add < 0 ? -1 : lp_next(u, (unsigned)add, 1);
    pull = cleanup < 0 ? -1 : lp_next(u, (unsigned)cleanup, 1);

    if (cleanup >= 0 && pull < 0) {
        i = (unsigned)cleanup + 1;

        while (i < u->count && u->lines[i].text[0] == ';') {
            ++i;
        }

        if (i < u->count && u->lines[i].label && !strncmp(u->lines[i].text, "return_", 7))
            pull = lp_next(u, i, 1);
    }

    ret = pull < 0 ? -1 : lp_next(u, (unsigned)pull, 1);

    if (ret < 0 || !lp_line_is(&u->lines[read], "tsc") || !lp_line_is(&u->lines[clear], "clc") ||
        !lp_is(&u->lines[add], "adc") || u->lines[add].m8 ||
        (arguments = (int)lp_immediate(&u->lines[add])) <= 0 ||
        !lp_line_is(&u->lines[cleanup], "tcs") || !lp_line_is(&u->lines[pull], "plx") ||
        u->lines[pull].x8 || (!lp_is(&u->lines[ret], "rts") && !lp_is(&u->lines[ret], "rtl")))
        return 0;

    for (i = first + 1; i < u->count; ++i) {
        LpLine *l = &u->lines[i];
        size_t n;
        const char *p = lp_operand(l, &n);

        if (!l->op)
            continue;
        if (i > (unsigned)ret || l->target >= 0 || lp_branch(l) || l->use == LP_ALL ||
            (l->ends && i != (unsigned)ret) || lp_is(l, "tsx") || lp_is(l, "txs") ||
            (lp_is(l, "tsc") && i != (unsigned)read) ||
            (lp_is(l, "tcs") && i != (unsigned)cleanup) ||
            (n >= 2 && p[n - 2] == ',' && p[n - 1] == 's') ||
            (n >= 5 && !memcmp(p + n - 5, ",s),y", 5)))
            return 0;
    }

    lp_liveness(u);

    if ((u->lines[cleanup].out & (LP_A | LP_FLAGS)) || (u->lines[pull].out & (LP_X | LP_N | LP_Z)))
        return 0;

    depth = allocate(u->count * sizeof *depth);

    if (lp_stack_depths(u, first, depth) && depth[call] == arguments + 2 && depth[pull] == 2) {
        ok = 1;

        for (i = first + 1; i <= (unsigned)pull; ++i) {
            if (depth[i] < 2) {
                ok = 0;
                break;
            }
        }
    }

    free(depth);

    if (ok)
        u->lines[first].deleted = u->lines[pull].deleted = 1;

    return ok;
}

static int fr_arguments_above_frame(const LpLine *l, int available)
{
    Symbol *callee = lp_callee(l);
    int required = 0;

    if (l->ends || !callee || callee->interrupt || callee->old_style || callee->variadic ||
        callee->param_count < 0 || structure_object(callee->type))
        return 0;

    for (int k = 0; k < callee->param_count; ++k) {
        if (!register_parameter(k, callee->params[k]))
            required += argument_width(callee->params[k]);
    }

    return available >= required;
}

/* Aggregate arguments alone can mark the source frame address-visible.
 * After lowering, a literal-only outgoing argument area cannot carry a
 * pointer into the frame. Accept only this straight-line calling shape. */
static int fr_literal_call_frame(LpUnit *u, Function *f, unsigned ready, int frame,
                                 const int *depth)
{
    if (body_asm_statements(f->body) || f->symbol->interrupt)
        return 0;

    lp_liveness(u);

    for (unsigned i = ready; i < u->count; ++i) {
        LpLine *l = &u->lines[i];
        size_t n;
        const char *p = lp_operand(l, &n);

        if (!l->op)
            continue;

        if (l->target >= 0) {
            /* A forward error check may skip its branch veneer and a
             * nullary error call without changing argument construction. */
            unsigned j = i + 1;

            for (; j < (unsigned)l->target; ++j) {
                LpLine *skip = &u->lines[j];

                if (!skip->op)
                    continue;
                if (lp_is(skip, "jmp") && skip->target > (int)j)
                    continue;

                Symbol *callee = skip->call ? lp_callee(skip) : NULL;

                if (callee && callee->param_count == 0 && fr_arguments_above_frame(skip, 0))
                    continue;

                return 0;
            }

            if (j != (unsigned)l->target)
                return 0;

            continue;
        }

        if (l->x8)
            return 0;
        if (lp_line_is(l, "sep #$20") || lp_line_is(l, "rep #$20"))
            continue;

        if (l->m8) {
            /* A byte store cannot expose a frame address. Calls and stack
             * adjustments still require the public 16-bit register modes. */
            if ((lp_is(l, "lda") && lp_immediate(l) >= 0) ||
                (lp_is(l, "sta") && lp_private(p, n) && p[n - 1] == 's'))
                continue;

            return 0;
        }

        if (lp_is(l, "tcs")) {
            if (l->out & LP_A)
                return 0;
        } else if (lp_is(l, "lda") || lp_is(l, "ldx") || lp_is(l, "adc") || lp_is(l, "cmp") ||
                   lp_is(l, "cpx") || lp_is(l, "cpy")) {
            if (lp_immediate(l) < 0)
                return 0;
        } else if (lp_is(l, "sta")) {
            if (!lp_private(p, n) || p[n - 1] != 's')
                return 0;
        } else if (lp_is(l, "pha")) {
            /* The last aggregate word may already be in A. As with PEA,
             * a literal push cannot pass an address into this frame. */
            int prev = (int)i - 1;

            for (; prev >= 0; --prev) {
                LpLine *prior = &u->lines[prev];

                if (prior->text[0] == ';' || lp_is(prior, "sta") || lp_is(prior, "pea"))
                    continue;
                if (!u->indirect && (!strncmp(prior->text, ".export __inlined_", 18) ||
                                     (lp_fallthrough_label(prior) && prior->first_incoming < 0)))
                    continue;

                break;
            }

            if (prev < 0 || !lp_is(&u->lines[prev], "lda") || lp_immediate(&u->lines[prev]) < 0)
                return 0;
        } else if (l->call) {
            if (!fr_arguments_above_frame(l, depth[i] - frame))
                return 0;
        } else if (!lp_is(l, "pea") && !lp_is(l, "tsc") && !lp_is(l, "clc") && !lp_is(l, "tax") &&
                   !lp_is(l, "txa") && !lp_is(l, "rts") && !lp_is(l, "rtl"))
            return 0;
    }

    return 1;
}

/* Once a literal call wrapper has no stack references, its own frame
 * reservation and release cancel. The outgoing argument pushes remain. */
static int fr_drop_unused_reservation(LpUnit *u, Function *f, unsigned entry, unsigned ready,
                                      int frame, const int *depth)
{
    int release = -1, restored = 0;

    if (lp_state.parser->no_stack_frames || body_asm_statements(f->body) ||
        (lp_state.frame_address && !fr_literal_call_frame(u, f, ready, frame, depth)))
        return 0;

    lp_liveness(u);

    for (unsigned i = ready; i < u->count; ++i) {
        LpLine *l = &u->lines[i];

        if (!l->op)
            continue;

        size_t n;
        const char *op = lp_operand(l, &n);

        if ((n >= 2 && op[n - 2] == ',' && op[n - 1] == 's') ||
            (lp_is(l, "tcs") && (l->out & (LP_FLAGS | LP_A))) ||
            (l->call && !fr_arguments_above_frame(l, depth[i] - frame)))
            return 0;

        if (lp_is(l, "tsc") && depth[i] == frame) {
            int clear = lp_next(u, i, 1);
            int add = clear < 0 ? -1 : lp_next(u, (unsigned)clear, 1);
            int set = add < 0 ? -1 : lp_next(u, (unsigned)add, 1);

            if (release >= 0 || set < 0 || !lp_line_is(&u->lines[clear], "clc") ||
                !lp_is(&u->lines[add], "adc") || lp_immediate(&u->lines[add]) != frame ||
                !lp_line_is(&u->lines[set], "tcs"))
                return 0;

            release = (int)i;
            restored = set;
        }
    }

    if (release < 0)
        return 0;

    for (unsigned i = entry; i <= ready; ++i) {
        if (u->lines[i].op)
            u->lines[i].deleted = 1;
    }

    for (int i = release; i <= restored; ++i) {
        if (u->lines[i].op)
            u->lines[i].deleted = 1;
    }

    return 1;
}

/* A private S-relative frame can retain spills after its loads have been
 * forwarded. Normalize the operands through temporary pushes before doing
 * byte liveness across the final emitted control flow. */
static int lp_dead_stack_frame_stores(LpUnit *u, Function *f, size_t at)
{
    struct {
        uint64_t read, write, live;
        int local_store;
    } *bytes;

    unsigned entry = 0, i;
    int carry, subtract, ready, frame, saved = 0, allocated, *depth, changed = 0, again = 1;

    (void)at;

    if (lp_state.parser->no_private_regions || lp_state.is_volatile || u->indirect)
        return 0;

    while (entry < u->count) {
        LpLine *l = &u->lines[entry];
        size_t n;
        const char *p = lp_operand(l, &n);

        if (l->op && !((lp_is(l, "sta") || lp_is(l, "stx")) && lp_workspace_word(p, n) >= 0))
            break;

        ++entry;
    }

    if (entry < u->count && lp_line_is(&u->lines[entry], "phy") && !u->lines[entry].x8) {
        int setup = lp_next(u, entry, 1);

        if (setup < 0 || lp_state.frame_address || body_asm_statements(f->body))
            return 0;

        saved = 2;
        entry = (unsigned)setup;
    }

    if (entry == u->count || !lp_line_is(&u->lines[entry], "tsc"))
        return 0;

    carry = lp_next(u, entry, 1);
    subtract = carry < 0 ? -1 : lp_next(u, (unsigned)carry, 1);
    ready = subtract < 0 ? -1 : lp_next(u, (unsigned)subtract, 1);

    if (ready < 0 || (unsigned)(ready + 1) >= u->count || !lp_line_is(&u->lines[carry], "sec") ||
        !lp_is(&u->lines[subtract], "sbc") || u->lines[subtract].m8 ||
        (frame = (int)lp_immediate(&u->lines[subtract])) < 1 || frame > 64 ||
        !lp_line_is(&u->lines[ready], "tcs"))
        return 0;

    for (i = 0; i < u->count; ++i) {
        if (u->lines[i].target >= 0 && u->lines[i].target <= ready)
            return 0;
    }

    depth = allocate(u->count * sizeof *depth);
    bytes = allocate(u->count * sizeof *bytes);
    allocated = frame + saved;

    if (!lp_stack_depths_from(u, (unsigned)ready + 1, allocated, depth))
        goto done;
    if (lp_state.frame_address && !fr_literal_call_frame(u, f, (unsigned)ready, frame, depth))
        goto done;

    for (i = (unsigned)ready + 1; i < u->count; ++i) {
        LpLine *l = &u->lines[i];
        size_t n;
        const char *p = lp_operand(l, &n);
        char *end;
        int offset, b, width;
        uint64_t mask = 0;

        if (depth[i] < 0 || !l->op)
            continue;
        if ((depth[i] > saved && depth[i] < allocated) ||
            (!depth[i] && lp_stack_op(l) && !l->ends) ||
            (i + 1 < u->count && depth[i] >= allocated && depth[i + 1] == saved && !l->ends &&
             (!lp_is(l, "tcs") || depth[i] != allocated)))
            goto done;
        if (saved && l->call && !fr_arguments_above_frame(l, depth[i] - allocated))
            goto done;

        if (lp_is(l, "tsc")) {
            int clear = lp_next(u, i, 1), add = clear < 0 ? -1 : lp_next(u, (unsigned)clear, 1);
            int set = add < 0 ? -1 : lp_next(u, (unsigned)add, 1);

            if (set < 0 || !lp_line_is(&u->lines[clear], "clc") || !lp_is(&u->lines[add], "adc") ||
                lp_immediate(&u->lines[add]) < 0 || !lp_line_is(&u->lines[set], "tcs"))
                goto done;
        }

        if ((l->use == LP_ALL && !lp_line_is(l, "sep #$20") && !lp_line_is(l, "rep #$20")) ||
            lp_is(l, "tsx") || (n >= 2 && p[n - 2] == ',' && p[n - 1] == 'y'))
            goto done;
        if (n < 3 || p[n - 2] != ',' || p[n - 1] != 's')
            continue;

        offset = (int)strtol(p, &end, 10);

        if (end != p + n - 2 || offset < 0 || offset > 255 || depth[i] < allocated)
            goto done;

        offset += allocated - depth[i];
        width = lp_width(l);

        for (b = offset; b < offset + width; ++b) {
            if (b >= 1 && b <= frame)
                mask |= UINT64_C(1) << (b - 1);
        }

        if (lp_is(l, "sta")) {
            bytes[i].write = mask;
            bytes[i].local_store = offset >= 1 && offset + width - 1 <= frame;
        } else
            bytes[i].read = mask;
    }

    while (again) {
        again = 0;

        for (i = u->count; i-- > (unsigned)ready + 1;) {
            LpLine *l = &u->lines[i];
            uint64_t out = (!l->ends && i + 1 < u->count) ? bytes[i + 1].live : 0;
            uint64_t live;

            if (l->target >= 0)
                out |= bytes[l->target].live;

            live = bytes[i].read | (out & ~bytes[i].write);

            if (live != bytes[i].live) {
                bytes[i].live = live;
                again = 1;
            }
        }
    }

    for (i = (unsigned)ready + 1; i < u->count; ++i) {
        if (bytes[i].local_store) {
            LpLine *l = &u->lines[i];
            uint64_t out = (!l->ends && i + 1 < u->count) ? bytes[i + 1].live : 0;

            if (l->target >= 0)
                out |= bytes[l->target].live;

            if (!(bytes[i].write & out)) {
                l->deleted = 1;
                changed = 1;
            }
        }
    }

    if (!changed && !saved)
        changed = fr_drop_unused_reservation(u, f, entry, (unsigned)ready, frame, depth);

done:
    free(bytes);
    free(depth);
    return changed;
}

/* Remove saves across straight-line code that already preserves the index */
static int lp_remove_index_save(LpUnit *u, Function *f, size_t at)
{
    unsigned i, j;
    (void)f;
    (void)at;

    if (u->indirect)
        return 0;

    lp_liveness(u);

    for (i = 0; i < u->count; ++i) {
        LpLine *push = &u->lines[i];

        unsigned reg = lp_is(push, "phx") ? LP_X : lp_is(push, "phy") ? LP_Y : 0;
        unsigned last_target = i;

        if (!reg)
            continue;

        for (j = i + 1; j < u->count; ++j) {
            LpLine *l = &u->lines[j];
            size_t n;
            const char *p = lp_operand(l, &n);

            if (l->label && !lp_inner_label(u, j, i + 1, j))
                break;
            if (!l->op)
                continue;

            if (lp_is(l, reg == LP_X ? "plx" : "ply")) {
                if (j >= last_target && !(l->out & (LP_N | LP_Z))) {
                    push->deleted = l->deleted = 1;
                    return 1;
                }

                break;
            }

            if (l->target > (int)j && !l->call) {
                if ((unsigned)l->target > last_target)
                    last_target = (unsigned)l->target;

                continue;
            }
            if (l->call || l->ends || lp_branch(l) || l->use == LP_ALL || (l->def & reg) ||
                !strncmp(l->op, "ph", 2) || !strncmp(l->op, "pl", 2) || lp_is(l, "tsc") ||
                lp_is(l, "tsx") || lp_is(l, "tcs") || lp_is(l, "txs") ||
                (n >= 2 && p[n - 2] == ',' && p[n - 1] == 's') ||
                (n >= 5 && p[n - 5] == ',' && p[n - 4] == 's' && p[n - 3] == ')'))
                break;
        }
    }

    return 0;
}

/* Keep early exits frameless when every path through the suffix enters
 * through the first Y save. Route only suffix exits through the restore. */
static int lp_place_late_y_save(LpUnit *u, unsigned first, unsigned ret)
{
    unsigned i, tail = ret, early = 0, tag;
    char restore[96], definition[120];

    while (tail > first && !u->lines[tail - 1].op) {
        --tail;
    }

    if (tail <= first)
        return 0;

    for (i = 0; i < u->count; ++i) {
        LpLine *l = &u->lines[i];

        if (l->target < 0)
            continue;

        if (i < first) {
            if ((unsigned)l->target >= tail)
                ++early;
            else if ((unsigned)l->target > first)
                return 0;
        } else if ((unsigned)l->target <= first)
            return 0;
        else if ((unsigned)l->target >= tail && !lp_branch(l) && !lp_is(l, "jmp"))
            return 0;
    }

    if (!early)
        return 0;

    tag = lp_next_label();
    snprintf(restore, sizeof restore, "cg_%s_%u", lp_state.parser->unit, tag);
    snprintf(definition, sizeof definition, "%s = *\n    ply\n", restore);
    lp_insert(&u->lines[first], "    phy\n");
    lp_insert(&u->lines[tail], definition);

    for (i = first; i < ret; ++i) {
        LpLine *l = &u->lines[i];

        if (l->target >= 0 && (unsigned)l->target >= tail) {
            if (lp_is(l, "jmp"))
                lp_set(l, "    jmp .loword(%s)", restore);
            else
                lp_set(l, "    %.3s %s", l->op, restore);
        }
    }

    return 1;
}

/* If Y is used only inside disjoint locally saved regions, preserve it once
 * across the whole function. The original stack-depth graph proves that
 * every Y use is protected and that no edge enters or leaves a save live. */
static int lp_hoist_local_y_saves(LpUnit *u, Function *f, size_t at)
{
    unsigned i, entry = 0, saves = 0, restores = 0, first_save = 0, returns = 0, ret = 0;
    int *depth, ok = 0, plain_push = 0, late;

    (void)at;

    if (u->calls || u->indirect || f->symbol->interrupt || lp_state.parser->no_register_cursors)
        return 0;

    while (entry < u->count && !u->lines[entry].op) {
        ++entry;
    }

    if (entry == u->count)
        return 0;

    depth = allocate(u->count * sizeof *depth);

    if (!lp_stack_depths(u, 0, depth))
        goto done;

    for (i = entry; i < u->count; ++i) {
        LpLine *l = &u->lines[i];
        size_t n;
        const char *p = lp_operand(l, &n);

        if (l->label && plain_push)
            goto done;
        if (!l->op)
            continue;
        if (depth[i] < 0 || l->x8 || (l->target >= 0 && (unsigned)l->target <= entry))
            goto done;

        if (lp_is(l, "pha")) {
            if (plain_push || depth[i] != 0 || l->m8)
                goto done;

            plain_push = 1;
        } else if (lp_is(l, "pla")) {
            if (!plain_push || depth[i] != 2 || l->m8)
                goto done;

            plain_push = 0;
        } else if (plain_push && (l->target >= 0 || l->ends || ((l->use | l->def) & LP_Y)))
            goto done;
        else if (lp_is(l, "phy")) {
            if (depth[i] != 0)
                goto done;
            if (!saves)
                first_save = i;

            ++saves;
        } else if (lp_is(l, "ply")) {
            if (depth[i] != 2)
                goto done;

            ++restores;
        } else if (lp_is(l, "rts") || lp_is(l, "rtl")) {
            if (depth[i])
                goto done;

            ++returns;
            ret = i;
        } else if (lp_line_is(l, "rep #$20") || lp_line_is(l, "sep #$20")) {
            continue;
        } else if (l->use == LP_ALL || lp_is(l, "tsc") || lp_is(l, "tsx") || lp_is(l, "tcs") ||
                   lp_is(l, "txs") || !strncmp(l->op, "ph", 2) || !strncmp(l->op, "pl", 2) ||
                   (n >= 2 && p[n - 2] == ',' && p[n - 1] == 's') ||
                   (n >= 5 && p[n - 5] == ',' && p[n - 4] == 's' && p[n - 3] == ')') ||
                   (((l->use | l->def) & LP_Y) && depth[i] != 2))
            goto done;
    }

    if (plain_push || saves < 2 || !restores)
        goto done;

    /* Removing PLY changes N/Z, so check the flag uses independently of
     * accumulator-width switches. */
    for (i = entry; i < u->count; ++i) {
        if (lp_line_is(&u->lines[i], "rep #$20") || lp_line_is(&u->lines[i], "sep #$20"))
            u->lines[i].use = 0;
    }

    lp_liveness(u);

    for (i = entry; i < u->count; ++i) {
        if (lp_is(&u->lines[i], "ply") && (u->lines[i].out & (LP_N | LP_Z)))
            goto done;
    }

    late = returns == 1 && lp_place_late_y_save(u, first_save, ret);

    if (!late)
        lp_insert(&u->lines[entry], "    phy\n");

    for (i = entry; i < u->count; ++i) {
        LpLine *l = &u->lines[i];

        if (lp_is(l, "phy") || lp_is(l, "ply"))
            l->deleted = 1;
        else if (!late && (lp_is(l, "rts") || lp_is(l, "rtl")))
            lp_insert(l, "    ply\n");
    }

    ok = 1;
done:
    free(depth);
    return ok;
}
