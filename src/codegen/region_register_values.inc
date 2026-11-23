/* Repeated copies into scratch stay redundant across joins when all incoming
 * edges established the same copy and neither private home was overwritten. */
typedef struct {
    const char *frame, *scratch;
    size_t frame_length, scratch_length;
    int frame_offset, scratch_offset;
} FrameWordCopy;

static int lp_word_copy_input(const LpUnit *u, const PrState *states, unsigned store,
                              const FrameWordCopy *copy)
{
    int load = lp_next(u, store, -1);

    if (load < 0 || !states[load].frame || u->lines[load].m8 || !lp_is(&u->lines[load], "lda") ||
        !lp_operand_is(&u->lines[load], copy->frame, copy->frame_length))
        return -1;

    for (unsigned j = (unsigned)load + 1; j < store; ++j) {
        if (!lp_internal_path_marker(u, j, (unsigned)load))
            return -1;
    }

    return load;
}

static int lp_preserved_frame_copy(const LpUnit *u, const PrState *states, unsigned at,
                                   const FrameWordCopy *copy, unsigned *budget)
{
    for (;;) {
        const LpLine *line = &u->lines[at];
        int incoming = line->first_incoming, has_incoming = 0;

        if (!*budget)
            return 0;

        --*budget;

        for (; incoming >= 0; incoming = u->lines[incoming].next_incoming) {
            if ((unsigned)incoming >= at)
                return 0;
            if (!states[incoming].seen)
                continue;
            if (!lp_preserved_frame_copy(u, states, (unsigned)incoming, copy, budget))
                return 0;

            has_incoming = 1;
        }

        if (!at || u->lines[at - 1].ends || !states[at - 1].seen)
            return has_incoming;

        --at;
        line = &u->lines[at];

        if (!line->op)
            continue;
        if (line->call || line->use == LP_ALL || lp_line_is(line, "tcs") ||
            lp_line_is(line, "txs") || !strncmp(line->op, "mvn ", 4) ||
            !strncmp(line->op, "mvp ", 4))
            return 0;
        if (lp_may_write(line, copy->scratch, copy->scratch_length, 2))
            return lp_is(line, "sta") && !line->m8 &&
                   lp_operand_is(line, copy->scratch, copy->scratch_length) &&
                   lp_word_copy_input(u, states, at, copy) >= 0;

        if (lp_store_op(line)) {
            size_t n;
            const char *op = lp_operand(line, &n);

            if (states[at].frame && n == 9 && !strncmp(op, "a:$", 3) && op[7] == ',' &&
                op[8] == 'y' &&
                lp_overlaps_n(line, (int)strtol(op + 3, NULL, 16), copy->frame_offset, 2))
                return 0;

            /* The prologue owns these two frame bytes. A different Y
             * cursor or a stack-relative write needs its own alias proof. */
            if (n >= 2 && op[n - 2] == ',' &&
                (op[n - 1] == 's' || (op[n - 1] == 'y' && !states[at].frame)))
                return 0;
        }
    }
}

static int lp_reuse_frame_copies(LpUnit *u, Function *f, size_t at)
{
    PrState *states = NULL;

    (void)at;

    if (!f->frame || lp_state.frame_address || lp_state.is_volatile || u->indirect ||
        lp_state.parser->no_private_regions || lp_state.parser->no_value_reuse ||
        body_asm_statements(f->body) || !lp_fixed_workspace(u))
        return 0;

    lp_liveness(u);

    for (unsigned i = 0; i < u->count; ++i) {
        LpLine *store = &u->lines[i];
        FrameWordCopy copy;
        int load;

        unsigned budget = 300;

        if (!lp_is(store, "sta") || store->m8 || (store->out & (LP_A | LP_N | LP_Z)))
            continue;

        copy.scratch = lp_operand(store, &copy.scratch_length);
        copy.scratch_offset = lp_workspace_word(copy.scratch, copy.scratch_length);

        if (copy.scratch_offset < 0 || copy.scratch_offset > 30)
            continue;

        load = lp_next(u, i, -1);

        if (load < 0 || !lp_is(&u->lines[load], "lda") || u->lines[load].m8)
            continue;

        copy.frame = lp_operand(&u->lines[load], &copy.frame_length);

        if (copy.frame_length != 9 || strncmp(copy.frame, "a:$", 3) ||
            strncmp(copy.frame + 7, ",y", 2))
            continue;

        copy.frame_offset = (int)strtol(copy.frame + 3, NULL, 16);

        if (copy.frame_offset <= 0 || copy.frame_offset + 1 > (int)f->frame)
            continue;
        if (!states)
            states = pr_states(u);
        if (lp_word_copy_input(u, states, i, &copy) != load ||
            !lp_preserved_frame_copy(u, states, (unsigned)load, &copy, &budget))
            continue;

        u->lines[load].deleted = store->deleted = 1;
        lp_insert(&u->lines[load], "; reused frame word in direct-page scratch\n");
        free(states);
        return 1;
    }

    free(states);
    return 0;
}

/* A loop with a shared offset can compare the just-stored value in X and
 * enter the next iteration after its index load. Continue edges that did
 * not advance the offset seed X from the home at their jump */
static int lp_workspace_index_backedge(LpUnit *u, Function *f, size_t at)
{
    int known;
    unsigned char *targets;

    (void)at;

    if (u->indirect || lp_state.parser->no_strength_reduction ||
        lp_state.parser->no_register_cursors || lp_state.parser->no_index_elimination ||
        lp_state.parser->no_value_reuse || body_asm_statements(f->body) || !lp_fixed_workspace(u))
        return 0;

    targets = lp_local_targets(u, &known);

    /* The unsigned word quotient receives both operands in DP and
     * preserves X. Any live-out value still propagates through the call */
    for (unsigned i = 0; i < u->count; ++i) {
        if (u->lines[i].call && lp_line_is(&u->lines[i], "jsr .loword(__uquot16)"))
            u->lines[i].use = LP_Y;
    }

    lp_liveness(u);

    for (unsigned i = 0; known && i < u->count; ++i) {
        LpLine *edge = &u->lines[i];
        int head = edge->target, branch, compare, load, store, index, cold[8], count = 0, can_cpx;
        size_t length, bound_length;
        const char *home, *bound;

        if (head < 0 || (unsigned)head >= i || (!lp_is(edge, "jmp") && !lp_is(edge, "bra")) ||
            edge->x8)
            continue;

        branch = lp_next_fallthrough(u, i, -1, targets, known);

        if (branch < 0 || (!lp_is(&u->lines[branch], "beq") && !lp_is(&u->lines[branch], "bne")) ||
            u->lines[branch].target <= (int)i)
            continue;

        compare = lp_next_fallthrough(u, (unsigned)branch, -1, targets, known);

        if (compare < 0 || !lp_is(&u->lines[compare], "cmp") || u->lines[compare].m8 ||
            u->lines[compare].x8 || (u->lines[compare].use & LP_X) ||
            (u->lines[compare].out & (LP_A | LP_X)))
            continue;

        bound = lp_operand(&u->lines[compare], &bound_length);
        can_cpx =
            lp_workspace_word(bound, bound_length) >= 0 || lp_immediate(&u->lines[compare]) >= 0;
        load = lp_next_fallthrough(u, (unsigned)compare, -1, targets, known);

        if (load < 0 || !lp_is(&u->lines[load], "lda") || u->lines[load].m8 || u->lines[load].x8)
            continue;

        home = lp_operand(&u->lines[load], &length);

        if (lp_workspace_word(home, length) < 0)
            continue;

        index = lp_next_fallthrough(u, (unsigned)head, 1, targets, known);

        if (index <= head || index >= load || !lp_is(&u->lines[index], "ldx") ||
            u->lines[index].x8 || (u->lines[index].out & (LP_N | LP_Z)) ||
            !lp_operand_is(&u->lines[index], home, length))
            continue;

        for (store = load - 1; store > index; --store) {
            LpLine *line = &u->lines[store];

            if (line->op || (!lp_fallthrough_label(line) && line->text[0] != ';'))
                break;
        }

        if (store <= index || !lp_is(&u->lines[store], "sta") || u->lines[store].m8 ||
            u->lines[store].x8 || !lp_operand_is(&u->lines[store], home, length))
            continue;

        for (int j = store + 1; j <= load && count >= 0; ++j) {
            LpLine *line = &u->lines[j];

            if (j < load && line->length && line->text[0] != ';' && !lp_fallthrough_label(line)) {
                count = -1;
                break;
            }

            for (int p = line->first_incoming; p >= 0; p = u->lines[p].next_incoming) {
                LpLine *from = &u->lines[p];

                if (count == 8 || p <= index || p >= store || from->x8 ||
                    (!lp_is(from, "jmp") && !lp_is(from, "bra"))) {
                    count = -1;
                    break;
                }

                cold[count++] = p;
            }
        }

        if (count < 0)
            continue;

        unsigned id = lp_next_label();
        char text[96];

        lp_insert(&u->lines[store], "; carry workspace index across the loop backedge\n    tax\n");
        lp_set(&u->lines[store], "    stx %.*s", (int)length, home);

        for (int j = 0; j < count; ++j) {
            snprintf(text, sizeof text, "    ldx %.*s\n", (int)length, home);
            lp_insert(&u->lines[cold[j]], text);
        }

        if (can_cpx) {
            u->lines[load].deleted = 1;
            lp_set(&u->lines[compare], "    cpx %.*s", (int)bound_length, bound);
        } else
            lp_set(&u->lines[load], "    txa");

        snprintf(text, sizeof text, "cg_lp_%u:\n", id);
        lp_insert(&u->lines[index + 1], text);
        lp_set(edge, "    jmp .loword(cg_lp_%u)", id);
        free(targets);
        return 1;
    }

    free(targets);
    return 0;
}

/* Use the incoming accumulator before an independent X calculation would
 * overwrite it. Both arithmetic sequences start with their own carry. */
static int lp_schedule_entry_words(LpUnit *u, Function *f, size_t at)
{
    int save = -1, transfer, first_carry, first_op, first_store, reload, carry, op, store;
    int slots[3], first_register;
    size_t n, m;
    const char *old, *again;
    LpWorkspaceLive *memory;
    char text[128];

    (void)at;

    if (u->indirect || lp_state.is_volatile || lp_state.parser->no_value_reuse ||
        body_asm_statements(f->body) || !lp_fixed_workspace(u))
        return 0;

    for (unsigned i = 0; i < u->count; ++i) {
        if (u->lines[i].op) {
            save = (int)i;
            break;
        }
    }

    if (save < 0 || !lp_is(&u->lines[save], "sta") || u->lines[save].m8)
        return 0;

    old = lp_operand(&u->lines[save], &n);

    if ((slots[0] = lp_workspace_word(old, n)) < 0 || slots[0] > 30)
        return 0;

    transfer = lp_next(u, (unsigned)save, 1);

    if (transfer >= 0 && lp_line_is(&u->lines[transfer], "phy"))
        transfer = lp_next(u, (unsigned)transfer, 1);
    if (transfer < 0 || !lp_line_is(&u->lines[transfer], "txa"))
        return 0;

    first_carry = lp_next(u, (unsigned)transfer, 1);
    first_op = first_carry < 0 ? -1 : lp_next(u, (unsigned)first_carry, 1);
    first_store = first_op < 0 ? -1 : lp_next(u, (unsigned)first_op, 1);
    reload = first_store < 0 ? -1 : lp_next(u, (unsigned)first_store, 1);
    carry = reload < 0 ? -1 : lp_next(u, (unsigned)reload, 1);
    op = carry < 0 ? -1 : lp_next(u, (unsigned)carry, 1);
    store = op < 0 ? -1 : lp_next(u, (unsigned)op, 1);

    if (store < 0)
        return 0;

    first_register = lp_line_is(&u->lines[first_store], "tax");

    if ((!first_register && !lp_is(&u->lines[first_store], "sta")) ||
        !lp_is(&u->lines[store], "sta") || !lp_is(&u->lines[reload], "lda") ||
        !lp_operand_is(&u->lines[reload], old, n))
        return 0;

    for (int i = save + 1; i <= store; ++i) {
        const LpLine *l = &u->lines[i];

        if (l->m8 || l->x8 || (!l->op && !lp_internal_path_marker(u, (unsigned)i, (unsigned)save)))
            return 0;
    }

    for (unsigned i = 0; i < 2; ++i) {
        LpLine *set = &u->lines[i ? carry : first_carry], *arith = &u->lines[i ? op : first_op];

        if ((!lp_line_is(set, "clc") || !lp_is(arith, "adc")) &&
            (!lp_line_is(set, "sec") || !lp_is(arith, "sbc")))
            return 0;
        if (lp_immediate(arith) < 0)
            return 0;
        if (!i && first_register)
            continue;

        again = lp_operand(&u->lines[i ? store : first_store], &m);

        if ((slots[i + 1] = lp_workspace_word(again, m)) < 0 || slots[i + 1] > 30)
            return 0;
    }

    if (abs(slots[0] - slots[2]) < 2 ||
        (!first_register && (abs(slots[0] - slots[1]) < 2 || abs(slots[1] - slots[2]) < 2)))
        return 0;

    lp_liveness(u);

    if (u->lines[store].out & (LP_A | LP_FLAGS))
        return 0;

    memory = allocate(u->count * sizeof *memory);
    lp_workspace_liveness(u, memory, 0);

    if (memory[store].out & (3u << slots[0])) {
        free(memory);
        return 0;
    }

    free(memory);
    snprintf(text, sizeof text, "; calculate with incoming A before X\n%.*s\n%.*s\n%.*s\n",
             (int)u->lines[carry].length, u->lines[carry].text, (int)u->lines[op].length,
             u->lines[op].text, (int)u->lines[store].length, u->lines[store].text);
    lp_insert(&u->lines[transfer], text);
    u->lines[save].deleted = u->lines[reload].deleted = u->lines[carry].deleted = 1;
    u->lines[op].deleted = u->lines[store].deleted = 1;
    return 1;
}
