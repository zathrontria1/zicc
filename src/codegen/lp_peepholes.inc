// Specialized line peepholes: MMIO, post-cursors, dividers, reductions, and guard frames

/* A fixed access whose entire operand is mirrored in bank $80 */
static unsigned lp_mmio_mirror(const LpLine *l)
{
    size_t n;
    const char *p = lp_operand(l, &n);
    char *end;
    unsigned long address, last;

    if (n != 9 || strncmp(p, "f:$", 3))
        return 0;
    if (!lp_is(l, "sta") && !lp_is(l, "lda") && !lp_is(l, "adc") && !lp_is(l, "sbc") &&
        !lp_is(l, "and") && !lp_is(l, "ora") && !lp_is(l, "eor") && !lp_is(l, "cmp"))
        return 0;

    address = strtoul(p + 3, &end, 16);

    if (end != p + n || (address >> 16) != 0)
        return 0;

    last = address + !l->m8;

    if ((address >= 0x2100 && last <= 0x21ff) || (address >= 0x4016 && last <= 0x4017) ||
        (address >= 0x4200 && last <= 0x437f))
        return (unsigned)address;

    return 0;
}

static int lp_mmio_return_fallthrough(const LpUnit *u, unsigned i)
{
    const LpLine *l = &u->lines[i];

    return lp_is(l, "jmp") && l->target == (int)(i + 1) &&
           !strncmp(u->lines[i + 1].text, "return_", 7);
}

typedef struct {
    int bytes, cycles;
} LpMmioSavings;

static unsigned lp_mmio_page(const LpLine *l, unsigned address)
{
    if (!l->m8 && (address & 0xff) == 0xff)
        return 0;

    return address & 0xff00;
}

/* Score and emit the same lowering, including loads made dead by STZ.
 * A zero page argument means the original D is left in place. */
static LpMmioSavings lp_mmio_lower(LpUnit *u, LpLine *ret, unsigned page, int bank, int emit)
{
    LpMmioSavings savings = {-(page ? 6 : 0) - (bank ? 5 : 0), -(page ? 19 : 0) - (bank ? 13 : 0)};
    LpLine *zero = NULL;
    int zero_only_stores = 0;

    unsigned i;

    for (i = 0; i < u->count; ++i) {
        LpLine *l = &u->lines[i];

        unsigned address;
        int direct, shorten, stz;

        if (!l->op)
            continue;
        if (lp_mmio_return_fallthrough(u, i)) {
            if (emit)
                l->deleted = 1;

            continue;
        }

        address = lp_mmio_mirror(l);
        direct = address && page && lp_mmio_page(l, address) == page;
        shorten = direct || (address && bank);
        stz = shorten && lp_is(l, "sta") && zero && l->m8 == zero->m8;

        if (shorten) {
            savings.bytes += 1 + direct;
            savings.cycles += 1 + direct;

            if (emit) {
                const char *op = stz ? "stz" : l->op;

                /* Four digits distinguish MMIO offsets from the ABI's
                 * two-digit direct-page workspace operands. */
                if (direct)
                    lp_set(l, "    %.3s z:$%04X", op, address - page);
                else
                    lp_set(l, "    %.3s a:$%04X", op, address);
            }
        }

        if (stz) {
            zero_only_stores = 1;
            continue;
        }

        if (zero && zero_only_stores &&
            ((lp_is(l, "lda") && (zero->m8 || !l->m8)) || (l == ret && !lp_state.value_result))) {
            savings.bytes += zero->m8 ? 2 : 3;
            savings.cycles += zero->m8 ? 2 : 3;

            if (emit)
                zero->deleted = 1;
        }

        /* REP can precede a void return without consuming the zero */
        if (lp_line_is(l, "rep #$20"))
            continue;

        zero = lp_is(l, "lda") && lp_immediate(l) == 0 ? l : NULL;
        zero_only_stores = 0;
    }

    return savings;
}

/* Scope D and/or DBR to a straight-line leaf with only fixed mirrored
 * operands. No branch or PHP can observe the flags changed by PLD/PLB. */
static int lp_mmio_addressing(LpUnit *u, Function *f, size_t at)
{
    LpLine *first = NULL, *ret = NULL;

    unsigned pages[256] = {0}, i, count = 0, best_page = 0;
    int can_dp = 1, bank, best_bank = 0;
    LpMmioSavings best = {0, 0};

    (void)at;

    if (u->calls || u->indirect || statement_inline_markers(f->body))
        return 0;

    for (i = 0; i < u->count; ++i) {
        LpLine *l = &u->lines[i];

        unsigned address;
        size_t n;

        if (!l->op) {
            if (first && l->label && strncmp(l->text, "return_", 7))
                return 0;

            continue;
        }
        if (ret)
            return 0;
        if (!first)
            first = l;

        if (lp_is(l, "rts") || lp_is(l, "rtl"))
            ret = l;
        else if ((address = lp_mmio_mirror(l)) != 0) {
            ++count;
            ++pages[lp_mmio_page(l, address) >> 8];
        } else if (lp_mmio_return_fallthrough(u, i))
            continue;
        else if (lp_line_is(l, "sep #$20") || lp_line_is(l, "rep #$20"))
            continue;
        else if (lp_has_immediate(l) && lp_immediate(l) >= 0)
            continue;
        else {
            /* Reject stack use and memory operands that depend on the
             * original D or DBR. TDC/TCD also preclude changing D. */
            lp_operand(l, &n);

            if (n || l->use == LP_ALL || l->ends || lp_stack_op(l) || lp_is(l, "tsc") ||
                lp_is(l, "tsx"))
                return 0;
            if (lp_is(l, "tdc") || lp_is(l, "tcd"))
                can_dp = 0;
        }
    }

    if (!count || !ret)
        return 0;

    for (i = 0; i < 256; ++i) {
        if (i && (!can_dp || !pages[i]))
            continue;

        for (bank = i == 0; bank <= 1; ++bank) {
            LpMmioSavings trial = lp_mmio_lower(u, ret, i << 8, bank, 0);

            if (trial.bytes > 0 &&
                (trial.cycles > best.cycles ||
                 (trial.cycles == best.cycles && trial.bytes > best.bytes && trial.cycles > 0))) {
                best = trial;
                best_page = i << 8;
                best_bank = bank;
            }
        }
    }

    if (!best.cycles)
        return 0;

    /* The entry ABI supplies DBR=$7E, so one PEA provides both PLBs */
    if (best_bank)
        lp_insert(first, "    pea $7E80\n    plb\n");

    if (best_page) {
        char setup[40];

        snprintf(setup, sizeof setup, "    phd\n    pea $%04X\n    pld\n", best_page);
        lp_insert(first, setup);
        lp_insert(ret, "    pld\n");
    }

    if (best_bank)
        lp_insert(ret, "    plb\n");

    lp_mmio_lower(u, ret, best_page, best_bank, 1);
    return 1;
}

/* In a sentinel scan the cursor's only update is by a fixed word stride.
 * Carry it across the backedge in X. Keep the private memory home current
 * at each iteration and reproduce the loaded word's condition flags. */
static int lp_word_scan_cursor(LpUnit *u, Function *f, size_t at)
{
    (void)at;

    if (u->indirect || lp_state.is_volatile || lp_state.parser->no_register_cursors ||
        body_asm_statements(f->body))
        return 0;

    lp_liveness(u);

    for (unsigned i = 0; i < u->count; ++i) {
        LpLine *load = &u->lines[i];
        size_t n;
        const char *home = lp_operand(load, &n);

        if (!lp_is(load, "ldx") || load->m8 || load->x8 || lp_workspace_word(home, n) < 0)
            continue;

        int seq[5], k = (int)i;

        unsigned count = 0, back;

        for (; count < 5 && (k = lp_next(u, (unsigned)k, 1)) >= 0; ++count) {
            seq[count] = k;
        }

        if (count != 5 || !lp_line_is(&u->lines[seq[0]], "txa") ||
            !lp_line_is(&u->lines[seq[1]], "inc a") || !lp_line_is(&u->lines[seq[2]], "inc a") ||
            !lp_is(&u->lines[seq[3]], "sta") || !lp_operand_is(&u->lines[seq[3]], home, n) ||
            !lp_line_is(&u->lines[seq[4]], "lda a:$0000,x") ||
            (u->lines[seq[4]].out & (LP_X | LP_C)))
            continue;

        int head = lp_loop(u, i, &back);

        if (head < 0 || !u->lines[back].ends || back <= (unsigned)seq[4])
            continue;

        int valid = 1;

        for (unsigned j = 0; j < u->count && valid; ++j) {
            LpLine *l = &u->lines[j];

            if (j >= (unsigned)head && j < i && l->op)
                valid = 0;
            if (j > (unsigned)seq[4] && j <= back && l->op &&
                ((!lp_branch(l) && !lp_is(l, "jmp")) || l->target < 0))
                valid = 0;
            if (l->target >= head && l->target <= (int)back &&
                (j < (unsigned)head || j > back ||
                 (l->target <= (int)seq[4] && (l->target != head || j != back))))
                valid = 0;
        }

        if (!valid)
            continue;

        char setup[80];

        snprintf(setup, sizeof setup, "    ldx %.*s\n", (int)n, home);
        lp_insert(&u->lines[head], setup);
        lp_set(load, "    lda a:$0000,x");
        lp_set(&u->lines[seq[0]], "    inx");
        lp_set(&u->lines[seq[1]], "    inx");
        lp_set(&u->lines[seq[2]], "    stx %.*s", (int)n, home);
        lp_set(&u->lines[seq[3]], "    cmp #0");
        u->lines[seq[4]].deleted = 1;
        return 1;
    }

    return 0;
}

/* A private promoted pointer can stay in an index register across a
 * single-entry loop when its only uses are marked post-update transfers.
 * Keep both homes coherent at the exit and save the incoming Y on the stack. */
typedef struct {
    unsigned load, access, step1, step2, store, slot;
} LpCursorTransfer;

static int lp_cursor_transfer(LpUnit *u, unsigned i, LpCursorTransfer *t)
{
    const char *home;
    size_t n;
    int a, b, c, d;
    int word;

    if (!i || !lp_is(&u->lines[i], "ldx") ||
        strncmp(u->lines[i - 1].text, post_cursor_marker, sizeof post_cursor_marker - 1))
        return 0;

    home = lp_operand(&u->lines[i], &n);
    word = lp_workspace_word(home, n);

    if (word < 0 || word > 30 || (word & 1))
        return 0;

    a = lp_next(u, i, 1);
    b = a < 0 ? -1 : lp_next(u, (unsigned)a, 1);
    c = b < 0 ? -1 : lp_next(u, (unsigned)b, 1);
    d = c < 0 ? -1 : lp_next(u, (unsigned)c, 1);

    if (d < 0 || !lp_operand_is(&u->lines[a], "a:$0000,x", 9) ||
        !(lp_is(&u->lines[a], "lda") || lp_is(&u->lines[a], "sta") || lp_is(&u->lines[a], "adc") ||
          lp_is(&u->lines[a], "sbc") || lp_is(&u->lines[a], "and") || lp_is(&u->lines[a], "ora") ||
          lp_is(&u->lines[a], "eor")) ||
        !((lp_is(&u->lines[b], "inx") && lp_is(&u->lines[c], "inx")) ||
          (lp_is(&u->lines[b], "dex") && lp_is(&u->lines[c], "dex"))) ||
        !lp_is(&u->lines[d], "stx") || !lp_operand_is(&u->lines[d], home, n))
        return 0;

    for (unsigned j = i; j <= (unsigned)d; ++j) {
        if (u->lines[j].m8 || u->lines[j].x8)
            return 0;
    }

    *t = (LpCursorTransfer){i,           (unsigned)a, (unsigned)b,
                            (unsigned)c, (unsigned)d, (unsigned)word / 2};
    return 1;
}

/* Account for the extra PHY only for slots outside the loop's own
 * pushes. A reference spanning both regions cannot be moved safely. */
static int lp_cursor_stack(const LpLine *l, int *depth, int *adjust)
{
    size_t n;
    const char *o = lp_operand(l, &n);

    if (n >= 2 && o[n - 2] == ',' && o[n - 1] == 's') {
        char *end;
        long offset = strtol(o, &end, 10);

        if (end != o + n - 2 || offset < 1 || offset > 255)
            return 0;

        if (offset > *depth) {
            if (offset > 253)
                return 0;

            *adjust = (int)offset + 2;
        } else if (offset + lp_width(l) - 1 > *depth)
            return 0;
    }

    if (lp_line_is(l, "pha"))
        *depth += l->m8 ? 1 : 2;
    else if (lp_line_is(l, "pla"))
        *depth -= l->m8 ? 1 : 2;
    else if (lp_stack_op(l))
        return 0;

    return *depth >= 0;
}

static int lp_keep_post_cursors(LpUnit *u, Function *f, size_t at)
{
    unsigned latch;
    (void)f;
    (void)at;

    if (u->indirect || lp_state.is_volatile || lp_state.parser->no_register_cursors ||
        lp_state.parser->no_dp_homes)
        return 0;

    for (latch = 0; latch < u->count; ++latch) {
        if (lp_line_is(&u->lines[latch], "sep #$20") || lp_line_is(&u->lines[latch], "rep #$20"))
            u->lines[latch].use = 0;
    }

    lp_liveness(u);

    for (latch = 0; latch < u->count; ++latch) {
        LpLine *edge = &u->lines[latch];
        LpCursorTransfer transfers[16];

        unsigned start, exit, i, count = 0, slots[2], slot_count = 0;
        int valid = 1, depth = 0, depths[256], stack_adjust[256] = {0};
        char setup[160], restore[120];

        if (edge->target < 0 || (unsigned)edge->target >= latch || edge->call)
            continue;

        start = (unsigned)edge->target;

        if (!lp_fallthrough_label(&u->lines[start]) || u->lines[start].m8 || u->lines[start].x8 ||
            (u->lines[start].live & (LP_X | LP_N | LP_Z)))
            continue;

        exit = latch + 1;

        while (exit < u->count && !u->lines[exit].op) {
            ++exit;
        }

        if (exit - start >= 256 || exit == u->count || u->lines[exit].m8 || u->lines[exit].x8 ||
            (u->lines[exit].live & (LP_X | LP_N | LP_Z)))
            continue;

        /* External jumps must bypass both the body and the register restore */
        for (i = 0; i < u->count; ++i) {
            LpLine *l = &u->lines[i];

            if ((i < start || i > latch) && l->target >= (int)start && l->target <= (int)exit)
                valid = 0;
        }

        for (i = start; valid && i <= latch; ++i) {
            LpLine *l = &u->lines[i];
            LpCursorTransfer t;

            unsigned j;
            depths[i - start] = depth;

            if (!l->op)
                continue;

            if (lp_cursor_transfer(u, i, &t) && t.store <= latch && count < 16) {
                for (j = 0; j < slot_count && slots[j] != t.slot; ++j) {
                }

                if (j == slot_count) {
                    if (slot_count == 2) {
                        valid = 0;
                        break;
                    }

                    slots[slot_count++] = t.slot;
                }

                transfers[count++] = t;

                for (j = i + 1; j <= t.store; ++j) {
                    depths[j - start] = depth;
                }

                i = t.store;
                continue;
            }

            if (l->call || l->x8 || l->use == LP_ALL || ((l->use | l->def) & (LP_X | LP_Y)) ||
                (l->target >= 0 && (l->target < (int)start || l->target > (int)exit)) ||
                (l->ends && l->target < 0) || lp_is(l, "tcd") || lp_is(l, "pld") ||
                lp_is(l, "plb") || lp_is(l, "mvn") || lp_is(l, "mvp") || lp_is(l, "tsc"))
                valid = 0;
            if (!lp_cursor_stack(l, &depth, &stack_adjust[i - start]))
                valid = 0;
        }

        if (!valid || depth || slot_count != 2)
            continue;

        for (i = latch + 1; i <= exit; ++i) {
            depths[i - start] = 0;
        }

        for (i = start; valid && i <= latch; ++i) {
            int target = u->lines[i].target;

            if (target >= 0 && depths[target - (int)start] != depths[i - start])
                valid = 0;
        }

        for (i = start; valid && i <= latch; ++i) {
            size_t n;
            const char *o = lp_operand(&u->lines[i], &n);

            unsigned j;

            for (j = 0; j < count; ++j) {
                if (i == transfers[j].load) {
                    i = transfers[j].store;
                    break;
                }
            }

            if (j < count)
                continue;

            {
                int word = lp_workspace_word(o, n);

                if (word >= 0) {
                    if (lp_overlaps_n(&u->lines[i], word, 2 * (int)slots[0], 2) ||
                        lp_overlaps_n(&u->lines[i], word, 2 * (int)slots[1], 2))
                        valid = 0;
                } else if (lp_text_words(o, o + n) & ((1u << slots[0]) | (1u << slots[1])))
                    valid = 0;
            }
        }

        if (!valid)
            continue;

        snprintf(setup, sizeof setup,
                 "; retain private word cursors in X and Y\n"
                 "    phy\n    ldx z:__arith_lhs+%u\n    ldy z:__arith_lhs+%u\n",
                 slots[0] * 2, slots[1] * 2);
        snprintf(restore, sizeof restore,
                 "    stx z:__arith_lhs+%u\n    sty z:__arith_lhs+%u\n    ply\n", slots[0] * 2,
                 slots[1] * 2);
        lp_insert(&u->lines[start], setup);
        lp_insert(&u->lines[exit], restore);

        for (i = start; i <= latch; ++i) {
            if (stack_adjust[i - start])
                lp_set(&u->lines[i], "    %.3s %d,s", u->lines[i].op, stack_adjust[i - start]);
        }

        for (i = 0; i < count; ++i) {
            LpCursorTransfer *t = &transfers[i];

            u->lines[t->load].deleted = 1;
            u->lines[t->store].deleted = 1;

            if (t->slot == slots[1]) {
                const char *step = lp_is(&u->lines[t->step1], "inx") ? "iny" : "dey";

                lp_set(&u->lines[t->access], "    %.3s a:$0000,y", u->lines[t->access].op);
                lp_set(&u->lines[t->step1], "    %s", step);
                lp_set(&u->lines[t->step2], "    %s", step);
            }
        }

        return 1;
    }

    return 0;
}

enum { DIVIDER_WAIT_SLOTS = 5 };

/* Match the compiler's hardware start, width restore and complete wait.
 * The first full-word result read may be either quotient or remainder. */
static int lp_divider_wait(const LpUnit *u, unsigned trigger, int *first)
{
    int rep, read;

    if (!lp_line_is(&u->lines[trigger], "sta f:$004206") || !u->lines[trigger].m8)
        return -1;

    rep = lp_next(u, trigger, 1);

    if (rep < 0 || !lp_line_is(&u->lines[rep], "rep #$20") ||
        (unsigned)(rep + 2 + DIVIDER_WAIT_SLOTS) >= u->count ||
        strncmp(u->lines[rep + 1].text, ".a16\n", 5))
        return -1;

    *first = rep + 2;
    for (read = *first; read < *first + DIVIDER_WAIT_SLOTS; ++read) {
        const LpLine *wait = &u->lines[read];

        if (!lp_line_is(wait, "nop") && !lp_line_is(wait, "inx") && !lp_line_is(wait, "dex") &&
            !lp_line_is(wait, "iny") && !lp_line_is(wait, "dey"))
            return -1;
    }

    if (u->lines[read].m8 || (!lp_line_is(&u->lines[read], "lda f:$004214") &&
                              !lp_line_is(&u->lines[read], "lda f:$004216")))
        return -1;

    return read;
}

/* Index steps take the same two cycles as NOP and do not change A or
 * carry. Move them across divider setup only inside a straight-line
 * region that never observes the index or the steps' N/Z results. */
static int lp_divider_index_wait(LpUnit *u, Function *f, size_t at)
{
    unsigned trigger;
    (void)f;
    (void)at;

    if (lp_state.is_volatile || u->indirect || lp_state.parser->no_strength_reduction)
        return 0;

    for (trigger = 0; trigger < u->count; ++trigger) {
        unsigned blocked = 0, moved = 0;
        int i, dividend = 0, first, next = lp_divider_wait(u, trigger, &first);

        if (next < 0 || !lp_line_is(&u->lines[next], "lda f:$004216"))
            continue;

        for (i = first; i < next && lp_line_is(&u->lines[i], "nop"); ++i) {
        }

        if (i != next)
            continue;

        for (i = (int)trigger - 1; i >= 0 && (int)trigger - i <= 24; --i) {
            LpLine *l = &u->lines[i];

            unsigned index;

            if (!l->op) {
                if (l->text[0] == ';' || !strncmp(l->text, ".a8\n", 4) ||
                    !strncmp(l->text, ".a16\n", 5))
                    continue;

                break;
            }
            if (lp_line_is(l, "sep #$20") || lp_line_is(l, "rep #$20"))
                continue;
            if (l->x8 || l->call || l->target >= 0 || l->ends || l->use == LP_ALL ||
                l->use & (LP_N | LP_Z))
                break;

            if (lp_line_is(l, "sta f:$004204") && !l->m8 && !dividend)
                dividend = 1;
            else if (lp_mmio_mirror(l))
                break;

            index = lp_is(l, "inx") || lp_is(l, "dex")   ? LP_X
                    : lp_is(l, "iny") || lp_is(l, "dey") ? LP_Y
                                                         : 0;

            if (dividend && index && !(blocked & index) && !l->m8) {
                lp_set(&u->lines[next - 1 - (int)moved], "    %.3s", l->op);
                l->deleted = 1;

                if (++moved == DIVIDER_WAIT_SLOTS)
                    break;

                continue;
            }

            blocked |= l->use | l->def;
        }

        if (moved)
            return 1;
    }

    return 0;
}

/* Forward an interleaved pair of saved word results. Copy the first
 * result to its final private home while it is still in A, then keep
 * the second result in A instead of reloading both temporary homes. */
static int lp_forward_interleaved_words(LpUnit *u, Function *f, size_t at)
{
    unsigned i;
    (void)f;
    (void)at;

    if (lp_state.is_volatile || lp_state.parser->no_value_reuse)
        return 0;

    for (i = 0; i < u->count; ++i) {
        LpLine *sequence[6];
        static const char *const ops[] = {"sta", "lda", "sta", "lda", "sta", "lda"};
        const char *operand[6];
        size_t length[6];

        unsigned j;
        int k = (int)i, first, second, destination, input;

        for (j = 0; j < 6 && k >= 0; ++j) {
            LpLine *l = &u->lines[k];

            if (l->m8 || !lp_is(l, ops[j]))
                break;

            sequence[j] = l;
            operand[j] = lp_operand(l, &length[j]);

            if (j < 5)
                k = lp_next(u, (unsigned)k, 1);
        }

        if (j != 6)
            continue;

        first = lp_workspace_word(operand[0], length[0]);
        second = lp_workspace_word(operand[2], length[2]);
        destination = lp_workspace_word(operand[4], length[4]);
        input = lp_workspace_word(operand[1], length[1]);

        if (first < 0 || second < 0 || destination < 0 || abs(first - second) < 2 ||
            abs(first - destination) < 2 || abs(second - destination) < 2 ||
            !lp_operand_is(sequence[3], operand[0], length[0]) ||
            !lp_operand_is(sequence[5], operand[2], length[2]))
            continue;

        if (input >= 0) {
            if (abs(input - destination) < 2)
                continue;
        } else if (lp_immediate(sequence[1]) < 0) {
            int producer = lp_next(u, i, -1);

            /* Only a latched divider quotient can be delayed here. The
             * preceding remainder read comes from the same operation. */
            if (producer < 0 || !lp_line_is(&u->lines[producer], "lda f:$004216") ||
                !lp_line_is(sequence[1], "lda f:$004214"))
                continue;
        }

        lp_set(sequence[0], "    sta %.*s\n    sta %.*s", (int)length[0], operand[0],
               (int)length[4], operand[4]);
        sequence[3]->deleted = sequence[4]->deleted = sequence[5]->deleted = 1;
        return 1;
    }

    return 0;
}

/* Both divider results are ready. Save the quotient before reading the
 * remainder when the next use reloads the remainder or the quotient
 * goes directly through a private cursor. The result homes are disjoint. */
static int lp_divider_remainder_last(LpUnit *u, Function *f, size_t at)
{
    unsigned trigger;
    (void)f;
    (void)at;

    if (lp_state.is_volatile || u->indirect || lp_state.parser->no_value_reuse)
        return 0;

    lp_liveness(u);

    for (trigger = 0; trigger < u->count; ++trigger) {
        int first, ready = lp_divider_wait(u, trigger, &first), q, store, tail, step;

        unsigned i, rem_words = 0, quot_words = 0;
        size_t n;
        const char *o;

        if (ready < 0 || !lp_line_is(&u->lines[ready], "lda f:$004216"))
            continue;

        i = (unsigned)ready;
        q = lp_next(u, i, 1);

        while (q >= 0 && lp_is(&u->lines[q], "sta") && !u->lines[q].m8) {
            int home;

            o = lp_operand(&u->lines[q], &n);
            home = lp_workspace_word(o, n);

            if (home < 0 || (home & 1))
                break;

            rem_words |= 1u << (home / 2);
            q = lp_next(u, (unsigned)q, 1);
        }

        if (!rem_words || q < 0 || !lp_line_is(&u->lines[q], "lda f:$004214") || u->lines[q].m8)
            continue;

        store = lp_next(u, (unsigned)q, 1);

        while (store >= 0 && lp_is(&u->lines[store], "sta") && !u->lines[store].m8) {
            int home;

            o = lp_operand(&u->lines[store], &n);
            home = lp_workspace_word(o, n);

            if (home < 0 || (home & 1))
                break;

            quot_words |= 1u << (home / 2);
            store = lp_next(u, (unsigned)store, 1);
        }

        if (store < 1 || (rem_words & quot_words) || u->lines[store].m8 || u->lines[store].x8)
            continue;

        if (lp_is(&u->lines[store], "lda")) {
            int home;

            o = lp_operand(&u->lines[store], &n);
            home = lp_workspace_word(o, n);

            if (home < 0 || (home & 1) || !(rem_words & (1u << (home / 2))))
                continue;

            /* The reload already selects the remainder and its flags.
             * Read it from the divider here, after saving the quotient. */
            lp_set(&u->lines[store], "%.*s", (int)(u->lines[q].text - u->lines[i].text - 1),
                   u->lines[i].text);
        } else {
            if (strncmp(u->lines[store - 1].text, post_cursor_marker,
                        sizeof post_cursor_marker - 1) ||
                !lp_line_is(&u->lines[store], "sta a:$0000,y"))
                continue;

            step = lp_next(u, (unsigned)store, 1);
            tail = step < 0 ? -1 : lp_next(u, (unsigned)step, 1);

            if (tail < 0 ||
                !((lp_line_is(&u->lines[step], "iny") && lp_line_is(&u->lines[tail], "iny")) ||
                  (lp_line_is(&u->lines[step], "dey") && lp_line_is(&u->lines[tail], "dey"))) ||
                (u->lines[tail].out & (LP_A | LP_N | LP_Z)))
                continue;

            lp_set(&u->lines[tail], "    %.3s\n%.*s", u->lines[tail].op,
                   (int)(u->lines[q].text - u->lines[i].text - 1), u->lines[i].text);
        }

        for (; i < (unsigned)q; ++i) {
            u->lines[i].deleted = 1;
        }

        return 1;
    }

    return 0;
}

/* Seed a word load once when a loop latch already carries the same
 * private home in A. Reject alternate backedges to the load. */
static int lp_keep_loop_word_in_a(LpUnit *u, Function *f, size_t at)
{
    unsigned latch;
    (void)f;
    (void)at;

    if (u->indirect || lp_state.is_volatile || lp_state.parser->no_value_reuse)
        return 0;

    lp_liveness(u);

    for (latch = 0; latch < u->count; ++latch) {
        int head = u->lines[latch].target, load, producer;
        size_t n;
        const char *home;

        unsigned j;

        if (head < 0 || (unsigned)head >= latch || !lp_fallthrough_label(&u->lines[head]))
            continue;

        for (load = head + 1; (unsigned)load < latch && !u->lines[load].op; ++load) {
            if (u->lines[load].label || u->lines[load].text[0] != ';')
                break;
        }

        if ((unsigned)load >= latch || !lp_is(&u->lines[load], "lda") || u->lines[load].m8)
            continue;

        home = lp_operand(&u->lines[load], &n);

        for (j = 0; j < u->count; ++j) {
            if (j != latch && u->lines[j].target >= head && u->lines[j].target <= load)
                break;
        }

        if (j != u->count)
            continue;

        int update = lp_next(u, latch, -1);

        if (update > load && !u->lines[update].m8 && lp_is(&u->lines[update], "sta") &&
            lp_private(home, n) && lp_operand_is(&u->lines[update], home, n) &&
            lp_flags_from_a(u, lp_next(u, (unsigned)update, -1))) {
            /* A and N/Z already hold the stored word on this backedge */
            char text[80];

            snprintf(text, sizeof text, "    lda %.*s\n", (int)n, home);
            lp_insert(&u->lines[head], text);
            u->lines[load].deleted = 1;
            return 1;
        }

        if (update > load && !u->lines[update].m8 && !(u->lines[load].out & LP_A) &&
            (lp_is(&u->lines[update], "inc") || lp_is(&u->lines[update], "dec")) &&
            pr_named(home, n)) {
            size_t m;
            const char *updated = lp_operand(&u->lines[update], &m);

            if (lp_named_word_alias(home, n, updated, m)) {
                /* Execute the load on entry. INC/DEC supply the same N/Z
                 * on the unique backedge and the loaded word is dead. */
                char *text = allocate(n + 16);

                snprintf(text, n + 16, "    lda %.*s\n", (int)n, home);
                lp_insert(&u->lines[head], text);
                free(text);
                u->lines[load].deleted = 1;
                return 1;
            }
        }

        if ((u->lines[load].out & (LP_N | LP_Z)) || lp_workspace_word(home, n) < 0)
            continue;

        /* Only cross consecutive labels with no incoming jumps. The
         * ordinary fallthrough enters these after the final A definition. */
        for (producer = (int)latch - 1; producer > load; --producer) {
            LpLine *l = &u->lines[producer];

            if (l->label) {
                if (!lp_inner_label(u, (unsigned)producer, (unsigned)producer, (unsigned)producer))
                    break;

                continue;
            }
            if (!l->op) {
                if (l->text[0] != ';')
                    break;

                continue;
            }
            if (!l->m8 && lp_is(l, "sta") && lp_operand_is(l, home, n))
                break;
            if (l->m8 || l->call || l->ends || (l->target >= 0 && (unsigned)l->target <= latch) ||
                (l->def & LP_A) || l->use == LP_ALL || lp_may_write(l, home, n, 2))
                break;
            if (!lp_branch(l) && !lp_is(l, "cmp") && !lp_is(l, "cpx") && !lp_is(l, "cpy") &&
                !lp_is(l, "dec") && !lp_is(l, "inc") && !lp_is(l, "inx") && !lp_is(l, "dex") &&
                !lp_is(l, "iny") && !lp_is(l, "dey") && !lp_is(l, "nop"))
                break;
        }

        if (producer <= load || !lp_is(&u->lines[producer], "sta") || u->lines[producer].m8 ||
            !lp_operand_is(&u->lines[producer], home, n))
            continue;

        {
            char text[80];

            snprintf(text, sizeof text, "; carry private word in A across loop\n    lda %.*s\n",
                     (int)n, home);
            lp_insert(&u->lines[head], text);
            u->lines[load].deleted = 1;
        }
        return 1;
    }

    return 0;
}

/* A cleared byte takes the zero exit when its nonvolatile loop test is
 * reached immediately. Keep the clear, and preserve status on both edges. */
static int lp_cleared_byte_loop(LpUnit *u, Function *f, size_t at)
{
    (void)f;
    (void)at;

    if (lp_state.is_volatile || u->indirect)
        return 0;

    int known, changed = 0;
    unsigned char *targets = lp_local_targets(u, &known);

    lp_liveness(u);

    for (unsigned i = 0; i < u->count && !changed; ++i) {
        LpLine *clear = &u->lines[i];
        size_t n, m;
        const char *slot = lp_operand(clear, &n);

        if (!lp_is(clear, "stz") || !clear->m8 || !pr_named(slot, n))
            continue;

        int restore = lp_next(u, i, 1);

        if (restore < 0 || !lp_line_is(&u->lines[restore], "rep #$20") ||
            (unsigned)restore + 1 >= u->count || u->lines[restore + 1].length != 4 ||
            strncmp(u->lines[restore + 1].text, ".a16", 4))
            continue;

        int latch = lp_next_fallthrough(u, (unsigned)restore + 1, 1, targets, known);

        if (latch < 0 || !lp_is(&u->lines[latch], "jmp"))
            continue;

        int head = u->lines[latch].target;

        if (head < 0 || (unsigned)head >= i)
            continue;

        int mode = lp_next(u, (unsigned)head, 1);
        int load = mode < 0 ? -1 : lp_next_mode(u, (unsigned)mode);
        int wide = load < 0 ? -1 : lp_next(u, (unsigned)load, 1);
        int branch = wide < 0 ? -1 : lp_next_mode(u, (unsigned)wide);

        if (branch < 0 || !lp_line_is(&u->lines[mode], "sep #$20") ||
            !lp_is(&u->lines[load], "lda") || !u->lines[load].m8 ||
            !lp_operand_is(&u->lines[load], slot, n) || !lp_line_is(&u->lines[wide], "rep #$20") ||
            !lp_line_is(&u->lines[branch], "bne :+"))
            continue;

        int after = -1, target = lp_cond_branch_target(u, branch, &after);

        if (target < 0 || after != branch + 2 || (u->lines[target].live & (LP_AL | LP_N | LP_Z)))
            continue;

        const char *dest = lp_operand(&u->lines[branch + 1], &m);

        lp_set(&u->lines[latch], "    jmp %.*s", (int)m, dest);
        changed = 1;
    }

    free(targets);
    return changed;
}

static int lp_reduction_home_ok(const char *home, size_t hn)
{
    if (lp_workspace_word(home, hn) >= 0)
        return 1;

    return lp_private(home, hn) && !lp_state.frame_address && !lp_is_mmio_operand(home, hn);
}

static int lp_reduction_step(const LpUnit *u, unsigned i, const char **home_out, size_t *hn_out,
                             const char **src_out, size_t *sn_out, int *op_idx_out,
                             int *store_idx_out, const char *fixed_home, size_t fixed_hn,
                             const char *fixed_op)
{
    const LpLine *load = &u->lines[i], *op, *store;
    int next, op_idx, st_idx;
    size_t hn, sn;
    const char *home, *src;

    if (load->deleted || load->replace || load->m8 || load->x8 || !lp_is(load, "lda"))
        return 0;

    src = lp_operand(load, &sn);

    if (!sn)
        return 0;

    next = lp_next(u, i, 1);

    if (next < 0)
        return 0;

    if (lp_line_is(&u->lines[next], "clc")) {
        op_idx = lp_next(u, (unsigned)next, 1);

        if (op_idx < 0)
            return 0;

        op = &u->lines[op_idx];

        if (!lp_is(op, "adc"))
            return 0;
    } else {
        op_idx = next;
        op = &u->lines[op_idx];

        if (!lp_is(op, "and") && !lp_is(op, "ora") && !lp_is(op, "eor"))
            return 0;
    }

    if (op->deleted || op->replace || op->m8 || op->x8)
        return 0;
    if (fixed_op && !lp_is(op, fixed_op))
        return 0;

    home = lp_operand(op, &hn);

    if (!lp_reduction_home_ok(home, hn))
        return 0;
    if (fixed_home && (hn != fixed_hn || strncmp(home, fixed_home, hn)))
        return 0;

    st_idx = lp_next(u, (unsigned)op_idx, 1);

    if (st_idx < 0)
        return 0;

    store = &u->lines[st_idx];

    if (store->deleted || store->replace || store->m8 || store->x8 || !lp_is(store, "sta") ||
        !lp_operand_is(store, home, hn))
        return 0;
    if (lp_operand_is(load, home, hn) || lp_may_write(store, src, sn, 2))
        return 0;

    *home_out = home;
    *hn_out = hn;
    *src_out = src;
    *sn_out = sn;
    *op_idx_out = op_idx;
    *store_idx_out = st_idx;
    return 1;
}

/* Fuse straight-line sequences of two or more commutative DP/private word
 * reductions ("lda <src>; [clc]; <op> home; sta home") so A keeps the
 * running accumulator across the entire chain. */
static int lp_chain_reduction_in_a(LpUnit *u, Function *f, size_t at)
{
    unsigned i;
    (void)f;
    (void)at;

    if (u->indirect || lp_state.is_volatile || lp_state.parser->no_value_reuse)
        return 0;

    lp_liveness(u);

    for (i = 0; i < u->count; ++i) {
        const char *home = NULL, *srcs[32], *op_name;
        size_t hn = 0, sns[32];
        int loads[32], ops[32], stores[32], count = 0, next;
        char op_buf[4];

        if (!lp_reduction_step(u, i, &home, &hn, &srcs[0], &sns[0], &ops[0], &stores[0], NULL, 0,
                               NULL))
            continue;

        loads[0] = (int)i;
        snprintf(op_buf, sizeof op_buf, "%.3s", u->lines[ops[0]].op);
        op_name = op_buf;
        count = 1;

        while (count < 32 && (next = lp_next(u, (unsigned)stores[count - 1], 1)) >= 0) {
            const char *h2 = NULL;
            size_t hn2 = 0;

            if (!lp_reduction_step(u, (unsigned)next, &h2, &hn2, &srcs[count], &sns[count],
                                   &ops[count], &stores[count], home, hn, op_name))
                break;

            loads[count] = next;
            ++count;
        }

        if (count < 2 || (u->lines[stores[count - 1]].out & LP_V))
            continue;

        lp_set(&u->lines[loads[0]], "    lda %.*s", (int)hn, home);

        for (int k = 0; k < count; ++k) {
            if (k > 0)
                u->lines[loads[k]].deleted = 1;

            lp_set(&u->lines[ops[k]], "    %s %.*s", op_name, (int)sns[k], srcs[k]);

            if (k + 1 < count)
                u->lines[stores[k]].deleted = 1;
        }

        return 1;
    }

    return 0;
}

/* Hoist the load and sink the store of a commutative DP/private word reduction
 * out of a single-block loop when the loop body and backedge preserve A. */
static int lp_keep_reduction_in_a(LpUnit *u, Function *f, size_t at)
{
    unsigned latch;
    int known_targets;
    unsigned char *targets;

    (void)f;
    (void)at;

    if (u->indirect || lp_state.is_volatile || lp_state.parser->no_value_reuse)
        return 0;

    targets = lp_local_targets(u, &known_targets);
    lp_liveness(u);

    for (latch = 0; latch < u->count; ++latch) {
        int head = u->lines[latch].target;

        unsigned j;
        int first_op = -1, red_load = -1, red_store = -1, is_chain = 0;
        const char *home = NULL, *src = NULL;
        size_t hn = 0, sn = 0;
        int op_idx = -1;

        if (head < 0 || (unsigned)head >= latch || !known_targets || latch + 1 >= u->count)
            continue;
        if (!lp_branch(&u->lines[latch]) || u->lines[latch].ends || (u->lines[latch].use & LP_A))
            continue;
        if (!lp_fallthrough_label(&u->lines[head]))
            continue;

        for (j = 0; j < u->count; ++j) {
            if (j != latch && u->lines[j].target >= head && u->lines[j].target <= (int)latch)
                break;
        }

        if (j != u->count)
            continue;

        for (j = (unsigned)head + 1; j < latch; ++j) {
            const LpLine *l = &u->lines[j];

            if (l->deleted || l->replace)
                break;
            if (!l->op) {
                if (l->label || l->text[0] != ';')
                    break;

                continue;
            }
            if (l->m8 || l->x8 || l->ends || lp_branch(l) || l->call || lp_stack_op(l) ||
                l->use == LP_ALL)
                break;
            if (first_op < 0)
                first_op = (int)j;
        }

        if (j != latch || first_op < 0 || (u->lines[first_op].use & (LP_A | LP_N | LP_Z | LP_C)))
            continue;

        for (j = (unsigned)first_op; j < latch; ++j) {
            const LpLine *l = &u->lines[j];

            if (!l->op || l->deleted)
                continue;
            if (red_load < 0 && lp_reduction_step(u, j, &home, &hn, &src, &sn, &op_idx, &red_store,
                                                  NULL, 0, NULL)) {
                red_load = (int)j;
                j = (unsigned)red_store;
                continue;
            }

            if (red_load < 0 && lp_is(l, "lda") && lp_reduction_home_ok(lp_operand(l, &hn), hn)) {
                int cur = (int)j, last_st = -1, ok = 1, steps = 0;

                home = lp_operand(l, &hn);

                while (ok) {
                    int nxt = lp_next(u, (unsigned)cur, 1);

                    if (nxt < 0 || (unsigned)nxt >= latch) {
                        ok = 0;
                        break;
                    }
                    if (lp_is(&u->lines[nxt], "sta") && lp_operand_is(&u->lines[nxt], home, hn)) {
                        last_st = nxt;
                        break;
                    }

                    if (lp_line_is(&u->lines[nxt], "clc")) {
                        int nxt2 = lp_next(u, (unsigned)nxt, 1);

                        if (nxt2 < 0 || (unsigned)nxt2 >= latch || !lp_is(&u->lines[nxt2], "adc")) {
                            ok = 0;
                            break;
                        }

                        nxt = nxt2;
                    } else if (!lp_is(&u->lines[nxt], "and") && !lp_is(&u->lines[nxt], "ora") &&
                               !lp_is(&u->lines[nxt], "eor")) {
                        ok = 0;
                        break;
                    }

                    if (lp_operand_is(&u->lines[nxt], home, hn) ||
                        lp_may_write(&u->lines[nxt], home, hn, 2)) {
                        ok = 0;
                        break;
                    }

                    cur = nxt;
                    ++steps;
                }

                if (ok && steps > 0 && last_st >= 0) {
                    int alias = 0;

                    for (int c = j + 1; c < last_st; ++c) {
                        size_t cn;
                        const char *co = lp_operand(&u->lines[c], &cn);

                        if (u->lines[c].op && cn && lp_may_write(&u->lines[last_st], co, cn, 2)) {
                            alias = 1;
                            break;
                        }
                    }

                    if (!alias) {
                        red_load = (int)j;
                        red_store = last_st;
                        is_chain = 1;
                        j = (unsigned)last_st;
                        continue;
                    }
                }

                home = NULL;
                hn = 0;
            }

            if ((l->use & LP_A) || (l->def & LP_A))
                break;
            if ((l->use & LP_C) && j + 1 < latch)
                break;
        }

        if (j != latch || red_load < 0 || red_store < 0 || (u->lines[red_store].out & LP_V))
            continue;

        for (j = (unsigned)first_op; j <= latch; ++j) {
            const LpLine *l = &u->lines[j];
            size_t ln;
            const char *lo;

            if (!l->op || l->deleted || ((int)j >= red_load && (int)j <= red_store))
                continue;

            lo = lp_operand(l, &ln);

            if (lp_may_write(l, home, hn, 2) || lp_operand_is(l, home, hn) ||
                (ln && lp_may_write(&u->lines[red_store], lo, ln, 2)))
                break;
        }

        if (j <= latch)
            continue;

        {
            char enter_text[160], exit_text[160];

            snprintf(enter_text, sizeof enter_text, "    lda %.*s\n", (int)hn, home);
            snprintf(exit_text, sizeof exit_text, "    sta %.*s\n", (int)hn, home);
            lp_insert(&u->lines[head], enter_text);
            lp_insert(&u->lines[latch + 1], exit_text);
            u->lines[red_load].deleted = 1;
            u->lines[red_store].deleted = 1;

            if (!is_chain)
                lp_set(&u->lines[op_idx], "    %.3s %.*s", u->lines[op_idx].op, (int)sn, src);
        }
        free(targets);
        return 1;
    }

    free(targets);
    return 0;
}

typedef struct {
    uint32_t read, write, live, out, update;
} LpWorkspaceLive;

static uint32_t lp_workspace_access(const LpLine *l, int *exact)
{
    size_t n;
    const char *o = lp_operand(l, &n);
    int offset = lp_workspace_word(o, n);
    uint32_t mask = 0;

    *exact = 0;
    if (offset < 0 && n > 3 && o[1] == ':' && o[2] == '$' &&
        (o[0] == 'z' || o[0] == 'a' || o[0] == 'f')) {
        char *end;
        unsigned long address = strtoul(o + 3, &end, 16);
        unsigned long bank = address >> 16, low = address & 65535;
        int start = (int)low - DP_SCRATCH_BASE, width = lp_width(l);

        if (start < 32 && start + width > 0 && (bank == 0x7E || (bank & 0x7F) < 0x40)) {
            if (end == o + n) {
                *exact = 1;
                if (start < 0)
                    return (1u << (start + width)) - 1u;

                offset = start;
            } else if (o[0] == 'z' && lp_index_use(l))
                return UINT32_MAX;
        }
    }

    if (offset >= 0) {
        *exact = 1;
        return ((1u << lp_width(l)) - 1u) << offset;
    }

    {
        int w = n > 4 && o[0] == '(' && !strncmp(o + n - 3, "),y", 3)
                    ? lp_workspace_offset(o + 1, n - 4)
                    : -1;
        unsigned words = lp_text_words(o, o + n);

        if (w >= 0 && !(w & 1))
            return 3u << w;
        if (words && lp_index_use(l))
            return UINT32_MAX;

        for (unsigned i = 0; i < 16; ++i) {
            if (words & (1u << i))
                mask |= 3u << (2 * i);
        }
    }
    return mask;
}

// True when a call target is a 32-bit shift helper reading only __arith_lhs+0..3 and __arith_rhs+0..1
static int lp_shift32_helper_call(const LpLine *l)
{
    size_t n;
    const char *o;

    if (!l->op || (!lp_is(l, "jsr") && !lp_is(l, "jmp")))
        return 0;

    o = lp_operand(l, &n);

    return (n == 17 && !strncmp(o, ".loword(__ushr32)", 17)) ||
           (n == 16 && !strncmp(o, ".loword(__shl32)", 16)) ||
           (n == 17 && !strncmp(o, ".loword(__sshr32)", 17));
}

/* The arithmetic workspace is caller-clobbered. Unknown calls and
 * instructions may read every byte. During DSE a flag-dead update only
 * needs its input if a successor observes the written value. */
static void lp_workspace_liveness(LpUnit *u, LpWorkspaceLive *memory, int dead_updates)
{
    unsigned i;
    int changed;

    for (i = 0; i < u->count; ++i) {
        LpLine *l = &u->lines[i];
        int exact;
        uint32_t access;

        if (!l->op || lp_line_is(l, "sep #$20") || lp_line_is(l, "rep #$20"))
            continue;
        if (lp_shift32_helper_call(l)) {
            memory[i].read = 0x3Fu;
            continue;
        }
        if (l->call && lp_callee(l))
            continue;
        if (l->call || l->use == LP_ALL) {
            memory[i].read = UINT32_MAX;
            continue;
        }

        access = lp_workspace_access(l, &exact);

        if (exact && (lp_is(l, "sta") || lp_is(l, "stx") || lp_is(l, "sty") || lp_is(l, "stz")))
            memory[i].write = access;
        else if (dead_updates && exact && (lp_is(l, "inc") || lp_is(l, "dec")) &&
                 !(l->out & l->def))
            memory[i].write = memory[i].update = access;
        else
            memory[i].read = access;
    }

    do {
        changed = 0;

        for (i = u->count; i-- > 0;) {
            LpLine *l = &u->lines[i];
            uint32_t out = 0, live;

            if (!l->ends)
                out = i + 1 < u->count ? memory[i + 1].live : UINT32_MAX;
            if (l->target >= 0)
                out |= memory[l->target].live;

            live = memory[i].read | (out & ~memory[i].write);

            if (out & memory[i].update)
                live |= memory[i].update;
            if (live != memory[i].live || out != memory[i].out)
                changed = 1;

            memory[i].live = live;
            memory[i].out = out;
        }
    } while (changed);
}

/* A short conditional update can keep the saved word in A. Reorder
 * the commutative add once the branch and the intervening memory
 * update are proved to preserve A and exclude alternate entries. */
static int lp_forward_conditional_word(LpUnit *u, Function *f, size_t at)
{
    unsigned i;
    (void)f;
    (void)at;

    if (u->indirect || lp_state.is_volatile || lp_state.parser->no_value_reuse)
        return 0;

    for (i = 0; i < u->count; ++i) {
        LpLine *save = &u->lines[i];
        int branch, exit, start, jump, load, clear, add;
        size_t n, m;
        const char *home = lp_operand(save, &n), *other;

        if (!lp_is(save, "sta") || save->m8 || lp_workspace_word(home, n) < 0)
            continue;

        branch = lp_next(u, i, 1);

        if (branch < 0 || !lp_branch(&u->lines[branch]) || u->lines[branch].ends ||
            u->lines[branch].target <= branch)
            continue;

        exit = u->lines[branch].target;
        start = branch + 1;
        jump = lp_next(u, (unsigned)branch, 1);

        if (jump >= 0 && u->lines[jump].ends && !u->lines[jump].call &&
            u->lines[jump].target > exit && jump + 1 == exit) {
            start = exit;
            exit = u->lines[jump].target;
        }

        for (; start < exit && !u->lines[start].op; ++start) {
            const LpLine *l = &u->lines[start];

            if (l->label) {
                if (!lp_inner_label(u, (unsigned)start, (unsigned)branch, (unsigned)branch + 1))
                    break;
            } else if (l->text[0] != ';')
                break;
        }

        if (start >= exit || u->lines[start].m8)
            continue;

        if (lp_is(&u->lines[start], "lda"))
            load = start;
        else {
            LpLine *update = &u->lines[start];

            if (lp_is(update, "dec") || lp_is(update, "inc")) {
                int exact;
                uint32_t changed = lp_workspace_access(update, &exact);
                uint32_t saved = 3u << lp_workspace_word(home, n);

                if ((update->def & LP_A) || (changed & saved))
                    continue;
            } else if (!lp_is(update, "inx") && !lp_is(update, "dex") && !lp_is(update, "iny") &&
                       !lp_is(update, "dey"))
                continue;

            load = lp_next(u, (unsigned)start, 1);
        }

        clear = load < 0 ? -1 : lp_next(u, (unsigned)load, 1);
        add = clear < 0 ? -1 : lp_next(u, (unsigned)clear, 1);

        if (add < 0 || add >= exit || u->lines[load].m8 || u->lines[add].m8 ||
            !lp_is(&u->lines[load], "lda") || !lp_line_is(&u->lines[clear], "clc") ||
            !lp_is(&u->lines[add], "adc") || !lp_operand_is(&u->lines[add], home, n))
            continue;

        other = lp_operand(&u->lines[load], &m);

        if (!lp_private(other, m) && lp_immediate(&u->lines[load]) < 0)
            continue;

        lp_insert(save, "; conditional word save\n");
        u->lines[load].deleted = 1;
        lp_set(&u->lines[add], "    adc %.*s", (int)m, other);
        return 1;
    }

    return 0;
}

static int lp_fixed_workspace(const LpUnit *u)
{
    for (unsigned i = 0; i < u->count; ++i) {
        const LpLine *l = &u->lines[i];

        if (lp_is(l, "tcd") || lp_is(l, "pld") || lp_is(l, "plb") || lp_is(l, "xce"))
            return 0;
    }

    return 1;
}

#include "region_register_values.inc"
#include "guard_frames.inc"

/* A register argument already spilled in the opposite operand order can feed
 * a commutative add directly. Later DSE removes the unused A spill. */
static int lp_direct_rhs_operand(LpUnit *u, Function *f, size_t at)
{
    (void)f;
    (void)at;

    if (u->indirect || lp_state.parser->no_value_reuse || !lp_fixed_workspace(u))
        return 0;

    for (unsigned i = 0; i < u->count; ++i) {
        LpLine *load = &u->lines[i];
        int save, lhs, alu, next;
        size_t n, m;
        const char *src, *lhs_op;

        if (load->deleted || load->replace || !lp_is(load, "lda") || load->m8)
            continue;

        src = lp_operand(load, &n);

        if (!n || memchr(src, '(', n) || memchr(src, '[', n) ||
            (n >= 2 && src[n - 2] == ',' && src[n - 1] == 'x'))
            continue;
        if (!lp_private(src, n) && (lp_state.is_volatile || n < 13 ||
                                    strncmp(src, "a:.loword(_", 11) || !pr_named(src, n)))
            continue;
        if (lp_workspace_word(src, n) == 16)
            continue; /* z:__arith_rhs */

        save = lp_next(u, i, 1);

        if (save < 0 || !lp_line_is(&u->lines[save], "sta z:__arith_rhs") || u->lines[save].m8)
            continue;

        lhs = lp_next(u, (unsigned)save, 1);

        if (lhs < 0 || !lp_is(&u->lines[lhs], "lda") || u->lines[lhs].m8)
            continue;

        lhs_op = lp_operand(&u->lines[lhs], &m);

        if (lp_workspace_word(lhs_op, m) == 16)
            continue;

        next = lp_next(u, (unsigned)lhs, 1);

        if (next >= 0 && (lp_line_is(&u->lines[next], "clc") || lp_line_is(&u->lines[next], "sec")))
            alu = lp_next(u, (unsigned)next, 1);
        else
            alu = next;

        if (alu < 0 || u->lines[alu].m8 ||
            (!lp_line_is(&u->lines[alu], "adc z:__arith_rhs") &&
             !lp_line_is(&u->lines[alu], "sbc z:__arith_rhs") &&
             !lp_line_is(&u->lines[alu], "and z:__arith_rhs") &&
             !lp_line_is(&u->lines[alu], "ora z:__arith_rhs") &&
             !lp_line_is(&u->lines[alu], "eor z:__arith_rhs") &&
             !lp_line_is(&u->lines[alu], "cmp z:__arith_rhs"))) {
            continue;
        }

        /* Ensure z:__arith_rhs is not read after alu before being overwritten */
        int k = lp_next(u, (unsigned)alu, 1), dead_rhs = 0;

        for (; k >= 0; k = lp_next(u, (unsigned)k, 1)) {
            LpLine *cur = &u->lines[k];
            size_t cn;
            const char *co = lp_operand(cur, &cn);

            if (lp_workspace_word(co, cn) == 16) {
                if (lp_is(cur, "sta") || lp_is(cur, "stx") || lp_is(cur, "sty") ||
                    lp_is(cur, "stz"))
                    dead_rhs = 1;

                break;
            }
            if (cur->ends || lp_branch(cur) || cur->call || cur->use == LP_ALL)
                break;
        }

        if (k < 0 || lp_line_is(&u->lines[k], "rts") || lp_line_is(&u->lines[k], "rtl"))
            dead_rhs = 1;
        if (!dead_rhs)
            continue;

        lp_set(&u->lines[alu], "    %.3s %.*s", u->lines[alu].op, (int)n, src);
        load->deleted = u->lines[save].deleted = 1;
        return 1;
    }

    return 0;
}

static int lp_commute_spilled_add(LpUnit *u, Function *f, size_t at)
{
    (void)f;
    (void)at;

    if (u->indirect || lp_state.is_volatile || lp_state.parser->no_value_reuse ||
        !lp_fixed_workspace(u))
        return 0;

    for (unsigned i = 0; i < u->count; ++i) {
        // Fold sta z:D; lda OP; [clc]; adc/and/ora/eor z:D into [clc]; op OP
        if (lp_is(&u->lines[i], "sta") && !u->lines[i].m8) {
            size_t an, on;
            const char *a = lp_operand(&u->lines[i], &an);
            int aslot = lp_workspace_word(a, an);
            int load = aslot < 0 ? -1 : lp_next(u, i, 1);

            if (load >= 0 && lp_is(&u->lines[load], "lda") && !u->lines[load].m8) {
                int after = lp_next(u, (unsigned)load, 1);
                int alu = after;
                int is_add = 0;

                if (after >= 0 && lp_line_is(&u->lines[after], "clc")) {
                    alu = lp_next(u, (unsigned)after, 1);
                    is_add = 1;
                }

                if (alu >= 0 && !u->lines[alu].m8 &&
                    (is_add ? lp_is(&u->lines[alu], "adc")
                            : (lp_is(&u->lines[alu], "and") || lp_is(&u->lines[alu], "ora") ||
                               lp_is(&u->lines[alu], "eor"))) &&
                    lp_operand_is(&u->lines[alu], a, an)) {
                    const char *op_text = lp_operand(&u->lines[load], &on);

                    lp_set(&u->lines[alu], "    %.3s %.*s", u->lines[alu].op, (int)on, op_text);
                    u->lines[load].deleted = 1;
                    return 1;
                }
            }
        }

        int save = lp_next(u, i, 1);
        int copy = save < 0 ? -1 : lp_next(u, (unsigned)save, 1);
        int clear = copy < 0 ? -1 : lp_next(u, (unsigned)copy, 1);
        int add = clear < 0 ? -1 : lp_next(u, (unsigned)clear, 1);
        size_t n, m;
        const char *x = lp_operand(&u->lines[i], &n), *a;
        int xslot, aslot;

        if (add < 0 || !lp_is(&u->lines[i], "stx") || u->lines[i].x8 ||
            (xslot = lp_workspace_word(x, n)) < 0 || !lp_is(&u->lines[save], "sta") ||
            u->lines[save].m8 || u->lines[add].m8 || !lp_line_is(&u->lines[copy], "txa") ||
            !lp_line_is(&u->lines[clear], "clc") || !lp_is(&u->lines[add], "adc"))
            continue;

        a = lp_operand(&u->lines[save], &m);
        aslot = lp_workspace_word(a, m);

        if (aslot < 0 || abs(xslot - aslot) < 2 || !lp_operand_is(&u->lines[add], a, m))
            continue;

        lp_set(&u->lines[add], "    adc %.*s", (int)n, x);
        u->lines[copy].deleted = 1;
        return 1;
    }

    return 0;
}

// Next non-comment line, including directives and labels
static int lp_next_noncomment(const LpUnit *u, unsigned k)
{
    unsigned i = k;

    for (;;) {
        if (++i >= u->count)
            return -1;
        if (!u->lines[i].length)
            return -1;
        if (u->lines[i].text[0] == ';')
            continue;

        return (int)i;
    }
}

// High byte of A is already zero after an 8-bit mask, so a narrow immediate CMP can stay 16-bit
static int lp_zero_extended_byte_compare(LpUnit *u, Function *f, size_t at)
{
    (void)f;
    (void)at;

    if (u->indirect)
        return 0;

    int liveness_ready = 0;

    for (unsigned i = 0; i < u->count; ++i) {
        LpLine *mask = &u->lines[i];
        long bits;
        int enter, a8, cmp, leave, a16;
        long value;

        if (mask->m8 || !lp_is(mask, "and"))
            continue;

        bits = lp_immediate(mask);

        if (bits < 0 || bits > 255)
            continue;

        enter = lp_next(u, i, 1);

        if (enter < 0 || !lp_line_is(&u->lines[enter], "sep #$20"))
            continue;

        a8 = lp_next_noncomment(u, (unsigned)enter);

        if (a8 < 0 || u->lines[a8].label || u->lines[a8].length != 3 ||
            strncmp(u->lines[a8].text, ".a8", 3))
            continue;

        cmp = lp_next_noncomment(u, (unsigned)a8);

        if (cmp < 0 || !u->lines[cmp].op || !u->lines[cmp].m8 || !lp_is(&u->lines[cmp], "cmp"))
            continue;

        value = lp_immediate(&u->lines[cmp]);

        if (value < 0 || value > 255)
            continue;

        leave = lp_next_noncomment(u, (unsigned)cmp);

        if (leave < 0 || !u->lines[leave].op || !lp_line_is(&u->lines[leave], "rep #$20"))
            continue;

        a16 = lp_next_noncomment(u, (unsigned)leave);

        if (a16 < 0 || u->lines[a16].label || u->lines[a16].length != 4 ||
            strncmp(u->lines[a16].text, ".a16", 4))
            continue;

        if (!liveness_ready) {
            lp_liveness(u);
            liveness_ready = 1;
        }

        // Only C and Z match between 8-bit and 16-bit CMP when high byte is zero
        if ((u->lines[cmp].out & LP_N) || (u->lines[leave].out & LP_N))
            continue;

        u->lines[enter].deleted = 1;
        u->lines[a8].deleted = 1;
        u->lines[leave].deleted = 1;
        u->lines[a16].deleted = 1;
        lp_set(&u->lines[cmp], "    cmp #$%04lX", value);
        return 1;
    }

    return 0;
}

// True when an instruction cannot write memory or change globals
static int lp_pure_register_or_branch(const LpLine *l)
{
    if (!l->op || l->m8 || l->x8 || l->call || l->ends || l->use == LP_ALL)
        return 0;

    if (lp_branch(l))
        return 1;

    if (lp_line_is(l, "txa") || lp_line_is(l, "tya") || lp_line_is(l, "tax") ||
        lp_line_is(l, "tay") || lp_line_is(l, "txy") || lp_line_is(l, "tyx") ||
        lp_line_is(l, "clc") || lp_line_is(l, "sec") || lp_line_is(l, "inx") ||
        lp_line_is(l, "dex") || lp_line_is(l, "iny") || lp_line_is(l, "dey") ||
        lp_line_is(l, "xba") || lp_line_is(l, "asl a") || lp_line_is(l, "lsr a") ||
        lp_line_is(l, "inc a") || lp_line_is(l, "dec a"))
        return 1;

    if (lp_is(l, "lda") || lp_is(l, "ldx") || lp_is(l, "ldy"))
        return 1;

    if ((lp_is(l, "cmp") || lp_is(l, "cpx") || lp_is(l, "cpy") || lp_is(l, "and") ||
         lp_is(l, "ora") || lp_is(l, "eor") || lp_is(l, "adc") || lp_is(l, "sbc")) &&
        lp_immediate(l) >= 0)
        return 1;

    return 0;
}

// Eliminate redundant workspace copies when reloading a direct global or forwarding to a workspace slot
static int lp_forward_workspace_copy(LpUnit *u, Function *f, size_t at)
{
    LpWorkspaceLive *memory = NULL;
    int changed = 0;

    (void)f;
    (void)at;

    if (u->indirect || lp_state.is_volatile || lp_state.parser->no_value_reuse ||
        !lp_fixed_workspace(u))
        return 0;

    for (unsigned i = 0; i < u->count; ++i) {
        LpLine *first = &u->lines[i];
        size_t sn, wn;
        const char *src, *w;

        if (first->m8 || first->x8)
            continue;

        // Case A: lda direct_global; sta z:W; [pure ops / dead-W branch]; op z:W -> op direct_global
        if (lp_is(first, "lda")) {
            int save = lp_next(u, i, 1);

            src = lp_operand(first, &sn);

            if (save >= 0 && lp_is(&u->lines[save], "sta") && !u->lines[save].m8 &&
                !memchr(src, ',', sn) && !memchr(src, '[', sn) &&
                lp_workspace_word(src, sn) < 0 &&
                ((sn > 3 && !memchr(src, '(', sn) &&
                  (!strncmp(src, "z:_", 3) || !strncmp(src, "a:_", 3))) ||
                 (sn > 12 && !strncmp(src, "a:.loword(_", 11) && src[sn - 1] == ')' &&
                  !memchr(src + 11, '(', sn - 11)))) {
                w = lp_operand(&u->lines[save], &wn);

                if (lp_workspace_word(w, wn) >= 0) {
                    if (!memory) {
                        lp_liveness(u);
                        memory = allocate(u->count * sizeof *memory);
                        lp_workspace_liveness(u, memory, 1);
                    }

                    uint32_t wmask = memory[save].write;
                    int jumped = 0;

                    for (unsigned k = (unsigned)save + 1, steps = 0; k < u->count && steps < 16;
                         ++k) {
                        LpLine *cur = &u->lines[k];

                        if (!cur->length || cur->text[0] == ';')
                            continue;

                        if (cur->label) {
                            if (cur->first_incoming >= 0)
                                break;

                            continue;
                        }

                        if (!cur->op)
                            break;

                        ++steps;

                        if (!cur->m8 &&
                            (lp_is(cur, "adc") || lp_is(cur, "sbc") || lp_is(cur, "and") ||
                             lp_is(cur, "ora") || lp_is(cur, "eor") || lp_is(cur, "cmp") ||
                             lp_is(cur, "lda")) &&
                            lp_operand_is(cur, w, wn)) {
                            if (!(memory[k].out & wmask)) {
                                lp_set(cur, "    %.3s %.*s", cur->op, (int)sn, src);
                                changed = 1;
                                goto done;
                            }

                            break;
                        }

                        // Follow a single-entry forward jmp (from relaxed-later inverted branches)
                        if (!jumped && lp_is(cur, "jmp") && !cur->indirect &&
                            cur->target > (int)k &&
                            u->lines[cur->target].first_incoming == (int)k &&
                            cur->next_incoming < 0) {
                            int prev = (int)cur->target - 1;

                            while (prev >= 0 &&
                                   (!u->lines[prev].length || u->lines[prev].text[0] == ';' ||
                                    (u->lines[prev].label &&
                                     u->lines[prev].first_incoming < 0))) {
                                --prev;
                            }

                            if (prev >= 0 && u->lines[prev].ends) {
                                jumped = 1;
                                k = (unsigned)cur->target;
                                continue;
                            }
                        }

                        if (!lp_pure_register_or_branch(cur) || (memory[k].read & wmask) ||
                            (memory[k].write & wmask))
                            break;

                        if (lp_branch(cur)) {
                            if (cur->target < 0)
                                break;

                            if (!(memory[cur->target].live & wmask))
                                continue;

                            // Follow a single-entry early-guard branch when fallthrough is dead on W
                            if (!jumped && cur->target > (int)k && k + 1 < u->count &&
                                !(memory[k + 1].live & wmask) &&
                                u->lines[cur->target].first_incoming == (int)k &&
                                cur->next_incoming < 0) {
                                int prev = (int)cur->target - 1;

                                while (prev >= 0 &&
                                       (!u->lines[prev].length || u->lines[prev].text[0] == ';' ||
                                        (u->lines[prev].label &&
                                         u->lines[prev].first_incoming < 0))) {
                                    --prev;
                                }

                                if (prev >= 0 && u->lines[prev].ends) {
                                    jumped = 1;
                                    k = (unsigned)cur->target;
                                    continue;
                                }
                            }

                            break;
                        }
                    }
                }
            }
        }

        // Case B: sta z:W; [straight-line not touching W or R]; lda z:W; sta z:R -> sta z:R
        if (lp_is(first, "sta")) {
            w = lp_operand(first, &wn);

            if (lp_workspace_word(w, wn) >= 0) {
                if (!memory) {
                    lp_liveness(u);
                    memory = allocate(u->count * sizeof *memory);
                    lp_workspace_liveness(u, memory, 1);
                }

                uint32_t wmask = memory[i].write;
                int k = lp_next(u, i, 1);

                for (unsigned steps = 0; k >= 0 && steps < 12;
                     k = lp_next(u, (unsigned)k, 1), ++steps) {
                    LpLine *cur = &u->lines[k];

                    if (cur->m8 || cur->x8 || cur->call || cur->ends || lp_branch(cur))
                        break;

                    if (lp_is(cur, "lda") && lp_operand_is(cur, w, wn)) {
                        int store = lp_next(u, (unsigned)k, 1);

                        if (store >= 0 && lp_is(&u->lines[store], "sta") && !u->lines[store].m8 &&
                            !(memory[k].out & wmask)) {
                            size_t rn;
                            const char *r = lp_operand(&u->lines[store], &rn);
                            int rslot = lp_workspace_word(r, rn);

                            if (rslot >= 0 && !(memory[store].write & wmask)) {
                                uint32_t rmask = memory[store].write;
                                int conflict = 0;

                                for (unsigned j = i + 1; j < (unsigned)k; ++j) {
                                    if ((memory[j].read & rmask) || (memory[j].write & rmask)) {
                                        conflict = 1;
                                        break;
                                    }
                                }

                                int after = lp_next(u, (unsigned)store, 1);
                                int a_dead = !(u->lines[store].out & (LP_A | LP_FLAGS)) ||
                                             (after >= 0 &&
                                              lp_shift32_helper_call(&u->lines[after]));

                                if (!conflict && a_dead) {
                                    lp_set(first, "    sta %.*s", (int)rn, r);
                                    cur->deleted = 1;
                                    u->lines[store].deleted = 1;
                                    changed = 1;
                                    goto done;
                                }
                            }
                        }

                        break;
                    }

                    if ((memory[k].read & wmask) || (memory[k].write & wmask))
                        break;
                }
            }
        }
    }

done:
    free(memory);
    return changed;
}

/* Fuse the saved trip counter with the retained X displacement. The typed
 * emitter proves that the loop cannot need more than one period of 2*i. */
static int lp_scaled_word_latch(LpUnit *u, Function *f, size_t at)
{
    unsigned i, used, slot;
    int known;
    unsigned char *targets;

    (void)f;
    (void)at;

    if (u->indirect || lp_state.is_volatile || lp_state.parser->no_index_elimination ||
        !lp_fixed_workspace(u))
        return 0;

    used = lp_text_words(u->text, u->text + strlen(u->text));

    for (slot = 0; slot < 16 && (used & (1u << slot)); ++slot) {
    }

    if (slot == 16)
        return 0;

    targets = lp_local_targets(u, &known);
    lp_liveness(u);

    if (known)
        for (i = 1; i + 3 < u->count; ++i) {
            LpLine *dec = &u->lines[i];
            int beq, jump, head, x, shift, seed, save, sub, sec, bound, push, pull, restore, step,
                first;
            size_t n, m;
            const char *index;

            if (!lp_line_is(dec, "dec z:$0000") || dec->m8 || dec->x8 ||
                (dec->out & (LP_C | LP_N)) ||
                strncmp(u->lines[i - 1].text, "; word-array loop distance fits 32768\n",
                        sizeof "; word-array loop distance fits 32768\n" - 1))
                continue;

            beq = lp_next(u, i, 1);
            jump = beq < 0 ? -1 : lp_next(u, (unsigned)beq, 1);

            if (jump < 0 || !lp_line_is(&u->lines[beq], "beq :+") ||
                !lp_is(&u->lines[jump], "jmp") || u->lines[beq].target != jump + 1)
                continue;

            head = u->lines[jump].target;

            if (head < 0 || head >= (int)i || (u->lines[head].live & LP_V))
                continue;

            step = lp_next_fallthrough(u, i, -1, targets, known);
            first = step < 0 ? -1 : lp_next_fallthrough(u, (unsigned)step, -1, targets, known);

            if (first < 0 || !lp_line_is(&u->lines[step], "inx") ||
                !lp_line_is(&u->lines[first], "inx"))
                continue;

            x = lp_next_fallthrough(u, (unsigned)head, -1, targets, known);
            shift = x < 0 ? -1 : lp_next(u, (unsigned)x, -1);
            seed = shift < 0 ? -1 : lp_next(u, (unsigned)shift, -1);
            save = seed < 0 ? -1 : lp_next_fallthrough(u, (unsigned)seed, -1, targets, known);
            sub = save < 0 ? -1 : lp_next(u, (unsigned)save, -1);
            sec = sub < 0 ? -1 : lp_next(u, (unsigned)sub, -1);
            bound = sec < 0 ? -1 : lp_next(u, (unsigned)sec, -1);
            push = bound < 0 ? -1 : lp_next(u, (unsigned)bound, -1);

            if (push < 0 || !lp_line_is(&u->lines[push], "pei ($00)") ||
                !lp_is(&u->lines[bound], "lda") || !lp_line_is(&u->lines[sec], "sec") ||
                !lp_is(&u->lines[sub], "sbc") || !lp_line_is(&u->lines[save], "sta z:$0000") ||
                !lp_is(&u->lines[seed], "lda") || !lp_line_is(&u->lines[shift], "asl a") ||
                !lp_line_is(&u->lines[x], "tax"))
                continue;

            index = lp_operand(&u->lines[seed], &n);
            const char *limit = lp_operand(&u->lines[bound], &m);

            if (lp_workspace_word(index, n) < 0 || !lp_operand_is(&u->lines[sub], index, n) ||
                lp_workspace_word(limit, m) < 0)
                continue;

            /* The branch around the backedge is the only way into the restore */
            if (targets[jump + 1] != 1)
                continue;

            pull = lp_next_fallthrough(u, (unsigned)jump + 1, 1, targets, known);
            restore = pull < 0 ? -1 : lp_next(u, (unsigned)pull, 1);

            if (restore < 0 || !lp_line_is(&u->lines[pull], "pla") ||
                !lp_line_is(&u->lines[restore], "sta z:$0000") ||
                (u->lines[restore].out & (LP_A | LP_FLAGS)))
                continue;
            if (targets[head] != 1)
                continue;

            for (unsigned j = 0; j < u->count; ++j) {
                int dest = u->lines[j].target;

                if ((j <= (unsigned)push || j >= (unsigned)pull) && dest > push && dest < pull)
                    goto next;
            }

            for (int k = push + 1; k < pull; ++k) {
                const LpLine *l = &u->lines[k];
                size_t length;
                int exact;
                const char *operand = lp_operand(l, &length);

                if (!l->op)
                    continue;
                if (l->m8 || l->x8 || l->use == LP_ALL || lp_stack_op(l) || lp_is(l, "tsx") ||
                    lp_is(l, "tsc") || (k > x && k < first && (l->def & LP_X)) ||
                    (length >= 2 && operand[length - 2] == ',' && operand[length - 1] == 's') ||
                    (length >= 5 && !memcmp(operand + length - 5, ",s),y", 5)) ||
                    (lp_workspace_access(l, &exact) & (3u << (slot * 2))) ||
                    (l->target >= 0 && (l->target < head || l->target > jump + 1)) ||
                    (l->ends && l->target < 0))
                    goto next;
            }

            u->lines[push].deleted = u->lines[sub].deleted = u->lines[pull].deleted =
                u->lines[restore].deleted = 1;
            lp_set(&u->lines[sec], "    asl a");
            lp_set(&u->lines[save], "    sta z:__arith_lhs+%u", slot * 2);
            u->lines[i - 1].deleted = 1;
            lp_insert(dec, "; scaled word-array end offset\n");
            lp_set(dec, "    cpx z:__arith_lhs+%u", slot * 2);
            free(targets);
            return 1;
        next:;
        }

    free(targets);
    return 0;
}

/* Track a saved word index through a straight-line sequence. A nearby
 * constant displacement needs only the remaining wrapping index steps. */
static int lp_saved_index_steps(LpUnit *u, Function *f, size_t at)
{
    (void)f;
    (void)at;

    if (u->indirect || lp_state.is_volatile || lp_state.parser->no_private_regions)
        return 0;

    lp_liveness(u);

    for (unsigned i = 0; i < u->count; ++i) {
        LpLine *save = &u->lines[i];
        size_t n;
        const char *home = lp_operand(save, &n);

        if (!lp_is(save, "stx") || save->x8 || lp_workspace_word(home, n) < 0)
            continue;

        int delta = 0;

        for (int j = lp_next(u, i, 1); j >= 0; j = lp_next(u, (unsigned)j, 1)) {
            LpLine *l = &u->lines[j];

            if (l->m8 || l->x8 || l->target >= 0 || l->ends || l->call ||
                lp_may_write(l, home, n, 2))
                break;

            if (lp_line_is(l, "inx"))
                ++delta;
            else if (lp_line_is(l, "dex"))
                --delta;
            else if (l->def & LP_X)
                break;
            else if (lp_is(l, "lda") && lp_operand_is(l, home, n)) {
                int carry = lp_next(u, (unsigned)j, 1);
                int add = carry < 0 ? -1 : lp_next(u, (unsigned)carry, 1);
                int move = add < 0 ? -1 : lp_next(u, (unsigned)add, 1);

                if (move < 0 || !lp_line_is(&u->lines[carry], "clc") ||
                    !lp_is(&u->lines[add], "adc") || !lp_line_is(&u->lines[move], "tax") ||
                    (u->lines[move].out & (LP_A | LP_C | LP_V)))
                    break;

                long displacement = lp_immediate(&u->lines[add]);

                if (displacement < 0)
                    break;

                int steps = (int)(int16_t)(displacement - delta);

                if (steps < -2 || steps > 2 || (!steps && (u->lines[move].out & (LP_N | LP_Z))))
                    break;

                l->deleted = u->lines[carry].deleted = u->lines[add].deleted = 1;

                if (!steps)
                    u->lines[move].deleted = 1;
                else {
                    const char *step = steps < 0 ? "dex" : "inx";

                    if (steps == -2 || steps == 2)
                        lp_set(&u->lines[move], "    %s\n    %s", step, step);
                    else
                        lp_set(&u->lines[move], "    %s", step);
                }

                return 1;
            }
        }
    }

    return 0;
}

/* Fold a small word displacement into a scaled index after adding its
 * original base. The pointer and index still wrap at the same word width. */
static int lp_scaled_base_steps(LpUnit *u, Function *f, size_t at)
{
    (void)f;
    (void)at;

    if (u->indirect || lp_state.is_volatile || lp_state.parser->no_private_regions)
        return 0;

    lp_liveness(u);

    for (unsigned i = 0; i < u->count; ++i) {
        LpLine *base = &u->lines[i];
        size_t n, m;
        const char *p = lp_operand(base, &n);

        if (!lp_is(base, "lda") || base->m8 || base->x8 || lp_workspace_word(p, n) < 0)
            continue;

        int first = lp_next(u, i, 1), k = first, count = 0;

        while (k >= 0 && lp_line_is(&u->lines[k], "inc a") && count < 3) {
            ++count;
            k = lp_next(u, (unsigned)k, 1);
        }

        if (!count || k < 0 || !lp_is(&u->lines[k], "sta"))
            continue;

        int save = k;
        const char *q = lp_operand(&u->lines[save], &m);
        int slot = lp_workspace_word(q, m);

        k = lp_next(u, (unsigned)k, 1);

        if (slot < 0 || k < 0 ||
            (!lp_line_is(&u->lines[k], "tya") && !lp_line_is(&u->lines[k], "txa")))
            continue;

        k = lp_next(u, (unsigned)k, 1);

        while (k >= 0 && lp_line_is(&u->lines[k], "asl a")) {
            k = lp_next(u, (unsigned)k, 1);
        }

        if (k < 0 || !lp_line_is(&u->lines[k], "clc"))
            continue;

        int add = lp_next(u, (unsigned)k, 1);

        if (add < 0 || !lp_is(&u->lines[add], "adc") || !lp_operand_is(&u->lines[add], q, m) ||
            (u->lines[add].out & (LP_C | LP_V)))
            continue;

        LpWorkspaceLive *state = allocate(u->count * sizeof *state);

        lp_workspace_liveness(u, state, 0);
        int dead = !(state[add].out & (3u << slot));

        free(state);

        if (!dead)
            continue;

        for (k = (int)i; k <= save; ++k) {
            if (u->lines[k].op)
                u->lines[k].deleted = 1;
        }

        lp_set(&u->lines[add], "    adc %.*s%.*s", (int)n, p, 10 * count,
               "\n    inc a\n    inc a\n    inc a");
        return 1;
    }

    return 0;
}

/* Restore a once-stepped pointer index when its only saved use is a
 * direct-page indirect load. Reversing INX/DEX preserves word wrap. */
static int lp_restore_indirect_index(LpUnit *u, Function *f, size_t at)
{
    (void)f;
    (void)at;

    if (u->indirect || lp_state.is_volatile || lp_state.parser->no_private_regions)
        return 0;

    lp_liveness(u);

    for (unsigned i = 0; i < u->count; ++i) {
        LpLine *save = &u->lines[i];
        size_t n;
        const char *home = lp_operand(save, &n);
        int slot = lp_workspace_word(home, n);

        if (slot < 0 || save->x8 || !lp_is(save, "stx"))
            continue;

        int step = lp_next(u, i, 1);

        if (step < 0 ||
            (!lp_line_is(&u->lines[step], "inx") && !lp_line_is(&u->lines[step], "dex")))
            continue;

        for (int k = lp_next(u, (unsigned)step, 1); k >= 0; k = lp_next(u, (unsigned)k, 1)) {
            LpLine *l = &u->lines[k];
            size_t m;
            const char *address = lp_operand(l, &m);

            if (l->x8 || l->m8 || l->call || l->ends || lp_branch(l) || (l->def & LP_X) ||
                l->use == LP_ALL)
                break;

            if (lp_is(l, "lda") && m == n && address[0] == '(' && address[m - 1] == ')' &&
                !memcmp(address + 1, home + 2, n - 2) && !(l->out & LP_X)) {
                LpWorkspaceLive *state = allocate(u->count * sizeof *state);

                lp_workspace_liveness(u, state, 0);
                int dead = !(state[k].out & (3u << slot));

                free(state);

                if (!dead)
                    break;

                save->deleted = 1;
                lp_set(l, "    %s\n    lda a:$0000,x",
                       lp_is(&u->lines[step], "inx") ? "dex" : "inx");
                return 1;
            }

            int exact;

            if (lp_workspace_access(l, &exact) & (3u << slot))
                break;
        }
    }

    return 0;
}

/* Compare the two ends of a short index interval directly in X when
 * normalizing the index in A would spill an unrelated pointer. */
static int lp_preserved_range_pointer(LpUnit *u, Function *f, size_t at)
{
    (void)at;

    if (u->indirect || lp_state.is_volatile || lp_state.parser->no_private_regions ||
        lp_state.parser->no_value_reuse || body_asm_statements(f->body) || !lp_fixed_workspace(u))
        return 0;

    int known, changed = 0;
    unsigned char *targets = lp_local_targets(u, &known);

    lp_liveness(u);

    for (unsigned i = 0; i < u->count; ++i) {
        LpLine *store = &u->lines[i];
        size_t length;
        const char *home = lp_operand(store, &length);
        int word = lp_workspace_word(home, length);

        if (word < 0 || !lp_is(store, "sta") || store->m8 || store->x8)
            continue;

        int move = lp_next(u, i, 1), carry = move < 0 ? -1 : lp_next(u, (unsigned)move, 1);
        int subtract = carry < 0 ? -1 : lp_next(u, (unsigned)carry, 1);
        int compare = subtract < 0 ? -1 : lp_next(u, (unsigned)subtract, 1);
        int branch = compare < 0 ? -1 : lp_next(u, (unsigned)compare, 1), after = -1;
        int outside = lp_cond_branch_target(u, branch, &after);

        if (outside < 0 || after != branch + 2 || !lp_line_is(&u->lines[branch], "bcc :+") ||
            !lp_line_is(&u->lines[move], "txa") || !lp_line_is(&u->lines[carry], "sec") ||
            !lp_is(&u->lines[subtract], "sbc") || !lp_is(&u->lines[compare], "cmp") ||
            (u->lines[branch].out & LP_FLAGS) || (u->lines[outside].live & LP_A))
            continue;

        long base = lp_immediate(&u->lines[subtract]), span = lp_immediate(&u->lines[compare]);

        if (base <= 0 || span <= 0 || base > 65535 - span)
            continue;

        int reload = lp_next_fallthrough(u, (unsigned)after, 1, targets, known);

        if (reload < 0 || !lp_is(&u->lines[reload], "ldx") ||
            !lp_operand_is(&u->lines[reload], home, length) || (u->lines[reload].out & LP_A))
            continue;

        size_t n;
        const char *jump = lp_operand(&u->lines[branch + 1], &n);

        lp_set(&u->lines[subtract], "    cpx #$%04lX\n    bcs :+\n    jmp %.*s\n:", base, (int)n,
               jump);
        lp_set(&u->lines[compare], "    cpx #$%04lX", base + span);
        lp_set(&u->lines[reload], "    tax");
        u->lines[move].deleted = u->lines[carry].deleted = 1;
        changed = 1;
        break;
    }

    free(targets);
    return changed;
}

/* A register-indexed word can be the ALU operand itself. Moving its read
 * across the private left-word load preserves the index and reads both once. */
static int lp_indexed_alu_rhs(LpUnit *u, Function *f, size_t at)
{
    (void)at;

    if (u->indirect || lp_state.is_volatile || lp_state.parser->no_private_regions ||
        body_asm_statements(f->body))
        return 0;

    for (unsigned i = 0; i < u->count; ++i) {
        LpLine *load = &u->lines[i];
        size_t n, m, k;
        const char *operand = lp_operand(load, &n);

        if (!lp_is(load, "lda") || load->m8 || load->x8 || n != 9 || strncmp(operand, "a:$", 3) ||
            operand[7] != ',' || (operand[8] != 'x' && operand[8] != 'y'))
            continue;

        int save = lp_next(u, i, 1), lhs = save < 0 ? -1 : lp_next(u, (unsigned)save, 1);
        int carry = lhs < 0 ? -1 : lp_next(u, (unsigned)lhs, 1),
            op = carry < 0 ? -1 : lp_next(u, (unsigned)carry, 1);

        if (op < 0 || !lp_is(&u->lines[save], "sta") || !lp_is(&u->lines[lhs], "lda") ||
            !lp_line_is(&u->lines[carry], "sec") || !lp_is(&u->lines[op], "sbc"))
            continue;

        const char *scratch = lp_operand(&u->lines[save], &m),
                   *left = lp_operand(&u->lines[lhs], &k);
        int word = lp_workspace_word(scratch, m);

        if (word < 0 || !lp_private(left, k) || lp_may_write(&u->lines[save], left, k, 2) ||
            !lp_operand_is(&u->lines[op], scratch, m))
            continue;

        LpWorkspaceLive *state = allocate(u->count * sizeof *state);

        lp_workspace_liveness(u, state, 0);
        int dead = !(state[op].out & (3u << word));

        free(state);

        if (dead) {
            load->deleted = u->lines[save].deleted = 1;
            lp_set(&u->lines[op], "    sbc %.*s", (int)n, operand);
            return 1;
        }
    }

    return 0;
}

static int lp_drop_dead_workspace_stores(LpUnit *u, Function *f, size_t at)
{
    LpWorkspaceLive *memory = NULL;

    unsigned i;
    int changed = 0;

    (void)f;
    (void)at;

    if (u->indirect || lp_state.is_volatile || lp_state.parser->no_value_reuse ||
        !lp_fixed_workspace(u))
        return 0;

    for (i = 0; i < u->count; ++i) {
        LpLine *l = &u->lines[i];
        size_t n;
        const char *o = lp_operand(l, &n);

        if ((!lp_is(l, "sta") && !lp_is(l, "stx") && !lp_is(l, "sty") && !lp_is(l, "stz") &&
             !lp_is(l, "inc") && !lp_is(l, "dec")) ||
            lp_workspace_word(o, n) < 0)
            continue;

        if (!memory) {
            lp_liveness(u);
            memory = allocate(u->count * sizeof *memory);
            lp_workspace_liveness(u, memory, 1);
        }

        if (memory[i].write && !(memory[i].out & memory[i].write) && !(l->out & l->def)) {
            l->deleted = 1;
            changed = 1;
        }
    }

    free(memory);
    return changed;
}

/* Once X carries the stack cursor along its complete backedge, the
 * workspace copy is unused by code outside that cursor. */
static int lp_dead_retained_varargs_cursor(LpUnit *u, Function *f, size_t at)
{
    (void)at;

    if (!f->uses_varargs || u->calls || u->indirect || lp_state.is_volatile ||
        lp_state.parser->no_private_regions || lp_state.parser->no_value_reuse ||
        body_asm_statements(f->body))
        return 0;

    PrState *frames = NULL;
    int changed = 0;

    for (unsigned i = 0; i < u->count; ++i) {
        LpLine *save = &u->lines[i];
        size_t n;
        const char *home = lp_operand(save, &n);
        int slot = lp_workspace_word(home, n);

        if (slot < 0 || save->m8 || save->x8 || !lp_is(save, "sta"))
            continue;

        int add = lp_next(u, i, -1), clear = add < 0 ? -1 : lp_next(u, (unsigned)add, -1);
        int frame = clear < 0 ? -1 : lp_next(u, (unsigned)clear, -1), index = lp_next(u, i, 1);

        if (frame < 0 || index < 0 || !lp_is(&u->lines[add], "adc") ||
            !lp_line_is(&u->lines[clear], "clc") || !lp_line_is(&u->lines[frame], "tya") ||
            !lp_line_is(&u->lines[index], "tax"))
            continue;

        long offset = lp_immediate(&u->lines[add]);

        if (offset <= (long)f->frame + 2 || offset > 255)
            continue;

        int read = index + 1, back = -1;

        for (; (unsigned)read < u->count && !u->lines[read].op; ++read) {
            const LpLine *marker = &u->lines[read];

            if (!marker->length || marker->text[0] == ';')
                continue;
            if (!lp_fallthrough_label(marker))
                break;

            if (marker->first_incoming >= 0) {
                if (back >= 0 || u->lines[marker->first_incoming].next_incoming >= 0)
                    break;

                back = marker->first_incoming;
            }
        }

        if ((unsigned)read >= u->count || back <= read ||
            !lp_line_is(&u->lines[read], "lda a:$0000,x") ||
            (!lp_is(&u->lines[back], "jmp") && !lp_is(&u->lines[back], "bra")))
            continue;

        int first = lp_next(u, (unsigned)read, 1),
            second = first < 0 ? -1 : lp_next(u, (unsigned)first, 1);
        int write = second < 0 ? -1 : lp_next(u, (unsigned)second, 1);

        if (write < 0 || write >= back || !lp_line_is(&u->lines[first], "inx") ||
            !lp_line_is(&u->lines[second], "inx") || !lp_is(&u->lines[write], "stx") ||
            !lp_operand_is(&u->lines[write], home, n))
            continue;

        int j = write + 1;

        for (; j < back; ++j) {
            const LpLine *line = &u->lines[j];

            if (line->m8 || line->x8 || line->use == LP_ALL || (line->def & LP_X))
                break;
            if (line->label && !lp_inner_label(u, (unsigned)j, (unsigned)read, (unsigned)back))
                break;
        }

        if (j != back)
            continue;
        if (!frames)
            frames = pr_states(u);
        if (!frames[frame].frame || !frames[read].frame)
            continue;

        uint32_t bits = 3u << slot;

        unsigned k = 0;

        for (; k < u->count; ++k) {
            const LpLine *line = &u->lines[k];

            if (!line->op || k == i || (int)k == read || (int)k == write)
                continue;
            if (line->use == LP_ALL)
                break;

            int exact, within = lp_frame_indexed_offset(line, 'y');

            if (within > 0 && within < 256 && frames[k].frame)
                continue;
            if (lp_workspace_access(line, &exact) & bits)
                break;
        }

        if (k != u->count)
            continue;

        save->deleted = u->lines[write].deleted = 1;
        changed = 1;
        break;
    }

    free(frames);
    return changed;
}

/* A far pointer already on the hardware stack can be read using D=S.
 * Preserve D and rebase the pointer past PHD. PLD changes N/Z and a byte
 * load retains the accumulator high byte, so both must be dead. */
static int lp_far_stack_read(LpUnit *u, Function *f, size_t at)
{
    (void)at;

    if (u->indirect || lp_state.is_volatile || body_asm_statements(f->body))
        return 0;

    lp_liveness(u);

    for (unsigned i = 0; i < u->count; ++i) {
        LpLine *high = &u->lines[i];

        if (high->m8 || !lp_is(high, "lda"))
            continue;

        size_t n;
        const char *operand = lp_operand(high, &n);
        char *end;
        long offset = strtol(operand, &end, 10);

        if (n < 3 || end != operand + n - 2 || strncmp(end, ",s", 2) || offset < 3 || offset > 255)
            continue;

        int sh = lp_next(u, i, 1), low = sh < 0 ? -1 : lp_next(u, (unsigned)sh, 1);
        int sl = low < 0 ? -1 : lp_next(u, (unsigned)low, 1),
            mode = sl < 0 ? -1 : lp_next(u, (unsigned)sl, 1);

        if (mode < 0 || !lp_line_is(&u->lines[sh], "sta z:__arith_lhs+2") ||
            !lp_is(&u->lines[low], "lda") || !lp_line_is(&u->lines[sl], "sta z:__arith_lhs") ||
            !lp_line_is(&u->lines[mode], "sep #$20"))
            continue;

        operand = lp_operand(&u->lines[low], &n);

        if (strtol(operand, &end, 10) != offset - 2 || n < 3 || end != operand + n - 2 ||
            strncmp(end, ",s", 2))
            continue;

        int read = lp_next_mode(u, (unsigned)mode);

        if (read < 0 || !u->lines[read].m8 || !lp_line_is(&u->lines[read], "lda [__arith_lhs]") ||
            (u->lines[read].out & (LP_AH | LP_N | LP_Z)))
            continue;

        LpWorkspaceLive *memory = allocate(u->count * sizeof *memory);

        lp_workspace_liveness(u, memory, 0);
        int live = (memory[read].out & 15) != 0;

        free(memory);

        if (live)
            continue;

        lp_set(high, "    phd");
        lp_set(&u->lines[sh], "    tsc");
        lp_set(&u->lines[low], "    tcd");
        u->lines[sl].deleted = 1;
        lp_set(&u->lines[read], "    lda [$%02lX]\n    pld", offset);
        return 1;
    }

    return 0;
}

/* An OR reduction can start with its last-produced operand still in A.
 * Keep its store for any other readers, then let workspace DSE remove it. */
static int lp_forward_or_chain(LpUnit *u, Function *f, size_t at)
{
    (void)f;
    (void)at;

    if (u->indirect || lp_state.is_volatile || lp_state.parser->no_value_reuse ||
        !lp_fixed_workspace(u))
        return 0;

    for (unsigned i = 0; i < u->count; ++i) {
        LpLine *save = &u->lines[i];
        size_t n, m;
        const char *home = lp_operand(save, &n), *first;
        int load, combine;

        if (!lp_is(save, "sta") || save->m8 || lp_workspace_word(home, n) < 0)
            continue;

        load = lp_next(u, i, 1);

        if (load < 0 || !lp_is(&u->lines[load], "lda") || u->lines[load].m8)
            continue;

        first = lp_operand(&u->lines[load], &m);

        if (lp_workspace_word(first, m) < 0)
            continue;

        for (combine = lp_next(u, (unsigned)load, 1); combine >= 0;
             combine = lp_next(u, (unsigned)combine, 1)) {
            LpLine *op = &u->lines[combine];

            if (!lp_is(op, "ora") || op->m8)
                break;
            if (!lp_operand_is(op, home, n))
                continue;

            u->lines[load].deleted = 1;
            lp_set(op, "    ora %.*s", (int)m, first);
            return 1;
        }
    }

    return 0;
}

/* Accumulator mode switches preserve carry. Look through them to a
 * straight-line overwrite when general register liveness is conservative. */
static int lp_carry_overwritten(const LpUnit *u, unsigned start)
{
    for (unsigned i = start + 1; i < u->count; ++i) {
        const LpLine *l = &u->lines[i];

        if (lp_line_is(l, "sep #$20") || lp_line_is(l, "rep #$20"))
            continue;
        if (!l->op) {
            if (l->text[0] == ';' || !strncmp(l->text, ".a8\n", 4) ||
                !strncmp(l->text, ".a16\n", 5))
                continue;

            return 0;
        }
        if (l->ends || l->call || l->target >= 0 || (l->use & LP_C))
            return 0;
        if (l->def & LP_C)
            return 1;
    }

    return 0;
}

/* If a shift-and-combine already has one input in A, shift it first.
 * The other input must be independent of the scratch store moved ahead
 * of its load. The final logical operation restores N/Z, but not carry. */
static int lp_forward_shifted_word(LpUnit *u, Function *f, size_t at)
{
    unsigned i;
    LpWorkspaceLive *memory = NULL;

    (void)f;
    (void)at;

    if (u->indirect || lp_state.is_volatile || lp_state.parser->no_value_reuse ||
        !lp_fixed_workspace(u))
        return 0;

    for (i = 0; i < u->count; ++i) {
        LpLine *save = &u->lines[i];
        int load, left, stage, reload, right, combine, source, temporary, other_home;
        size_t n, m, other_n, used = 0;
        const char *home = lp_operand(save, &n), *scratch, *other, *shift;

        unsigned count = 0;
        char before[256];

        if (!lp_is(save, "sta") || save->m8 || (source = lp_workspace_word(home, n)) < 0)
            continue;

        load = lp_next(u, i, 1);

        if (load < 0 || u->lines[load].m8 || !lp_is(&u->lines[load], "lda"))
            continue;

        other = lp_operand(&u->lines[load], &other_n);
        other_home = lp_workspace_word(other, other_n);

        if (other_home < 0 && !(lp_private(other, other_n) && other[other_n - 1] == 's'))
            continue;

        left = lp_next(u, (unsigned)load, 1);

        for (stage = left; stage >= 0; stage = lp_next(u, (unsigned)stage, 1)) {
            if (!lp_line_is(&u->lines[stage], "asl a") && !lp_line_is(&u->lines[stage], "lsr a"))
                break;
        }

        if (stage < 0 || stage == left || !lp_is(&u->lines[stage], "sta"))
            continue;

        scratch = lp_operand(&u->lines[stage], &m);
        temporary = lp_workspace_word(scratch, m);

        if (temporary < 0 || abs(source - temporary) < 2 ||
            (other_home >= 0 && abs(other_home - temporary) < 2))
            continue;

        reload = lp_next(u, (unsigned)stage, 1);

        if (reload < 0 || !lp_is(&u->lines[reload], "lda") ||
            !lp_operand_is(&u->lines[reload], home, n))
            continue;

        right = lp_next(u, (unsigned)reload, 1);

        if (right < 0)
            continue;

        shift = lp_line_is(&u->lines[right], "lsr a") ? "lsr a" : "asl a";

        for (combine = right; combine >= 0 && lp_line_is(&u->lines[combine], shift);
             combine = lp_next(u, (unsigned)combine, 1)) {
            ++count;
        }

        if (!count || count > 15 || combine < 0 || !lp_operand_is(&u->lines[combine], scratch, m) ||
            (!lp_is(&u->lines[combine], "ora") && !lp_is(&u->lines[combine], "eor") &&
             !lp_is(&u->lines[combine], "and")))
            continue;

        if (!memory) {
            lp_liveness(u);
            memory = allocate(u->count * sizeof *memory);
            lp_workspace_liveness(u, memory, 0);
        }

        if ((memory[combine].out & (3u << temporary)) ||
            ((u->lines[combine].out & LP_C) && !lp_carry_overwritten(u, (unsigned)combine)))
            continue;

        for (unsigned step = 0; step < count; ++step) {
            used += (size_t)snprintf(before + used, sizeof before - used, "    %s\n", shift);
        }

        snprintf(before + used, sizeof before - used, "    sta %.*s\n", (int)m, scratch);
        lp_insert(&u->lines[load], before);
        u->lines[stage].deleted = u->lines[reload].deleted = 1;

        for (; right < combine; ++right) {
            if (u->lines[right].op)
                u->lines[right].deleted = 1;
        }

        free(memory);
        return 1;
    }

    free(memory);
    return 0;
}

/* Compute a masked private word in unused divider wait slots, then
 * combine it with the result directly in A. Each replacement takes
 * at least as many cycles as the NOP it replaces. */
static int lp_divider_wait_mask(LpUnit *u, Function *f, size_t at)
{
    LpWorkspaceLive *memory = NULL;

    (void)f;
    (void)at;

    if (u->indirect || lp_state.is_volatile || lp_state.parser->no_value_reuse ||
        lp_state.parser->no_strength_reduction || !lp_fixed_workspace(u))
        return 0;

    for (unsigned trigger = 0; trigger < u->count; ++trigger) {
        int first, ready = lp_divider_wait(u, trigger, &first), slot, result, stage, load, mask,
                   join;
        size_t input_n, scratch_n, mask_n;
        const char *input, *scratch, *immediate;
        int input_home, scratch_home;
        uint32_t saved = 0, input_bytes = 0;

        if (ready < 0)
            continue;

        for (slot = first; slot + 2 < ready; ++slot) {
            if (lp_line_is(&u->lines[slot], "nop") && lp_line_is(&u->lines[slot + 1], "nop") &&
                lp_line_is(&u->lines[slot + 2], "nop"))
                break;
        }

        if (slot + 2 >= ready)
            continue;

        result = ready;

        if (lp_line_is(&u->lines[ready], "lda f:$004214")) {
            for (result = lp_next(u, (unsigned)ready, 1);
                 result >= 0 && lp_is(&u->lines[result], "sta");
                 result = lp_next(u, (unsigned)result, 1)) {
                int exact;
                size_t n;
                const char *o = lp_operand(&u->lines[result], &n);

                if (lp_workspace_word(o, n) < 0)
                    break;

                saved |= lp_workspace_access(&u->lines[result], &exact);
            }
        }

        if (result < 0 || !lp_line_is(&u->lines[result], "lda f:$004216"))
            continue;

        for (stage = lp_next(u, (unsigned)result, 1); stage >= 0;
             stage = lp_next(u, (unsigned)stage, 1)) {
            if (!lp_line_is(&u->lines[stage], "asl a") && !lp_line_is(&u->lines[stage], "lsr a"))
                break;
        }

        if (stage < 0 || !lp_is(&u->lines[stage], "sta"))
            continue;

        scratch = lp_operand(&u->lines[stage], &scratch_n);
        scratch_home = lp_workspace_word(scratch, scratch_n);

        if (scratch_home < 0)
            continue;

        load = lp_next(u, (unsigned)stage, 1);
        mask = load < 0 ? -1 : lp_next(u, (unsigned)load, 1);
        join = mask < 0 ? -1 : lp_next(u, (unsigned)mask, 1);

        if (join < 0 || !lp_is(&u->lines[mask], "and") || lp_immediate(&u->lines[mask]) < 0 ||
            !lp_operand_is(&u->lines[join], scratch, scratch_n) ||
            (!lp_is(&u->lines[join], "ora") && !lp_is(&u->lines[join], "and") &&
             !lp_is(&u->lines[join], "eor")))
            continue;

        input = lp_operand(&u->lines[load], &input_n);
        input_home = lp_workspace_word(input, input_n);

        if (lp_is(&u->lines[load], "lda")) {
            if (input_home < 0 || abs(input_home - scratch_home) < 2)
                continue;

            input_bytes = 3u << input_home;
        } else {
            int k, from_x = lp_line_is(&u->lines[load], "txa");

            if (!from_x && !lp_line_is(&u->lines[load], "tya"))
                continue;

            for (k = slot + 3; k < ready; ++k) {
                if (lp_is(&u->lines[k], from_x ? "inx" : "iny") ||
                    lp_is(&u->lines[k], from_x ? "dex" : "dey"))
                    break;
            }

            if (k < ready)
                continue;
        }

        if (saved & (input_bytes | (3u << scratch_home)))
            continue;

        if (!memory) {
            memory = allocate(u->count * sizeof *memory);
            lp_workspace_liveness(u, memory, 0);
        }

        if (memory[join].out & (3u << scratch_home))
            continue;

        immediate = lp_operand(&u->lines[mask], &mask_n);

        if (input_bytes)
            lp_set(&u->lines[slot], "    lda %.*s", (int)input_n, input);
        else
            lp_set(&u->lines[slot], "    %.3s", u->lines[load].op);

        lp_set(&u->lines[slot + 1], "    and %.*s", (int)mask_n, immediate);
        lp_set(&u->lines[slot + 2], "    sta %.*s", (int)scratch_n, scratch);
        u->lines[stage].deleted = u->lines[load].deleted = u->lines[mask].deleted = 1;
        free(memory);
        return 1;
    }

    free(memory);
    return 0;
}

/* Only the low byte of this private load starts the divider. The
 * wait touches no part of A, and the first ready-result read overwrites
 * the full word before the old high byte can be observed. */
static int lp_narrow_divisor_load(LpUnit *u, Function *f, size_t at)
{
    unsigned i;
    (void)f;
    (void)at;

    if (lp_state.is_volatile || u->indirect || lp_state.parser->no_strength_reduction)
        return 0;

    for (i = 0; i + 12 < u->count; ++i) {
        LpLine *load = &u->lines[i];
        int sep = lp_next(u, i, 1), trigger, first;
        size_t n;
        const char *operand = lp_operand(load, &n);

        if (!lp_is(load, "lda") || load->m8 || !lp_private(operand, n) || sep < 0 ||
            !lp_line_is(&u->lines[sep], "sep #$20") || (unsigned)sep + 2 >= u->count ||
            strncmp(u->lines[sep + 1].text, ".a8\n", 4))
            continue;

        trigger = lp_next(u, (unsigned)sep + 1, 1);

        if (trigger < 0 || lp_divider_wait(u, (unsigned)trigger, &first) < 0)
            continue;

        lp_set(load, "    sep #$20\n.a8\n    lda %.*s", (int)n, operand);
        u->lines[sep].deleted = u->lines[sep + 1].deleted = 1;
        return 1;
    }

    return 0;
}

/* Drop straight-line stores to private frame locals right before teardown */
static int lp_frame_byte_private(Function *f, unsigned byte)
{
    unsigned i;

    for (i = 0; i < lp_state.parser->symbol_count; ++i) {
        Symbol *v = &lp_state.parser->symbols[i];

        if (v->owner == f->id && v->offset && byte >= v->offset &&
            byte < v->offset + width(v->type))
            return loop_private(v) && !object_volatile(v->type) && !structure_object(v->type) &&
                   !v->type.array && value_width(v->type) <= 4;
    }

    return 1;
}

/* Keep a private argument in X while preparing other call operands */
static int lp_keep_frame_argument_in_x(LpUnit *u, Function *f, size_t at)
{
    (void)at;

    if (!f->slots || u->indirect || lp_state.parser->no_private_regions ||
        lp_state.parser->no_value_reuse || body_asm_statements(f->body))
        return 0;

    for (unsigned i = 0; i < (f->slots + 1) / 2 && i < 384; ++i) {
        if (lp_state.frame_map[i])
            return 0;
    }

    for (unsigned i = 0; i < u->count; ++i) {
        size_t n;
        const char *operand = lp_operand(&u->lines[i], &n);

        if (lp_operand_has_s(operand, n))
            return 0;
    }

    int known;
    unsigned char *targets = lp_local_targets(u, &known);
    PrState *frames = pr_states(u);

    lp_liveness(u);
    int changed = 0;

    for (unsigned i = 0; i < u->count && !changed; ++i) {
        LpLine *save = &u->lines[i];

        if (!lp_is(save, "sta") || save->m8 || save->x8 || !frames[i].frame ||
            (save->out & (LP_N | LP_Z)))
            continue;

        int slot = lp_frame_indexed_offset(save, 'y');

        if (slot <= 0 || (unsigned)(slot + 1) > f->slots ||
            !lp_frame_byte_private(f, (unsigned)slot) ||
            !lp_frame_byte_private(f, (unsigned)slot + 1))
            continue;

        int reload = (int)i;

        do {
            reload = lp_next_fallthrough(u, (unsigned)reload, 1, targets, known);

            if (reload < 0 || (unsigned)reload > i + 32) {
                reload = -1;
                break;
            }

            LpLine *line = &u->lines[reload];

            if (lp_is(line, "ldx") && !line->x8 && lp_frame_indexed_offset(line, 'y') == slot)
                break;
            if (line->call || line->ends || lp_branch(line) || line->x8 ||
                ((line->use | line->def) & LP_X)) {
                reload = -1;
                break;
            }
        } while (1);

        if (reload < 0 || !frames[reload].frame || (u->lines[reload].out & (LP_N | LP_Z)))
            continue;

        int exclusive = 1;

        for (unsigned j = 0; j < u->count && exclusive; ++j) {
            if (j == i || j == (unsigned)reload)
                continue;

            int off = lp_frame_indexed_offset(&u->lines[j], 'y');

            if (off >= 0 &&
                (!frames[j].frame || (off <= slot + 1 && off + lp_width(&u->lines[j]) > slot)))
                exclusive = 0;
        }

        if (!exclusive)
            continue;

        lp_set(save, "    tax");
        u->lines[reload].deleted = 1;
        changed = 1;
    }

    free(frames);
    free(targets);
    return changed;
}

static int lp_dead_epilogue_stores(LpUnit *u, Function *f, size_t at)
{
    unsigned i;
    int changed = 0;

    (void)at;

    if (lp_state.parser->no_private_regions || lp_state.is_volatile || lp_state.frame_address ||
        u->indirect)
        return 0;

    for (i = 0; i < u->count; ++i) {
        LpLine *l = &u->lines[i];
        size_t n;
        const char *o;
        char *end;

        unsigned off = 0, w, k, steps = 0;
        int is_y = 0, dead = 0;

        if (l->deleted || l->replace || l->call || !lp_is(l, "sta"))
            continue;

        w = (unsigned)lp_width(l);
        o = lp_operand(l, &n);

        if (n == 9 && !strncmp(o, "a:$", 3) && o[7] == ',' && o[8] == 'y') {
            off = (unsigned)strtoul(o + 3, &end, 16);

            if (end != o + 7)
                continue;

            is_y = 1;
        } else if (n >= 3 && o[n - 2] == ',' && o[n - 1] == 's' && isdigit((unsigned char)o[0])) {
            off = (unsigned)strtoul(o, &end, 10);

            if (end != o + n - 2)
                continue;

            is_y = 0;
        } else
            continue;

        if (!off || off + w - 1 > f->slots || !lp_frame_byte_private(f, off) ||
            (w == 2 && !lp_frame_byte_private(f, off + 1)))
            continue;

        k = i + 1;

        while (k < u->count && steps++ < 64) {
            LpLine *p = &u->lines[k];

            if (p->deleted) {
                ++k;
                continue;
            }
            if (p->replace || p->call)
                break;

            if (!p->op) {
                if (!p->length || p->text[0] == ';' || !strncmp(p->text, ".a8", 3) ||
                    !strncmp(p->text, ".a16", 4) || p->label) {
                    ++k;
                    continue;
                }

                break;
            }

            if (lp_is(p, "bra") || (lp_is(p, "jmp") && p->target >= 0)) {
                if (p->target < 0)
                    break;

                k = (unsigned)p->target;
                continue;
            }

            if (lp_line_is(p, is_y ? "tya" : "tsc")) {
                int c = lp_next(u, k, 1), a = c < 0 ? -1 : lp_next(u, (unsigned)c, 1),
                    t = a < 0 ? -1 : lp_next(u, (unsigned)a, 1);
                long freed;

                if (c >= 0 && a >= 0 && t >= 0 && lp_line_is(&u->lines[c], "clc") &&
                    lp_is(&u->lines[a], "adc") && !u->lines[a].m8 &&
                    (freed = lp_immediate(&u->lines[a])) > 0 && lp_line_is(&u->lines[t], "tcs")) {
                    if ((unsigned long)(off + w - 1) <= (unsigned long)freed)
                        dead = 1;
                }

                break;
            }

            if (p->ends || lp_branch(p) || lp_stack_op(p))
                break;
            if (is_y && (p->def & LP_Y))
                break;

            if (lp_is(p, "sep") || lp_is(p, "rep") || lp_line_is(p, "clc") ||
                lp_line_is(p, "sec") || lp_line_is(p, "tax") || lp_line_is(p, "txa") ||
                (!is_y && (lp_line_is(p, "tay") || lp_line_is(p, "tya"))) ||
                lp_line_is(p, "inc a") || lp_line_is(p, "dec a") || lp_line_is(p, "asl a") ||
                lp_line_is(p, "lsr a") || lp_line_is(p, "xba")) {
                ++k;
                continue;
            }

            if (lp_is(p, "lda") || lp_is(p, "ldx") || lp_is(p, "sta") || lp_is(p, "stx") ||
                lp_is(p, "stz") || lp_is(p, "adc") || lp_is(p, "sbc") || lp_is(p, "and") ||
                lp_is(p, "ora") || lp_is(p, "eor") || lp_is(p, "cmp")) {
                size_t pn;
                const char *po = lp_operand(p, &pn);

                if (pn && po[0] == '#') {
                    ++k;
                    continue;
                }
                if (lp_workspace_word(po, pn) >= 0) {
                    ++k;
                    continue;
                }

                if (is_y && pn == 9 && !strncmp(po, "a:$", 3) && po[7] == ',' && po[8] == 'y') {
                    char *pe;

                    unsigned po_off = (unsigned)strtoul(po + 3, &pe, 16),
                             po_w = (unsigned)lp_width(p);

                    if (pe == po + 7 && (po_off + po_w <= off || off + w <= po_off)) {
                        ++k;
                        continue;
                    }
                }
            }

            break;
        }

        if (dead) {
            l->deleted = 1;
            changed = 1;
        }
    }

    return changed;
}

/* A zero edge can bypass a dead frame counter step and the subsequent
 * repeat of the same two-word zero test. */
static int lp_skip_dead_loop_step(LpUnit *u, Function *f, size_t at)
{
    int known, matched = 0;
    unsigned char *targets;

    (void)at;

    if (lp_state.frame_address || lp_state.is_volatile || lp_state.parser->no_private_regions ||
        u->indirect || body_asm_statements(f->body))
        return 0;

    targets = lp_local_targets(u, &known);

    if (!known) {
        free(targets);
        return 0;
    }

    for (unsigned i = 0; i < u->count; ++i) {
        LpLine *edge = &u->lines[i];
        int after, join = lp_cond_branch_target(u, (int)i, &after);

        if (join <= (int)i || edge->m8 || !lp_is(edge, after == (int)i ? "beq" : "bne"))
            continue;

        int first_or = lp_next(u, i, -1);
        int high = first_or < 0 ? -1 : lp_next(u, (unsigned)first_or, -1);
        int counter = lp_next_fallthrough(u, (unsigned)join, 1, targets, known);
        int increment = counter < 0 ? -1 : lp_next(u, (unsigned)counter, 1);
        int save = increment < 0 ? -1 : lp_next(u, (unsigned)increment, 1);
        int reread = save < 0 ? -1 : lp_next_fallthrough(u, (unsigned)save, 1, targets, known);
        int last_or = reread < 0 ? -1 : lp_next(u, (unsigned)reread, 1);
        int repeat = last_or < 0 ? -1 : lp_next(u, (unsigned)last_or, 1);
        int repeat_after, back = lp_cond_branch_target(u, repeat, &repeat_after);

        if (high < 0 || repeat < 0 || !lp_is(&u->lines[first_or], "ora") ||
            (!lp_is(&u->lines[high], "lda") && !lp_is(&u->lines[high], "sta")) ||
            !lp_is(&u->lines[counter], "lda") || !lp_line_is(&u->lines[increment], "inc a") ||
            !lp_is(&u->lines[save], "sta") || !lp_is(&u->lines[reread], "lda") ||
            !lp_is(&u->lines[last_or], "ora") || back < 0 || back >= (int)i ||
            !lp_is(&u->lines[repeat], repeat_after == repeat ? "bne" : "beq") ||
            u->lines[counter].m8 || u->lines[reread].m8 || u->lines[repeat].m8)
            continue;

        int release = repeat_after + 1;

        while ((unsigned)release < u->count && !u->lines[release].op) {
            ++release;
        }

        int clear = (unsigned)release < u->count ? lp_next(u, (unsigned)release, 1) : -1;
        int add = clear < 0 ? -1 : lp_next(u, (unsigned)clear, 1);
        int set = add < 0 ? -1 : lp_next(u, (unsigned)add, 1);

        if (set < 0 || !lp_line_is(&u->lines[release], "tya") ||
            !lp_line_is(&u->lines[clear], "clc") || !lp_is(&u->lines[add], "adc") ||
            !lp_line_is(&u->lines[set], "tcs"))
            continue;

        size_t n, upper_length, lower_length;
        const char *slot = lp_operand(&u->lines[counter], &n);
        const char *upper = lp_operand(&u->lines[high], &upper_length);
        const char *lower = lp_operand(&u->lines[first_or], &lower_length);

        if (n != 9 || strncmp(slot, "a:$", 3) || strncmp(slot + 7, ",y", 2) ||
            !lp_operand_is(&u->lines[save], slot, n) || !lp_private(upper, upper_length) ||
            !lp_private(lower, lower_length) ||
            !lp_operand_is(&u->lines[reread], upper, upper_length) ||
            !lp_operand_is(&u->lines[last_or], lower, lower_length) ||
            lp_may_write(&u->lines[save], lower, lower_length, 2) ||
            lp_may_write(&u->lines[save], upper, upper_length, 2))
            continue;

        unsigned offset = (unsigned)strtoul(slot + 3, NULL, 16);

        if (!offset || offset + 1 > f->slots || (long)offset + 1 > lp_immediate(&u->lines[add]) ||
            !lp_frame_byte_private(f, offset) || !lp_frame_byte_private(f, offset + 1))
            continue;

        unsigned label = lp_next_label();
        char destination[96];

        snprintf(destination, sizeof destination, "cg_%s_%u = *\n", lp_state.parser->unit, label);
        lp_insert(&u->lines[release], destination);

        if (after == (int)i)
            lp_set(edge, "    beq cg_%s_%u", lp_state.parser->unit, label);
        else
            lp_set(&u->lines[i + 1], "    jmp .loword(cg_%s_%u)", lp_state.parser->unit, label);

        matched = 1;
        break;
    }

    free(targets);
    return matched;
}

static int lp_abs_x_operand(const char *o, size_t n)
{
    const char *comma;

    if (n < 6 || strncmp(o, "a:", 2) || o[n - 2] != ',' || o[n - 1] != 'x')
        return 0;

    comma = memchr(o, ',', n);
    return comma == o + n - 2;
}

static int lp_can_wrap_fn_y(const LpUnit *u, const Function *f, unsigned *entry_out)
{
    unsigned i, entry = 0, returns = 0;

    if (f->symbol->interrupt || f->frame || u->indirect)
        return 0;

    while (entry < u->count && !u->lines[entry].op) {
        ++entry;
    }

    if (entry == u->count)
        return 0;

    for (i = entry; i < u->count; ++i) {
        const LpLine *l = &u->lines[i];
        size_t n;
        const char *o = lp_operand(l, &n);

        if (!l->op || l->deleted)
            continue;
        if (l->x8 || (l->target >= 0 && (unsigned)l->target <= entry))
            return 0;
        if (lp_is(l, "rti") || (l->call && (lp_is(l, "jmp") || lp_is(l, "jml"))))
            return 0;
        if (lp_is(l, "rts") || lp_is(l, "rtl")) {
            ++returns;
            continue;
        }
        if (lp_is(l, "tcs") || lp_is(l, "txs") || lp_is(l, "tsc") || lp_is(l, "tsx") ||
            lp_operand_has_s(o, n))
            return 0;
        if (!l->call && !lp_line_is(l, "sep #$20") && !lp_line_is(l, "rep #$20") &&
            (l->use == LP_ALL || ((l->use | l->def) & LP_Y)))
            return 0;
    }

    if (!returns)
        return 0;

    *entry_out = entry;
    return 1;
}

/* Straight-line tax / (phx ... plx / sta|stz a:...,x)+ ending with dead X:
 * keep the saved index in Y and eliminate all X push/pull traffic. */
static int lp_y_saved_index(LpUnit *u, Function *f, size_t at)
{
    unsigned i, entry = 0;
    int can_wrap_fn_y = !u->indirect && lp_can_wrap_fn_y(u, f, &entry);

    (void)at;

    if (u->indirect)
        return 0;

    lp_liveness(u);

    for (i = 0; i < u->count; ++i) {
        LpLine *tax = &u->lines[i];

        unsigned phxs[32], plxs[32], stores[32], saves = 0, nstores = 0, j;
        int in_save = 0, x_clobbered = 0, inner_x_def = 0, done = 0, y_live;

        if (!lp_line_is(tax, "tax") || tax->x8 || tax->deleted || tax->replace ||
            (tax->out & (LP_N | LP_Z)))
            continue;

        y_live = (tax->out & LP_Y) != 0;

        for (j = i + 1; j < u->count && !done; ++j) {
            LpLine *l = &u->lines[j];
            size_t n;
            const char *o = lp_operand(l, &n);

            if (l->deleted || l->replace || l->label)
                break;

            if (!l->op) {
                if (!l->length)
                    break;
                if (l->text[0] == ';' || (l->length == 3 && !strncmp(l->text, ".a8", 3)) ||
                    (l->length == 4 && !strncmp(l->text, ".a16", 4)))
                    continue;

                break;
            }

            if (l->x8 || l->call || l->ends || lp_branch(l))
                break;
            if ((l->use & LP_Y) || (l->def & LP_Y))
                break;
            if (l->use == LP_ALL && !lp_line_is(l, "sep #$20") && !lp_line_is(l, "rep #$20"))
                break;

            if (in_save) {
                if (lp_line_is(l, "plx")) {
                    if ((l->out & (LP_N | LP_Z)) || saves >= 32)
                        break;

                    plxs[saves++] = j;
                    in_save = 0;
                } else {
                    if (lp_stack_op(l) || lp_operand_has_s(o, n))
                        break;
                    if ((l->use & LP_X) && x_clobbered && !inner_x_def)
                        break;
                    if ((l->def & LP_X) && !(l->use & LP_X))
                        inner_x_def = 1;
                    if (l->def & LP_X)
                        x_clobbered = 1;
                }
            } else {
                if (lp_line_is(l, "phx")) {
                    if (saves >= 32)
                        break;

                    phxs[saves] = j;
                    in_save = 1;
                    inner_x_def = 0;
                } else if ((lp_is(l, "sta") || lp_is(l, "stz") || lp_is(l, "lda") ||
                            lp_is(l, "adc") || lp_is(l, "sbc") || lp_is(l, "and") ||
                            lp_is(l, "ora") || lp_is(l, "eor") || lp_is(l, "cmp")) &&
                           !(l->def & LP_X) && lp_abs_x_operand(o, n)) {
                    if (lp_is(l, "stz") && (!l->m8 || (l->out & (LP_A | LP_N | LP_Z))))
                        break;
                    if (nstores >= 32)
                        break;

                    stores[nstores++] = j;

                    if (!(l->out & LP_X)) {
                        done = 1;
                        break;
                    }
                } else if (lp_line_is(l, "sep #$20") || lp_line_is(l, "rep #$20")) {
                    continue;
                } else if (!(l->use & LP_X) && !(l->def & LP_X) && !lp_stack_op(l) &&
                           !lp_operand_has_s(o, n)) {
                    continue;
                } else
                    break;
            }
        }

        if (done && !in_save && saves > 0 && nstores > 0) {
            unsigned k;

            if (y_live) {
                if (can_wrap_fn_y) {
                    lp_insert(&u->lines[entry], "    phy\n");

                    for (k = entry; k < u->count; ++k) {
                        if (!u->lines[k].deleted &&
                            (lp_is(&u->lines[k], "rts") || lp_is(&u->lines[k], "rtl")))
                            lp_insert(&u->lines[k], "    ply\n");
                    }

                    lp_set(tax, "    tay");
                } else if (saves >= 2 && !(u->lines[stores[nstores - 1]].out & (LP_N | LP_Z))) {
                    lp_set(tax, "    phy\n    tay");
                } else
                    continue;
            } else {
                lp_set(tax, "    tay");
            }

            for (k = 0; k < saves; ++k) {
                u->lines[phxs[k]].deleted = u->lines[plxs[k]].deleted = 1;
            }

            for (k = 0; k < nstores; ++k) {
                LpLine *c = &u->lines[stores[k]];
                size_t n;
                const char *o = lp_operand(c, &n);
                const char *tail =
                    (y_live && !can_wrap_fn_y && k + 1 == nstores) ? "\n    ply" : "";

                if (lp_is(c, "stz"))
                    lp_set(c, "    lda #$00\n    sta %.*s,y%s", (int)(n - 2), o, tail);
                else
                    lp_set(c, "    %.3s %.*s,y%s", c->op, (int)(n - 2), o, tail);
            }

            return 1;
        }
    }

    return 0;
}

static int lp_y_scratch_match(const LpUnit *u, const LpWorkspaceLive *memory, unsigned i, int slot,
                              int *mul_out)
{
    int j, mul_at = -1;

    for (j = (int)i + 1; (unsigned)j < u->count; ++j) {
        const LpLine *l = &u->lines[j];
        size_t m;
        const char *lo = lp_operand(l, &m);

        if (l->deleted)
            continue;
        if (l->replace || l->label)
            break;

        if (!l->op) {
            if (!l->length)
                break;
            if (l->text[0] == ';' || (l->length == 3 && !strncmp(l->text, ".a8", 3)) ||
                (l->length == 4 && !strncmp(l->text, ".a16", 4)))
                continue;

            break;
        }

        if (l->x8 || l->call || l->ends || lp_branch(l))
            break;
        if ((l->use & LP_Y) || (l->def & LP_Y))
            break;
        if (l->use == LP_ALL && !lp_line_is(l, "sep #$20") && !lp_line_is(l, "rep #$20"))
            break;

        if (lp_is(l, "lda") && !l->m8 && lp_workspace_word(lo, m) == slot) {
            if (!(memory[j].out & (3u << slot))) {
                if (mul_out)
                    *mul_out = mul_at;

                return j;
            }

            break;
        }

        if ((memory[j].read | memory[j].write) & (3u << slot))
            break;
        if (lp_is(l, "sta") &&
            (lp_operand_is(l, "f:$004206", 9) || (!l->m8 && lp_operand_is(l, "f:$004205", 9))))
            break;
        if (lp_is(l, "sta") &&
            (lp_operand_is(l, "f:$004203", 9) || (!l->m8 && lp_operand_is(l, "f:$004202", 9))))
            mul_at = j;
    }

    return -1;
}

static int lp_y_scratch_mul_safe(const LpUnit *u, int mul_at, int found)
{
    int k, cycles = 0;

    if (mul_at < 0)
        return 1;

    for (k = mul_at + 1; k < found; ++k) {
        const LpLine *l = &u->lines[k];

        if (l->deleted || !l->op)
            continue;

        cycles += lp_line_is(l, "sep #$20") || lp_line_is(l, "rep #$20") ? 3 : 2;
    }

    cycles += 2; /* tya */

    for (k = found + 1; (unsigned)k < u->count && cycles < 8; ++k) {
        const LpLine *l = &u->lines[k];

        if (l->deleted || l->label)
            break;
        if (!l->op) {
            if (!l->length)
                break;

            continue;
        }
        if (lp_operand_is(l, "f:$004216", 9) || lp_operand_is(l, "f:$004217", 9))
            return cycles + 4 >= 8;
        if (l->ends || lp_branch(l) || l->call)
            break;

        cycles += 2;
    }

    return 1;
}

static int lp_y_scratch_straight_ok(const LpLine *l)
{
    if (l->replace || l->label)
        return 0;
    if (!l->op)
        return !l->length ? 0
                          : (l->text[0] == ';' || (l->length == 3 && !strncmp(l->text, ".a8", 3)) ||
                             (l->length == 4 && !strncmp(l->text, ".a16", 4)));
    if (l->x8 || l->call || l->ends || lp_branch(l))
        return 0;
    if ((l->use & LP_Y) || (l->def & LP_Y))
        return 0;
    if (l->use == LP_ALL && !lp_line_is(l, "sep #$20") && !lp_line_is(l, "rep #$20"))
        return 0;

    return 1;
}

/* Straight-line 16-bit workspace spill/reload pairs with Y dead (or wrappable
 * at function entry/exit, or across a run of 2+ pairs) keep temps in Y. */
static int lp_y_scratch_reuse(LpUnit *u, Function *f, size_t at)
{
    unsigned i, entry = 0, back;
    int can_wrap_fn_y, changed = 0, wrapped = 0, wrap_loop = 0;
    LpWorkspaceLive *memory;

    (void)at;

    if (u->indirect || lp_state.is_volatile || lp_state.parser->no_value_reuse ||
        !lp_fixed_workspace(u))
        return 0;

    can_wrap_fn_y = lp_can_wrap_fn_y(u, f, &entry);
    memory = allocate(u->count * sizeof *memory);
    lp_liveness(u);
    lp_workspace_liveness(u, memory, 1);

    if (can_wrap_fn_y) {
        for (i = 0; i < u->count; ++i) {
            const LpLine *sta = &u->lines[i];
            size_t n;
            const char *o = lp_operand(sta, &n);
            int slot;

            if (sta->deleted || sta->replace || sta->m8 || sta->x8 || !lp_is(sta, "sta") ||
                (sta->out & (LP_N | LP_Z)) || !(sta->out & LP_Y))
                continue;

            slot = lp_workspace_word(o, n);

            if (slot < 0 || (slot & 1) || !(memory[i].write & (3u << slot)))
                continue;
            if (lp_y_scratch_match(u, memory, i, slot, NULL) >= 0 && lp_loop(u, i, &back) >= 0) {
                wrap_loop = 1;
                break;
            }
        }

        if (!wrap_loop)
            can_wrap_fn_y = 0;
    }

    for (i = 0; i < u->count; ++i) {
        LpLine *sta = &u->lines[i];
        size_t n;
        const char *o = lp_operand(sta, &n);
        int slot, mul_at = -1, found;

        if (sta->deleted || sta->replace || sta->m8 || sta->x8 || !lp_is(sta, "sta") ||
            (sta->out & (LP_N | LP_Z)))
            continue;

        slot = lp_workspace_word(o, n);

        if (slot < 0 || (slot & 1) || !(memory[i].write & (3u << slot)))
            continue;
        if ((sta->out & LP_Y) && !can_wrap_fn_y)
            continue;

        found = lp_y_scratch_match(u, memory, i, slot, &mul_at);

        if (found < 0 || !lp_y_scratch_mul_safe(u, mul_at, found))
            continue;

        if ((sta->out & LP_Y) && !wrapped) {
            unsigned k;

            if (!can_wrap_fn_y)
                continue;

            lp_insert(&u->lines[entry], "    phy\n");

            for (k = entry; k < u->count; ++k) {
                if (!u->lines[k].deleted &&
                    (lp_is(&u->lines[k], "rts") || lp_is(&u->lines[k], "rtl")))
                    lp_insert(&u->lines[k], "    ply\n");
            }

            wrapped = 1;
        }

        lp_set(sta, "    tay");
        lp_set(&u->lines[found], "    tya");
        changed = 1;
        break;
    }

    if (!changed) {
        for (i = 0; i < u->count; ++i) {
            unsigned stas[16], ldas[16], pairs = 0, j;
            int slot;
            size_t n;
            const char *o;

            if (u->lines[i].deleted || u->lines[i].replace || u->lines[i].m8 || u->lines[i].x8 ||
                !lp_is(&u->lines[i], "sta") || (u->lines[i].live & (LP_N | LP_Z)) ||
                (u->lines[i].out & (LP_N | LP_Z)))
                continue;

            o = lp_operand(&u->lines[i], &n);
            slot = lp_workspace_word(o, n);

            if (slot < 0 || (slot & 1) || !(memory[i].write & (3u << slot)))
                continue;

            j = i;

            while (j < u->count && pairs < 16) {
                const LpLine *cur = &u->lines[j];
                int cur_slot, mul_at = -1, found;
                size_t cn;
                const char *co;

                if (cur->deleted) {
                    ++j;
                    continue;
                }
                if (!lp_y_scratch_straight_ok(cur))
                    break;

                if (lp_is(cur, "sta") && !cur->m8 && !(cur->out & (LP_N | LP_Z))) {
                    co = lp_operand(cur, &cn);
                    cur_slot = lp_workspace_word(co, cn);

                    if (cur_slot >= 0 && !(cur_slot & 1) && (memory[j].write & (3u << cur_slot))) {
                        found = lp_y_scratch_match(u, memory, j, cur_slot, &mul_at);

                        if (found >= 0 && lp_y_scratch_mul_safe(u, mul_at, found)) {
                            stas[pairs] = j;
                            ldas[pairs++] = (unsigned)found;
                            j = (unsigned)found + 1;
                            continue;
                        }
                    }
                }

                ++j;
            }

            if (pairs >= 2) {
                unsigned last = ldas[pairs - 1];
                int free_slot = -1;

                if (!(u->lines[last].out & (LP_N | LP_Z))) {
                    for (int s = 30; s >= 0; s -= 2) {
                        int ok = 1;

                        if ((memory[stas[0]].live | memory[last].out) & (3u << s)) {
                            ok = 0;
                        }

                        for (unsigned k = stas[0]; k <= last && ok; ++k) {
                            if ((memory[k].read | memory[k].write | memory[k].live |
                                 memory[k].out) &
                                (3u << s))
                                ok = 0;
                            else {
                                size_t kn;
                                const char *ko = lp_operand(&u->lines[k], &kn);

                                if (lp_text_words(ko, ko + kn) & (1u << (s / 2)))
                                    ok = 0;
                            }
                        }

                        if (ok) {
                            free_slot = s;
                            break;
                        }
                    }
                }

                if (free_slot >= 0) {
                    lp_set(&u->lines[stas[0]], "    sty z:__arith_lhs+%d\n    tay", free_slot);
                    lp_set(&u->lines[ldas[0]], "    tya");

                    for (unsigned p = 1; p < pairs; ++p) {
                        lp_set(&u->lines[stas[p]], "    tay");
                        lp_set(&u->lines[ldas[p]], "    tya");
                    }

                    lp_set(&u->lines[last], "    tya\n    ldy z:__arith_lhs+%d", free_slot);
                    changed = 1;
                    break;
                }
            }
        }
    }

    free(memory);
    return changed;
}

/* Delay saving an incoming X bound until its positive arm uses it */
static int lp_delay_guarded_x_store(LpUnit *u, Function *f, size_t at)
{
    (void)at;

    if (u->indirect || lp_state.parser->no_value_reuse || !lp_fixed_workspace(u) ||
        body_asm_statements(f->body))
        return 0;

    LpWorkspaceLive *memory = allocate(u->count * sizeof *memory);

    lp_workspace_liveness(u, memory, 0);
    int changed = 0;

    for (unsigned i = 0; i < u->count && !changed; ++i) {
        LpLine *save = &u->lines[i];

        if (!lp_is(save, "stx") || save->x8)
            continue;

        size_t n;
        const char *home = lp_operand(save, &n);
        int offset = lp_workspace_word(home, n);

        if (offset < 0 || (offset & 1))
            continue;

        uint32_t mask = 3u << offset;
        int test = lp_next(u, i, 1);

        if (test >= 0 && lp_is(&u->lines[test], "sta") && memory[test].write &&
            !(memory[test].write & mask))
            test = lp_next(u, (unsigned)test, 1);
        if (test < 0 || !lp_line_is(&u->lines[test], "txa") || u->lines[test].m8)
            continue;

        int zero = lp_next(u, (unsigned)test, 1), after_zero, after_negative;
        int zero_exit = lp_cond_branch_target(u, zero, &after_zero);

        if (zero_exit < 0 || !lp_is(&u->lines[zero], after_zero == zero ? "beq" : "bne") ||
            (after_zero != zero &&
             (u->lines[after_zero].first_incoming != zero || u->lines[zero].next_incoming >= 0)) ||
            (memory[zero_exit].live & mask))
            continue;

        int negative = lp_next(u, (unsigned)after_zero, 1);
        int negative_exit = lp_cond_branch_target(u, negative, &after_negative);

        if (negative_exit < 0 || (unsigned)(after_negative + 1) >= u->count ||
            !lp_is(&u->lines[negative], after_negative == negative ? "bmi" : "bpl") ||
            (after_negative != negative && (u->lines[after_negative].first_incoming != negative ||
                                            u->lines[negative].next_incoming >= 0)) ||
            (memory[negative_exit].live & mask))
            continue;

        char text[64];

        snprintf(text, sizeof text, "    stx %.*s\n", (int)n, home);
        lp_insert(&u->lines[after_negative + 1], text);
        save->deleted = 1;
        changed = 1;
    }

    free(memory);
    return changed;
}

/* Sink a 16-bit workspace store across guard branches when every taken target leaves the slot dead */
static int lp_next_byte_guard(const LpUnit *u, int at)
{
    for (unsigned i = (unsigned)at + 1; i < u->count; ++i) {
        const LpLine *l = &u->lines[i];

        if (l->op)
            return (int)i;
        if (l->text[0] == ';' || lp_fallthrough_label(l) ||
            !strncmp(l->text, ".export __inlined_", 18) ||
            (l->length == 3 && !strncmp(l->text, ".a8", 3)) ||
            (l->length == 4 && !strncmp(l->text, ".a16", 4)))
            continue;

        break;
    }

    return -1;
}

static int lp_byte_index_guard_end(const LpUnit *u, const LpWorkspaceLive *memory, int store,
                                   int index, unsigned mask)
{
    int mode, load, edge, next, join, restore;

    if (index < 0 || u->lines[index].x8 || !lp_line_is(&u->lines[index], "tax"))
        return -1;

    mode = lp_next_byte_guard(u, index);

    if (mode < 0 || !lp_line_is(&u->lines[mode], "sep #$20"))
        return -1;

    load = lp_next_byte_guard(u, mode);

    if (load < 0 || !lp_is(&u->lines[load], "lda") || lp_index_use(&u->lines[load]) != LP_X)
        return -1;

    edge = lp_next_byte_guard(u, load);

    if (edge >= 0 && lp_is(&u->lines[edge], "cmp") && lp_immediate(&u->lines[edge]) >= 0)
        edge = lp_next_byte_guard(u, edge);
    if (edge < 0 || (!lp_is(&u->lines[edge], "beq") && !lp_is(&u->lines[edge], "bne")))
        return -1;

    next = lp_next_byte_guard(u, edge);

    if (next < 0 || !lp_is(&u->lines[next], "lda") || lp_index_use(&u->lines[next]) != LP_X)
        return -1;

    restore = lp_next_byte_guard(u, next);

    if (restore >= 0 && lp_is(&u->lines[restore], "cmp") && lp_immediate(&u->lines[restore]) >= 0) {
        next = restore;
        restore = lp_next_byte_guard(u, next);
    }

    join = u->lines[edge].target;

    if (restore < 0 || !lp_line_is(&u->lines[restore], "rep #$20") || join <= next ||
        join >= restore)
        return -1;

    for (int i = store + 1; i <= restore; ++i) {
        const LpLine *l = &u->lines[i];

        if (memory[i].read & mask)
            return -1;
        if (l->label && l->first_incoming >= 0 &&
            (i != join || l->first_incoming != edge || u->lines[edge].next_incoming >= 0))
            return -1;
    }

    return restore;
}

static int lp_sink_branch_store(LpUnit *u, Function *f, size_t at)
{
    unsigned i;
    LpWorkspaceLive *memory;

    (void)f;
    (void)at;

    if (u->indirect || lp_state.is_volatile || lp_state.parser->no_value_reuse ||
        !lp_fixed_workspace(u))
        return 0;

    memory = allocate(u->count * sizeof *memory);
    lp_liveness(u);
    lp_workspace_liveness(u, memory, 1);

    for (i = 0; i + 3 < u->count; ++i) {
        LpLine *store = &u->lines[i], *cmp, *after;
        size_t n;
        const char *o = lp_operand(store, &n);
        int slot, k1, k2, after1 = -1, t1, fall, guard_end, live_index = 0;

        if (store->deleted || store->replace || store->m8 || store->label || !lp_is(store, "sta"))
            continue;
        if (n < 3 || strncmp(o, "z:", 2))
            continue;

        slot = lp_workspace_word(o, n);

        if (slot < 0 || (slot & 1) || !(memory[i].write & (3u << slot)))
            continue;

        guard_end =
            lp_byte_index_guard_end(u, memory, (int)i, lp_next_byte_guard(u, (int)i), 3u << slot);
        k1 = guard_end >= 0 ? guard_end : lp_next(u, i, 1);

        if (k1 < 0)
            continue;

        cmp = &u->lines[k1];
        int remat_x = 0;

        if (guard_end >= 0) {
            live_index = 1;
        } else if (!cmp->deleted && !cmp->replace && !cmp->label && !cmp->m8 && lp_is(cmp, "asl") &&
                   lp_operand_is(cmp, "a", 1)) {
            int prev = lp_next(u, i, -1);
            int kx = lp_next(u, (unsigned)k1, 1);

            if (prev >= 0 && lp_is(&u->lines[prev], "and") &&
                lp_operand_is(&u->lines[prev], "#$00FF", 6) && kx >= 0 && !u->lines[kx].label &&
                !u->lines[kx].x8 && lp_is(&u->lines[kx], "tax")) {
                int cur = lp_next(u, (unsigned)kx, 1);

                for (int steps = 0; steps < 4 && cur >= 0; ++steps) {
                    LpLine *cl = &u->lines[cur];

                    if (cl->deleted || cl->replace || cl->label || cl->m8 || cl->x8 || cl->call)
                        break;
                    if (memory[cur].read & (3u << slot))
                        break;
                    if (lp_is(cl, "cmp")) {
                        k1 = cur;
                        cmp = cl;
                        remat_x = 1;
                        break;
                    }
                    if (cl->def & LP_X)
                        break;

                    cur = lp_next(u, (unsigned)cur, 1);
                }
            }
        } else if (!cmp->deleted && !cmp->replace && !cmp->label &&
                   (lp_is(cmp, "tax") || lp_is(cmp, "tay"))) {
            int kc = lp_next(u, (unsigned)k1, 1);

            if (kc >= 0 && !u->lines[kc].label && !u->lines[kc].m8 && lp_is(&u->lines[kc], "cmp") &&
                !(memory[kc].read & (3u << slot))) {
                k1 = kc;
                cmp = &u->lines[k1];
            }
        }

        if (cmp->deleted || cmp->replace || cmp->label ||
            (!live_index && (cmp->m8 || !lp_is(cmp, "cmp"))))
            continue;
        if (memory[k1].read & (3u << slot))
            continue;

        k2 = live_index ? lp_next_byte_guard(u, k1) : lp_next(u, (unsigned)k1, 1);

        if (live_index) {
            int j;

            for (j = k1 + 1; j < k2; ++j) {
                if (u->lines[j].label && u->lines[j].first_incoming >= 0)
                    break;
            }

            if (j < k2)
                continue;
        }

        t1 = lp_cond_branch_target(u, k2, &after1);

        if (t1 < 0 || (memory[t1].live & (3u << slot)))
            continue;
        if (live_index && after1 != k2 &&
            (u->lines[after1].first_incoming != k2 || u->lines[k2].next_incoming >= 0))
            continue;

        fall = after1 + 1;
        {
            int k3 = lp_next(u, (unsigned)after1, 1), after2 = -1, t2;

            t2 = lp_cond_branch_target(u, k3, &after2);

            if (t2 >= 0 && !live_index) {
                if (memory[t2].live & (3u << slot))
                    continue;

                fall = after2 + 1;
            }
        }

        if ((unsigned)fall >= u->count)
            continue;

        after = &u->lines[fall];

        if (remat_x && (after->live & (LP_A | LP_N | LP_Z | LP_C)))
            continue;

        {
            char text[160];

            if (remat_x)
                snprintf(text, sizeof text, "    txa\n    lsr a\n    sta %.*s\n", (int)n, o);
            else if (live_index)
                snprintf(text, sizeof text, "; spill tested index on live edge\n    stx %.*s\n",
                         (int)n, o);
            else
                snprintf(text, sizeof text, "    sta %.*s\n", (int)n, o);

            lp_insert(after, text);
        }
        store->deleted = 1;
        free(memory);
        return 1;
    }

    free(memory);
    return 0;
}

static int lp_thread_equal_store(LpUnit *u, Function *f, size_t at)
{
    unsigned i;
    (void)f;
    (void)at;

    if (lp_state.is_volatile || lp_state.parser->no_value_reuse)
        return 0;

    lp_liveness(u);

    for (i = 0; i + 2 < u->count; ++i) {
        LpLine *cmp = &u->lines[i];
        size_t n, sn;
        const char *o, *so;
        int k1, after1 = -1, t, k_sta, k_after;

        unsigned lbl;
        char ltext[64], btext[64];

        if (cmp->deleted || cmp->replace || cmp->label || !lp_is(cmp, "cmp"))
            continue;

        o = lp_operand(cmp, &n);

        if (n < 3 || strncmp(o, "z:", 2))
            continue;

        k1 = lp_next(u, i, 1);

        if (k1 < 0 || u->lines[k1].label || !lp_is(&u->lines[k1], "beq"))
            continue;

        t = lp_cond_branch_target(u, k1, &after1);

        if (t < 0 || after1 != k1)
            continue;

        k_sta = lp_next(u, (unsigned)t, 1);

        if (k_sta < 0 || u->lines[k_sta].deleted || u->lines[k_sta].replace ||
            u->lines[k_sta].label || u->lines[k_sta].m8 != cmp->m8 ||
            !lp_is(&u->lines[k_sta], "sta"))
            continue;

        so = lp_operand(&u->lines[k_sta], &sn);

        if (sn != n || strncmp(so, o, n))
            continue;

        k_after = lp_next(u, (unsigned)k_sta, 1);

        if (k_after < 0 || (u->lines[k_after].live & (LP_N | LP_Z)))
            continue;

        lbl = lp_next_label();
        snprintf(ltext, sizeof ltext, "cg_lp_%u:\n", lbl);
        snprintf(btext, sizeof btext, "    beq cg_lp_%u\n", lbl);
        lp_insert(&u->lines[k_after], ltext);
        lp_insert(&u->lines[k1], btext);
        u->lines[k1].deleted = 1;
        return 1;
    }

    return 0;
}

/* The target exit routine restores S and then transfers to main_exit */
/* A known C result overwrites an unpassed register before any caller use */
static int lp_dead_literal_before_call(LpUnit *u, Function *f, size_t at)
{
    (void)at;

    if (u->indirect || lp_state.parser->no_body_optimizations || lp_state.parser->no_value_reuse ||
        body_asm_statements(f->body))
        return 0;

    int live = 0, changed = 0;

    for (unsigned i = 0; i < u->count; ++i) {
        LpLine *load = &u->lines[i];

        unsigned reg = lp_is(load, "lda") ? LP_A : lp_is(load, "ldx") ? LP_X : 0;

        if (!reg || load->m8 || load->x8 || lp_immediate(load) < 0)
            continue;

        unsigned next = i + 1;

        while (next < u->count && lp_internal_path_marker(u, next, i)) {
            ++next;
        }

        if (next >= u->count)
            continue;

        LpLine *call = &u->lines[next];

        if (!call->call || call->ends || call->use & reg)
            continue;

        Symbol *callee = lp_callee(call);
        Function *body = callee ? inl.by_symbol[callee - lp_state.parser->symbols] : NULL;

        if (!body || body->aggregate_abi || body->uses_wide || callee->interrupt ||
            body_asm_statements(body->body) || !inl_definitely_returns(body->body))
            continue;

        int result = reg_width(callee->type);

        if (result != 4 && (reg == LP_X || result != 2))
            continue;

        if (!live) {
            lp_liveness(u);
            live = 1;
        }

        if (call->out & (LP_N | LP_Z))
            continue;

        load->deleted = 1;
        ++changed;
    }

    return changed;
}

static int lp_jump_to_runtime_exit(LpUnit *u, Function *f, size_t at)
{
    int changed = 0;

    (void)at;

    if (lp_state.parser->no_body_optimizations || u->indirect || body_asm_statements(f->body))
        return 0;

    for (unsigned i = 0; i < u->count; ++i) {
        LpLine *call = &u->lines[i];
        int long_call = lp_is(call, "jsl");

        if ((!long_call && !lp_is(call, "jsr")) || call->m8 || call->x8 ||
            !body_library_exit(lp_callee(call)))
            continue;

        size_t n;
        const char *operand = lp_operand(call, &n);

        lp_set(call, "    %s %.*s", long_call ? "jml" : "jmp", (int)n, operand);
        ++changed;
    }

    return changed;
}

typedef struct {
    int lines[9], join, low, high;
} LpFarStackAdvance;

static int lp_far_advance_offset(const LpLine *line)
{
    size_t n;
    const char *operand = lp_operand(line, &n);

    if (n < 3 || n > 5 || memcmp(operand + n - 2, ",s", 2) || !isdigit((unsigned char)*operand))
        return -1;

    char *end;
    long offset = strtol(operand, &end, 10);

    return end == operand + n - 2 && offset > 0 && offset < 256 ? (int)offset : -1;
}

static int lp_far_stack_advance(const LpUnit *u, int first, LpFarStackAdvance *advance)
{
    advance->lines[0] = first;

    if (!lp_is(&u->lines[first], "lda"))
        return 0;

    for (unsigned i = 1; i < 9; ++i) {
        int next = lp_next(u, (unsigned)advance->lines[i - 1], 1);

        if (next < 0 || u->lines[next].m8 || u->lines[next].x8)
            return 0;

        advance->lines[i] = next;
    }

    int *line = advance->lines;

    if (u->lines[first].m8 || u->lines[first].x8 || !lp_line_is(&u->lines[line[1]], "tax") ||
        !lp_is(&u->lines[line[2]], "lda") || !lp_line_is(&u->lines[line[3]], "inc a") ||
        !lp_is(&u->lines[line[4]], "bne") || !lp_line_is(&u->lines[line[5]], "inx") ||
        !lp_is(&u->lines[line[6]], "cpx") || lp_immediate(&u->lines[line[6]]) != 256 ||
        !lp_is(&u->lines[line[7]], "bne") || !lp_is(&u->lines[line[8]], "ldx") ||
        lp_immediate(&u->lines[line[8]]) != 0)
        return 0;

    int join = u->lines[line[4]].target;

    if (join != line[8] + 1 || u->lines[line[7]].target != join ||
        u->lines[join].first_incoming != line[4] || u->lines[line[4]].next_incoming != line[7] ||
        u->lines[line[7]].next_incoming >= 0)
        return 0;

    advance->high = lp_far_advance_offset(&u->lines[first]);
    advance->low = lp_far_advance_offset(&u->lines[line[2]]);
    advance->join = join;
    return advance->low > 0 && advance->high == advance->low + 2;
}

/* An advanced far pointer is already in X:A before its bound comparison.
 * Save its low word in the dead cursor register for the selected return. */
static int lp_far_advance_return(LpUnit *u, Function *f, size_t at)
{
    (void)at;

    if (u->indirect || !far_pointer(f->symbol->type) || lp_state.is_volatile ||
        lp_state.parser->no_value_reuse || body_asm_statements(f->body))
        return 0;

    lp_liveness(u);

    for (unsigned i = 0; i < u->count; ++i) {
        LpFarStackAdvance before, after;

        if (!lp_far_stack_advance(u, (int)i, &before) || (u->lines[before.join].live & LP_Y))
            continue;

        int clear = lp_next(u, (unsigned)before.join, 1),
            low = clear < 0 ? -1 : lp_next(u, (unsigned)clear, 1);
        int copy = low < 0 ? -1 : lp_next(u, (unsigned)low, 1),
            high = copy < 0 ? -1 : lp_next(u, (unsigned)copy, 1);
        int test = high < 0 ? -1 : lp_next(u, (unsigned)high, 1), fallthrough = -1;

        if (test < 0 || !lp_line_is(&u->lines[clear], "clc") || !lp_is(&u->lines[low], "sbc") ||
            !lp_line_is(&u->lines[copy], "txa") || !lp_is(&u->lines[high], "sbc") ||
            lp_far_advance_offset(&u->lines[low]) < 0 ||
            lp_far_advance_offset(&u->lines[high]) < 0 ||
            lp_cond_branch_target(u, test, &fallthrough) < 0 ||
            !lp_is(&u->lines[test], fallthrough == test ? "bcs" : "bcc"))
            continue;

        unsigned next = (unsigned)fallthrough + 1;

        while (next < u->count && lp_internal_path_marker(u, next, (unsigned)fallthrough)) {
            ++next;
        }

        if (next >= u->count || !lp_far_stack_advance(u, (int)next, &after) ||
            after.low != before.low || after.high != before.high)
            continue;

        int tail = lp_next(u, (unsigned)after.join, 1);

        if (tail < 0 || !lp_is(&u->lines[tail], "jmp") || u->lines[tail].target < 0)
            continue;

        LpLine *target = &u->lines[u->lines[tail].target];

        if (strncmp(target->text, "return_", 7) || (target->live & (LP_Y | LP_FLAGS)))
            continue;

        lp_insert(&u->lines[clear], "    tay\n");
        lp_set(&u->lines[next], "    tya");

        for (unsigned k = 1; k < 9; ++k) {
            u->lines[after.lines[k]].deleted = 1;
        }

        return 1;
    }

    return 0;
}

/* Both runtime termination paths reset S. An earlier stack adjustment
 * is redundant if every subsequent path reaches one without using S. */
static int lp_stack_cleanup_before_exit(LpUnit *u, Function *f, size_t at)
{
    (void)at;

    if (u->indirect || lp_state.parser->no_stack_frames || body_asm_statements(f->body))
        return 0;

    int changed = 0;
    unsigned char *resets = NULL;

    for (unsigned i = 0; i < u->count; ++i) {
        LpLine *stack = &u->lines[i];

        if (!lp_line_is(stack, "tsc") || stack->m8 || stack->x8)
            continue;

        int carry = lp_next(u, i, 1), adjust = carry < 0 ? -1 : lp_next(u, (unsigned)carry, 1);
        int commit = adjust < 0 ? -1 : lp_next(u, (unsigned)adjust, 1);

        if (commit < 0 || !lp_line_is(&u->lines[carry], "clc") ||
            !lp_is(&u->lines[adjust], "adc") || lp_immediate(&u->lines[adjust]) <= 0 ||
            !lp_line_is(&u->lines[commit], "tcs"))
            continue;

        if (!resets) {
            resets = allocate(u->count + 1);

            for (unsigned j = u->count; j-- > i;) {
                LpLine *line = &u->lines[j];

                if (!line->op) {
                    resets[j] = resets[j + 1];
                    continue;
                }

                Symbol *callee = line->call ? lp_callee(line) : NULL;

                if (callee) {
                    Expr call = {.kind = EX_CALL,
                                 .symbol = callee,
                                 .arg_count = (unsigned)callee->param_count};

                    if (body_termination_call(&call))
                        resets[j] = 1;

                    continue;
                }

                if (lp_stack_op(line) || lp_is(line, "tsc") || lp_is(line, "tsx") ||
                    line->use == LP_ALL)
                    continue;

                size_t n;
                const char *operand = lp_operand(line, &n);
                int stack_operand = 0;

                for (size_t k = 1; k < n; ++k) {
                    if (operand[k - 1] == ',' && operand[k] == 's')
                        stack_operand = 1;
                }

                if (stack_operand || ((line->ends || lp_branch(line)) && line->target < 0))
                    continue;

                int taken = line->target < 0 || (line->target > (int)j && resets[line->target]);

                resets[j] = (unsigned char)(taken && (line->ends || resets[j + 1]));
            }

            lp_liveness(u);
        }

        if (!resets[commit + 1] || (u->lines[commit].out & (LP_A | LP_FLAGS)))
            continue;

        stack->deleted = u->lines[carry].deleted = u->lines[adjust].deleted =
            u->lines[commit].deleted = 1;
        changed = 1;
        break;
    }

    free(resets);
    return changed;
}

/* A private slot cannot be read after the runtime discards this frame */
static int lp_dead_exit_frame_store(LpUnit *u, Function *f, size_t at)
{
    (void)at;

    if (lp_state.parser->no_private_regions || lp_state.is_volatile || u->indirect || !f->slots ||
        body_asm_statements(f->body))
        return 0;

    for (unsigned i = 0; i < (f->slots + 1) / 2 && i < 384; ++i) {
        if (lp_state.frame_map[i])
            return 0;
    }

    PrState *frames = NULL;
    int changed = 0;

    for (unsigned i = 0; i < u->count; ++i) {
        LpLine *exit = &u->lines[i];

        if ((!lp_is(exit, "jmp") && !lp_is(exit, "jml")) || !body_library_exit(lp_callee(exit)))
            continue;

        for (unsigned j = i; j-- > 0;) {
            LpLine *line = &u->lines[j];

            if (!line->op || lp_line_is(line, "rep #$20") || lp_line_is(line, "sep #$20") ||
                ((lp_is(line, "lda") || lp_is(line, "ldx")) && lp_immediate(line) >= 0))
                continue;
            if (!lp_is(line, "sta") && !lp_is(line, "stz"))
                break;

            size_t n;
            const char *p = lp_operand(line, &n);

            if (n != 9 || strncmp(p, "a:$", 3) || memcmp(p + 7, ",y", 2) || line->x8)
                break;

            char *end;

            unsigned slot = (unsigned)strtoul(p + 3, &end, 16);
            unsigned bytes = (unsigned)lp_width(line);

            if (end != p + 7 || !slot || slot + bytes - 1 > f->slots)
                break;
            if (!frames)
                frames = pr_states(u);
            if (!frames[j].frame)
                break;

            for (unsigned k = 0; k < lp_state.parser->symbol_count; ++k) {
                Symbol *v = &lp_state.parser->symbols[k];

                if (v->owner != f->id || !v->offset || !v->scope || v->storage ||
                    slot < v->offset || object_volatile(v->type))
                    continue;

                unsigned char read[512] = {0};

                unsigned size = width(v->type);

                if (slot - v->offset + bytes > size || size > sizeof read)
                    continue;
                if (v->type.array ? object_volatile(array_element(v->type)) ||
                                        !body_unread_fixed_stores(f->body, v, read, 0)
                                  : structure_object(v->type) || !loop_private(v))
                    break;

                line->deleted = 1;
                changed = 1;
                break;
            }

            break;
        }

        if (changed)
            break;
    }

    free(frames);
    return changed;
}

/* A frame used only for one outgoing local address need not hold Y.
 * The stack reservations and pushed arguments keep their relative layout. */
static int lp_address_only_frame(LpUnit *u, Function *f, size_t at)
{
    (void)at;

    if (!f->slots || u->calls != 1 || u->indirect || lp_state.parser->no_stack_frames ||
        f->uses_varargs || f->aggregate_abi || body_asm_statements(f->body))
        return 0;

    LpLine *ops[48];

    unsigned count = 0;

    for (unsigned i = 0; i < u->count; ++i) {
        LpLine *l = &u->lines[i];

        if (!l->op)
            continue;
        if (count == sizeof ops / sizeof *ops || l->m8 || l->x8 || lp_branch(l) || l->target >= 0)
            return 0;

        ops[count++] = l;
    }

    if (count < 9 || !lp_is(ops[0], "phy"))
        return 0;

    unsigned i = 1, frame = 0;

    while (i < count && lp_is(ops[i], "pha")) {
        ++i;
        ++frame;
    }

    if (!frame || i + 3 >= count || !lp_is(ops[i++], "tsc") || !lp_is(ops[i], "tay"))
        return 0;

    LpLine *save = ops[i++];

    unsigned outgoing = 0;

    while (i < count && lp_is(ops[i], "pea")) {
        ++i;
        ++outgoing;
    }

    if (!outgoing || i >= count || !lp_is(ops[i], "tyx"))
        return 0;

    LpLine *address = ops[i++];

    unsigned offset = 0;

    while (i < count && lp_is(ops[i], "inx")) {
        ++i;
        ++offset;
    }

    if (!offset || offset > 2 * frame || i >= count || !ops[i]->call || ops[i]->ends ||
        (ops[i]->use & LP_A) || !(ops[i]->use & LP_X))
        return 0;

    unsigned pops = 0;
    int result = 0;

    for (++i; i < count; ++i) {
        if (lp_is(ops[i], "plx")) {
            ++pops;
            continue;
        }
        if (!result && lp_is(ops[i], "lda") && lp_immediate(ops[i]) >= 0) {
            result = 1;
            continue;
        }

        break;
    }

    if (pops != frame + outgoing || i + 2 != count || !lp_is(ops[i], "ply") ||
        (!lp_is(ops[i + 1], "rts") && !lp_is(ops[i + 1], "rtl")))
        return 0;

    ops[0]->deleted = save->deleted = ops[i]->deleted = 1;
    lp_set(address, "    tax");
    return 1;
}

/* Two adjacent stack words can share storage across a linear handoff. Read
 * the dying top word into X, then reuse its slot for the new A value. */
static int lp_reuse_stack_word(LpUnit *u, Function *f, size_t at)
{
    (void)at;

    if (lp_state.parser->no_stack_frames || lp_state.parser->no_private_regions || u->indirect ||
        u->calls < 2 || f->symbol->interrupt || f->uses_varargs || frame_address_visible(f->body) ||
        body_asm_statements(f->body))
        return 0;

    lp_liveness(u);

    for (unsigned i = 0; i < u->count; ++i) {
        LpLine *reserve = &u->lines[i];
        int save, put = -1, get = -1, release = -1;

        unsigned accesses = 0, calls = 0;

        if (!lp_line_is(reserve, "pha") || reserve->m8 || reserve->x8)
            continue;

        save = lp_next(u, i, 1);

        if (save < 0 || !lp_line_is(&u->lines[save], "phx") || u->lines[save].x8)
            continue;

        for (unsigned j = i + 1; j < u->count; ++j) {
            LpLine *l = &u->lines[j];
            size_t length;
            const char *operand = lp_operand(l, &length);

            if (l->label && l->first_incoming >= 0)
                break;
            if (!l->op || j == (unsigned)save)
                continue;
            if (l->m8 || l->x8 || lp_branch(l) || l->ends || l->use == LP_ALL || lp_is(l, "tsc") ||
                lp_is(l, "tsx") || lp_is(l, "tcs") || lp_is(l, "txs"))
                break;

            if (put < 0 && lp_line_is(l, "sta 3,s")) {
                put = (int)j;
                get = lp_next(u, j, 1);

                if (get < 0 || !lp_line_is(&u->lines[get], "lda 1,s") ||
                    (u->lines[get].out & LP_X) || !calls)
                    break;

                continue;
            }

            if ((int)j == get)
                continue;

            if (lp_operand_has_s(operand, length)) {
                if (put < 0 || !lp_operand_is(l, "3,s", 3) || !lp_accumulator_memory(l))
                    break;

                ++accesses;
            }

            if (l->call) {
                Symbol *callee = lp_callee(l);

                unsigned args;

                if (!callee || callee->variadic || callee->param_count < 0 ||
                    structure_object(callee->type))
                    break;

                for (args = 0; args < (unsigned)callee->param_count &&
                               register_parameter(args, callee->params[args]);
                     ++args) {
                }

                if (args != (unsigned)callee->param_count)
                    break;

                ++calls;
                continue;
            }

            if (lp_stack_op(l)) {
                int second = lp_next(u, j, 1);
                int ret = second >= 0 ? lp_next(u, (unsigned)second, 1) : -1;

                if (put >= 0 && accesses && calls >= 2 && lp_line_is(l, "plx") && ret >= 0 &&
                    lp_line_is(&u->lines[second], "plx") && !u->lines[second].x8 &&
                    (lp_is(&u->lines[ret], "rts") || lp_is(&u->lines[ret], "rtl")))
                    release = (int)j;

                break;
            }
        }

        if (release < 0)
            continue;

        reserve->deleted = 1;
        lp_set(&u->lines[put], "    plx\n    pha");
        lp_set(&u->lines[get], "    txa");

        for (int j = get + 1; j < release; ++j) {
            if (lp_operand_is(&u->lines[j], "3,s", 3))
                lp_set(&u->lines[j], "    %.3s 1,s", u->lines[j].op);
        }

        u->lines[release].deleted = 1;
        lp_insert(&u->lines[save], "; reuse a stack word across calls\n");
        return 1;
    }

    return 0;
}

/* Retain an unescaped near cursor in a free caller-clobbered DP word.
 * No value of the cursor may be live across a call. */
static int lp_home_private_cursor(LpUnit *u, Function *f, size_t at)
{
    (void)at;

    if (!f->slots || u->indirect || lp_state.parser->no_dp_homes ||
        lp_state.parser->no_direct_dpage || lp_state.parser->no_private_regions ||
        !lp_fixed_workspace(u) || body_asm_statements(f->body))
        return 0;

    for (unsigned i = 0; i < (f->slots + 1) / 2 && i < 384; ++i) {
        if (lp_state.frame_map[i] && lp_state.frame_map[i] != 2 * i + 1)
            return 0;
    }

    uint32_t used = 0;

    for (unsigned i = 0; i < u->count; ++i) {
        LpLine *l = &u->lines[i];
        size_t n;
        const char *operand = lp_operand(l, &n);

        if (lp_operand_has_s(operand, n) || (l->op && !l->call && l->use == LP_ALL))
            return 0;

        int exact;
        uint32_t bytes = lp_workspace_access(l, &exact);

        if (exact)
            used |= bytes;
    }

    /* Named workspace references can also feed indirect operands.
     * Indexed C object addresses cannot designate compiler-owned scratch. */
    unsigned words = lp_text_words(u->text, u->text + strlen(u->text));

    for (unsigned i = 0; i < 16; ++i) {
        if (words & (1u << i))
            used |= 3u << (2 * i);
    }

    unsigned word = 0;

    while (word < 32 && (used & (3u << word))) {
        word += 2;
    }

    if (word >= 32)
        return 0;

    PrState *frames = NULL;
    unsigned char *access = NULL, *live = NULL;
    int changed = 0;

    for (unsigned i = 0; i < lp_state.parser->symbol_count && !changed; ++i) {
        Symbol *v = &lp_state.parser->symbols[i];

        if (v->owner != f->id || !v->offset || !v->type.pointers || !body_private(v) ||
            value_width(v->type) != 2 || v->offset + 1 > f->slots)
            continue;

        int slot = (int)v->offset, valid = 1, loop_use = 0;

        unsigned count = 0;

        if (!frames) {
            frames = pr_states(u);
            access = allocate(u->count * 2);
            live = access + u->count;
        } else
            memset(access, 0, u->count * 2);

        for (unsigned j = 0; j < u->count; ++j) {
            LpLine *l = &u->lines[j];
            int off = lp_frame_indexed_offset(l, 'y');

            if (off < 0)
                continue;
            if (!frames[j].frame) {
                valid = 0;
                break;
            }
            if (!lp_overlaps(l, off, slot))
                continue;
            if (off != slot || l->m8 || (!lp_is(l, "lda") && !lp_is(l, "sta"))) {
                valid = 0;
                break;
            }

            access[j] = (unsigned char)(lp_is(l, "lda") ? 1 : 2);
            unsigned back;

            if (!loop_use && lp_loop(u, j, &back) >= 0)
                loop_use = 1;

            ++count;
        }

        if (!valid || !loop_use || count < 3)
            continue;

        int again = 1;

        while (again) {
            again = 0;

            for (unsigned j = u->count; j-- > 0;) {
                LpLine *l = &u->lines[j];
                int out = (!l->ends && j + 1 < u->count && live[j + 1]) ||
                          (l->target >= 0 && live[l->target]);
                unsigned char in = (unsigned char)(access[j] == 1 || (out && access[j] != 2));

                if (live[j] != in) {
                    live[j] = in;
                    again = 1;
                }
            }
        }

        for (unsigned j = 0; j < u->count && valid; ++j) {
            if (u->lines[j].call && live[j])
                valid = 0;
        }

        if (!valid)
            continue;

        for (unsigned j = 0; j < u->count; ++j) {
            if (access[j])
                lp_set(&u->lines[j], "    %.3s z:__arith_lhs+%u", u->lines[j].op, word);
        }

        lp_mark_arithmetic();
        changed = 1;
    }

    free(frames);
    free(access);
    return changed;
}

/* A leaf can move its mutable far stack argument into two free DP
 * words. A loop with two cursor bases avoids rebasing D for each test. */
static int lp_home_far_stack_argument(LpUnit *u, Function *f, size_t at)
{
    (void)at;

    if (u->calls || u->indirect || lp_state.is_volatile || lp_state.frame_address ||
        f->uses_varargs || lp_state.parser->no_dp_homes || lp_state.parser->no_direct_dpage ||
        lp_state.parser->no_private_regions || body_asm_statements(f->body))
        return 0;

    unsigned entry = 0;

    while (entry < u->count && !u->lines[entry].op) {
        ++entry;
    }

    if (entry == u->count || u->lines[entry].m8 || u->lines[entry].x8)
        return 0;

    lp_liveness(u);

    if (u->lines[entry].live & (LP_A | LP_N | LP_Z))
        return 0;

    int *depth = allocate(u->count * sizeof *depth);
    unsigned char *mark = allocate(u->count);

    if (!lp_stack_depths(u, entry, depth)) {
        free(mark);
        free(depth);
        return 0;
    }

    int home = -1, valid = 1, loop = 0, second_cursor = 0;

    unsigned touched = 0;

    for (unsigned i = entry; i < u->count; ++i) {
        if (!lp_line_is(&u->lines[i], "phd"))
            continue;
        if (lp_far_stack_byte_test(u, (int)i) < 0) {
            valid = 0;
            break;
        }

        int stack = lp_next_mode(u, i), page = lp_next_mode(u, (unsigned)stack);
        int mode = lp_next_mode(u, (unsigned)page), load = lp_next_mode(u, (unsigned)mode);
        int restore = lp_next_mode(u, (unsigned)load);
        size_t n;
        const char *operand = lp_operand(&u->lines[load], &n);
        int base = (int)strtol(operand + 2, NULL, 16) - depth[load];

        if (depth[load] < 0 || base < 3 || base > 253 || (home >= 0 && home != base) ||
            (u->lines[restore].out & (LP_AH | LP_N | LP_Z))) {
            valid = 0;
            break;
        }

        home = base;
        mark[i] = mark[stack] = mark[page] = mark[restore] = 1;
        mark[load] = 2;
        unsigned back;

        if (!loop && lp_loop(u, i, &back) >= 0)
            loop = 1;
    }

    uint32_t used = 0;

    for (unsigned i = entry; i < u->count && valid && home >= 0 && loop; ++i) {
        LpLine *l = &u->lines[i];

        if (!l->op || mark[i])
            continue;
        if (lp_is(l, "tcd") || lp_is(l, "pld") || lp_is(l, "plb") || lp_is(l, "xce") ||
            l->use == LP_ALL || (lp_is(l, "rtl") && home < 4)) {
            valid = 0;
            break;
        }

        size_t n;
        const char *p = lp_operand(l, &n);

        if (lp_operand_has_s(p, n)) {
            char *end;
            long s = strtol(p, &end, 10);

            if (n < 3 || end != p + n - 2 || p[n - 2] != ',' || p[n - 1] != 's' || depth[i] < 0 ||
                s < 0 || s > 255) {
                valid = 0;
                break;
            }

            int off = (int)s - depth[i];

            if (!lp_overlaps_n(l, off, home, 4))
                continue;
            if ((off != home && off != home + 2) || l->m8 || !lp_accumulator_memory(l)) {
                valid = 0;
                break;
            }

            mark[i] = (unsigned char)(3 + (off - home) / 2);
            ++touched;
        } else {
            int exact;
            uint32_t bytes = lp_workspace_access(l, &exact);

            if (exact)
                used |= bytes;
            if (n > 2 && p[0] == '[' && lp_text_words(p, p + n))
                second_cursor = 1;
        }
    }

    int changed = 0;

    if (valid && home >= 0 && loop && second_cursor && touched >= 5) {
        unsigned words = lp_text_words(u->text, u->text + strlen(u->text));

        for (unsigned i = 0; i < 16; ++i) {
            if (words & (1u << i))
                used |= 3u << (2 * i);
        }

        unsigned word = 0;

        while (word <= 28 && (used & (15u << word))) {
            word += 2;
        }

        if (word <= 28) {
            char setup[120];

            snprintf(
                setup, sizeof setup,
                "    lda %d,s\n    sta z:__arith_lhs+%u\n    lda %d,s\n    sta z:__arith_lhs+%u\n",
                home, word, home + 2, word + 2);
            lp_insert(&u->lines[entry], setup);

            for (unsigned i = entry; i < u->count; ++i) {
                LpLine *l = &u->lines[i];

                if (mark[i] == 1)
                    l->deleted = 1;
                else if (mark[i] == 2)
                    lp_set(l, "    lda [__arith_lhs+%u]", word);
                else if (mark[i] >= 3)
                    lp_set(l, "    %.3s z:__arith_lhs+%u", l->op, word + 2 * (mark[i] - 3));
            }

            lp_mark_arithmetic();
            changed = 1;
        }
    }

    free(mark);
    free(depth);
    return changed;
}

/* A word read from direct page can go straight into its index register */
static int lp_load_index_from_workspace(LpUnit *u, Function *f, size_t at)
{
    (void)f;
    (void)at;
    lp_liveness(u);
    int changed = 0;

    for (unsigned i = 0; i < u->count; ++i) {
        LpLine *load = &u->lines[i];

        if (!lp_is(load, "lda") || load->m8 || load->x8)
            continue;

        size_t n;
        const char *p = lp_operand(load, &n);

        if (lp_workspace_word(p, n) < 0)
            continue;

        int next = lp_next(u, i, 1);

        if (next < 0)
            continue;

        LpLine *move = &u->lines[next];
        int x = lp_line_is(move, "tax");

        if ((!x && !lp_line_is(move, "tay")) || (move->out & LP_A))
            continue;

        lp_set(load, "    %s %.*s", x ? "ldx" : "ldy", (int)n, p);
        move->deleted = 1;
        changed = 1;
    }

    return changed;
}
