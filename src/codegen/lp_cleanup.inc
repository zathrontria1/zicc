// Fixed-point cleanup loop, private-value passes, frame promotion, and carry tracking

static Symbol *lp_callee(const LpLine *call);

typedef struct {
    unsigned char seen, frame, count, stack[64];
} PrState;

static PrState *pr_states(LpUnit *u);
#include "private_values.inc"
#include "private_regions.inc"
#include "accumulator_cfg.inc"

/* Propagate a later low-bit demand through modular immediate arithmetic.
 * Control flow, memory observations and live arithmetic flags are barriers. */
typedef struct {
    char name[64];
    unsigned zero, ones;
} LpKnownSlot;

static void lp_known_invalidate(LpKnownSlot *slots, unsigned *nslots, const LpLine *l)
{
    unsigned k = 0;

    while (k < *nslots) {
        size_t len = strlen(slots[k].name);

        if (lp_may_write(l, slots[k].name, len, 2) ||
            (slots[k].name[len - 1] == 'y' && (l->def & LP_Y)) ||
            (slots[k].name[len - 1] == 's' && lp_stack_op(l)))
            slots[k] = slots[--*nslots];
        else
            ++k;
    }
}

static void lp_known_record(LpKnownSlot *slots, unsigned *nslots, const LpLine *l, unsigned zero,
                            unsigned ones)
{
    size_t n;
    const char *o = lp_operand(l, &n);

    lp_known_invalidate(slots, nslots, l);

    if (n >= sizeof slots[0].name || !lp_private(o, n) || *nslots >= 16)
        return;

    LpKnownSlot *slot = &slots[(*nslots)++];

    memcpy(slot->name, o, n);
    slot->name[n] = 0;
    slot->zero = zero;
    slot->ones = ones;
}

/* Eliminate redundant bit masks via backward demand and forward known-zero tracking */
static int lp_bits_dead_after(LpUnit *u, unsigned start, unsigned bits, int low_ok,
                              const unsigned char *targets, int known_targets)
{
    int k = (int)start;

    while ((unsigned)++k < u->count) {
        LpLine *p = &u->lines[k];
        long n;

        if (p->deleted)
            continue;
        if (p->replace)
            break;

        if (!p->op) {
            if (!p->length)
                break;
            if (p->text[0] == ';' || (p->length == 3 && !strncmp(p->text, ".a8", 3)) ||
                (p->length == 4 && !strncmp(p->text, ".a16", 4)) ||
                (known_targets && !targets[k] && lp_fallthrough_label(p)))
                continue;

            break;
        }

        if (!p->x8 && !(p->def & LP_A) && !(p->use & LP_A) &&
            (lp_is(p, "ldx") || lp_is(p, "ldy") || lp_line_is(p, "plx") || lp_line_is(p, "ply")))
            continue;

        if (p->m8) {
            if (!(bits & 0x00FFu) &&
                (lp_is(p, "sta") || lp_is(p, "cmp") || lp_is(p, "bit") || lp_is(p, "and") ||
                 lp_is(p, "ora") || lp_is(p, "eor") || lp_is(p, "adc") || lp_is(p, "sbc") ||
                 lp_line_is(p, "inc a") || lp_line_is(p, "dec a") || lp_line_is(p, "asl a") ||
                 lp_line_is(p, "lsr a") || lp_line_is(p, "rol a") || lp_line_is(p, "ror a"))) {
                if (!(p->out & LP_A))
                    return 1;

                continue;
            }

            break;
        }

        if (lp_line_is(p, "sep #$20") || lp_line_is(p, "rep #$20") || lp_line_is(p, "clc") ||
            lp_line_is(p, "sec"))
            continue;

        if (lp_is(p, "and") && (n = lp_immediate(p)) >= 0) {
            bits &= (unsigned)n;

            if (!bits)
                return 1;
            if (p->out & (LP_N | LP_Z))
                break;
        } else if (lp_is(p, "ora") && (n = lp_immediate(p)) >= 0 && !(p->out & (LP_N | LP_Z))) {
            bits &= ~(unsigned)n;

            if (!bits)
                return 1;
        } else if (lp_is(p, "eor") && lp_immediate(p) >= 0 && !(p->out & (LP_N | LP_Z))) {
        } else if (lp_line_is(p, "xba") && !(p->out & (LP_N | LP_Z))) {
            bits = ((bits >> 8) | (bits << 8)) & 0xFFFFu;
            low_ok = 0;
        } else if (lp_line_is(p, "asl a") && !(p->out & (LP_C | LP_N | LP_Z))) {
            bits = (bits << 1) & 0xFFFFu;
            low_ok = 0;

            if (!bits)
                return 1;
        } else if (lp_line_is(p, "lsr a") && !(p->out & (LP_C | LP_N | LP_Z))) {
            bits = (bits >> 1) & 0xFFFFu;
            low_ok = 0;

            if (!bits)
                return 1;
        } else if (low_ok && (lp_is(p, "adc") || lp_is(p, "sbc")) && lp_immediate(p) >= 0 &&
                   !(p->out & LP_FLAGS)) {
        } else
            break;
    }

    return 0;
}

/* If A is copied to an index, both consumers must discard every bit the
 * original mask cleared. Reject any other observation of the saved index. */
static int lp_masked_index_copy(LpUnit *u, unsigned transfer, unsigned bits, int low_ok,
                                const unsigned char *targets, int known_targets)
{
    LpLine *copy = &u->lines[transfer];
    int x = lp_line_is(copy, "tax");

    unsigned reg = x ? LP_X : LP_Y;

    if ((!x && !lp_line_is(copy, "tay")) || copy->m8 || copy->x8 || (copy->out & (LP_N | LP_Z)) ||
        !lp_bits_dead_after(u, transfer, bits, low_ok, targets, known_targets))
        return 0;

    for (int k = (int)transfer; (k = lp_next(u, (unsigned)k, 1)) >= 0;) {
        LpLine *l = &u->lines[k];

        if (l->m8 || l->x8 || l->ends || l->call || lp_branch(l) || l->replace || l->deleted)
            return 0;
        if (lp_line_is(l, x ? "txa" : "tya"))
            return !(l->out & (reg | LP_Z | LP_N)) &&
                   lp_bits_dead_after(u, (unsigned)k, bits, low_ok, targets, known_targets);
        if ((l->use | l->def) & reg)
            return 0;
    }

    return 0;
}

/* Only the negative half of a masked value needs high sign bits */
static int lp_sign_extension_branch(LpUnit *u, Function *f, size_t at)
{
    (void)at;

    if (body_asm_statements(f->body))
        return 0;

    lp_liveness(u);

    for (unsigned i = 0; i < u->count; ++i) {
        LpLine *mask = &u->lines[i];

        if (!lp_is(mask, "and") || mask->m8)
            continue;

        long bits = lp_immediate(mask);

        if (bits < 3 || bits >= 32768 || (bits & (bits + 1)))
            continue;

        int bias = lp_next(u, i, 1);
        int carry = bias < 0 ? -1 : lp_next(u, (unsigned)bias, 1);
        int sub = carry < 0 ? -1 : lp_next(u, (unsigned)carry, 1);
        long sign = (bits + 1) / 2;

        if (sub < 0 || !lp_is(&u->lines[bias], "eor") || lp_immediate(&u->lines[bias]) != sign ||
            !lp_line_is(&u->lines[carry], "sec") || !lp_is(&u->lines[sub], "sbc") ||
            lp_immediate(&u->lines[sub]) != sign || u->lines[sub].out & LP_FLAGS)
            continue;

        unsigned label = lp_next_label();
        lp_set(&u->lines[bias], "    cmp #$%04lX\n    bcc cg_%s_%u", sign, lp_state.parser->unit,
               label);
        u->lines[carry].deleted = 1;
        lp_set(&u->lines[sub], "    ora #$%04lX\ncg_%s_%u = *", 65535 - bits, lp_state.parser->unit,
               label);
        return 1;
    }

    return 0;
}

static int lp_demanded_masks(LpUnit *u, Function *f, size_t at)
{
    unsigned i, zero_a = 0, ones_a = 0, nslots = 0;
    int changed = 0, known = 0, known_targets;
    int private_stack = !lp_state.frame_address && !u->indirect && !body_asm_statements(f->body);
    LpKnownSlot slots[16];
    unsigned char *targets = lp_local_targets(u, &known_targets);

    (void)at;

    lp_liveness(u);

    for (i = 0; i < u->count; ++i) {
        LpLine *l = &u->lines[i];
        long mask;
        int k;

        if (l->deleted || l->replace)
            continue;

        /* A byte load already sets Z from exactly the bits in a later
         * word mask. REP changes M without disturbing that result. */
        if (i >= 3 && !l->m8 && lp_is(l, "and") && lp_immediate(l) == 255 &&
            !(l->out & (LP_AH | LP_N)) && u->lines[i - 1].length == 4 &&
            !strncmp(u->lines[i - 1].text, ".a16", 4) && lp_line_is(&u->lines[i - 2], "rep #$20")) {
            int load = lp_next(u, i - 2, -1);

            if (load >= 0 && u->lines[load].m8 && lp_is(&u->lines[load], "lda")) {
                l->deleted = 1;
                ++changed;
                continue;
            }
        }

        if (lp_is(l, "ora") && lp_immediate(l) == 0 && !(l->out & (LP_N | LP_Z))) {
            l->deleted = 1;
            ++changed;
            continue;
        }

        if (lp_is(l, "eor") && !l->m8 && (mask = lp_immediate(l)) > 0 && (mask & 0x00FF) == 0) {
            int k1 = lp_next(u, i, 1), k2 = k1 < 0 ? -1 : lp_next(u, (unsigned)k1, 1);

            if (k2 >= 0 && !u->lines[k1].label && !u->lines[k2].label && !u->lines[k1].replace &&
                !u->lines[k2].replace && lp_line_is(&u->lines[k1], "sec") &&
                lp_is(&u->lines[k2], "sbc") && !u->lines[k2].m8 &&
                lp_immediate(&u->lines[k2]) == mask && !(u->lines[k2].out & LP_FLAGS)) {
                unsigned low = (unsigned)mask & (0u - (unsigned)mask);
                unsigned bits = (~(low - 1u)) & 0xFFFFu;

                if (lp_bits_dead_after(u, (unsigned)k2, bits, 1, targets, known_targets)) {
                    l->deleted = u->lines[k1].deleted = u->lines[k2].deleted = 1;
                    ++changed;
                    continue;
                }
            }
        }

        if (!lp_is(l, "and") || l->m8 || (mask = lp_immediate(l)) < 0 || l->out & (LP_N | LP_Z))
            continue;

        k = lp_next(u, i, 1);

        if (k >= 0 && !u->lines[k].m8 && !u->lines[k].deleted && !u->lines[k].replace &&
            lp_is(&u->lines[k], "and") && lp_immediate(&u->lines[k]) >= 0) {
            long m2 = lp_immediate(&u->lines[k]);

            lp_set(&u->lines[k], "    and #$%04lX", (unsigned)(mask & m2) & 0xFFFFu);
            l->deleted = 1;
            ++changed;
            continue;
        }

        {
            unsigned bits = (~(unsigned)mask) & 0xFFFFu;
            int low_ok = !(mask & (mask + 1));

            if (lp_bits_dead_after(u, i, bits, low_ok, targets, known_targets) ||
                (k >= 0 &&
                 lp_masked_index_copy(u, (unsigned)k, bits, low_ok, targets, known_targets))) {
                l->deleted = 1;
                ++changed;
            }
        }
    }

    if (changed) {
        free(targets);
        return changed;
    }

    /* Forward pass: drop AND #imm that only clears already-zero bits */
    int saved_target = -1;
    unsigned saved_zero = 0, saved_ones = 0;

    for (i = 0; i < u->count; ++i) {
        LpLine *l = &u->lines[i];
        size_t n;
        const char *o = lp_operand(l, &n);
        long imm;

        if (l->deleted || l->replace)
            continue;

        if ((int)i == saved_target) {
            known = 1;
            zero_a = saved_zero;
            ones_a = saved_ones;
            nslots = 0;
            saved_target = -1;
            continue;
        }

        if (!l->op) {
            int fallthrough =
                known_targets && !targets[i] &&
                (lp_fallthrough_label(l) || (l->label && l->length == 1 && l->text[0] == ':'));

            if ((l->length == 3 && !strncmp(l->text, ".a8", 3)) ||
                (l->length == 4 && !strncmp(l->text, ".a16", 4)))
                known = 0;
            else if (!fallthrough && l->length && l->text[0] != ';' &&
                     strncmp(l->text, ".export", 7)) {
                known = 0;
                nslots = 0;
            }

            continue;
        }

        if (known_targets && i + 2 < u->count && lp_branch(l) && l->target == (int)(i + 2) &&
            !u->lines[i + 1].deleted && u->lines[i + 1].ends && !u->lines[i + 1].label &&
            targets[i + 2] == 1 && u->lines[i + 2].label) {
            // Preserve known A bits across a single-entry guard jump
            if (known && saved_target < 0 && lp_is(&u->lines[i + 1], "jmp") &&
                !u->lines[i + 1].indirect && u->lines[i + 1].target > (int)(i + 2) &&
                targets[u->lines[i + 1].target] == 1) {
                int prev = u->lines[i + 1].target - 1;

                while (prev >= 0 &&
                       (!u->lines[prev].length || u->lines[prev].text[0] == ';' ||
                        (u->lines[prev].label && !targets[prev]))) {
                    --prev;
                }

                if (prev >= 0 && u->lines[prev].ends) {
                    saved_target = u->lines[i + 1].target;
                    saved_zero = zero_a;
                    saved_ones = ones_a;
                }
            }

            i += 2;
            continue;
        }

        if (l->call && !l->x8 && private_stack && lp_callee(l)) {
            unsigned k = 0;

            /* A call returns to the same S and cannot name a private slot */
            while (k < nslots) {
                if (slots[k].name[strlen(slots[k].name) - 1] == 's')
                    ++k;
                else
                    slots[k] = slots[--nslots];
            }

            known = 0;
            continue;
        }

        if (l->call || l->x8 ||
            (l->use == LP_ALL && !lp_line_is(l, "sep #$20") && !lp_line_is(l, "rep #$20"))) {
            known = 0;
            nslots = 0;
            continue;
        }
        if (lp_line_is(l, "sep #$20") || lp_line_is(l, "rep #$20")) {
            known = 0;
            continue;
        }

        if (l->m8) {
            lp_known_invalidate(slots, &nslots, l);
            known = 0;

            if (l->ends)
                nslots = 0;

            continue;
        }

        if (known && lp_is(l, "and") && (imm = lp_immediate(l)) >= 0) {
            unsigned mask = (unsigned)imm & 0xFFFFu;

            if (!(mask & ~(zero_a | ones_a))) {
                lp_set(l, "    lda #$%04X", mask & ones_a);
                free(targets);
                return changed + 1;
            }
            if (!((~zero_a & 0xFFFFu) & ~mask) && !(l->out & (LP_N | LP_Z))) {
                l->deleted = 1;
                ++changed;
                continue;
            }
        }

        if (lp_is(l, "lda")) {
            lp_known_invalidate(slots, &nslots, l);

            if ((imm = lp_immediate(l)) >= 0) {
                known = 1;
                zero_a = (~(unsigned)imm) & 0xFFFFu;
                ones_a = (unsigned)imm & 0xFFFFu;
            } else {
                unsigned k;
                known = 0;
                ones_a = 0;

                if (n < sizeof slots[0].name && lp_private(o, n))
                    for (k = 0; k < nslots; ++k) {
                        if (strlen(slots[k].name) == n && !strncmp(slots[k].name, o, n)) {
                            known = 1;
                            zero_a = slots[k].zero;
                            ones_a = slots[k].ones;
                            break;
                        }
                    }
            }
        } else if (lp_is(l, "and") && (imm = lp_immediate(l)) >= 0) {
            if (!known) {
                zero_a = 0;
                ones_a = 0;
            }

            known = 1;
            zero_a |= (~(unsigned)imm) & 0xFFFFu;
            ones_a &= (unsigned)imm & 0xFFFFu;
        } else if (lp_is(l, "ora") && (imm = lp_immediate(l)) >= 0) {
            if (!known) {
                known = 1;
                zero_a = 0;
                ones_a = 0;
            }

            zero_a &= (~(unsigned)imm) & 0xFFFFu;
            ones_a |= (unsigned)imm & 0xFFFFu;
        } else if (lp_is(l, "eor") && (imm = lp_immediate(l)) >= 0) {
            if (known) {
                unsigned nz = (zero_a & ~(unsigned)imm) | (ones_a & (unsigned)imm);
                unsigned no = (ones_a & ~(unsigned)imm) | (zero_a & (unsigned)imm);
                zero_a = nz;
                ones_a = no;
            }
        } else if (lp_line_is(l, "xba")) {
            if (known) {
                zero_a = ((zero_a >> 8) | (zero_a << 8)) & 0xFFFFu;
                ones_a = ((ones_a >> 8) | (ones_a << 8)) & 0xFFFFu;
            }
        } else if (lp_line_is(l, "asl a")) {
            if (known) {
                zero_a = ((zero_a << 1) | 1u) & 0xFFFFu;
                ones_a = (ones_a << 1) & 0xFFFFu;
            }
        } else if (lp_line_is(l, "lsr a")) {
            if (known) {
                zero_a = ((zero_a >> 1) | 0x8000u) & 0xFFFFu;
                ones_a = (ones_a >> 1) & 0xFFFFu;
            }
        } else if (lp_is(l, "sta")) {
            if (known)
                lp_known_record(slots, &nslots, l, zero_a, ones_a);
            else
                lp_known_invalidate(slots, &nslots, l);
        } else if (lp_is(l, "stz")) {
            lp_known_record(slots, &nslots, l, 0xFFFFu, 0);
        } else {
            lp_known_invalidate(slots, &nslots, l);

            if (l->def & LP_A)
                known = 0;
        }

        if (l->ends) {
            known = 0;
            nslots = 0;
        }
    }

    free(targets);
    return changed;
}

static int lp_m_invariant_op(const LpLine *l)
{
    return l->op && !l->deleted && !l->replace && !l->x8 &&
           (lp_is(l, "ldx") || lp_is(l, "ldy") || lp_is(l, "stx") || lp_is(l, "sty") ||
            lp_is(l, "cpx") || lp_is(l, "cpy") || lp_is(l, "inx") || lp_is(l, "dex") ||
            lp_is(l, "iny") || lp_is(l, "dey") || lp_is(l, "phx") || lp_is(l, "phy") ||
            lp_is(l, "plx") || lp_is(l, "ply") || lp_is(l, "txy") || lp_is(l, "tyx") ||
            lp_is(l, "clc") || lp_is(l, "sec") || lp_is(l, "clv") || lp_is(l, "nop") ||
            lp_is(l, "pea"));
}

static int lp_m_invariant(const LpLine *l)
{
    return !l->m8 && lp_m_invariant_op(l);
}

static int lp_operand_has_s(const char *o, size_t n)
{
    size_t k;

    for (k = 0; k + 1 < n; ++k) {
        if (o[k] == ',' && o[k + 1] == 's')
            return 1;
    }

    return 0;
}

static int lp_is_mmio_operand(const char *o, size_t n)
{
    size_t k;
    const char *p = o;
    char *end;
    unsigned long addr;

    if (!n || o[0] == '#' || o[0] == '(' || o[0] == '[' || lp_operand_has_s(o, n))
        return 1;

    for (k = 0; k < n; ++k) {
        if (o[k] == '_')
            return 0;
    }

    if ((p[0] == 'a' || p[0] == 'f' || p[0] == 'z') && p[1] == ':' && p[2] == '$')
        p += 3;
    else if (p[0] == '$')
        p += 1;
    else
        return 1;

    addr = strtoul(p, &end, 16);

    if (end == p)
        return 1;

    addr &= 0xFFFFul;
    return addr >= 0x2000ul && addr < 0x6000ul;
}

/* Track the hardware M flag over internal branches. Assembler width
 * annotations describe operand encoding and stay in the output. */
static int lp_known_accumulator_mode(LpUnit *u, Function *f, size_t at)
{
    unsigned char *out;
    int again = 1, changed = 0;

    (void)at;

    if (!u->count || u->indirect || f->symbol->interrupt || body_asm_statements(f->body))
        return 0;

    out = allocate(u->count * sizeof *out);

    while (again) {
        again = 0;

        for (unsigned i = 0; i < u->count; ++i) {
            LpLine *l = &u->lines[i];

            /* Ordinary compiler entry follows the A16 calling convention */
            unsigned in = i ? (u->lines[i - 1].ends ? 0 : out[i - 1]) : 1;

            for (int edge = l->first_incoming; edge >= 0; edge = u->lines[edge].next_incoming) {
                in |= out[edge];
            }

            if (!in)
                continue;

            unsigned mode = in;

            if (lp_line_is(l, "rep #$20"))
                mode = 1;
            else if (lp_line_is(l, "sep #$20"))
                mode = 2;
            else if (l->call || (l->op && (l->use == LP_ALL || lp_is(l, "plp") || lp_is(l, "xce") ||
                                           lp_is(l, "rep") || lp_is(l, "sep"))))
                mode = 3;

            if (out[i] != mode) {
                out[i] = (unsigned char)mode;
                again = 1;
            }
        }
    }

    for (unsigned i = 1; i < u->count; ++i) {
        LpLine *l = &u->lines[i];

        if (!u->lines[i - 1].ends && ((out[i - 1] == 1 && lp_line_is(l, "rep #$20")) ||
                                      (out[i - 1] == 2 && lp_line_is(l, "sep #$20")))) {
            l->deleted = 1;
            ++changed;
        }
    }

    free(out);
    return changed;
}

static int lp_frame_byte_private(Function *f, unsigned byte);

static int lp_byte_test_branch(const LpUnit *u, unsigned restore, int taken_when_equal, int *after,
                               int *edge)
{
    if (!lp_line_is(&u->lines[restore], "rep #$20") || restore + 1 >= u->count ||
        u->lines[restore + 1].length != 4 || strncmp(u->lines[restore + 1].text, ".a16", 4))
        return -1;

    int compare = lp_next(u, restore, -1);

    if (compare < 0 || !u->lines[compare].m8 || !lp_is(&u->lines[compare], "cmp") ||
        lp_immediate(&u->lines[compare]) < 0)
        return -1;

    int branch = lp_next_mode(u, restore);
    int target = lp_cond_branch_target(u, branch, after);

    if (target < 0 ||
        !lp_is(&u->lines[branch], (taken_when_equal == (*after == branch)) ? "beq" : "bne"))
        return -1;

    *edge = *after == branch ? branch : branch + 1;
    return target;
}

/* Find the first instruction after a join with just one branch and
 * its contiguous fallthrough. The first op must follow the target label. */
static int lp_byte_test_join(const LpUnit *u, int from, int target, int edge)
{
    for (int i = from; (unsigned)i < u->count; ++i) {
        const LpLine *line = &u->lines[i];

        if (line->op)
            return i > target ? i : -1;
        if (!line->length || line->text[0] == ';')
            continue;
        if (!lp_fallthrough_label(line) || line->first_incoming != (i == target ? edge : -1) ||
            (i == target && u->lines[edge].next_incoming >= 0))
            break;
    }

    return -1;
}

/* Keep byte mode on both outcomes of the test until the cursor advance
 * needs word mode. The pretest and latch join only at those two points. */
static int lp_byte_loop_test_exits(LpUnit *u, Function *f, size_t at)
{
    (void)at;

    if (u->indirect || lp_state.parser->no_byte_shuffles || body_asm_statements(f->body))
        return 0;

    for (unsigned first = 0; first < u->count; ++first) {
        int entry_after, entry_edge;
        int exit = lp_byte_test_branch(u, first, 0, &entry_after, &entry_edge);

        if (exit < 0 || exit <= entry_after || (unsigned)(exit - entry_after) > 96)
            continue;

        for (int latch = entry_after + 1; latch < exit; ++latch) {
            int latch_after, latch_edge;
            int head = lp_byte_test_branch(u, (unsigned)latch, 1, &latch_after, &latch_edge);

            if (head <= entry_after || head >= latch || latch_after >= exit)
                continue;

            int step = lp_byte_test_join(u, entry_after + 1, head, latch_edge);
            int narrow = lp_byte_test_join(u, latch_after + 1, exit, entry_edge);

            if (step < 0 || step >= latch || narrow < 0 ||
                !lp_line_is(&u->lines[narrow], "sep #$20") || (unsigned)narrow + 1 >= u->count ||
                u->lines[narrow + 1].length != 3 || strncmp(u->lines[narrow + 1].text, ".a8", 3))
                continue;

            lp_insert(&u->lines[step], "    rep #$20\n.a16\n");
            u->lines[first].deleted = u->lines[first + 1].deleted = 1;
            u->lines[latch].deleted = u->lines[latch + 1].deleted = u->lines[narrow].deleted = 1;
            return 1;
        }
    }

    return 0;
}

static int lp_frame_indexed_offset(const LpLine *line, int index)
{
    size_t n;
    const char *p = lp_operand(line, &n);

    if (n != 9 || strncmp(p, "a:$", 3) || p[7] != ',' || p[8] != index)
        return -1;

    char *end;
    long offset = strtol(p + 3, &end, 16);

    return end == p + 7 && offset >= 0 && offset <= 65535 ? (int)offset : -1;
}

static int lp_previous_frame_index_transfer(const LpUnit *u, int before)
{
    for (int i = before; (i = lp_next(u, (unsigned)i, -1)) >= 0;) {
        const LpLine *line = &u->lines[i];

        if (lp_line_is(line, "tax") && !line->m8 && !line->x8)
            return i;
        if ((line->def & (LP_X | LP_Y)) || line->use == LP_ALL || line->call || line->ends ||
            lp_branch(line))
            break;
    }

    return -1;
}

static int lp_remove_equal_frame_compare(LpUnit *u, int compare)
{
    int branch = lp_next(u, (unsigned)compare, 1), after = -1;

    if (branch < 0 || lp_cond_branch_target(u, branch, &after) < 0 ||
        !lp_is(&u->lines[branch], after == branch ? "bne" : "beq"))
        return 0;

    unsigned live = after == branch ? u->lines[branch].out : u->lines[after].live;

    if (live & (LP_C | LP_N | LP_Z))
        return 0;

    u->lines[compare].deleted = u->lines[branch].deleted = 1;

    if (after != branch)
        u->lines[branch + 1].deleted = 1;

    return 1;
}

/* Only direct, disjoint frame stores can intervene in this snapshot */
static int lp_previous_frame_word_store(const LpUnit *u, int before, int slot)
{
    for (int i = before; i-- > 0;) {
        const LpLine *line = &u->lines[i];

        if (!line->op) {
            if (!line->length || line->text[0] == ';' ||
                !strncmp(line->text, ".export __inlined_", 18) ||
                (lp_fallthrough_label(line) && line->first_incoming < 0))
                continue;

            break;
        }

        if (line->x8 || line->use == LP_ALL || (line->def & LP_Y) || lp_stack_op(line) ||
            line->ends || lp_branch(line))
            break;
        if (!lp_store_op(line) || lp_operand_is(line, "a", 1))
            continue;

        int other = lp_frame_indexed_offset(line, 'y');

        if (other < 0)
            break;
        if (lp_overlaps(line, other, slot))
            return other == slot && !line->m8 && lp_is(line, "sta") ? i : -1;
    }

    return -1;
}

/* A frame pointer stored back after an increment is still a known
 * offset from Y. The comparison can use the two offsets directly. */
static int lp_compare_saved_frame_offset(LpUnit *u, Function *f, size_t at)
{
    (void)at;

    if (u->indirect || lp_state.is_volatile || lp_state.parser->no_private_regions ||
        lp_state.parser->no_value_reuse || body_asm_statements(f->body))
        return 0;

    long *offsets = NULL;
    PrState *frames = NULL;
    int changed = 0;

    for (unsigned i = 0; i < u->count; ++i) {
        LpLine *compare = &u->lines[i];

        if (compare->m8 || compare->x8 || !lp_is(compare, "cmp"))
            continue;

        int slot = lp_frame_indexed_offset(compare, 'y');

        if (slot <= 0 || (unsigned)(slot + 1) > f->slots)
            continue;

        int store = lp_previous_frame_word_store(u, (int)i, slot);

        if (store < 0)
            continue;

        int load = store, delta = 0;

        while ((load = lp_next(u, (unsigned)load, -1)) >= 0) {
            LpLine *step = &u->lines[load];

            if (step->m8 || (!lp_line_is(step, "inc a") && !lp_line_is(step, "dec a")))
                break;

            delta += lp_is(step, "inc") ? 1 : -1;
        }

        if (load < 0 || !delta || u->lines[load].m8 || !lp_is(&u->lines[load], "lda") ||
            lp_frame_indexed_offset(&u->lines[load], 'y') != slot)
            continue;

        int initial = lp_previous_frame_word_store(u, load, slot);

        if (initial < 0)
            continue;

        if (!offsets) {
            offsets = allocate(u->count * sizeof *offsets);
            lp_accumulator_offsets(u, offsets, LP_Y);
            frames = pr_states(u);
            lp_liveness(u);
        }

        if (offsets[initial] < 0 || offsets[i] < 0 ||
            ((offsets[initial] + delta) & 65535) != offsets[i] || !frames[initial].frame ||
            !frames[i].frame)
            continue;
        if (lp_remove_equal_frame_compare(u, (int)i)) {
            changed = 1;
            break;
        }
    }

    free(offsets);
    free(frames);
    return changed;
}

/* X can refer to a different stack slot than the word just saved in Y.
 * Clearing that slot leaves the accumulator and its saved copy equal. */
static int lp_compare_past_frame_clear(LpUnit *u, Function *f, size_t at)
{
    (void)at;

    if (u->indirect || lp_state.is_volatile || lp_state.parser->no_private_regions ||
        lp_state.parser->no_value_reuse || body_asm_statements(f->body))
        return 0;

    long *offsets = NULL;
    PrState *frames = NULL;
    int changed = 0;

    for (unsigned i = 0; i < u->count; ++i) {
        LpLine *clear = &u->lines[i];

        if (clear->m8 || clear->x8 || !lp_is(clear, "stz") ||
            lp_frame_indexed_offset(clear, 'x') != 0)
            continue;

        int store = lp_next(u, i, -1), compare = lp_next(u, i, 1);

        if (store < 0 || compare < 0 || !lp_is(&u->lines[store], "sta") ||
            !lp_is(&u->lines[compare], "cmp") || u->lines[store].m8 || u->lines[compare].m8)
            continue;

        int slot = lp_frame_indexed_offset(&u->lines[store], 'y');

        if (slot <= 0 || (unsigned)(slot + 1) > f->slots ||
            lp_frame_indexed_offset(&u->lines[compare], 'y') != slot)
            continue;

        int transfer = lp_previous_frame_index_transfer(u, store);

        if (transfer < 0)
            continue;

        if (!offsets) {
            offsets = allocate(u->count * sizeof *offsets);
            lp_accumulator_offsets(u, offsets, LP_Y);
            frames = pr_states(u);
            lp_liveness(u);
        }

        long cleared = offsets[transfer];

        if (cleared <= 0 || (unsigned long)(cleared + 1) > f->slots || labs(cleared - slot) < 2 ||
            !frames[transfer].frame || !frames[i].frame)
            continue;
        if (lp_remove_equal_frame_compare(u, compare)) {
            changed = 1;
            break;
        }
    }

    free(offsets);
    free(frames);
    return changed;
}

/* The same stack word can be addressed through either the retained
 * frame register or an index derived from it without intervening writes. */
static int lp_forward_frame_clear(LpUnit *u, Function *f, size_t at)
{
    (void)at;

    if (u->indirect || lp_state.is_volatile || lp_state.parser->no_private_regions ||
        lp_state.parser->no_value_reuse || body_asm_statements(f->body))
        return 0;

    long *offsets = NULL;
    PrState *frames = NULL;
    int changed = 0;

    for (unsigned i = 0; i < u->count; ++i) {
        LpLine *clear = &u->lines[i];

        if (clear->m8 || clear->x8 || !lp_is(clear, "stz") ||
            lp_frame_indexed_offset(clear, 'x') != 0)
            continue;

        unsigned next = i + 1;

        while (next < u->count && lp_internal_path_marker(u, next, i)) {
            ++next;
        }

        if (next >= u->count)
            continue;

        LpLine *load = &u->lines[next];

        if (load->m8 || load->x8 || !lp_is(load, "lda"))
            continue;

        int slot = lp_frame_indexed_offset(load, 'y');
        int transfer = lp_previous_frame_index_transfer(u, (int)i);

        if (slot <= 0 || (unsigned)(slot + 1) > f->slots || transfer < 0)
            continue;

        if (!offsets) {
            offsets = allocate(u->count * sizeof *offsets);
            lp_accumulator_offsets(u, offsets, LP_Y);
            frames = pr_states(u);
        }

        if (offsets[transfer] != slot || !frames[transfer].frame || !frames[next].frame)
            continue;

        lp_set(load, "    lda #$0000");
        changed = 1;
        break;
    }

    free(offsets);
    free(frames);
    return changed;
}

/* A byte already loaded from a private local can provide bit 7 in C
 * before its masked store. This avoids a second word load and XBA/ASL. */
static int lp_carry_from_shift_byte(LpUnit *u, Function *f, size_t at)
{
    int changed = 0;

    (void)at;

    if (!u->count || u->indirect || lp_state.is_volatile || lp_state.frame_address ||
        lp_state.parser->no_private_regions || lp_state.parser->no_value_reuse ||
        body_asm_statements(f->body))
        return 0;

    PrState *frames = NULL;

    for (unsigned i = 0; i + 1 < u->count; ++i) {
        LpLine *rep = &u->lines[i];

        if (!lp_line_is(rep, "rep #$20") || u->lines[i + 1].length != 4 ||
            strncmp(u->lines[i + 1].text, ".a16", 4))
            continue;

        int store = lp_next(u, i, -1), reload = lp_next(u, i + 1, 1);

        if (store < 0 || reload < 0 || !lp_is(&u->lines[store], "sta") || !u->lines[store].m8 ||
            !lp_is(&u->lines[reload], "lda") || u->lines[reload].m8)
            continue;

        int mask = lp_next(u, (unsigned)store, -1);

        if (mask >= 0 && lp_is(&u->lines[mask], "ldx"))
            mask = lp_next(u, (unsigned)mask, -1);
        if (mask < 0 || !lp_is(&u->lines[mask], "and") || !u->lines[mask].m8 ||
            lp_immediate(&u->lines[mask]) < 0)
            continue;

        int read = lp_next(u, (unsigned)mask, -1);

        if (read < 0 || !lp_is(&u->lines[read], "lda") || !u->lines[read].m8)
            continue;

        size_t length;
        const char *home = lp_operand(&u->lines[read], &length);

        if (length != 9 || strncmp(home, "a:$", 3) || memcmp(home + 7, ",y", 2) ||
            !lp_operand_is(&u->lines[reload], home, length))
            continue;

        int swap = lp_next(u, (unsigned)reload, 1),
            shift = swap < 0 ? -1 : lp_next(u, (unsigned)swap, 1);
        int next = shift < 0 ? -1 : lp_next(u, (unsigned)shift, 1);

        if (next < 0 || !lp_line_is(&u->lines[swap], "xba") ||
            !lp_line_is(&u->lines[shift], "asl a") || !lp_is(&u->lines[next], "lda") ||
            u->lines[next].m8)
            continue;

        unsigned home_byte = (unsigned)strtoul(home + 3, NULL, 16);

        if (!home_byte || home_byte + 1 > f->slots || !lp_frame_byte_private(f, home_byte) ||
            !lp_frame_byte_private(f, home_byte + 1))
            continue;

        int offset;

        if (!frames)
            frames = pr_states(u);
        if (!frames[read].frame || !frames[reload].frame ||
            pr_memory(&u->lines[store], &frames[store], f, &offset) != PR_OTHER)
            continue;

        lp_insert(&u->lines[mask], "    cmp #$80\n");
        u->lines[reload].deleted = u->lines[swap].deleted = u->lines[shift].deleted = 1;
        changed = 1;
        break;
    }

    free(frames);
    return changed;
}

/* Adjacent byte regions need one width transition pair, bridging any
 * M-invariant X/Y/flag/immediate-push instructions between them. */
static int lp_byte_region_modes(LpUnit *u, Function *f, size_t at)
{
    unsigned i, j;
    int changed = 0, known_targets = 0;
    unsigned char *targets = lp_local_targets(u, &known_targets);

    (void)at;

    if (!f->symbol->interrupt && !lp_state.is_volatile) {
        lp_liveness(u);

        for (i = 0; i + 1 < u->count; ++i) {
            int k, load = -1;
            size_t n;
            const char *o;

            if (u->lines[i].deleted || u->lines[i].replace || u->lines[i].before ||
                u->lines[i].label || u->lines[i + 1].deleted || u->lines[i + 1].replace ||
                u->lines[i + 1].before || u->lines[i + 1].label || u->lines[i].m8 ||
                !lp_line_is(&u->lines[i], "sep #$20") || u->lines[i + 1].length != 3 ||
                strncmp(u->lines[i + 1].text, ".a8", 3))
                continue;
            if ((u->lines[i].live & (LP_N | LP_Z)) || (u->lines[i + 1].out & LP_AH))
                continue;

            for (k = (int)i - 1; k >= 0; --k) {
                const LpLine *l = &u->lines[k];

                if (l->deleted)
                    continue;
                if (!l->op) {
                    if (!l->label && l->length && l->text[0] == ';')
                        continue;

                    break;
                }
                if (l->replace || l->before || l->label)
                    break;
                if (lp_is(l, "lda") && !l->m8) {
                    load = k;
                    break;
                }
                if ((lp_is(l, "and") || lp_is(l, "ora") || lp_is(l, "eor")) && !l->m8 &&
                    lp_immediate(l) >= 0)
                    continue;
                if (!lp_m_invariant(l))
                    break;
            }

            if (load < 0)
                continue;

            o = lp_operand(&u->lines[load], &n);
            long imm = lp_immediate(&u->lines[load]);

            if (imm < 0 && !lp_operand_has_s(o, n) && lp_is_mmio_operand(o, n))
                continue;

            /* Only the low byte survives this region. Shorten its logical
             * immediates alongside the load; they do not read the flags. */
            if (imm >= 0)
                lp_set(&u->lines[load], "    lda #$%02lX", imm & 255);

            for (k = load + 1; k < (int)i; ++k) {
                LpLine *l = &u->lines[k];

                if (!l->deleted && (lp_is(l, "and") || lp_is(l, "ora") || lp_is(l, "eor")))
                    lp_set(l, "    %.3s #$%02lX", l->op, lp_immediate(l) & 255);
            }

            lp_insert(&u->lines[load], "    sep #$20\n.a8\n");
            u->lines[i].deleted = u->lines[i + 1].deleted = 1;
            changed = 1;
        }

        if (changed) {
            free(targets);
            return 1;
        }
    }

    for (i = 0; i + 1 < u->count; ++i) {
        if (!u->lines[i].deleted && lp_line_is(&u->lines[i], "rep #$20") &&
            u->lines[i + 1].length == 4 && !strncmp(u->lines[i + 1].text, ".a16", 4)) {
            for (j = i + 2; j < u->count; ++j) {
                const LpLine *l = &u->lines[j];

                if (l->deleted)
                    continue;
                if (lp_fallthrough_marker(l, j, targets, known_targets))
                    continue;
                if (lp_m_invariant(l))
                    continue;

                break;
            }

            if (j + 1 < u->count && !u->lines[j].deleted && lp_line_is(&u->lines[j], "sep #$20") &&
                u->lines[j + 1].length == 3 && !strncmp(u->lines[j + 1].text, ".a8", 3)) {
                u->lines[i].deleted = u->lines[i + 1].deleted = u->lines[j].deleted =
                    u->lines[j + 1].deleted = 1;
                changed = 1;
                i = j + 1;
            }
        }
    }

    for (i = 0; i + 1 < u->count; ++i) {
        if (!u->lines[i].deleted && lp_line_is(&u->lines[i], "sep #$20") &&
            u->lines[i + 1].length == 3 && !strncmp(u->lines[i + 1].text, ".a8", 3)) {
            int entry_a16 = 0;

            for (j = i; j-- > 0;) {
                const LpLine *p = &u->lines[j];

                if (p->deleted)
                    continue;
                if (p->length == 4 && !strncmp(p->text, ".a16", 4)) {
                    entry_a16 = 1;
                    break;
                }
                if (p->length == 3 && !strncmp(p->text, ".a8", 3))
                    break;
                if (!p->op) {
                    if (p->length && p->text[0] == ';')
                        continue;

                    break;
                }
                if (lp_is(p, "sep") || lp_is(p, "rep") || lp_line_is(p, "plp") ||
                    lp_line_is(p, "rti"))
                    break;
            }

            if (!entry_a16)
                continue;

            for (j = i + 2; j < u->count; ++j) {
                const LpLine *l = &u->lines[j];

                if (l->deleted)
                    continue;
                if (lp_fallthrough_marker(l, j, targets, known_targets))
                    continue;
                if (lp_m_invariant_op(l))
                    continue;

                break;
            }

            if (j + 1 < u->count && !u->lines[j].deleted && lp_line_is(&u->lines[j], "rep #$20") &&
                u->lines[j + 1].length == 4 && !strncmp(u->lines[j + 1].text, ".a16", 4)) {
                u->lines[i].deleted = u->lines[i + 1].deleted = u->lines[j].deleted =
                    u->lines[j + 1].deleted = 1;
                changed = 1;
                i = j + 1;
            }
        }
    }

    /* If a width region lost its last instruction, intervening assembler
     * width annotations do not observe M. The final REP establishes A16
     * even when the incoming hardware width is unknown. */
    for (i = 0; i < u->count; ++i) {
        if (lp_line_is(&u->lines[i], "sep #$20") && !u->lines[i].deleted) {
            for (j = i + 1; j < u->count; ++j) {
                LpLine *l = &u->lines[j];

                if (l->deleted || !l->length || l->text[0] == ';' ||
                    (l->length == 3 && !strncmp(l->text, ".a8", 3)) ||
                    (l->length == 4 && !strncmp(l->text, ".a16", 4)))
                    continue;

                if (lp_line_is(l, "rep #$20") && j + 1 < u->count && u->lines[j + 1].length == 4 &&
                    !strncmp(u->lines[j + 1].text, ".a16", 4)) {
                    for (unsigned k = i; k < j; ++k) {
                        if (k == i || u->lines[k].text[0] == '.')
                            u->lines[k].deleted = 1;
                    }

                    changed = 1;
                }

                break;
            }
        }
    }

    free(targets);
    return changed;
}

/* Remove PHX/PLX pairs when nothing in between modifies X, shifts S or uses ,s */
static int lp_dead_x_save(LpUnit *u, Function *f, size_t at)
{
    unsigned i;
    int changed = 0;

    (void)f;
    (void)at;

    lp_liveness(u);

    for (i = 0; i < u->count; ++i) {
        LpLine *push = &u->lines[i];
        int k;

        if (!lp_line_is(push, "phx") || push->x8 || push->deleted || push->replace)
            continue;

        k = (int)i;

        while ((k = lp_next(u, (unsigned)k, 1)) >= 0) {
            LpLine *l = &u->lines[k];
            size_t n;
            const char *o;
            int sp_rel = 0;

            unsigned c;

            if (l->deleted || l->replace)
                break;

            if (lp_line_is(l, "plx") && !l->x8) {
                if (!(l->out & (LP_N | LP_Z))) {
                    push->deleted = l->deleted = 1;
                    ++changed;
                }

                break;
            }

            if (l->x8 || l->call || l->ends || lp_branch(l) || lp_stack_op(l) || (l->def & LP_X) ||
                (l->use == LP_ALL && !lp_line_is(l, "sep #$20") && !lp_line_is(l, "rep #$20")))
                break;

            o = lp_operand(l, &n);

            for (c = 0; c + 1 < n; ++c) {
                if (o[c] == ',' && o[c + 1] == 's') {
                    sp_rel = 1;
                    break;
                }
            }

            if (sp_rel)
                break;
        }
    }

    return changed;
}

/* Narrow 16-bit RMWs ending in "sep #$20 / .a8 / sta <same>" when A and N/Z die */
static int lp_byte_rmw(LpUnit *u, Function *f, size_t at)
{
    unsigned i;
    int changed = 0;

    (void)f;
    (void)at;

    if (lp_state.is_volatile)
        return 0;

    lp_liveness(u);

    for (i = 0; i < u->count; ++i) {
        LpLine *load = &u->lines[i];
        size_t n;
        const char *op;
        int k, sep = -1, store = -1, steps = 0, ok = 1;

        if (!lp_is(load, "lda") || load->m8 || load->deleted || load->replace)
            continue;

        op = lp_operand(load, &n);

        if (!n || op[0] == '#')
            continue;

        k = (int)i;

        while ((k = lp_next(u, (unsigned)k, 1)) >= 0) {
            LpLine *l = &u->lines[k];

            if (l->deleted || l->replace) {
                ok = 0;
                break;
            }
            if (lp_line_is(l, "sep #$20")) {
                sep = k;
                break;
            }
            if (l->m8 || l->call || l->ends || lp_branch(l)) {
                ok = 0;
                break;
            }
            if ((lp_is(l, "and") || lp_is(l, "ora") || lp_is(l, "eor")) && lp_immediate(l) >= 0 &&
                !(l->out & (LP_N | LP_Z))) {
                ++steps;
                continue;
            }
            if ((lp_line_is(l, "inc a") || lp_line_is(l, "dec a")) && !(l->out & (LP_N | LP_Z))) {
                ++steps;
                continue;
            }

            ok = 0;
            break;
        }

        if (!ok || sep < 0 || !steps || (unsigned)sep + 1 >= u->count ||
            u->lines[sep + 1].length != 3 || strncmp(u->lines[sep + 1].text, ".a8", 3))
            continue;

        store = lp_next(u, (unsigned)sep + 1, 1);

        if (store < 0 || !lp_is(&u->lines[store], "sta") ||
            !lp_operand_is(&u->lines[store], op, n) || u->lines[store].deleted ||
            u->lines[store].replace || (u->lines[store].out & (LP_A | LP_N | LP_Z)))
            continue;

        lp_set(load, "    sep #$20\n.a8\n    lda %.*s", (int)n, op);

        for (k = lp_next(u, i, 1); k >= 0 && k < sep; k = lp_next(u, (unsigned)k, 1)) {
            LpLine *l = &u->lines[k];
            long imm = lp_immediate(l);

            if (imm >= 0) {
                unsigned b = (unsigned)imm & 0xFFu;

                if ((lp_is(l, "and") && b == 0xFFu) ||
                    ((lp_is(l, "ora") || lp_is(l, "eor")) && b == 0u))
                    l->deleted = 1;
                else
                    lp_set(l, "    %.3s #$%02X", l->op, b);
            }
        }

        u->lines[sep].deleted = u->lines[sep + 1].deleted = 1;
        ++changed;
        i = (unsigned)store;
    }

    return changed;
}

/* Advance a private masked cursor before loading its old indexed element.
 * Keeping the old cursor in X leaves the loaded value in A for its consumer. */
static int lp_advance_before_indexed_load(LpUnit *u, Function *f, size_t at)
{
    unsigned i;
    (void)f;
    (void)at;

    if (u->indirect || lp_state.is_volatile)
        return 0;

    for (i = 0; i < u->count; ++i) {
        LpLine *x = &u->lines[i], *q[8];
        int j = (int)i, word;

        unsigned k;
        size_t n, m;
        const char *cell, *cursor, *array;

        if (x->m8 || x->x8 || (!lp_is(x, "tax") && !lp_is(x, "ldx")))
            continue;

        for (k = 0; k < 8; ++k) {
            j = lp_next(u, (unsigned)j, 1);

            if (j < 0 || u->lines[j].m8 || u->lines[j].x8)
                break;

            q[k] = &u->lines[j];
        }

        if (k < 8 || !lp_is(q[0], "lda") || !lp_is(q[1], "sta") || !lp_line_is(q[2], "txa") ||
            !lp_line_is(q[3], "clc") || !lp_is(q[4], "adc") || lp_immediate(q[4]) < 0 ||
            !lp_is(q[5], "and") || lp_immediate(q[5]) < 0 || !lp_is(q[6], "sta") ||
            !lp_is(q[7], "lda"))
            continue;

        array = lp_operand(q[0], &n);

        if (n < 15 || strncmp(array, "a:.loword(_", 11) || array[n - 2] != ',' ||
            array[n - 1] != 'x')
            continue;

        cell = lp_operand(q[1], &n);
        cursor = lp_operand(q[6], &m);
        word = lp_workspace_word(cell, n);

        if (word < 0 || (word & 1) || lp_workspace_word(cursor, m) < 0 ||
            (lp_workspace_word(cursor, m) & 1) || lp_workspace_word(cursor, m) == word ||
            !lp_operand_is(q[7], cell, n))
            continue;
        if (lp_is(x, "ldx") && !lp_operand_is(x, cursor, m))
            continue;

        lp_set(q[7], "    %.*s\n    %.*s", (int)q[0]->length - 4, q[0]->op, (int)q[1]->length - 4,
               q[1]->op);
        q[0]->deleted = q[1]->deleted = 1;

        if (lp_is(x, "tax"))
            q[2]->deleted = 1;

        return 1;
    }

    return 0;
}

/* A discarded word update can use native RMW on compiler scratch or a
 * nonvolatile named WRAM object. INC/DEC preserve the same N/Z and C/V. */
static int lp_memory_word_steps(LpUnit *u, Function *f, size_t at)
{
    unsigned i;
    (void)f;
    (void)at;

    lp_liveness(u);

    for (i = 0; i < u->count; ++i) {
        LpLine *l = &u->lines[i];
        int step, store, w;
        size_t n, m;
        const char *p, *destination;

        if (lp_is(l, "ldx") && !l->x8) {
            int txa = lp_next(u, i, 1);

            p = lp_operand(l, &n);
            w = lp_workspace_word(p, n);

            if (txa >= 0 && lp_line_is(&u->lines[txa], "txa") && !u->lines[txa].m8 &&
                (w >= 0 || ((n >= 4 && !strncmp(p, "a:_", 3)) ||
                            (n >= 13 && !strncmp(p, "a:.loword(_", 11) && p[n - 1] == ')'))) &&
                (w >= 0 || (!memchr(p, ',', n) && pr_named(p, n)))) {
                step = lp_next(u, (unsigned)txa, 1);

                if (step >= 0 && (lp_line_is(&u->lines[step], "inc a") ||
                                  lp_line_is(&u->lines[step], "dec a"))) {
                    store = lp_next(u, (unsigned)step, 1);

                    if (store >= 0 && lp_is(&u->lines[store], "sta") && !u->lines[store].m8 &&
                        !(u->lines[store].out & LP_A)) {
                        destination = lp_operand(&u->lines[store], &m);

                        if (lp_operand_is(&u->lines[store], p, n) ||
                            (w < 0 && n == m + 9 && m >= 4 && !strncmp(p, "a:.loword(_", 11) &&
                             !strncmp(destination, "a:_", 3) &&
                             !strncmp(p + 10, destination + 2, m - 2))) {
                            lp_set(&u->lines[txa], "    %.3s %.*s", u->lines[step].op, (int)n, p);
                            u->lines[step].deleted = u->lines[store].deleted = 1;
                            return 1;
                        }
                    }
                }
            }
        }

        if (!lp_is(l, "lda") || l->m8)
            continue;

        p = lp_operand(l, &n);
        w = lp_workspace_word(p, n);

        if (w < 0 && ((n < 4 || strncmp(p, "a:_", 3)) &&
                      (n < 13 || strncmp(p, "a:.loword(_", 11) || p[n - 1] != ')')))
            continue;
        if (w < 0 && (memchr(p, ',', n) || !pr_named(p, n)))
            continue;

        step = lp_next(u, i, 1);

        if (step < 0)
            continue;
        if (!lp_line_is(&u->lines[step], "inc a") && !lp_line_is(&u->lines[step], "dec a"))
            continue;

        store = lp_next(u, (unsigned)step, 1);

        if (store < 0 || !lp_is(&u->lines[store], "sta") || u->lines[store].m8 ||
            u->lines[store].out & LP_A)
            continue;

        destination = lp_operand(&u->lines[store], &m);

        if (!lp_operand_is(&u->lines[store], p, n) &&
            !(w < 0 && n == m + 9 && m >= 4 && !strncmp(p, "a:.loword(_", 11) &&
              !strncmp(destination, "a:_", 3) && !strncmp(p + 10, destination + 2, m - 2)))
            continue;

        lp_set(l, "    %.3s %.*s", u->lines[step].op, (int)n, p);
        u->lines[step].deleted = u->lines[store].deleted = 1;
        return 1;
    }

    return 0;
}

/* INC and DEC set the same N/Z as a same-width reload of the result.
 * Only named nonvolatile objects are eligible, including indexed arrays. */
static int lp_rmw_reload(LpUnit *u, Function *f, size_t at)
{
    unsigned i;
    (void)f;
    (void)at;

    if (lp_state.is_volatile || u->indirect)
        return 0;

    lp_liveness(u);

    for (i = 0; i < u->count; ++i) {
        LpLine *update = &u->lines[i], *load;
        const char *operand;
        size_t length;
        int next;

        if (!lp_is(update, "inc") && !lp_is(update, "dec"))
            continue;

        next = lp_next(u, i, 1);

        if (next < 0)
            continue;

        load = &u->lines[next];

        if (!lp_is(load, "lda") || load->m8 != update->m8 || (load->out & LP_A))
            continue;

        operand = lp_operand(update, &length);

        if (!pr_named(operand, length) || !lp_operand_is(load, operand, length))
            continue;

        load->deleted = 1;
        return 1;
    }

    for (i = 0; i < u->count; ++i) {
        LpLine *load = &u->lines[i], *shift, *store;
        const char *operand, *comma;
        size_t length;
        int s, t;

        if (!lp_is(load, "lda") || load->deleted || load->replace)
            continue;

        operand = lp_operand(load, &length);

        if (length < 3 || (strncmp(operand, "z:", 2) && strncmp(operand, "a:", 2)) ||
            memchr(operand, '(', length) || memchr(operand, '[', length))
            continue;

        comma = memchr(operand, ',', length);

        if (comma && !(comma + 2 == operand + length && comma[1] == 'x'))
            continue;

        s = lp_next(u, i, 1);
        t = s < 0 ? -1 : lp_next(u, (unsigned)s, 1);

        if (t < 0)
            continue;

        shift = &u->lines[s];
        store = &u->lines[t];

        if (shift->deleted || shift->replace || store->deleted || store->replace ||
            shift->m8 != load->m8 || store->m8 != load->m8 ||
            (!lp_line_is(shift, "lsr a") && !lp_line_is(shift, "asl a") &&
             !lp_line_is(shift, "ror a") && !lp_line_is(shift, "rol a")) ||
            !lp_is(store, "sta") || !lp_operand_is(store, operand, length) || (store->out & LP_A))
            continue;

        lp_set(load, "    %.3s %.*s", shift->op, (int)length, operand);
        shift->deleted = store->deleted = 1;
        return 1;
    }

    return 0;
}

/* Swap a constant's bytes instead of swapping A around a word operation.
 * The final XBA reports byte N/Z, so those flags must be dead. */
static int lp_swapped_word_mask(LpUnit *u, Function *f, size_t at)
{
    unsigned i;
    (void)f;
    (void)at;

    lp_liveness(u);

    for (i = 0; i < u->count; ++i) {
        LpLine *first = &u->lines[i], *operation, *last;
        int op, end;
        long mask;

        if (!lp_line_is(first, "xba") || first->m8 || (op = lp_next(u, i, 1)) < 0)
            continue;

        operation = &u->lines[op];

        if (operation->m8 ||
            (!lp_is(operation, "and") && !lp_is(operation, "ora") && !lp_is(operation, "eor")) ||
            (mask = lp_immediate(operation)) < 0 || mask > 65535 ||
            (end = lp_next(u, (unsigned)op, 1)) < 0)
            continue;

        last = &u->lines[end];

        if (last->m8 || !lp_line_is(last, "xba") || (last->out & (LP_N | LP_Z)))
            continue;

        lp_set(operation, "    %.3s #$%04lX", operation->op, ((mask & 255) << 8) | (mask >> 8));
        first->deleted = last->deleted = 1;
        return 1;
    }

    return 0;
}

/* A full-width transfer solely to feed an unindexed store can use the
 * source register's store opcode. Keep live A and transfer flags intact. */
static int lp_store_index_value(LpUnit *u, Function *f, size_t at)
{
    unsigned i;
    (void)f;
    (void)at;

    lp_liveness(u);

    for (i = 0; i < u->count; ++i) {
        LpLine *transfer = &u->lines[i], *store;
        int next;
        size_t n;
        const char *operand;

        if (transfer->m8 || transfer->x8 ||
            (!lp_line_is(transfer, "txa") && !lp_line_is(transfer, "tya")) ||
            (next = lp_next(u, i, 1)) < 0)
            continue;

        store = &u->lines[next];

        if (store->m8 || !lp_is(store, "sta") || (store->out & (LP_A | LP_N | LP_Z)))
            continue;

        operand = lp_operand(store, &n);

        if (n < 3 || (strncmp(operand, "a:", 2) && strncmp(operand, "z:", 2)) ||
            memchr(operand, ',', n))
            continue;

        lp_set(store, "    %s %.*s", lp_line_is(transfer, "txa") ? "stx" : "sty", (int)n, operand);
        transfer->deleted = 1;
        return 1;
    }

    return 0;
}

/* The direct-page word is already a near address. If the loaded X is
 * otherwise dead, an unindexed indirect load gives the same value and flags. */
static int lp_near_indirect(LpUnit *u, Function *f, size_t at)
{
    unsigned i;
    int changed = 0;

    (void)f;
    (void)at;

    if (lp_state.parser->no_direct_dpage)
        return 0;

    lp_liveness(u);

    for (i = 0; i < u->count; ++i) {
        LpLine *l = &u->lines[i], *read;
        const char *p;
        size_t n;
        int j;

        if (!lp_is(l, "ldx") || l->x8 || (j = lp_next(u, i, 1)) < 0)
            continue;

        read = &u->lines[j];
        p = lp_operand(l, &n);

        if ((read->out & LP_X) || lp_workspace_word(p, n) < 0 || n < 3 || strncmp(p, "z:", 2))
            continue;
        if (!lp_operand_is(read, "a:$0000,x", 9) || !lp_accumulator_memory(read))
            continue;

        /* Unlike LDA, a store does not replace the flags set by LDX */
        if (lp_is(read, "sta") && (read->out & (LP_N | LP_Z)))
            continue;

        l->deleted = 1;
        lp_set(read, "    %.3s (%.*s)", read->op, (int)n - 2, p + 2);
        ++changed;
    }

    return changed;
}

/* With the two-word parameter frame still in place, a reload of its first
 * slot into X can feed a self-call without rewriting that same slot. */
static int lp_first_parameter_in_x(LpUnit *u, unsigned call)
{
    for (int j = (int)call; (j = lp_next(u, (unsigned)j, -1)) >= 0;) {
        LpLine *l = &u->lines[j];

        if (l->m8 || l->x8 || l->use == LP_ALL || lp_stack_op(l) || lp_store_op(l) || l->ends ||
            l->target >= 0)
            return 0;

        if (l->def & LP_X) {
            int source = lp_next(u, (unsigned)j, -1);

            return lp_line_is(l, "tax") && source >= 0 && !u->lines[source].m8 &&
                   lp_line_is(&u->lines[source], "lda 1,s");
        }
    }

    return 0;
}

/* A void wrapper can restore a short push-only frame before transferring
 * to a register-argument callee. Pull through Y so X and A still hold args. */
static int lp_tail_return_compatible(Type caller, Type callee)
{
    if (caller.base == TY_VOID && !caller.pointers)
        return !structure_object(callee);

    return !structure_object(caller) && !structure_object(callee) &&
           (callee.base != TY_VOID || callee.pointers) && reg_width(caller) == reg_width(callee) &&
           reg_width(caller) <= 4 && width(caller) == width(callee) &&
           caller.is_bool == callee.is_bool &&
           (width(caller) != 1 || caller.is_bool || caller.is_unsigned == callee.is_unsigned);
}

static int lp_tail_wrapper(LpUnit *u, Function *f, size_t at)
{
    unsigned first = 0, i;
    int long_return = lp_state.parser->long_return;
    const char *call_op = long_return ? "jsl" : "jsr", *jump_op = long_return ? "jml" : "jmp";
    int changed = 0, *depths, saved_y, known_depths;

    (void)at;

    if (u->indirect || f->symbol->interrupt || frame_address_visible(f->body) || f->aggregate_abi ||
        structure_object(f->symbol->type) || reg_width(f->symbol->type) > 4)
        return 0;

    while (first < u->count && !u->lines[first].op) {
        ++first;
    }

    if (first == u->count || u->lines[first].x8)
        return 0;

    saved_y = lp_line_is(&u->lines[first], "phy");
    depths = allocate(u->count * sizeof *depths);
    known_depths = lp_stack_depths(u, first, depths);

    if (saved_y && known_depths)
        for (i = first + 1; i < u->count; ++i) {
            if (depths[i] == 0 && u->lines[i].op && !lp_line_is(&u->lines[i], "rtl") &&
                !lp_line_is(&u->lines[i], "rts")) {
                saved_y = 0;
                break;
            }
        }

    for (i = first; i < u->count; ++i) {
        LpLine *call = &u->lines[i];
        const char *name;
        size_t length;

        unsigned j, pulls = 0;
        int k, last_y = 0;
        Symbol *callee = NULL;

        if (!lp_is(call, call_op) || call->m8 || call->x8)
            continue;

        name = lp_operand(call, &length);

        if (!long_return &&
            (length <= 9 || strncmp(name, ".loword(", 8) || name[length - 1] != ')'))
            continue;

        callee = lp_callee(call);

        if (!callee || callee->variadic || callee->param_count < 0 ||
            !lp_tail_return_compatible(f->symbol->type, callee->type))
            continue;

        for (j = 0; j < (unsigned)callee->param_count && register_parameter(j, callee->params[j]);
             ++j) {
        }

        if (j != (unsigned)callee->param_count)
            continue;

        k = (int)i + 1;

        for (j = 0; j < 8; ++j) {
            while (k < (int)u->count && !u->lines[k].op) {
                ++k;
            }

            if (k == (int)u->count || !u->lines[k].ends || u->lines[k].target < 0)
                break;

            k = u->lines[k].target;
        }

        /* A Y-based frame's existing release preserves X but uses A.
         * Move that exact release ahead of a call taking zero or one words. */
        if (callee->param_count <= 1 && k < (int)u->count) {
            int saved_result = lp_line_is(&u->lines[k], "tax");
            int start = saved_result ? lp_next(u, (unsigned)k, 1) : k;
            int clc = start >= 0 ? lp_next(u, (unsigned)start, 1) : -1;
            int add = clc >= 0 ? lp_next(u, (unsigned)clc, 1) : -1;
            int tcs = add >= 0 ? lp_next(u, (unsigned)add, 1) : -1;
            int ret = tcs >= 0 ? lp_next(u, (unsigned)tcs, 1) : -1;
            int restore_y;

            if (saved_result && ret >= 0 && lp_line_is(&u->lines[ret], "txa"))
                ret = lp_next(u, (unsigned)ret, 1);
            else if (saved_result)
                ret = -1;

            restore_y = ret >= 0 && lp_line_is(&u->lines[ret], "ply");

            if (restore_y)
                ret = lp_next(u, (unsigned)ret, 1);

            if (ret >= 0 && !u->lines[start].m8 &&
                (lp_line_is(&u->lines[start], "tsc") ||
                 (restore_y && lp_line_is(&u->lines[start], "tya"))) &&
                lp_line_is(&u->lines[clc], "clc") && lp_is(&u->lines[add], "adc") &&
                lp_immediate(&u->lines[add]) > 0 && lp_line_is(&u->lines[tcs], "tcs") &&
                (lp_line_is(&u->lines[ret], "rts") ||
                 (long_return && lp_line_is(&u->lines[ret], "rtl")))) {
                lp_set(call, "    %.3s\n    clc\n%.*s\n    tcs\n%s    %s %.*s", u->lines[start].op,
                       (int)u->lines[add].length, u->lines[add].text, restore_y ? "    ply\n" : "",
                       jump_op, (int)length, name);
                ++changed;
                continue;
            }
        }

        if (!known_depths || depths[i] < 0 || depths[i] > 8)
            continue;

        for (; k < (int)u->count; ++k) {
            LpLine *l = &u->lines[k];

            if (!l->op)
                continue;
            if (l->x8 || last_y)
                break;
            if (lp_line_is(l, "plx") || (lp_line_is(l, "pla") && !l->m8)) {
                ++pulls;
                continue;
            }
            if (lp_line_is(l, "ply")) {
                ++pulls;
                last_y = 1;
                continue;
            }

            break;
        }

        if (callee == f->symbol && callee->param_count == 2 && !last_y && pulls == 2 &&
            depths[i] == 4 && k < (int)u->count &&
            (lp_line_is(&u->lines[k], "rts") || lp_line_is(&u->lines[k], "rtl")) &&
            lp_line_is(&u->lines[first], "pha")) {
            int second = lp_next(u, first, 1);
            int body = second >= 0 ? lp_next(u, (unsigned)second, 1) : -1;

            if (body >= 0 && lp_line_is(&u->lines[second], "phx")) {
                lp_liveness(u);

                if (!(u->lines[body].live & (LP_N | LP_Z))) {
                    /* The recursive edge reuses the existing argument frame.
                     * Preserve A when the entry body consumes its register value. */
                    char entry[128];

                    unsigned target = lp_next_label();
                    snprintf(entry, sizeof entry, "cg_%s_%u = *\n", lp_state.parser->unit, target);
                    lp_insert(&u->lines[body], entry);
                    int same_x = lp_first_parameter_in_x(u, i);

                    lp_set(call, "    sta 3,s\n%s%s    jmp cg_%s_%u",
                           same_x ? "" : "    txa\n    sta 1,s\n",
                           !same_x && (u->lines[body].live & LP_A) ? "    lda 3,s\n" : "",
                           lp_state.parser->unit, target);
                    ++changed;
                    continue;
                }
            }
        }

        if ((last_y && saved_y) || !depths[i] || (!last_y && callee->param_count <= 1)) {
            while (k < (int)u->count && !u->lines[k].op) {
                ++k;
            }

            if (k < (int)u->count &&
                (lp_line_is(&u->lines[k], "rts") ||
                 (long_return && lp_line_is(&u->lines[k], "rtl"))) &&
                2 * pulls == (unsigned)depths[i]) {
                char restore[40] = "";

                for (j = 0; j < pulls; ++j) {
                    strcat(restore, last_y ? "    ply\n" : "    pla\n");
                }

                lp_set(call, "%s    %s %.*s", restore, jump_op, (int)length, name);
                ++changed;
            }
        }
    }

    free(depths);
    return changed;
}

/* Keep an incoming X parameter in X when its frame home is read-only
 * and the body never uses X for anything else. Preserve it around ordinary
 * calls. Keep a second parameter in scratch if all uses precede calls,
 * otherwise give it one stack-relative word. */
static int lp_register_parameter_frame(LpUnit *u, Function *f, size_t at)
{
    Symbol *s = f->symbol;

    unsigned entry = 0, i, frame;
    int save_a, save_x, base, ready, *depths, ok = 0, dp_a, reads_a = 0, call_seen = 0, stack_only;

    (void)at;

    if (s->param_count < 1 || s->param_count > 2 || s->variadic || u->indirect || u->helpers ||
        statement_inline_markers(f->body) || !register_parameter(0, s->params[0]) ||
        (s->param_count == 2 && !register_parameter(1, s->params[1])))
        return 0;

    while (entry < u->count && !u->lines[entry].op) {
        ++entry;
    }

    if (entry == u->count || u->lines[entry].x8)
        return 0;

    stack_only = s->param_count == 1 && lp_line_is(&u->lines[entry], "phx");

    if (!stack_only && !lp_line_is(&u->lines[entry], "phy"))
        return 0;

    save_a = s->param_count == 2 ? lp_next(u, entry, 1) : -1;

    if (s->param_count == 2 &&
        (save_a < 0 || !lp_line_is(&u->lines[save_a], "pha") || u->lines[save_a].m8))
        return 0;

    save_x = stack_only ? (int)entry : lp_next(u, save_a >= 0 ? (unsigned)save_a : entry, 1);

    if (save_x < 0 || !lp_line_is(&u->lines[save_x], "phx"))
        return 0;

    base = stack_only ? save_x : lp_next(u, (unsigned)save_x, 1);

    if (base < 0 || (!stack_only && !lp_line_is(&u->lines[base], "tsc")))
        return 0;

    ready = stack_only ? base : lp_next(u, (unsigned)base, 1);

    if (ready < 0 || (!stack_only && !lp_line_is(&u->lines[ready], "tay")))
        return 0;

    frame = stack_only ? 2 : save_a >= 0 ? 6 : 4;
    depths = allocate(u->count * sizeof *depths);

    if (!lp_stack_depths(u, entry, depths))
        goto done;

    for (i = (unsigned)ready + 1; i < u->count; ++i) {
        if (lp_line_is(&u->lines[i], "sep #$20") || lp_line_is(&u->lines[i], "rep #$20"))
            u->lines[i].use = 0;
    }

    lp_liveness(u);

    if (!stack_only && (u->lines[ready].out & (LP_A | LP_N | LP_Z)))
        goto done;

    dp_a = save_a >= 0 && !lp_state.parser->no_dp_homes &&
           !(lp_text_words(u->text, u->text + strlen(u->text)) & 1);

    for (i = (unsigned)ready + 1; dp_a && i < u->count; ++i) {
        LpLine *l = &u->lines[i];

        if (!l->op || depths[i] < 0)
            continue;
        if (l->target >= 0 && (unsigned)l->target <= i)
            dp_a = 0;
        if (l->call)
            call_seen = 1;

        if (lp_line_is(l, "lda a:$0003,y") &&
            (lp_next(u, (unsigned)ready, 1) != (int)i || l->out & (LP_N | LP_Z))) {
            ++reads_a;

            if (call_seen)
                dp_a = 0;
        }
    }

    for (i = (unsigned)ready + 1; i < u->count; ++i) {
        LpLine *l = &u->lines[i];
        const char *operand;
        size_t length;
        int next;

        if (!l->op || depths[i] < 0)
            continue;
        if (l->target >= 0 && l->target <= ready)
            goto done;
        if (lp_line_is(l, "rts") || lp_line_is(l, "rtl") ||
            (l->ends && (l->call || l->target < 0))) {
            if (depths[i] != 0)
                goto done;

            continue;
        }

        if (stack_only && (lp_line_is(l, "pla") || lp_line_is(l, "plx"))) {
            Symbol *callee;

            next = lp_next(u, i, 1);

            if (next < 0 || depths[i] != 2 || l->m8)
                goto done;

            callee = lp_callee(&u->lines[next]);

            if (lp_line_is(l, "pla") && (!u->lines[next].ends || !callee ||
                                         callee->param_count < 0 || callee->param_count > 1))
                goto done;
            if (lp_line_is(l, "plx") && !lp_line_is(&u->lines[next], "rts") &&
                !lp_line_is(&u->lines[next], "rtl"))
                goto done;

            l->deleted = 1;
            continue;
        }

        if (lp_line_is(l, "ply") || lp_line_is(l, "plx")) {
            next = lp_next(u, i, 1);

            if (l->x8 || depths[i] <= 0 || depths[i] > (int)frame || next < 0 ||
                (depths[i] > 2 && !lp_line_is(&u->lines[next], "plx") &&
                 !lp_line_is(&u->lines[next], "ply")) ||
                (depths[i] == 2 &&
                 (!lp_line_is(l, "ply") ||
                  !(lp_line_is(&u->lines[next], "rts") || lp_line_is(&u->lines[next], "rtl") ||
                    (u->lines[next].ends && (u->lines[next].call || u->lines[next].target < 0))))))
                goto done;
            if (save_a < 0 || dp_a || depths[i] == (int)frame)
                l->deleted = 1;

            continue;
        }

        if (depths[i] != (int)frame || l->x8)
            goto done;
        if (l->call) {
            if (l->out & (LP_X | LP_N | LP_Z))
                goto done;

            lp_set(l, "    phx\n%.*s\n    plx", (int)l->length, l->text);
            continue;
        }
        if (lp_stack_op(l))
            goto done;
        if (lp_line_is(l, "ldx a:$0001,y")) {
            if (l->out & (LP_N | LP_Z))
                goto done;

            l->deleted = 1;
            continue;
        }

        if (lp_line_is(l, stack_only ? "lda 1,s" : "lda a:$0001,y") && !l->m8) {
            next = lp_next(u, i, 1);

            if (next >= 0 && lp_line_is(&u->lines[next], "tax") && !u->lines[next].x8) {
                /* X still holds this argument. Keep TXA only for A or N/Z */
                if (u->lines[next].out & (LP_A | LP_N | LP_Z))
                    lp_set(l, "    txa");
                else
                    l->deleted = 1;

                u->lines[next].deleted = 1;
                i = (unsigned)next;
            } else
                lp_set(l, "    txa");

            continue;
        }

        if (save_a >= 0 && lp_line_is(l, "lda a:$0003,y") && !l->m8) {
            if (lp_next(u, (unsigned)ready, 1) == (int)i && !(l->out & (LP_N | LP_Z)))
                l->deleted = 1;
            else
                lp_set(l, dp_a ? "    lda z:__arith_lhs" : "    lda 1,s");

            continue;
        }

        operand = lp_operand(l, &length);

        if (l->def & LP_X) {
            int previous = lp_next(u, i, -1);

            if (lp_line_is(l, "tax") && !l->m8 && previous >= 0 &&
                lp_line_is(&u->lines[previous], "txa")) {
                l->deleted = 1;
                continue;
            }

            /* A final argument may replace the incoming X immediately
             * before a validated cleanup and terminal transfer. */
            next = lp_next(u, i, 1);

            while (next >= 0 &&
                   (lp_line_is(&u->lines[next], "ply") || lp_line_is(&u->lines[next], "plx") ||
                    (stack_only && lp_line_is(&u->lines[next], "pla")))) {
                next = lp_next(u, (unsigned)next, 1);
            }

            if (next < 0 || !u->lines[next].ends ||
                (!u->lines[next].call && u->lines[next].target >= 0))
                goto done;
        }

        if ((l->def & LP_Y) || (l->use & LP_Y) || lp_line_is(l, "tsc") ||
            (length >= 2 && operand[length - 2] == ',' && operand[length - 1] == 's') ||
            (l->use == LP_ALL && !lp_line_is(l, "sep #$20") && !lp_line_is(l, "rep #$20")))
            goto done;
    }

    if (save_a < 0 || dp_a)
        u->lines[entry].deleted = 1;

    if (dp_a) {
        if (reads_a) {
            lp_set(&u->lines[save_a], "    sta z:__arith_lhs");
            lp_mark_arithmetic();
        } else
            u->lines[save_a].deleted = 1;
    }

    u->lines[save_x].deleted = u->lines[base].deleted = u->lines[ready].deleted = 1;
    ok = 1;
done:
    free(depths);
    return ok;
}

static int lp_store_zero_operand(const LpLine *store, const char **operand, size_t *length, int m8)
{
    if (!lp_is(store, "sta") || store->m8 != m8 || store->deleted || store->replace)
        return 0;

    *operand = lp_operand(store, length);
    return *length >= 3 && (!strncmp(*operand, "a:", 2) || !strncmp(*operand, "z:", 2)) &&
           !(*length >= 2 && (*operand)[*length - 2] == ',' && (*operand)[*length - 1] != 'x');
}

static int lp_store_zero(LpUnit *u, Function *f, size_t at)
{
    unsigned i;
    int changed = 0;

    (void)f;
    (void)at;

    lp_liveness(u);

    for (i = 0; i < u->count; ++i) {
        LpLine *load = &u->lines[i];
        int k, last = -1, m8 = load->m8;
        const char *operand;
        size_t length;

        unsigned live_mask = m8 ? (LP_A | LP_AL | LP_N | LP_Z) : (LP_A | LP_N | LP_Z);

        if (!lp_is(load, "lda") || load->deleted || load->replace || lp_immediate(load) != 0)
            continue;

        k = lp_next(u, i, 1);

        if (!m8 && k >= 0 && lp_line_is(&u->lines[k], "sep #$20") && (unsigned)k + 1 < u->count &&
            !u->lines[k + 1].deleted && u->lines[k + 1].length == 3 &&
            !strncmp(u->lines[k + 1].text, ".a8", 3)) {
            m8 = 1;
            k = lp_next(u, (unsigned)(k + 1), 1);
            live_mask = LP_A | LP_AL | LP_N | LP_Z;
        }

        if (k < 0)
            continue;

        for (; k >= 0 && (unsigned)k < u->count; k = lp_next(u, (unsigned)k, 1)) {
            if (!lp_store_zero_operand(&u->lines[k], &operand, &length, m8))
                break;

            last = k;

            if (!(u->lines[k].out & live_mask))
                break;
        }

        if (last < 0 || (u->lines[last].out & live_mask))
            continue;

        for (k = (int)i + 1; k <= last; ++k) {
            LpLine *store = &u->lines[k];

            if (lp_store_zero_operand(store, &operand, &length, m8))
                lp_set(store, "    stz %.*s", (int)length, operand);
        }

        load->deleted = 1;
        ++changed;
    }

    return changed;
}

/* Relocate a call-free stack-relative frame to unused DP words. No
 * transfer is folded, so volatile stack accesses retain their width and
 * order. A tail call may clobber the relocated locals after the last use. */
static int lp_closed_frame(LpUnit *u, Function *f, size_t at)
{
    unsigned entry = 0, i, slot, words, used;
    int sec, sub, ready;
    long size;

    (void)at;

    if (lp_state.parser->no_dp_homes || u->indirect || f->symbol->param_count != 0 ||
        f->symbol->type.base != TY_VOID || f->symbol->type.pointers)
        return 0;

    while (entry < u->count && !u->lines[entry].op) {
        ++entry;
    }

    if (entry == u->count || !lp_line_is(&u->lines[entry], "tsc"))
        return 0;

    sec = lp_next(u, entry, 1);
    sub = sec >= 0 ? lp_next(u, (unsigned)sec, 1) : -1;
    ready = sub >= 0 ? lp_next(u, (unsigned)sub, 1) : -1;

    if (ready < 0 || !lp_line_is(&u->lines[sec], "sec") || !lp_is(&u->lines[sub], "sbc") ||
        (size = lp_immediate(&u->lines[sub])) < 1 || size > 24 ||
        !lp_line_is(&u->lines[ready], "tcs"))
        return 0;

    words = ((unsigned)size + 1) / 2;
    used = lp_text_words(u->text, u->text + strlen(u->text));

    for (slot = 0; slot + words <= 16; ++slot) {
        if (!(used & (((1u << words) - 1u) << slot)))
            break;
    }

    if (slot + words > 16)
        return 0;

    for (i = (unsigned)ready + 1; i < u->count; ++i) {
        if (lp_line_is(&u->lines[i], "sep #$20") || lp_line_is(&u->lines[i], "rep #$20"))
            u->lines[i].use = 0;
    }

    lp_liveness(u);

    if (u->lines[ready].out & (LP_A | LP_FLAGS))
        return 0;

    for (i = (unsigned)ready + 1; i < u->count; ++i) {
        LpLine *l = &u->lines[i];
        const char *p;
        size_t n;

        if (!l->op)
            continue;
        if (l->x8 || (l->call && !l->ends) ||
            ((lp_branch(l) || l->target >= 0) && l->target <= ready))
            return 0;

        if (lp_line_is(l, "tsc")) {
            int clc = lp_next(u, i, 1);
            int add = clc >= 0 ? lp_next(u, (unsigned)clc, 1) : -1;
            int reset = add >= 0 ? lp_next(u, (unsigned)add, 1) : -1;
            int ret = reset >= 0 ? lp_next(u, (unsigned)reset, 1) : -1;
            int saved_result = ret >= 0 && lp_line_is(&u->lines[ret], "txa");
            int previous = lp_next(u, i, -1);

            if (saved_result)
                ret = lp_next(u, (unsigned)ret, 1);
            if (ret < 0 || l->m8 || !lp_line_is(&u->lines[clc], "clc") ||
                !lp_is(&u->lines[add], "adc") || lp_immediate(&u->lines[add]) != size ||
                !lp_line_is(&u->lines[reset], "tcs") ||
                !(lp_line_is(&u->lines[ret], "rts") || lp_line_is(&u->lines[ret], "rtl") ||
                  (u->lines[ret].ends && u->lines[ret].call)))
                return 0;

            if (saved_result) {
                int after = lp_next(u, (unsigned)reset, 1);

                if (previous < 0 || !lp_line_is(&u->lines[previous], "tax") ||
                    (u->lines[ret].ends && u->lines[ret].call))
                    return 0;

                u->lines[previous].deleted = u->lines[after].deleted = 1;
            }

            l->deleted = u->lines[clc].deleted = u->lines[add].deleted = u->lines[reset].deleted =
                1;
            i = (unsigned)ret;
            continue;
        }

        if (lp_stack_op(l) || lp_is(l, "tsx"))
            return 0;

        p = lp_operand(l, &n);

        if (n >= 2 && p[n - 2] == ',' && p[n - 1] == 's') {
            char *end;
            long offset = strtol(p, &end, 10);

            if (end != p + n - 2 || offset < 1 || offset + lp_width(l) - 1 > size ||
                (!lp_is(l, "lda") && !lp_is(l, "sta") && !lp_is(l, "adc") && !lp_is(l, "sbc") &&
                 !lp_is(l, "and") && !lp_is(l, "ora") && !lp_is(l, "eor") && !lp_is(l, "cmp")))
                return 0;

            lp_set(l, "    %.3s z:__arith_lhs+%u", l->op, 2 * slot + (unsigned)offset - 1);
        } else if (l->use == LP_ALL && !lp_line_is(l, "sep #$20") && !lp_line_is(l, "rep #$20"))
            return 0;
    }

    u->lines[entry].deleted = u->lines[sec].deleted = u->lines[sub].deleted =
        u->lines[ready].deleted = 1;
    lp_mark_arithmetic();
    return 1;
}

#include "frame_regions.inc"

/* Keep a saved X in its register through a stack-free dispatch. A tail
 * callee with one register argument needs the adjusted X, but not the PLA
 * that used to release the wrapper's stack word. */
static int lp_tail_index_dispatch(LpUnit *u, Function *f, size_t at)
{
    unsigned first = 0, i;
    int *depth, ok = 0, tails = 0, stack, word;
    const char *saved;
    size_t saved_length = 3;

    (void)at;

    if (u->indirect || lp_state.parser->no_stack_frames || frame_address_visible(f->body) ||
        f->symbol->type.base != TY_VOID || f->symbol->type.pointers)
        return 0;

    while (first < u->count && !u->lines[first].op) {
        ++first;
    }

    if (first == u->count || u->lines[first].x8)
        return 0;

    stack = lp_line_is(&u->lines[first], "phx");
    saved = stack ? "1,s" : lp_operand(&u->lines[first], &saved_length);

    if (stack)
        word = -1;
    else if (!lp_is(&u->lines[first], "stx") ||
             (word = lp_workspace_word(saved, saved_length)) < 0 || (word & 1))
        return 0;

    depth = allocate(u->count * sizeof *depth);

    if (!lp_stack_depths(u, first, depth))
        goto done;

    for (i = first + 1; i < u->count; ++i) {
        LpLine *l = &u->lines[i];
        size_t n;
        const char *operand = lp_operand(l, &n);
        int next;

        if (!l->op)
            continue;
        if (l->m8 || l->x8 || depth[i] < 0 || (l->target >= 0 && (unsigned)l->target <= first))
            goto done;

        next = lp_next(u, i, 1);

        if (stack && lp_line_is(l, "plx") && depth[i] == 2 && next >= 0 &&
            (lp_is(&u->lines[next], "rts") || lp_is(&u->lines[next], "rtl"))) {
            l->deleted = 1;
            i = (unsigned)next;
        } else if (lp_is(l, "lda") && n > 1 && operand[0] == '#' && depth[i] == 2 * stack) {
            int add = next >= 0 ? lp_next(u, (unsigned)next, 1) : -1;
            int tax = add >= 0 ? lp_next(u, (unsigned)add, 1) : -1;
            int after = tax >= 0 ? lp_next(u, (unsigned)tax, 1) : -1;
            int jump = stack && after >= 0 ? lp_next(u, (unsigned)after, 1) : after;
            Symbol *callee = jump >= 0 ? lp_callee(&u->lines[jump]) : NULL;

            if (!callee || callee->interrupt || callee->variadic || callee->param_count != 1 ||
                !register_parameter(0, callee->params[0]) || !u->lines[jump].ends ||
                !u->lines[jump].call || !lp_line_is(&u->lines[next], "clc") ||
                !lp_is(&u->lines[add], "adc") ||
                !lp_operand_is(&u->lines[add], saved, saved_length) ||
                !lp_line_is(&u->lines[tax], "tax") ||
                (stack && !lp_line_is(&u->lines[after], "pla")))
                continue;

            lp_set(l, "    txa");
            lp_set(&u->lines[add], "    adc %.*s", (int)n, operand);

            if (stack)
                u->lines[after].deleted = 1;

            i = (unsigned)jump;
            ++tails;
        } else if (!stack && (lp_is(l, "rts") || lp_is(l, "rtl"))) {
            continue;
        } else if (depth[i] != 2 * stack || lp_stack_op(l) || lp_is(l, "tsx") || lp_is(l, "tsc") ||
                   (l->def & LP_X) || l->use == LP_ALL || (lp_branch(l) && l->target < 0) ||
                   (!stack && (lp_text_words(operand, operand + n) & (1u << (word / 2)))) ||
                   (n >= 2 && operand[n - 2] == ',' && operand[n - 1] == 's') ||
                   (n >= 5 && !memcmp(operand + n - 5, ",s),y", 5)))
            goto done;
    }

    if (tails) {
        u->lines[first].deleted = 1;
        ok = 1;
    }

done:
    free(depth);
    return ok;
}

typedef struct {
    char mem[4][64], imm[4][64];
    signed char eq[4];
    unsigned count, valid;
} LpFactSet;

static void lp_fact_kill(LpFactSet *f, const LpLine *l)
{
    unsigned i = 0;

    if (!l->op || l->deleted)
        return;
    if (l->call || l->use == LP_ALL) {
        f->count = 0;
        return;
    }

    while (i < f->count) {
        size_t n = strlen(f->mem[i]);

        if (lp_may_write(l, f->mem[i], n, 2) ||
            (n >= 2 && f->mem[i][n - 2] == ',' && f->mem[i][n - 1] == 's' && lp_stack_op(l))) {
            f->count--;

            if (i < f->count) {
                memcpy(f->mem[i], f->mem[f->count], 64);
                memcpy(f->imm[i], f->imm[f->count], 64);
                f->eq[i] = f->eq[f->count];
            }
        } else
            ++i;
    }
}

static void lp_fact_set(LpFactSet *f, const char *mem, const char *imm, int eq)
{
    unsigned i;

    for (i = 0; i < f->count; ++i) {
        if (!strcmp(f->mem[i], mem) && !strcmp(f->imm[i], imm)) {
            f->eq[i] = (signed char)eq;
            return;
        }
    }

    if (f->count < 4) {
        snprintf(f->mem[f->count], 64, "%s", mem);
        snprintf(f->imm[f->count], 64, "%s", imm);
        f->eq[f->count] = (signed char)eq;
        ++f->count;
    }
}

static void lp_fact_meet(LpFactSet *dst, const LpFactSet *src)
{
    unsigned i = 0, j;

    if (!src->valid)
        return;
    if (!dst->valid) {
        *dst = *src;
        return;
    }

    while (i < dst->count) {
        for (j = 0; j < src->count; ++j) {
            if (!strcmp(dst->mem[i], src->mem[j]) && !strcmp(dst->imm[i], src->imm[j]) &&
                dst->eq[i] == src->eq[j])
                break;
        }

        if (j == src->count) {
            dst->count--;

            if (i < dst->count) {
                memcpy(dst->mem[i], dst->mem[dst->count], 64);
                memcpy(dst->imm[i], dst->imm[dst->count], 64);
                dst->eq[i] = dst->eq[dst->count];
            }
        } else
            ++i;
    }
}

static int lp_first_code(const LpUnit *u, unsigned k)
{
    while (k < u->count) {
        if (u->lines[k].deleted || u->lines[k].label || !u->lines[k].op) {
            ++k;
            continue;
        }

        return (int)k;
    }

    return (int)u->count;
}

static int lp_next_in_block(const LpUnit *u, unsigned k)
{
    while (++k < u->count) {
        if (u->lines[k].deleted)
            continue;
        if (u->lines[k].label || !u->lines[k].length)
            return -1;
        if (u->lines[k].text[0] == ';')
            continue;

        return u->lines[k].op ? (int)k : -1;
    }

    return -1;
}

static int lp_label_name_at(const LpUnit *u, unsigned k, char *out, size_t out_sz)
{
    while (k < u->count) {
        const LpLine *l = &u->lines[k];

        if (l->deleted) {
            ++k;
            continue;
        }

        if (l->label) {
            size_t len = l->length;

            if (len >= 4 && !strncmp(l->text + len - 4, " = *", 4))
                len -= 4;
            else if (len >= 1 && l->text[len - 1] == ':')
                --len;

            if (len > 3 && !strncmp(l->text, "cg_", 3) && len < out_sz) {
                memcpy(out, l->text, len);
                out[len] = 0;
                return 1;
            }

            ++k;
            continue;
        }

        if (!l->op) {
            ++k;
            continue;
        }

        break;
    }

    return 0;
}

static int lp_match_test_at(const LpUnit *u, unsigned start, char *mem, char *imm, int *eq_line,
                            int *ne_line, int *end_line)
{
    int k0 = lp_first_code(u, start), k1, kb, kj;
    const LpLine *l0, *lc, *lb, *lj;
    size_t n;
    const char *o;

    if (k0 >= (int)u->count)
        return 0;

    l0 = &u->lines[k0];

    if (!lp_is(l0, "lda") || l0->m8 || l0->deleted || l0->replace || lp_index_use(l0))
        return 0;

    o = lp_operand(l0, &n);

    if (!n || n >= 64 || o[0] == '#' || o[0] == '(' || o[0] == '[' || !strncmp(o, "f:$", 3))
        return 0;
    if (lp_state.is_volatile && !lp_private(o, n))
        return 0;

    memcpy(mem, o, n);
    mem[n] = 0;
    k1 = lp_next_in_block(u, (unsigned)k0);

    if (k1 < 0)
        return 0;

    lc = &u->lines[k1];

    if (lp_is(lc, "cmp")) {
        if (lc->m8 || lc->deleted || lc->replace)
            return 0;

        o = lp_operand(lc, &n);

        if (!n || n >= 64 || o[0] != '#')
            return 0;

        memcpy(imm, o, n);
        imm[n] = 0;
        kb = lp_next_in_block(u, (unsigned)k1);

        if (kb < 0)
            return 0;
    } else {
        strcpy(imm, "#0");
        kb = k1;
    }

    lb = &u->lines[kb];

    if ((!lp_is(lb, "beq") && !lp_is(lb, "bne")) || lb->deleted || lb->replace || lb->target < 0)
        return 0;

    if (u->lines[lb->target].length == 1 && u->lines[lb->target].text[0] == ':') {
        int colon = lb->target;

        kj = lp_next_in_block(u, (unsigned)kb);

        if (kj < 0 || kj >= colon)
            return 0;

        lj = &u->lines[kj];

        if (!lp_is(lj, "jmp") || lj->deleted || lj->replace || lj->target < 0)
            return 0;
        if (lp_next_in_block(u, (unsigned)kj) >= 0)
            return 0;

        if (lp_is(lb, "bne")) {
            *eq_line = lj->target;
            *ne_line = colon + 1;
        } else {
            *eq_line = colon + 1;
            *ne_line = lj->target;
        }

        *end_line = colon;
        return 1;
    }

    if (lp_is(lb, "beq")) {
        *eq_line = lb->target;
        *ne_line = kb + 1;
    } else {
        *ne_line = lb->target;
        *eq_line = kb + 1;
    }

    *end_line = kb;
    return 1;
}

static int lp_jump_threading(LpUnit *u, Function *f, size_t at)
{
    LpFactSet *in, *out, *branch_out;

    unsigned i;
    int changed = 0, iter, step_changed = 0;

    (void)f;
    (void)at;

    if (!u->count)
        return 0;

    in = allocate(u->count * sizeof *in);
    out = allocate(u->count * sizeof *out);
    branch_out = allocate(u->count * sizeof *branch_out);
    {
        lp_liveness(u);
        memset(in, 0, u->count * sizeof *in);
        memset(out, 0, u->count * sizeof *out);
        memset(branch_out, 0, u->count * sizeof *branch_out);
        in[0].valid = 1;

        for (iter = 0; iter < 16; ++iter) {
            int diff = 0;

            for (i = 0; i < u->count; ++i) {
                LpLine *l = &u->lines[i];
                LpFactSet cur = {0};

                if (i == 0) {
                    cur.valid = 1;
                } else if (l->label) {
                    int p;

                    if (!u->lines[i - 1].ends && out[i - 1].valid)
                        lp_fact_meet(&cur, &out[i - 1]);

                    for (p = l->first_incoming; p >= 0; p = u->lines[p].next_incoming) {
                        if (u->lines[p].deleted)
                            continue;

                        if (lp_branch(&u->lines[p])) {
                            if (branch_out[p].valid)
                                lp_fact_meet(&cur, &branch_out[p]);
                        } else if (out[p].valid)
                            lp_fact_meet(&cur, &out[p]);
                    }
                } else if (!u->lines[i - 1].ends && out[i - 1].valid) {
                    cur = out[i - 1];
                }

                if (!cur.valid)
                    continue;

                if (memcmp(&in[i], &cur, sizeof cur) != 0) {
                    in[i] = cur;
                    diff = 1;
                }

                {
                    LpFactSet nxt = cur, bout = cur;
                    char mem[64], imm[64];
                    int eq_l, ne_l, end_l;

                    if (lp_match_test_at(u, i, mem, imm, &eq_l, &ne_l, &end_l)) {
                        /* Check conditional branch lines generated inside [i..end_l] below; propagate per-line cleanly */
                    }

                    lp_fact_kill(&nxt, l);
                    lp_fact_kill(&bout, l);

                    /* Look back at cmp/lda right before a conditional branch b */
                    if (!l->deleted && (lp_is(l, "beq") || lp_is(l, "bne"))) {
                        int k1 = (int)i - 1, k0;

                        while (k1 >= 0 && (u->lines[k1].deleted || !u->lines[k1].op)) {
                            --k1;
                        }

                        if (k1 >= 0 && lp_is(&u->lines[k1], "cmp") && !u->lines[k1].m8) {
                            const char *co;
                            size_t cn;

                            co = lp_operand(&u->lines[k1], &cn);
                            k0 = k1 - 1;

                            while (k0 >= 0 && (u->lines[k0].deleted || !u->lines[k0].op)) {
                                --k0;
                            }

                            if (k0 >= 0 && lp_is(&u->lines[k0], "lda") && !u->lines[k0].m8 &&
                                !lp_index_use(&u->lines[k0]) && cn && cn < 64 && co[0] == '#') {
                                size_t mn;
                                const char *mo = lp_operand(&u->lines[k0], &mn);

                                if (mn && mn < 64 && mo[0] != '#' && mo[0] != '(' && mo[0] != '[' &&
                                    strncmp(mo, "f:$", 3) &&
                                    (!lp_state.is_volatile || lp_private(mo, mn))) {
                                    char mb[64], ib[64];

                                    memcpy(mb, mo, mn);
                                    mb[mn] = 0;
                                    memcpy(ib, co, cn);
                                    ib[cn] = 0;
                                    lp_fact_set(&bout, mb, ib, lp_is(l, "beq") ? 1 : 0);
                                    lp_fact_set(&nxt, mb, ib, lp_is(l, "beq") ? 0 : 1);
                                }
                            }
                        } else if (k1 >= 0 && lp_is(&u->lines[k1], "lda") && !u->lines[k1].m8 &&
                                   !lp_index_use(&u->lines[k1])) {
                            size_t mn;
                            const char *mo = lp_operand(&u->lines[k1], &mn);

                            if (mn && mn < 64 && mo[0] != '#' && strncmp(mo, "f:$", 3) &&
                                (!lp_state.is_volatile || lp_private(mo, mn))) {
                                char mb[64];

                                memcpy(mb, mo, mn);
                                mb[mn] = 0;
                                lp_fact_set(&bout, mb, "#0", lp_is(l, "beq") ? 1 : 0);
                                lp_fact_set(&nxt, mb, "#0", lp_is(l, "beq") ? 0 : 1);
                            }
                        }
                    }

                    (void)eq_l;
                    (void)ne_l;
                    (void)end_l;
                    (void)mem;
                    (void)imm;

                    if (memcmp(&out[i], &nxt, sizeof nxt) != 0) {
                        out[i] = nxt;
                        diff = 1;
                    }

                    if (memcmp(&branch_out[i], &bout, sizeof bout) != 0) {
                        branch_out[i] = bout;
                        diff = 1;
                    }
                }
            }

            if (!diff)
                break;
        }

        /* Thread edges targeting redundant conditional tests */
        for (i = 0; i < u->count; ++i) {
            LpLine *l = &u->lines[i];
            const LpFactSet *ef;
            char t_mem[64], t_imm[64], dest_lbl[64], old_lbl[64];
            int eq_l, ne_l, end_l, dest_l, dest_op;

            unsigned j;

            if (l->deleted || !l->op || l->target < 0)
                continue;
            if (!lp_is(l, "jmp") && !lp_is(l, "beq") && !lp_is(l, "bne") && !lp_is(l, "bra"))
                continue;
            if (u->lines[l->target].length == 1 && u->lines[l->target].text[0] == ':')
                continue;

            ef = lp_branch(l) ? &branch_out[i] : &in[i];

            if (!ef->valid)
                continue;
            if (!lp_match_test_at(u, (unsigned)l->target, t_mem, t_imm, &eq_l, &ne_l, &end_l))
                continue;

            for (j = 0; j < ef->count; ++j) {
                if (!strcmp(ef->mem[j], t_mem) && !strcmp(ef->imm[j], t_imm))
                    break;
            }

            if (j == ef->count)
                continue;

            dest_l = ef->eq[j] ? eq_l : ne_l;
            dest_op = lp_first_code(u, (unsigned)dest_l);

            if (dest_op >= (int)u->count)
                continue;
            if (u->lines[dest_op].live & (LP_A | LP_N | LP_Z | LP_C))
                continue;
            if (!lp_label_name_at(u, (unsigned)dest_l, dest_lbl, sizeof dest_lbl))
                continue;
            if (lp_label_name_at(u, (unsigned)l->target, old_lbl, sizeof old_lbl) &&
                !strcmp(old_lbl, dest_lbl))
                continue;

            if (lp_is(l, "jmp"))
                lp_set(l, "    jmp .loword(%s)", dest_lbl);
            else
                lp_set(l, "    %.*s %s", 3, l->op, dest_lbl);

            ++step_changed;
            ++changed;
            break;
        }

        if (!step_changed) {
            for (i = 0; i < u->count; ++i) {
                char t_mem[64], t_imm[64], dest_lbl[64];
                int eq_l, ne_l, end_l, dest_l, dest_op;

                unsigned j, k;

                if (!in[i].valid || u->lines[i].label || u->lines[i].deleted || !u->lines[i].op)
                    continue;
                if (!lp_match_test_at(u, i, t_mem, t_imm, &eq_l, &ne_l, &end_l))
                    continue;
                if (lp_first_code(u, i) != (int)i)
                    continue;

                for (j = 0; j < in[i].count; ++j) {
                    if (!strcmp(in[i].mem[j], t_mem) && !strcmp(in[i].imm[j], t_imm))
                        break;
                }

                if (j == in[i].count)
                    continue;

                dest_l = in[i].eq[j] ? eq_l : ne_l;
                dest_op = lp_first_code(u, (unsigned)dest_l);

                if (dest_op >= (int)u->count)
                    continue;
                if (u->lines[dest_op].live & (LP_A | LP_N | LP_Z | LP_C))
                    continue;

                if (dest_l == end_l + 1) {
                    for (k = i; k <= (unsigned)end_l; ++k) {
                        if (u->lines[k].op)
                            u->lines[k].deleted = 1;
                    }

                    ++step_changed;
                    ++changed;
                    break;
                }

                if (lp_label_name_at(u, (unsigned)dest_l, dest_lbl, sizeof dest_lbl)) {
                    lp_set(&u->lines[i], "    jmp .loword(%s)", dest_lbl);

                    for (k = i + 1; k <= (unsigned)end_l; ++k) {
                        if (u->lines[k].op)
                            u->lines[k].deleted = 1;
                    }

                    ++step_changed;
                    ++changed;
                    break;
                }
            }
        }

        (void)step_changed;
    }
    free(in);
    free(out);
    free(branch_out);
    return changed;
}

static int lp_next_carry(const LpUnit *u, unsigned k)
{
    unsigned i = k;

    while (++i < u->count) {
        const LpLine *l = &u->lines[i];

        if (l->deleted || l->text[0] == ';')
            continue;

        if (l->label) {
            int p, used = 0;

            for (p = l->first_incoming; p >= 0; p = u->lines[p].next_incoming) {
                if (!u->lines[p].deleted) {
                    used = 1;
                    break;
                }
            }

            if (!used)
                continue;

            return -1;
        }

        return l->op ? (int)i : -1;
    }

    return -1;
}

static int lp_reuse_address_carry(LpUnit *u, Function *f, size_t at)
{
    unsigned i;
    int changed = 0;

    (void)f;
    (void)at;

    lp_liveness(u);

    for (i = 0; i < u->count; ++i) {
        LpLine *l0 = &u->lines[i];
        int k, mask1 = -1, clc1, adc1, p, cnt = 0;
        const char *o;
        size_t mn, an;
        char slot[64], imm[64];

        if (l0->deleted || l0->replace || l0->m8 || !lp_is(l0, "lda") || lp_index_use(l0))
            continue;

        o = lp_operand(l0, &mn);

        if (!mn || mn >= 64 || o[0] == '#' || !strncmp(o, "f:$", 3))
            continue;
        if (lp_state.is_volatile && !(mn >= 3 && mn <= 5 && o[mn - 2] == ',' && o[mn - 1] == 's' &&
                                      isdigit((unsigned char)o[0])))
            continue;

        memcpy(slot, o, mn);
        slot[mn] = 0;
        k = lp_next(u, i, 1);

        if (k < 0)
            continue;

        if (lp_is(&u->lines[k], "and") && lp_immediate(&u->lines[k]) == 255 && !u->lines[k].m8 &&
            !u->lines[k].deleted) {
            mask1 = k;
            k = lp_next(u, (unsigned)k, 1);

            if (k < 0)
                continue;
        }

        if (!lp_line_is(&u->lines[k], "clc") || u->lines[k].deleted)
            continue;

        clc1 = k;
        adc1 = lp_next(u, (unsigned)clc1, 1);

        if (adc1 < 0)
            continue;
        if (!lp_is(&u->lines[adc1], "adc") || u->lines[adc1].m8 || u->lines[adc1].deleted ||
            u->lines[adc1].replace)
            continue;

        o = lp_operand(&u->lines[adc1], &an);

        if (!an || an >= 64 || o[0] != '#')
            continue;

        memcpy(imm, o, an);
        imm[an] = 0;
        p = lp_next_carry(u, (unsigned)adc1);

        while (p >= 0 && cnt < 8) {
            LpLine *cur = &u->lines[p];

            if (cur->deleted) {
                p = lp_next_carry(u, (unsigned)p);
                continue;
            }

            if (lp_is(cur, "lda") && lp_operand_is(cur, slot, mn) && !cur->m8 && !cur->replace) {
                int q = lp_next(u, (unsigned)p, 1), end_q;

                if (mask1 >= 0) {
                    if (q < 0 || !lp_is(&u->lines[q], "and") || lp_immediate(&u->lines[q]) != 255 ||
                        u->lines[q].m8)
                        break;

                    q = lp_next(u, (unsigned)q, 1);
                }

                if (q < 0 || !lp_line_is(&u->lines[q], "clc") || u->lines[q].deleted)
                    break;

                end_q = lp_next(u, (unsigned)q, 1);

                if (end_q < 0 || !lp_is(&u->lines[end_q], "adc") || u->lines[end_q].m8 ||
                    u->lines[end_q].deleted || u->lines[end_q].replace)
                    break;

                if (lp_operand_is(&u->lines[end_q], imm, an) &&
                    !(u->lines[end_q].out & (LP_A | LP_N | LP_Z | LP_V))) {
                    int d;

                    for (d = p; d <= end_q; ++d) {
                        if (u->lines[d].op)
                            u->lines[d].deleted = 1;
                    }

                    ++changed;
                    break;
                }

                break;
            }

            if ((cur->def & LP_C) || cur->call || cur->use == LP_ALL || lp_branch(cur) ||
                lp_may_write(cur, slot, mn, 2) ||
                (mn >= 2 && slot[mn - 2] == ',' && slot[mn - 1] == 's' && lp_stack_op(cur)))
                break;
            if (!lp_is(cur, "sta") && !lp_is(cur, "stx") && !lp_is(cur, "sty") &&
                !lp_is(cur, "stz") && !lp_is(cur, "ldx") && !lp_is(cur, "ldy"))
                break;

            ++cnt;
            p = lp_next_carry(u, (unsigned)p);
        }
    }

    return changed;
}

/* Propagate known clear carry only through a closed forward region. A
 * marked ADC was emitted from an unsigned sum whose range fits a word. */
static int lp_reuse_clear_carry(LpUnit *u, Function *f, size_t at)
{
    (void)f;
    (void)at;

    if (u->indirect || lp_state.parser->no_known_values || lp_state.parser->no_strength_reduction)
        return 0;

    for (unsigned i = 1; i < u->count; ++i) {
        LpLine *adc = &u->lines[i];
        int clear;

        if (!lp_is(adc, "adc") || adc->m8 || u->lines[i - 1].length != 18 ||
            strncmp(u->lines[i - 1].text, "; ADC cannot carry", 18))
            continue;

        clear = lp_next(u, i, -1);

        if (clear < 0 || !lp_line_is(&u->lines[clear], "clc"))
            continue;

        for (unsigned j = i + 1; j < u->count; ++j) {
            LpLine *l = &u->lines[j];

            if (l->label && (!lp_fallthrough_label(l) && l->length != 1))
                break;
            if (l->label && !lp_inner_label(u, j, i + 1, j))
                break;
            if (!l->op)
                continue;
            if (lp_line_is(l, "clc")) {
                l->deleted = 1;
                return 1;
            }
            if (l->call || l->indirect || l->use == LP_ALL || (l->def & LP_C) ||
                ((lp_branch(l) || l->ends) && l->target <= (int)j))
                break;
        }
    }

    return 0;
}

static int lp_edge_has_carry(const LpUnit *u, int edge, int set)
{
    const LpLine *branch = &u->lines[edge];
    int test;

    if (lp_is(branch, set ? "bcs" : "bcc"))
        return 1;
    if (!lp_is(branch, "jmp") && !lp_is(branch, "bra") && !lp_is(branch, "brl"))
        return 0;

    test = lp_next(u, (unsigned)edge, -1);

    if (test < 0 || u->lines[test].target <= edge || !lp_is(&u->lines[test], set ? "bcc" : "bcs"))
        return 0;

    for (int i = test + 1; i <= edge; ++i) {
        if (u->lines[i].label && u->lines[i].first_incoming >= 0)
            return 0;
    }

    return 1;
}

/* A branch into a join may already provide its requested carry. Set it on
 * the linear edge alone, before the join's labels, or remove it entirely. */
static int lp_carry_on_fallthrough(LpUnit *u, Function *f, size_t at)
{
    (void)at;

    if (u->indirect || lp_state.parser->no_strength_reduction || body_asm_statements(f->body))
        return 0;

    for (unsigned i = 0; i < u->count; ++i) {
        LpLine *carry = &u->lines[i];
        int join = -1, fall = -1, set = lp_is(carry, "sec");

        if (!set && !lp_is(carry, "clc"))
            continue;

        for (unsigned j = i; j-- > 0;) {
            LpLine *l = &u->lines[j];

            if (l->label) {
                int edge = l->first_incoming;

                for (; edge >= 0; edge = u->lines[edge].next_incoming) {
                    if (!lp_edge_has_carry(u, edge, set))
                        break;
                }

                if (edge >= 0) {
                    join = -1;
                    break;
                }
                if (l->first_incoming >= 0 || join >= 0)
                    join = (int)j;
            } else if (l->op) {
                if (join >= 0) {
                    fall = (int)j;
                    break;
                }
                if (l->call || l->ends || lp_branch(l) || ((l->use | l->def) & LP_C))
                    break;
            } else if (l->length && l->text[0] != ';') {
                join = -1;
                break;
            }
        }

        if (join < 0 || fall < 0)
            continue;
        if (!u->lines[fall].ends)
            lp_insert(&u->lines[join], set ? "    sec\n" : "    clc\n");

        carry->deleted = 1;
        return 1;
    }

    return 0;
}

static int lp_slot_written_byte_clean(const LpUnit *u, const char *slot, unsigned off,
                                      unsigned read_at)
{
    unsigned i;
    int stores = 0, safe_before = 0;
    char adj_lo[16], adj_hi[16];

    snprintf(adj_lo, sizeof adj_lo, "a:$%04X,y", (off - 1) & 0xFFFFu);
    snprintf(adj_hi, sizeof adj_hi, "a:$%04X,y", (off + 1) & 0xFFFFu);

    for (i = 0; i < u->count; ++i) {
        const LpLine *l = &u->lines[i];
        size_t n;
        const char *o;

        if (l->deleted)
            continue;
        if (l->replace)
            return 0;
        if (!l->op)
            continue;

        o = lp_operand(l, &n);

        if (n == 9 && (!strncmp(o, adj_lo, 9) || !strncmp(o, adj_hi, 9)))
            return 0;

        if (lp_store_op(l) && n == 9 && !strncmp(o, slot, 9)) {
            int prev;
            long imm_v;

            if (l->m8)
                return 0;
            if (lp_is(l, "stz")) {
                ++stores;

                if (i < read_at)
                    safe_before = 1;

                continue;
            }
            if (!lp_is(l, "sta"))
                return 0;

            prev = lp_next(u, i, -1);

            if (prev >= 0 && lp_is(&u->lines[prev], "lda") && !u->lines[prev].m8 &&
                (imm_v = lp_immediate(&u->lines[prev])) >= 0 && imm_v <= 255) {
                ++stores;

                if (i < read_at)
                    safe_before = 1;

                continue;
            }

            /* Check all predecessors of the label right before l for lda #imm (<=255) */
            {
                unsigned lbl = i;

                while (lbl > 0 && !u->lines[lbl - 1].op) {
                    --lbl;
                }

                if (lbl > 0 && u->lines[lbl].label) {
                    unsigned p, ok_all = 1, seen = 0;

                    for (p = 0; p < u->count; ++p) {
                        int k;
                        long pv;

                        if (u->lines[p].deleted || !u->lines[p].op)
                            continue;

                        if (p + 1 == lbl && !u->lines[p].ends) {
                            k = (int)p;
                        } else if (u->lines[p].target == (int)lbl &&
                                   (op_is(u->lines[p].op, "bra") || op_is(u->lines[p].op, "jmp"))) {
                            k = lp_next(u, p, -1);
                        } else
                            continue;

                        if (k < 0 || !lp_is(&u->lines[k], "lda") || u->lines[k].m8 ||
                            (pv = lp_immediate(&u->lines[k])) < 0 || pv > 255) {
                            ok_all = 0;
                            break;
                        }

                        seen = 1;
                    }

                    if (ok_all && seen) {
                        ++stores;

                        if (i < read_at)
                            safe_before = 1;

                        continue;
                    }
                }
            }
            return 0;
        }
    }

    /* Ensure no control flow falls from entry without at least one prior write visible before loop/read */
    (void)safe_before;
    return stores > 0;
}

static int lp_next_skip_modes(const LpUnit *u, unsigned k, int *mode_line)
{
    unsigned i = k;

    if (mode_line)
        *mode_line = -1;

    while (++i < u->count) {
        const LpLine *l = &u->lines[i];

        if (l->deleted)
            continue;
        if (!l->length)
            return -1;
        if (l->text[0] == ';')
            continue;
        if (!l->op && ((l->length == 3 && !strncmp(l->text, ".a8", 3)) ||
                       (l->length == 4 && !strncmp(l->text, ".a16", 4)))) {
            if (mode_line && *mode_line < 0)
                *mode_line = (int)i;

            continue;
        }

        return l->op ? (int)i : -1;
    }

    return -1;
}

static int lp_bool_slot_test(LpUnit *u, Function *f, size_t at)
{
    unsigned i;
    int changed = 0;

    (void)f;
    (void)at;

    if (lp_state.is_volatile || lp_state.frame_address || u->indirect)
        return 0;

    lp_liveness(u);

    for (i = 0; i + 3 < u->count; ++i) {
        LpLine *s0 = &u->lines[i];
        int d0 = -1, k1, k2, d1 = -1, k3;

        unsigned off;
        size_t n;
        const char *o;
        char *end;
        char slot[16];

        if (s0->deleted || s0->replace || !lp_line_is(s0, "sep #$20"))
            continue;

        k1 = lp_next_skip_modes(u, i, &d0);

        if (k1 < 0)
            continue;

        k2 = lp_next_skip_modes(u, (unsigned)k1, NULL);

        if (k2 < 0)
            continue;

        k3 = lp_next_skip_modes(u, (unsigned)k2, &d1);

        if (k3 < 0)
            continue;
        if (!lp_is(&u->lines[k1], "lda") || !lp_line_is(&u->lines[k2], "rep #$20") ||
            (!lp_is(&u->lines[k3], "beq") && !lp_is(&u->lines[k3], "bne")))
            continue;
        if (u->lines[k1].deleted || u->lines[k1].replace || u->lines[k2].deleted ||
            u->lines[k2].replace)
            continue;
        if (u->lines[k2].out & (LP_A | LP_N | LP_V | LP_C))
            continue;

        o = lp_operand(&u->lines[k1], &n);

        if (n != 9 || strncmp(o, "a:$", 3) || o[7] != ',' || o[8] != 'y')
            continue;

        off = (unsigned)strtoul(o + 3, &end, 16);

        if (end != o + 7)
            continue;

        memcpy(slot, o, 9);
        slot[9] = 0;

        if (!lp_slot_written_byte_clean(u, slot, off, (unsigned)k1))
            continue;

        s0->deleted = 1;
        u->lines[k2].deleted = 1;

        if (d0 >= 0)
            u->lines[d0].deleted = 1;
        if (d1 >= 0)
            u->lines[d1].deleted = 1;

        u->lines[k1].m8 = 0;
        u->lines[k1].def = LP_A | LP_N | LP_Z;
        ++changed;
    }

    return changed;
}

typedef struct {
    char slot[64];
    unsigned shifts;
    signed char valid;
} LpScaleState;

static int lp_scale_invalidated(const LpLine *l, const char *slot, size_t length)
{
    return lp_may_write(l, slot, length, 2) || (slot[length - 1] == 's' && lp_stack_op(l)) ||
           (slot[length - 1] == 'y' && (l->def & LP_Y)) || lp_is(l, "tcd") || lp_is(l, "pld") ||
           lp_is(l, "plb");
}

static int lp_match_scale_seq(const LpUnit *u, unsigned i, char *slot_out, unsigned *shifts_out,
                              int *tx_out)
{
    const LpLine *l0 = &u->lines[i];
    const char *o;
    size_t mn;
    int k;

    unsigned shifts = 0;

    if (l0->deleted || l0->replace || l0->m8 || !lp_is(l0, "lda") || lp_index_use(l0))
        return 0;

    o = lp_operand(l0, &mn);

    if (!mn || mn >= 64 || !lp_private(o, mn))
        return 0;

    memcpy(slot_out, o, mn);
    slot_out[mn] = 0;
    k = lp_next(u, i, 1);

    while (k >= 0 && shifts < 7 && !u->lines[k].deleted && !u->lines[k].replace &&
           !u->lines[k].m8 && lp_line_is(&u->lines[k], "asl a")) {
        ++shifts;
        k = lp_next(u, (unsigned)k, 1);
    }

    if (!shifts || k < 0 || u->lines[k].deleted || u->lines[k].replace || u->lines[k].x8 ||
        !lp_is(&u->lines[k], "tax"))
        return 0;

    *shifts_out = shifts;
    *tx_out = k;
    return 1;
}

static int lp_cfg_scaled_index(LpUnit *u, Function *f, size_t at)
{
    LpScaleState *in, *out;
    int *plx_src;

    unsigned i;
    int changed = 0, iter;

    (void)f;
    (void)at;

    if (!u->count || u->indirect || lp_state.parser->no_value_reuse)
        return 0;

    lp_liveness(u);
    in = allocate(u->count * sizeof *in);
    out = allocate(u->count * sizeof *out);
    plx_src = allocate(u->count * sizeof *plx_src);

    for (i = 0; i < u->count; ++i) {
        in[i].valid = -1;
        out[i].valid = -1;
        plx_src[i] = -1;
    }

    /* Pair balanced straight-line phx ... plx regions free of non-phx/plx stack ops */
    for (i = 0; i < u->count; ++i) {
        if (!u->lines[i].deleted && lp_is(&u->lines[i], "phx")) {
            int depth = 1;

            unsigned m = i + 1;

            while (m < u->count && depth > 0) {
                const LpLine *cur = &u->lines[m];

                if (!cur->deleted) {
                    if (cur->label || lp_branch(cur) || cur->ends || cur->call ||
                        cur->use == LP_ALL)
                        break;

                    if (cur->op) {
                        if (lp_is(cur, "phx"))
                            ++depth;
                        else if (lp_is(cur, "plx")) {
                            if (--depth == 0) {
                                plx_src[m] = (int)i;
                                break;
                            }
                        } else if (lp_stack_op(cur) || lp_is(cur, "tsx") || lp_is(cur, "tsc"))
                            break;
                    }
                }

                ++m;
            }
        }
    }

    in[0].valid = 0;

    for (iter = 0; iter < 16; ++iter) {
        int diff = 0;

        for (i = 0; i < u->count; ++i) {
            LpScaleState cur = {0};

            cur.valid = -1;

            if (i == 0) {
                cur.valid = 0;
            } else if (u->lines[i].label) {
                int p;

                if (!u->lines[i - 1].ends && out[i - 1].valid >= 0) {
                    cur = out[i - 1];
                }

                for (p = u->lines[i].first_incoming; p >= 0 && cur.valid != 0;
                     p = u->lines[p].next_incoming) {
                    if (u->lines[p].deleted)
                        continue;
                    if (out[p].valid < 0)
                        continue;

                    if (cur.valid < 0)
                        cur = out[p];
                    else if (out[p].valid == 0 || cur.shifts != out[p].shifts ||
                             strcmp(cur.slot, out[p].slot))
                        cur.valid = 0;
                }
            } else if (!u->lines[i - 1].ends) {
                cur = out[i - 1];
            } else {
                cur.valid = 0;
            }

            if (cur.valid < 0)
                continue;

            if (memcmp(&in[i], &cur, sizeof cur) != 0) {
                in[i] = cur;
                diff = 1;
            }

            {
                LpScaleState nxt = cur;
                const LpLine *l = &u->lines[i];

                if (plx_src[i] >= 0) {
                    unsigned phx_i = (unsigned)plx_src[i];

                    if (in[phx_i].valid == 1) {
                        unsigned m;
                        int ok = 1;
                        size_t mn = strlen(in[phx_i].slot);

                        for (m = phx_i + 1; m < i; ++m) {
                            if (!u->lines[m].deleted &&
                                lp_scale_invalidated(&u->lines[m], in[phx_i].slot, mn)) {
                                ok = 0;
                                break;
                            }
                        }

                        if (ok)
                            nxt = in[phx_i];
                        else
                            nxt.valid = 0;
                    } else
                        nxt.valid = 0;
                } else if (!l->deleted && l->op) {
                    if ((l->def & LP_X) || l->call || l->use == LP_ALL) {
                        /* Allow tax ending a scaled sequence to establish new state when reached */
                        nxt.valid = 0;
                    } else if (nxt.valid == 1 &&
                               lp_scale_invalidated(l, nxt.slot, strlen(nxt.slot)))
                        nxt.valid = 0;
                }

                /* If l is `tax`, check if preceded immediately by `lda <slot>; asl^sh; tax`: */
                if (!l->deleted && lp_is(l, "tax") && !l->x8) {
                    int k = lp_next(u, i, -1);

                    unsigned sh2 = 0;

                    while (k >= 0 && lp_line_is(&u->lines[k], "asl a") && !u->lines[k].m8 &&
                           sh2 < 7) {
                        ++sh2;
                        k = lp_next(u, (unsigned)k, -1);
                    }

                    if (sh2 && k >= 0) {
                        int tx;

                        if (lp_match_scale_seq(u, (unsigned)k, nxt.slot, &nxt.shifts, &tx) &&
                            tx == (int)i)
                            nxt.valid = 1;
                    }
                }

                if (memcmp(&out[i], &nxt, sizeof nxt) != 0) {
                    out[i] = nxt;
                    diff = 1;
                }
            }
        }

        if (!diff)
            break;
    }

    for (i = 0; i < u->count; ++i) {
        char slot[64];

        unsigned sh = 0;
        int tx = -1;

        if (in[i].valid != 1)
            continue;
        if (!lp_match_scale_seq(u, i, slot, &sh, &tx))
            continue;
        if (in[i].shifts != sh || strcmp(in[i].slot, slot))
            continue;
        if (u->lines[tx].out & LP_FLAGS)
            continue;

        if (!(u->lines[tx].out & LP_A)) {
            int k;

            for (k = (int)i; k <= tx; ++k) {
                if (u->lines[k].op)
                    u->lines[k].deleted = 1;
            }

            ++changed;
        } else if (sh >= 1) {
            int k;

            for (k = (int)i; k < tx; ++k) {
                if (u->lines[k].op)
                    u->lines[k].deleted = 1;
            }

            lp_set(&u->lines[tx], "    txa");
            ++changed;
        }
    }

    free(in);
    free(out);
    free(plx_src);
    return changed;
}

/* For a discarded postdecrement tested against zero, subtracting one
 * leaves carry set exactly when the previous unsigned bit pattern was
 * nonzero. Store the new word and branch on that same carry. */
static int lp_postdecrement_truth(LpUnit *u, Function *f, size_t at)
{
    (void)at;

    if (lp_state.is_volatile || u->indirect || body_asm_statements(f->body))
        return 0;

    lp_liveness(u);

    for (unsigned i = 0; i < u->count; ++i) {
        LpLine *load = &u->lines[i];

        if (!lp_is(load, "lda") || load->m8)
            continue;

        size_t n;
        const char *home = lp_operand(load, &n);
        int step = lp_next(u, i, 1), test = step < 0 ? -1 : lp_next(u, (unsigned)step, 1);
        int edge = test < 0 ? -1 : lp_next(u, (unsigned)test, 1);

        if (edge < 0 || !lp_is(&u->lines[step], "dec") ||
            !lp_operand_is(&u->lines[step], home, n) || !lp_is(&u->lines[test], "cmp") ||
            lp_immediate(&u->lines[test]) != 0 || n < 2 || home[0] == '#' ||
            lp_is_mmio_operand(home, n))
            continue;

        LpLine *branch = &u->lines[edge];

        if ((!lp_is(branch, "beq") && !lp_is(branch, "bne")) || branch->target < 0 ||
            (branch->out & (LP_A | LP_FLAGS)))
            continue;

        size_t length;
        const char *dest = lp_operand(branch, &length);

        lp_set(&u->lines[step], "    sec\n    sbc #$0001");
        lp_set(&u->lines[test], "    sta %.*s", (int)n, home);
        lp_set(branch, "    %s %.*s", lp_is(branch, "bne") ? "bcs" : "bcc", (int)length, dest);
        return 1;
    }

    return 0;
}

static void lp_cleanup(LpRunner *runner, Function *f, size_t at, int relocated)
{
    static int (*const passes[])(LpUnit *, Function *, size_t) = {lp_region_private_copies,
                                                                  lp_region_dead_stores,
                                                                  lp_forward_constants,
                                                                  lp_dead_workspace,
                                                                  lp_dead_code,
                                                                  lp_dead_push_pairs,
                                                                  lp_fold_steps,
                                                                  lp_y_forms,
                                                                  lp_const_branches,
                                                                  lp_unreachable,
                                                                  lp_push_offsets,
                                                                  lp_ax_reuse,
                                                                  lp_register_values,
                                                                  lp_add_overflow_branch,
                                                                  lp_byte_compare,
                                                                  lp_stack_sum_series};
    unsigned round, k;

    for (round = 0; round < 8; ++round) {
        int any =
            lp_run(runner, f, at, lp_demanded_masks) | lp_run(runner, f, at, lp_byte_region_modes);
        any |= lp_run(runner, f, at, lp_bool_slot_test);
        any |= lp_run(runner, f, at, lp_reuse_address_carry);
        any |= lp_run(runner, f, at, lp_dead_x_save);
        any |= lp_run(runner, f, at, lp_byte_rmw);
        any |= lp_run(runner, f, at, lp_memory_word_steps);
        any |= lp_run(runner, f, at, lp_swapped_word_mask);
        any |= lp_run(runner, f, at, lp_store_index_value);
        any |= lp_run(runner, f, at, lp_near_indirect);

        /* Keep operands in their original order until the stack frame is chosen */
        if (relocated) {
            any |= lp_run(runner, f, at, lp_commute_saved_word);
            any |= lp_run(runner, f, at, lp_forward_named_word);
            any |= lp_run(runner, f, at, lp_test_saved_byte);
            any |= lp_run(runner, f, at, lp_relocated_word_steps);
            any |= lp_run(runner, f, at, lp_sink_word_step);
            any |= lp_run(runner, f, at, lp_boolean_join);
        }

        any |= lp_run(runner, f, at, lp_reloads);
        any |= lp_run(runner, f, at, lp_add_constants);
        any |= lp_run(runner, f, at, lp_private_copies);
        any |= lp_run(runner, f, at, relocated ? lp_relocated_dead_stores : lp_private_dead_stores);

        for (k = 0; k < sizeof passes / sizeof *passes; ++k) {
            any |= lp_run(runner, f, at, passes[k]);
        }

        any |= lp_run(runner, f, at, lp_cfg_accumulator);
        any |= lp_run(runner, f, at, lp_cfg_index);
        any |= lp_run(runner, f, at, lp_reuse_scaled_index);
        any |= lp_run(runner, f, at, lp_cfg_scaled_index);
        any |= lp_run(runner, f, at, lp_advance_before_indexed_load);
        any |= lp_run(runner, f, at, lp_jump_threading);

        if (!any)
            break;
    }
}
