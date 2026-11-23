// Early assembly line passes: loop bounds, reloads, constants, dead code, and Y forms

/* Precomputed loop-exit bounds. Index elimination tests "X - base == k" as
 * TXA/SEC/SBC base/CMP #k; with base invariant in the loop the test is
 * CPX of base+k, computed once ahead of the loop (and of enclosing loops in
 * which base is also invariant) into a free workspace word. The loop's A, C,
 * N and V results of the old test must be dead, its Z is the same. */
static int lp_stop_bounds(LpUnit *u, Function *f, size_t at)
{
    unsigned i, changed = 0, used = lp_text_words(u->text, u->text + strlen(u->text));
    (void)f;
    (void)at;

    lp_liveness(u);

    for (i = 0; i + 2 < u->count; ++i) {
        LpLine *t = &u->lines[i];
        int s1, s2, s3, last, h, word = -1, prev;
        unsigned k = 0, back, free_word, b, sites[8], sites_count, e;
        size_t n;
        const char *o;
        char text[160], pre[256];
        if (!lp_line_is(t, "txa") || t->m8 || t->x8)
            continue;
        if ((s1 = lp_next(u, i, 1)) < 0 || !lp_line_is(&u->lines[s1], "sec"))
            continue;
        if ((s2 = lp_next(u, (unsigned)s1, 1)) < 0 || !lp_is(&u->lines[s2], "sbc"))
            continue;
        last = s2;
        s3 = lp_next(u, (unsigned)s2, 1);
        if (s3 >= 0 && lp_is(&u->lines[s3], "cmp") && !strncmp(u->lines[s3].op, "cmp #$", 6) &&
            u->lines[s3].length == 14) {
            k = (unsigned)strtoul(u->lines[s3].op + 6, NULL, 16);
            last = s3;
        }
        if (u->lines[last].out & (LP_A | LP_N | LP_C | LP_V))
            continue;
        o = lp_operand(&u->lines[s2], &n);
        if (!k && n > 2 && (!strncmp(o, "z:", 2) || !strncmp(o, "a:", 2)) && !memchr(o, ',', n)) {
            /* X - base == 0 needs no precomputed bound at all */
            lp_set(t, "    cpx %.*s", (int)n, o);
            u->lines[s1].deleted = u->lines[s2].deleted = 1;
            ++changed;
            break;
        }

        /* The test must open its loop: only labels and comments before it */
        if ((h = lp_loop(u, i, &back)) < 0 ||
            !lp_entries(u, (unsigned)h, back, sites, &sites_count))
            continue;
        for (prev = h + 1; prev < (int)i && !u->lines[prev].op; ++prev)
            ;
        if (prev != (int)i)
            continue;
        if (n > 1 && o[0] == '#') {
            /* An immediate base needs no workspace */
            if (k)
                lp_set(t, "    cpx #.loword(%.*s+$%04X)", (int)(n - 1), o + 1, k);
            else
                lp_set(t, "    cpx %.*s", (int)n, o);
            u->lines[s1].deleted = u->lines[s2].deleted = 1;
            if (last == s3)
                u->lines[s3].deleted = 1;
            ++changed;
            continue;
        }
        if ((word = lp_workspace_word(o, n)) < 0 || (word & 1))
            continue;
        if (lp_region_writes(u, (unsigned)h, back, o, n, word))
            continue;
        for (free_word = 0; free_word < 16 && (used >> free_word & 1); ++free_word)
            ;
        if (free_word == 16)
            continue;

        /* Hoist past enclosing loops that keep base and give A and flags no meaning */
        b = back;
        for (;;) {
            int up, h2;
            unsigned back2, sites2[8], count2;
            for (up = h - 1; up >= 0 && !u->lines[up].op; --up)
                ;
            if (up < 0)
                break;
            h2 = lp_loop(u, (unsigned)up, &back2);
            if (h2 < 0 || back2 < b || !lp_entries(u, (unsigned)h2, back2, sites2, &count2) ||
                lp_region_writes(u, (unsigned)h2, back2, o, n, word))
                break;
            {
                int first = (int)h2;
                while (first < (int)u->count && !u->lines[first].op)
                    ++first;
                if (first >= (int)u->count || u->lines[first].live & (LP_A | LP_FLAGS))
                    break;
            }
            h = h2;
            b = back2;
            memcpy(sites, sites2, sizeof sites);
            sites_count = count2;
        }
        used |= 1u << free_word;
        snprintf(pre, sizeof pre, "; loop bound %.*s%+d precomputed\n    lda %.*s\n", (int)n, o,
                 (int)(int16_t)k, (int)n, o);
        if (k == 1 || k == 2 || k == 0xFFFF || k == 0xFFFE) {
            unsigned j, c = k < 3 ? k : 0x10000u - k;
            for (j = 0; j < c; ++j)
                strcat(pre, k < 3 ? "    inc a\n" : "    dec a\n");
        } else if (k) {
            snprintf(text, sizeof text, "    clc\n    adc #$%04X\n", k);
            strcat(pre, text);
        }
        snprintf(text, sizeof text, "    sta z:__arith_lhs+%u\n", free_word * 2);
        strcat(pre, text);
        for (e = 0; e < sites_count; ++e)
            lp_insert(&u->lines[sites[e]], pre);
        lp_set(t, "    cpx z:__arith_lhs+%u", free_word * 2);
        u->lines[s1].deleted = u->lines[s2].deleted = 1;
        if (last == s3)
            u->lines[s3].deleted = 1;

        /* At the innermost head CPX now sets N/Z/C and A/V were dead, so the
         * preheader's clobbers are unobserved; enclosing heads were checked. */
        ++changed;
        break; /* one rewrite per analysis; the caller iterates */
    }
    return (int)changed;
}

/* Private storage: the arithmetic workspace, Y-frame slots and N,s slots.
 * No volatile object or escaping address lives there. */
static int lp_private(const char *o, size_t n)
{
    if (lp_workspace_word(o, n) >= 0)
        return 1;
    if (lp_state.is_volatile)
        return 0;
    if (n == 9 && !strncmp(o, "a:$", 3) && o[7] == ',' && o[8] == 'y')
        return 1;
    if (n >= 3 && n <= 5 && o[n - 2] == ',' && o[n - 1] == 's') {
        size_t i;
        for (i = 0; i + 2 < n; ++i)
            if (!isdigit((unsigned char)o[i]))
                return 0;
        return 1;
    }
    return 0;
}

static int lp_stack_op(const LpLine *l)
{
    static const char *const ops[] = {"pha", "phx", "phy", "php", "phb", "phd", "phk",
                                      "pea", "pei", "per", "pla", "plx", "ply", "plp",
                                      "plb", "pld", "tcs", "txs", "rts", "rtl", "rti"};
    unsigned i;

    for (i = 0; i < sizeof ops / sizeof *ops; ++i)
        if (lp_is(l, ops[i]))
            return 1;
    return l->call;
}

/* Could line l change memory operand o (private, spelled once)? */
static const char *lp_near_name(const char *operand, size_t *length);

static size_t lp_named_base(const char **operand, size_t length)
{
    size_t i;
    const char *p = lp_near_name(*operand, &length);

    if (length > 3 && (p[0] == 'z' || p[0] == 'f') && p[1] == ':' && p[2] == '_') {
        p += 2;
        length -= 2;
    }
    if (length < 2 || p[0] != '_')
        return 0;
    *operand = p;
    for (i = 1; i < length && (isalnum((unsigned char)p[i]) || p[i] == '_'); ++i) {
    }
    return i;
}

static int lp_field_displacement(const char *suffix, const char *end)
{
    if (suffix == end)
        return 0;
    if (end - suffix >= 2 && end - suffix <= 6 && suffix[0] == '+' &&
        isdigit((unsigned char)suffix[1])) {
        char *next;
        long offset = strtol(suffix + 1, &next, 10);
        return next == end && offset <= 65535 ? (int)offset : -1;
    }
    if (end - suffix != 6 || strncmp(suffix, "+$", 2) ||
        strspn(suffix + 2, "0123456789abcdefABCDEF") != 4)
        return -1;
    return (int)strtol(suffix + 2, NULL, 16);
}

static int lp_named_word_alias(const char *a, size_t na, const char *b, size_t nb)
{
    if (na < 3 || nb < 3 || strncmp(a, "a:", 2) || strncmp(b, "a:", 2))
        return 0;
    a = lp_near_name(a, &na);
    b = lp_near_name(b, &nb);
    const char *end_a = a + na, *end_b = b + nb;
    size_t name = lp_named_base(&a, na), other = lp_named_base(&b, nb);
    if (!name || name != other || memcmp(a, b, name))
        return 0;
    int first = lp_field_displacement(a + name, end_a);
    return first >= 0 && lp_field_displacement(b + other, end_b) == first;
}

static int lp_frame_slot_escaped(const Function *f, int offset, int bytes)
{
    unsigned i;

    if (!lp_state.frame_address)
        return 0;
    if (!f || f->uses_varargs || f->aggregate_abi)
        return 1;

    for (i = 0; i < lp_state.parser->symbol_count; ++i) {
        const Symbol *v = &lp_state.parser->symbols[i];
        if (v->owner != f->id || !v->offset)
            continue;
        if (!v->address_taken && !v->type.array && !structure_object(v->type) &&
            !loop_escapes(f->body, (Symbol *)v))
            continue;
        int start = (int)frame_offset(v->offset), end = start + (int)width(v->type);
        if (offset < end && offset + bytes > start)
            return 1;
    }
    return 0;
}

static int lp_may_write(const LpLine *l, const char *o, size_t n, int bytes)
{
    size_t m;
    const char *p = lp_operand(l, &m);
    int word = lp_workspace_word(o, n);

    if (l->call || lp_is(l, "mvn") || lp_is(l, "mvp") ||
        (l->use == LP_ALL && !lp_is(l, "rep") && !lp_is(l, "sep")))
        return 1;
    if (!lp_store_op(l))
        return 0;
    if (word >= 0) {
        int w = lp_workspace_word(p, m);
        if (w < 0)
            return (lp_text_words(p, p + m) & (3u << (word / 2))) != 0;
        return lp_overlaps_n(l, w, word, bytes);
    }

    /* Frame and stack slots: the same spelling, a neighbour, or any indexed or indirect store */
    if (m && (p[0] == '(' || p[0] == '[' || (m >= 2 && p[m - 2] == ',' && p[m - 1] == 'x')))
        return 1;
    if (m == n && !strncmp(p, o, n))
        return 1;
    if (n == 9 && m == 9 && !strncmp(p, "a:$", 3) && p[7] == ',' && p[8] == 'y') {
        long a = strtol(o + 3, NULL, 16), b = strtol(p + 3, NULL, 16);
        return lp_overlaps_n(l, (int)b, (int)a, bytes);
    }
    if (o[n - 1] == 's' && m && p[m - 1] == 's') {
        long a = strtol(o, NULL, 10), b = strtol(p, NULL, 10);
        return lp_overlaps_n(l, (int)b, (int)a, bytes);
    }

    /* Literal field displacements on the same absolute object need only
     * invalidate the bytes they overlap. Other same-name spellings may alias. */
    const char *read_end = o + n, *write_end = p + m;
    int absolute =
        n > 11 && m > 11 && !strncmp(o, "a:.loword(_", 11) && !strncmp(p, "a:.loword(_", 11);
    n = lp_named_base(&o, n);
    m = lp_named_base(&p, m);
    if (!n || n != m || memcmp(o, p, n))
        return 0;
    if (absolute && read_end[-1] == ')' && write_end[-1] == ')') {
        int first = lp_field_displacement(o + n, read_end - 1),
            second = lp_field_displacement(p + m, write_end - 1);
        if (first >= 0 && second >= 0 && first + bytes <= 65536 && second + lp_width(l) <= 65536)
            return lp_overlaps_n(l, second, first, bytes);
    }
    return 1;
}

static long lp_immediate(const LpLine *l);

static unsigned char *lp_local_targets(LpUnit *u, int *known_targets)
{
    unsigned i;
    unsigned char *targets = allocate(u->count);

    *known_targets = !u->indirect;
    for (i = 0; i < u->count; ++i) {
        if (u->lines[i].target >= 0) {
            unsigned char *count = &targets[u->lines[i].target];
            if (*count < 2)
                ++*count;
        } else if (lp_branch(&u->lines[i]))
            *known_targets = 0;
    }
    return targets;
}

static int lp_fallthrough_label(const LpLine *l)
{
    return l->label && (!strncmp(l->text, "cg_", 3) || !strncmp(l->text, "__inlined_", 10));
}

/* Skip comments and untargeted fallthrough labels in direction (+1 or -1) */
static int lp_next_fallthrough(const LpUnit *u, unsigned k, int direction,
                               const unsigned char *targets, int known_targets)
{
    unsigned i = k;

    for (;;) {
        if (direction < 0) {
            if (!i)
                return -1;
            --i;
        } else if (++i >= u->count)
            return -1;
        if (!u->lines[i].length)
            return -1;
        if (u->lines[i].text[0] == ';' || !strncmp(u->lines[i].text, ".export __inlined_", 18))
            continue;
        if (known_targets && !targets[i] && lp_fallthrough_label(&u->lines[i]))
            continue;
        return u->lines[i].op ? (int)i : -1;
    }
}

static int pr_named(const char *p, size_t n);

static int lp_flags_from_a(const LpUnit *u, int at)
{
    const LpLine *l;

    if (at < 0)
        return 0;
    l = &u->lines[at];
    return !l->deleted && !l->replace && !l->m8 &&
           (l->def & (LP_A | LP_N | LP_Z)) == (LP_A | LP_N | LP_Z);
}

/* Two adjacent writes of the same register to a private home (or a
 * direct nonvolatile object) produce one value and do not set flags. */
static int lp_duplicate_stores(LpUnit *u, Function *f, size_t at)
{
    int changed = 0;
    (void)at;

    if (lp_state.is_volatile || lp_state.parser->no_value_reuse || body_asm_statements(f->body))
        return 0;

    for (unsigned i = 0; i < u->count; ++i) {
        LpLine *first = &u->lines[i];
        size_t n;
        const char *home = lp_operand(first, &n);
        if ((!lp_is(first, "sta") && !lp_is(first, "stx") && !lp_is(first, "sty") &&
             !lp_is(first, "stz")) ||
            (!lp_private(home, n) && (memchr(home, ',', n) || !pr_named(home, n))))
            continue;
        int next = lp_next(u, i, 1);
        if (next >= 0 && lp_is(&u->lines[next], first->op) &&
            lp_operand_is(&u->lines[next], home, n)) {
            first->deleted = 1;
            ++changed;
        }
    }
    return changed;
}

/* A store immediately after a value-select join inherits N/Z from A
 * if both the fallthrough and every incoming jump carry such a value. */
static int lp_store_flags_from_a(const LpUnit *u, unsigned store)
{
    int prev = lp_next(u, store, -1);

    if (prev >= 0)
        return lp_flags_from_a(u, prev);
    if (u->indirect || !store)
        return 0;
    unsigned j = store;

    while (j) {
        const LpLine *mark = &u->lines[--j];
        if (mark->op)
            return lp_flags_from_a(u, (int)j);
        if (mark->text[0] == ';')
            continue;
        if (!lp_fallthrough_label(mark) &&
            !(mark->label && mark->length == 1 && mark->text[0] == ':'))
            return 0;
        for (int from = mark->first_incoming; from >= 0; from = u->lines[from].next_incoming) {
            if (!u->lines[from].ends || u->lines[from].call ||
                !lp_flags_from_a(u, lp_next(u, (unsigned)from, -1)))
                return 0;
        }
    }
    return 0;
}

/* The emitter uses both spellings for a named near operand */
static const char *lp_near_name(const char *operand, size_t *length)
{
    if (*length > 12 && !strncmp(operand, "a:.loword(_", 11) && operand[*length - 1] == ')') {
        *length -= 11;
        return operand + 10;
    }
    if (*length > 3 && !strncmp(operand, "a:_", 3)) {
        *length -= 2;
        return operand + 2;
    }
    return operand;
}

static int lp_reloads(LpUnit *u, Function *f, size_t at)
{
    unsigned i;
    int changed = 0, known_targets;
    unsigned char *targets = lp_local_targets(u, &known_targets);
    (void)f;
    (void)at;

    lp_liveness(u);

    for (i = 0; i < u->count; ++i) {
        LpLine *s = &u->lines[i], *l;
        int j, prev;
        size_t n, m;
        const char *o, *p;
        if ((lp_line_is(s, "phx") || lp_line_is(s, "pha")) && !s->m8 && !s->x8 &&
            (j = lp_next(u, i, 1)) >= 0 && lp_line_is(&u->lines[j], "lda 1,s") && !u->lines[j].m8 &&
            !u->lines[j].replace && !u->lines[j].deleted) {
            /* The value just pushed is still in X or A */
            if (lp_line_is(s, "phx")) {
                lp_set(&u->lines[j], "    txa");
                ++changed;
            } else if (!(u->lines[j].out & (LP_N | LP_Z))) {
                u->lines[j].deleted = 1;
                ++changed;
            } else if (!(u->lines[j].out & LP_X)) {
                lp_set(&u->lines[j], "    tax");
                ++changed;
            } else if (!(u->lines[j].out & LP_Y)) {
                lp_set(&u->lines[j], "    tay");
                ++changed;
            }
            continue;
        }
        if (!s->op || s->m8 || s->x8 || !(lp_is(s, "sta") || lp_is(s, "stx") || lp_is(s, "sty")))
            continue;
        o = lp_operand(s, &n);
        if (lp_is(s, "sta") && !lp_state.is_volatile && !lp_state.parser->no_value_reuse &&
            (lp_private(o, n) || (!memchr(o, ',', n) && pr_named(o, n))) &&
            (j = lp_next_fallthrough(u, i, 1, targets, known_targets)) >= 0) {
            l = &u->lines[j];
            if (!l->x8 && !l->m8 && !l->replace && !l->deleted && lp_operand_is(l, o, n) &&
                (lp_is(l, "ldx") || lp_is(l, "ldy"))) {
                lp_set(l, lp_is(l, "ldx") ? "    tax" : "    tay");
                ++changed;
                continue;
            }
        }
        if (!lp_state.is_volatile && !lp_state.parser->no_value_reuse &&
            (lp_is(s, "stx") || lp_is(s, "sty")) && pr_named(o, n) &&
            (j = lp_next_fallthrough(u, i, 1, targets, known_targets)) >= 0) {
            l = &u->lines[j];
            p = lp_operand(l, &m);
            if (lp_is(l, "lda") && !l->m8 && !l->replace && !l->deleted &&
                lp_named_word_alias(o, n, p, m)) {
                lp_set(l, lp_is(s, "stx") ? "    txa" : "    tya");
                ++changed;
                continue;
            }
        }
        if (!lp_private(o, n)) {
            size_t name_length = n;
            const char *name;
            if (lp_state.parser->no_value_reuse || !lp_is(s, "sta") || memchr(o, ',', n) ||
                (j = lp_next_fallthrough(u, i, 1, targets, known_targets)) < 0)
                continue;
            l = &u->lines[j];
            if (!lp_is(l, "lda") || l->m8)
                continue;
            name = lp_near_name(o, &name_length);
            p = lp_operand(l, &m);
            p = lp_near_name(p, &m);
            if (name_length == m && !memcmp(name, p, m) && pr_named(o, n) &&
                (!(l->out & (LP_N | LP_Z)) || lp_store_flags_from_a(u, i))) {
                l->deleted = 1;
                ++changed;
            }
            continue;
        }

        /* Redundant A8 zero-test reload of a byte value already zero-extended in A */
        if (lp_is(s, "sta") && (prev = lp_next(u, i, -1)) >= 0 && !u->lines[prev].m8) {
            long pv = lp_immediate(&u->lines[prev]);
            if (pv >= 0 && pv <= 255 &&
                (lp_is(&u->lines[prev], "and") || lp_is(&u->lines[prev], "lda"))) {
                int sep = lp_next_fallthrough(u, i, 1, targets, known_targets);
                if (sep >= 0 && lp_line_is(&u->lines[sep], "sep #$20") &&
                    (unsigned)sep + 1 < u->count && !strncmp(u->lines[sep + 1].text, ".a8", 3) &&
                    u->lines[sep + 1].length == 3) {
                    int load2 = lp_next(u, (unsigned)sep + 1, 1);
                    int rep = load2 >= 0 ? lp_next(u, (unsigned)load2, 1) : -1;
                    if (load2 >= 0 && rep >= 0 && lp_is(&u->lines[load2], "lda") &&
                        lp_operand_is(&u->lines[load2], o, n) &&
                        lp_line_is(&u->lines[rep], "rep #$20") && (unsigned)rep + 1 < u->count &&
                        !strncmp(u->lines[rep + 1].text, ".a16", 4) &&
                        u->lines[rep + 1].length == 4 && !(u->lines[rep].out & (LP_A | LP_N))) {
                        u->lines[sep].deleted = u->lines[sep + 1].deleted =
                            u->lines[load2].deleted = 1;
                        u->lines[rep].deleted = u->lines[rep + 1].deleted = 1;
                        ++changed;
                        continue;
                    }
                }
            }
        }
        j = lp_next_fallthrough(u, i, 1, targets, known_targets);
        if (j < 0)
            continue;
        l = &u->lines[j];
        p = lp_operand(l, &m);
        if (l->m8 || l->x8 || m != n || strncmp(p, o, n) || l->replace || l->deleted)
            continue;
        if (lp_is(l, "lda") && lp_is(s, "sta")) {
            if ((l->out & (LP_N | LP_Z)) && !lp_store_flags_from_a(u, i))
                continue;
            l->deleted = 1;
            ++changed;
        } else if (lp_is(l, "lda")) {
            lp_set(l, lp_is(s, "stx") ? "    txa" : "    tya");
            ++changed;
        } else if (lp_is(l, "ldx")) {
            if (lp_is(s, "stx")) {
                if (l->out & (LP_N | LP_Z))
                    continue;
                l->deleted = 1;
            } else
                lp_set(l, lp_is(s, "sta") ? "    tax" : "    tyx");
            ++changed;
        } else if (lp_is(l, "ldy")) {
            if (lp_is(s, "sty")) {
                if (l->out & (LP_N | LP_Z))
                    continue;
                l->deleted = 1;
            } else
                lp_set(l, lp_is(s, "sta") ? "    tay" : "    txy");
            ++changed;
        }
    }
    free(targets);
    return changed;
}

/* Numeric immediate "#$XXXX" or unsigned decimal "#N" of a line, or -1 */
static long lp_immediate(const LpLine *l)
{
    size_t m;
    const char *p = lp_operand(l, &m);
    char *stop;
    unsigned long v;

    if (m >= 2 && p[0] == '#' && isdigit((unsigned char)p[1])) {
        v = strtoul(p + 1, &stop, 10);
        return stop == p + m && v <= 0xFFFFul ? (long)v : -1;
    }
    if (m < 3 || p[0] != '#' || p[1] != '$')
        return -1;
    v = strtoul(p + 2, &stop, 16);
    return stop == p + m ? (long)v : -1;
}

static int lp_has_immediate(const LpLine *l)
{
    static const char *const ops[] = {"lda", "ldx", "ldy", "adc", "sbc", "cmp",
                                      "cpx", "cpy", "and", "ora", "eor"};
    unsigned i;

    for (i = 0; i < sizeof ops / sizeof *ops; ++i)
        if (lp_is(l, ops[i]))
            return 1;
    return 0;
}

/* A label every branch to which comes from lines [from, to) */
static int lp_inner_label(const LpUnit *u, unsigned k, unsigned from, unsigned to)
{
    unsigned j;

    if (u->indirect)
        return 0;
    if (u->lines[k].length >= 2 && u->lines[k].text[0] == '_' &&
        !lp_fallthrough_label(&u->lines[k]))
        return 0; /* the function's own entry */

    for (j = 0; j < u->count; ++j)
        if (u->lines[j].op && u->lines[j].target == (int)k && (j < from || j >= to))
            return 0;
    return 1;
}

/* Constant store forwarding: after "lda #v / sta M" (or "stz M"), later
 * reads of M along straight-line code (labels only entered from it) use #v
 * while nothing may write M. A byte store also serves a 16-bit read whose
 * high byte an AND #$00FF discards. */
static int lp_forward_constants(LpUnit *u, Function *f, size_t at)
{
    unsigned i;
    int changed = 0, named_ok = !lp_state.parser->no_value_reuse && !lp_state.is_volatile &&
                                !u->indirect && !body_asm_statements(f->body);
    (void)at;

    for (i = 0; i < u->count; ++i) {
        LpLine *s = &u->lines[i];
        size_t n, vn = 0;
        const char *o, *value = NULL;
        unsigned j;
        int y_frame, stack, dead = 0, byte, named;
        long bv = -1;
        char text[16];
        int index_store = lp_is(s, "stx");
        if (!s->op || !(lp_is(s, "sta") || lp_is(s, "stz") || index_store) || s->deleted)
            continue;
        o = lp_operand(s, &n);
        byte = index_store ? s->x8 : s->m8;
        if (index_store && byte)
            continue;
        named = !lp_private(o, n);
        if (named && (!named_ok || memchr(o, ',', n) || !pr_named(o, n)))
            continue;
        if (lp_is(s, "stz")) {
            value = byte ? "$00" : "$0000";
            vn = byte ? 3 : 5;
            bv = 0;
        } else if (!byte) {
            int k, from_x = index_store, step = 0;

            /* Recover a literal and any intervening word increments */
            for (k = (int)i - 1; k >= 0; --k) {
                LpLine *l = &u->lines[k];
                if (!l->op) {
                    if (l->text[0] == ';' || !strncmp(l->text, ".export __inlined_", 18) ||
                        (!u->indirect && l->first_incoming < 0 && lp_fallthrough_label(l)))
                        continue;
                    break;
                }
                if (l->ends)
                    break;
                if (lp_is(l, from_x ? "ldx" : "lda")) {
                    size_t m;
                    const char *p = lp_operand(l, &m);
                    if (!(from_x ? l->x8 : l->m8) && m > 1 && p[0] == '#') {
                        bv = lp_immediate(l);
                        if (bv >= 0)
                            bv = (bv + step) & 65535;
                        if (!step) {
                            value = p + 1;
                            vn = m - 1;
                        } else if (bv >= 0) {
                            vn = (size_t)snprintf(text, sizeof text, "$%04X",
                                                  (unsigned)(lp_immediate(l) + step) & 65535u);
                            value = text;
                        }
                    }
                    break;
                }
                if (!from_x && !l->m8 && (lp_line_is(l, "inc a") || lp_line_is(l, "dec a"))) {
                    step += lp_is(l, "inc") ? 1 : -1;
                    continue;
                }
                if (!from_x && !l->m8 && !l->x8 && lp_line_is(l, "txa")) {
                    from_x = 1;
                    continue;
                }
                if ((l->def & (from_x ? LP_X : LP_A)) || l->use == LP_ALL || l->m8 || l->x8 ||
                    l->call)
                    break;
            }
            if (!value)
                continue;
        } else {
            int k;

            /* The low byte of A: back over stores, comments and accumulator width changes */
            for (k = (int)i - 1; k >= 0; --k) {
                LpLine *l = &u->lines[k];
                if (!l->op) {
                    if (l->label)
                        break;
                    continue;
                }
                if (lp_is(l, "lda")) {
                    bv = lp_immediate(l);
                    break;
                }
                if ((lp_is(l, "rep") || lp_is(l, "sep")) &&
                    lp_line_is(l, lp_is(l, "rep") ? "rep #$20" : "sep #$20"))
                    continue;
                if (lp_is(l, "sta") || lp_is(l, "stx") || lp_is(l, "sty") || lp_is(l, "stz") ||
                    lp_is(l, "ldx") || lp_is(l, "ldy"))
                    continue;
                break;
            }
            if (bv < 0)
                continue;
            bv &= 0xFF;
            snprintf(text, sizeof text, "$%02lX", bv);
            value = text;
            vn = 3;
        }
        y_frame = o[n - 1] == 'y';
        stack = o[n - 1] == 's';
        unsigned pushed = 0;
        for (j = i + 1; j < u->count; ++j) {
            LpLine *l = &u->lines[j];
            size_t m;
            const char *p;
            int a_op, x_op;
            char adjusted[12];
            const char *home = o;
            size_t home_length = n;
            if (l->label) {
                if (pushed || !lp_inner_label(u, j, i, j))
                    break;
                dead = 0;
                continue;
            }
            if (!l->op || dead)
                continue;
            if (stack && lp_stack_op(l)) {
                if (lp_is(l, "pea"))
                    pushed += 2;
                else if (lp_is(l, "pha"))
                    pushed += l->m8 ? 1u : 2u;
                else if (lp_is(l, "phx") || lp_is(l, "phy"))
                    pushed += l->x8 ? 1u : 2u;
                else
                    break;
                continue;
            }
            if (pushed) {
                unsigned offset = (unsigned)atoi(o) + pushed;
                if (offset > 255 || l->ends || lp_branch(l))
                    break;
                home_length = (size_t)snprintf(adjusted, sizeof adjusted, "%u,s", offset);
                home = adjusted;
            }
            if (named && lp_store_op(l)) {
                size_t width;
                const char *dest = lp_operand(l, &width);

                /* A direct slot in the reserved hardware stack cannot
                 * overlap an ordinary named object in this ABI. */
                if (width >= 3 && dest[width - 2] == ',' && dest[width - 1] == 's' &&
                    strspn(dest, "0123456789") == width - 2)
                    continue;
                if (memchr(dest, ',', width) || !pr_named(dest, width))
                    break;
            }
            if (lp_may_write(l, home, home_length, byte ? 1 : 2) || (y_frame && (l->def & LP_Y)))
                break;

            /* After an unconditional transfer only internal labels continue the path */
            if (l->ends) {
                dead = 1;
                continue;
            }
            if (lp_is(l, "rep") || lp_is(l, "sep")) {
                if (lp_line_is(l, "rep #$20") || lp_line_is(l, "sep #$20"))
                    continue;
                break;
            }
            p = lp_operand(l, &m);
            if ((!lp_operand_is(l, home, home_length) &&
                 (!named || !lp_named_word_alias(home, home_length, p, m))) ||
                !lp_has_immediate(l) || l->replace || l->deleted)
                continue;
            a_op = lp_is(l, "lda") || lp_is(l, "adc") || lp_is(l, "sbc") || lp_is(l, "cmp") ||
                   lp_is(l, "and") || lp_is(l, "ora") || lp_is(l, "eor");
            x_op = !a_op;
            if (!byte && ((a_op && !l->m8) || (x_op && !l->x8))) {
                lp_set(l, "    %.3s #%.*s", l->op, (int)vn, value);
                ++changed;
            } else if (byte && ((a_op && l->m8) || (x_op && l->x8))) {
                lp_set(l, "    %.3s #%.*s", l->op, (int)vn, value);
                ++changed;
            } else if (!byte && a_op && l->m8 && bv >= 0) {
                lp_set(l, "    %.3s #$%02lX", l->op, bv & 255);
                ++changed;
            } else if (byte && lp_is(l, "lda") && !l->m8) {
                int k = lp_next(u, j, 1);
                if (k >= 0 && lp_line_is(&u->lines[k], "and #$00FF")) {
                    lp_set(l, "    lda #$00%02lX", bv);
                    ++changed;
                }
            }
        }
    }
    return changed;
}

/* A nonvolatile object assigned a literal and immediately stepped needs
 * just the final store. The old accumulator value must be dead afterward. */
static int lp_step_literal_store(LpUnit *u, Function *f, size_t at)
{
    (void)at;
    if (lp_state.parser->no_value_reuse || lp_state.is_volatile || u->indirect ||
        body_asm_statements(f->body))
        return 0;
    lp_liveness(u);

    for (unsigned i = 0; i < u->count; ++i) {
        LpLine *clear = &u->lines[i];
        if (lp_is(clear, "stz")) {
            size_t n;
            const char *home = lp_operand(clear, &n);
            if (memchr(home, ',', n) || !pr_named(home, n))
                continue;
            const char *object = home;
            size_t length = lp_named_base(&object, n);
            for (int k = lp_next(u, i, 1); k >= 0; k = lp_next(u, (unsigned)k, 1)) {
                LpLine *l = &u->lines[k];
                if (l->m8 != clear->m8)
                    break;
                if (lp_is(l, "inc") || lp_is(l, "dec")) {
                    if (lp_operand_is(l, home, n) && !(l->out & (l->m8 ? LP_AL : LP_A))) {
                        unsigned value = lp_is(l, "inc") ? 1u : l->m8 ? 255u : 65535u;
                        lp_set(l, "    lda #$%0*X\n    sta %.*s", l->m8 ? 2 : 4, value, (int)n,
                               home);
                        clear->deleted = 1;
                        return 1;
                    }
                    break;
                }
                if (!lp_is(l, "lda") && !lp_is(l, "sta"))
                    break;
                size_t m;
                const char *p = lp_operand(l, &m);
                if (lp_immediate(l) >= 0 || lp_workspace_word(p, m) >= 0)
                    continue;
                if (memchr(p, ',', m) || !pr_named(p, m))
                    break;
                size_t other = lp_named_base(&p, m);
                if (!length || !other || (other == length && !memcmp(p, object, length)))
                    break;
            }
            continue;
        }
        LpLine *load = &u->lines[i];
        int store, step;
        size_t n;
        const char *home;
        long value;
        if (!lp_is(load, "lda") || (value = lp_immediate(load)) < 0 ||
            (store = lp_next(u, i, 1)) < 0 || !lp_is(&u->lines[store], "sta") ||
            (step = lp_next(u, (unsigned)store, 1)) < 0)
            continue;
        LpLine *update = &u->lines[step];
        home = lp_operand(&u->lines[store], &n);
        if ((!lp_is(update, "inc") && !lp_is(update, "dec")) || load->m8 != update->m8 ||
            (update->out & (load->m8 ? LP_AL : LP_A)) || memchr(home, ',', n) ||
            !pr_named(home, n) || !lp_operand_is(update, home, n))
            continue;
        value = (value + (lp_is(update, "inc") ? 1 : -1)) & (load->m8 ? 255 : 65535);
        lp_set(load, load->m8 ? "    lda #$%02lX" : "    lda #$%04lX", value);
        update->deleted = 1;
        return 1;
    }
    return 0;
}

/* Cache a word store in an otherwise unused index while A is reused.
 * Keep the original store until normal dead-store analysis proves it dead. */
static int lp_cache_stored_word(LpUnit *u, Function *f, size_t at)
{
    (void)at;
    if (lp_state.is_volatile || u->indirect || body_asm_statements(f->body))
        return 0;
    lp_liveness(u);

    for (unsigned i = 0; i < u->count; ++i) {
        LpLine *store = &u->lines[i];
        size_t n;
        const char *home = lp_operand(store, &n);
        int named = !lp_private(home, n);
        if (!lp_is(store, "sta") || store->m8 || store->x8 ||
            (named &&
             (lp_state.parser->no_value_reuse || memchr(home, ',', n) || !pr_named(home, n))) ||
            ((store->out & (LP_N | LP_Z)) && !lp_flags_from_a(u, lp_next(u, i, -1))))
            continue;
        unsigned spare = LP_X | LP_Y;
        int clobbered = 0;
        for (int k = (int)i; spare && (k = lp_next(u, (unsigned)k, 1)) >= 0;) {
            LpLine *l = &u->lines[k];
            if (l->m8 || l->x8 || l->call || l->ends || lp_branch(l) || l->use == LP_ALL ||
                lp_may_write(l, home, n, 2) || lp_stack_op(l) ||
                (home[n - 1] == 'y' && (l->def & LP_Y)))
                break;
            if (named && lp_store_op(l)) {
                size_t length;
                const char *dest = lp_operand(l, &length);
                if (memchr(dest, ',', length) || !pr_named(dest, length))
                    break;
            }
            if (lp_is(l, "lda") && lp_operand_is(l, home, n)) {
                spare &= ~l->out;
                if (clobbered && spare) {
                    lp_set(store, "    sta %.*s\n    %s", (int)n, home,
                           spare & LP_X ? "tax" : "tay");
                    lp_set(l, spare & LP_X ? "    txa" : "    tya");
                    return 1;
                }
                break;
            }
            spare &= ~(l->use | l->def);
            if (l->def & LP_A)
                clobbered = 1;
        }
    }
    return 0;
}

/* Defer the low word of a signed zero comparison until its high word
 * has proved zero. A/X and unsigned carry must be dead on every exit. */
static int lp_signed_home_positive(LpUnit *u, Function *f, size_t at)
{
    (void)f;
    (void)at;
    if (lp_state.is_volatile || u->indirect)
        return 0;
    lp_liveness(u);

    for (unsigned i = 0; i < u->count; ++i) {
        LpLine *high = &u->lines[i];
        int seq[6], j = (int)i;
        size_t width;
        const char *low;
        if (high->m8 || high->x8 || !lp_is(high, "lda"))
            continue;
        unsigned n = 0;
        for (; n < 6 && (j = lp_next(u, (unsigned)j, 1)) >= 0; ++n)
            seq[n] = j;
        if (n != 6)
            continue;
        LpLine *transfer = &u->lines[seq[0]], *load = &u->lines[seq[1]], *neg = &u->lines[seq[3]],
               *pos = &u->lines[seq[4]];
        if (!lp_line_is(transfer, "tax") || !lp_is(load, "lda") ||
            !lp_line_is(&u->lines[seq[2]], "cpx #0") || !lp_is(neg, "bmi") || !lp_is(pos, "bne") ||
            !lp_line_is(&u->lines[seq[5]], "cmp #0") || neg->target < 0 || pos->target < 0)
            continue;
        low = lp_operand(load, &width);
        if (!lp_private(low, width) ||
            ((u->lines[neg->target].live | u->lines[pos->target].live) & (LP_A | LP_X | LP_C)) ||
            (u->lines[seq[5]].out & (LP_X | LP_C)))
            continue;
        lp_set(&u->lines[seq[5]], "    lda %.*s", (int)width, low);
        transfer->deleted = load->deleted = u->lines[seq[2]].deleted = 1;
        return 1;
    }
    return 0;
}

/* A signed long comparison consumes the high flags first. Exchange
 * X:A before subtracting the high word so X can retain the low result. */
static int lp_signed_difference_flags(LpUnit *u, Function *f, size_t at)
{
    (void)f;
    (void)at;
    lp_liveness(u);

    for (unsigned i = 0; i < u->count; ++i) {
        LpLine *push = &u->lines[i];
        if (push->m8 || push->x8 || !lp_line_is(push, "pha"))
            continue;
        int seq[8], next = (int)i;
        unsigned count = 0;
        for (; count < 8 && (next = lp_next(u, (unsigned)next, 1)) >= 0; ++count)
            seq[count] = next;
        if (count != 8 || !lp_line_is(&u->lines[seq[0]], "txa") ||
            !lp_is(&u->lines[seq[1]], "sbc") || !lp_line_is(&u->lines[seq[2]], "tax") ||
            !lp_line_is(&u->lines[seq[3]], "pla") || !lp_line_is(&u->lines[seq[4]], "cpx #0") ||
            !lp_is(&u->lines[seq[5]], "bmi") || !lp_is(&u->lines[seq[6]], "bne") ||
            !lp_line_is(&u->lines[seq[7]], "cmp #0"))
            continue;
        LpLine *high = &u->lines[seq[1]], *negative = &u->lines[seq[5]],
               *positive = &u->lines[seq[6]];
        if (negative->target < 0 || positive->target < 0 ||
            ((u->lines[negative->target].live | u->lines[positive->target].live) &
             (LP_A | LP_X | LP_C)) ||
            (u->lines[seq[7]].out & (LP_A | LP_X)))
            continue;
        size_t n;
        const char *operand = lp_operand(high, &n);
        int stack = lp_private(operand, n) && operand[n - 1] == 's';
        if (stack) {
            if (atoi(operand) < 3)
                continue;
            lp_set(&u->lines[seq[2]], "    sbc %u,s", (unsigned)atoi(operand) - 2);
        } else {
            if (!pr_named(operand, n) || memchr(operand, ',', n))
                continue;
            lp_set(&u->lines[seq[2]], "    sbc %.*s", (int)n, operand);
        }
        lp_set(push, "    phx");
        lp_set(&u->lines[seq[0]], "    tax");
        lp_set(high, "    pla");
        u->lines[seq[3]].deleted = u->lines[seq[4]].deleted = 1;
        lp_set(&u->lines[seq[7]], "    cpx #0");
        return 1;
    }
    return 0;
}

/* Stage a register pair into the private arithmetic workspace without
 * borrowing X. The low source must survive the earlier high-word store. */
static int lp_stage_pair_words(LpUnit *u, Function *f, size_t at)
{
    (void)f;
    (void)at;
    lp_liveness(u);

    for (unsigned i = 0; i < u->count; ++i) {
        LpLine *save = &u->lines[i];
        if (save->m8 || save->x8 || !lp_line_is(save, "tax"))
            continue;
        int load = lp_next(u, i, 1), low = load < 0 ? -1 : lp_next(u, (unsigned)load, 1);
        int high = low < 0 ? -1 : lp_next(u, (unsigned)low, 1);
        if (high < 0 || !lp_is(&u->lines[load], "lda") || (u->lines[load].use & LP_X) ||
            !lp_is(&u->lines[low], "sta") || !lp_is(&u->lines[high], "stx") ||
            (u->lines[high].out & LP_X))
            continue;
        size_t n, m, k;
        const char *a = lp_operand(&u->lines[low], &n), *b = lp_operand(&u->lines[high], &m);
        const char *source = lp_operand(&u->lines[load], &k);
        if (lp_workspace_word(a, n) < 0 || lp_workspace_word(b, m) < 0 || !lp_private(source, k) ||
            lp_may_write(&u->lines[high], a, n, 2) || lp_may_write(&u->lines[high], source, k, 2))
            continue;
        lp_set(save, "    sta %.*s", (int)m, b);
        u->lines[high].deleted = 1;
        return 1;
    }
    return 0;
}

/* Compare an already-computed signed word against a literal on the left.
 * Bias both words to unsigned order, replacing the reverse subtraction and
 * its overflow correction. No arithmetic flags survive the sign branch. */
static int lp_reverse_signed_literal(LpUnit *u, Function *f, size_t at)
{
    (void)f;
    (void)at;
    lp_liveness(u);

    for (unsigned i = 0; i < u->count; ++i) {
        LpLine *save = &u->lines[i];
        size_t n;
        const char *home = lp_operand(save, &n);
        if (save->m8 || !lp_is(save, "sta") || lp_workspace_word(home, n) < 0)
            continue;
        int load = lp_next(u, i, 1), carry = load < 0 ? -1 : lp_next(u, (unsigned)load, 1);
        int sub = carry < 0 ? -1 : lp_next(u, (unsigned)carry, 1);
        if (sub < 0 || !lp_is(&u->lines[load], "lda") || !lp_line_is(&u->lines[carry], "sec") ||
            !lp_is(&u->lines[sub], "sbc") || !lp_operand_is(&u->lines[sub], home, n))
            continue;
        long literal = lp_immediate(&u->lines[load]);
        if (literal < 0 || literal > 65535 || literal == 32767)
            continue;
        int check = lp_next(u, (unsigned)sub, 1),
            invert = check < 0 ? -1 : lp_next(u, (unsigned)check, 1);
        if (invert < 0 || !lp_line_is(&u->lines[check], "bvc :+") ||
            !lp_line_is(&u->lines[invert], "eor #$8000") || (unsigned)invert + 2 >= u->count)
            continue;
        LpLine *label = &u->lines[invert + 1], *branch = &u->lines[invert + 2];
        if (label->length != 1 || label->text[0] != ':' || label->first_incoming != check ||
            u->lines[check].next_incoming >= 0 || (branch->out & (LP_A | LP_FLAGS)))
            continue;
        int greater = lp_is(branch, "bmi");
        if (!greater && !lp_is(branch, "bpl"))
            continue;
        const char *target = lp_operand(branch, &n);
        lp_set(&u->lines[load], "    eor #$8000");
        lp_set(&u->lines[carry], "    cmp #$%04lX", (literal ^ 32768) + 1);
        u->lines[sub].deleted = u->lines[check].deleted = u->lines[invert].deleted = 1;

        /* Keep the anonymous label so later relative-label references do not change */
        lp_set(branch, "    %s %.*s", greater ? "bcs" : "bcc", (int)n, target);
        return 1;
    }
    return 0;
}

/* Two private destinations can take the low half of X:A before TXA
 * exposes the high half. Keep the order of any overlapping writes. */
static int lp_pair_store_order(LpUnit *u, Function *f, size_t at)
{
    (void)at;
    if (lp_state.is_volatile || lp_state.frame_address || body_asm_statements(f->body))
        return 0;

    for (unsigned i = 0; i < u->count; ++i) {
        LpLine *low = &u->lines[i];
        size_t n, m, h;
        const char *home = lp_operand(low, &n);
        if (!lp_is(low, "sta") || low->m8 || low->x8 || !lp_private(home, n) ||
            (home[n - 1] != 's' && home[n - 1] != 'y'))
            continue;
        int seq[5], next = (int)i;
        unsigned count = 0;
        for (; count < 5 && (next = lp_next(u, (unsigned)next, 1)) >= 0; ++count)
            seq[count] = next;
        if (count != 5 || !lp_line_is(&u->lines[seq[0]], "txa") ||
            !lp_is(&u->lines[seq[1]], "sta") || !lp_is(&u->lines[seq[2]], "lda") ||
            !lp_operand_is(&u->lines[seq[2]], home, n) || !lp_is(&u->lines[seq[3]], "sta") ||
            !lp_line_is(&u->lines[seq[4]], "txa"))
            continue;
        LpLine *high = &u->lines[seq[1]], *also = &u->lines[seq[3]];
        const char *second = lp_operand(also, &m), *upper = lp_operand(high, &h);
        if (!lp_private(second, m) || !lp_private(upper, h) || second[m - 1] != home[n - 1] ||
            upper[h - 1] != home[n - 1] || lp_may_write(high, home, n, 2) ||
            lp_may_write(high, second, m, 2))
            continue;
        lp_set(&u->lines[seq[0]], "    sta %.*s\n    txa", (int)m, second);
        u->lines[seq[2]].deleted = also->deleted = u->lines[seq[4]].deleted = 1;
        return 1;
    }
    return 0;
}

/* X:A already holds a double-word result. Propagate the low word's
 * carry into X without moving either half through the stack. */
static int lp_fold_index_carry(LpUnit *u, unsigned i)
{
    LpLine *save = &u->lines[i];

    if (save->m8 || save->x8 || !lp_line_is(save, "pha"))
        return 0;
    int transfer = lp_next(u, i, 1);
    int high = transfer < 0 ? -1 : lp_next(u, (unsigned)transfer, 1);
    int index = high < 0 ? -1 : lp_next(u, (unsigned)high, 1);
    int restore = index < 0 ? -1 : lp_next(u, (unsigned)index, 1);
    if (restore < 0 || !lp_line_is(&u->lines[transfer], "txa") ||
        !lp_line_is(&u->lines[index], "tax") || !lp_line_is(&u->lines[restore], "pla") ||
        (u->lines[restore].out & (LP_C | LP_V)))
        return 0;
    int add = lp_is(&u->lines[high], "adc");
    if ((!add && !lp_is(&u->lines[high], "sbc")) || lp_immediate(&u->lines[high]) != 0)
        return 0;
    unsigned label = lp_next_label();
    lp_set(save, "    %s cg_%s_%u", add ? "bcc" : "bcs", lp_state.parser->unit, label);
    lp_set(&u->lines[transfer], "    %s", add ? "inx" : "dex");
    lp_set(&u->lines[high], "cg_%s_%u = *%s", lp_state.parser->unit, label,
           (u->lines[restore].out & (LP_N | LP_Z)) ? "\n    ora #$0000" : "");
    u->lines[index].deleted = u->lines[restore].deleted = 1;
    return restore;
}

static int lp_index_carry(LpUnit *u, Function *f, size_t at)
{
    int changed = 0;
    (void)f;
    (void)at;

    lp_liveness(u);

    for (unsigned i = 0; i < u->count; ++i) {
        int end = lp_fold_index_carry(u, i);
        if (end) {
            ++changed;
            i = (unsigned)end;
        }
    }
    return changed;
}

/* Track a private word backwards across outgoing argument pushes. Only
 * direct nonoverlapping frame stores and loads may intervene. */
static int lp_fixed_stack_argument(LpUnit *u, Function *f, size_t at)
{
    (void)f;
    (void)at;
    if (lp_state.is_volatile || u->indirect)
        return 0;
    lp_liveness(u);

    for (unsigned i = 0; i < u->count; ++i) {
        LpLine *load = &u->lines[i];
        size_t n;
        const char *op = lp_operand(load, &n);
        if (!lp_is(load, "lda") || load->m8 || !lp_private(op, n) || op[n - 1] != 's')
            continue;
        int push = lp_next(u, i, 1);
        if (push < 0 || !lp_line_is(&u->lines[push], "pha") || u->lines[push].m8)
            continue;
        int slot = atoi(op), crossed = 0;
        for (int j = (int)i; (j = lp_next(u, (unsigned)j, -1)) >= 0;) {
            LpLine *l = &u->lines[j];
            if (lp_is(l, "pea") || lp_line_is(l, "pha")) {
                slot -= lp_is(l, "pea") || !l->m8 ? 2 : 1;
                if (slot < 1)
                    break;
                crossed = 1;
                continue;
            }
            if (lp_is(l, "lda"))
                continue;
            if (!lp_is(l, "sta"))
                break;
            op = lp_operand(l, &n);
            if (!lp_private(op, n) || op[n - 1] != 's')
                break;
            int stored = atoi(op);
            if (stored >= slot + 2 || stored + (l->m8 ? 1 : 2) <= slot)
                continue;
            if (stored == slot && !l->m8 && crossed) {
                int def = lp_next(u, (unsigned)j, -1);
                long literal;
                if (def >= 0 && !u->lines[def].m8 && lp_is(&u->lines[def], "lda") &&
                    (literal = lp_immediate(&u->lines[def])) >= 0 && literal <= 65535) {
                    if (!(u->lines[push].out & (LP_A | LP_N | LP_Z))) {
                        lp_set(load, "    pea $%04lX", literal);
                        u->lines[push].deleted = 1;
                    } else
                        lp_set(load, "    lda #$%04lX", literal);
                    return 1;
                }
            }
            break;
        }
    }
    return 0;
}

/* Workspace words read nowhere except by "lda M / inc a... / sta M" updates
 * of themselves: those updates and every other store go. */
static int lp_dead_workspace(LpUnit *u, Function *f, size_t at)
{
    unsigned word, i;
    int changed = 0;
    (void)f;
    (void)at;

    if (u->helpers || u->indirect)
        return 0;
    lp_liveness(u);

    for (word = 0; word < 32; word += 2) {
        int ok = 1, stores = 0;
        for (i = 0; i < u->count && ok; ++i) {
            LpLine *l = &u->lines[i];
            size_t m;
            const char *p;
            int w;
            if (!l->op || l->deleted)
                continue;
            p = lp_operand(l, &m);
            w = lp_workspace_word(p, m);
            if (w < 0) {
                if (lp_text_words(p, p + m) & (1u << (word / 2)))
                    ok = 0;
                continue;
            }
            if (!lp_overlaps(l, w, (int)word))
                continue;
            if ((lp_is(l, "sta") || lp_is(l, "stx") || lp_is(l, "sty") || lp_is(l, "stz")) &&
                w == (int)word) {
                ++stores;
                continue;
            }
            if (lp_is(l, "lda") && w == (int)word && !l->m8) {
                /* A self-update chain ending in "sta M" with dead results */
                int k = (int)i;
                unsigned written = LP_A | LP_N | LP_Z;
                while ((k = lp_next(u, (unsigned)k, 1)) >= 0) {
                    LpLine *c = &u->lines[k];
                    if (lp_line_is(c, "inc a") || lp_line_is(c, "dec a") || lp_line_is(c, "inc") ||
                        lp_line_is(c, "dec"))
                        continue;
                    if (lp_line_is(c, "clc") || lp_line_is(c, "sec")) {
                        written |= LP_C;
                        continue;
                    }
                    if ((lp_is(c, "adc") || lp_is(c, "sbc")) && !strncmp(c->op + 4, "#", 1)) {
                        written |= LP_FLAGS;
                        continue;
                    }
                    break;
                }
                if (k >= 0 && lp_is(&u->lines[k], "sta") && !u->lines[k].m8 &&
                    lp_operand_is(&u->lines[k], p, m) && !(u->lines[k].out & written))
                    continue;
            }
            ok = 0;
        }
        if (!ok || !stores)
            continue;
        for (i = 0; i < u->count; ++i) {
            LpLine *l = &u->lines[i];
            size_t m;
            const char *p;
            if (!l->op || l->deleted)
                continue;
            p = lp_operand(l, &m);
            if (lp_workspace_word(p, m) != (int)word)
                continue;
            if (lp_is(l, "lda")) {
                int k = (int)i;
                l->deleted = 1;
                while ((k = lp_next(u, (unsigned)k, 1)) >= 0) {
                    u->lines[k].deleted = 1;
                    if (lp_is(&u->lines[k], "sta"))
                        break;
                }
            } else
                l->deleted = 1;
            ++changed;
        }
        if (changed)
            break;
    }
    return changed;
}

/* Instructions without side effects whose results are all dead */
static unsigned lp_byte_live_out(const LpUnit *u, unsigned i)
{
    int rep = lp_next(u, i, 1);

    return rep >= 0 && lp_line_is(&u->lines[rep], "rep #$20") ? u->lines[rep].out : u->lines[i].out;
}

static int lp_dead_code(LpUnit *u, Function *f, size_t at)
{
    unsigned i;
    int changed = 0;
    (void)f;
    (void)at;

    lp_liveness(u);

    for (i = 0; i < u->count; ++i) {
        LpLine *l = &u->lines[i];
        size_t m;
        const char *p;
        int pure = 0;
        if (!l->op || l->deleted || l->replace)
            continue;
        p = lp_operand(l, &m);
        if (lp_is(l, "cmp") && lp_immediate(l) == 0 && !(l->out & LP_C)) {
            int prev = lp_next(u, i, -1);
            if (prev >= 0 && u->lines[prev].m8 == l->m8 &&
                (u->lines[prev].def & (LP_N | LP_Z)) == (LP_N | LP_Z) &&
                (u->lines[prev].def & (LP_A | LP_AL))) {
                l->deleted = 1;
                ++changed;
                continue;
            }
        }
        if (l->m8 && m > 1 && p[0] == '#' && (lp_is(l, "cmp") || lp_is(l, "lda"))) {
            unsigned live = lp_byte_live_out(u, i);
            if (!(live & l->def)) {
                l->deleted = 1;
                ++changed;
                continue;
            }
        }
        if ((lp_is(l, "lda") || lp_is(l, "and") || lp_is(l, "ora") || lp_is(l, "eor") ||
             lp_is(l, "adc") || lp_is(l, "sbc") || lp_is(l, "cmp")) &&
            !l->m8)
            pure = m > 1 && (p[0] == '#' || lp_private(p, m));
        else if ((lp_is(l, "ldx") || lp_is(l, "ldy") || lp_is(l, "cpx") || lp_is(l, "cpy")) &&
                 !l->x8)
            pure = m > 1 && (p[0] == '#' || lp_private(p, m));
        else if (lp_line_is(l, "tax") || lp_line_is(l, "tay") || lp_line_is(l, "txy") ||
                 lp_line_is(l, "tyx") || lp_line_is(l, "inx") || lp_line_is(l, "dex") ||
                 lp_line_is(l, "iny") || lp_line_is(l, "dey"))
            pure = !l->x8;
        else if (lp_line_is(l, "txa") || lp_line_is(l, "tya") || lp_line_is(l, "inc a") ||
                 lp_line_is(l, "dec a") || lp_line_is(l, "inc") || lp_line_is(l, "dec") ||
                 lp_line_is(l, "asl a") || lp_line_is(l, "lsr a") || lp_line_is(l, "asl") ||
                 lp_line_is(l, "lsr"))
            pure = !l->m8;
        else if (lp_line_is(l, "clc") || lp_line_is(l, "sec"))
            pure = 1;
        if (pure && l->def && !(l->def & l->out)) {
            l->deleted = 1;
            ++changed;
        }
    }
    return changed;
}

/* Cleanup can leave an adjacent save/restore after removing the instructions
 * between them. A pull also sets N/Z, so remove the pair only when those
 * results are dead. */
static int lp_operand_has_s(const char *o, size_t n);

static int lp_dead_push_pairs(LpUnit *u, Function *f, size_t at)
{
    static const char *const push[] = {"pha", "phx", "phy"}, *const pull[] = {"pla", "plx", "ply"};
    static const unsigned reg[] = {LP_A, LP_X, LP_Y};
    unsigned i, j;
    int changed = 0;
    (void)f;
    (void)at;

    lp_liveness(u);

    for (i = 0; i < u->count; ++i) {
        int k, clobbered = 0;
        unsigned spare = LP_X | LP_Y;
        if (u->lines[i].deleted || u->lines[i].m8 || u->lines[i].x8)
            continue;
        for (j = 0; j < 3 && !lp_is(&u->lines[i], push[j]); ++j) {
        }
        if (j == 3)
            continue;
        for (k = lp_next(u, i, 1); k >= 0; k = lp_next(u, (unsigned)k, 1)) {
            LpLine *cur = &u->lines[k];
            size_t n;
            const char *o;
            if (cur->deleted || cur->m8 || cur->x8)
                break;
            if (lp_is(cur, pull[j])) {
                if (!(cur->out & (LP_N | LP_Z | (clobbered ? reg[j] : 0)))) {
                    u->lines[i].deleted = cur->deleted = 1;
                    changed = 1;
                } else if (j == 0 && clobbered) {
                    /* Rematerialize a saved word literal once intervening
                     * code has overwritten A. LDA reproduces the flags of PLA. */
                    int prev = (int)i;
                    while ((prev = lp_next(u, (unsigned)prev, -1)) >= 0) {
                        LpLine *source = &u->lines[prev];
                        long value;
                        if (lp_is(source, "lda") && !source->m8 &&
                            (value = lp_immediate(source)) >= 0) {
                            u->lines[i].deleted = 1;
                            lp_set(cur, "    lda #$%04lX", value);
                            changed = 1;
                            break;
                        }
                        if (!lp_is(source, "sta") && !lp_is(source, "stx") && !lp_is(source, "sty"))
                            break;
                    }
                    spare &= ~cur->out;
                    if (!u->lines[i].deleted && spare && !(u->lines[i].out & (LP_N | LP_Z))) {
                        /* Keep a wide add/subtract in X:A when only carry
                         * can change its high word. No temporary is needed. */
                        if (lp_fold_index_carry(u, i)) {
                            changed = 1;
                            break;
                        }

                        /* A dead index may hold the saved word until this pull */
                        lp_set(&u->lines[i], spare & LP_X ? "    tax" : "    tay");
                        lp_set(cur, spare & LP_X ? "    txa" : "    tya");
                        changed = 1;
                    }
                }
                break;
            }
            o = lp_operand(cur, &n);
            if (cur->ends || lp_branch(cur) || cur->call || lp_stack_op(cur) ||
                cur->use == LP_ALL || lp_is(cur, "sep") || lp_is(cur, "rep") || lp_is(cur, "tsx") ||
                lp_is(cur, "tsc") || lp_operand_has_s(o, n))
                break;
            spare &= ~(cur->use | cur->def);
            if ((cur->def & reg[j]) || (j == 0 && lp_is(cur, "xba")))
                clobbered = 1;
        }
    }
    return changed;
}

static int lp_next_mode(const LpUnit *u, unsigned k)
{
    unsigned i = k;

    for (;;) {
        if (++i >= u->count)
            return -1;
        if (!u->lines[i].length)
            return -1;
        if (u->lines[i].text[0] == ';' || u->lines[i].deleted)
            continue;
        if (!u->lines[i].op && ((u->lines[i].length == 3 && !strncmp(u->lines[i].text, ".a8", 3)) ||
                                (u->lines[i].length == 4 && !strncmp(u->lines[i].text, ".a16", 4))))
            continue;
        return u->lines[i].op ? (int)i : -1;
    }
}

/* X used only as an a:$D,x index from line k on until it dies there:
 * returns the last such line and counts the uses, or -1. */
static int lp_index_run(const LpUnit *u, int k, int *uses, int any_op)
{
    int j;

    *uses = 0;
    for (j = k; j >= 0; j = lp_next_mode(u, (unsigned)j)) {
        const LpLine *c = &u->lines[j];
        size_t m;
        const char *p = lp_operand(c, &m);
        if (c->replace || c->deleted)
            return -1;
        if (lp_line_is(c, "sep #$20") || lp_line_is(c, "rep #$20")) {
            if (!(c->out & LP_X))
                return *uses ? j : -1;
            continue;
        }
        if (c->use & LP_X) {
            if (c->use == LP_ALL || c->call || c->def & LP_X ||
                !(m == 9 && !strncmp(p, "a:$", 3) && p[7] == ',' && p[8] == 'x'))
                return -1;
            if (!any_op &&
                !(lp_is(c, "lda") || lp_is(c, "sta") || lp_is(c, "adc") || lp_is(c, "sbc") ||
                  lp_is(c, "cmp") || lp_is(c, "and") || lp_is(c, "ora") || lp_is(c, "eor")))
                return -1;
            ++*uses;
        }
        if (!(c->out & LP_X))
            return *uses ? j : -1;
        if (c->ends || lp_branch(c))
            return -1;
    }
    return -1;
}

/* "inx/dex ... op a:$D,x" while X dies: fold the steps into the displacements */
static int lp_fold_steps(LpUnit *u, Function *f, size_t at)
{
    unsigned i;
    int changed = 0;
    (void)f;
    (void)at;

    lp_liveness(u);

    for (i = 0; i < u->count; ++i) {
        int k = (int)i, last = -1, delta = 0, end, uses, j;
        if (!(lp_line_is(&u->lines[i], "inx") || lp_line_is(&u->lines[i], "dex")) ||
            u->lines[i].wrap_step || u->lines[i].x8 || u->lines[i].deleted || u->lines[i].replace)
            continue;
        for (; k >= 0 && (lp_line_is(&u->lines[k], "inx") || lp_line_is(&u->lines[k], "dex")) &&
               !u->lines[k].wrap_step && !u->lines[k].deleted;
             k = lp_next(u, (unsigned)k, 1)) {
            delta += lp_line_is(&u->lines[k], "inx") ? 1 : -1;
            last = k;
        }
        if (k < 0 || u->lines[last].out & (LP_N | LP_Z) || (end = lp_index_run(u, k, &uses, 1)) < 0)
            continue;
        { /* Indexed addresses carry into the next bank: a folded displacement
             * must stay within 0..$FFFF, where X itself would have wrapped. */
            int ok = 1;
            for (j = k; j >= 0; j = lp_next_mode(u, (unsigned)j)) {
                size_t m;
                const char *p = lp_operand(&u->lines[j], &m);
                long d;
                if (u->lines[j].use & LP_X) {
                    d = (long)strtoul(p + 3, NULL, 16) + delta;
                    if (d < 0 || d > 0xFFFF)
                        ok = 0;
                }
                if (j == end)
                    break;
            }
            if (!ok)
                continue;
        }
        for (j = k; j >= 0; j = lp_next_mode(u, (unsigned)j)) {
            LpLine *c = &u->lines[j];
            size_t m;
            const char *p = lp_operand(c, &m);
            if (c->use & LP_X) {
                unsigned d = ((unsigned)strtoul(p + 3, NULL, 16) + (unsigned)delta) & 0xFFFFu;
                lp_set(c, "    %.3s a:$%04X,x", c->op, d);
            }
            if (j == end)
                break;
        }
        for (j = (int)i; j <= last; ++j)
            if (u->lines[j].op)
                u->lines[j].deleted = 1;
        ++changed;
        i = (unsigned)end;
    }
    return changed;
}

static int lp_cond_branch_target(const LpUnit *u, int k, int *after)
{
    const LpLine *b;

    if (k < 0 || (unsigned)k >= u->count)
        return -1;
    b = &u->lines[k];
    if (!lp_branch(b) || b->ends || b->deleted || b->replace || b->label || b->target < 0)
        return -1;
    if (b->target == k + 2 && (unsigned)(k + 2) < u->count && u->lines[k + 2].length == 1 &&
        u->lines[k + 2].text[0] == ':' && !u->lines[k + 2].deleted &&
        lp_is(&u->lines[k + 1], "jmp") && !u->lines[k + 1].deleted && !u->lines[k + 1].replace &&
        !u->lines[k + 1].label && u->lines[k + 1].target >= 0) {
        if (after)
            *after = k + 2;
        return u->lines[k + 1].target;
    }
    if (u->lines[b->target].length == 1 && u->lines[b->target].text[0] == ':')
        return -1;
    if (after)
        *after = k;
    return b->target;
}

static int lp_far_stack_guard(LpUnit *u, int start, int ops[4], int *after, int *carry)
{
    static const char *const op[] = {"lda", "cmp", "lda", "sbc"};
    int k = start;

    for (unsigned i = 0; i < 4; ++i) {
        if (k < 0)
            return -1;
        LpLine *l = &u->lines[k];
        size_t n;
        const char *operand = lp_operand(l, &n);
        if (l->m8 || !lp_is(l, op[i]) || !lp_private(operand, n) || operand[n - 1] != 's' ||
            atoi(operand) < 1)
            return -1;
        ops[i] = k;
        k = lp_next(u, (unsigned)k, 1);
    }
    if (lp_cond_branch_target(u, k, after) < 0)
        return -1;
    if (lp_is(&u->lines[k], "bcs"))
        *carry = (*after == k);
    else if (lp_is(&u->lines[k], "bcc"))
        *carry = (*after != k);
    else
        return -1;
    if (*after != k && (u->lines[*after].first_incoming != k || u->lines[k].next_incoming >= 0))
        return -1;
    return k;
}

/* A byte test using a temporary stack-relative direct page restores
 * both S and D before its branch. */
static int lp_far_stack_byte_test(LpUnit *u, int k)
{
    static const char *const prologue[] = {"phd", "tsc", "tcd", "sep #$20"};

    for (unsigned i = 0; i < sizeof prologue / sizeof *prologue; ++i) {
        if (k < 0 || !lp_line_is(&u->lines[k], prologue[i]))
            return -1;
        k = lp_next_mode(u, (unsigned)k);
    }
    if (k < 0 || !lp_is(&u->lines[k], "lda") || !u->lines[k].m8)
        return -1;
    size_t n;
    const char *p = lp_operand(&u->lines[k], &n);
    if (n != 5 || p[0] != '[' || p[1] != '$' || p[4] != ']' || !isxdigit((unsigned char)p[2]) ||
        !isxdigit((unsigned char)p[3]))
        return -1;
    k = lp_next_mode(u, (unsigned)k);
    if (k < 0 || !lp_line_is(&u->lines[k], "pld"))
        return -1;
    k = lp_next_mode(u, (unsigned)k);
    if (k < 0 || !lp_is(&u->lines[k], "cmp") || !u->lines[k].m8 || lp_immediate(&u->lines[k]) < 0)
        return -1;
    k = lp_next_mode(u, (unsigned)k);
    if (k < 0 || !lp_line_is(&u->lines[k], "rep #$20"))
        return -1;
    return lp_next_mode(u, (unsigned)k);
}

/* The passed stack-pointer guard remains true across a register counter
 * test or a byte test that leaves its operand slots unchanged. */
static int lp_skip_repeated_far_loop_guard(LpUnit *u, Function *f, size_t at)
{
    (void)at;
    if (u->indirect || body_asm_statements(f->body))
        return 0;
    int known, changed = 0;
    unsigned char *targets = lp_local_targets(u, &known);
    lp_liveness(u);

    for (unsigned i = 0; i < u->count && !changed; ++i) {
        int ops[4], repeat[4], after, want, again_after, again_want;
        if (lp_far_stack_guard(u, (int)i, ops, &after, &want) < 0)
            continue;
        int step = lp_next_fallthrough(u, (unsigned)after, 1, targets, known);
        if (step < 0 || u->lines[step].x8)
            continue;
        int enter, enter_after;
        int counter = lp_is(&u->lines[step], "dey") || lp_is(&u->lines[step], "dex");
        if (counter) {
            int check = lp_next(u, (unsigned)step, 1);
            if (check < 0 ||
                !lp_is(&u->lines[check], lp_is(&u->lines[step], "dey") ? "cpy" : "cpx") ||
                lp_immediate(&u->lines[check]) < 0)
                continue;
            enter = lp_next(u, (unsigned)check, 1);
        } else
            enter = lp_far_stack_byte_test(u, step);
        int target = lp_cond_branch_target(u, enter, &enter_after);
        if (target < 0 || (counter && target >= (int)i))
            continue;
        int head = lp_next_fallthrough(u, (unsigned)target, 1, targets, known);
        if (lp_far_stack_guard(u, head, repeat, &again_after, &again_want) < 0 ||
            want != again_want || (unsigned)(again_after + 1) >= u->count ||
            (u->lines[again_after + 1].live & (LP_A | LP_FLAGS)))
            continue;
        int same = 1;
        for (unsigned j = 0; j < 4; ++j) {
            size_t n;
            const char *p = lp_operand(&u->lines[ops[j]], &n);
            if (!lp_operand_is(&u->lines[repeat[j]], p, n))
                same = 0;
        }
        if (!same)
            continue;
        char label[48];
        unsigned id = lp_next_label();
        snprintf(label, sizeof label, "cg_lp_%u:\n", id);
        lp_insert(&u->lines[again_after + 1], label);
        if (enter_after == enter)
            lp_set(&u->lines[enter], "    %.3s cg_lp_%u", u->lines[enter].op, id);
        else
            lp_set(&u->lines[enter + 1], "    jmp .loword(cg_lp_%u)", id);
        changed = 1;
    }
    free(targets);
    return changed;
}

/* An index initialized before a signed-length guard is needed only
 * on the positive path, provided neither exit observes the old Y. */
static int lp_delay_guarded_y_init(LpUnit *u, Function *f, size_t at)
{
    (void)at;
    if (u->indirect || body_asm_statements(f->body))
        return 0;
    lp_liveness(u);

    for (unsigned i = 0; i < u->count; ++i) {
        LpLine *init = &u->lines[i];
        if (!lp_is(init, "ldy") || init->x8 || lp_immediate(init) < 0)
            continue;
        int load = lp_next(u, i, 1), zero = load < 0 ? -1 : lp_next(u, (unsigned)load, 1);
        int after_zero, after_negative;
        int zero_exit = lp_cond_branch_target(u, zero, &after_zero);
        if (zero_exit < 0 || !lp_is(&u->lines[load], "lda") || (u->lines[load].use & LP_Y) ||
            !lp_is(&u->lines[zero], after_zero == zero ? "beq" : "bne") ||
            (after_zero != zero &&
             (u->lines[after_zero].first_incoming != zero || u->lines[zero].next_incoming >= 0)) ||
            (u->lines[zero_exit].live & LP_Y))
            continue;
        int negative = lp_next(u, (unsigned)after_zero, 1);
        int negative_exit = lp_cond_branch_target(u, negative, &after_negative);
        if (negative_exit < 0 || (unsigned)(after_negative + 1) >= u->count ||
            !lp_is(&u->lines[negative], after_negative == negative ? "bmi" : "bpl") ||
            (after_negative != negative && (u->lines[after_negative].first_incoming != negative ||
                                            u->lines[negative].next_incoming >= 0)) ||
            (u->lines[negative_exit].live & LP_Y) ||
            (u->lines[after_negative + 1].live & (LP_N | LP_Z)))
            continue;
        char literal[32];
        snprintf(literal, sizeof literal, "    ldy #$%04X\n", (unsigned)lp_immediate(init));
        lp_insert(&u->lines[after_negative + 1], literal);
        init->deleted = 1;
        return 1;
    }
    return 0;
}

/* Y register forms: TYA/INC A/TAY -> INY, TYA/TAX -> TYX, TXA/TAY -> TXY,
 * and TYX feeding only a:$D,x operands -> a:$D,y. */
static int lp_y_forms(LpUnit *u, Function *f, size_t at)
{
    unsigned i;
    int changed = 0;
    (void)f;
    (void)at;

    lp_liveness(u);

    for (i = 0; i < u->count; ++i) {
        LpLine *l = &u->lines[i];
        int k, steps = 0, dir = 0;
        if (!l->op || l->m8 || l->x8 || l->deleted || l->replace)
            continue;
        if (lp_line_is(l, "tya") || lp_line_is(l, "txa")) {
            int from_y = lp_line_is(l, "tya");
            int carry = lp_next(u, i, 1);
            if (carry >= 0 && lp_is(&u->lines[carry], "cmp") && !u->lines[carry].deleted &&
                !u->lines[carry].replace) {
                size_t n;
                const char *operand = lp_operand(&u->lines[carry], &n);
                if (n && (operand[0] == '#' || (n > 2 && (operand[0] == 'a' || operand[0] == 'z') &&
                                                operand[1] == ':' && !memchr(operand, ',', n)))) {
                    if (!(u->lines[carry].out & LP_A)) {
                        l->deleted = 1;
                        lp_set(&u->lines[carry], "    cp%c %.*s", from_y ? 'y' : 'x', (int)n,
                               operand);
                        ++changed;
                        continue;
                    } else {
                        int br = lp_next(u, (unsigned)carry, 1), after_br = -1, target;
                        target = lp_cond_branch_target(u, br, &after_br);
                        if (target >= 0 &&
                            !(u->lines[target].live & (u->lines[target].m8 ? LP_AL : LP_A))) {
                            unsigned t = (unsigned)after_br + 1;
                            while (t < u->count && !u->lines[t].op && u->lines[t].length &&
                                   (u->lines[t].text[0] == ';' || u->lines[t].deleted ||
                                    (u->lines[t].label && u->lines[t].first_incoming < 0)))
                                ++t;
                            if (t < u->count && u->lines[t].op && !u->lines[t].deleted &&
                                !u->lines[t].replace && !u->lines[t].m8 && !u->lines[t].x8 &&
                                lp_line_is(&u->lines[t], from_y ? "tax" : "tay") &&
                                !(u->lines[t].out & (LP_A | LP_N | LP_Z))) {
                                l->deleted = 1;
                                lp_set(&u->lines[carry], "    cp%c %.*s", from_y ? 'y' : 'x',
                                       (int)n, operand);
                                lp_set(&u->lines[t], from_y ? "    tyx" : "    txy");
                                ++changed;
                                continue;
                            }
                        }
                    }
                }
            }
            if (carry >= 0 &&
                (lp_line_is(&u->lines[carry], "clc") || lp_line_is(&u->lines[carry], "sec"))) {
                int arith = lp_next(u, (unsigned)carry, 1);
                int transfer = arith >= 0 ? lp_next(u, (unsigned)arith, 1) : -1;
                int add = lp_line_is(&u->lines[carry], "clc");
                long count = arith >= 0 ? lp_immediate(&u->lines[arith]) : -1;
                if (transfer >= 0 && count > 0 && count <= 3 &&
                    lp_is(&u->lines[arith], add ? "adc" : "sbc") &&
                    lp_line_is(&u->lines[transfer], from_y ? "tay" : "tax") &&
                    !(u->lines[transfer].out & (LP_A | LP_C | LP_V)) && !u->lines[carry].deleted &&
                    !u->lines[carry].replace && !u->lines[arith].deleted &&
                    !u->lines[arith].replace && !u->lines[transfer].deleted &&
                    !u->lines[transfer].replace) {
                    const char *step = from_y ? (add ? "iny" : "dey") : (add ? "inx" : "dex");
                    char text[32] = "";
                    long j;
                    for (j = 0; j < count; ++j) {
                        if (j)
                            strcat(text, "\n");
                        strcat(text, "    ");
                        strcat(text, step);
                    }
                    l->deleted = u->lines[carry].deleted = u->lines[arith].deleted = 1;
                    lp_set(&u->lines[transfer], "%s", text);
                    ++changed;
                    continue;
                }
            }
            for (k = lp_next(u, i, 1);
                 k >= 0 && (lp_line_is(&u->lines[k], "inc a") || lp_line_is(&u->lines[k], "dec a"));
                 k = lp_next(u, (unsigned)k, 1)) {
                int d = lp_line_is(&u->lines[k], "inc a") ? 1 : -1;
                if (dir && d != dir)
                    break;
                dir = d;
                ++steps;
            }
            if (k < 0 || u->lines[k].out & LP_A || u->lines[k].replace || u->lines[k].deleted)
                continue;
            if (from_y && lp_line_is(&u->lines[k], "tay") && steps && steps <= 3) {
                int j;
                for (j = (int)i; j <= k; ++j)
                    if (u->lines[j].op)
                        u->lines[j].deleted = 1;
                {
                    char text[48] = "";
                    int s;
                    for (s = 0; s < steps; ++s)
                        strcat(text, s ? "\n    iny" : "    iny");
                    if (dir < 0) {
                        char *q;
                        for (q = text; (q = strstr(q, "iny")) != NULL; q += 3)
                            q[0] = 'd', q[1] = 'e';
                    }
                    lp_set(&u->lines[k], "%s", text);
                }
                ++changed;
                continue;
            }
            if (!steps && lp_line_is(&u->lines[k], from_y ? "tax" : "tay")) {
                l->deleted = 1;
                lp_set(&u->lines[k], from_y ? "    tyx" : "    txy");
                ++changed;
                continue;
            }
            continue;
        }
        if (!changed && (lp_line_is(l, "tyx") || lp_line_is(l, "txy"))) {
            /* Keep the transfer establishing equality intact for this round.
             * Reparse before the indexed-address rewrites reconsider it. */
            for (k = lp_next_mode(u, i); k >= 0; k = lp_next_mode(u, (unsigned)k)) {
                LpLine *same = &u->lines[k];
                if (same->x8 || same->deleted || same->replace)
                    break;
                if (lp_line_is(same, "tyx") || lp_line_is(same, "txy")) {
                    if (!(same->out & (LP_N | LP_Z))) {
                        same->deleted = 1;
                        return 1;
                    }
                    continue;
                }
                if (lp_line_is(same, "sep #$20") || lp_line_is(same, "rep #$20"))
                    continue;
                if (same->call || same->ends || lp_branch(same) || (same->def & (LP_X | LP_Y)) ||
                    same->use == LP_ALL)
                    break;
            }
        }
        if (lp_line_is(l, "tyx") && !(l->out & (LP_N | LP_Z))) {
            int j, uses, end, start = lp_next_mode(u, i), ok = 1;
            if (start < 0 || (end = lp_index_run(u, start, &uses, 0)) < 0)
                continue;
            for (j = start; j >= 0; j = lp_next_mode(u, (unsigned)j)) {
                if (u->lines[j].op && (u->lines[j].def & LP_Y))
                    ok = 0;
                if (j == end)
                    break;
            }
            if (!ok)
                continue;
            for (j = start; j >= 0; j = lp_next_mode(u, (unsigned)j)) {
                LpLine *c = &u->lines[j];
                size_t m;
                const char *p = lp_operand(c, &m);
                if (c->op && (c->use & LP_X))
                    lp_set(c, "    %.3s %.7s,y", c->op, p);
                if (j == end)
                    break;
            }
            l->deleted = 1;
            ++changed;
            i = (unsigned)end;
        }
    }
    return changed;
}

/* Loop depth of every line from backward branches */
static void lp_depths(const LpUnit *u, unsigned *depth)
{
    unsigned i, j;

    for (i = 0; i < u->count; ++i)
        depth[i] = 0;

    for (j = 0; j < u->count; ++j)
        if (u->lines[j].op && u->lines[j].target >= 0 && (unsigned)u->lines[j].target < j)
            for (i = (unsigned)u->lines[j].target; i <= j; ++i)
                ++depth[i];
}

/* Bytes pushed since entry before each line (-1 unreached), along every path;
 * 0 when a push depth is unknown or differs between paths into a label. */
static int lp_stack_depths_from(const LpUnit *u, unsigned first, int initial, int *sd)
{
    unsigned *work = malloc((u->count + 1) * sizeof *work), top = 0, i;
    int ok = 1;

    if (!work) {
        fputs("out of memory emitting assembly\n", stderr);
        exit(EXIT_FAILURE);
    }

    for (i = 0; i < u->count; ++i)
        sd[i] = -1;
    sd[first] = initial;
    work[top++] = first;

    while (ok && top) {
        unsigned k = work[--top];
        int d = sd[k];
        for (; k < u->count; ++k) {
            const LpLine *l = &u->lines[k];
            int delta = 0;
            if (sd[k] >= 0 && sd[k] != d) {
                ok = 0;
                break;
            }
            if (sd[k] < 0)
                sd[k] = d;
            if (!l->op)
                continue;
            if (lp_is(l, "pha"))
                delta = l->m8 ? 1 : 2;
            else if (lp_is(l, "pla"))
                delta = l->m8 ? -1 : -2;
            else if (lp_is(l, "phx") || lp_is(l, "phy"))
                delta = l->x8 ? 1 : 2;
            else if (lp_is(l, "plx") || lp_is(l, "ply"))
                delta = l->x8 ? -1 : -2;
            else if (lp_is(l, "php") || lp_is(l, "phb") || lp_is(l, "phk"))
                delta = 1;
            else if (lp_is(l, "plp") || lp_is(l, "plb"))
                delta = -1;
            else if (lp_is(l, "phd") || lp_is(l, "pea") || lp_is(l, "pei") || lp_is(l, "per"))
                delta = 2;
            else if (lp_is(l, "pld"))
                delta = -2;
            else if (lp_is(l, "tcs")) {
                int b = lp_next(u, k, -1), c = b >= 0 ? lp_next(u, (unsigned)b, -1) : -1,
                    t = c >= 0 ? lp_next(u, (unsigned)c, -1) : -1;
                if (t < 0 || !lp_line_is(&u->lines[t], "tsc")) {
                    ok = 0;
                    break;
                }
                if (lp_line_is(&u->lines[c], "clc") && !strncmp(u->lines[b].op, "adc #$", 6))
                    delta = -(int)strtoul(u->lines[b].op + 6, NULL, 16);
                else if (lp_line_is(&u->lines[c], "sec") && !strncmp(u->lines[b].op, "sbc #$", 6))
                    delta = (int)strtoul(u->lines[b].op + 6, NULL, 16);
                else {
                    ok = 0;
                    break;
                }
            } else if (lp_is(l, "txs") || lp_is(l, "rti") || lp_is(l, "mvn") || lp_is(l, "mvp")) {
                ok = 0;
                break;
            }
            d += delta;
            if (d < 0) {
                ok = 0;
                break;
            }
            if ((lp_is(l, "rts") || lp_is(l, "rtl") || (l->call && l->ends)) && d) {
                ok = 0;
                break;
            }
            if (l->target >= 0) {
                if (sd[l->target] < 0) {
                    sd[l->target] = d;
                    work[top++] = (unsigned)l->target;
                } else if (sd[l->target] != d) {
                    ok = 0;
                    break;
                }
            } else if (l->use == LP_ALL && lp_branch(l)) {
                ok = 0;
                break;
            }
            if (l->ends)
                break;
            if (k + 1 < u->count && sd[k + 1] >= 0) {
                if (sd[k + 1] != d)
                    ok = 0;
                break;
            }
        }
    }
    free(work);
    return ok;
}

static int lp_stack_depths(const LpUnit *u, unsigned first, int *sd)
{
    return lp_stack_depths_from(u, first, 0, sd);
}
