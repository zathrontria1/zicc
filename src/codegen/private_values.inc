/* Value forwarding and byte-accurate dead stores in compiler-owned homes.
 * Unknown calls/indirect writes are barriers for copies; frame dead-store
 * analysis is limited to unescaped C scalars and compiler-created slots. */
static int pv_math(const LpLine *l, unsigned *writes, int *result)
{
    size_t n;
    const char *p = lp_operand(l, &n);

    unsigned i;

    if (!l->call) {
        return 0;
    }

    if (n > 8 && !strncmp(p, ".loword(", 8)) {
        p += 8;
        n -= 9;
    }

    if (!((n == 7 && !strncmp(p, "__mul16", 7)) || (n == 6 && !strncmp(p, "__mul8", 6)) ||
          (n == 9 && (!strncmp(p, "__mul8x16", 9) || !strncmp(p, "__mul16x8", 9) ||
                      !strncmp(p, "__uquot16", 9))) ||
          (n == 8 && (!strncmp(p, "__udiv16", 8) || !strncmp(p, "__umod16", 8) ||
                      !strncmp(p, "__uquot8", 8))) ||
          (n == 7 && (!strncmp(p, "__udiv8", 7) || !strncmp(p, "__umod8", 7)))))
        return 0;

    for (i = 0; i < sizeof helper_clobbers / sizeof *helper_clobbers; ++i) {
        if (strlen(helper_clobbers[i].name) == n && !strncmp(helper_clobbers[i].name, p, n))
            break;
    }

    if (i == sizeof helper_clobbers / sizeof *helper_clobbers)
        return 0;

    *writes = helper_clobbers[i].writes;
    /* The paired divider and word multipliers publish a copy of A in
     * scratch. Standalone results and the byte multiplier may leave it stale. */
    *result = p[2] == 'u' && p[3] == 'd' ? 0 : p[2] == 'm' && n > 6 ? 8 : -1;
    return 1;
}

static int pv_key(const LpLine *l, char *key)
{
    size_t n;
    const char *p = lp_operand(l, &n);
    int w = lp_workspace_word(p, n);

    if (w >= 0) {
        snprintf(key, 128, "z:__arith_lhs+%d", w);
        return 1;
    }

    if (n >= 4 && n < 128 && !strncmp(p, "a:_", 3)) {
        size_t i;

        for (i = 3; i < n && (isalnum((unsigned char)p[i]) || p[i] == '_'); ++i) {
        }

        if (i == n) {
            memcpy(key, p, n);
            key[n] = 0;
            return 1;
        }
    }

    if (n > 12 && !strncmp(p, "a:.loword(_", 11) && p[n - 1] == ')') {
        size_t i;

        for (i = 11; i < n - 1 && (isalnum((unsigned char)p[i]) || p[i] == '_'); ++i) {
        }

        if (i == n - 1) {
            snprintf(key, 128, "a:%.*s", (int)(n - 11), p + 10);
            return 1;
        }
    }

    if (n < 128 && (lp_private(p, n))) {
        memcpy(key, p, n);
        key[n] = 0;
        return 1;
    }

    return 0;
}

static int pv_overlap(const char *a, const char *b)
{
    int x = lp_workspace_word(a, strlen(a)), y = lp_workspace_word(b, strlen(b));

    if (x >= 0 && y >= 0)
        return x <= y + 1 && y <= x + 1;
    if (strlen(a) == 9 && strlen(b) == 9 && !strncmp(a, "a:$", 3) && !strncmp(b, "a:$", 3) &&
        a[8] == 'y' && b[8] == 'y') {
        long p = strtol(a + 3, NULL, 16), q = strtol(b + 3, NULL, 16);

        return p <= q + 1 && q <= p + 1;
    }
    if (strstr(a, ",s") && strstr(b, ",s")) {
        long p = strtol(a, NULL, 10), q = strtol(b, NULL, 10);

        return p <= q + 1 && q <= p + 1;
    }

    return !strcmp(a, b);
}

static unsigned pv_workspace_words(const char *key)
{
    int offset = lp_workspace_word(key, strlen(key));

    if (offset < 0)
        return 0;

    return (offset & 1 ? 3u : 1u) << (offset / 2);
}

static int lp_private_copies(LpUnit *u, Function *f, size_t at)
{
    struct {
        char key[128], value[128];
        int bytes;
    } copies[64];

    char a[128] = "";
    int bytes = 0;

    unsigned count = 0, i, j;
    int changed = 0;

    (void)f;
    (void)at;

    if (lp_state.is_volatile || u->indirect)
        return 0;

    lp_liveness(u);

    for (i = 0; i < u->count; ++i) {
        LpLine *l = &u->lines[i];
        char key[128];
        int iskey;

        if (!l->op) {
            if (l->label) {
                unsigned k;
                int entry = strncmp(l->text, "__inlined_", 10) != 0;

                for (k = 0; !entry && k < u->count; ++k) {
                    if (u->lines[k].op && u->lines[k].target == (int)i)
                        entry = 1;
                }

                if (entry) {
                    count = 0;
                    a[0] = 0;
                    bytes = 0;
                }
            }

            continue;
        }

        iskey = pv_key(l, key);

        if (l->call) {
            unsigned mask;
            int result;

            if (!pv_math(l, &mask, &result)) {
                count = 0;
                a[0] = 0;
                bytes = 0;
                continue;
            }

            for (j = 0; j < count;) {
                if (mask &
                    (pv_workspace_words(copies[j].value) | pv_workspace_words(copies[j].key))) {
                    copies[j] = copies[--count];
                    continue;
                }

                ++j;
            }

            if (result >= 0) {
                snprintf(a, sizeof a, "z:__arith_lhs+%d", result);
                bytes = 2;
            } else {
                a[0] = 0;
                bytes = 0;
            }

            continue;
        }

        if (lp_store_op(l)) {
            if (!iskey) {
                count = 0;
                a[0] = 0;
                bytes = 0;
                continue;
            }

            for (j = 0; j < count;) {
                if (pv_overlap(copies[j].key, key) || pv_overlap(copies[j].value, key) ||
                    (!strncmp(key, "a:_", 3) && !strncmp(copies[j].key, "a:_", 3)))
                    copies[j] = copies[--count];
                else
                    ++j;
            }

            /* A partial overwrite invalidates the source for the new copy too */
            if (a[0] && strcmp(a, key) && pv_overlap(a, key)) {
                a[0] = 0;
                bytes = 0;
            }

            if (lp_is(l, "sta") && a[0] && bytes >= lp_width(l) && strcmp(a, key) && count < 64) {
                strcpy(copies[count].key, key);
                strcpy(copies[count].value, a);
                copies[count++].bytes = lp_width(l);
            }

            if (lp_is(l, "sta") && !a[0]) {
                strcpy(a, key);
                bytes = lp_width(l);
            } else if (a[0] && pv_overlap(a, key) && !lp_is(l, "sta")) {
                a[0] = 0;
                bytes = 0;
            }

            continue;
        }

        if (lp_is(l, "lda") && iskey) {
            int need = lp_width(l), k = lp_next(u, i, 1);

            if (k >= 0 && lp_line_is(&u->lines[k], "and #$00FF"))
                need = 1;

            for (j = 0; j < count; ++j) {
                if (!strcmp(copies[j].key, key) && copies[j].bytes >= need) {
                    if (strcmp(key, copies[j].value)) {
                        lp_set(l, "    lda %s", copies[j].value);
                        ++changed;
                        strcpy(key, copies[j].value);
                    }

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

        if (lp_line_is(l, "and #$00FF") && a[0]) {
            bytes = 1;
            continue;
        }

        if (lp_stack_op(l)) {
            for (j = 0; j < count;) {
                if (strstr(copies[j].key, ",s") || strstr(copies[j].value, ",s"))
                    copies[j] = copies[--count];
                else
                    ++j;
            }

            if (strstr(a, ",s")) {
                a[0] = 0;
                bytes = 0;
            }
        }

        if (lp_is(l, "rep") || lp_is(l, "sep"))
            continue;

        if (l->def & LP_Y) {
            count = 0;
            a[0] = 0;
            bytes = 0;
        }

        if ((l->def & LP_A) || lp_is(l, "lda") || lp_is(l, "xba") || lp_is(l, "txa") ||
            lp_is(l, "tya") || lp_is(l, "pla") || lp_is(l, "adc") || lp_is(l, "sbc") ||
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

    return changed;
}

static int pv_frame_private(Function *f, unsigned byte, int native_longs)
{
    for (unsigned i = 0; i < lp_state.parser->symbol_count; ++i) {
        Symbol *v = &lp_state.parser->symbols[i];

        if (v->owner != f->id || !v->offset || byte + 1 < v->offset ||
            byte >= v->offset + width(v->type))
            continue;
        if (body_private(v))
            continue;
        if (native_longs && !v->type.pointers && !v->type.array && v->type.base == TY_LONG &&
            !object_volatile(v->type) && loop_private(v))
            continue;

        return 0;
    }

    return byte > 0 && byte <= f->slots;
}

static int pv_private_word_step(LpUnit *u, unsigned at, const char *operand, size_t n)
{
    int end = lp_next(u, at, 1);

    if (end < 0 || (!lp_line_is(&u->lines[end], "inc a") && !lp_line_is(&u->lines[end], "dec a")))
        return -1;

    do {
        end = lp_next(u, (unsigned)end, 1);
    } while (end >= 0 &&
             (lp_line_is(&u->lines[end], "inc a") || lp_line_is(&u->lines[end], "dec a")));

    if (end < 0 || u->lines[end].m8 || !lp_is(&u->lines[end], "sta") ||
        !lp_operand_is(&u->lines[end], operand, n) || u->lines[end].out & (LP_A | LP_N | LP_Z))
        return -1;

    return end;
}

static int lp_private_dead_stores_impl(LpUnit *u, Function *f, int relocated)
{
    unsigned word, i;
    unsigned char *use, *def, *live, *out, *step;
    int changed = 0;
    PrState *frames;

    if (lp_state.is_volatile || u->indirect)
        return 0;

    frames = !relocated && f->slots ? pr_states(u) : NULL;

    /* With one addressing convention, both words of an unescaped native
     * long are ordinary frame homes. All observations use the same Y base. */
    int native_longs =
        frames && !lp_state.parser->no_private_regions && !body_asm_statements(f->body);

    for (i = 0; i < u->count && native_longs; ++i) {
        size_t n;
        const char *operand = lp_operand(&u->lines[i], &n);

        for (size_t j = 1; j < n; ++j) {
            if (operand[j - 1] == ',' && operand[j] == 's') {
                native_longs = 0;
                break;
            }
        }
    }

    if (frames)
        lp_liveness(u);

    use = calloc(u->count * 5, 1);

    if (!use) {
        fputs("out of memory\n", stderr);
        exit(EXIT_FAILURE);
    }

    def = use + u->count;
    live = def + u->count;
    out = live + u->count;
    step = out + u->count;

    for (word = 0; word < 16 + (relocated ? 0 : (f->slots + 1) / 2); ++word) {
        int frame = word >= 16, base = frame ? (int)(word - 16) * 2 + 1 : (int)word * 2;
        int again = 1;

        if (frame && !pv_frame_private(f, (unsigned)base, native_longs))
            continue;

        memset(use, 0, u->count * 5);

        for (i = 0; i < u->count; ++i) {
            LpLine *l = &u->lines[i];
            size_t n;
            const char *p = lp_operand(l, &n);
            int w = -1, j;

            unsigned mask = 0;
            int result;

            if (!l->op)
                continue;

            if (l->call) {
                if (!frame) {
                    Symbol *callee = relocated ? lp_callee(l) : NULL;

                    if (pv_math(l, &mask, &result)) {
                        use[i] = (word == 0 || word == 2) ? 3 : 0;
                        def[i] = (mask & (1u << word)) ? 3 : 0;
                    } else if (!callee || callee->interrupt)
                        use[i] = 3;

                    /* Ordinary C calls take no scratch inputs. Still propagate
                     * later reads through the call, since it may preserve DP. */
                }

                continue;
            }

            if (l->use == LP_ALL && !lp_is(l, "rep") && !lp_is(l, "sep")) {
                use[i] = 3;
                continue;
            }

            if (frame) {
                if (n == 9 && !strncmp(p, "a:$", 3) && p[7] == ',' && p[8] == 'y') {
                    if (!frames[i].frame || l->x8) {
                        use[i] = 3;
                        continue;
                    }

                    w = (int)strtol(p + 3, NULL, 16);
                }
            } else
                w = lp_workspace_word(p, n);

            if (w < 0) {
                if (!frame && (lp_text_words(p, p + n) & (1u << word)))
                    use[i] = 3;

                continue;
            }

            for (j = 0; j < lp_width(l); ++j) {
                if (w + j >= base && w + j < base + 2)
                    mask |= 1u << (w + j - base);
            }

            if (!mask)
                continue;
            if (step[i])
                continue;
            if (frame && mask == 3 && lp_is(l, "lda") &&
                (j = pv_private_word_step(u, i, p, n)) >= 0) {
                step[j] = 1;
                continue;
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
                if (l->target >= 0)
                    o |= live[l->target];

                /* A private step reads its old word only if the new word is live */
                v = step[i] ? (o ? 3 : 0) : use[i] | (o & ~def[i]);

                if (v != live[i] || o != out[i]) {
                    live[i] = (unsigned char)v;
                    out[i] = (unsigned char)o;
                    again = 1;
                }
            }
        }

        for (i = 0; i < u->count; ++i) {
            if (def[i] && (lp_width(&u->lines[i]) == 1 || def[i] == 3) && !(def[i] & out[i]) &&
                !use[i] && !u->lines[i].call && !u->lines[i].deleted) {
                u->lines[i].deleted = 1;
                ++changed;
            }
        }

        for (i = 0; i < u->count; ++i) {
            if (step[i] && !out[i]) {
                int j = (int)i;

                do {
                    u->lines[j].deleted = 1;
                    j = lp_next(u, (unsigned)j, -1);
                } while (!lp_is(&u->lines[j], "lda"));

                u->lines[j].deleted = 1;
                ++changed;
            }
        }
    }

    free(frames);
    free(use);
    return changed;
}

static int lp_private_dead_stores(LpUnit *u, Function *f, size_t at)
{
    (void)at;
    return lp_private_dead_stores_impl(u, f, 0);
}

static int lp_relocated_dead_stores(LpUnit *u, Function *f, size_t at)
{
    (void)at;
    return lp_private_dead_stores_impl(u, f, 1);
}

/* Trim trailing dead frame homes after value/store elimination. All surviving
 * Y accesses and object-address formations must be understood; incoming stack
 * arguments move by the same delta to preserve their physical addresses. */
static int lp_trim_private_frame(LpUnit *u, Function *f, size_t at)
{
    unsigned i, j, max = 0, old = 0, fresh;
    int pro = -1, region = 0, found = 0;

    (void)at;

    /* Index-register address formation and inlined homes need the full caller frame */
    if (lp_state.is_volatile || lp_state.frame_address || u->indirect ||
        strstr(u->text, "; block copy payload "))
        return 0;

    for (i = 0; i < u->count; ++i) {
        if (lp_line_is(&u->lines[i], "tsc")) {
            int a = lp_next(u, i, 1), b = a < 0 ? -1 : lp_next(u, (unsigned)a, 1),
                c = b < 0 ? -1 : lp_next(u, (unsigned)b, 1),
                d = c < 0 ? -1 : lp_next(u, (unsigned)c, 1);
            long n;

            if (a >= 0 && b >= 0 && c >= 0 && d >= 0 && lp_line_is(&u->lines[a], "sec") &&
                lp_is(&u->lines[b], "sbc") && (n = lp_immediate(&u->lines[b])) > 0 &&
                lp_line_is(&u->lines[c], "tcs") && lp_line_is(&u->lines[d], "tay")) {
                if (pro >= 0)
                    return 0;

                pro = b;
                old = (unsigned)n;
            }
        }
    }

    if (pro < 0)
        return 0;

    for (i = 0; i < u->count; ++i) {
        LpLine *l = &u->lines[i];
        size_t n;
        const char *p = lp_operand(l, &n);

        if (!l->op) {
            if (l->length > 28 && !strncmp(l->text, "; arithmetic indexed region:", 28) &&
                memchr(l->text, 'Y', l->length))
                region = 1;

            continue;
        }
        if (region) {
            if (lp_is(l, "ply"))
                region = 0;

            continue;
        }

        if (n == 9 && !strncmp(p, "a:$", 3) && p[7] == ',' && p[8] == 'y') {
            unsigned off = (unsigned)strtoul(p + 3, NULL, 16);

            if (off <= old && off + (unsigned)lp_width(l) - 1 > max)
                max = off + (unsigned)lp_width(l) - 1;
        }

        if (lp_line_is(l, "tya")) {
            int a = lp_next(u, i, 1), b = a < 0 ? -1 : lp_next(u, (unsigned)a, 1),
                c = b < 0 ? -1 : lp_next(u, (unsigned)b, 1);
            long off;

            if (a < 0 || b < 0 || !lp_line_is(&u->lines[a], "clc") || !lp_is(&u->lines[b], "adc") ||
                (off = lp_immediate(&u->lines[b])) < 0)
                return 0;
            if (c >= 0 && lp_line_is(&u->lines[c], "tcs")) {
                if ((unsigned)off != old)
                    return 0;

                ++found;
                continue;
            }

            for (j = 0; j < lp_state.parser->symbol_count; ++j) {
                Symbol *v = &lp_state.parser->symbols[j];

                if (v->owner == f->id && v->offset && (unsigned)off >= v->offset &&
                    (unsigned)off <= v->offset + width(v->type)) {
                    unsigned end = v->offset + width(v->type) - 1;

                    if (end > max)
                        max = end;

                    break;
                }
            }

            if (j == lp_state.parser->symbol_count)
                return 0;
        }
    }

    fresh = (max + 1) & ~1u;

    if (!found || !fresh || fresh >= old)
        return 0;

    lp_set(&u->lines[pro], "    sbc #$%04X", fresh);
    region = 0;

    for (i = 0; i < u->count; ++i) {
        LpLine *l = &u->lines[i];
        size_t n;
        const char *p = lp_operand(l, &n);

        if (!l->op) {
            if (l->length > 28 && !strncmp(l->text, "; arithmetic indexed region:", 28) &&
                memchr(l->text, 'Y', l->length))
                region = 1;

            continue;
        }
        if (region) {
            if (lp_is(l, "ply"))
                region = 0;

            continue;
        }

        if (n == 9 && !strncmp(p, "a:$", 3) && p[7] == ',' && p[8] == 'y') {
            unsigned off = (unsigned)strtoul(p + 3, NULL, 16);

            if (off > old)
                lp_set(l, "    %.3s a:$%04X,y", l->op, off - (old - fresh));
        }

        if (lp_line_is(l, "tya")) {
            int a = lp_next(u, i, 1), b = lp_next(u, (unsigned)a, 1),
                c = lp_next(u, (unsigned)b, 1);

            if (c >= 0 && lp_line_is(&u->lines[c], "tcs"))
                lp_set(&u->lines[b], "    adc #$%04X", fresh);
        }
    }

    return 1;
}
