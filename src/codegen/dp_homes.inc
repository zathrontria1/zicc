/* Direct-page homes (Phase A v1). The ABI makes the 32-byte arithmetic
 * workspace call-clobbered, so a function that makes no ordinary call may keep
 * frame words there. Emission is speculative: a trial with ordinary homes finds
 * the workspace words and helper clobbers the body needs, the hottest frame
 * words take the remaining workspace words, and the promoted emission is kept
 * only if it re-validates; otherwise the function is emitted unchanged. */
static const struct {
    const char *name;
    unsigned writes;
} helper_clobbers[] = {
    /* Workspace words (bit n = scratch offset 2n) each runtime/integers.s entry may write,
     * derived by tools/helper-clobbers.py; tests/check-dp-homes.py checks it. */
    /* helper-clobbers begin */
        {"__mul16",0x0010},
        {"__mul16wide",0x0030},
        {"__mul16x32",0x0030},
        {"__mul16x8",0x0010},
        {"__mul32",0x00F0},
        {"__mul8",0x0000},
        {"__mul8x16",0x0010},
        {"__scmp16",0x0000},
        {"__scmp32",0x0000},
        {"__sdiv16",0x0055},
        {"__sdiv32",0x007F},
        {"__sdivmod16",0x00D5},
        {"__sdivmod32",0x00FF},
        {"__shl32",0x0003},
        {"__smod16",0x0095},
        {"__smod32",0x00BF},
        {"__sshr32",0x0003},
        {"__ucmp16",0x0000},
        {"__ucmp32",0x0000},
        {"__udiv16",0x0011},
        {"__udiv32",0x0033},
        {"__udiv8",0x0011},
        {"__umod16",0x0011},
        {"__umod32",0x0033},
        {"__umod8",0x0000},
        {"__uquot16",0x0011},
        {"__uquot32",0x0033},
        {"__uquot8",0x0000},
        {"__ushr32",0x0003},
/* helper-clobbers end */
};

static void emit_function_frame(Function *f, int frame_base, unsigned possible_registers,
                                size_t start);

/* Same-unit clobber summaries: the workspace words each function already
 * emitted in this unit may touch, including its helpers' and its own known
 * callees' words. A function that makes any other call has no summary, so
 * recursion and calls to later or external functions stay unresolved. */
static struct {
    char name[132];
    unsigned writes;
} dp_summaries[1024];

static unsigned dp_summary_count;

static int dp_call_target_info(const char *name, size_t n, unsigned *writes, int *is_summary)
{
    unsigned i;
    char near_name[132], smul_name[132], pack_name[132];

    if (is_summary)
        *is_summary = 0;

    near_strcmp_name(near_name, sizeof near_name);

    if (strlen(near_name) == n && !strncmp(near_name, name, n)) {
        *writes |= 3;
        return 1;
    }

    zicc_smul8_name(smul_name, sizeof smul_name);

    if (strlen(smul_name) == n && !strncmp(smul_name, name, n))
        return 1;

    zicc_pack_coeff_name(pack_name, sizeof pack_name);

    if (strlen(pack_name) == n && !strncmp(pack_name, name, n))
        return 1;

    for (i = 0; i < sizeof helper_clobbers / sizeof *helper_clobbers; ++i) {
        if (strlen(helper_clobbers[i].name) == n && !strncmp(helper_clobbers[i].name, name, n)) {
            *writes |= helper_clobbers[i].writes;
            return 1;
        }
    }

    if (!cg.parser->no_dp_summaries)
        for (i = 0; i < dp_summary_count; ++i) {
            if (strlen(dp_summaries[i].name) == n && !strncmp(dp_summaries[i].name, name, n)) {
                if (is_summary)
                    *is_summary = 1;

                *writes |= dp_summaries[i].writes;
                return 1;
            }
        }

    return 0;
}

static int dp_call_target(const char *name, size_t n, unsigned *taken)
{
    return dp_call_target_info(name, n, taken, NULL);
}

static void dp_mark_width(unsigned *taken, unsigned byte, unsigned bytes)
{
    unsigned b;

    for (b = byte; b < byte + bytes && b < 32; ++b) {
        *taken |= 1u << (b / 2);
    }
}

static void dp_mark(unsigned *taken, unsigned byte)
{
    dp_mark_width(taken, byte, 4);
}

/* Collect the workspace words [start,length) references other than home
 * placeholders, plus helper clobbers. Return 0 for any other call or an
 * indirect transfer, whose clobbers are unknown. */
static int dp_scan_range_mode(size_t start, size_t stop, unsigned *taken, int skip_summaries)
{
    const char *p = cg.assembly + start, *end = cg.assembly + stop;

    *taken = 0;
    while (p < end) {
        const char *eol = memchr(p, '\n', (size_t)(end - p)), *t = p, *q;

        if (!eol)
            eol = end;

        while (t < eol && *t == ' ') {
            ++t;
        }

        if (eol - t > 4 && (!strncmp(t, "jsr ", 4) || !strncmp(t, "jsl ", 4) ||
                            !strncmp(t, "jmp ", 4) || !strncmp(t, "jml ", 4))) {
            const char *name = t + 4;
            size_t n;

            unsigned cw = 0;
            int is_sum = 0;

            if (*name == '(' || *name == '[')
                return 0;
            if (!strncmp(name, ".loword(", 8))
                name += 8;

            n = strcspn(name, ") \n");

            if (t[1] == 'm' &&
                (!strncmp(name, "cg_", 3) || !strncmp(name, "return_", 7) ||
                 !strncmp(name, "interrupt_body_", 15) || *name == ':' || *name == '@'))
                ;
            else if (!dp_call_target_info(name, n, &cw, &is_sum))
                return 0;
            else if (!is_sum || !skip_summaries)
                *taken |= cw;
        }

        for (q = p; q < eol; ++q) {
            if (eol - q >= 11 &&
                (!strncmp(q, "__arith_lhs", 11) || !strncmp(q, "__arith_rhs", 11))) {
                unsigned byte = q[8] == 'r' ? 4 : 0;
                unsigned bytes = (q > p && q[-1] == '[') ? 3 : 2;
                q += 11;

                if (q < eol && *q == '+') {
                    byte += (unsigned)strtoul(q + 1, (char **)&q, 10);
                }

                dp_mark_width(taken, byte, bytes);
                --q;
            } else if ((*q == '$') && q > p && (q[-1] == ':' || q[-1] == '[' || q[-1] == '(') &&
                       eol - q >= 3 && isxdigit((unsigned char)q[1]) &&
                       isxdigit((unsigned char)q[2]) &&
                       (eol - q == 3 || !isxdigit((unsigned char)q[3])))
                dp_mark_width(taken, (unsigned)strtoul(q + 1, NULL, 16) - 0xE0u,
                              q[-1] == '[' ? 3u : 2u);
        }

        p = eol + 1;
    }

    return 1;
}

static int dp_scan_range(size_t start, size_t stop, unsigned *taken)
{
    return dp_scan_range_mode(start, stop, taken, 0);
}

static int dp_scan(size_t start, unsigned *taken)
{
    return dp_scan_range(start, cg.length, taken);
}

static void dp_restore(const CodegenCheckpoint *saved, size_t start)
{
    cg_checkpoint_restore(saved, start);
}

/* Replace validated placeholders with their workspace operands */
static void dp_resolve(size_t start)
{
    size_t length = cg.length - start;
    char *text = malloc(length + 1);
    const char *p;

    if (!text) {
        fputs("out of memory emitting assembly\n", stderr);
        exit(EXIT_FAILURE);
    }

    memcpy(text, cg.assembly + start, length + 1);
    cg.length = start;

    for (p = text; *p;) {
        const char *hit = strstr(p, "__dp_home_");

        if (!hit) {
            code("%s", p);
            break;
        }

        unsigned offset = 2u * (unsigned)strtoul(hit + 10, NULL, 10);
        const char *end = hit + 12;

        if (!strncmp(end, "+1", 2) && !isdigit((unsigned char)end[2])) {
            ++offset;
            end += 2;
        }

        code("%.*s__arith_lhs+%u", (int)(hit - p), p, offset);
        p = end;
    }

    free(text);
    cg.arithmetic = 1;
}

static int dp_scan(size_t start, unsigned *taken);

/* Record the summary of the function just emitted from start */
static void dp_summarize(Function *f, size_t start)
{
    unsigned taken;

    if (f->symbol->interrupt || dp_summary_count == sizeof dp_summaries / sizeof *dp_summaries ||
        !dp_scan(start, &taken))
        return;

    snprintf(dp_summaries[dp_summary_count].name, sizeof dp_summaries[0].name, "_%s",
             f->symbol->asm_name);
    dp_summaries[dp_summary_count++].writes = taken;
}

static int dp_parameter_home(Function *f, unsigned i)
{
    Symbol *v = leaf_parameter(f, i);

    unsigned word;

    if (!dp_state.homes || !v || !v->offset)
        return 0;

    word = (v->offset - 1) / 2;
    return word < dp_state.words && dp_state.map[word];
}

/* Store live register parameters straight into promoted homes at entry */
static void dp_home_parameters(Function *f)
{
    unsigned i;

    for (i = 0; i < 2 && i < (unsigned)(f->symbol->param_count < 0 ? 0 : f->symbol->param_count);
         ++i) {
        if ((cg.register_spills & (1u << i)) && dp_parameter_home(f, i))
            code("    %s %s\n", i ? "sta" : "stx", frame_operand(leaf_parameter(f, i)->offset));
    }
}

static uint64_t dp_ast_words(Function *f, Symbol *s, unsigned words)
{
    uint64_t mask = 0;

    unsigned w;

    if (!s || s->owner != f->id || !s->offset || s->offset > f->slots)
        return 0;

    w = (s->offset - 1) / 2;

    if (w < words && w < 64)
        mask |= UINT64_C(1) << w;

    if (width(s->type) == 4) {
        w = (s->offset + 1) / 2;

        if (w < words && w < 64)
            mask |= UINT64_C(1) << w;
    }

    return mask;
}

static uint64_t dp_ast_refs_skip(Function *f, Expr *e, unsigned words, Expr *skip)
{
    uint64_t r = 0;

    unsigned i;

    DotProduct *dp;

    if (!e || e == skip)
        return 0;

    if ((dp = dot_match_expr(e)) != NULL) {
        unsigned k;
        r |= dp_ast_words(f, dp->bias_sym, words);

        for (k = 0; k < dp->term_count; ++k) {
            r |= dp_ast_words(f, dp->terms[k].pack_sym, words);
            r |= dp_ast_refs_skip(f, dp->terms[k].value_expr, words, skip);
        }

        return r;
    }

    if (e->kind == EX_OBJECT)
        r |= dp_ast_words(f, e->symbol, words);

    r |= dp_ast_refs_skip(f, e->left, words, skip);
    r |= dp_ast_refs_skip(f, e->right, words, skip);
    r |= dp_ast_refs_skip(f, e->third, words, skip);

    for (i = 0; i < e->arg_count; ++i) {
        r |= dp_ast_refs_skip(f, e->args[i], words, skip);
    }

    return r;
}

static int dp_find_summary(const char *asm_name, unsigned *writes)
{
    unsigned i;
    char full[132];

    snprintf(full, sizeof full, "_%s", asm_name);

    for (i = 0; i < dp_summary_count; ++i) {
        if (!strcmp(dp_summaries[i].name, full)) {
            *writes = dp_summaries[i].writes;
            return 1;
        }
    }

    return 0;
}

static void dp_ast_scan_calls(Function *f, Expr *root, Expr *e, uint64_t after, unsigned words,
                              unsigned *forbidden, int *ok)
{
    unsigned i;

    if (!e || !*ok)
        return;

    if (e->kind == EX_CALL) {
        unsigned cw = 0;
        Symbol *callee = e->symbol
                             ? e->symbol
                             : (e->left && e->left->kind == EX_OBJECT ? e->left->symbol : NULL);

        if (!callee || !callee->function || !strcmp(callee->name, "$basic_asm")) {
            *ok = 0;
            return;
        }

        if (dp_find_summary(callee->asm_name, &cw)) {
            uint64_t live = after | dp_ast_refs_skip(f, root, words, e);

            unsigned w;

            for (w = 0; w < words; ++w) {
                if (live & (UINT64_C(1) << w))
                    forbidden[w] |= cw;
            }
        }
    }

    dp_ast_scan_calls(f, root, e->left, after, words, forbidden, ok);
    dp_ast_scan_calls(f, root, e->right, after, words, forbidden, ok);
    dp_ast_scan_calls(f, root, e->third, after, words, forbidden, ok);

    for (i = 0; i < e->arg_count; ++i) {
        dp_ast_scan_calls(f, root, e->args[i], after, words, forbidden, ok);
    }
}

static uint64_t dp_ast_live_expr(Function *f, Expr *e, uint64_t after, unsigned words,
                                 unsigned *forbidden, int *ok)
{
    uint64_t before, def = 0;

    if (!e)
        return after;

    dp_ast_scan_calls(f, e, e, after, words, forbidden, ok);

    if (e->kind == EX_ASSIGN && !e->op && e->left->kind == EX_OBJECT)
        def = dp_ast_words(f, e->left->symbol, words);

    before = (after & ~def) | dp_ast_refs_skip(f, def ? e->right : e, words, NULL);
    return before;
}

static uint64_t dp_ast_live(Function *f, Statement *s, uint64_t after, uint64_t brk, uint64_t cont,
                            unsigned words, unsigned *forbidden, int *ok, unsigned *budget)
{
    uint64_t next, head, body, step, again;

    if (!s || !*ok)
        return after;
    if (!*budget) {
        *ok = 0;
        return UINT64_MAX;
    }

    --(*budget);
    next = dp_ast_live(f, s->next, after, brk, cont, words, forbidden, ok, budget);

    switch (s->kind) {
    case ST_EMPTY:
        return next;
    case ST_EXPR:
        return dp_ast_live_expr(f, s->expression, next, words, forbidden, ok);
    case ST_RETURN:
        return dp_ast_live_expr(f, s->expression, 0, words, forbidden, ok);
    case ST_BREAK:
        return brk;
    case ST_CONTINUE:
        return cont;
    case ST_BLOCK:
        return dp_ast_live(f, s->body, next, brk, cont, words, forbidden, ok, budget);
    case ST_IF:
        body = dp_ast_live(f, s->body, next, brk, cont, words, forbidden, ok, budget);
        step = dp_ast_live(f, s->alternate, next, brk, cont, words, forbidden, ok, budget);
        return dp_ast_live_expr(f, s->expression, body | step, words, forbidden, ok);
    case ST_FOR:
    case ST_WHILE:
    case ST_DO:
        head = 0;

        do {
            again = head;

            if (s->kind == ST_DO) {
                step = dp_ast_live_expr(f, s->expression, next | head, words, forbidden, ok);
                head = dp_ast_live(f, s->body, step, next, step, words, forbidden, ok, budget);
            } else {
                step = dp_ast_live_expr(f, s->step, head, words, forbidden, ok);
                body = dp_ast_live(f, s->body, step, next, step, words, forbidden, ok, budget);
                head = dp_ast_live_expr(f, s->expression, next | body, words, forbidden, ok);
            }
        } while (head != again && *ok);

        head = dp_ast_live(f, s->initial, head, brk, cont, words, forbidden, ok, budget);
        {
            uint64_t setup_kill = 0, setup_gen = 0;

            unsigned d, k;

            for (d = 0; d < dot_state.count; ++d) {
                if (dot_state.dots[d].loop == s)
                    setup_kill |= dp_ast_words(f, dot_state.dots[d].bias_sym, words);
            }

            for (k = 0; k < dot_state.pack_count; ++k) {
                if (dot_state.packs[k].loop == s) {
                    setup_kill |= dp_ast_words(f, dot_state.packs[k].pack_sym, words);
                    setup_gen |= dp_ast_words(f, dot_state.packs[k].coeff_sym, words);
                }
            }

            head = (head & ~setup_kill) | setup_gen;
        }
        return head;
    default:
        *ok = 0;
        return UINT64_MAX;
    }
}

static int dp_ast_call_clobbers(Function *f, unsigned words, unsigned *forbidden)
{
    int ok = 1;

    unsigned budget = 100000;

    if (words <= 14 || words > 64 || cg.cursor_count || cg.parser->no_dp_summaries ||
        statement_has_case(f->body))
        return 0;

    memset(forbidden, 0, words * sizeof *forbidden);
    dp_ast_live(f, f->body, 0, 0, 0, words, forbidden, &ok, &budget);

    if (ok) {
        unsigned all_summaries = 0, i;
        uint64_t covered = 0;

        for (i = 0; i < dp_summary_count; ++i) {
            all_summaries |= dp_summaries[i].writes;
        }

        for (i = 0; i < cg.parser->symbol_count; ++i) {
            Symbol *v = &cg.parser->symbols[i];

            if (v->owner == f->id && v->offset && loop_private(v))
                covered |= dp_ast_words(f, v, words);
        }

        for (i = 0; i < words; ++i) {
            if (!(covered & (UINT64_C(1) << i)))
                forbidden[i] |= all_summaries;
        }
    }

    return ok;
}

static int dp_homes_function(Function *f, unsigned possible_registers)
{
    static CodegenCheckpoint saved;

    static unsigned weight[384], order[384];
    unsigned forbidden[64] = {0};
    int precise = 0;
    size_t start = cg.length;

    unsigned taken, mapped = 0, words = (f->slots + 1) / 2, frame = f->frame, i, j, count = 0,
                    free_count = 0, free_words[16], assigned = 0;

    if (cg.parser->no_dp_homes || f->symbol->interrupt || volatile_statements(f->body) ||
        !f->slots || words > 384)
        return 0;

    precise = dp_ast_call_clobbers(f, words, forbidden);
    cg_checkpoint_save(&saved);
    memset(dp_state.weight, 0, sizeof dp_state.weight);
    dp_state.trial = 1;
    emit_function_frame(f, 1, possible_registers, start);
    dp_state.trial = 0;
    i = dp_scan_range_mode(start, cg.length, &taken, precise);
    memcpy(weight, dp_state.weight, sizeof weight);
    dp_restore(&saved, start);
    f->frame = frame;

    if (!i)
        return 0;

    for (i = 0; i < 2 && i < (unsigned)(f->symbol->param_count < 0 ? 0 : f->symbol->param_count);
         ++i) {
        if (cg.register_spills & (1u << i)) {
            Symbol *v = leaf_parameter(f, i);

            if (v && v->offset) {
                unsigned w = (v->offset - 1) / 2;

                if (w < words)
                    ++weight[w];
            }
        }
    }

    for (i = 0; i < words; ++i) {
        if (weight[i]) {
            for (j = count; j && weight[order[j - 1]] < weight[i]; --j) {
                order[j] = order[j - 1];
            }

            order[j] = i;
            ++count;
        }
    }

    if (!count)
        return 0;

    {
        unsigned busy = taken;

        for (int retry = 0; retry < 2; ++retry) {
            free_count = 0;
            mapped = 0;
            assigned = 0;

            for (i = 0; i < 16; ++i) {
                if (!(busy & (1u << i)))
                    free_words[free_count++] = i;
            }

            if (!free_count)
                return 0;

            memset(dp_state.map, 0, sizeof dp_state.map);

            if (count <= free_count) {
                for (i = 0; i < count; ++i) {
                    unsigned w = order[i], fb = precise ? forbidden[w] : 0u;

                    for (j = 0; j < free_count; ++j) {
                        unsigned d = free_words[j];

                        if (!((mapped | fb) & (1u << d))) {
                            dp_state.map[w] = (unsigned char)(d + 1);
                            mapped |= 1u << d;
                            ++assigned;
                            break;
                        }
                    }
                }
            } else {
                static unsigned pword[384], pweight[384], porder[384], pfb[384];
                unsigned pcount = 0;
                memset(pweight, 0, words * sizeof *pweight);
                memset(pfb, 0, words * sizeof *pfb);

                for (i = 0; i < words; ++i) {
                    unsigned pw = (frame_offset(i * 2 + 1) - 1) / 2;
                    pword[i] = pw;

                    if (weight[i] && pw < words) {
                        pweight[pw] += weight[i];

                        if (precise)
                            pfb[pw] |= forbidden[i];
                    }
                }

                for (i = 0; i < words; ++i) {
                    if (pweight[i]) {
                        for (j = pcount; j && pweight[porder[j - 1]] < pweight[i]; --j) {
                            porder[j] = porder[j - 1];
                        }

                        porder[j] = i;
                        ++pcount;
                    }
                }

                for (i = 0; i < pcount; ++i) {
                    unsigned pw = porder[i], fb = precise ? pfb[pw] : 0u;

                    for (j = 0; j < free_count; ++j) {
                        unsigned d = free_words[j];

                        if (!((mapped | fb) & (1u << d))) {
                            unsigned w;
                            mapped |= 1u << d;

                            for (w = 0; w < words; ++w) {
                                if (weight[w] && pword[w] == pw) {
                                    dp_state.map[w] = (unsigned char)(d + 1);
                                    ++assigned;
                                }
                            }

                            break;
                        }
                    }
                }
            }

            if (!assigned)
                return 0;

            dp_state.words = words;
            dp_state.frameless = assigned == count;
            dp_state.homes = 1;
            dp_state.failed = 0;
            dp_state.zero_stack = 0;

            for (i = 0; i < (unsigned)(f->symbol->param_count < 0 ? 0 : f->symbol->param_count);
                 ++i) {
                if (!register_parameter(i, leaf_parameter(f, i)->type))
                    dp_state.zero_stack = 1;
            }

            dp_state.zero_stack &= dp_state.frameless;

            if (dp_state.zero_stack) {
                dp_state.incoming_base = f->frame + cg.frame_saved + 5 + cg.parser->long_return;
                f->frame = 0;
            }

            emit_function_frame(f, dp_state.zero_stack || !dp_state.frameless, possible_registers,
                                start);
            {
                int ok_scan = dp_scan_range_mode(start, cg.length, &taken, precise);

                i = !dp_state.failed && ok_scan && !(taken & mapped);

                if (i && precise) {
                    unsigned w;

                    for (w = 0; w < words; ++w) {
                        if (dp_state.map[w] && (forbidden[w] & (1u << (dp_state.map[w] - 1)))) {
                            i = 0;
                            break;
                        }
                    }
                }

                dp_state.homes = 0;
                dp_state.zero_stack = 0;
#ifdef DP_HOMES_DRYRUN
                i = 0;
#endif

                if (!i) {
                    dp_restore(&saved, start);
                    f->frame = frame;

                    if (!retry && !dp_state.failed && ok_scan && (taken & ~busy)) {
                        busy |= taken;
                        continue;
                    }

                    return 0;
                }
            }
            break;
        }
    }

    if (dp_state.frameless)
        f->frame = 0;

    dp_resolve(start);
    return 1;
}
