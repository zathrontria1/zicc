/* Loop-invariant signed-byte dot-product strength reduction:
 *   sum_k (+|-) v_k * c_k   (v_k in [-128, 127], loop-invariant c_k in [-255, 255])
 * Before the loop, each c_k is packed as (|c_k| | (mask_k << 8)) where
 *   mask_k = $80 (128) if c_k >= 0,  $7F (127) if c_k < 0,
 * and neg_bias = -sum_k (|c_k| * mask_k).
 * Inside the loop, each term computes unsigned (v_k ^ mask_k) * |c_k| in .a8
 * using the $4202/$4203/$4216 hardware multiplier and sums onto neg_bias. */

static Expr *dot_unwrap_signed_byte(Expr *e)
{
    while (e && e->kind == EX_CAST && !e->type.pointers && !e->type.is_bool &&
           e->type.base == TY_INT && !e->type.is_unsigned && e->left && !e->left->type.pointers &&
           !e->left->type.is_bool &&
           (e->left->type.base == TY_CHAR || e->left->type.base == TY_INT) &&
           !e->left->type.is_unsigned)
        e = e->left;
    return e;
}

static Expr *dot_unwrap_signed_word(Expr *e)
{
    while (e && e->kind == EX_CAST && !e->type.pointers && !e->type.is_bool &&
           e->type.base == TY_INT && !e->type.is_unsigned && e->left && !e->left->type.pointers &&
           !e->left->type.is_bool && e->left->type.base == TY_INT && !e->left->type.is_unsigned)
        e = e->left;
    return e;
}

static int dot_indexed_byte(Expr *e, Symbol **base_out, Expr **idx_out, unsigned *off_out,
                            unsigned *scale_out, int *far_out)
{
    Expr *cur = dot_unwrap_signed_byte(e);
    Expr *addr = NULL, *idx = NULL, *ptr_left = NULL;
    Symbol *base = NULL;
    unsigned off = 0, scale = 0, base_stride;
    int idx_ok;

    if (!cur || cur->type.base != TY_CHAR || cur->type.is_unsigned || cur->type.pointers ||
        cur->type.array || volatile_expression(cur))
        return 0;
    if (cur->kind == EX_MEMBER) {
        while (cur && cur->kind == EX_MEMBER && cur->op == '.') {
            off += cur->value;
            cur = cur->left;
        }
        if (!cur)
            return 0;
        if (cur->kind == EX_MEMBER && cur->op == TOK_ARROW) {
            off += cur->value;
            addr = cur->left;
        } else if (cur->kind == EX_DEREF) {
            addr = cur->left;
        } else
            return 0;
    } else if (cur->kind == EX_DEREF) {
        addr = cur->left;
    } else
        return 0;

    while (addr && addr->kind == EX_CAST && addr->type.pointers)
        addr = addr->left;
    if (!addr || addr->kind != EX_BINARY || addr->op != '+')
        return 0;
    if (addr->left && value_type(addr->left->type).pointers) {
        scale = width(pointed_type(value_type(addr->left->type)));
        ptr_left = addr->left;
        idx = addr->right;
    } else if (addr->right && value_type(addr->right->type).pointers) {
        scale = width(pointed_type(value_type(addr->right->type)));
        ptr_left = addr->right;
        idx = addr->left;
    }

    while (ptr_left && ptr_left->kind == EX_CAST && ptr_left->type.pointers)
        ptr_left = ptr_left->left;
    if (ptr_left && ptr_left->kind == EX_OBJECT)
        base = ptr_left->symbol;
    if (!base || base->owner || base->dpage || !base->type.array ||
        (base->type.element && base->type.element->array) || object_volatile(base->type) || !idx)
        return 0;
    idx_ok =
        !body_effect(idx) || (!idx->op && idx->kind == EX_ASSIGN && idx->left->kind == EX_OBJECT &&
                              body_private(idx->left->symbol) && !body_effect(idx->right));
    if (!idx_ok || reg_width(idx->type) != 2 || idx->type.pointers || idx->type.is_bool ||
        idx->type.base == TY_FLOAT)
        return 0;
    base_stride = width(pointed_type(value_type(base->type)));
    if (!scale || scale > 65535u || !base_stride || off >= base_stride ||
        width(base->type) > 65536u)
        return 0;
    if (base_out)
        *base_out = base;
    if (idx_out)
        *idx_out = idx;
    if (off_out)
        *off_out = off;
    if (scale_out)
        *scale_out = scale;
    if (far_out)
        *far_out = base->type.banked != 0;
    return 1;
}

static int dot_direct_byte(Expr *e, Symbol **sym_out, unsigned *off_out)
{
    Expr *cur = dot_unwrap_signed_byte(e);
    Symbol *s;
    unsigned off = 0;

    if (!cur || cur->type.base != TY_CHAR || cur->type.is_unsigned || cur->type.pointers ||
        cur->type.array || volatile_expression(cur))
        return 0;
    if (cur->kind == EX_OBJECT && body_private(cur->symbol) && !cur->symbol->dpage) {
        if (sym_out)
            *sym_out = cur->symbol;
        if (off_out)
            *off_out = 0;
        return 1;
    }
    s = fixed_memory_object(cur, &off);
    if (s && !s->owner && !s->dpage && !object_volatile(s->type)) {
        if (sym_out)
            *sym_out = s;
        if (off_out)
            *off_out = off;
        return 1;
    }
    return 0;
}

static int dot_match_term(Function *f, Statement *loop, Expr *e, int negate, DotTerm *out)
{
    Expr *lhs, *rhs, *val = NULL, *cnode = NULL;
    Symbol *csym;

    e = dot_unwrap_signed_word(e);
    if (!e)
        return 0;
    if (e->kind == EX_UNARY && e->op == '-' && reg_width(e->type) == 2 && !e->type.pointers)
        return dot_match_term(f, loop, e->left, !negate, out);
    if (e->kind != EX_BINARY || e->op != '*' || e->type.pointers || e->type.base != TY_INT ||
        reg_width(e->type) != 2 || volatile_expression(e))
        return 0;
    lhs = e->left;
    rhs = e->right;
    Expr *lc = dot_unwrap_signed_word(lhs), *rc = dot_unwrap_signed_word(rhs);
    if ((dot_indexed_byte(lhs, NULL, NULL, NULL, NULL, NULL) || dot_direct_byte(lhs, NULL, NULL)) &&
        rc && rc->kind == EX_OBJECT) {
        val = lhs;
        cnode = rc;
    } else if ((dot_indexed_byte(rhs, NULL, NULL, NULL, NULL, NULL) ||
                dot_direct_byte(rhs, NULL, NULL)) &&
               lc && lc->kind == EX_OBJECT) {
        val = rhs;
        cnode = lc;
    } else
        return 0;
    csym = cnode->symbol;
    if (!csym || csym->owner != f->id || !csym->scope || csym->offset > f->slots ||
        !body_private(csym) || known_integer(csym->type) == 0 || width(csym->type) != 2 ||
        csym->type.is_unsigned || csym->type.is_bool || scalar_writes(loop, csym) ||
        !cnode->known.valid || cnode->known.min < -255 || cnode->known.max > 255)
        return 0;
    out->value_expr = val;
    out->coeff_sym = csym;
    out->pack_sym = NULL;
    out->negate = negate;
    return 1;
}

static int dot_collect_sum(Function *f, Statement *loop, Expr *e, int negate, DotTerm *terms,
                           unsigned *count)
{
    if (!e || volatile_expression(e) || e->type.pointers || e->type.base != TY_INT ||
        reg_width(e->type) != 2)
        return 0;
    if (e->kind == EX_BINARY && (e->op == '+' || e->op == '-')) {
        if (!dot_collect_sum(f, loop, e->left, negate, terms, count))
            return 0;
        if (!dot_collect_sum(f, loop, e->right, e->op == '-' ? !negate : negate, terms, count))
            return 0;
        return 1;
    }
    if (*count >= MAX_DOT_TERMS)
        return 0;
    if (!dot_match_term(f, loop, e, negate, &terms[*count]))
        return 0;
    ++(*count);
    return 1;
}

static int dot_term_already_claimed(Expr *e)
{
    for (unsigned i = 0; i < dot_state.count; ++i)
        if (dot_state.dots[i].expr == e)
            return 1;
    return 0;
}

static unsigned dot_count_symbol_in_expr(Expr *e, Symbol *s)
{
    unsigned n = 0;

    if (!e)
        return 0;
    if (e->kind == EX_OBJECT && e->symbol == s)
        ++n;
    n += dot_count_symbol_in_expr(e->left, s);
    n += dot_count_symbol_in_expr(e->right, s);
    n += dot_count_symbol_in_expr(e->third, s);

    for (unsigned i = 0; i < e->arg_count; ++i)
        n += dot_count_symbol_in_expr(e->args[i], s);
    return n;
}

static unsigned dot_count_symbol_outside_start(Statement *s, Statement *loop, int *after_or_in,
                                               Symbol *sym)
{
    unsigned n = 0;

    for (; s; s = s->next) {
        if (s == loop)
            *after_or_in = 1;
        if (*after_or_in) {
            n += dot_count_symbol_in_expr(s->expression, sym);
            n += dot_count_symbol_in_expr(s->step, sym);
        }
        n += dot_count_symbol_outside_start(s->initial, loop, after_or_in, sym);
        n += dot_count_symbol_outside_start(s->body, loop, after_or_in, sym);
        n += dot_count_symbol_outside_start(s->alternate, loop, after_or_in, sym);
        if (s == loop)
            *after_or_in = 1;
    }
    return n;
}

static Symbol *dot_new_temp(Function *f, const char *prefix, int is_unsigned, Location at)
{
    char name[64];

    Type t = type(TY_INT, 0);
    Symbol *v;
    if (cg.parser->symbol_count >= 1024 || f->slots + 2 > 768)
        return NULL;
    t.is_unsigned = is_unsigned;
    snprintf(name, sizeof name, "__%s_%u_%u", prefix, f->id, cg.parser->symbol_count);
    v = new_symbol(cg.parser, name, t, at);
    v->owner = f->id;
    v->scope = 1;
    v->active = 1;
    v->internal = 1;
    v->offset = f->slots + 1;
    f->slots += 2;
    return v;
}

static int dot_same_byte_offset(Expr *prev_idx, unsigned prev_scale, Expr *idx, unsigned scale);

static void dot_scan_expr(Function *f, Statement *loop, int in_outer_loop, Expr *e)
{
    DotTerm terms[MAX_DOT_TERMS];
    unsigned count = 0;
    if (!e || dot_state.count >= MAX_DOT_PRODUCTS)
        return;
    if (e->kind == EX_BINARY && (e->op == '+' || e->op == '-') && !dot_term_already_claimed(e) &&
        dot_collect_sum(f, loop, e, 0, terms, &count) && count >= 2) {
        /* Verify k > 0 indexed index expressions don't clobber __arith_lhs */
        int ok = 1, uses_x = 0;
        Expr *prev_idx = NULL;
        unsigned prev_scale = 0;
        int prev_indexed = 0;
        for (unsigned k = 0; k < count && ok; ++k) {
            Expr *idx = NULL;
            unsigned scale = 0;
            if (dot_indexed_byte(terms[k].value_expr, NULL, &idx, NULL, &scale, NULL)) {
                uses_x = 1;
                if (k > 0 &&
                    (!prev_indexed || !dot_same_byte_offset(prev_idx, prev_scale, idx, scale))) {
                    WordScale plan;
                    if (idx->kind != EX_OBJECT || !body_private(idx->symbol) ||
                        (scale != 1 && (scale & (scale - 1)) &&
                         !(word_scale_plan(scale, 0, &plan) &&
                           direct_operand(idx, type(TY_INT, 0), 0, 0))))
                        ok = 0;
                    prev_idx = idx;
                    prev_scale = scale;
                } else if (!prev_indexed) {
                    prev_idx = idx;
                    prev_scale = scale;
                }
                prev_indexed = 1;
            } else
                prev_indexed = 0;
        }
        if (ok) {
            Symbol *bias = dot_new_temp(f, "dp_bias", 0, e->location);
            if (!bias)
                return;
            DotProduct *dp = &dot_state.dots[dot_state.count++];
            dp->loop = loop;
            dp->expr = e;
            dp->bias_sym = bias;
            dp->term_count = count;
            dp->uses_x = uses_x;
            memcpy(dp->terms, terms, count * sizeof terms[0]);
            (void)in_outer_loop;
            return;
        }
    }
    dot_scan_expr(f, loop, in_outer_loop, e->left);
    dot_scan_expr(f, loop, in_outer_loop, e->right);
    dot_scan_expr(f, loop, in_outer_loop, e->third);

    for (unsigned i = 0; i < e->arg_count; ++i)
        dot_scan_expr(f, loop, in_outer_loop, e->args[i]);
}

static void dot_scan_statements(Function *f, Statement *loop, int in_outer_loop, Statement *s)
{
    for (; s; s = s->next) {
        if (s->kind == ST_FOR || s->kind == ST_WHILE || s->kind == ST_DO)
            continue;
        if (loop) {
            dot_scan_expr(f, loop, in_outer_loop, s->expression);
            dot_scan_expr(f, loop, in_outer_loop, s->step);
        }
        dot_scan_statements(f, loop, in_outer_loop, s->initial);
        dot_scan_statements(f, loop, in_outer_loop, s->body);
        dot_scan_statements(f, loop, in_outer_loop, s->alternate);
    }
}

static void dot_finalize_loop_packs(Function *f, Statement *loop, int in_outer_loop)
{
    unsigned first_dot = dot_state.count;

    for (unsigned d = 0; d < dot_state.count; ++d)
        if (dot_state.dots[d].loop == loop) {
            first_dot = d;
            break;
        }
    if (first_dot == dot_state.count)
        return;

    for (unsigned d = first_dot; d < dot_state.count; ++d) {
        DotProduct *dp = &dot_state.dots[d];
        if (dp->loop != loop)
            continue;
        for (unsigned k = 0; k < dp->term_count; ++k) {
            DotTerm *term = &dp->terms[k];
            Symbol *csym = term->coeff_sym;
            unsigned p;
            if (term->pack_sym)
                continue;
            for (p = 0; p < dot_state.pack_count; ++p) {
                if (dot_state.packs[p].loop == loop && dot_state.packs[p].coeff_sym == csym &&
                    dot_state.packs[p].negate == term->negate) {
                    term->pack_sym = dot_state.packs[p].pack_sym;
                    break;
                }
            }
            if (term->pack_sym)
                continue;
            if (dot_state.pack_count >= MAX_DOT_PACKS) {
                dot_state.count = first_dot;
                return;
            }

            /* Pack in-place only if csym is not in an outer loop, has the same
             * negate on every dot term using csym in this loop, and is not
             * read outside dot terms from the start of loop onward. */
            unsigned matched_refs = 0;
            int mixed_sign = 0;
            for (unsigned d2 = first_dot; d2 < dot_state.count; ++d2) {
                if (dot_state.dots[d2].loop != loop)
                    continue;
                for (unsigned k2 = 0; k2 < dot_state.dots[d2].term_count; ++k2) {
                    if (dot_state.dots[d2].terms[k2].coeff_sym == csym) {
                        ++matched_refs;
                        if (dot_state.dots[d2].terms[k2].negate != term->negate)
                            mixed_sign = 1;
                    }
                }
            }
            int flag = 0;
            unsigned total_from_loop = dot_count_symbol_outside_start(f->body, loop, &flag, csym);
            Symbol *pack = NULL;
            if (!in_outer_loop && !mixed_sign && total_from_loop == matched_refs) {
                pack = csym;
            } else {
                pack = dot_new_temp(f, "dp_pack", 1, dp->expr->location);
                if (!pack) {
                    dot_state.count = first_dot;
                    return;
                }
            }
            dot_state.packs[dot_state.pack_count++] = (DotPack){loop, csym, pack, term->negate, 0};
            term->pack_sym = pack;
        }
    }

    for (unsigned p = 0; p < dot_state.pack_count; ++p) {
        DotPack *pk = &dot_state.packs[p];
        int uses_low = 0, uses_high = 0;
        if (pk->loop != loop)
            continue;
        for (unsigned d = first_dot; d < dot_state.count; ++d) {
            DotProduct *dp = &dot_state.dots[d];
            if (dp->loop != loop)
                continue;
            for (unsigned k = 0; k < dp->term_count; ++k) {
                Symbol *base = NULL;
                unsigned off = 0;
                if (dp->terms[k].pack_sym != pk->pack_sym)
                    continue;
                if (dot_indexed_byte(dp->terms[k].value_expr, &base, NULL, &off, NULL, NULL)) {
                    if (off >= 1)
                        uses_high = 1;
                    else
                        uses_low = 1;
                } else if (dot_direct_byte(dp->terms[k].value_expr, &base, &off)) {
                    if (!body_private(base) && off >= 1)
                        uses_high = 1;
                    else
                        uses_low = 1;
                }
            }
        }
        if (uses_low && !uses_high)
            pk->swapped = 1;
    }
}

static void dot_walk_loops(Function *f, Statement *s, int in_outer_loop)
{
    for (; s; s = s->next) {
        if (s->kind == ST_FOR || s->kind == ST_WHILE || s->kind == ST_DO) {
            unsigned start_dots = dot_state.count;
            unsigned start_packs = dot_state.pack_count;
            if (!volatile_statements(s->body)) {
                dot_scan_expr(f, s, in_outer_loop, s->expression);
                dot_scan_expr(f, s, in_outer_loop, s->step);
                dot_scan_statements(f, s, in_outer_loop, s->body);
                dot_finalize_loop_packs(f, s, in_outer_loop);
                if (dot_state.count == start_dots)
                    dot_state.pack_count = start_packs;
            }
            dot_walk_loops(f, s->body, 1);
            continue;
        }
        dot_walk_loops(f, s->initial, in_outer_loop);
        dot_walk_loops(f, s->body, in_outer_loop);
        dot_walk_loops(f, s->alternate, in_outer_loop);
    }
}

static void dot_products_prepare(Function *f)
{
    dot_state.count = 0;
    dot_state.pack_count = 0;
    if (cg.parser->no_strength_reduction || cg.parser->no_body_optimizations ||
        cg.parser->no_known_values || f->symbol->interrupt || f->uses_wide)
        return;
    dot_walk_loops(f, f->body, 0);
}

static DotProduct *dot_match_expr(Expr *e)
{
    if (!e)
        return NULL;

    for (unsigned i = 0; i < dot_state.count; ++i)
        if (dot_state.dots[i].expr == e)
            return &dot_state.dots[i];
    return NULL;
}

static int dot_reserved_symbol(const Symbol *v)
{
    unsigned i;

    if (!v)
        return 0;

    for (i = 0; i < dot_state.count; ++i)
        if (dot_state.dots[i].bias_sym == v)
            return 1;

    for (i = 0; i < dot_state.pack_count; ++i)
        if (dot_state.packs[i].pack_sym == v)
            return 1;
    return 0;
}

static int dot_preserves_x(Expr *e)
{
    DotProduct *dp = dot_match_expr(e);
    return dp ? !dp->uses_x : 0;
}

static void dot_emit_loop_setup(Statement *s)
{
    unsigned d, p, any = 0;
    unsigned char bias_started[MAX_DOT_PRODUCTS] = {0};
    char name[132];

    for (d = 0; d < dot_state.count; ++d)
        if (dot_state.dots[d].loop == s) {
            any = 1;
            break;
        }
    if (!any)
        return;
    cg.need_pack_coeff = 1;
    zicc_pack_coeff_name(name, sizeof name);
    code("; dot-product coefficient setup\n");

    for (p = 0; p < dot_state.pack_count; ++p) {
        DotPack *pk = &dot_state.packs[p];
        if (pk->loop != s)
            continue;
        code("    lda ");
        array_operand(pk->coeff_sym, 0);
        code("\n");
        if (pk->negate)
            code("    eor #$FFFF\n    inc a\n");
        call_entry(name);
        if (pk->swapped)
            code("    xba\n");
        code("    sta ");
        array_operand(pk->pack_sym, 0);
        code("\n");
        for (d = 0; d < dot_state.count; ++d) {
            DotProduct *dp = &dot_state.dots[d];
            if (dp->loop != s)
                continue;
            for (unsigned k = 0; k < dp->term_count; ++k) {
                if (dp->terms[k].pack_sym == pk->pack_sym) {
                    if (!bias_started[d]) {
                        code("    lda #$0000\n    sec\n    sbc f:$004216\n    sta ");
                        array_operand(dp->bias_sym, 0);
                        code("\n");
                        bias_started[d] = 1;
                    } else {
                        code("    lda ");
                        array_operand(dp->bias_sym, 0);
                        code("\n    sec\n    sbc f:$004216\n    sta ");
                        array_operand(dp->bias_sym, 0);
                        code("\n");
                    }
                }
            }
        }
    }
}

static int dot_same_byte_offset(Expr *prev_idx, unsigned prev_scale, Expr *idx, unsigned scale)
{
    if (prev_scale == scale && body_equal(prev_idx, idx))
        return 1;
    if (prev_scale == 1 && prev_idx && prev_idx->kind == EX_ASSIGN && !prev_idx->op &&
        prev_idx->right && prev_idx->right->kind == EX_BINARY && prev_idx->right->op == '*' &&
        prev_idx->right->right && prev_idx->right->right->kind == EX_INT &&
        prev_idx->right->right->value == scale) {
        Expr *inner = prev_idx->right->left;
        while (inner && inner->kind == EX_CAST && reg_width(inner->type) == 2 &&
               !inner->type.pointers)
            inner = inner->left;
        if (inner && body_equal(inner, idx))
            return 1;
    }
    return 0;
}

/* Cached materialized offsets and a retained X have different bases */
static int dot_retained_offsets(DotProduct *dp, unsigned *offsets)
{
    if (!cg.retained_index || cg.retained_y == 5 || cg.retained_scratch)
        return 0;

    for (unsigned k = 0; k < dp->term_count; ++k) {
        Expr *idx;
        unsigned off, scale, a, b;
        if (!dot_indexed_byte(dp->terms[k].value_expr, NULL, &idx, &off, &scale, NULL))
            continue;
        if (!retained_affine(idx, &a, &b) || !a || (int16_t)b < 0 || a * scale != cg.retained_scale)
            return 0;
        off += b * scale;
        if (off > 65535 ||
            (cg.retained_limit > 1 && cg.retained_scale > (65535 - off) / (cg.retained_limit - 1)))
            return 0;
        offsets[k] = off;
    }
    return 1;
}

static int dot_emit_expr(Expr *e)
{
    DotProduct *dp = dot_match_expr(e);
    Expr *prev_idx = NULL;
    unsigned prev_scale = 0, retained_offsets[MAX_DOT_TERMS];
    int prev_indexed = 0, saved_x = 0, use_retained_x;
    if (!dp)
        return 0;
    use_retained_x = dot_retained_offsets(dp, retained_offsets);
    cg.arithmetic = 1;

    for (unsigned k = 0; k < dp->term_count; ++k) {
        DotTerm *term = &dp->terms[k];
        Symbol *base = NULL;
        Expr *idx = NULL;
        unsigned off = 0, raw_off = 0, scale = 0;
        int is_far = 0, swapped = 0, word_setup = 0;
        int is_indexed = dot_indexed_byte(term->value_expr, &base, &idx, &off, &scale, &is_far);
        for (unsigned p = 0; p < dot_state.pack_count; ++p) {
            if (dot_state.packs[p].loop == dp->loop &&
                dot_state.packs[p].pack_sym == term->pack_sym) {
                swapped = dot_state.packs[p].swapped;
                break;
            }
        }
        raw_off = off;
        if (is_indexed) {
            unsigned base_stride = width(pointed_type(value_type(base->type)));
            if (use_retained_x)
                off = retained_offsets[k];
            if (!use_retained_x && !(k > 0 && prev_indexed &&
                                     dot_same_byte_offset(prev_idx, prev_scale, idx, scale))) {
                if (cg.retained_index && cg.retained_y != 5 && !saved_x && !cg.retained_scratch) {
                    code("; retained scratch begin\n    phx\n");
                    if (cg.stack_leaf)
                        cg.stack_bias += 2;
                    ++cg.retained_scratch;
                    saved_x = 1;
                }
                if (scale == 1)
                    emit_value_x(idx);
                else {
                    emit_value(idx);
                    strength_scale(scale, idx);
                    code("    tax\n");
                }
                prev_idx = idx;
                prev_scale = scale;
            }
            prev_indexed = 1;
            if (raw_off >= 1 || is_far || object_constant(base->type) || base_stride >= 2)
                word_setup = 1;
        } else {
            dot_direct_byte(term->value_expr, &base, &off);
            raw_off = off;
            prev_indexed = 0;
            if (body_private(base) || off >= 1 || base->type.banked ||
                object_constant(base->type) || width(base->type) >= 2)
                word_setup = 1;
        }
        if (word_setup) {
            int in_high = !swapped && raw_off >= 1;
            unsigned read_off = in_high ? off - 1 : off;
            int need_xba = (!swapped && raw_off == 0) || (swapped && raw_off >= 1);
            code("    lda ");
            if (is_indexed) {
                base->used = 1;
                if (is_far)
                    code("f:_%s+$%04X,x", base->asm_name, read_off);
                else
                    code("a:.loword(_%s+$%04X),x", base->asm_name, read_off);
            } else {
                array_operand(base, read_off);
            }
            code("\n");
            if (need_xba)
                code("    xba\n");
            code("    and #$%04X\n    eor ", swapped ? 0x00FFu : 0xFF00u);
            array_operand(term->pack_sym, 0);
            code("\n    sta f:$004202\n");
        } else {
            code("    sep #$20\n.a8\n    lda ");
            dp_state.byte_operand = 1;
            array_operand(term->pack_sym, swapped ? 1u : 0u);
            dp_state.byte_operand = 0;
            code("\n    sta f:$004202\n    lda ");
            if (is_indexed) {
                base->used = 1;
                if (is_far)
                    code("f:_%s+$%04X,x", base->asm_name, off);
                else
                    code("a:.loword(_%s+$%04X),x", base->asm_name, off);
            } else {
                dp_state.byte_operand = 1;
                array_operand(base, off);
                dp_state.byte_operand = 0;
            }
            code("\n    eor ");
            dp_state.byte_operand = 1;
            array_operand(term->pack_sym, swapped ? 0u : 1u);
            dp_state.byte_operand = 0;
            code("\n    sta f:$004203\n    rep #$20\n.a16\n");
        }
        if (k == 0) {
            code("    lda ");
            array_operand(dp->bias_sym, 0);
            code("\n");
        } else {
            code("    lda z:__arith_lhs\n");
        }
        code("    clc\n    adc f:$004216\n");
        if (k + 1 < dp->term_count)
            code("    sta z:__arith_lhs\n");
    }
    if (saved_x) {
        --cg.retained_scratch;
        if (cg.stack_leaf)
            cg.stack_bias -= 2;
        code("    plx\n; retained scratch end\n");
    }
    return 1;
}
