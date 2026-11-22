/* Interprocedural optimization for internal (static), non-escaping functions
 * in the current translation unit. Runs after inlining and dead-function
 * elimination so only live direct callers contribute. */

static void ipa_mark_escapes_expr(Parser *p, Expr *e, unsigned char *escaped)
{
    unsigned i;
    if (!e) return;
    if (e->kind == EX_CALL && !e->left && e->symbol) {
        for (i = 0; i < e->arg_count; ++i)
            ipa_mark_escapes_expr(p, e->args[i], escaped);
        return;
    }
    if ((e->kind == EX_OBJECT || e->kind == EX_ADDRESS) && e->symbol && e->symbol->function)
        escaped[e->symbol - p->symbols] = 1;
    ipa_mark_escapes_expr(p, e->left, escaped);
    ipa_mark_escapes_expr(p, e->right, escaped);
    ipa_mark_escapes_expr(p, e->third, escaped);
    for (i = 0; i < e->arg_count; ++i)
        ipa_mark_escapes_expr(p, e->args[i], escaped);
}

static void ipa_mark_escapes_stmt(Parser *p, Statement *s, unsigned char *escaped)
{
    for (; s; s = s->next) {
        ipa_mark_escapes_expr(p, s->expression, escaped);
        ipa_mark_escapes_expr(p, s->step, escaped);
        ipa_mark_escapes_stmt(p, s->initial, escaped);
        ipa_mark_escapes_stmt(p, s->body, escaped);
        ipa_mark_escapes_stmt(p, s->alternate, escaped);
    }
}

static int ipa_var_addr_expr(Expr *e, Symbol *v)
{
    unsigned i;
    if (!e) return 0;
    if (e->kind == EX_ADDRESS && e->left && e->left->kind == EX_OBJECT && e->left->symbol == v)
        return 1;
    if (ipa_var_addr_expr(e->left, v) || ipa_var_addr_expr(e->right, v) || ipa_var_addr_expr(e->third, v))
        return 1;
    for (i = 0; i < e->arg_count; ++i)
        if (ipa_var_addr_expr(e->args[i], v)) return 1;
    return 0;
}

static int ipa_var_addr_stmt(Statement *s, Symbol *v)
{
    for (; s; s = s->next)
        if (ipa_var_addr_expr(s->expression, v) || ipa_var_addr_expr(s->step, v) ||
            ipa_var_addr_stmt(s->initial, v) || ipa_var_addr_stmt(s->body, v) ||
            ipa_var_addr_stmt(s->alternate, v))
            return 1;
    return 0;
}

typedef struct {
    Function *caller;
    Expr *call;
} IpaCallSite;

static void ipa_collect_calls_expr(Function *caller, Expr *e, Symbol *target, IpaCallSite *sites, unsigned *count, unsigned cap)
{
    unsigned i;
    if (!e) return;
    if (e->kind == EX_CALL && !e->left && e->symbol == target) {
        if (*count < cap) {
            sites[*count].caller = caller;
            sites[*count].call = e;
        }
        ++*count;
    }
    ipa_collect_calls_expr(caller, e->left, target, sites, count, cap);
    ipa_collect_calls_expr(caller, e->right, target, sites, count, cap);
    ipa_collect_calls_expr(caller, e->third, target, sites, count, cap);
    for (i = 0; i < e->arg_count; ++i)
        ipa_collect_calls_expr(caller, e->args[i], target, sites, count, cap);
}

static void ipa_collect_calls_stmt(Function *caller, Statement *s, Symbol *target, IpaCallSite *sites, unsigned *count, unsigned cap)
{
    for (; s; s = s->next) {
        ipa_collect_calls_expr(caller, s->expression, target, sites, count, cap);
        ipa_collect_calls_expr(caller, s->step, target, sites, count, cap);
        ipa_collect_calls_stmt(caller, s->initial, target, sites, count, cap);
        ipa_collect_calls_stmt(caller, s->body, target, sites, count, cap);
        ipa_collect_calls_stmt(caller, s->alternate, target, sites, count, cap);
    }
}

static int ipa_function_alive(Function *f)
{
    Symbol *s = f->symbol;
    return !s->inline_omit && !(s->inline_hint && !s->internal && !s->inline_external);
}

static int ipa_linear_local_init(Statement *s, Symbol *target, Symbol *v, int *seen_call, Expr **out_rhs)
{
    for (; s; s = s->next) {
        if (s->kind == ST_BLOCK) {
            if (!ipa_linear_local_init(s->body, target, v, seen_call, out_rhs))
                return 0;
            if (*out_rhs) return 1;
            continue;
        }
        if (s->kind == ST_EMPTY) continue;
        if (s->kind != ST_EXPR) return 0;
        Expr *e = s->expression;
        if (e && e->kind == EX_ASSIGN && !e->op && e->left &&
            e->left->kind == EX_OBJECT && e->left->symbol == v) {
            if (*seen_call) return 0;
            *out_rhs = e->right;
            return 1;
        }
        IpaCallSite dummy[4];
        unsigned cnt = 0;
        ipa_collect_calls_expr(NULL, e, target, dummy, &cnt, 4);
        if (cnt) *seen_call = 1;
    }
    return 1;
}

static Expr *ipa_resolve_arg(Function *caller, Symbol *target, Expr *arg)
{
    if (arg && arg->kind == EX_OBJECT && arg->symbol->owner == caller->id &&
        !arg->symbol->type.array && !object_volatile(arg->symbol->type) &&
        !ipa_var_addr_stmt(caller->body, arg->symbol) &&
        scalar_writes(caller->body, arg->symbol) == 1) {
        int seen_call = 0;
        Expr *rhs = NULL;
        if (ipa_linear_local_init(caller->body, target, arg->symbol, &seen_call, &rhs) && rhs)
            return rhs;
    }
    return arg;
}

static int ipa_fixed_object_arg(Expr *arg, Type formal_type)
{
    Type ft = value_type(formal_type), at = value_type(arg->type);
    if (!ft.pointers || !at.pointers) return 0;
    if (far_pointer(ft) != far_pointer(at)) return 0;
    if (!same_type(unqualified_value(ft), unqualified_value(at))) return 0;
    while (arg->kind == EX_CAST && value_type(arg->type).pointers &&
           value_type(arg->left->type).pointers &&
           far_pointer(value_type(arg->type)) == far_pointer(value_type(arg->left->type)))
        arg = arg->left;
    if (arg->kind == EX_OBJECT && arg->type.array && !arg->symbol->owner) return 1;
    if (arg->kind == EX_ADDRESS && arg->left && arg->left->kind == EX_OBJECT &&
        !arg->left->symbol->owner && !arg->left->symbol->function) return 1;
    return 0;
}

static int ipa_local_near_writes_expr(Expr *e, Symbol *v, int *ok)
{
    unsigned i;
    if (!e || !*ok) return 0;
    if (e->kind == EX_ASSIGN && e->left && e->left->kind == EX_OBJECT && e->left->symbol == v) {
        if (!e->op) {
            if (!body_near_far_source(e->right, NULL, 1)) { *ok = 0; return 0; }
        } else if (e->op != '+' && e->op != '-') {
            *ok = 0; return 0;
        }
    }
    ipa_local_near_writes_expr(e->left, v, ok);
    ipa_local_near_writes_expr(e->right, v, ok);
    ipa_local_near_writes_expr(e->third, v, ok);
    for (i = 0; i < e->arg_count; ++i)
        ipa_local_near_writes_expr(e->args[i], v, ok);
    return *ok;
}

static int ipa_local_near_writes_stmt(Statement *s, Symbol *v, int *ok)
{
    for (; s && *ok; s = s->next) {
        ipa_local_near_writes_expr(s->expression, v, ok);
        ipa_local_near_writes_expr(s->step, v, ok);
        ipa_local_near_writes_stmt(s->initial, v, ok);
        ipa_local_near_writes_stmt(s->body, v, ok);
        ipa_local_near_writes_stmt(s->alternate, v, ok);
    }
    return *ok;
}

static int ipa_arg_is_near7e(Function *caller, Expr *arg)
{
    while (arg && arg->kind == EX_CAST && value_type(arg->type).pointers &&
           value_type(arg->left->type).pointers)
        arg = arg->left;
    if (!arg) return 0;
    if (body_near_far_source(arg, NULL, 1)) return 1;
    if (arg->kind == EX_OBJECT && arg->symbol->owner == caller->id &&
        !arg->symbol->type.array && far_pointer(arg->symbol->type) &&
        !object_volatile(arg->symbol->type) && !ipa_var_addr_stmt(caller->body, arg->symbol)) {
        int ok = 1;
        return scalar_writes(caller->body, arg->symbol) > 0 &&
               ipa_local_near_writes_stmt(caller->body, arg->symbol, &ok);
    }
    return 0;
}

static void ipa_set_param_type(Symbol *fn, unsigned k, Type t)
{
    fn->params[k] = t;
    if (fn->type.signature && (int)k < fn->type.signature->count) {
        FunctionType *old_sig = fn->type.signature;
        unsigned n = (unsigned)old_sig->count;
        FunctionType *sig = allocate(sizeof *sig + n * sizeof(Type));
        *sig = *old_sig;
        memcpy(sig->parameters, old_sig->parameters, n * sizeof(Type));
        sig->parameters[k] = t;
        fn->type.signature = sig;
    }
}

static void ipa_seed_ranges(Parser *p, Function **eligible, unsigned count)
{
    unsigned round, i, j, k;
    for (round = 0; round < 2; ++round) {
        KnownValue joined[64][16];
        unsigned char seen[64][16], bad[64][16];
        memset(seen, 0, sizeof seen);
        memset(bad, 0, sizeof bad);
        for (Function *caller = p->functions; caller; caller = caller->next) {
            if (!ipa_function_alive(caller) || caller->uses_wide || caller->jump_label_count)
                continue;
            cg.function = caller;
            known_prepare(caller);
            for (i = 0; i < count; ++i) {
                Function *f = eligible[i];
                IpaCallSite sites[128];
                unsigned site_count = 0;
                ipa_collect_calls_stmt(caller, caller->body, f->symbol, sites, &site_count, 128);
                for (j = 0; j < site_count && j < 128; ++j) {
                    Expr *c = sites[j].call;
                    for (k = 0; k < c->arg_count && k < 16; ++k) {
                        Expr *a = c->args[k];
                        if (a->type.pointers || a->type.array || !a->known.valid) {
                            bad[i][k] = 1;
                        } else if (!seen[i][k]) {
                            joined[i][k] = a->known;
                            seen[i][k] = 1;
                        } else {
                            joined[i][k] = known_join(joined[i][k], a->known, a->type);
                        }
                    }
                }
                if (site_count > 128)
                    for (k = 0; k < 16; ++k) bad[i][k] = 1;
            }
        }
        for (i = 0; i < count; ++i) {
            Function *f = eligible[i];
            for (k = 0; k < (unsigned)f->symbol->param_count && k < 16; ++k) {
                if (seen[i][k] && !bad[i][k]) {
                    f->ipa_known[k] = joined[i][k];
                    f->ipa_known_valid[k] = 1;
                } else {
                    f->ipa_known_valid[k] = 0;
                }
            }
        }
    }
    cg.function = NULL;
}

static void static_ipa_prepare(Parser *p)
{
    unsigned char escaped[1024] = {0};
    Function *eligible[64];
    unsigned eligible_count = 0;
    unsigned i, j, k;
    if (p->no_body_optimizations || p->no_strength_reduction) return;
    cg.parser = p;
    for (i = 0; i < p->symbol_count; ++i) {
        Relocation *r;
        for (r = p->symbols[i].relocations; r; r = r->next)
            if (r->symbol) escaped[r->symbol - p->symbols] = 1;
    }
    for (Function *f = p->functions; f; f = f->next)
        if (ipa_function_alive(f))
            ipa_mark_escapes_stmt(p, f->body, escaped);

    for (Function *f = p->functions; f && eligible_count < 64; f = f->next) {
        Symbol *s = f->symbol;
        if (!s->internal || s->external || s->address_taken || !ipa_function_alive(f) ||
            escaped[s - p->symbols] || s->variadic || s->old_style || s->interrupt ||
            f->uses_varargs || f->aggregate_abi || f->uses_wide || f->jump_label_count ||
            s->param_count <= 0 || s->param_count > MAX_PARAMETERS || body_asm_statements(f->body))
            continue;
        IpaCallSite sites[128];
        unsigned total = 0;
        for (Function *caller = p->functions; caller; caller = caller->next)
            if (ipa_function_alive(caller))
                ipa_collect_calls_stmt(caller, caller->body, s, sites, &total, 128);
        if (!total || total > 128) continue;
        int valid = 1;
        for (j = 0; j < total; ++j)
            if (sites[j].call->arg_count != (unsigned)s->param_count) { valid = 0; break; }
        if (!valid) continue;
        f->ipa_internal = 1;
        eligible[eligible_count++] = f;
    }
    if (!eligible_count) return;
    if (p->runtime_objects) {
        if (!p->no_known_values) ipa_seed_ranges(p, eligible, eligible_count);
        cg.function = NULL;
        return;
    }

    /* 1. Constant and fixed global-object parameter propagation */
    for (unsigned round = 0; round < 8; ++round) {
        int changed = 0;
        for (i = 0; i < eligible_count; ++i) {
            Function *f = eligible[i];
            IpaCallSite sites[128];
            unsigned total = 0;
            for (Function *caller = p->functions; caller; caller = caller->next)
                if (ipa_function_alive(caller))
                    ipa_collect_calls_stmt(caller, caller->body, f->symbol, sites, &total, 128);
            cg.function = f;
            for (k = 0; k < (unsigned)f->symbol->param_count; ++k) {
                Symbol *formal = leaf_parameter(f, k);
                Expr *resolved[128];
                Expr *arg0;
                int same = 1, is_const, is_fixed;
                if (!formal || object_volatile(formal->type) ||
                    !statement_references(f->body, formal) ||
                    scalar_writes(f->body, formal) || ipa_var_addr_stmt(f->body, formal))
                    continue;
                for (j = 0; j < total; ++j)
                    resolved[j] = ipa_resolve_arg(sites[j].caller, f->symbol, sites[j].call->args[k]);
                arg0 = resolved[0];
                is_const = arg0->kind == EX_INT && numeric(arg0->type) &&
                           reg_width(formal->type) <= 2 && !formal->type.pointers;
                is_fixed = !is_const && ipa_fixed_object_arg(arg0, formal->type);
                if (!is_const && !is_fixed) continue;
                for (j = 1; j < total; ++j) {
                    Expr *aj = resolved[j];
                    if (is_const) {
                        if (aj->kind != EX_INT || aj->value != arg0->value || aj->value_high != arg0->value_high) {
                            same = 0; break;
                        }
                    } else if (!body_equal(aj, arg0)) {
                        same = 0; break;
                    }
                }
                if (!same) continue;
                Expr *rep = is_const ? convert(body_clone(arg0), unqualified_value(formal->type))
                                     : body_clone(arg0);
                body_cursor_substitute(f->body, NULL, formal, rep);
                free_expression(rep);
                changed = 1;
            }
        }
        if (!changed) break;
    }

    /* 2. Narrow __far pointer parameters proven bank-$7E at every live call */
    if (!p->no_bank_specialization && !p->no_known_values) {
        for (i = 0; i < eligible_count; ++i) {
            Function *f = eligible[i];
            IpaCallSite sites[128];
            unsigned total = 0, uses[1024] = {0};
            unsigned char live[1024] = {0}, narrow[1024] = {0};
            int chg, any = 0;
            for (Function *caller = p->functions; caller; caller = caller->next)
                if (ipa_function_alive(caller))
                    ipa_collect_calls_stmt(caller, caller->body, f->symbol, sites, &total, 128);
            cg.function = f;
            for (k = 0; k < (unsigned)f->symbol->param_count; ++k) {
                Symbol *formal = leaf_parameter(f, k);
                if (!formal || formal->type.array || object_volatile(formal->type) ||
                    !far_pointer(value_type(formal->type)) ||
                    scalar_writes(f->body, formal) || ipa_var_addr_stmt(f->body, formal))
                    continue;
                live[formal - p->symbols] = 1;
                any = 1;
            }
            if (!any) continue;
            do {
                chg = 0;
                memset(uses, 0, sizeof uses);
                body_far_stmt_check(f->body, live, uses, &chg);
            } while (chg);
            any = 0;
            for (k = 0; k < (unsigned)f->symbol->param_count; ++k) {
                Symbol *formal = leaf_parameter(f, k);
                int all_near = 1;
                if (!formal || !live[formal - p->symbols]) continue;
                for (j = 0; j < total; ++j) {
                    if (!ipa_arg_is_near7e(sites[j].caller, sites[j].call->args[k])) {
                        all_near = 0; break;
                    }
                }
                if (!all_near) continue;
                formal->type.far_pointers &= ~pointer_bit(formal->type.pointers);
                ipa_set_param_type(f->symbol, k, formal->type);
                narrow[formal - p->symbols] = 1;
                any = 1;
                for (j = 0; j < total; ++j) {
                    body_unwrap_near_expr(&sites[j].call->args[k], formal->type);
                    if (far_pointer(value_type(sites[j].call->args[k]->type)))
                        sites[j].call->args[k] = convert(sites[j].call->args[k], unqualified_value(formal->type));
                }
            }
            if (any) body_narrow_far_statements(f->body, narrow);
        }
    }

    /* 3. Drop dead parameters and pack 2-byte parameters into (X, A) slots */
    for (i = 0; i < eligible_count; ++i) {
        Function *f = eligible[i];
        Symbol *s = f->symbol;
        IpaCallSite sites[128];
        unsigned total = 0, old_count = (unsigned)s->param_count;
        unsigned order[MAX_PARAMETERS], new_count = 0;
        int pure_calls = 1;
        for (Function *caller = p->functions; caller; caller = caller->next)
            if (ipa_function_alive(caller))
                ipa_collect_calls_stmt(caller, caller->body, s, sites, &total, 128);
        for (j = 0; j < total && pure_calls; ++j)
            for (k = 0; k < sites[j].call->arg_count; ++k)
                if (body_effect(sites[j].call->args[k]) || volatile_expression(sites[j].call->args[k])) {
                    pure_calls = 0; break;
                }
        if (!pure_calls) continue;
        cg.function = f;
        unsigned live_words[MAX_PARAMETERS], word_count = 0;
        for (k = 0; k < old_count; ++k) {
            Symbol *formal = leaf_parameter(f, k);
            if (!formal || !statement_references(f->body, formal)) continue;
            if (!structure_object(value_type(formal->type)) && reg_width(formal->type) == 2)
                live_words[word_count++] = k;
        }
        /* Keep slot 0 in X if already a 2-byte parameter; pick highest-use word for A */
        if (word_count >= 1) {
            order[new_count++] = live_words[0];
            if (word_count >= 2) {
                unsigned best = live_words[1], best_refs = statement_references(f->body, leaf_parameter(f, best));
                for (j = 2; j < word_count; ++j) {
                    unsigned cand = live_words[j];
                    unsigned refs = statement_references(f->body, leaf_parameter(f, cand));
                    if (refs > best_refs) { best = cand; best_refs = refs; }
                }
                order[new_count++] = best;
            }
        }
        for (k = 0; k < old_count; ++k) {
            Symbol *formal = leaf_parameter(f, k);
            int already = 0;
            if (!formal || !statement_references(f->body, formal)) continue;
            for (j = 0; j < new_count; ++j) if (order[j] == k) { already = 1; break; }
            if (!already) order[new_count++] = k;
        }
        if (new_count == old_count) {
            int same_order = 1;
            for (k = 0; k < new_count; ++k) if (order[k] != k) { same_order = 0; break; }
            if (same_order) continue;
        }
        Symbol *dropped[MAX_PARAMETERS];
        unsigned drop_count = 0;
        for (k = 0; k < old_count; ++k) {
            int kept_arg = 0;
            for (j = 0; j < new_count; ++j) if (order[j] == k) { kept_arg = 1; break; }
            if (!kept_arg) {
                Symbol *formal = leaf_parameter(f, k);
                if (formal) dropped[drop_count++] = formal;
            }
        }
        Type new_params[MAX_PARAMETERS];
        char new_names[MAX_PARAMETERS][64];
        for (k = 0; k < new_count; ++k) {
            new_params[k] = s->params[order[k]];
            strcpy(new_names[k], s->param_names[order[k]]);
        }
        for (k = 0; k < new_count; ++k) {
            s->params[k] = new_params[k];
            strcpy(s->param_names[k], new_names[k]);
        }
        s->param_count = (int)new_count;
        for (k = 0; k < drop_count; ++k)
            body_remove_local(f, dropped[k]);
        if (s->type.signature) {
            FunctionType *sig = allocate(sizeof *sig + new_count * sizeof(Type));
            *sig = *s->type.signature;
            sig->count = (int)new_count;
            for (k = 0; k < new_count; ++k) sig->parameters[k] = new_params[k];
            s->type.signature = sig;
        }
        for (j = 0; j < total; ++j) {
            Expr *c = sites[j].call;
            Expr *reordered[MAX_ARGUMENTS];
            unsigned char kept[MAX_ARGUMENTS] = {0};
            for (k = 0; k < new_count; ++k) {
                reordered[k] = c->args[order[k]];
                kept[order[k]] = 1;
            }
            for (k = 0; k < old_count; ++k)
                if (!kept[k]) free_expression(c->args[k]);
            for (k = 0; k < new_count; ++k) c->args[k] = reordered[k];
            c->arg_count = new_count;
        }
    }

    /* 4. Seed parameter known ranges from all live direct calls */
    if (!p->no_known_values)
        ipa_seed_ranges(p, eligible, eligible_count);
    cg.function = NULL;
}
