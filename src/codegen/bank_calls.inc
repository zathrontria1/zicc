/* Private out-of-line entries, never AST inlining. Public signatures and the
 * unknown-pointer path retain the normal ABI. Only actual object extents prove
 * containment; a bank number alone is not a sufficient proof. */
typedef struct BankVariant {
    Function *function;
    FarLeafPlan plan;
    ReductionPlan reduction;
    int is_reduction;
    Expr *anchor;
    unsigned mask;
    int used;
    char entry[196];
} BankVariant;

// Private state owned by bank_calls.inc for fixed-bank call specializations
typedef struct {
    BankVariant *variants[256]; // planned private specialized entries
    unsigned count; // number of entries in variants[]
} BankCallState;

static BankCallState bank_state;

static Expr *bank_root(Expr *e)
{
    while (e->kind == EX_CAST && value_type(e->type).pointers &&
           value_type(e->left->type).pointers) {
        e = e->left;
    }

    return e;
}

static int bank_object(Expr *e, unsigned *bytes)
{
    Symbol *s;

    e = bank_root(e);

    if (e->kind == EX_STRING) {
        *bytes = (unsigned)e->string->size;
        return 2;
    }

    if (e->kind == EX_OBJECT && e->symbol->type.array)
        s = e->symbol;
    else if (e->kind == EX_ADDRESS && e->left->kind == EX_OBJECT && !e->left->symbol->function)
        s = e->left->symbol;
    else
        return 0;

    *bytes = width(s->type);
    if (!*bytes || *bytes > 65535)
        return 0;
    if (s->wram)
        return 0;
    if (s->type.banked)
        return s->defined && s->initializer ? 2 : 0;

    return 1;
}

static void bank_reference(Expr *e)
{
    Symbol *s;

    e = bank_root(e);

    if (e->kind == EX_STRING) {
        e->string->used = 1;
        code("str_%s_%u", cg.parser->unit, e->string->id);
    } else {
        s = e->kind == EX_ADDRESS ? e->left->symbol : e->symbol;
        s->used = 1;
        code("_%s", s->asm_name);
    }
}

static int bank_reduction_signature(Symbol *s)
{
    Type base = value_type(s->params[0]), bound = value_type(s->params[1]);

    return far_pointer(base) && base.pointers == 1 && base.base == TY_STRUCT && !bound.pointers &&
           bound.base == TY_INT && !bound.is_unsigned;
}

static int bank_signature(Expr *call, unsigned *mask, Expr **anchor)
{
    unsigned i, bytes;
    int kind;
    Symbol *s = call->symbol;

    *mask = 0;
    *anchor = NULL;
    if (!s || s->noclone || structure_object(s->type) || volatile_expression(call) ||
        call->arg_count != 2 || s->param_count != 2 || s->variadic || s->interrupt)
        return 0;

    if (bank_reduction_signature(s)) {
        kind = bank_object(call->args[0], &bytes);

        if (!kind)
            return 0;

        if (kind == 2) {
            *mask = 1;
            *anchor = call->args[0];
        }

        return 1;
    }

    for (i = 0; i < 2; ++i) {
        Type t = value_type(s->params[i]);

        if (t.pointers != 1 || t.base != TY_CHAR || width(pointed_type(t)) != 1)
            return 0;

        if (far_pointer(t)) {
            kind = bank_object(call->args[i], &bytes);

            if (!kind)
                return 0;

            if (kind == 2) {
                *mask |= 1u << i;
                *anchor = call->args[i];
            }
        }
    }

    /* Absolute long,Y does not exist. Retain the general path for two ROM
     * cursors rather than changing DBR or adding per-character bank switches. */
    return *mask != 3;
}

static void bank_find_calls(Expr *e)
{
    unsigned i, mask;
    Expr *anchor;
    Function *f;

    BankVariant *v;
    Function *saved;

    if (!e)
        return;

    if (e->kind == EX_CALL && bank_state.count < 256 && bank_signature(e, &mask, &anchor)) {
        for (i = 0; i < bank_state.count; ++i) {
            if (bank_state.variants[i]->function->symbol == e->symbol &&
                bank_state.variants[i]->mask == mask)
                break;
        }

        if (i == bank_state.count) {
            for (f = cg.parser->functions; f && f->symbol != e->symbol; f = f->next) {
            }

            if (f && !volatile_statements(f->body)) {
                FarLeafPlan plan = {0};
                ReductionPlan reduction = {0};
                int near, accepted, is_reduction = bank_reduction_signature(e->symbol);

                saved = cg.function;
                cg.function = f;
                accepted = is_reduction
                               ? reduction_plan(f, &reduction)
                               : far_leaf_plan(f, &plan) && far_indexed_plan(&plan.loop, &near) &&
                                     !plan.loop.remaining && plan.loop.pointer_count == 2 &&
                                     plan.loop.instruction_count <= 48;
                cg.function = saved;

                if (accepted) {
                    for (i = 0; i < plan.loop.instruction_count; ++i) {
                        LoopInstruction *instruction = &plan.loop.instructions[i];

                        unsigned parameter =
                            (unsigned)loop_parameter(f, plan.loop.pointers[instruction->reg]);

                        if (instruction->kind == LOOP_STORE && (mask & (1u << parameter)))
                            accepted = 0;
                    }

                    for (i = 0; i < plan.ns; ++i) {
                        unsigned j;

                        for (j = 0; j < 2; ++j) {
                            if (plan.loop.pointers[j] ==
                                plan.stores[i]->expression->left->left->symbol)
                                break;
                        }

                        if (mask & (1u << (unsigned)loop_parameter(f, plan.loop.pointers[j])))
                            accepted = 0;
                    }

                    if (accepted) {
                        v = allocate(sizeof *v);
                        v->function = f;
                        v->plan = plan;
                        v->reduction = reduction;
                        v->is_reduction = is_reduction;
                        v->mask = mask;
                        v->anchor = anchor;
                        snprintf(v->entry, sizeof v->entry, "__bank_%s_%u_%u", cg.parser->unit,
                                 f->id, mask);
                        bank_state.variants[bank_state.count++] = v;
                    }
                }
            }
        }
    }

    bank_find_calls(e->left);
    bank_find_calls(e->right);
    bank_find_calls(e->third);

    for (i = 0; i < e->arg_count; ++i) {
        bank_find_calls(e->args[i]);
    }
}

static void bank_statements(Statement *s)
{
    for (; s; s = s->next) {
        bank_find_calls(s->expression);
        bank_find_calls(s->step);
        bank_statements(s->initial);
        bank_statements(s->body);
        bank_statements(s->alternate);
    }
}

static void bank_prepare(void)
{
    Function *f;

    memset(&bank_state, 0, sizeof bank_state);

    if (cg.parser->no_bank_specialization || cg.parser->no_register_loops)
        return;

    for (f = cg.parser->functions; f; f = f->next) {
        if (!f->symbol->inline_omit)
            bank_statements(f->body);
    }

    cg.function = NULL;
}

static int bank_low_constant(Expr *e)
{
    e = bank_root(e);
    return constant_address(e) ||
           (e->kind == EX_OBJECT && e->symbol->type.array && !e->symbol->owner);
}

static void bank_low_argument(Expr *e, int x)
{
    unsigned bytes;

    if (bank_object(e, &bytes)) {
        e = bank_root(e);

        if (bank_low_constant(e)) {
            code("    %s #.loword(", x ? "ldx" : "lda");
            bank_reference(e);
            code(")\n");
            return;
        }
    }

    load_argument(e, x);
}

static int bank_call(Expr *e)
{
    unsigned i, j, mask, bytes;
    Expr *anchor;

    BankVariant *v;

    if (!bank_state.count || !bank_signature(e, &mask, &anchor))
        return 0;

    for (i = 0; i < bank_state.count; ++i) {
        if (bank_state.variants[i]->function->symbol == e->symbol &&
            bank_state.variants[i]->mask == mask)
            break;
    }

    if (i == bank_state.count) {
        return 0;
    }

    v = bank_state.variants[i];
    v->used = 1;

    if (!bank_low_constant(e->args[1])) {
        bank_low_argument(e->args[1], 0);
        code("    pha\n");
        bank_low_argument(e->args[0], 1);
        code("    pla\n");
    } else {
        bank_low_argument(e->args[0], 1);
        bank_low_argument(e->args[1], 0);
    }

    for (j = 0; j < 2; ++j) {
        if (mask & (1u << j)) {
            bank_object(e->args[j], &bytes);
            code(".assert .bankbyte(");
            bank_reference(e->args[j]);
            code(") = .bankbyte(");
            bank_reference(v->anchor);
            code("), lderror, \"specialized ROM bank changed\"\n.assert .bankbyte(");
            bank_reference(e->args[j]);
            code(") = .bankbyte(");
            bank_reference(e->args[j]);
            code(" + $%04X), lderror, \"specialized ROM object crosses bank\"\n", bytes - 1);
        }
    }

    e->symbol->used = 1;
    call_entry(v->entry);
    narrow_char(e->type);
    divmod_state.available = 0;
    return 1;
}

static void bank_memory(BankVariant *v, const char *op, int reg, int x)
{
    unsigned parameter = (unsigned)loop_parameter(v->function, v->plan.loop.pointers[reg]);

    if (v->mask & (1u << parameter)) {
        code("    %s f:.bankbyte(", op);
        bank_reference(v->anchor);
        code(")*$10000,x\n");
    } else
        code("    %s a:$0000,%s\n", op, reg == x ? "x" : "y");
}

static void bank_predicate(BankVariant *v, LoopPredicate *p, int x, int *cached, int *zero_flags)
{
    if (*cached != p->reg) {
        bank_memory(v, "lda", p->reg, x);
        *cached = p->reg;
        *zero_flags = 1;
    }

    if (p->kind == LOOP_COMPARE) {
        bank_memory(v, "cmp", p->other, x);
        *zero_flags = 0;
    } else if (!*zero_flags) {
        code("    cmp #$00\n");
        *zero_flags = 1;
    }
}

static void bank_emit_variant(BankVariant *v)
{
    if (v->is_reduction) {
        cg.function = v->function;
        code("; bank specialization: %s %s %s\n", v->entry + 1, v->function->symbol->asm_name,
             v->mask ? "RW" : "NW");

        if (v->mask) {
            code("__bank_value_%s = .bankbyte(", v->entry + 1);
            bank_reference(v->anchor);
            code(")\n.export __bank_value_%s\n", v->entry + 1);
        }

        near_counted_reduction(&v->reduction, v->entry, v->mask ? v->anchor : NULL);
        return;
    }

    FarLeafPlan *plan = &v->plan;
    RegisterLoop *loop = &plan->loop;

    unsigned i, k, start = ++cg.label, end = ++cg.label, flags = ++cg.label, done = ++cg.label;
    int x = 0, x_parameter, cached = -1, zero_flags = 0, reload = 0;

    cg.function = v->function;

    if (!v->mask && loop->strides[0] != 1)
        x = 1;

    for (i = 0; i < 2; ++i) {
        if (v->mask & (1u << (unsigned)loop_parameter(v->function, loop->pointers[i])))
            x = (int)i;
    }

    x_parameter = loop_parameter(v->function, loop->pointers[x]);
    code(".segment \"CODE\"\n.export %s\n%s:\n; bank specialization: %s %s %s\n    phy\n", v->entry,
         v->entry, v->entry + 1, v->function->symbol->asm_name,
         v->mask == 1   ? "RN"
         : v->mask == 2 ? "NR"
                        : "NN");

    if (v->mask) {
        code("__bank_value_%s = .bankbyte(", v->entry + 1);
        bank_reference(v->anchor);
        code(")\n.export __bank_value_%s\n", v->entry + 1);
    }

    if (plan->coefficient)
        code("    %s\n", x_parameter == 0 ? "phx" : "pha");

    code(x_parameter == 0 ? "    tay\n" : "    txy\n    tax\n");
    code("    sep #$20\n.a8\n");
    label(start);

    if (loop->predicate_count) {
        for (i = 0; i < loop->predicate_count; ++i) {
            LoopPredicate *p = &loop->predicates[i];

            bank_predicate(v, p, x, &cached, &zero_flags);
            loop_predicate_branch(p, plan->predicate && loop_same_test(p, &plan->result) ? flags
                                                                                         : end);

            if (plan->predicate && !loop_same_test(p, &plan->result) && p->reg != plan->result.reg)
                reload = 1;
        }
    } else {
        bank_memory(v, "lda", loop->sentinel, x);
        code("    bne :+\n");
        jump(end);
        code(":\n");
        cached = loop->sentinel;

        if (plan->predicate)
            reload = loop->sentinel != plan->result.reg;
    }

    for (i = 0; i < loop->instruction_count; ++i) {
        LoopInstruction *instruction = &loop->instructions[i];

        switch (instruction->kind) {
        case LOOP_LOAD:
            if (cached != instruction->reg)
                bank_memory(v, "lda", instruction->reg, x);

            cached = instruction->reg;
            break;
        case LOOP_STORE:
            bank_memory(v, "sta", instruction->reg, x);
            cached = -1;
            break;
        case LOOP_STEP:
            code("    %s%s\n", instruction->op > 0 ? "in" : "de",
                 instruction->reg == x ? "x" : "y");

            if (cached == instruction->reg)
                cached = -1;

            break;
        case LOOP_LITERAL:
            code("    lda #$%02X\n", instruction->value);
            cached = -1;
            break;
        case LOOP_ALU:
            if (instruction->op == '+' || instruction->op == '-')
                code("    %s\n", instruction->op == '+' ? "clc" : "sec");

            code("    %s #$%02X\n",
                 instruction->op == '+'   ? "adc"
                 : instruction->op == '-' ? "sbc"
                 : instruction->op == '&' ? "and"
                 : instruction->op == '|' ? "ora"
                                          : "eor",
                 instruction->value);
            cached = -1;
            break;
        case LOOP_SAVE:
        case LOOP_RESTORE:
            code("    xba\n");
            cached = -1;
            break;
        }
    }

    jump(start);
    label(end);

    for (i = 0; i < plan->ns; ++i) {
        Expr *e = plan->stores[i]->expression;
        uint32_t value;

        unsigned reg;
        integer_constant(e->right, &value);

        for (reg = 0; reg < 2; ++reg) {
            if (loop->pointers[reg] == e->left->left->symbol)
                break;
        }

        if (i || loop->predicate_count || (value & 255)) {
            code("    lda #$%02X\n", value & 255);
        }

        bank_memory(v, "sta", (int)reg, x);
    }

    if (plan->predicate) {
        cached = reload ? -1 : plan->result.reg;
        zero_flags = 0;
        bank_predicate(v, &plan->result, x, &cached, &zero_flags);
        label(flags);
        code("    rep #$20\n.a16\n    %s :+\n    lda #1\n",
             plan->result.op == TOK_EQ ? "bne" : "beq");
        jump(done);
        code(":\n    lda #0\n");
        label(done);
    } else {
        code("    rep #$20\n.a16\n");

        if (plan->return_pointer >= 0)
            code("    %s\n", plan->return_pointer == x ? "txa" : "tya");
        else if (plan->coefficient) {
            unsigned magnitude =
                (unsigned)((int16_t)plan->coefficient < 0 ? -(int16_t)plan->coefficient
                                                          : (int16_t)plan->coefficient);
            code("    txa\n    sec\n    sbc 1,s\n");

            if (magnitude > 1) {
                code("    pha\n");

                for (k = 1; k <= magnitude / 2; k *= 2) {
                }

                for (k /= 2; k; k /= 2) {
                    code("    asl a\n");

                    if (magnitude & k)
                        code("    clc\n    adc 1,s\n");
                }

                code("    plx\n");
            }

            if ((int16_t)plan->coefficient < 0)
                code("    eor #$FFFF\n    inc a\n");
            if (plan->constant)
                code("    clc\n    adc #$%04X\n", plan->constant);
        } else
            code("    lda #$%04X\n", plan->constant);
    }

    narrow_char(v->function->symbol->type);

    if (plan->coefficient)
        code("    plx\n");

    code("    ply\n    rts\n__size_%s = * - %s\n", v->entry + 1, v->entry);
}

static void bank_emit(void)
{
    unsigned i;

    for (i = 0; i < bank_state.count; ++i) {
        if (bank_state.variants[i]->used)
            bank_emit_variant(bank_state.variants[i]);

        free(bank_state.variants[i]);
    }
}
