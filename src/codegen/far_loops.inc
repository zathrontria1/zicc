/* Reuse the byte-loop IR with private long-indirect cursors. No assumptions
 * about runtime banks or bank containment: carry and borrow are explicit.
 * The accepted leaf region contains no calls or observable pointer homes. */
static unsigned far_loop_argument(Function *f, unsigned parameter, unsigned saved)
{
    unsigned i, offset = 3 + saved + cg.parser->long_return;

    if (parameter < 2 && reg_width(f->symbol->params[parameter]) == 2)
        return saved - (parameter ? 5 : 3);

    for (i = 0; i < parameter; ++i) {
        if (i >= 2 || reg_width(f->symbol->params[i]) != 2)
            offset += reg_width(f->symbol->params[i]);
    }

    return offset;
}

static void far_loop_step(Symbol *pointer, unsigned reg, int delta)
{
    unsigned offset = reg * 4, done = ++cg.label;

    if (delta > 0) {
        code("    inc z:$%02X\n    bne cg_%s_%u\n    inc z:$%02X\n", DP_SCRATCH_BASE + offset,
             cg.parser->unit, done, DP_SCRATCH_BASE + 1 + offset);

        if (far_pointer(pointer->type))
            code("    bne cg_%s_%u\n    inc z:$%02X\n", cg.parser->unit, done,
                 DP_SCRATCH_BASE + 2 + offset);
    } else {
        /* Keep both accumulator bytes: LOOP_SAVE may hold a temporary in B */
        code("    pha\n    lda z:$%02X\n    bne cg_%s_%u\n", DP_SCRATCH_BASE + offset,
             cg.parser->unit, done);

        if (far_pointer(pointer->type)) {
            unsigned high = ++cg.label;
            code("    lda z:$%02X\n    bne cg_%s_%u\n    dec z:$%02X\n",
                 DP_SCRATCH_BASE + 1 + offset, cg.parser->unit, high, DP_SCRATCH_BASE + 2 + offset);
            label(high);
        }

        code("    dec z:$%02X\n", DP_SCRATCH_BASE + 1 + offset);
        label(done);
        code("    dec z:$%02X\n    pla\n", DP_SCRATCH_BASE + offset);
        return;
    }

    label(done);
}

static void far_loop_predicate(LoopPredicate *predicate, int *cached, int *zero_flags)
{
    if (*cached != predicate->reg) {
        code("    lda [$%02X]\n", DP_SCRATCH_BASE + predicate->reg * 4);
        *cached = predicate->reg;
        *zero_flags = 1;
    }

    if (predicate->kind == LOOP_COMPARE) {
        code("    cmp [$%02X]\n", DP_SCRATCH_BASE + predicate->other * 4);
        *zero_flags = 0;
    } else if (!*zero_flags) {
        code("    cmp #$00\n");
        *zero_flags = 1;
    }
}

static void far_loop_instructions(RegisterLoop *loop, int cached)
{
    unsigned i;

    for (i = 0; i < loop->instruction_count; ++i) {
        LoopInstruction *instruction = &loop->instructions[i];

        switch (instruction->kind) {
        case LOOP_LOAD:
            if (cached != instruction->reg)
                code("    lda [$%02X]\n", DP_SCRATCH_BASE + instruction->reg * 4);

            cached = instruction->reg;
            break;
        case LOOP_STORE:
            code("    sta [$%02X]\n", DP_SCRATCH_BASE + instruction->reg * 4);
            cached = -1;
            break;
        case LOOP_STEP:
            far_loop_step(loop->pointers[instruction->reg], instruction->reg, instruction->op);

            if (cached == instruction->reg) {
                cached = -1;
            }

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
}

#include "indexed_far_loops.inc"

typedef struct {
    RegisterLoop loop;
    Statement *stores[128];
    unsigned ns, coefficient, constant, remaining_value;
    int predicate, return_pointer;
    LoopPredicate result;
} FarLeafPlan;

static int far_leaf_plan(Function *f, FarLeafPlan *plan)
{
    Statement *statements[128], *initial[128], *stores[128], *region;
    Symbol *symbols[128];

    unsigned values[128], count = 0, n = 0, ni = 0, position = 128, ns = 0, i, j;
    unsigned coefficient = 0, constant = 0;
    uint32_t value;
    RegisterLoop loop;
    LoopPredicate result;
    Expr *tail = NULL;
    int predicate = 0, return_pointer = -1;

    memset(plan, 0, sizeof *plan);
    memset(&result, 0, sizeof result);

    if (cg.parser->no_register_loops || !strcmp(f->symbol->name, "main") ||
        f->symbol->param_count < 0 || reg_width(f->symbol->type) != 2 ||
        f->symbol->type.base == TY_FLOAT || cg.cursor_count || divmod_state.count)
        return 0;
    if (!loop_flatten(f->body, statements, &count))
        return 0;

    for (i = 0; i < count; ++i) {
        if (statements[i]->kind == ST_WHILE || statements[i]->kind == ST_FOR) {
            position = i;
            break;
        }
    }

    if (position == 128 || !loop_initializers(statements, position, symbols, values, &n))
        return 0;

    region = statements[position];

    if (!loop_flatten(region->initial, initial, &ni) ||
        !loop_initializers(initial, ni, symbols, values, &n) || !loop_plan(&loop, region) ||
        loop.indexed || !loop_has_far(&loop))
        return 0;

    for (i = position + 1; i < count; ++i) {
        Statement *s = statements[i];
        Expr *e = s->expression;

        if (s->kind == ST_RETURN) {
            if (i + 1 != count)
                return 0;

            tail = e;
            break;
        }
        if (s->kind != ST_EXPR || e->kind != EX_ASSIGN || e->op || e->left->kind != EX_DEREF ||
            width(e->left->type) != 1 || e->left->left->kind != EX_OBJECT ||
            !integer_constant(e->right, &value))
            return 0;

        for (j = 0; j < loop.pointer_count; ++j) {
            if (loop.pointers[j] == e->left->left->symbol)
                break;
        }

        if (j == loop.pointer_count) {
            return 0;
        }

        stores[ns++] = s;
    }

    if (!tail && f->symbol->type.base != TY_VOID)
        return 0;

    if (tail && tail->kind == EX_OBJECT)
        for (i = 0; i < loop.pointer_count; ++i) {
            if (tail->symbol == loop.pointers[i])
                return_pointer = (int)i;
        }

    if (tail && return_pointer < 0) {
        if (loop_predicate(&loop, tail, 0, &result))
            predicate = 1;
        else if (!loop_affine_result(&loop, tail, symbols, values, n, &coefficient, &constant))
            return 0;
    }
    if (predicate && ns)
        return 0;

    for (i = 0; i < loop.pointer_count; ++i) {
        if (loop_parameter(f, loop.pointers[i]) < 0)
            return 0;
    }

    if (loop.remaining && loop_parameter(f, loop.remaining) < 0) {
        for (i = 0; i < n; ++i) {
            if (symbols[i] == loop.remaining)
                break;
        }

        if (i == n)
            return 0;
    }

    plan->loop = loop;
    plan->ns = ns;
    plan->coefficient = coefficient;
    plan->constant = constant;
    plan->predicate = predicate;
    plan->return_pointer = return_pointer;
    plan->result = result;

    for (i = 0; i < ns; ++i) {
        plan->stores[i] = stores[i];
    }

    if (loop.remaining && loop_parameter(f, loop.remaining) < 0) {
        for (i = 0; i < n; ++i) {
            if (symbols[i] == loop.remaining)
                break;
        }

        plan->remaining_value = values[i];
    }

    return 1;
}

static int far_loop_leaf(Function *f)
{
    FarLeafPlan plan;
    RegisterLoop loop;
    Statement **stores;
    LoopPredicate result;

    unsigned ns, coefficient, constant, saved, start, end, flags, done, i, j, k;
    uint32_t value;
    int predicate, return_pointer, cached = -1, zero_flags = 0, parameter;

    if (!far_leaf_plan(f, &plan))
        return 0;

    loop = plan.loop;
    stores = plan.stores;
    ns = plan.ns;
    result = plan.result;
    predicate = plan.predicate;
    return_pointer = plan.return_pointer;
    coefficient = plan.coefficient;
    constant = plan.constant;

    if (far_indexed_leaf(f, &loop, stores, ns, predicate, &result, return_pointer, coefficient,
                         constant, plan.remaining_value))
        return 1;

    saved = 6;
    start = ++cg.label;
    end = ++cg.label;
    flags = ++cg.label;
    done = ++cg.label;
    code(".segment \"CODE\"\n.export _%s\n_%s:\n; far byte loop: private DP cursors, A8\n    phy\n "
         "   phx\n    pha\n",
         f->symbol->asm_name, f->symbol->asm_name);

    for (i = 0; i < loop.pointer_count; ++i) {
        parameter = loop_parameter(f, loop.pointers[i]);
        j = far_loop_argument(f, (unsigned)parameter, saved);
        code("    lda %u,s\n    sta z:$%02X\n", j, DP_SCRATCH_BASE + i * 4);

        if (far_pointer(loop.pointers[i]->type))
            code("    lda %u,s\n    and #$00FF\n", j + 2);
        else
            code("    lda #$007E\n");

        code("    sta z:$%02X\n", DP_SCRATCH_BASE + 2 + i * 4);
    }

    if (loop.remaining) {
        parameter = loop_parameter(f, loop.remaining);

        if (parameter >= 0)
            code("    lda %u,s\n    tay\n", far_loop_argument(f, (unsigned)parameter, saved));
        else
            code("    ldy #$%04X\n", plan.remaining_value);
    }

    code("    sep #$20\n.a8\n");
    label(start);

    if (loop.predicate_count) {
        for (i = 0; i < loop.predicate_count; ++i) {
            far_loop_predicate(&loop.predicates[i], &cached, &zero_flags);
            loop_predicate_branch(&loop.predicates[i],
                                  predicate && loop_same_test(&loop.predicates[i], &result) ? flags
                                                                                            : end);
        }
    } else if (loop.remaining) {
        code("    cpy #0\n    bne :+\n");
        jump(end);
        code(":\n");
    } else {
        code("    lda [$%02X]\n    bne :+\n", DP_SCRATCH_BASE + loop.sentinel * 4);
        jump(end);
        code(":\n");
        cached = loop.sentinel;
    }

    far_loop_instructions(&loop, cached);

    if (loop.remaining) {
        code("    dey\n");
    }

    jump(start);
    label(end);

    for (i = 0; i < ns; ++i) {
        Expr *e = stores[i]->expression;

        integer_constant(e->right, &value);

        for (j = 0; j < loop.pointer_count; ++j) {
            if (loop.pointers[j] == e->left->left->symbol)
                break;
        }

        code("    lda #$%02X\n    sta [$%02X]\n", value & 255, DP_SCRATCH_BASE + j * 4);
    }

    if (predicate) {
        cached = -1;
        zero_flags = 0;
        far_loop_predicate(&result, &cached, &zero_flags);
        label(flags);
        code("    rep #$20\n.a16\n    %s :+\n    lda #1\n", result.op == TOK_EQ ? "bne" : "beq");
        jump(done);
        code(":\n    lda #0\n");
        label(done);
    } else {
        code("    rep #$20\n.a16\n");

        if (return_pointer >= 0)
            code("    lda z:$%02X\n", DP_SCRATCH_BASE + return_pointer * 4);
        else if (coefficient) {
            unsigned magnitude =
                (unsigned)((int16_t)coefficient < 0 ? -(int16_t)coefficient : (int16_t)coefficient);
            j = far_loop_argument(f, (unsigned)loop_parameter(f, loop.pointers[loop.anchor]),
                                  saved);

            if (loop.strides[loop.anchor] > 0)
                code("    lda z:$%02X\n    sec\n    sbc %u,s\n", DP_SCRATCH_BASE + loop.anchor * 4,
                     j);
            else
                code("    lda %u,s\n    sec\n    sbc z:$%02X\n", j,
                     DP_SCRATCH_BASE + loop.anchor * 4);

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

            if ((int16_t)coefficient < 0)
                code("    eor #$FFFF\n    inc a\n");
            if (constant)
                code("    clc\n    adc #$%04X\n", constant);
        } else
            code("    lda #$%04X\n", constant);
    }

    narrow_char(f->symbol->type);
    code("    tax\n");
    code("    pla\n    pla\n    txa\n    ply\n    rts\n__size_%s = * - _%s\n", f->symbol->asm_name,
         f->symbol->asm_name);
    return 1;
}
