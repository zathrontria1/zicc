/* A common Y displacement replaces synchronized forward far-cursor updates.
 * Each cursor's accesses must precede its single step. Deferring those private
 * steps preserves the order of memory operations even when pointees alias. */
static int far_indexed_plan(RegisterLoop *loop, int *near)
{
    unsigned i;
    int stepped[2] = {0, 0};

    *near = -1;
    if (loop->remaining) {
        for (i = 0; i < loop->pointer_count; ++i) {
            if (!far_pointer(loop->pointers[i]->type))
                return 0;
        }
    }

    for (i = 0; i < loop->pointer_count; ++i) {
        if (far_pointer(loop->pointers[i]->type)) {
            if (loop->strides[i] != 1)
                return 0;
        } else {
            if (*near >= 0)
                return 0;

            *near = (int)i;
        }
    }

    for (i = 0; i < loop->instruction_count; ++i) {
        LoopInstruction *instruction = &loop->instructions[i];
        int reg = instruction->reg;

        if (!far_pointer(loop->pointers[reg]->type))
            continue;

        if (instruction->kind == LOOP_STEP) {
            if (stepped[reg] || instruction->op != 1) {
                return 0;
            }

            stepped[reg] = 1;
        } else if ((instruction->kind == LOOP_LOAD || instruction->kind == LOOP_STORE) &&
                   stepped[reg])
            return 0;
    }

    return 1;
}

static void far_indexed_memory(const char *op, int reg, int near, unsigned *slots)
{
    if (reg == near)
        code("    %s a:$0000,x\n", op);
    else
        code("    %s [$%02X],y\n", op, DP_SCRATCH_BASE + slots[reg] * 4);
}

static void far_indexed_predicate(LoopPredicate *predicate, int near, unsigned *slots, int *cached,
                                  int *zero_flags)
{
    if (*cached != predicate->reg) {
        far_indexed_memory("lda", predicate->reg, near, slots);
        *cached = predicate->reg;
        *zero_flags = 1;
    }

    if (predicate->kind == LOOP_COMPARE) {
        far_indexed_memory("cmp", predicate->other, near, slots);
        *zero_flags = 0;
    } else if (!*zero_flags) {
        code("    cmp #$00\n");
        *zero_flags = 1;
    }
}

/* Snapshots are unnecessary: X/A inputs are consumed before far arguments,
 * and iteration results come from Y. Arithmetic DP is already call-clobbered. */
static int far_indexed_leaf(Function *f, RegisterLoop *loop, Statement **stores, unsigned ns,
                            int predicate, LoopPredicate *result, int return_pointer,
                            unsigned coefficient, unsigned constant, unsigned remaining_value)
{
    int near, parameter = -1, cached = -1, zero_flags = 0, reload = 0;

    unsigned slots[2], far_count = 0, i, j, k, saved, start, end, flags, done;

    if (!far_indexed_plan(loop, &near))
        return 0;

    for (i = 0; i < loop->pointer_count; ++i) {
        if ((int)i != near)
            slots[i] = far_count++;
    }

    saved = 2;
    start = ++cg.label;
    end = ++cg.label;
    flags = ++cg.label;
    done = ++cg.label;

    if (near >= 0)
        parameter = loop_parameter(f, loop->pointers[near]);
    else if (loop->remaining)
        parameter = loop_parameter(f, loop->remaining);

    code(".segment \"CODE\"\n.export _%s\n_%s:\n; far byte loop: indexed Y%s, A8\n    phy\n",
         f->symbol->asm_name, f->symbol->asm_name, near >= 0 ? ", near X" : "");

    if (parameter == 1)
        code("    tax\n");

    if (parameter >= 2) {
        code("    lda %u,s\n    tax\n", far_loop_argument(f, (unsigned)parameter, saved));
    }

    if (loop->remaining && parameter < 0)
        code("    ldx #$%04X\n", remaining_value);

    for (i = 0; i < loop->pointer_count; ++i) {
        if ((int)i != near) {
            j = far_loop_argument(f, (unsigned)loop_parameter(f, loop->pointers[i]), saved);
            /* The public far ABI already guarantees a zero padding byte */
            code("    lda %u,s\n    sta z:$%02X\n    lda %u,s\n    sta z:$%02X\n", j,
                 DP_SCRATCH_BASE + slots[i] * 4, j + 2, DP_SCRATCH_BASE + 2 + slots[i] * 4);
        }
    }

    if (predicate && !loop->predicate_count)
        reload = loop->remaining || loop->sentinel != result->reg;

    code("    ldy #0\n    sep #$20\n.a8\n");
    label(start);

    if (loop->predicate_count) {
        for (i = 0; i < loop->predicate_count; ++i) {
            LoopPredicate *p = &loop->predicates[i];

            far_indexed_predicate(p, near, slots, &cached, &zero_flags);
            loop_predicate_branch(p, predicate && loop_same_test(p, result) ? flags : end);

            if (predicate && !loop_same_test(p, result) && p->reg != result->reg)
                reload = 1;
        }
    } else if (loop->remaining) {
        code("    cpx #0\n    bne :+\n");
        jump(end);
        code(":\n");
    } else {
        far_indexed_memory("lda", loop->sentinel, near, slots);
        code("    bne :+\n");
        jump(end);
        code(":\n");
        cached = loop->sentinel;
    }

    for (i = 0; i < loop->instruction_count; ++i) {
        LoopInstruction *instruction = &loop->instructions[i];

        switch (instruction->kind) {
        case LOOP_LOAD:
            if (cached != instruction->reg)
                far_indexed_memory("lda", instruction->reg, near, slots);

            cached = instruction->reg;
            break;
        case LOOP_STORE:
            far_indexed_memory("sta", instruction->reg, near, slots);
            cached = -1;
            break;
        case LOOP_STEP:
            if (instruction->reg == near)
                code("    %s\n", instruction->op > 0 ? "inx" : "dex");

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

    if (loop->remaining)
        code("    dex\n");

    code("    iny\n    bne cg_%s_%u\n", cg.parser->unit, start);

    for (i = 0; i < far_count; ++i) {
        code("    inc z:$%02X\n", DP_SCRATCH_BASE + 2 + i * 4);
    }

    jump(start);
    label(end);

    for (i = 0; i < ns; ++i) {
        Expr *e = stores[i]->expression;
        uint32_t value;

        integer_constant(e->right, &value);

        for (j = 0; j < loop->pointer_count; ++j) {
            if (loop->pointers[j] == e->left->left->symbol)
                break;
        }

        if (i || loop->predicate_count || loop->remaining || (value & 255))
            code("    lda #$%02X\n", value & 255);

        far_indexed_memory("sta", (int)j, near, slots);
    }

    if (predicate) {
        cached = reload ? -1 : result->reg;
        zero_flags = 0;
        far_indexed_predicate(result, near, slots, &cached, &zero_flags);
        label(flags);
        code("    rep #$20\n.a16\n    %s :+\n    lda #1\n", result->op == TOK_EQ ? "bne" : "beq");
        jump(done);
        code(":\n    lda #0\n");
        label(done);
    } else {
        code("    rep #$20\n.a16\n");

        if (return_pointer >= 0)
            code("    txa\n");
        else if (coefficient) {
            unsigned magnitude =
                (unsigned)((int16_t)coefficient < 0 ? -(int16_t)coefficient : (int16_t)coefficient);
            code("    tya\n");

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
    code("    ply\n    rts\n__size_%s = * - _%s\n", f->symbol->asm_name, f->symbol->asm_name);
    return 1;
}
