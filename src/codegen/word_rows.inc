/* Keep the two bases for a straight-line run of far word loads and near
 * merges. A split row may also assign a second word from the same load. */
typedef struct {
    Expr *statements[3];
    unsigned count, source, destination[2];
} WordRow;

typedef struct {
    WordRow rows[8];
    Statement *last;
    Symbol *source, *destination, *temp;
    unsigned count, max;
} WordRowPlan;

static int row_word(Type t)
{
    return t.base == TY_INT && !t.pointers && !t.array && !t.is_bool && width(t) == 2;
}

static Symbol *row_pointer(Expr *e, unsigned *offset)
{
    uint32_t index = 0;

    if (e->kind != EX_DEREF || !row_word(e->type))
        return NULL;

    e = e->left;

    if (e->kind == EX_BINARY && e->op == '+' && integer_constant(e->right, &index))
        e = e->left;
    if (e->kind != EX_OBJECT || e->type.pointers != 1 || !row_word(pointed_type(e->type)) ||
        index > 127 || !loop_private(e->symbol))
        return NULL;

    *offset = (unsigned)index * 2;
    return e->symbol;
}

/* Only constant conditionals can be flattened, and only expression
 * statements are accepted. No label or control transfer is swallowed. */
static int row_statements(Statement *s, WordRow *row)
{
    uint32_t test;

    if (s->kind == ST_EXPR) {
        if (row->count == 3 || volatile_expression(s->expression))
            return 0;

        row->statements[row->count++] = s->expression;
        return 1;
    }

    if (s->kind == ST_IF && integer_constant(s->expression, &test)) {
        if (statement_has_case(s->body) || statement_has_case(s->alternate))
            return 0;

        s = test ? s->body : s->alternate;
    } else if (s->kind == ST_BLOCK && !s->inline_callee)
        s = s->body;
    else
        return 0;

    for (; s; s = s->next) {
        if (!row_statements(s, row))
            return 0;
    }

    return 1;
}

/* Validate or emit an A16 expression with exactly one leaf */
typedef enum { ROW_CHECK, ROW_FAST, ROW_WRAP } RowEmission;

static Expr *row_value(Expr *e, RowEmission emit)
{
    Expr *leaf;
    uint32_t n;

    if (!row_word(e->type))
        return NULL;
    if (e->kind == EX_OBJECT || e->kind == EX_DEREF)
        return e;
    if (e->kind == EX_CAST)
        return row_value(e->left, emit);
    if (e->kind != EX_BINARY || !integer_constant(e->right, &n) ||
        (e->op != '&' && e->op != TOK_SHL && e->op != TOK_SHR) ||
        (e->op != '&' && (n >= 16 || (e->op == TOK_SHR && !e->type.is_unsigned))))
        return NULL;

    leaf = row_value(e->left, emit);

    if (leaf && emit) {
        if (e->op == '&')
            code("    and #$%04X\n", (unsigned)n & 65535);
        /* The loop template must not specialize shifts using facts about
         * the first row's operand alone. */
        else if (emit == ROW_WRAP || !word_shift_loaded(e->left, e->op, e->type, (unsigned)n))

            while (n--) {
                code(e->op == TOK_SHL ? "    asl a\n" : "    lsr a\n");
            }
    }

    return leaf;
}

static int row_plan(WordRow *row, Symbol **source, Symbol **dest, Symbol **temp)
{
    Expr *e, *leaf;
    Symbol *src, *dst, *tmp = NULL;

    unsigned i, first;

    if (row->count != 1 && row->count != 3)
        return 0;

    first = row->count == 3;
    e = row->statements[0];

    if (e->kind != EX_ASSIGN)
        return 0;

    if (first) {
        if (e->op || e->left->kind != EX_OBJECT || !row_word(e->left->type) ||
            !loop_private(e->left->symbol))
            return 0;

        tmp = e->left->symbol;
    }

    leaf = row_value(e->right, ROW_CHECK);

    if (!leaf || !(src = row_pointer(leaf, &row->source)) || !far_pointer(src->type))
        return 0;

    dst = NULL;

    for (i = first; i < row->count; ++i) {
        Symbol *base;

        e = row->statements[i];

        if (e->kind != EX_ASSIGN || (e->op != '|' && (!first || e->op)) ||
            !(base = row_pointer(e->left, &row->destination[i - first])) ||
            far_pointer(base->type) || (dst && dst != base))
            return 0;

        dst = base;

        if (first) {
            leaf = row_value(e->right, ROW_CHECK);

            if (!leaf || leaf->kind != EX_OBJECT || leaf->symbol != tmp)
                return 0;
        }
    }

    *source = src;
    *dest = dst;
    *temp = tmp;
    return 1;
}

static const char *const row_wrap_cursor[] = {"$00", "__arith_rhs"};

static void row_operations(WordRow *row, int split, Symbol *buffer, const WordRow *cursors)
{
    unsigned i, swap = cursors && row->destination[0] != cursors->destination[0];
    int indexed = !cursors;

    if (split) {
        row_value(row->statements[0]->right, indexed ? ROW_FAST : ROW_WRAP);
        code(indexed ? "    sta z:__arith_rhs\n" : "    pha\n");
    }

    for (i = split; i < row->count; ++i) {
        Expr *e = row->statements[i];

        unsigned slot = i - split;

        if (split && i > 1)
            code(indexed ? "    lda z:__arith_rhs\n" : "    pla\n    pha\n");

        row_value(e->right, indexed ? ROW_FAST : ROW_WRAP);

        if (indexed) {
            unsigned offset = row->destination[slot];

            if (buffer) {
                if (e->op == '|')
                    code("    ora a:.loword(_%s+$%04X),y\n", buffer->asm_name, offset);

                code("    sta a:.loword(_%s+$%04X),y\n", buffer->asm_name, offset);
            } else {
                if (e->op == '|')
                    code("    ora a:$%04X,x\n", offset);

                code("    sta a:$%04X,x\n", offset);
            }
        } else {
            const char *cursor = row_wrap_cursor[slot ^ swap];

            if (e->op == '|')
                code("    ora (%s)\n", cursor);

            code("    sta (%s)\n", cursor);
        }
    }

    if (split && !indexed)
        code("    pla\n");
}

/* The caller has validated each expression. Ignore the leaf address and
 * compare only the sequence of word operations applied to the loaded value. */
static int row_same_operations(Expr *a, Expr *b)
{
    uint32_t left, right;

    while (a->kind == EX_CAST) {
        a = a->left;
    }

    while (b->kind == EX_CAST) {
        b = b->left;
    }

    if (a->kind != EX_BINARY || b->kind != EX_BINARY)
        return a->kind == b->kind;

    return a->op == b->op && integer_constant(a->right, &left) &&
           integer_constant(b->right, &right) && left == right &&
           row_same_operations(a->left, b->left);
}

static void row_write_temporary(Symbol *temp)
{
    if (temp) {
        code("    lda z:__arith_rhs\n    sta ");
        array_operand(temp, 0);
        code("\n");
    }
}

static int row_can_wrap(WordRowPlan *plan)
{
    WordRow *rows = plan->rows;

    unsigned i, j, outputs = rows[0].count - (plan->temp != NULL);

    for (i = 1; i < plan->count; ++i) {
        for (j = 0; j < rows[0].count; ++j) {
            if (rows[i].statements[j]->op != rows[0].statements[j]->op ||
                !row_same_operations(rows[i].statements[j]->right, rows[0].statements[j]->right))
                return 0;
        }

        for (j = 0; j < outputs; ++j) {
            if (rows[i].destination[j] != rows[0].destination[j] + 2 * i)
                return 0;
        }
    }

    return 1;
}

static void row_wrap_setup(WordRowPlan *plan, FixedWordRows *fixed)
{
    WordRow *row = &plan->rows[0];

    unsigned j, outputs = row->count - (plan->temp != NULL);
    /* Borrow and restore the compiler-owned counter word at $00. Save a split row
     * on the stack so the cold path needs no extra arithmetic
     * DP homes, which would also change register allocation in the fast path. */
    code("    pei ($00)\n");

    for (j = 0; j < outputs; ++j) {
        code("    lda ");
        array_operand(plan->destination, 0);
        code("\n");

        if (fixed)
            code("    clc\n    adc #.loword(_%s)\n", fixed->buffer->asm_name);
        if (row->destination[j])
            code("    clc\n    adc #$%04X\n", row->destination[j]);

        code("    sta z:%s\n", row_wrap_cursor[j]);
    }

    code("    lda ");
    array_operand(plan->source, 0);
    code("\n");

    if (fixed) {
        code("    clc\n    adc #.loword(_%s)\n    sta z:__arith_lhs\n"
             "    lda #.bankbyte(_%s)\n    adc #0\n",
             fixed->font->asm_name, fixed->font->asm_name);
    } else {
        code("    sta z:__arith_lhs\n    lda ");
        array_operand(plan->source, 2);
        code("\n");
    }

    code("    sta z:__arith_lhs+2\n    phy\n    ldy #$%04X\n", row->source);
}

static void row_wrap_advance(WordRowPlan *plan)
{
    unsigned j, outputs = plan->rows[0].count - (plan->temp != NULL);

    /* Unindexed indirect stores stay in DBR. Each word cursor wraps at
     * 16 bits, while the long-indirect source may advance into another bank. */
    for (j = 0; j < outputs; ++j) {
        code("    inc z:%s\n    inc z:%s\n", row_wrap_cursor[j], row_wrap_cursor[j]);
    }

    code("    iny\n    iny\n");
}

static void row_wrap_finish(WordRowPlan *plan)
{
    code("    ply\n");

    if (plan->temp) {
        code("    sta ");
        array_operand(plan->temp, 0);
        code("\n");
    }

    code("    pla\n    sta z:$00\n");
}

static int row_wrapping_loop(WordRowPlan *plan, FixedWordRows *fixed)
{
    unsigned again;

    if (!row_can_wrap(plan))
        return 0;

    code("; compact wrapping word rows\n");
    row_wrap_setup(plan, fixed);
    code("    ldx #$%04X\n", plan->count);
    again = ++cg.label;
    label(again);
    code("    lda [__arith_lhs],y\n");
    row_operations(&plan->rows[0], plan->temp != NULL, NULL, &plan->rows[0]);
    row_wrap_advance(plan);
    code("    dex\n    bne cg_%s_%u\n", cg.parser->unit, again);
    row_wrap_finish(plan);
    return 1;
}

static int word_rows_enabled(void)
{
    return !(cg.parser->no_indexed_operands || cg.parser->no_body_optimizations ||
             cg.parser->no_strength_reduction || cg.stack_leaf || cg.scalar_leaf ||
             cg.scalar_first || cg.leaf_count || cg.retained_index || cg.retained_second ||
             cg.affine_active || bound_state.cursor || cg.scan_cursor || cg.dead_index_count ||
             cg.omitted_parameter_count || cg.function->symbol->interrupt);
}

static int word_row_plan(Statement *s, WordRowPlan *plan)
{
    Statement *entry = s;

    for (; s && plan->count < 8; s = s->next) {
        WordRow row = {0};
        Statement *end = s, *body = s;
        Symbol *source, *dest, *temp;

        unsigned i;

        if (s == entry && s->kind == ST_CASE)
            body = s->body;
        if (!row_statements(body, &row))
            break;

        if (row.count == 1 && row.statements[0]->kind == EX_ASSIGN &&
            row.statements[0]->left->kind == EX_OBJECT) {
            if (!s->next || !s->next->next || !row_statements(s->next, &row) ||
                !row_statements(s->next->next, &row) || row.count != 3)
                break;

            end = s->next->next;

            if (!row_plan(&row, &source, &dest, &temp))
                break;
        } else if (!row_plan(&row, &source, &dest, &temp))
            break;

        if (plan->count &&
            (plan->source != source || plan->destination != dest || plan->temp != temp ||
             row.source != plan->rows[plan->count - 1].source + 2))
            break;

        s = end;
        plan->source = source;
        plan->destination = dest;
        plan->temp = temp;
        plan->last = s;
        plan->rows[plan->count++] = row;

        for (i = 0; i < row.count - (temp != NULL); ++i) {
            if (row.destination[i] > plan->max)
                plan->max = row.destination[i];
        }
    }

    return plan->count >= 2;
}

static int fixed_row_limit(WordRowPlan *plan, FixedWordRows *fixed, unsigned *limit)
{
    unsigned bytes = width(fixed->buffer->type);

    if (plan->source != fixed->source || plan->destination != fixed->destination ||
        bytes < plan->max + 2 || width(fixed->font->type) < plan->rows[plan->count - 1].source + 2)
        return 0;

    *limit = bytes - plan->max - 1;
    return 1;
}

static void fixed_row_record(WordRowPlan *plan, FixedWordRows *fixed)
{
    unsigned i, j;

    for (i = 0; i < plan->count; ++i) {
        for (j = 0; j < plan->rows[i].count; ++j) {
            Expr *e = plan->rows[i].statements[j];

            fixed->source_uses += expression_references(e, plan->source);
            fixed->destination_uses += expression_references(e, plan->destination);
        }
    }

    fixed->font->used = fixed->buffer->used = 1;
}

static void row_fast(WordRowPlan *plan, FixedWordRows *fixed)
{
    unsigned i;

    if (fixed) {
        /* X holds the destination offset. Load the source before borrowing
         * Y, since the source offset may still have a frame home. */
        code("    phy\n    lda ");
        array_operand(plan->source, 0);
        code("\n    txy\n    tax\n");
    } else {
        code("    tax\n    lda ");
        array_operand(plan->source, 0);
        code("\n    sta z:__arith_lhs\n    lda ");
        array_operand(plan->source, 2);
        code("\n    sta z:__arith_lhs+2\n    phy\n");
    }

    for (i = 0; i < plan->count; ++i) {
        WordRow *row = &plan->rows[i];

        if (fixed)
            code("    lda f:_%s+$%04X,x\n", fixed->font->asm_name, row->source);
        else if (row->source)
            code("    ldy #$%04X\n    lda [__arith_lhs],y\n", row->source);
        else
            code("    lda [__arith_lhs]\n");

        row_operations(row, plan->temp != NULL, fixed ? fixed->buffer : NULL, NULL);
    }

    code("    ply\n");
    row_write_temporary(plan->temp);
}

static Statement *word_row_region(Statement *s)
{
    WordRowPlan plan = {0};
    FixedWordRows *fixed = NULL;

    unsigned limit, slow, done, i, j;
    int guard;

    if (!word_rows_enabled() || !word_row_plan(s, &plan))
        return NULL;

    if (cg.fixed_rows && plan.source == cg.fixed_rows->source &&
        plan.destination == cg.fixed_rows->destination) {
        fixed = cg.fixed_rows;

        if (!fixed_row_limit(&plan, fixed, &limit)) {
            fixed->failed = 1;
            return plan.last;
        }

        fixed_row_record(&plan, fixed);
    } else
        limit = 65536 - plan.max;

    guard = fixed ? fixed->max_offset >= limit : plan.max != 0;
    slow = ++cg.label;
    done = ++cg.label;
    cg.arithmetic = 1;

    if (s->kind == ST_CASE)
        label(s->case_label);

    divmod_state.available = 0;
    code("; retained far/near word rows: %u rows\n    %s ", plan.count, fixed ? "ldx" : "lda");
    array_operand(plan.destination, 0);
    code("\n");

    /* An indexed near address can carry out of DBR. Check the full row span */
    if (guard) {
        code("    %s #$%04X\n    bcc :+\n", fixed ? "cpx" : "cmp", limit);
        jump(slow);
        code(":\n");
    }

    row_fast(&plan, fixed);

    if (guard) {
        jump(done);
        label(slow);
        divmod_state.available = 0;

        if (!row_wrapping_loop(&plan, fixed)) {
            if (fixed)
                fixed->failed = 1;
            else
                for (i = 0; i < plan.count; ++i) {
                    for (j = 0; j < plan.rows[i].count; ++j) {
                        emit_discarded(plan.rows[i].statements[j]);
                    }
                }
        }

        label(done);
    }

    divmod_state.available = 0;
    return plan.last;
}

typedef struct {
    Statement *item;
    WordRowPlan plan;
    unsigned group;
} WordRowCase;

/* Take complete, independently entered arms with no fallthrough. A braced
 * arm may break either inside the block or immediately after it. */
static int word_row_case(Statement *item, WordRowPlan *plan, Statement **next)
{
    Statement *block = item->body, *stop;

    if (block && (block->kind != ST_BLOCK || block->inline_callee))
        block = NULL;
    if (!word_row_plan(block ? block->body : item, plan))
        return 0;

    stop = plan->last->next;

    if (block && !stop) {
        block = NULL;
        stop = item->next;
    }

    if (!stop || stop->kind != ST_BREAK || (block && stop->next))
        return 0;

    *next = block ? item->next : stop->next;
    return 1;
}

static int row_wrap_compatible(WordRowPlan *a, WordRowPlan *b)
{
    WordRow *left = &a->rows[0], *right = &b->rows[0];

    if (a->count != b->count || a->temp != b->temp || left->source != right->source)
        return 0;

    return (left->destination[0] == right->destination[0] &&
            left->destination[1] == right->destination[1]) ||
           (a->temp && left->destination[0] == right->destination[1] &&
            left->destination[1] == right->destination[0]);
}

static void row_wrap_group(WordRowCase *cases, unsigned count, unsigned group, FixedWordRows *fixed,
                           unsigned end)
{
    WordRowPlan *plan = &cases[group].plan;
    WordRow *cursors = &plan->rows[0];

    unsigned i, fallback = group, again = ++cg.label, step = ++cg.label;

    /* X holds the original selector. Prefer the default arm when present */
    for (i = group; i < count; ++i) {
        if (cases[i].group == group) {
            fallback = i;

            if (cases[i].item->is_default)
                break;
        }
    }

    code("; shared wrapping word rows\n");
    row_wrap_setup(plan, fixed);
    label(again);
    code("    lda [__arith_lhs],y\n");

    for (i = group; i < count; ++i) {
        if (cases[i].group == group && i != fallback) {
            unsigned next = ++cg.label;
            code("    cpx #$%04X\n    beq :+\n", cases[i].item->case_value & 65535);
            jump(next);
            code(":\n");
            row_operations(&cases[i].plan.rows[0], plan->temp != NULL, NULL, cursors);
            jump(step);
            label(next);
        }
    }

    row_operations(&cases[fallback].plan.rows[0], plan->temp != NULL, NULL, cursors);
    label(step);
    row_wrap_advance(plan);
    code("    cpy #$%04X\n    beq :+\n", plan->rows[0].source + 2 * plan->count);
    jump(again);
    code(":\n");
    row_wrap_finish(plan);
    jump(end);
}

static int emit_word_row_switch(Statement *s, unsigned end)
{
    FixedWordRows *fixed = cg.fixed_rows;
    WordRowCase cases[12];
    Statement *item, *current;

    unsigned count = 0, i, j, smallest = 65536, largest = 0, groups = 0, slow = 0, fallback;
    unsigned entry[sizeof cases / sizeof cases[0]];

    if (!fixed || !word_rows_enabled() || cg.function->jump_label_count || cg.numeric_index ||
        cg.numeric_recurrence || s->body->kind != ST_BLOCK || s->body->inline_callee ||
        s->expression->kind != EX_OBJECT || !row_word(s->expression->type) ||
        !body_private(s->expression->symbol))
        return 0;

    current = s->body->body;

    for (item = s->cases; item; item = item->case_next) {
        unsigned limit;

        if (current != item || count == sizeof cases / sizeof cases[0])
            return 0;

        cases[count].plan = (WordRowPlan){0};

        if (!word_row_case(item, &cases[count].plan, &current) ||
            !fixed_row_limit(&cases[count].plan, fixed, &limit))
            return 0;

        cases[count++].item = item;

        if (limit < smallest)
            smallest = limit;
        if (limit > largest)
            largest = limit;
    }

    if (current || count < 2)
        return 0;

    if (fixed->max_offset >= smallest) {
        /* Sharing one test must not narrow any individual arm's fast range */
        if (smallest != largest)
            return 0;

        for (i = 0; i < count; ++i) {
            if (!row_can_wrap(&cases[i].plan))
                return 0;

            for (j = 0; j < i; ++j) {
                if (row_wrap_compatible(&cases[i].plan, &cases[j].plan))
                    break;
            }

            cases[i].group = j;

            if (j == i)
                ++groups;
        }

        if (groups > count / 2)
            return 0;

        slow = ++cg.label;
    }

    code("; fixed word-row switch: %u cases\n    ldx ", count);
    array_operand(fixed->destination, 0);
    code("\n");

    if (slow) {
        code("    cpx #$%04X\n    bcc :+\n", smallest);
        jump(slow);
        code(":\n");
    }

    cg.arithmetic = 1;
    emit_switch_dispatch(s, assign_switch_labels(s, end), 0);

    for (i = 0; i < count; ++i) {
        label(cases[i].item->case_label);
        row_fast(&cases[i].plan, fixed);
        fixed_row_record(&cases[i].plan, fixed);
        jump(end);
    }

    if (slow) {
        label(slow);
        fallback = end;

        for (i = 0; i < count; ++i) {
            if (cases[i].group == i)
                entry[i] = ++cg.label;
        }

        for (i = 0; i < count; ++i) {
            item = cases[i].item;
            item->case_label = entry[cases[i].group];

            if (item->is_default)
                fallback = item->case_label;
        }

        /* One layout with a default can choose the operation inside the
         * wrapping loop without a second full switch dispatch. */
        if (groups == 1 && fallback != end) {
            emit_value(s->expression);
            code("    tax\n");
        } else
            emit_switch_dispatch(s, fallback, 1);

        for (i = 0; i < count; ++i) {
            if (cases[i].group == i) {
                label(entry[i]);
                row_wrap_group(cases, count, i, fixed, end);
            }
        }
    }

    divmod_state.available = 0;
    label(end);
    return 1;
}

static KnownValue known_type(Type t);
static KnownValue known_constant(uint32_t n, Type t);
static KnownValue known_cast(KnownValue v, Type t);
static KnownValue known_binary(int op, KnownValue a, KnownValue b, Type t);

/* Switches can lack flow facts. Typed masks and casts still bound the offset
 * locally, regardless of which control-flow edge reached the initializer. */
static KnownValue row_offset_value(Expr *e)
{
    if (e->known.valid)
        return e->known;
    if (e->range.valid)
        return e->range;
    if (e->kind == EX_INT)
        return known_constant(e->value, e->type);
    if (e->kind == EX_CAST)
        return known_cast(row_offset_value(e->left), e->type);
    if (e->kind == EX_BINARY)
        return known_binary(e->op, row_offset_value(e->left), row_offset_value(e->right), e->type);

    return known_type(e->type);
}

static unsigned fixed_row_max_offset(Expr *offset, unsigned scale, unsigned displacement)
{
    KnownValue v;
    uint64_t max;

    if (cg.parser->no_known_values)
        return 65536;

    v = row_offset_value(offset);

    if (!v.valid || v.min < 0)
        return 65536;

    max = (uint64_t)v.max * scale + displacement;
    return max <= 65535 ? (unsigned)max : 65536;
}

/* The far offset must already be an unsigned word in bytes, so replacing
 * pointer arithmetic with a long indexed load preserves the bank carry. */
static Symbol *fixed_row_font(Expr *e, Expr **offset)
{
    Expr *base;

    while (e->kind == EX_CAST && far_pointer(value_type(e->type)) &&
           far_pointer(value_type(e->left->type))) {
        e = e->left;
    }

    if (e->kind == EX_ADDRESS && e->left->kind == EX_DEREF)
        e = e->left->left;
    if (e->kind != EX_BINARY || e->op != '+')
        return NULL;

    base = e->left;

    if (base->kind != EX_OBJECT || !base->type.array || !base->type.banked || base->symbol->owner ||
        base->symbol->wram || width(pointed_type(value_type(base->type))) != 1 ||
        !row_word(e->right->type) || !e->right->type.is_unsigned)
        return NULL;

    *offset = e->right;
    return base->symbol;
}

static unsigned fixed_row_uses(Statement *s, Symbol *pointer)
{
    unsigned count = 0;

    for (; s; s = s->next) {
        uint32_t test;

        count +=
            expression_references(s->expression, pointer) + expression_references(s->step, pointer);
        count += fixed_row_uses(s->initial, pointer);

        if (s->kind == ST_IF && integer_constant(s->expression, &test) &&
            !statement_has_case(s->body) && !statement_has_case(s->alternate))
            count += fixed_row_uses(test ? s->body : s->alternate, pointer);
        else
            count += fixed_row_uses(s->body, pointer) + fixed_row_uses(s->alternate, pointer);
    }

    return count;
}

/* Bind consecutive private pointer initializers only across their following
 * conditional. The trial must account for every use of either pointer before
 * committing the offset representation. Other users keep real pointers. */
static Statement *fixed_word_row_region(Statement *s)
{
    Statement *second = s->next, *region, *next;
    Expr *source, *destination, *source_offset, *destination_offset = NULL;
    FixedWordRows fixed = {0};
    CodegenCheckpoint *saved;

    unsigned scale = 0, displacement = 0, source_uses, destination_uses;

    if (cg.fixed_rows || cg.parser->no_indexed_operands || cg.parser->no_body_optimizations ||
        cg.parser->no_strength_reduction || cg.stack_leaf || cg.function->symbol->interrupt ||
        !second || !(region = second->next) || region->kind != ST_IF)
        return NULL;

    source = plain_assignment(s);
    destination = plain_assignment(second);

    if (!source || !destination || !far_pointer(source->left->type) ||
        far_pointer(destination->left->type) || !destination->left->type.pointers ||
        volatile_expression(source) || volatile_expression(destination))
        return NULL;

    fixed.source = source->left->symbol;
    fixed.destination = destination->left->symbol;

    if (!loop_private(fixed.source) || !loop_private(fixed.destination) ||
        !(fixed.font = fixed_row_font(source->right, &source_offset)) ||
        !(fixed.buffer =
              indexed_near_base(destination->right, &destination_offset, &scale, &displacement)) ||
        !destination_offset || fixed.buffer->owner || !fixed.buffer->defined ||
        width(fixed.buffer->type) > 65535)
        return NULL;

    fixed.max_offset = fixed_row_max_offset(destination_offset, scale, displacement);
    source_uses = fixed_row_uses(cg.function->body, fixed.source);
    destination_uses = fixed_row_uses(cg.function->body, fixed.destination);

    if (source_uses < 3 || destination_uses < 3)
        return NULL;

    saved = malloc(sizeof *saved);

    if (!saved) {
        fputs("out of memory emitting word rows\n", stderr);
        exit(EXIT_FAILURE);
    }

    cg_checkpoint_save(saved);
    code("; fixed font and buffer offsets\n");
    emit_value(source_offset);
    code("    sta ");
    array_operand(fixed.source, 0);
    code("\n");
    emit_value(destination_offset);
    strength_scale(scale, destination_offset);
    strength_adjust(displacement);
    code("    sta ");
    array_operand(fixed.destination, 0);
    code("\n");
    cg.fixed_rows = &fixed;
    next = region->next;
    region->next = NULL;
    emit_statements(region);
    region->next = next;
    cg.fixed_rows = NULL;

    if (fixed.failed || fixed.source_uses + 1 != source_uses ||
        fixed.destination_uses + 1 != destination_uses) {
        cg_checkpoint_restore_length(saved);
        free(saved);
        return NULL;
    }

    free(saved);
    return region;
}
