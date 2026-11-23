// Per-function optimization driver, frame layout, leaf dispatch, and interrupt scratch

#include "counted_reductions.inc"
#include "recursive_products.inc"
#include "bank_calls.inc"
#include "guarded_updates.inc"
#include "range_scans.inc"

/* Inspect complete emitted instructions, including operands assembled through
 * multiple code() calls. This covers selected inline paths and frame cleanup,
 * rather than predicting scratch use from the unselected expression tree. */
static unsigned interrupt_scratch_writes(size_t start)
{
    const char *line = cg.assembly + start;
    unsigned mask = cg.interrupt_scratch;

    while (*line) {
        char op[16], operand[192];
        const char *end = strchr(line, '\n');
        if (sscanf(line, " %15s %191[^\r\n]", op, operand) == 2 &&
            (!strcmp(op, "sta") || !strcmp(op, "stx") || !strcmp(op, "sty") || !strcmp(op, "stz") ||
             !strcmp(op, "inc") || !strcmp(op, "dec") || !strcmp(op, "asl") || !strcmp(op, "lsr") ||
             !strcmp(op, "rol") || !strcmp(op, "ror") || !strcmp(op, "trb") ||
             !strcmp(op, "tsb"))) {
            char *comment = strchr(operand, ';'), *symbol;
            if (comment)
                *comment = 0;
            symbol = operand;
            if (!strncmp(symbol, "z:", 2) || !strncmp(symbol, "a:", 2) || !strncmp(symbol, "f:", 2))
                symbol += 2;
            if (strncmp(symbol, "__arith_", 8))
                symbol = NULL;
            if (symbol) {
                char *suffix;
                unsigned base, offset = 0;
                if (!strncmp(symbol, "__arith_lhs", 11))
                    base = 0;
                else if (!strncmp(symbol, "__arith_rhs", 11))
                    base = 4;
                else
                    error_at(here(cg.parser), "unknown interrupt scratch operand '%s'", operand);
                suffix = symbol + 11;
                if (*suffix == '+') {
                    char *next;
                    unsigned long n;
                    int radix = 10;
                    ++suffix;
                    if (*suffix == '$') {
                        ++suffix;
                        radix = 16;
                    }
                    n = strtoul(suffix, &next, radix);
                    if (next == suffix || n > 30)
                        error_at(here(cg.parser), "invalid interrupt scratch offset");
                    offset = (unsigned)n;
                    suffix = next;
                }
                while (isspace((unsigned char)*suffix))
                    ++suffix;
                if ((*suffix && *suffix != ';') || base + offset > 30)
                    error_at(here(cg.parser), "unsupported interrupt scratch addressing '%s'",
                             operand);

                /* Scratch instructions use 16-bit A/X/Y. Include both words
                 * if a future unaligned access straddles a word boundary. */
                mask |= (1u << ((base + offset) / 2)) | (1u << ((base + offset + 1) / 2));
            }
        }
        if (!end) {
            break;
        }
        line = end + 1;
    }
    return mask;
}

static void insert_interrupt_scratch(size_t start, size_t save, size_t restore)
{
    unsigned mask = interrupt_scratch_writes(start);
    int word;
    size_t size = cg.length - save, middle = restore - save;
    char *tail;

    if (!mask)
        return;
    tail = allocate(size + 1);
    memcpy(tail, cg.assembly + save, size + 1);
    cg.length = save;
    cg.assembly[save] = 0;

    for (word = 0; word < 16; ++word)
        if (mask & (1u << word))
            code("    pei ($%02X)\n", DP_SCRATCH_BASE + word * 2);
    code("%.*s", (int)middle, tail);

    for (word = 15; word >= 0; --word)
        if (mask & (1u << word))
            code("    pla\n    sta z:$%02X\n", DP_SCRATCH_BASE + word * 2);
    code("%s", tail + middle);
    free(tail);
}

static unsigned stack_reservation_offset(unsigned offset, unsigned *holes, unsigned *bytes,
                                         unsigned count)
{
    unsigned i, result = offset;

    for (i = 0; i < count; ++i)
        if (holes[i] < offset)
            result -= bytes[i];
    return result;
}

/* Specialized leaves have already selected their independent ABI lowering.
 * Ordinary entry-cursor dependencies must be included before omitting an
 * incoming register value, even if the body overwrites it before any C read. */
static int parameter_entry_cursor(Symbol *v)
{
    unsigned i;

    for (i = 0; i < cg.cursor_count; ++i) {
        InductionCursor *c = &cg.cursors[i];
        if (!c->index->scope && parameter_incoming_live(c->index) &&
            (c->base == v || c->index == v))
            return 1;
    }
    return 0;
}

/* Backward may-liveness of a scalar value. A full plain write kills it;
 * reads and address formation generate it. Expression sequencing beyond such
 * writes remains conservative. Escapes after a definite write need a home,
 * but do not require the old incoming contents in that home. */
static int scalar_live_expr(Expr *e, Symbol *v, int after)
{
    if (!e)
        return after;
    if (e->kind == EX_ASSIGN && !e->op && e->left->kind == EX_OBJECT && e->left->symbol == v)
        return loop_mentions(e->right, v);
    return after || loop_mentions(e, v);
}

static unsigned scalar_live_budget;
static Statement *scalar_live_target;
static int scalar_live_captured, scalar_live_after;
static int body_private(Symbol *v);
static int body_address_pure(Expr *e);
static int body_has_deref(Expr *e);
static void body_drop_expr(Expr **at, Symbol *v);

static int scalar_live_statements(Statement *s, Symbol *v, int after, int breaking, int continuing,
                                  int rewrite)
{
    int next, head, body, step, again;

    if (!s)
        return after;
    if (!scalar_live_budget)
        return 1;
    --scalar_live_budget;
    next = scalar_live_statements(s->next, v, after, breaking, continuing, rewrite);
    if (s == scalar_live_target) {
        scalar_live_captured = 1;
        scalar_live_after |= next;
    }
    switch (s->kind) {
    case ST_SWITCH:
    case ST_CASE:
        return 1; /* Multiple entry labels: keep the input */
    case ST_EMPTY:
        return next;
    case ST_EXPR:
        if (rewrite && !next) {
            body_drop_expr(&s->expression, v);
            if (!s->expression)
                s->kind = ST_EMPTY;
        }
        return scalar_live_expr(s->expression, v, next);
    case ST_RETURN:
        return scalar_live_expr(s->expression, v, 0);
    case ST_BREAK:
        return breaking;
    case ST_CONTINUE:
        return continuing;
    case ST_BLOCK:
        return scalar_live_statements(s->body, v, next, breaking, continuing, rewrite);
    case ST_IF:
        body = scalar_live_statements(s->body, v, next, breaking, continuing, rewrite);
        step = scalar_live_statements(s->alternate, v, next, breaking, continuing, rewrite);
        return scalar_live_expr(s->expression, v, body || step);
    case ST_WHILE:
    case ST_FOR:
    case ST_DO:
        head = 0;
        do {
            again = head;
            if (s->kind == ST_DO) {
                step = scalar_live_expr(s->expression, v, next || head);
                body = scalar_live_statements(s->body, v, step, next, step, 0);
                head = body;
            } else {
                step = scalar_live_expr(s->step, v, head);
                body = scalar_live_statements(s->body, v, step, next, step, 0);
                head = scalar_live_expr(s->expression, v, next || body);
            }
        } while (head != again);
        if (rewrite && scalar_live_budget) {
            if (s->kind == ST_DO)
                step = scalar_live_expr(s->expression, v, next || head);
            else {
                if (!head)
                    body_drop_expr(&s->step, v);
                step = scalar_live_expr(s->step, v, head);
            }
            scalar_live_statements(s->body, v, step, next, step, 1);
        }
        return scalar_live_statements(s->initial, v, head, breaking, continuing, rewrite);
    }
    return 1;
}

/* Capture a private scalar's loop continuation during backward may-liveness,
 * including enclosing loop backedges and break/continue paths. */
static int dot_reserved_symbol(const Symbol *v);

static void region_home_liveness(Function *f, Statement *s, unsigned offset, int *in, int *out)
{
    unsigned i;
    Symbol *v = NULL;
    Statement single = *s;

    *in = *out = 1;
    if (cg.parser->no_private_regions || cg.parser->no_body_optimizations)
        return;

    for (i = 0; i < cg.parser->symbol_count; ++i) {
        Symbol *candidate = &cg.parser->symbols[i];
        if (candidate->owner == f->id && loop_private(candidate) &&
            !object_volatile(candidate->type) && !structure_object(candidate->type) &&
            !candidate->type.array && width(candidate->type) <= 4 &&
            (candidate->offset == offset ||
             (reg_width(candidate->type) == 4 && candidate->offset + 2 == offset))) {
            v = candidate;
            break;
        }
    }
    if (!v || dot_reserved_symbol(v))
        return;
    scalar_live_target = s;
    scalar_live_after = scalar_live_captured = 0;
    scalar_live_budget = 100000;
    scalar_live_statements(f->body, v, 0, 1, 1, 0);
    scalar_live_target = NULL;
    if (!scalar_live_captured || !scalar_live_budget)
        return;
    *out = scalar_live_after;
    single.next = NULL;
    scalar_live_budget = 100000;
    *in = scalar_live_statements(&single, v, *out, 1, 1, 0);
}

static int parameter_incoming_live(Symbol *v)
{
    scalar_live_budget = 4096;
    return scalar_live_statements(cg.function->body, v, 0, 1, 1, 0);
}

static unsigned plan_register_homes(Function *f)
{
    unsigned i, possible = 0;

    cg.register_homes = cg.register_spills = 0;

    for (i = 0; i < (unsigned)(f->symbol->param_count < 0 ? 0 : f->symbol->param_count); ++i) {
        Symbol *v = leaf_parameter(f, i);
        int cursor;
        if (!v)
            error_at(here(cg.parser), "internal parameter layout failure");
        if (!register_parameter(i, v->type))
            continue;
        possible |= 1u << i;
        cursor = parameter_entry_cursor(v);
        if (f->jump_label_count || object_volatile(v->type)) {
            cg.register_homes |= 1u << i;
            cg.register_spills |= 1u << i;
            continue;
        }
        if (!statement_references(f->body, v) && !cursor)
            continue;
        cg.register_homes |= 1u << i;
        if (cursor || parameter_incoming_live(v))
            cg.register_spills |= 1u << i;
    }
    return possible;
}

static unsigned compact_parameter_reservations(Function *f)
{
    /* Stack arguments retain their incoming homes. Unreferenced register
     * parameters need no storage; written/read parameters retain their homes. */
    Symbol *parameters[MAX_PARAMETERS];
    unsigned holes[MAX_PARAMETERS], bytes[MAX_PARAMETERS], count = 0, total = 0, stacked = 0, i, j;

    for (i = 0; i < (unsigned)(f->symbol->param_count < 0 ? 0 : f->symbol->param_count); ++i) {
        Symbol *v = leaf_parameter(f, i);
        if (!v)
            error_at(here(cg.parser), "internal parameter layout failure");
        if (register_parameter(i, v->type)) {
            if (cg.register_homes & (1u << i))
                continue;
            cg.omitted_parameters[cg.omitted_parameter_count++] = v;
        } else
            ++stacked;
        parameters[count] = v;
        holes[count] = v->offset;
        bytes[count] = (width(v->type) + 1) & ~1u;
        total += bytes[count++];
    }
    if (!count)
        return 0;

    for (i = 0; i < cg.parser->symbol_count; ++i) {
        Symbol *v = &cg.parser->symbols[i];
        if (v->owner != f->id)
            continue;
        for (j = 0; j < count; ++j)
            if (parameters[j] == v)
                break;
        v->offset = j < count ? 0 : stack_reservation_offset(v->offset, holes, bytes, count);
    }

    for (i = 0; i < cg.cursor_count; ++i)
        cg.cursors[i].offset = stack_reservation_offset(cg.cursors[i].offset, holes, bytes, count);

    for (i = 0; i < cg.affine_count; ++i)
        for (j = 0; j < cg.affine[i].count; ++j)
            cg.affine[i].accesses[j].offset =
                stack_reservation_offset(cg.affine[i].accesses[j].offset, holes, bytes, count);

    for (i = 0; i < divmod_state.count; ++i)
        divmod_state.entries[i].offset =
            stack_reservation_offset(divmod_state.entries[i].offset, holes, bytes, count);
    f->slots -= total;
    return stacked;
}

#include "scalar_values.inc"
#include "body_opt.inc"
#include "value_reuse.inc"
#include "known_values.inc"
#include "loop_fusion.inc"
static int function_uses_wide(Function *f);
#include "inline.inc"
#include "static_ipa.inc"
#include "value_recurrence.inc"
#include "dot_products.inc"
#include "dp_homes.inc"
#include "frame_packing.inc"
#include "byte_loop_regions.inc"

/* Recycle a consumed private DP home for an accumulated word value. A scalar
 * read here must be completely consumed on the left and dead afterward; a
 * previously consumed scalar must be dead on entry and exit. Continuations
 * include loop backedges. Pure operands cannot observe its replacement. */
static int dp_home_shared(unsigned word)
{
    unsigned i;
    unsigned char mapped;

    if (word >= dp_state.words || !dp_state.map[word])
        return 0;
    mapped = dp_state.map[word];

    for (i = 0; i < dp_state.words; ++i)
        if (i != word && dp_state.map[i] == mapped)
            return 1;
    return 0;
}

static Symbol *last_use_home_at(Expr *e, unsigned depth)
{
    Symbol *v, *found;
    int in, out;

    if (!e)
        return NULL;
    if (!depth && e->kind == EX_OBJECT) {
        v = e->symbol;
        if (!body_private(v) || dot_reserved_symbol(v) || v->owner != cg.function->id ||
            !v->offset || width(v->type) != 2 || !dp_state.map[(v->offset - 1) / 2] ||
            dp_home_shared((v->offset - 1) / 2) ||
            expression_references(loop_current->expression, v) != 1 ||
            !direct_operand(e, v->type, 0, 0))
            return NULL;
        region_home_liveness(cg.function, loop_current, v->offset, &in, &out);
        return out ? NULL : v;
    }
    if (!depth)
        return NULL;
    if ((found = last_use_home_at(e->left, depth - 1)))
        return found;
    if ((found = last_use_home_at(e->right, depth - 1)))
        return found;
    return last_use_home_at(e->third, depth - 1);
}

static Symbol *recent_dead_home(void)
{
    Symbol *best = NULL;
    size_t latest = 0, begin = cg.length > 4096 ? cg.length - 4096 : 0;
    unsigned i;

    for (i = 0; i < cg.parser->symbol_count; ++i) {
        Symbol *v = &cg.parser->symbols[i];
        char name[32];
        const char *p;
        size_t read = 0;
        int in, out;
        if (!body_private(v) || dot_reserved_symbol(v) || v->owner != cg.function->id ||
            !v->offset || width(v->type) != 2 || !dp_state.map[(v->offset - 1) / 2] ||
            dp_home_shared((v->offset - 1) / 2) ||
            expression_references(loop_current->expression, v))
            continue;
        snprintf(name, sizeof name, "__dp_home_%02u", dp_state.map[(v->offset - 1) / 2] - 1u);
        for (p = cg.assembly + begin; (p = strstr(p, name)) != NULL; ++p) {
            const char *line = p;
            while (line > cg.assembly && line[-1] != '\n')
                --line;
            if (!strncmp(line, "    lda ", 8) || !strncmp(line, "    ora ", 8) ||
                !strncmp(line, "    and ", 8) || !strncmp(line, "    eor ", 8) ||
                !strncmp(line, "    adc ", 8) || !strncmp(line, "    sbc ", 8))
                read = (size_t)(p - cg.assembly);
        }
        if (read <= latest)
            continue;
        region_home_liveness(cg.function, loop_current, v->offset, &in, &out);
        if (!in && !out) {
            best = v;
            latest = read;
        }
    }
    return best;
}

static int last_use_binary_home(Expr *left, Expr *right, int op, Type t)
{
    Symbol *home = NULL;
    Expr operand = {0};
    unsigned depth;

    if (cg.parser->no_body_optimizations || !dp_state.homes || !loop_current ||
        !loop_current->expression || t.pointers || t.base == TY_FLOAT || reg_width(t) != 2 ||
        (op != '+' && op != '&' && op != '|' && op != '^') || !indexed_pure(left) ||
        !indexed_pure(right))
        return 0;

    /* Prefer an already consumed home from the preceding expression. Its
     * last emitted read ranks candidates; IR liveness establishes safety. */
    home = recent_dead_home();

    for (depth = 0; depth < 16 && !home; ++depth)
        home = last_use_home_at(left, depth);
    if (!home)
        return 0;
    operand.kind = EX_OBJECT;
    operand.symbol = home;
    operand.type = home->type;
    if (!direct_operand(&operand, t, 0, 0))
        return 0;
    code("; last-use home accumulation: %s\n", home->name);
    convert_registers(value_type(left->type), t);
    store_symbol(home);
    emit_value(right);
    convert_registers(value_type(right->type), t);
    register_binary(op, t, &operand);
    return 1;
}

static void forward_rebuilt_record(Function *f)
{
    Type t = f->symbol->type;
    Statement *first, *s, *ret;
    Expr *result;
    Symbol *destination, *source = NULL;
    if (cg.parser->no_copy_selection || cg.parser->no_body_optimizations || !structure_object(t) ||
        t.structure->is_union || volatile_type(t) || f->jump_label_count)
        return;
    first = body_single(f->body);

    for (ret = first; ret && ret->kind != ST_RETURN; ret = ret->next) {
    }
    if (!ret || ret->next || !(result = ret->expression) || result->kind != EX_ASSIGN ||
        result->right->kind != EX_OBJECT)
        return;
    destination = result->right->symbol;
    if (destination->owner != f->id || !destination->scope || !destination->offset)
        return;
    s = first;

    for (Member *m = t.structure->members; m; m = m->next, s = s->next) {
        Expr *copy, *to, *from;
        while (s != ret && (s->kind == ST_EMPTY || (s->kind == ST_BLOCK && !s->body)))
            s = s->next;
        if (s == ret || s->kind != ST_EXPR || s->inline_callee || !(copy = s->expression) ||
            copy->kind != EX_ASSIGN || copy->op || m->bit_width || m->type.array)
            return;
        to = copy->left;
        from = copy->right;
        if (to->kind != EX_MEMBER || from->kind != EX_MEMBER || to->op != '.' || from->op != '.' ||
            to->value != m->offset || from->value != m->offset || to->left->kind != EX_OBJECT ||
            to->left->symbol != destination || from->left->kind != EX_OBJECT ||
            (source && source != from->left->symbol) ||
            !same_type(unqualified_value(from->left->type), unqualified_value(t)) ||
            volatile_expression(copy))
            return;
        source = from->left->symbol;
    }

    while (s != ret && (s->kind == ST_EMPTY || (s->kind == ST_BLOCK && !s->body)))
        s = s->next;
    if (s != ret || !source || source->owner != f->id || source->scope)
        return;

    /* Every field came from the same by-value argument. Return it directly */
    for (s = first; s != ret; s = s->next) {
        free_expression(s->expression);
        s->expression = NULL;
        s->kind = ST_EMPTY;
    }
    result->right->symbol = source;
    result->right->type = source->type;
    body_remove_local(f, destination);
}

static int literal_record_return(Function *f)
{
    Symbol *fn = f->symbol, *record;

    Type t = fn->type;
    Statement *parts[9];
    Expr *result;
    unsigned base, n = 0, size = width(t), expected = 0, written = 0;
    uint64_t packed = 0;
    if (cg.parser->no_copy_selection || !structure_object(t) || t.banked || t.structure->is_union ||
        volatile_type(t) || size < 2 || size > 8 || (size & 1) ||
        statement_inline_markers(f->body) || !reduction_statements(f->body, parts, &n, 9) ||
        n < 2 || parts[n - 1]->kind != ST_RETURN)
        return 0;
    result = parts[n - 1]->expression;
    if (!result || result->kind != EX_ASSIGN || volatile_expression(result->right))
        return 0;
    record = direct_memory_object(result->right, &base);
    if (!record || record->owner != f->id || !record->scope || !record->offset ||
        base > width(record->type) || size > width(record->type) - base)
        return 0;

    for (Member *m = t.structure->members; m; m = m->next) {
        unsigned bytes = width(m->type);
        if (m->bit_width || m->type.array || !bytes || m->offset + bytes > size)
            return 0;
        expected |= ((1u << bytes) - 1) << m->offset;
    }

    for (unsigned i = 0; i + 1 < n; ++i) {
        Expr *store = parts[i]->expression;
        unsigned offset, bytes, mask;
        uint32_t value;
        uint64_t bits;
        if (parts[i]->kind != ST_EXPR || !store || store->kind != EX_ASSIGN || store->op ||
            store->left->kind != EX_MEMBER || volatile_expression(store) ||
            fixed_memory_object(store->left, &offset) != record || offset < base ||
            !integer_constant(store->right, &value))
            return 0;
        offset -= base;
        bytes = width(store->left->type);
        if (!bytes || bytes > 4 || offset + bytes > size)
            return 0;
        mask = ((1u << bytes) - 1) << offset;
        if ((expected & mask) != mask)
            return 0;
        bits = (UINT64_C(1) << (8 * bytes)) - 1;
        packed = (packed & ~(bits << (8 * offset))) |
                 ((initializer_cast(value, store->left->type) & bits) << (8 * offset));
        written |= mask;
    }
    if (written != expected)
        return 0;

    /* The hidden result pointer is the first stack argument */
    code(".segment \"%s\"\n.export _%s\n_%s:\n; literal aggregate return\n", code_segment(),
         fn->asm_name, fn->asm_name);
    code("    lda %u,s\n    tax\n", 3u + cg.parser->long_return);

    for (unsigned offset = 0; offset < size; offset += 2) {
        unsigned word = (unsigned)(packed >> (8 * offset)) & 65535;
        if (word)
            code("    lda #$%04X\n    sta a:$%04X,x\n", word, offset);
        else
            code("    stz a:$%04X,x\n", offset);
    }
    code("    txa\n    rts\n__size_%s = * - _%s\n", fn->asm_name, fn->asm_name);
    f->frame = 0;
    return 1;
}

static void emit_function(Function *f)
{
    Symbol *s = f->symbol;

    cg.function = f;
    cg.loop_count = 0;
    cg.switch_depth = 0;
    int frame_base, stacked;
    unsigned possible_registers;
    size_t start = cg.length;
    cg.interrupt_scratch = 0;
    cg.dead_index_count = 0;
    cg.omitted_parameter_count = 0;
    memset(cg.frame_map, 0, sizeof cg.frame_map);
    cg.frame_saved = 0;
    forward_rebuilt_record(f);
    if (!cg.parser->no_body_optimizations && !cg.parser->no_strength_reduction &&
        !f->jump_label_count && !s->interrupt && !body_asm_statements(f->body) &&
        !find_symbol(cg.parser, "$basic_asm") && f->body->kind == ST_BLOCK)
        body_project_switch_strings(f->body->body);
    body_drop_unused_homes(f);
    if (!cg.parser->no_body_optimizations && !cg.parser->no_strength_reduction &&
        !cg.parser->no_loop_unroll && !f->jump_label_count && !body_asm_statements(f->body))
        body_drop_empty_loops(f->body);
    if (f->uses_wide && !s->interrupt && !cg.parser->no_body_optimizations &&
        !cg.parser->no_strength_reduction && !f->jump_label_count && !statement_has_case(f->body) &&
        !body_asm_statements(f->body)) {
        BodyFacts *facts = allocate(sizeof *facts);
        unsigned slots = f->slots;
        body_entry_values(f);
        scalar_refold(f->body);
        body_flow(f->body, facts);
        body_clear(facts);
        body_dead_locals(f);
        if (body_terminal_return_stores(f->body)) {
            body_flow(f->body, facts);
            body_clear(facts);
            body_dead_locals(f);
        }
        if (f->slots != slots) {
            body_flow(f->body, facts);
            body_clear(facts);
            body_drop_unused_homes(f);
        }
        free(facts);
        if (narrow_statements(f->body, 1))
            f->uses_wide = function_uses_wide(f);
    }
    if (!cg.parser->no_body_optimizations && !f->symbol->interrupt)
        body_simplify_branches(f->body, f->symbol->type);

    /* Unstructured entries prevent path-dependent liveness, but a private
     * scalar that is never read on any path still needs no frame slot. */
    if (f->jump_label_count && !f->uses_wide && !f->uses_varargs && !f->aggregate_abi &&
        !f->uses_bitfields && !s->interrupt && !cg.parser->no_body_optimizations &&
        !cg.parser->no_strength_reduction && !body_asm_statements(f->body) &&
        !find_symbol(cg.parser, "$basic_asm"))
        body_dead_locals(f);
    copy_prepare(f, f->body);
    if (f->uses_wide) {
        unsigned i;
        possible_registers = 0;
        cg.register_homes = cg.register_spills = 0;
        cg.cursor_count = cg.affine_count = divmod_state.count = divmod_state.available =
            lftr_state.count = 0;
        if (!f->jump_label_count && !f->uses_varargs && !f->aggregate_abi && !f->uses_bitfields)
            strength_prepare(f);
        for (i = 0; i < (unsigned)(s->param_count < 0 ? 0 : s->param_count); ++i)
            if (register_parameter(i, s->params[i]))
                possible_registers |= 1u << i;
        cg.register_homes = cg.register_spills = possible_registers;
        stacked = compact_parameter_reservations(f) != 0;
        f->frame = f->slots;
        emit_function_frame(f, stacked || f->slots != 0 || f->uses_varargs || f->aggregate_abi,
                            possible_registers, start);
        return;
    }
    if (f->jump_label_count || f->uses_varargs || f->aggregate_abi || f->uses_bitfields) {
        /* Labels can enter structured regions from outside. Variadic access
         * also needs a stable frame so the incoming cursor remains valid. */
        cg.cursor_count = cg.affine_count = divmod_state.count = divmod_state.available =
            lftr_state.count = 0;
        if (!f->jump_label_count && !s->interrupt && !cg.parser->no_body_optimizations &&
            !cg.parser->no_strength_reduction && !statement_has_case(f->body) &&
            !body_asm_statements(f->body) &&
            (f->aggregate_abi || f->uses_bitfields ||
             (f->uses_varargs && body_discarded_loads(f->body)))) {
            BodyFacts *facts = allocate(sizeof *facts);
            if (f->aggregate_abi)
                body_dead_locals(f);
            if (f->uses_bitfields)
                body_narrow_far_locals(f);
            body_flow(f->body, facts);
            body_clear(facts);
            free(facts);
            body_dead_locals(f);
            if (f->aggregate_abi) {
                body_drop_unused_homes(f);
                if (!cg.parser->no_loop_unroll && body_drop_empty_loops(f->body))
                    body_dead_locals(f);
            }
            if (literal_record_return(f))
                return;
        }
        possible_registers = plan_register_homes(f);
        stacked = compact_parameter_reservations(f) != 0;
        f->frame = f->slots + (reg_width(s->type) == 4 && f->slots > 4 ? 2 : 0);
        emit_function_frame(f, stacked || f->slots || f->uses_varargs || f->aggregate_abi,
                            possible_registers, start);
        return;
    }
    if (!s->interrupt && !volatile_statements(f->body) && !statement_inline_markers(f->body) &&
        (word_shift_scan_leaf(f) || range_scan_leaf(f) || guarded_update_leaf(f) ||
         guarded_byte_lookup_leaf(f) || counted_reduction(f)))
        return;
    scalar_propagate(f);
    body_optimize(f);
    if (!cg.parser->no_body_optimizations && !cg.parser->no_strength_reduction &&
        !cg.parser->no_value_reuse && !s->interrupt && !body_asm_statements(f->body))
        body_keep_clamps(f->body);
    if (!cg.parser->no_body_optimizations && !cg.parser->no_strength_reduction &&
        !cg.parser->no_loop_unroll && !s->interrupt && !body_asm_statements(f->body))
        body_split_xor_loops(f->body);
    loop_fusion_prepare(f);
    body_shared_selections(f);
    value_reuse_prepare(f);
    body_reuse_addresses(f);
    body_order_homes(f);
    value_recurrences_prepare(f);
    body_byte_ranges(f);
    if (!volatile_statements(f->body)) {
        forward_return(f, f->body);
    }
    f->frame = f->slots ? f->slots + 4 : 0;
    if (recursive_word_product(f))
        return;
    strength_prepare(f);
    affine_prepare(f);
    affine_prune_function_cursors(f);
    affine_compact_indices(f);
    lftr_prepare(f);
    divmod_prepare(f);
    known_prepare(f);
    dot_products_prepare(f);
    if (!s->interrupt && !volatile_statements(f->body) &&
        (statement_inline_markers(f->body)
             ? word_expression_leaf(f)
             : (far_loop_leaf(f) || predicate_loop_leaf(f) || indexed_loop_leaf(f) ||
                register_loop_leaf(f) || word_leaf(f) || word_expression_leaf(f) || wide_leaf(f) ||
                entry_cursor_leaf(f) || entry_cursor_nested_leaf(f))))
        return;
    if (scalar_leaf(f))
        return;

    /* Word results can survive stack restoration in caller-clobbered X.
     * Wide results keep X untouched and need only one saved word for A. */
    possible_registers = plan_register_homes(f);
    stacked = compact_parameter_reservations(f) != 0;
    frame_base = stacked || f->slots != 0;
    pack_private_frame(f);
    f->frame = f->slots - cg.frame_saved + (reg_width(s->type) == 4 && f->slots > 4 ? 2 : 0);
    if (lftr_state.count) {
        /* Speculative index elimination: any read or write of an eliminated
         * home re-emits the function with every index kept. */
        CodegenCheckpoint *saved = malloc(sizeof *saved);
        unsigned frame = f->frame;
        if (!saved) {
            fputs("out of memory emitting assembly\n", stderr);
            exit(EXIT_FAILURE);
        }
        cg_checkpoint_save(saved);
        lftr_state.active = 1;
        lftr_state.failed = 0;
        if (!(frame_base && dp_homes_function(f, possible_registers)))
            emit_function_frame(f, frame_base, possible_registers, start);
#ifdef LFTR_DRYRUN
        lftr_state.failed = 1;
#endif
        if (!lftr_state.failed) {
            lftr_state.active = 0;
            free(saved);
            return;
        }
        cg_checkpoint_restore(saved, start);
        free(saved);
        f->frame = frame;
        lftr_state.active = 0;
    }
    if (frame_base && dp_homes_function(f, possible_registers))
        return;
    emit_function_frame(f, frame_base, possible_registers, start);
}

static void emit_function_frame(Function *f, int frame_base, unsigned possible_registers,
                                size_t start)
{
    Symbol *s = f->symbol;
    Statement *body = f->body;
    unsigned i, stack_offset = structure_object(s->type) ? 2 : 0;
    size_t save = 0, restore = 0;

    cg.loop_count = 0;
    cg.switch_depth = f->jump_label_count != 0;
    cg.interrupt_scratch = 0;
    cg.jump_base = cg.label;
    cg.label += f->jump_label_count;
    code(".segment \"%s\"\n.export _%s\n_%s:\n", code_segment(), s->asm_name, s->asm_name);
    if (s->interrupt) {
        static const char *const names[] = {"", "nmi", "irq", "brk", "cop"};
        code(".export __vector_%s := _%s\n", names[s->interrupt], s->asm_name);
        if (s->interrupt == INT_NMI)
            code(".export __nmi_entry := _%s\n", s->asm_name);
        code("    jml interrupt_body_%s\ninterrupt_body_%s:\n", s->asm_name, s->asm_name);
        code("    rep #$30\n    pha\n    phx\n    phy\n    phd\n    pea $0000\n    pld\n    phb\n  "
             "  sep #$20\n.a8\n    lda #$7E\n    pha\n    plb\n    rep #$20\n.a16\n");
        if (f->uses_wide)
            code("    cld\n");
        save = cg.length;
    }
    if (body->kind == ST_BLOCK)
        body = body->body;
    if (!f->uses_wide && !f->jump_label_count && !f->uses_varargs && !f->aggregate_abi &&
        !f->uses_bitfields && !s->interrupt && !volatile_statements(f->body)) {
        entry_guard(f, &body);
        zero_argument_entry(f);
        zero_mask_entry(f);
    }
    dp_home_parameters(f);
    if (frame_base) {
        if (f->frame <= 4) {
            unsigned offset;
            Symbol *first = s->param_count > 0 ? leaf_parameter(f, 0) : NULL;
            code("    phy\n");

            /* Push high homes first. A holds parameter 1, X parameter 0;
             * unused homes may contain arbitrary values until initialized. */
            for (offset = f->frame; offset; offset -= 2)
                code("    %s\n", first && (cg.register_spills & 1) && first->offset == offset - 1
                                     ? "phx"
                                     : "pha");
            code("    tsc\n    tay\n");
        } else {
            if ((cg.register_spills & 2) && !dp_parameter_home(f, 1)) {
                cg.arithmetic = 1;
                code("    sta z:__arith_rhs\n");
            }
            code("    phy\n    tsc\n    sec\n    sbc #$%04X\n    tcs\n    tay\n", f->frame);
        }
        for (i = 0; i < (unsigned)(s->param_count < 0 ? 0 : s->param_count); ++i) {
            Symbol *v = NULL;
            unsigned j;
            for (j = 0; j < cg.parser->symbol_count; ++j)
                if (cg.parser->symbols[j].owner == f->id && cg.parser->symbols[j].scope == 0 &&
                    !strcmp(cg.parser->symbols[j].name, s->param_names[i])) {
                    v = &cg.parser->symbols[j];
                    break;
                }
            if (!v)
                error_at(here(cg.parser), "internal parameter layout failure");
            if (register_parameter(i, v->type)) {
                if (f->frame > 4 && (cg.register_spills & (1u << i)) && !dp_parameter_home(f, i)) {
                    if (!i)
                        code("    txa\n");
                    else
                        code("    lda z:__arith_rhs\n");
                    code("    sta %s\n", frame_operand(v->offset));
                }
            } else {
                /* Incoming stack arguments already are private writable homes.
                 * Address them in place instead of copying every word. */
                v->offset = dp_state.zero_stack ? dp_state.incoming_base + stack_offset
                                                : f->frame + cg.frame_saved + 5 + stack_offset +
                                                      cg.parser->long_return;
                stack_offset += argument_width(v->type);
            }
        }
    }
    if (cg.register_homes != possible_registers || cg.register_spills != possible_registers)
        code("; register entry: homes $%02X, spills $%02X\n", cg.register_homes,
             cg.register_spills);
    strength_parameters();
    if (emit_statements(body) &&
        (s->type.base != TY_VOID || s->type.pointers || !strcmp(s->name, "main")))
        code("    lda #0\n    ldx #0\n");
    code("return_%s = *\n", s->asm_name);
    if (frame_base) {
        if (f->frame <= 4) {
            unsigned offset;
            for (offset = 0; offset < f->frame; offset += 2)
                code("    %s\n", reg_width(s->type) == 4 ? "ply" : "plx");
            code("    ply\n");
        } else if (reg_width(s->type) == 4)
            code("    sta %s\n    tya\n    clc\n    adc #$%04X\n    tcs\n    pla\n    ply\n",
                 frame_operand(f->frame - 1), f->frame - 2);
        else
            code("    tax\n    tya\n    clc\n    adc #$%04X\n    tcs\n    txa\n    ply\n",
                 f->frame);
    }
    if (s->interrupt) {
        if (s->interrupt == INT_NMI) {
            code("__size_%s = * - _%s\n.segment \"NMI_END\"\n", s->asm_name, s->asm_name);
        }
        restore = cg.length;
        code("    plb\n    pld\n    ply\n    plx\n    pla\n    rti\n");
        if (s->interrupt != INT_NMI)
            code("__size_%s = * - _%s\n", s->asm_name, s->asm_name);
        insert_interrupt_scratch(start, save, restore);
    } else {
        if (!strcmp(s->name, "main"))
            code("    rtl\n");
        else
            code("    rts\n");
        code("__size_%s = * - _%s\n", s->asm_name, s->asm_name);
    }
}

/* A near call whose next instruction, past label-only lines, is RTS. With
 * nothing between them the callee takes no stack arguments and sees the same
 * registers, flags and workspace; its return then reaches our caller. */
