// Core codegen state, subsystem-owned state structs, speculative checkpoints,
// and assembly buffer/frame operand helpers

#define DP_SCRATCH_BASE 0x02

// Each call keeps its C locals in a stack frame; calls can overwrite arithmetic scratch space
typedef struct {
    Symbol *base;
    Symbol *index;
    unsigned scale;
    unsigned offset;
    int wram;
} InductionCursor;

typedef struct {
    Expr *address;
    unsigned offset;
    unsigned stride;
} AffineAccess;

typedef struct {
    Symbol *index;
    Expr *bound;
    int update_index;
    int recover_index;
    int wide;
    int countdown;
    int descending;
    int inclusive;
    int wrap_at_limit;
    int starts_zero;
    int bound_loaded;
    int entry_test;
} DpCounter;

typedef struct {
    unsigned factor;
    unsigned span;
    unsigned width;
    unsigned stride;
    unsigned bytes;
    unsigned cost;
    unsigned rolled;
    int known;
    int full;
    int hoist;
    DpCounter counter;
} UnrollPlan;

typedef struct {
    Statement *statement;
    Symbol *index;
    int delta;
    AffineAccess accesses[8];
    unsigned count;
    Symbol *dependencies[32];
    unsigned dependency_count;
    UnrollPlan unroll;
    int unroll_selected;
    int dead_index;
} AffineLoop;

typedef struct {
    Expr *expression;
    unsigned operations;
    unsigned offset;
    int reused;
    int survives_indirect;
} DivmodCache;

typedef struct {
    Symbol *source;
    Symbol *destination;
    Symbol *font;
    Symbol *buffer;
    unsigned source_uses;
    unsigned destination_uses;
    unsigned max_offset;
    int failed;
} FixedWordRows;

enum { MAX_DOT_TERMS = 8, MAX_DOT_PRODUCTS = 16, MAX_DOT_PACKS = 24 };

typedef struct {
    Expr *value_expr;
    Symbol *coeff_sym;
    Symbol *pack_sym;
    int negate;
} DotTerm;

typedef struct {
    Statement *loop;
    Expr *expr;
    Symbol *bias_sym;
    DotTerm terms[MAX_DOT_TERMS];
    unsigned term_count;
    int uses_x;
} DotProduct;

typedef struct {
    Statement *loop;
    Symbol *coeff_sym;
    Symbol *pack_sym;
    int negate;
    int swapped;
} DotPack;

enum { MAX_RETAINED_CURSORS = 4 };

typedef struct {
    Symbol *base;
    unsigned offset;
    unsigned scale;
    unsigned dp_word;
} RetainedCursor;

// State owned by divmod.inc (quotient/remainder reuse cache)
typedef struct {
    DivmodCache entries[16]; // active divmod pairs in the current function
    unsigned count; // number of entries in entries[]
    unsigned available; // bitmask of pairs valid at the current point
    Symbol *version; // cached symbol for 16-bit hardware divider
    int wide_version; // cached flag for 32-bit divider
} DivmodState;

// State owned by dot_products.inc (signed-byte dot-product strength reduction)
typedef struct {
    DotProduct dots[MAX_DOT_PRODUCTS]; // recognized dot products in the function
    unsigned count; // number of active dot products
    DotPack packs[MAX_DOT_PACKS]; // pre-packed coefficient tables
    unsigned pack_count; // number of active coefficient packs
} DotProductState;

// State owned by lftr.inc (speculative C index elimination)
typedef struct {
    Symbol *indices[8]; // candidate index variables to eliminate
    unsigned count; // number of candidates in indices[]
    int active; // 1 during a speculative LFTR emission trial
    int failed; // set to 1 if any eliminated home is touched
} LftrState;

// State owned by bound_cursors.inc (X-held register cursor trial)
typedef struct {
    InductionCursor *cursor; // active cursor bound to X, or NULL
    InductionCursor *pending; // cursor waiting to enter at the loop head
    unsigned delta; // constant displacement held in X (cursor + delta)
    unsigned mark_count; // number of own X-writing offsets recorded
    int failed; // 1 if the trial violated cursor invariants
    int own; // 1 while bound_cursors itself is emitting X ops
    int entered; // 1 once the trial loop entered the binding
    size_t start; // assembly byte offset where binding began
    size_t end; // assembly byte offset where binding ended
    size_t marks[128]; // assembly offsets of our own allowed X writes
} BoundCursorState;

// State owned by dp_homes.inc and region_homes.inc (direct-page home promotion)
typedef struct {
    int homes; // 1 while promoted DP homes are active
    int frameless; // 1 if the whole frame moved to DP
    int trial; // 1 during a weight-counting trial emission
    int failed; // 1 if an unsupported access rejected promotion
    int byte_operand; // 1 when a byte-offset operand may use DP
    unsigned words; // number of frame words tracked in map[]
    unsigned incoming_base; // incoming stack-arg base when zero_stack is set
    int zero_stack; // 1 when incoming args sit directly past saved Y
    unsigned char map[384]; // 1 + workspace word index for each frame word
    unsigned weight[384]; // weighted access count per frame word during trial
} DpHomeState;

// Core codegen state shared across expression, loop, and function emitters
typedef struct {
    Parser *parser;
    Function *function;
    unsigned label;
    unsigned inline_label;
    int arithmetic;
    int require_float_format;
    int require_int64_format;
    Symbol *retained_index;
    Symbol *retained_second;
    Symbol *retained_ptr;
    unsigned retained_scale;
    unsigned retained_limit;
    unsigned retained_second_scale;
    unsigned retained_bias;
    unsigned retained_unroll;
    int retained_y;
    int retained_scratch;
    int retained_failed;
    Symbol *scaled_ring_head;
    Symbol *scaled_ring_tail;
    unsigned scaled_ring_x_guards;
    unsigned scaled_ring_x_tests;
    RetainedCursor retained_cursors[MAX_RETAINED_CURSORS];
    unsigned retained_cursor_count;
    unsigned retained_cursor_mask;
    Symbol *numeric_index;
    Symbol *numeric_recurrence;
    unsigned numeric_limit;
    unsigned numeric_scale;
    unsigned numeric_offset;
    unsigned interrupt_scratch;
    const char *helpers[64];
    unsigned helper_count;
    unsigned loop_start[64];
    unsigned loop_end[64];
    unsigned loop_count;
    unsigned switch_depth;
    unsigned jump_base;
    InductionCursor cursors[32];
    unsigned cursor_count;
    AffineLoop affine[32];
    AffineLoop *affine_active;
    unsigned affine_count;
    Symbol *dead_indices[32];
    unsigned dead_index_count;
    Symbol *omitted_parameters[2];
    unsigned omitted_parameter_count;
    unsigned register_homes;
    unsigned register_spills;
    int stack_leaf;
    unsigned stack_bias;
    int loop_y_borrowed;
    Symbol *scaled_ring_indices[4];
    FixedWordRows *fixed_rows;
    Symbol *scalar_first;
    int scalar_leaf;
    int scalar_spill;
    Symbol *leaf_count;
    int near_strcmp;
    int need_smul8;
    int need_pack_coeff;
    Symbol *scan_cursor;
    int scan_failed;
    unsigned short frame_map[384];
    unsigned frame_saved;
    char *assembly;
    size_t length;
    size_t capacity;
} Codegen;

static Codegen cg;
static DivmodState divmod_state;
static DotProductState dot_state;
static LftrState lftr_state;
static BoundCursorState bound_state;
static DpHomeState dp_state;

// Snapshot of mutable codegen and subsystem states for speculative trial emission
typedef struct {
    Codegen cg; // core emitter state
    DivmodState divmod; // active divmod cache state
    LftrState lftr; // active index-elimination state
    BoundCursorState bound; // active register-cursor trial state
    DpHomeState dp; // active direct-page home state
} CodegenCheckpoint;

// Reset all unit-wide emitter and subsystem states before emitting a translation unit
static void cg_reset_program(Parser *p)
{
    memset(&cg, 0, sizeof cg);
    memset(&divmod_state, 0, sizeof divmod_state);
    memset(&dot_state, 0, sizeof dot_state);
    memset(&lftr_state, 0, sizeof lftr_state);
    memset(&bound_state, 0, sizeof bound_state);
    memset(&dp_state, 0, sizeof dp_state);
    cg.parser = p;
}

static void cg_checkpoint_save(CodegenCheckpoint *cp)
{
    cp->cg = cg;
    cp->divmod = divmod_state;
    cp->lftr = lftr_state;
    cp->bound = bound_state;
    cp->dp = dp_state;
}

// Restore a saved checkpoint while keeping the grown assembly buffer intact
static void cg_checkpoint_restore(const CodegenCheckpoint *cp, size_t start)
{
    char *assembly = cg.assembly;
    size_t capacity = cg.capacity;

    cg = cp->cg;
    cg.assembly = assembly;
    cg.capacity = capacity;
    cg.length = start;

    if (cg.assembly) {
        cg.assembly[start] = 0;
    }

    divmod_state = cp->divmod;
    lftr_state = cp->lftr;
    bound_state = cp->bound;
    dp_state = cp->dp;
}

static void cg_checkpoint_restore_length(const CodegenCheckpoint *cp)
{
    cg_checkpoint_restore(cp, cp->cg.length);
}

static int integer_constant(Expr *e, uint32_t *value);
static int parameter_incoming_live(Symbol *v);

/* The caller's automatic objects stay live while a callee runs. Once
 * their addresses can be observed, even a zero-argument call may read them
 * through a previously published pointer. Use a function-wide guard until
 * stack-pointer provenance is available at each individual call. */
static int automatic_designator(Expr *e)
{
    while (e && e->kind == EX_MEMBER && e->op != TOK_ARROW) {
        e = e->left;
    }

    return e && e->kind == EX_OBJECT && e->symbol->owner;
}

static int frame_address_expression(Expr *e)
{
    unsigned i;

    if (!e)
        return 0;

    /* A direct scalar field access does not publish the enclosing address */
    if (e->kind == EX_MEMBER && !e->type.array && !structure_object(e->type) &&
        automatic_designator(e))
        return 0;
    if (e->kind == EX_VA_START || e->kind == EX_RESULT_ADDR ||
        (e->kind == EX_ADDRESS && automatic_designator(e->left)) ||
        (e->kind == EX_OBJECT && e->symbol->owner &&
         (e->symbol->type.array || structure_object(e->symbol->type))))
        return 1;
    if (frame_address_expression(e->left) || frame_address_expression(e->right) ||
        frame_address_expression(e->third))
        return 1;

    for (i = 0; i < e->arg_count; ++i) {
        if (frame_address_expression(e->args[i]))
            return 1;
    }

    return 0;
}

static const char frame_address_marker[] = "; caller frame address visible\n";

static int frame_address_visible(Statement *s)
{
    for (; s; s = s->next) {
        if (frame_address_expression(s->expression) || frame_address_expression(s->step) ||
            frame_address_visible(s->initial) || frame_address_visible(s->body) ||
            frame_address_visible(s->alternate))
            return 1;
    }

    return 0;
}

static int loop_escapes(Statement *s, Symbol *symbol);
static int known_integer(Type t);
static int vr_immutable(Symbol *s);
static int body_private(Symbol *v);
static int body_equal(Expr *a, Expr *b);
static int body_address_pure(Expr *e);
static int body_has_deref(Expr *e);
static int mapped_word_home(Symbol *v);
static int structured_byte_loop(Statement *s);
static int fixed_byte_copy_loop(Statement *s);
static int counted_byte_copy_loop(Statement *s);
static int fixed_byte_sum_loop(Statement *s);
static int runtime_byte_sum_loop(Statement *s);
static int strided_byte_store_loop(Statement *s);
static int packed_byte_mask_loop(Statement *s);
static void known_prepare(Function *f);
static unsigned scalar_writes(Statement *s, Symbol *v);
static int dot_reserved_symbol(const Symbol *v);
static void region_home_liveness(Function *f, Statement *s, unsigned offset, int *in, int *out);
static DotProduct *dot_match_expr(Expr *e);
static int dot_indexed_byte(Expr *e, Symbol **base_out, Expr **idx_out, unsigned *off_out,
                            unsigned *scale_out, int *far_out);
static int dot_preserves_x(Expr *e);
static void dot_emit_loop_setup(Statement *s);
static int dot_emit_expr(Expr *e);
static void zicc_smul8_name(char *name, size_t size);
static void zicc_pack_coeff_name(char *name, size_t size);

static void require_frame_home(Symbol *s)
{
    unsigned i;

    if (s == cg.scan_cursor)
        cg.scan_failed = 1;
    if (s == cg.retained_index && (cg.retained_y == 1 || cg.retained_y == 2 || cg.retained_y == 4 ||
                                   (cg.retained_y == 5 && cg.retained_ptr)))
        cg.retained_failed = 1;

    for (i = 0; i < cg.dead_index_count; ++i) {
        if (cg.dead_indices[i] == s)
            error_at(here(cg.parser), "internal read/write of eliminated induction home '%s'",
                     s->name);
    }

    for (i = 0; i < cg.omitted_parameter_count; ++i) {
        if (cg.omitted_parameters[i] == s)
            error_at(here(cg.parser), "internal read/write of eliminated parameter home '%s'",
                     s->name);
    }
}

static void code(const char *format, ...)
{
    va_list args, copy;
    int n;
    char *buffer;

    va_start(args, format);
    va_copy(copy, args);
    n = vsnprintf(NULL, 0, format, args);
    va_end(args);

    if (n < 0) {
        va_end(copy);
        fputs("assembly formatting failed\n", stderr);
        exit(EXIT_FAILURE);
    }

    if (cg.length + (size_t)n + 1 > cg.capacity) {
        size_t capacity = cg.capacity ? cg.capacity : 4096;

        while (capacity < cg.length + (size_t)n + 1) {
            capacity *= 2;
        }

        buffer = realloc(cg.assembly, capacity);

        if (!buffer) {
            va_end(copy);
            fputs("out of memory emitting assembly\n", stderr);
            exit(EXIT_FAILURE);
        }

        cg.assembly = buffer;
        cg.capacity = capacity;
    }

    vsnprintf(cg.assembly + cg.length, cg.capacity - cg.length, format, copy);
    va_end(copy);
    cg.length += (size_t)n;
}

static void inline_marker(Statement *s)
{
    if (!s->inline_callee)
        return;

    unsigned id = ++cg.inline_label;
    code("; inlined call: %s %s\n.export __inlined_%s_%u_%s\n__inlined_%s_%u_%s:\n",
         cg.function->symbol->asm_name, s->inline_callee->asm_name, cg.parser->unit, id,
         s->inline_callee->asm_name, cg.parser->unit, id, s->inline_callee->asm_name);
}

static int statement_inline_markers(Statement *s)
{
    for (; s; s = s->next) {
        if (s->inline_callee || statement_inline_markers(s->body) ||
            statement_inline_markers(s->alternate) || statement_inline_markers(s->initial)) {
            return 1;
        }
    }

    return 0;
}

/* Operand text for the general path's frame byte at offset. Every Y-relative
 * frame access is formatted here so individual slots can later be relocated
 * without touching emitters. Rotating buffers allow several per call. */
static unsigned frame_offset(unsigned offset)
{
    unsigned word = (offset - 1) / 2;

    if (offset > cg.function->slots)
        return offset - cg.frame_saved;
    if (offset && word < 384 && cg.frame_map[word])
        return cg.frame_map[word] + ((offset - 1) & 1);

    return offset;
}

static const char *frame_operand(unsigned offset)
{
    static char buffers[8][24];

    static unsigned next;
    char *text = buffers[next++ & 7];

    unsigned word;

    if (cg.retained_index &&
        (cg.retained_y == 1 || cg.retained_y == 2 || cg.retained_y == 4 ||
         (cg.retained_y == 5 && cg.retained_ptr)) &&
        offset >= cg.retained_index->offset && offset < cg.retained_index->offset + 2)
        cg.retained_failed = 1;

    if (dp_state.homes && dp_state.zero_stack && offset >= dp_state.incoming_base) {
        if (cg.loop_y_borrowed)
            dp_state.failed = 1;

        snprintf(text, sizeof buffers[0], "a:$%04X,y",
                 offset - dp_state.incoming_base + 5 + cg.parser->long_return);
        return text;
    }

    if (bound_state.cursor && !bound_state.own && offset == bound_state.cursor->offset)
        bound_state.failed = 1;

    if (lftr_state.active) {
        unsigned k;

        for (k = 0; k < lftr_state.count; ++k) {
            if (offset >= lftr_state.indices[k]->offset &&
                offset <= lftr_state.indices[k]->offset + 1)
                lftr_state.failed = 1;
        }
    }

    word = offset ? (offset - 1) / 2 : 0;

    if ((dp_state.trial) && offset && word < 384) {
        unsigned depth = cg.loop_count < 4 ? cg.loop_count : 4;
        dp_state.weight[word] += 1u << (3 * depth);
    }

    if (dp_state.homes) {
        /* A promoted word is spelled as a placeholder until the function is
         * validated, so the workspace scan can tell homes from other uses. */
        if (offset && word < dp_state.words && dp_state.map[word] &&
            (!((offset - 1) & 1) || dp_state.byte_operand)) {
            snprintf(text, sizeof buffers[0], "z:__dp_home_%02u%s", dp_state.map[word] - 1u,
                     (offset - 1) & 1 ? "+1" : "");
            return text;
        }
        if (dp_state.frameless || (offset && word < dp_state.words && dp_state.map[word]))
            dp_state.failed = 1;
    }

    if (cg.loop_y_borrowed)
        dp_state.failed = 1;

    offset = frame_offset(offset);
    snprintf(text, sizeof buffers[0], "a:$%04X,y", offset);
    return text;
}

static int affine_pointer(Expr *e, int in_x);

/* The build driver supplies cross-bank public entries before relaxation */
static void call_entry(const char *name)
{
    const char *p = cg.parser->long_calls;
    int far = cg.parser->long_return || !strcmp(name, "_main");
    size_t n = strlen(name);

    if (cg.parser->source_lto && name[0] == '_') {
        Function *f;

        for (f = cg.parser->functions; f; f = f->next) {
            if (!strcmp(f->symbol->asm_name, name + 1) && !f->symbol->inline_omit &&
                (!f->symbol->inline_hint || f->symbol->internal || f->symbol->inline_external)) {
                p = NULL;
                break;
            }
        }
    }

    while (p && *p) {
        const char *end = strchr(p, ',');
        size_t length = end ? (size_t)(end - p) : strlen(p);

        if (length == n && !strncmp(p, name, n))
            far = 1;

        p = end ? end + 1 : NULL;
    }

    if (far)
        code("    jsl %s\n", name);
    else
        code("    jsr .loword(%s)\n", name);
}

static void helper(const char *name)
{
    if (cg.function && cg.function->symbol->interrupt) {
        /* Word bits are relative to the scratch base. Helper contracts are audited against
         * the assembly modules by tests/check-interrupt-scratch.py. */
        static const struct {
            const char *name;

            unsigned writes;
            const char *entry;
        } safe[] = {{"__ucmp16", 0},
                    {"__scmp16", 0},
                    {"__ucmp32", 0},
                    {"__scmp32", 0},
                    {"__shl32", 3},
                    {"__ushr32", 3},
                    {"__sshr32", 3},
                    {"__ucmp64", 0},
                    {"__scmp64", 0},
                    {"__shl64", 0x000f},
                    {"__ushr64", 0x000f},
                    {"__sshr64", 0x000f},
                    {"__mul64", 0x0fff, "__mul64_soft"},
                    {"__uquot64", 0x1f0f, "__udiv64_soft"},
                    {"__umod64", 0x1f0f, "__umod64_soft"},
                    {"__sdiv64", 0x1fff, "__sdiv64_soft"},
                    {"__smod64", 0x1fff, "__smod64_soft"},
                    {"__dcmp", 0},
                    {"__dcmp_signal", 0},
                    {"__dneg", 0x0008},
                    {"__dadd", 0x3fff},
                    {"__dsub", 0x3fff},
                    {"__dmul", 0x1fff, "__dmul_soft"},
                    {"__ddiv", 0x7fff, "__ddiv_soft"},
                    {"__fext32_64", 0x01ff},
                    {"__ftrunc64_32", 0x0ff3},
                    {"__sfloat64_32", 0x00ff},
                    {"__ufloat64_32", 0x00ff},
                    {"__sfloat64_64", 0x003f},
                    {"__ufloat64_64", 0x003f},
                    {"__sfloat32_64", 0x007f},
                    {"__ufloat32_64", 0x007f},
                    {"__fix64_32", 0x0073},
                    {"__ufix64_32", 0x0073},
                    {"__fix64_64", 0x001f},
                    {"__ufix64_64", 0x001f}};

        unsigned i;

        for (i = 0; i < sizeof safe / sizeof *safe; ++i) {
            if (!strcmp(name, safe[i].name))
                break;
        }

        if (i == sizeof safe / sizeof *safe)
            error_at(here(cg.parser), "interrupt handler requires unsafe arithmetic helper '%s'",
                     name);

        cg.interrupt_scratch |= safe[i].writes;

        if (safe[i].entry)
            name = safe[i].entry;
    }

    unsigned i;
    cg.arithmetic = 1;

    for (i = 0; i < cg.helper_count; ++i) {
        if (!strcmp(cg.helpers[i], name))
            break;
    }

    if (i == cg.helper_count)
        cg.helpers[cg.helper_count++] = name;

    call_entry(name);
}

static const char *code_segment(void)
{
    return cg.function && cg.function->symbol->interrupt == INT_NMI ? "NMI_USER" : "CODE";
}

static void label(unsigned id)
{
    code("cg_%s_%u = *\n", cg.parser->unit, id);
}

static void jump(unsigned id)
{
    code("    jmp .loword(cg_%s_%u)\n", cg.parser->unit, id);
}

static void push_value(Type t)
{
    if (reg_width(t) == 4)
        code("    phx\n");

    code("    pha\n");

    if (cg.stack_leaf)
        cg.stack_bias += reg_width(t);
}

static void pop_value(Type t)
{
    code("    pla\n");

    if (reg_width(t) == 4)
        code("    plx\n");
    if (cg.stack_leaf)
        cg.stack_bias -= reg_width(t);
}
