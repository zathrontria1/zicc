// Shared state and core infrastructure for post-emission assembly line passes
// Owns per-function flags instead of storing them inside global cg

typedef struct {
    Parser *parser; // compiler flags, unit name, and symbol table
    int is_volatile; // 1 if the function contains volatile accesses
    int frame_address; // 1 if any local variable address can escape
    int word_result; // 1 if the return value fits in 16-bit A alone
    int value_result; // 1 if the function returns a value
    unsigned *label_counter; // points to the unit's next label id
    int *arithmetic_used; // set when a rewrite uses __arith_lhs/__arith_rhs
    const unsigned short *frame_map; // packed frame-slot map for this function
    char **assembly; // points to the unit's assembly text buffer
    size_t *length; // points to the active length of *assembly
} LpState;

static LpState lp_state;

// Bind the line-pass state to the current unit buffers and per-function flags
static void lp_bind_state(Parser *parser, unsigned *label_counter, int *arithmetic_used,
                          const unsigned short *frame_map, char **assembly, size_t *length,
                          int is_volatile, int frame_address, int word_result, int value_result)
{
    lp_state.parser = parser;
    lp_state.label_counter = label_counter;
    lp_state.arithmetic_used = arithmetic_used;
    lp_state.frame_map = frame_map;
    lp_state.assembly = assembly;
    lp_state.length = length;
    lp_state.is_volatile = is_volatile;
    lp_state.frame_address = frame_address;
    lp_state.word_result = word_result;
    lp_state.value_result = value_result;
}

static unsigned lp_next_label(void)
{
    return ++(*lp_state.label_counter);
}

static void lp_mark_arithmetic(void)
{
    *lp_state.arithmetic_used = 1;
}

/* Post-emission passes over one finished function's assembly lines. They run
 * after the frame passes and before relaxation, so branches are still
 * "bxx :+ / jmp .loword(cg_N) / :" sequences. A backward liveness analysis of
 * A, X, Y and the N/Z/C/V flags over the function's control flow decides
 * where an instruction's register or flag results are unobserved. Anything
 * the analysis does not model (unknown instructions, indirect transfers)
 * reads everything, so it only blocks rewrites. */
enum {
    LP_AL = 1,
    LP_AH = 2,
    LP_A = LP_AL | LP_AH,
    LP_X = 4,
    LP_Y = 8,
    LP_N = 16,
    LP_Z = 32,
    LP_C = 64,
    LP_V = 128,
    LP_FLAGS = LP_N | LP_Z | LP_C | LP_V,
    LP_ALL = 255
};

// One parsed line of assembly text and its liveness/edit metadata
typedef struct {
    const char *text; // raw line text inside the unit buffer
    size_t length; // line length excluding '\n'
    const char *op; // mnemonic start if this line is an instruction, else NULL
    int label; // 1 if this line defines a label
    int m8; // 1 if accumulator A is in 8-bit mode here
    int x8; // 1 if index registers X/Y are in 8-bit mode here
    int target; // destination line index for a local branch/jump, or -1
    int first_incoming; // head of linked list of lines jumping here, or -1
    int next_incoming; // next incoming jumper sharing the same target, or -1
    int ends; // 1 if control flow does not fall through to the next line
    int call; // 1 if this line is a call or tail call
    int indirect; // 1 if this line is an indirect jump
    int wrap_step; // 1 if preceded by a near-pointer wrap marker
    unsigned use; // bitmask of registers/flags read by this line
    unsigned def; // bitmask of registers/flags written by this line
    unsigned live; // bitmask live on entry to this line
    unsigned out; // bitmask live on exit from this line
    char *replace; // replacement line text staged by a pass, or NULL
    int deleted; // 1 if a pass marked this line for removal
    char *before; // extra text to insert right before this line, or NULL
} LpLine;

// Parsed assembly lines for one function body
typedef struct {
    char *text; // owned copy of the function's assembly text
    LpLine *lines; // array of parsed lines
    unsigned count; // number of entries in lines[]
    int indirect; // 1 if the function contains jump tables or indirect jumps
    int calls; // number of call / tail-call instructions
    int helpers; // 1 if any call targets an internal __helper or pointer
} LpUnit;

static int lp_is(const LpLine *l, const char *name)
{
    return l->op && op_is(l->op, name);
}

static int lp_line_is(const LpLine *l, const char *text)
{
    size_t n = strlen(text);

    return l->op && l->length == n + 4 && !strncmp(l->op, text, n);
}

/* Operand text after the mnemonic, and its length */
static const char *lp_operand(const LpLine *l, size_t *n)
{
    if (!l->op || l->length < 8 || l->op[3] != ' ') {
        *n = 0;
        return "";
    }

    *n = l->length - 8;
    return l->op + 4;
}

static int lp_operand_is(const LpLine *l, const char *text, size_t n)
{
    size_t m;
    const char *o = lp_operand(l, &m);

    return m == n && !strncmp(o, text, n);
}

static unsigned lp_index_use(const LpLine *l)
{
    size_t n;
    const char *o = lp_operand(l, &n);

    unsigned use = 0;

    if (n >= 2 && o[n - 2] == ',' && o[n - 1] == 'x')
        use |= LP_X;
    if (n >= 2 && o[n - 2] == ',' && o[n - 1] == 'y')
        use |= LP_Y;
    if (n >= 3 && o[0] == '(' && memchr(o, ',', n) && o[n - 1] == ')' && o[n - 2] == 'x')
        use |= LP_X;

    return use;
}

static void lp_effects(LpLine *l)
{
    static const char *const branches[] = {"bcc", "bcs", "beq", "bne", "bmi", "bpl", "bvc", "bvs"};

    static const unsigned reads[] = {LP_C, LP_C, LP_Z, LP_Z, LP_N, LP_N, LP_V, LP_V};
    const char *op = l->op;

    unsigned a = l->m8 ? LP_AL : LP_A, x = l->x8 ? 0 : LP_X, y = l->x8 ? 0 : LP_Y,
             idx = lp_index_use(l);
    size_t n;

    unsigned i;
    const char *operand = lp_operand(l, &n);
    int accumulator = !n || (n == 1 && operand[0] == 'a');

    l->use = LP_ALL;
    l->def = 0;
    l->target = -1;

    for (i = 0; i < 8; ++i) {
        if (op_is(op, branches[i])) {
            l->use = reads[i];
            return;
        }
    }

    if (op_is(op, "bra") || op_is(op, "brl")) {
        l->use = 0;
        l->ends = 1;
        return;
    }

    if (op_is(op, "jmp") || op_is(op, "jml")) {
        l->ends = 1;

        if (n && (operand[0] == '(' || operand[0] == '[')) {
            l->indirect = 1;
            l->use = LP_ALL;
            return;
        }

        l->use = 0;
        return; /* resolved as a label below, or a tail call */
    }

    /* A word result leaves X caller-clobbered */
    if (op_is(op, "rts") || op_is(op, "rtl")) {
        l->ends = 1;
        l->use = LP_Y | (lp_state.value_result ? (LP_A | (lp_state.word_result ? 0 : LP_X)) : 0);
        return;
    }
    if (op_is(op, "rti") || op_is(op, "brk") || op_is(op, "cop") || op_is(op, "stp") ||
        op_is(op, "wai")) {
        l->ends = op_is(op, "rti") || op_is(op, "stp");
        return;
    }

    /* Callees read A, X, Y (preserved) and no flags; their results stay
     * unmodelled, so nothing counts as defined. */
    if (op_is(op, "jsr") || op_is(op, "jsl")) {
        l->call = 1;
        l->use = LP_A | LP_X | LP_Y;
        return;
    }
    if (op_is(op, "lda")) {
        l->use = idx;
        l->def = a | LP_N | LP_Z;
        return;
    }
    if (op_is(op, "ldx")) {
        l->use = idx;
        l->def = x | LP_N | LP_Z;
        return;
    }
    if (op_is(op, "ldy")) {
        l->use = idx;
        l->def = y | LP_N | LP_Z;
        return;
    }
    if (op_is(op, "sta")) {
        l->use = a | idx;
        return;
    }
    if (op_is(op, "stx")) {
        l->use = LP_X | idx;
        return;
    }
    if (op_is(op, "sty")) {
        l->use = LP_Y | idx;
        return;
    }
    if (op_is(op, "stz")) {
        l->use = idx;
        return;
    }
    if (op_is(op, "adc") || op_is(op, "sbc")) {
        l->use = a | LP_C | idx;
        l->def = a | LP_FLAGS;
        return;
    }
    if (op_is(op, "and") || op_is(op, "ora") || op_is(op, "eor")) {
        l->use = a | idx;
        l->def = a | LP_N | LP_Z;
        return;
    }
    if (op_is(op, "cmp")) {
        l->use = a | idx;
        l->def = LP_N | LP_Z | LP_C;
        return;
    }
    if (op_is(op, "cpx")) {
        l->use = LP_X | idx;
        l->def = LP_N | LP_Z | LP_C;
        return;
    }
    if (op_is(op, "cpy")) {
        l->use = LP_Y | idx;
        l->def = LP_N | LP_Z | LP_C;
        return;
    }
    if (op_is(op, "bit")) {
        l->use = a | idx;
        l->def = LP_Z;
        return;
    }
    if (op_is(op, "inc") || op_is(op, "dec")) {
        l->use = accumulator ? a : idx;
        l->def = (accumulator ? a : 0) | LP_N | LP_Z;
        return;
    }
    if (op_is(op, "asl") || op_is(op, "lsr")) {
        l->use = accumulator ? a : idx;
        l->def = (accumulator ? a : 0) | LP_N | LP_Z | LP_C;
        return;
    }
    if (op_is(op, "rol") || op_is(op, "ror")) {
        l->use = (accumulator ? a : idx) | LP_C;
        l->def = (accumulator ? a : 0) | LP_N | LP_Z | LP_C;
        return;
    }
    if (op_is(op, "inx") || op_is(op, "dex")) {
        l->use = LP_X;
        l->def = x | LP_N | LP_Z;
        return;
    }
    if (op_is(op, "iny") || op_is(op, "dey")) {
        l->use = LP_Y;
        l->def = y | LP_N | LP_Z;
        return;
    }
    if (op_is(op, "tax")) {
        l->use = l->x8 ? LP_AL : LP_A;
        l->def = x | LP_N | LP_Z;
        return;
    }
    if (op_is(op, "tay")) {
        l->use = l->x8 ? LP_AL : LP_A;
        l->def = y | LP_N | LP_Z;
        return;
    }
    if (op_is(op, "txa")) {
        l->use = LP_X;
        l->def = a | LP_N | LP_Z;
        return;
    }
    if (op_is(op, "tya")) {
        l->use = LP_Y;
        l->def = a | LP_N | LP_Z;
        return;
    }
    if (op_is(op, "txy")) {
        l->use = LP_X;
        l->def = y | LP_N | LP_Z;
        return;
    }
    if (op_is(op, "tyx")) {
        l->use = LP_Y;
        l->def = x | LP_N | LP_Z;
        return;
    }
    if (op_is(op, "tsc") || op_is(op, "tdc")) {
        l->use = 0;
        l->def = LP_A | LP_N | LP_Z;
        return;
    }
    if (op_is(op, "tsx")) {
        l->use = 0;
        l->def = x | LP_N | LP_Z;
        return;
    }
    if (op_is(op, "tcs") || op_is(op, "tcd")) {
        l->use = LP_A;
        l->def = op[2] == 'd' ? LP_N | LP_Z : 0;
        return;
    }
    if (op_is(op, "txs")) {
        l->use = LP_X;
        return;
    }
    if (op_is(op, "xba")) {
        l->use = LP_A;
        l->def = LP_N | LP_Z;
        return;
    }
    if (op_is(op, "clc") || op_is(op, "sec")) {
        l->use = 0;
        l->def = LP_C;
        return;
    }
    if (op_is(op, "clv")) {
        l->use = 0;
        l->def = LP_V;
        return;
    }
    if (op_is(op, "nop")) {
        l->use = 0;
        return;
    }
    if (op_is(op, "pha")) {
        l->use = a;
        return;
    }
    if (op_is(op, "phx")) {
        l->use = LP_X;
        return;
    }
    if (op_is(op, "phy")) {
        l->use = LP_Y;
        return;
    }
    if (op_is(op, "pea") || op_is(op, "pei") || op_is(op, "phb") || op_is(op, "phd") ||
        op_is(op, "phk") || op_is(op, "per")) {
        l->use = 0;
        return;
    }
    if (op_is(op, "pla")) {
        l->use = 0;
        l->def = a | LP_N | LP_Z;
        return;
    }
    if (op_is(op, "plx")) {
        l->use = 0;
        l->def = x | LP_N | LP_Z;
        return;
    }
    if (op_is(op, "ply")) {
        l->use = 0;
        l->def = y | LP_N | LP_Z;
        return;
    }
    if (op_is(op, "plb") || op_is(op, "pld")) {
        l->use = 0;
        l->def = LP_N | LP_Z;
        return;
    }
    if (op_is(op, "php")) {
        l->use = LP_FLAGS;
        return;
    }
    if ((op_is(op, "rep") || op_is(op, "sep")) && n == 4 && !strncmp(operand, "#$20", 4)) {
        l->use = 0;
        return;
    }

    /* REP/SEP, PLP, block moves and anything else: reads everything */
}

static int lp_branch(const LpLine *l)
{
    static const char *const names[] = {"bcc", "bcs", "beq", "bne", "bmi",
                                        "bpl", "bvc", "bvs", "bra", "brl"};
    unsigned i;

    for (i = 0; i < 10; ++i) {
        if (lp_is(l, names[i]))
            return 1;
    }

    return 0;
}

static Symbol *lp_callee(const LpLine *call)
{
    size_t length;
    const char *name = lp_operand(call, &length);

    unsigned i;

    if (length > 9 && !strncmp(name, ".loword(", 8) && name[length - 1] == ')') {
        name += 8;
        length -= 9;
    }

    if (length < 2 || name[0] != '_' || name[1] == '_')
        return NULL;

    for (i = 0; i < lp_state.parser->symbol_count; ++i) {
        Symbol *s = &lp_state.parser->symbols[i];

        if (s->function && strlen(s->asm_name) == length - 1 &&
            !memcmp(name + 1, s->asm_name, length - 1))
            return s;
    }

    return NULL;
}

static unsigned lp_call_use(const LpLine *call)
{
    Symbol *callee = lp_callee(call);

    if (!callee || callee->variadic || callee->param_count < 0)
        return LP_A | LP_X | LP_Y;

    if (callee->old_style) {
        /* A visible K&R definition still has fixed incoming register homes */
        Function *body = inl.by_symbol[callee - lp_state.parser->symbols];

        if (!body || body->aggregate_abi || body->uses_varargs || callee->interrupt ||
            body_asm_statements(body->body))
            return LP_A | LP_X | LP_Y;
    }

    return LP_Y |
           (callee->param_count >= 1 && register_parameter(0, callee->params[0]) ? LP_X : 0) |
           (callee->param_count >= 2 && register_parameter(1, callee->params[1]) ? LP_A : 0);
}

static void lp_parse(LpUnit *u, const char *source, size_t length)
{
    const char *p;
    int m8 = 0, x8 = 0, wrap_step = 0;

    unsigned i, label_count = 0;
    AssemblyLabels labels;

    memset(u, 0, sizeof *u);
    u->text = malloc(length + 1);
    u->lines = malloc((length / 2 + 2) * sizeof *u->lines);

    if (!u->text || !u->lines) {
        fputs("out of memory emitting assembly\n", stderr);
        exit(EXIT_FAILURE);
    }

    memcpy(u->text, source, length);
    u->text[length] = 0;

    for (p = u->text; *p;) {
        const char *eol = strchr(p, '\n');
        LpLine *l = &u->lines[u->count++];

        if (!eol)
            eol = p + strlen(p);

        memset(l, 0, sizeof *l);
        l->text = p;
        l->length = (size_t)(eol - p);
        l->target = -1;
        l->first_incoming = l->next_incoming = -1;
        l->label = assembly_decode(p, l->length, &m8, &x8, &l->op);
        l->m8 = m8;
        l->x8 = x8;

        if (!strncmp(p, "; near pointer wrap\n", 20))
            wrap_step = 1;
        if (!l->op && !l->label && l->length && *p == '.' &&
            (!strncmp(p, ".word", 5) || !strncmp(p, ".addr", 5) || !strncmp(p, ".byte", 5) ||
             !strncmp(p, ".faraddr", 8)))
            u->indirect = 1;

        if (l->op) {
            l->wrap_step = wrap_step;
            wrap_step = 0;
        }

        if (l->label)
            ++label_count;

        p = *eol ? eol + 1 : eol;
    }

    assembly_labels_init(&labels, label_count);

    for (i = 0; i < u->count; ++i) {
        const LpLine *l = &u->lines[i];

        if (l->label)
            assembly_label_add(&labels, l->text, l->length, i);
    }

    for (i = 0; i < u->count; ++i) {
        LpLine *l = &u->lines[i];

        if (!l->op)
            continue;

        lp_effects(l);

        if (l->indirect)
            u->indirect = 1;
        if (l->call)
            ++u->calls;

        if (lp_branch(l) || op_is(l->op, "jmp") || op_is(l->op, "jml")) {
            size_t n;
            const char *name = lp_operand(l, &n);

            if (!l->indirect && n) {
                if (n > 9 && !strncmp(name, ".loword(", 8) && name[n - 1] == ')') {
                    name += 8;
                    n -= 9;
                }

                l->target = assembly_label_target(&labels, i, name, n);

                if (l->target < 0 && (op_is(l->op, "jmp") || op_is(l->op, "jml"))) {
                    /* A transfer out of the function: a tail call */
                    l->call = 1;
                    ++u->calls;
                    l->use = lp_call_use(l);

                    if (!strncmp(name, "__", 2))
                        u->helpers = 1;
                } else if (l->target < 0)
                    l->use = LP_ALL;
            }
        }

        if (op_is(l->op, "jsr") || op_is(l->op, "jsl")) {
            size_t n;
            const char *name = lp_operand(l, &n);

            l->use = lp_call_use(l);
            static const char stack_args[] = "; unprototyped stack arguments: ";

            if (i && u->lines[i - 1].length > sizeof stack_args - 1 &&
                !strncmp(u->lines[i - 1].text, stack_args, sizeof stack_args - 1)) {
                Symbol *callee = lp_callee(l);
                size_t name_length = u->lines[i - 1].length - (sizeof stack_args - 1);

                if (callee && callee->param_count < 0 && strlen(callee->asm_name) == name_length &&
                    !memcmp(u->lines[i - 1].text + sizeof stack_args - 1, callee->asm_name,
                            name_length))
                    l->use = LP_Y;
            }

            if (n > 8 && !strncmp(name, ".loword(", 8)) {
                name += 8;
            }

            if (!strncmp(name, "__", 2) || name[0] == '(' || name[0] == '[')
                u->helpers = 1;
        }
    }

    assembly_labels_free(&labels);

    for (i = u->count; i-- > 0;) {
        LpLine *l = &u->lines[i];

        if (l->target >= 0) {
            LpLine *target = &u->lines[l->target];

            l->next_incoming = target->first_incoming;
            target->first_incoming = (int)i;
        }
    }
}

static void lp_free_edits(LpUnit *u)
{
    unsigned i;

    for (i = 0; i < u->count; ++i) {
        free(u->lines[i].replace);
        free(u->lines[i].before);
    }
}

/* Backward liveness: live = registers and flags read before being written
 * from the start of the line; out = the same after it. */
static void lp_liveness(LpUnit *u)
{
    int changed = 1;

    unsigned i;

    for (i = 0; i < u->count; ++i) {
        u->lines[i].live = u->lines[i].out = 0;
    }

    while (changed) {
        changed = 0;

        for (i = u->count; i-- > 0;) {
            LpLine *l = &u->lines[i];

            unsigned out = 0, live;

            if (!l->op) {
                out = i + 1 < u->count ? u->lines[i + 1].live : LP_ALL;
                live = out;
            } else {
                if (!l->ends)
                    out |= i + 1 < u->count ? u->lines[i + 1].live : LP_ALL;
                if (l->target >= 0)
                    out |= u->lines[l->target].live;

                live = l->use | (out & ~l->def);
            }

            if (live != l->live || out != l->out) {
                l->live = live;
                l->out = out;
                changed = 1;
            }
        }
    }
}

/* Next or previous instruction past comments only; -1 at a label, directive or edge */
static int lp_next(const LpUnit *u, unsigned k, int direction)
{
    unsigned i = k;

    for (;;) {
        if (direction < 0) {
            if (!i)
                return -1;

            --i;
        } else if (++i >= u->count)
            return -1;

        if (!u->lines[i].length)
            return -1;
        if (u->lines[i].text[0] == ';')
            continue;

        return u->lines[i].op ? (int)i : -1;
    }
}

static void lp_set(LpLine *l, const char *format, ...)
{
    va_list args;
    int n;
    char *text;

    va_start(args, format);
    n = vsnprintf(NULL, 0, format, args);
    va_end(args);
    text = malloc((size_t)n + 1);

    if (!text) {
        fputs("out of memory emitting assembly\n", stderr);
        exit(EXIT_FAILURE);
    }

    va_start(args, format);
    vsnprintf(text, (size_t)n + 1, format, args);
    va_end(args);
    free(l->replace);
    l->replace = text;
    l->deleted = 0;
}

static void lp_insert(LpLine *l, const char *text)
{
    size_t old = l->before ? strlen(l->before) : 0, n = strlen(text);
    char *b = realloc(l->before, old + n + 1);

    if (!b) {
        fputs("out of memory emitting assembly\n", stderr);
        exit(EXIT_FAILURE);
    }

    memcpy(b + old, text, n + 1);
    l->before = b;
}

/* Write the edited lines back over the function's text */
static void lp_emit(LpUnit *u, size_t at)
{
    unsigned i;

    *lp_state.length = at;
    (*lp_state.assembly)[at] = 0;

    for (i = 0; i < u->count; ++i) {
        LpLine *l = &u->lines[i];

        if (l->before)
            code("%s", l->before);
        if (l->deleted)
            continue;
        if (l->replace) {
            code("%s\n", l->replace);
            continue;
        }
        if (i + 1 < u->count || l->length)
            code("%.*s\n", (int)l->length, l->text);
    }
}

/* Workspace words (scratch offset 2n) the text references: two bytes for
 * direct/near-indirect accesses and three bytes for far-indirect `[dp]`. */
static unsigned lp_text_words(const char *p, const char *end)
{
    unsigned taken = 0;
    const char *q;

    for (q = p; q < end; ++q) {
        if (end - q >= 11 && (!strncmp(q, "__arith_lhs", 11) || !strncmp(q, "__arith_rhs", 11))) {
            unsigned byte = q[8] == 'r' ? 4 : 0;
            unsigned bytes = (q > p && q[-1] == '[') ? 3u : 2u;
            q += 11;

            if (q < end && *q == '+')
                byte += (unsigned)strtoul(q + 1, (char **)&q, 10);

            dp_mark_width(&taken, byte, bytes);
            --q;
        } else if (*q == '$' && q > p && (q[-1] == ':' || q[-1] == '[' || q[-1] == '(') &&
                   end - q >= 3 && isxdigit((unsigned char)q[1]) && isxdigit((unsigned char)q[2]) &&
                   (end - q == 3 || !isxdigit((unsigned char)q[3])))
            dp_mark_width(&taken, (unsigned)strtoul(q + 1, NULL, 16) - 0xE0u,
                          (q > p && q[-1] == '[') ? 3u : 2u);
    }

    return taken;
}

/* A workspace word operand "z:__arith_lhs+N" / "z:__arith_rhs+N" as its byte
 * offset, or -1. */
static int lp_workspace_offset(const char *o, size_t n)
{
    unsigned byte;
    char *stop;

    if (n < 11 || strncmp(o, "__arith_", 8) ||
        (strncmp(o + 8, "lhs", 3) && strncmp(o + 8, "rhs", 3)))
        return -1;

    byte = o[8] == 'r' ? 4 : 0;

    if (n == 11)
        return (int)byte;
    if (o[11] != '+')
        return -1;

    byte += (unsigned)strtoul(o + 12, &stop, 10);

    if (stop != o + n || byte > 30)
        return -1;

    return (int)byte;
}

static int lp_workspace_word(const char *o, size_t n)
{
    return n > 2 && !strncmp(o, "z:", 2) ? lp_workspace_offset(o + 2, n - 2) : -1;
}

static int lp_workspace_pointer(const char *o, size_t n)
{
    return n > 2 && o[0] == '(' && o[n - 1] == ')' ? lp_workspace_offset(o + 1, n - 2) : -1;
}

static int lp_accumulator_memory(const LpLine *l)
{
    return lp_is(l, "lda") || lp_is(l, "sta") || lp_is(l, "adc") || lp_is(l, "sbc") ||
           lp_is(l, "and") || lp_is(l, "ora") || lp_is(l, "eor") || lp_is(l, "cmp");
}

/* Bytes a direct operand access covers: the register width, or four when unknown */
static int lp_width(const LpLine *l)
{
    static const char *const a_ops[] = {"lda", "sta", "adc", "sbc", "cmp", "and",
                                        "ora", "eor", "bit", "inc", "dec", "asl",
                                        "lsr", "rol", "ror", "stz", "tsb", "trb"};
    static const char *const x_ops[] = {"ldx", "stx", "cpx", "ldy", "sty", "cpy"};

    unsigned i;

    for (i = 0; i < sizeof a_ops / sizeof *a_ops; ++i) {
        if (lp_is(l, a_ops[i]))
            return l->m8 ? 1 : 2;
    }

    for (i = 0; i < sizeof x_ops / sizeof *x_ops; ++i) {
        if (lp_is(l, x_ops[i]))
            return l->x8 ? 1 : 2;
    }

    if (lp_is(l, "pei"))
        return 2;

    return 4;
}

static int lp_overlaps_n(const LpLine *l, int at, int word, int bytes)
{
    return at <= word + bytes - 1 && at + lp_width(l) - 1 >= word;
}

static int lp_overlaps(const LpLine *l, int at, int word)
{
    return lp_overlaps_n(l, at, word, 2);
}

static int lp_store_op(const LpLine *l)
{
    return lp_is(l, "sta") || lp_is(l, "stx") || lp_is(l, "sty") || lp_is(l, "stz") ||
           lp_is(l, "inc") || lp_is(l, "dec") || lp_is(l, "asl") || lp_is(l, "lsr") ||
           lp_is(l, "rol") || lp_is(l, "ror") || lp_is(l, "tsb") || lp_is(l, "trb");
}

/* The innermost loop around line k: a label h <= k that a branch b >= k jumps
 * back to, entered only by falling into h. Returns h and sets *back to the
 * last such branch, or -1. */
static int lp_loop(const LpUnit *u, unsigned k, unsigned *back)
{
    int h;

    for (h = (int)k; h >= 0; --h) {
        unsigned j, last = 0;
        int found = 0;

        if (!u->lines[h].label)
            continue;

        for (j = k; j < u->count; ++j) {
            if (u->lines[j].op && u->lines[j].target == h) {
                found = 1;
                last = j;
            }
        }

        if (!found)
            continue;

        *back = last;
        return h;
    }

    return -1;
}

/* Entries of the loop region [h, b]: falling into h's label group from above,
 * or unconditional jumps from outside to a label of that group. Each entry
 * gets a preheader copy: sites[] holds the lines to insert before. Any other
 * transfer from outside into the region rejects it. */
static int lp_entries(const LpUnit *u, unsigned h, unsigned b, unsigned *sites, unsigned *count)
{
    unsigned j, group = h, end = h;
    int prev;

    if (u->indirect)
        return 0;

    while (group > 0 && !u->lines[group - 1].op) {
        --group;
    }

    while (end + 1 < u->count && !u->lines[end + 1].op) {
        ++end;
    }

    *count = 0;
    for (j = 0; j < u->count; ++j) {
        const LpLine *l = &u->lines[j];

        if (!l->op || l->target < 0 || (j >= h && j <= b))
            continue;
        if ((unsigned)l->target < group || (unsigned)l->target > b)
            continue;
        if ((unsigned)l->target > end || !l->ends || lp_is(l, "jml") || *count == 8)
            return 0;

        sites[(*count)++] = j;
    }

    for (prev = (int)group - 1; prev >= 0 && !u->lines[prev].op; --prev) {
    }

    if (prev >= 0 && !u->lines[prev].ends) {
        if (*count == 8)
            return 0;

        sites[(*count)++] = group;
    }

    return *count > 0;
}

static int lp_region_writes(const LpUnit *u, unsigned h, unsigned b, const char *operand, size_t n,
                            int word)
{
    unsigned j;

    for (j = h; j <= b; ++j) {
        const LpLine *l = &u->lines[j];
        size_t m;
        const char *o;

        if (!l->op)
            continue;
        if (l->call || lp_is(l, "mvn") || lp_is(l, "mvp") ||
            (l->use == LP_ALL && !lp_is(l, "rep") && !lp_is(l, "sep")))
            return 1;

        o = lp_operand(l, &m);

        if (word >= 0) {
            int w = lp_workspace_word(o, m);

            if (w < 0 && lp_text_words(o, o + m) & (3u << (word / 2)))
                return 1; /* other spelling of the workspace */
            if (w >= 0 && lp_overlaps(l, w, word) && lp_store_op(l))
                return 1;
        } else if (m == n && !strncmp(o, operand, n) && lp_store_op(l))
            return 1;
    }

    return 0;
}

// Scratch cache for running line passes to a fixed point without re-parsing unchanged text
typedef struct {
    LpUnit parsed; // cached parse of the current assembly text
    LpLine *work; // scratch copy passed to each pass so rejected passes stay clean
    unsigned capacity; // allocated size of work[]
} LpRunner;

static void lp_invalidate(LpRunner *runner)
{
    free(runner->parsed.text);
    free(runner->parsed.lines);
    runner->parsed.text = NULL;
    runner->parsed.lines = NULL;
}

// Run one line pass up to 64 rounds until it stops changing the function; returns 1 if anything changed
static int lp_run(LpRunner *runner, Function *f, size_t at,
                  int (*pass)(LpUnit *, Function *, size_t))
{
    unsigned rounds;
    int any = 0;

    for (rounds = 0; rounds < 64; ++rounds) {
        LpUnit u;
        int changed;

        if (!runner->parsed.text) {
            lp_parse(&runner->parsed, *lp_state.assembly + at, *lp_state.length - at);
        }

        u = runner->parsed;

        if (runner->capacity < u.count) {
            free(runner->work);
            runner->work = allocate(u.count * sizeof *runner->work);
            runner->capacity = u.count;
        }

        // Rejected passes can change analysis fields as well as stage edits, so give each pass a fresh copy
        u.lines = runner->work;

        if (u.count) {
            memcpy(u.lines, runner->parsed.lines, u.count * sizeof *u.lines);
        }

        changed = pass(&u, f, at);

        if (changed) {
            lp_emit(&u, at);
        }

        lp_free_edits(&u);

        if (!changed) {
            break;
        }

        lp_invalidate(runner);
        any = 1;
    }

    return any;
}
