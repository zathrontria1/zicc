// Post-emission text sweeps, near relocations, and Y-frame to S-relative conversion

static int tail_call(const char *p)
{
    int adjacent = 1;

    p = strchr(p, '\n');

    while (p && *++p) {
        const char *eol = strchr(p, '\n');
        size_t n = eol ? (size_t)(eol - p) : strlen(p);
        if (n == 7 && !strncmp(p, "    rts", 7))
            return adjacent && eol ? 2 : 1;
        adjacent = 0;
        if (!eol || !n || *p == ' ' || *p == ';' || *p == '.')
            return 0;

        /* Labels: "name:" or "name = *" */
        if (!((p[n - 1] == ':' && !memchr(p, ' ', n)) || (n > 4 && !strncmp(p + n - 4, " = *", 4))))
            return 0;
        p = eol;
    }
    return 0;
}

/* Materialize copy data after the function's return, in its code segment.
 * Until then the assembly passes only see the copy instructions. */
static void emit_block_copy_payloads(size_t at)
{
    static const char marker[] = "; block copy payload ";
    const char *start = cg.assembly + at, *p = strstr(start, marker);
    char *payloads;

    if (!p)
        return;
    payloads = allocate(strlen(p) + 1);
    strcpy(payloads, p);

    for (p = payloads; p; p = strstr(p, marker)) {
        char *bytes;
        unsigned id = (unsigned)strtoul(p + sizeof marker - 1, &bytes, 10);
        code("cg_%s_%u_data:\n", cg.parser->unit, id);
        for (++bytes; *bytes != '\n'; bytes += 2)
            code("    .byte $%.2s\n", bytes);
        p = bytes;
    }
    free(payloads);
}

static void near_relocations(void)
{
    char *original = cg.assembly;
    const char *p = original;
    int tail, frame_visible = 0;

    cg.assembly = NULL;
    cg.length = cg.capacity = 0;

    while (*p) {
        if (p == original || p[-1] == '\n') {
            if (!strncmp(p, "; allocation function ", sizeof "; allocation function " - 1))
                frame_visible = 0;
            if (!strncmp(p, frame_address_marker, sizeof frame_address_marker - 1))
                frame_visible = 1;
        }
        if (!frame_visible && !cg.parser->long_return && (p == original || p[-1] == '\n') &&
            !strncmp(p, "    jsr ", 8) && p[8] != '(' && (tail = tail_call(p)) != 0) {
            /* The callee's RTS returns straight to our caller. An adjacent RTS
             * is unreachable afterwards; one behind a label stays a target. */
            const char *eol = strchr(p, '\n');
            code("    jmp%.*s\n", (int)(eol - p - 7), p + 7);
            p = eol + 1;
            if (tail == 2)
                p += 8;
        } else if (cg.parser->long_return && !strncmp(p, "    rts\n", 8)) {
            code("    rtl\n");
            p += 8;
        } else if (!strncmp(p, "a:_", 3)) {
            const char *end = p + 2;
            while (*end && *end != ',' && *end != '\n' && !isspace((unsigned char)*end))
                ++end;
            code("a:.loword(%.*s)", (int)(end - p - 2), p + 2);
            p = end;
        } else {
            code("%c", *p);
            ++p;
        }
    }
    free(original);
}

/* Instruction mnemonic of an assembly line, or NULL for a comment, label or
 * directive. */
static const char *reload_op(const char *line, const char *eol)
{
    if (eol - line < 5 || strncmp(line, "    ", 4) || line[4] == ';' || line[4] == ' ')
        return NULL;
    return line + 4;
}

/* N/Z after a removed reload: 1 if they are written before being read, 0 if
 * something may read them (branches, calls, returns, labels, flag pushes). */
static int reload_flags_dead(const char *p)
{
    static const char *const writers[] = {"lda", "ldx", "ldy", "cmp", "cpx", "cpy", "and", "ora",
                                          "eor", "adc", "sbc", "tax", "tay", "txa", "tya", "tsx",
                                          "tdc", "tcd", "xba", "inc", "dec", "inx", "dex", "iny",
                                          "dey", "asl", "lsr", "rol", "ror", "pla", "plx", "ply"};
    static const char *const neutral[] = {"sta", "stx", "sty", "stz", "pha", "phx", "phy",
                                          "phb", "phd", "clc", "sec", "nop", "tcs", "txs"};

    while (*p) {
        const char *eol = strchr(p, '\n'), *op;
        unsigned i;
        if (!eol)
            return 0;
        if (*p == ';') {
            p = eol + 1;
            continue;
        }
        if (*p == '.' && (!strncmp(p, ".a8\n", 4) || !strncmp(p, ".a16\n", 5) ||
                          !strncmp(p, ".i8\n", 4) || !strncmp(p, ".i16\n", 5))) {
            p = eol + 1;
            continue;
        }
        if (!(op = reload_op(p, eol)))
            return 0;
        for (i = 0; i < sizeof writers / sizeof *writers; ++i)
            if (!strncmp(op, writers[i], 3) && (op[3] == ' ' || op[3] == '\n'))
                return 1;
        for (i = 0; i < sizeof neutral / sizeof *neutral; ++i)
            if (!strncmp(op, neutral[i], 3) && (op[3] == ' ' || op[3] == '\n'))
                break;
        if (i == sizeof neutral / sizeof *neutral) {
            /* REP/SEP leave N/Z alone unless they name those status bits */
            if ((!strncmp(op, "rep #$", 6) || !strncmp(op, "sep #$", 6)) &&
                !(strtoul(op + 6, NULL, 16) & 0x82u)) {
                p = eol + 1;
                continue;
            }
            return 0;
        }
        p = eol + 1;
    }
    return 0;
}

/* Drop "lda X" after "sta X" with only comments between: A still holds the
 * stored value. X is restricted to private, non-volatile storage (frame and
 * stack slots, arithmetic scratch) and the load's N/Z must be dead. */
static void drop_reloads(size_t at)
{
    char *p = cg.assembly + at, *w = p;

    while (*p) {
        char *eol = strchr(p, '\n'), *next, *q;
        size_t n;
        if (!eol)
            break;
        n = (size_t)(eol - p);
        if (n > 8 && !strncmp(p, "    sta ", 8) &&
            ((n > 10 && !strncmp(p + n - 2, ",y", 2) && !strncmp(p + 8, "a:$", 3)) ||
             !strncmp(p + n - 2, ",s", 2) || !strncmp(p + 8, "z:__arith_", 10))) {
            q = eol + 1;
            while (*q == ';' && (next = strchr(q, '\n')))
                q = next + 1;
            next = strchr(q, '\n');
            if (next && (size_t)(next - q) == n && !strncmp(q, "    lda ", 8) &&
                !strncmp(q + 8, p + 8, n - 8) && reload_flags_dead(next + 1)) {
                /* Keep the store and the comments; skip the load */
                size_t keep = (size_t)(q - p);
                memmove(w, p, keep);
                w += keep;
                p = next + 1;
                continue;
            }
        }
        memmove(w, p, n + 1);
        w += n + 1;
        p = eol + 1;
    }
    {
        size_t rest = strlen(p);
        memmove(w, p, rest + 1);
        w += rest;
    }
    cg.length = (size_t)(w - cg.assembly);
}

static int op_is(const char *op, const char *name)
{
    return !strncmp(op, name, 3) && (op[3] == ' ' || op[3] == '\n');
}

/* Accumulator effect of one instruction inside a PHA/PLA window: 0 leaves A
 * alone, 1 overwrites A, -1 is not allowed in a window (stack, control,
 * width or block-move effects). */
static int window_effect(const char *op, const char *end)
{
    static const char *const keep[] = {"ldx", "ldy", "stx", "sty", "sta", "stz", "tax",
                                       "tay", "txy", "tyx", "inx", "dex", "iny", "dey",
                                       "cpx", "cpy", "cmp", "clc", "sec", "bit"};
    static const char *const write[] = {"lda", "txa", "tya", "adc", "sbc",
                                        "and", "ora", "eor", "xba"};
    static const char *const shifts[] = {"asl", "lsr", "rol", "ror", "inc", "dec"};
    const char *comma;
    unsigned i;

    for (comma = op; comma < end;) {
        comma = memchr(comma, ',', (size_t)(end - comma));
        if (!comma)
            break;
        if (++comma < end && *comma == 's')
            return -1;
    }

    for (i = 0; i < sizeof keep / sizeof *keep; ++i)
        if (op_is(op, keep[i]))
            return 0;

    for (i = 0; i < sizeof write / sizeof *write; ++i)
        if (op_is(op, write[i]))
            return 1;

    for (i = 0; i < sizeof shifts / sizeof *shifts; ++i)
        if (op_is(op, shifts[i]))
            return op[3] == '\n' || !strncmp(op + 3, " a\n", 3);
    return -1;
}

/* Remove PHA ... PLA when the window cannot observe the stack and either
 * preserves A or A is overwritten (without being read) right after PLA. The
 * PLA's N/Z must be dead too; calls count as overwriting them because no
 * callee reads its entry flags. */
static void drop_push_pairs(size_t at)
{
    char *p = cg.assembly + at, *w = p;

    while (*p) {
        char *eol = strchr(p, '\n');
        if (!eol)
            break;
        if (!strncmp(p, "    pha\n", 8)) {
            char *q = eol + 1, *pull = NULL, *after;
            int writes = 0, ok = 1;
            while (*q && ok) {
                char *end = strchr(q, '\n');
                const char *op;
                int effect;
                if (!end) {
                    ok = 0;
                    break;
                }
                if (*q == ';') {
                    q = end + 1;
                    continue;
                }
                if (!(op = reload_op(q, end))) {
                    ok = 0;
                    break;
                }
                if (!strncmp(q, "    pla\n", 8)) {
                    pull = q;
                    break;
                }
                effect = window_effect(op, end);
                if (effect < 0)
                    ok = 0;
                else
                    writes |= effect;
                q = end + 1;
            }
            if (ok && pull) {
                const char *next = pull + 8, *op = NULL;
                while (*next == ';') {
                    const char *end = strchr(next, '\n');
                    if (!end)
                        break;
                    next = end + 1;
                }
                {
                    const char *end = strchr(next, '\n');
                    if (end)
                        op = reload_op(next, end);
                }
                after = (char *)next;
                if (op && (op_is(op, "jsr") || op_is(op, "jsl")) && !writes)
                    ok = 1;
                else if (op && (op_is(op, "lda") || op_is(op, "txa") || op_is(op, "tya") ||
                                op_is(op, "tdc") || op_is(op, "tsc") || op_is(op, "pla")))
                    ok = 1;
                else
                    ok = !writes && reload_flags_dead(after);
                if (ok) {
                    size_t keep = (size_t)(pull - (eol + 1));
                    memmove(w, eol + 1, keep);
                    w += keep;
                    p = pull + 8;
                    continue;
                }
            }
        }
        {
            size_t n = (size_t)(eol - p) + 1;
            memmove(w, p, n);
            w += n;
            p = eol + 1;
        }
    }
    {
        size_t rest = strlen(p);
        memmove(w, p, rest + 1);
        w += rest;
    }
    cg.length = (size_t)(w - cg.assembly);
}

static const char *skip_comments(const char *p)
{
    while (*p == ';') {
        const char *end = strchr(p, '\n');
        if (!end)
            break;
        p = end + 1;
    }
    return p;
}

/* After "rep #$20\n.a16\n" at p: the end of "lda #imm / sep #$20 / .a8 /
 * byte stores / rep #$20 / .a16" (the next 16-bit point), or NULL. */
static const char *byte_store_group(const char *p)
{
    const char *q = skip_comments(p);
    int stores = 0;

    if (strncmp(q, "    lda #$", 10) || !isxdigit((unsigned char)q[10]))
        return NULL;
    q = strchr(q, '\n');
    if (!q)
        return NULL;
    ++q;
    if (strncmp(q, "    sep #$20\n.a8\n", 17)) {
        return NULL;
    }
    q += 17;

    for (;;) {
        q = skip_comments(q);
        if (!strncmp(q, "    sta ", 8) || !strncmp(q, "    stz ", 8)) {
            q = strchr(q, '\n');
            if (!q)
                return NULL;
            ++q;
            ++stores;
            continue;
        }
        break;
    }
    if (!stores || strncmp(q, "    rep #$20\n.a16\n", 18))
        return NULL;
    return q + 18;
}

/* A merge leaves A's high byte and N/Z different, so each group must end at a
 * full overwrite of A or at another mergeable group. */
static int byte_group_mergeable(const char *p)
{
    const char *end = byte_store_group(p), *op, *eol;

    if (!end)
        return 0;

    /* A following group starts with a word LDA. Its own merge is checked
     * separately, so an unsafe final group can still stay in word mode. */
    if (byte_store_group(end))
        return 1;
    do {
        end = skip_comments(end);
        eol = strchr(end, '\n');
        if (!eol || !(op = reload_op(end, eol)))
            return 0;
        end = eol + 1;
    } while (op_is(op, "pea") || op_is(op, "pei"));
    return op_is(op, "pla") || op_is(op, "txa") || op_is(op, "tya") || op_is(op, "tdc") ||
           op_is(op, "tsc") || op_is(op, "lda");
}

/* Keep consecutive constant byte stores in one 8-bit region */
static void merge_byte_stores(size_t at)
{
    char *p = cg.assembly + at, *w = p;
    int store = 0;

    while (*p) {
        char *eol = strchr(p, '\n');
        if (!eol)
            break;
        if (store && !strncmp(p, "    rep #$20\n.a16\n", 18) && byte_group_mergeable(p + 18)) {
            char *q = p + 18, *imm;
            size_t n;

            /* Comments, then the immediate narrowed to its stored byte */
            imm = (char *)skip_comments(q);
            n = (size_t)(imm - q);
            memmove(w, q, n);
            w += n;
            {
                char *line = strchr(imm, '\n');
                unsigned long v = strtoul(imm + 10, NULL, 16);
                char buffer[24];
                int k = snprintf(buffer, sizeof buffer, "    lda #$%02lX\n", v & 0xFFu);
                memcpy(w, buffer, (size_t)k);
                w += k;
                p = line + 1 + 17;
            }
            continue;
        }

        /* Set at .a8; kept by stores and comments; cleared by anything else */
        if (!strncmp(p, ".a8\n", 4))
            store = 1;
        else if (strncmp(p, "    sta ", 8) && strncmp(p, "    stz ", 8) && *p != ';')
            store = 0;
        {
            size_t n = (size_t)(eol - p) + 1;
            memmove(w, p, n);
            w += n;
            p = eol + 1;
        }
    }
    {
        size_t rest = strlen(p);
        memmove(w, p, rest + 1);
        w += rest;
    }
    cg.length = (size_t)(w - cg.assembly);
}

#include "assembly_lines.inc"

/* Y-frame to stack-relative conversion of one finished function */
/* edit: 1 delete, 2 TYA->TSC, 3 adjusted N,s, 4 LDX via A before a load,
 * 5 LDX moved to its carry line (1 + its index), the start of the A run. */
typedef struct {
    const char *text;
    size_t length;
    const char *op;
    int label, depth, edit, offset, m8, x8, carry;
} FrameLine;

/* Instructions that only compute A from A and non-X operands */
static int frame_a_only(const FrameLine *l)
{
    static const char *const ops[] = {"and", "ora", "eor", "adc", "sbc", "clc", "sec", "cmp"};
    static const char *const shifts[] = {"asl", "lsr", "rol", "ror", "inc", "dec"};
    const char *comma = strstr(l->op, ",x");
    unsigned i;

    if (l->m8 || (comma && comma < l->text + l->length))
        return 0;

    for (i = 0; i < sizeof ops / sizeof *ops; ++i)
        if (op_is(l->op, ops[i]))
            return 1;

    for (i = 0; i < sizeof shifts / sizeof *shifts; ++i)
        if (op_is(l->op, shifts[i]))
            return l->op[3] == '\n' || l->length == 9;
    return 0;
}

static int frame_line_is(const FrameLine *l, const char *text)
{
    size_t n = strlen(text);

    return l->op && l->length == n + 4 && !strncmp(l->op, text, n);
}

/* Byte change of S, or 99 when the instruction's stack effect is unknown */
static int frame_stack_delta(const FrameLine *l)
{
    const char *op = l->op;

    if (op_is(op, "tcs") || op_is(op, "txs") || op_is(op, "mvn") || op_is(op, "mvp") ||
        op_is(op, "rti"))
        return 99;
    return assembly_stack_bytes(op, l->m8, l->x8);
}

static int frame_y_use(const FrameLine *l)
{
    static const char *const users[] = {"ldy", "sty", "cpy", "iny", "dey", "tay", "tya",
                                        "tyx", "txy", "phy", "ply", "tsx", "mvn", "mvp"};
    unsigned i;
    const char *comma;

    for (i = 0; i < sizeof users / sizeof *users; ++i)
        if (op_is(l->op, users[i]))
            return 1;
    comma = strstr(l->op, ",y");
    return comma && comma < l->text + l->length;
}

static int frame_operand_at(const FrameLine *l, unsigned *n, size_t *at, size_t *span)
{
    const char *p = strstr(l->op, "a:$"), *end = l->text + l->length;
    char *stop;

    if (!p || p > end)
        return 0;
    *n = (unsigned)strtoul(p + 3, &stop, 16);
    if (stop + 2 != end || stop[0] != ',' || stop[1] != 'y' || stop - p != 7)
        return 0;
    *at = (size_t)(p - l->text);
    *span = 9;
    return 1;
}

/* The neighbouring instruction past comments, or -1 at a label, directive or
 * the edge of the function. */
static int frame_instruction(const FrameLine *lines, unsigned count, unsigned k, int direction)
{
    unsigned i = k;

    for (;;) {
        if (direction < 0) {
            if (!i)
                return -1;
            --i;
        } else if (++i >= count)
            return -1;
        if (!lines[i].length)
            return -1;
        if (lines[i].text[0] == ';')
            continue;
        return lines[i].op ? (int)i : -1;
    }
}

static int stack_frames(Function *f, size_t at)
{
    char *text;

    FrameLine *lines;
    unsigned count = 0, i, frame = 0, start = 0, base_line = 0, *work, top = 0;
    size_t length = cg.length - at;
    const char *p;
    int m8 = 0, x8 = 0, ok = 1, prologue = -1, large = 0, base = 0, keep_y = 0, unreachable = 0;
    AssemblyLabels labels = {0};
    unsigned label_count = 0;
    if (f->symbol->interrupt || cg.parser->no_stack_frames)
        return 0;
    text = malloc(length + 1);
    lines = malloc((length / 2 + 2) * sizeof *lines);
    work = malloc((length / 2 + 2) * sizeof *work);
    if (!text || !lines || !work) {
        fputs("out of memory emitting assembly\n", stderr);
        exit(EXIT_FAILURE);
    }
    memcpy(text, cg.assembly + at, length + 1);

    for (p = text; *p;) {
        const char *eol = strchr(p, '\n');
        FrameLine *l = &lines[count++];
        if (!eol)
            eol = p + strlen(p);
        memset(l, 0, sizeof *l);
        l->text = p;
        l->length = (size_t)(eol - p);
        l->depth = -1;
        l->offset = -1;
        l->label = assembly_decode(p, l->length, &m8, &x8, &l->op);
        l->m8 = m8;
        l->x8 = x8;
        if (l->label)
            ++label_count;
        p = *eol ? eol + 1 : eol;
    }

    /* Exactly one prologue: PHY, then pushes and TSC/TAY, or a TCS frame */
    for (i = 0; i < count && ok; ++i)
        if (lines[i].op && frame_line_is(&lines[i], "phy")) {
            unsigned j = i + 1, pushes = 0;

            /* Later PHYs are Y windows, checked while walking */
            if (prologue >= 0)
                continue;
            while (j < count &&
                   (frame_line_is(&lines[j], "pha") || frame_line_is(&lines[j], "phx"))) {
                ++pushes;
                ++j;
            }
            if (j + 1 < count && frame_line_is(&lines[j], "tsc") &&
                frame_line_is(&lines[j + 1], "tay")) {
                prologue = (int)i;
                frame = pushes * 2;
                lines[i].edit = 1;
                lines[j].edit = 1;
                lines[j + 1].edit = 1;
                base_line = j + 1;
            } else if (!pushes && j + 4 < count && frame_line_is(&lines[j], "tsc") &&
                       frame_line_is(&lines[j + 1], "sec") && lines[j + 2].op &&
                       !strncmp(lines[j + 2].op, "sbc #$", 6) &&
                       frame_line_is(&lines[j + 3], "tcs") && frame_line_is(&lines[j + 4], "tay")) {
                prologue = (int)i;
                frame = (unsigned)strtoul(lines[j + 2].op + 6, NULL, 16);
                large = 1;
                lines[i].edit = 1;
                lines[j + 4].edit = 1;
                base_line = j + 4;
            } else {
                /* Pushes interleaved with straight-line parameter setup: every
             * word pushed before TSC/TAY is a frame word. */
                for (j = i + 1, pushes = 0; j + 1 < count; ++j) {
                    const FrameLine *l = &lines[j];
                    if (!l->op) {
                        if (l->label || (l->length && l->text[0] == '.'))
                            break;
                        continue;
                    }
                    if (frame_line_is(l, "tsc") && frame_line_is(&lines[j + 1], "tay"))
                        break;
                    if (l->m8 || l->x8 || frame_y_use(l))
                        break;
                    if (frame_line_is(l, "pha") || frame_line_is(l, "phx") ||
                        !strncmp(l->op, "pea ", 4)) {
                        pushes += 2;
                        continue;
                    }
                    if (frame_stack_delta(l) || op_is(l->op, "jsr") || op_is(l->op, "jsl") ||
                        op_is(l->op, "jmp") || op_is(l->op, "rts") ||
                        (l->op[0] == 'b' && !op_is(l->op, "bit"))) {
                        break;
                    }
                }
                if (j + 1 < count && frame_line_is(&lines[j], "tsc") &&
                    frame_line_is(&lines[j + 1], "tay") && pushes) {
                    prologue = (int)i;
                    frame = pushes;
                    lines[i].edit = 1;
                    lines[j].edit = 1;
                    lines[j + 1].edit = 1;
                    base_line = j + 1;
                } else
                    ok = 0;
            }
        }
    if (prologue < 0)
        ok = 0;
    if (ok && lines[prologue].x8)
        ok = 0;

    /* Y windows: "phy / ldy #k ... [ptr],y ... ply" around far accesses. A
     * converted frame leaves Y free, so the windows go and the caller's Y is
     * saved once by the prologue's PHY and restored by the final PLY. */
    for (i = 0; ok && i < count; ++i)
        if (i != (unsigned)prologue && frame_line_is(&lines[i], "phy"))
            keep_y = 1;
    if (keep_y)
        lines[prologue].edit = 6;

    /* Walk every path from entry. A state is the push depth from entry times
     * two, plus one while the saved Y (removed below) is on the stack. */
    if (ok) {
        assembly_labels_init(&labels, label_count);
        for (i = 0; i < count; ++i)
            if (lines[i].label)
                assembly_label_add(&labels, lines[i].text, lines[i].length, i);
        lines[0].depth = 0;
        work[top++] = 0;
    }

    while (ok && top) {
        unsigned k = work[--top], first = k;
        int state = lines[k].depth, d = state >> 2, win = (state >> 1) & 1, active = state & 1;
        for (; k < count && ok; ++k) {
            FrameLine *l = &lines[k];
            int delta, target = -1, ends = 0, conditional = 0;
            if (k != first && l->depth >= 0) {
                if (l->depth != ((d << 2) | (win << 1) | active))
                    ok = 0;
                break;
            }
            l->depth = ((d << 2) | (win << 1) | active);
            if (!l->op)
                continue;
            if (k == (unsigned)prologue) {
                d += 2;
                active = 1;
                continue;
            }
            if (win) {
                /* Inside a window Y is an index: only these uses, and no
                 * frame or stack-relative operand. */
                const char *end = l->text + l->length;
                if (frame_line_is(l, "ply")) {
                    l->edit = 1;
                    d -= 2;
                    win = 0;
                    continue;
                }
                if (frame_y_use(l)) {
                    if (op_is(l->op, "ldy") || op_is(l->op, "iny") || op_is(l->op, "dey") ||
                        op_is(l->op, "txy") ||
                        (l->length > 3 &&
                         (!strncmp(end - 3, "],y", 3) || !strncmp(end - 3, "),y", 3)))) {
                        l->edit = 6;
                        continue;
                    }
                    ok = 0;
                    break;
                }
                if (l->length > 2 && end[-2] == ',' && end[-1] == 's') {
                    ok = 0;
                    break;
                }
                if (op_is(l->op, "rts") || op_is(l->op, "rtl")) {
                    ok = 0;
                    break;
                }
            } else if (keep_y && frame_line_is(l, "phy")) {
                if (!active) {
                    ok = 0;
                    break;
                }
                l->edit = 1;
                d += 2;
                win = 1;
                continue;
            }
            if (l->edit && k != base_line) {
                d += frame_stack_delta(l);
                continue;
            }
            if (k == base_line) {
                if (large)
                    d += (int)frame;
                base = d;
                continue;
            }
            if (large && frame_line_is(l, "tcs") && k == base_line - 1)
                continue;
            if (frame_line_is(l, "tya")) {
                /* Large-frame teardown: TYA is S at the frame base, then
                 * CLC/ADC/TCS releases the frame. */
                if (d != base || !active || k + 3 >= count ||
                    !frame_line_is(&lines[k + 1], "clc") || !lines[k + 2].op ||
                    strncmp(lines[k + 2].op, "adc #$", 6) || !frame_line_is(&lines[k + 3], "tcs")) {
                    ok = 0;
                    break;
                }
                l->edit = 2;
                lines[k + 1].depth = lines[k + 2].depth = ((d << 2) | (win << 1) | active);
                d -= (int)strtoul(lines[k + 2].op + 6, NULL, 16);
                k += 3;
                lines[k].depth = ((d << 2) | (win << 1) | active);
                continue;
            }
            if (frame_line_is(l, "ply")) {
                if (!active || d != 2) {
                    ok = 0;
                    break;
                }
                l->edit = keep_y ? 6 : 1;
                d = 0;
                active = 0;
                continue;
            }
            if (frame_y_use(l)) {
                unsigned n;
                size_t pos, span;

                /* Only these instructions have a stack-relative mode. LDX
                 * has none; it goes through A where A and N/Z are dead. */
                if (op_is(l->op, "ldx") && !l->m8 && !l->x8) {
                    int before = frame_instruction(lines, count, k, -1),
                        after = frame_instruction(lines, count, k, 1);
                    while (after >= 0 && (frame_line_is(&lines[after], "inx") ||
                                          frame_line_is(&lines[after], "dex")))
                        after = frame_instruction(lines, count, (unsigned)after, 1);
                    if (after >= 0 && lines[after].op && op_is(lines[after].op, "lda") &&
                        !lines[after].m8)
                        l->edit = 4;
                    else if (after >= 0 &&
                             (op_is(lines[after].op, "jsr") || op_is(lines[after].op, "jsl"))) {
                        /* Before a call (which reads no flags), load X ahead of
                         * the run of A-only instructions that produced A. */
                        while (before >= 0 && frame_a_only(&lines[before]))
                            before = frame_instruction(lines, count, (unsigned)before, -1);
                        if (before < 0 || !op_is(lines[before].op, "lda") || lines[before].m8 ||
                            lines[before].carry ||
                            (strstr(lines[before].op, ",x") &&
                             strstr(lines[before].op, ",x") <
                                 lines[before].text + lines[before].length)) {
                            ok = 0;
                            break;
                        }
                        l->edit = 5;
                        lines[before].carry = (int)k + 1;
                    } else {
                        ok = 0;
                        break;
                    }
                } else if (!(op_is(l->op, "lda") || op_is(l->op, "sta") || op_is(l->op, "adc") ||
                             op_is(l->op, "sbc") || op_is(l->op, "and") || op_is(l->op, "ora") ||
                             op_is(l->op, "eor") || op_is(l->op, "cmp"))) {
                    ok = 0;
                    break;
                }
                if (!active || !frame_operand_at(l, &n, &pos, &span) || d < base || !base) {
                    ok = 0;
                    break;
                }
                if (n > frame && n <= frame + 2) {
                    ok = 0;
                    break;
                }
                l->offset = (int)(keep_y || n <= frame ? n : n - 2) + (d - base);
                if (l->offset > 255) {
                    ok = 0;
                    break;
                }
                continue;
            }
            if (active) {
                /* An existing N,s operand above the removed slot moves down */
                const char *end = l->text + l->length;
                if (l->length > 2 && end[-2] == ',' && end[-1] == 's') {
                    const char *q = end - 2;
                    unsigned n;
                    while (q > l->op && isdigit((unsigned char)q[-1]))
                        --q;
                    if (q == end - 2 || q[-1] != ' ') {
                        ok = 0;
                        break;
                    }
                    n = (unsigned)strtoul(q, NULL, 10);
                    if (keep_y)
                        l->offset = (int)n;
                    else if ((int)n > d)
                        l->offset = (int)n - 2;
                    else if ((int)n > d - 2) {
                        ok = 0;
                        break;
                    } else
                        l->offset = (int)n;
                    l->edit = 3;
                }
            }
            if (frame_line_is(l, "tsc") && k + 3 < count && frame_line_is(&lines[k + 1], "clc") &&
                lines[k + 2].op && !strncmp(lines[k + 2].op, "adc #$", 6) &&
                frame_line_is(&lines[k + 3], "tcs")) {
                lines[k + 1].depth = lines[k + 2].depth = d;
                d -= (int)strtoul(lines[k + 2].op + 6, NULL, 16);
                k += 3;
                lines[k].depth = d;
                continue;
            }
            delta = frame_stack_delta(l);
            if (delta == 99) {
                ok = 0;
                break;
            }
            d += delta;
            if (d < 0) {
                ok = 0;
                break;
            }
            if (op_is(l->op, "rts") || op_is(l->op, "rtl")) {
                if (d) {
                    ok = 0;
                }
                ends = 1;
            } else if (op_is(l->op, "jml") || op_is(l->op, "brk") || op_is(l->op, "cop") ||
                       op_is(l->op, "stp"))
                ends = 1;
            else if (op_is(l->op, "jmp") || op_is(l->op, "bra") || op_is(l->op, "brl") ||
                     (l->op[0] == 'b' &&
                      (op_is(l->op, "bcc") || op_is(l->op, "bcs") || op_is(l->op, "beq") ||
                       op_is(l->op, "bne") || op_is(l->op, "bmi") || op_is(l->op, "bpl") ||
                       op_is(l->op, "bvc") || op_is(l->op, "bvs")))) {
                const char *name = l->op + 4;
                size_t n = (size_t)(l->text + l->length - name);
                conditional = l->op[0] == 'b' && !op_is(l->op, "bra") && !op_is(l->op, "brl");
                if (*name == '(' || *name == '[') {
                    ok = 0;
                    break;
                }
                target = assembly_label_target(&labels, k, name, n);
                if (target < 0) {
                    /* A transfer out of the function is a tail call: frame gone */
                    if (conditional || d) {
                        ok = 0;
                        break;
                    }
                    ends = 1;
                }
            }
            if (target >= 0) {
                if (lines[target].depth < 0) {
                    lines[target].depth = ((d << 2) | (win << 1) | active);
                    work[top++] = (unsigned)target;
                } else if (lines[target].depth != ((d << 2) | (win << 1) | active)) {
                    ok = 0;
                    break;
                }
                if (!conditional)
                    break;
            }
            if (ends)
                break;
        }
    }

    /* Unreachable frame references must be pruned before removing Y */
    for (i = 0; ok && i < count; ++i)
        if (lines[i].op && frame_y_use(&lines[i]) && !lines[i].edit && lines[i].offset < 0 &&
            lines[i].depth >= 0)
            ok = 0;

    for (i = 0; ok && i < count; ++i)
        if (lines[i].op && frame_y_use(&lines[i]) && lines[i].depth < 0) {
            ok = 0;
            unreachable = 1;
        }
    if (ok) {
        const FrameLine *previous = NULL;
        cg.length = at;
        cg.assembly[at] = 0;
        for (i = 0; i < count; ++i) {
            FrameLine *l = &lines[i];
            if (l->edit == 1 || l->edit == 5)
                continue;
            if (l->edit == 4) {
                code("    lda %u,s\n    tax\n", (unsigned)l->offset);
                previous = NULL;
                continue;
            }

            /* An LDX before a call moves ahead of the run that produced A */
            if (l->carry) {
                code("    lda %u,s\n    tax\n", (unsigned)lines[l->carry - 1].offset);
                previous = NULL;
            }
            if (l->edit == 2) {
                code("    tsc\n");
                previous = l;
                continue;
            }
            if (l->edit == 3) {
                const char *q = l->text + l->length - 2;
                while (isdigit((unsigned char)q[-1]))
                    --q;
                code("%.*s%u,s\n", (int)(q - l->text), l->text, (unsigned)l->offset);
                previous = l;
                continue;
            }
            if (l->offset >= 0) {
                unsigned n;
                size_t pos, span;
                frame_operand_at(l, &n, &pos, &span);

                /* Just after a 16-bit PHX, 1,s is X itself: TXA gives the same
                 * A and N/Z without the stack read. */
                if (l->offset == 1 && pos == 4 && !strncmp(l->op, "lda ", 4) && !l->m8 && !l->x8 &&
                    previous && frame_line_is(previous, "phx")) {
                    code("    txa\n");
                    previous = l;
                    continue;
                }
                code("%.*s%u,s\n", (int)pos, l->text, (unsigned)l->offset);
                previous = l;
                continue;
            }
            if (l->length || l->text[0])
                code("%.*s\n", (int)l->length, l->text);
            if (l->op)
                previous = l;
            else if (l->label)
                previous = NULL;
        }
    }
    (void)start;
    assembly_labels_free(&labels);
    free(text);
    free(lines);
    free(work);
    return unreachable;
}
