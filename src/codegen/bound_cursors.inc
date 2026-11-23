/* Register-resident strength cursors (Phase B). An innermost loop may keep one
 * strength cursor in X for its whole body: element accesses at the region's
 * single displacement need no cursor load, and cursor updates become INX/DEX.
 * X holds cursor+delta. The home is loaded once at region entry and written
 * back at the loop's end label, which every exit through the loop reaches;
 * a return leaves the compiler-private cursor dead.
 *
 * Emission is speculative. The loop is emitted with the binding, then the
 * region's text is scanned: any write to X other than the binding's own
 * recorded instructions, any call, an index-width change, or any remaining
 * access to the cursor's home rejects it, and the loop is emitted again
 * exactly as before. */
static void bound_enter(void)
{
    InductionCursor *c = bound_state.pending;
    int bias;

    if (!c || bound_state.entered)
        return;

    bound_state.cursor = c;
    bound_state.entered = 1;
    bound_state.start = cg.length;
    code("; register cursor %s[%s] in X, displacement %d\n", c->base->name, c->index->name,
         (int)(int16_t)bound_state.delta);
    bound_state.own = 1;
    bound_emit("ldx", frame_operand(c->offset));
    bound_state.own = 0;
    bias = (int)(int16_t)bound_state.delta;

    if (bias)
        bound_step(bound_state.delta);
}

static void bound_exit(void)
{
    InductionCursor *c = bound_state.cursor;
    int bias;
    const char *home;

    if (!c)
        return;

    bias = (int)(int16_t)bound_state.delta;
    bound_state.own = 1;
    home = frame_operand(c->offset);

    /* STX has no absolute,Y mode: a Y-frame home is stored through A */
    if (!strncmp(home, "z:", 2) && bias >= -3 && bias <= 3) {
        if (bias)
            bound_step(0u - bound_state.delta);

        code("    stx %s\n", home);
    } else if (!bias)
        code("    txa\n    sta %s\n", home);
    else
        code("    txa\n    sec\n    sbc #$%04X\n    sta %s\n", bound_state.delta, home);

    bound_state.own = 0;
    bound_state.end = cg.length;
    bound_state.cursor = NULL;
}

static int bound_contains_loop(Statement *s)
{
    for (; s; s = s->next) {
        if (s->kind == ST_WHILE || s->kind == ST_FOR || s->kind == ST_DO)
            return 1;
        if (bound_contains_loop(s->body) || bound_contains_loop(s->alternate) ||
            bound_contains_loop(s->initial))
            return 1;
    }

    return 0;
}

/* Collect the distinct displacements of the region's cursor accesses, most
 * frequent first; each is a candidate for the value X holds. */
typedef struct {
    unsigned delta[4];
    int uses[4];
    unsigned count;
} BoundDeltas;

static void bound_deltas_expr(Expr *e, InductionCursor *c, BoundDeltas *d)
{
    unsigned i, delta;

    if (!e)
        return;

    if (strength_pointer_plan(e, &delta) == c) {
        for (i = 0; i < d->count && d->delta[i] != delta; ++i) {
        }

        if (i == d->count && d->count < 4) {
            d->delta[d->count] = delta;
            d->uses[d->count++] = 0;
        }

        if (i < d->count)
            ++d->uses[i];
    }

    bound_deltas_expr(e->left, c, d);
    bound_deltas_expr(e->right, c, d);
    bound_deltas_expr(e->third, c, d);

    for (i = 0; i < e->arg_count; ++i) {
        bound_deltas_expr(e->args[i], c, d);
    }
}

static void bound_deltas(Statement *s, InductionCursor *c, BoundDeltas *d)
{
    for (; s; s = s->next) {
        bound_deltas_expr(s->expression, c, d);
        bound_deltas_expr(s->step, c, d);
        bound_deltas(s->initial, c, d);
        bound_deltas(s->body, c, d);
        bound_deltas(s->alternate, c, d);
    }
}

static int bound_marked(size_t offset)
{
    unsigned i;

    for (i = 0; i < bound_state.mark_count; ++i) {
        if (bound_state.marks[i] == offset)
            return 1;
    }

    return 0;
}

/* Reject any foreign write to X, call or index-width change in the region */
static int bound_scan(void)
{
    static const char *const writers[] = {"ldx", "tax", "plx", "inx", "dex", "tsx", "tyx",
                                          "mvn", "mvp", "jsr", "jsl", "jml", "brk", "cop"};
    const char *p = cg.assembly + bound_state.start, *end = cg.assembly + bound_state.end;

    while (p < end) {
        const char *eol = memchr(p, '\n', (size_t)(end - p)), *t = p;

        unsigned i;

        if (!eol)
            eol = end;

        while (t < eol && *t == ' ') {
            ++t;
        }

        if (t != p && eol - t >= 3) {
            for (i = 0; i < sizeof writers / sizeof *writers; ++i) {
                if (!strncmp(t, writers[i], 3) && (eol - t == 3 || t[3] == ' '))
                    break;
            }

            if (i < sizeof writers / sizeof *writers && !bound_marked((size_t)(p - cg.assembly)))
                return 0;
            if ((!strncmp(t, "rep #$", 6) || !strncmp(t, "sep #$", 6)) &&
                (strtoul(t + 6, NULL, 16) & 0x10))
                return 0;

            if (!strncmp(t, "jmp ", 4)) {
                const char *name = t + 4;

                if (!strncmp(name, ".loword(", 8))
                    name += 8;
                if (strncmp(name, "cg_", 3) && strncmp(name, "return_", 7) && *name != ':')
                    return 0;
            }
        }

        p = eol + 1;
    }

    return 1;
}

static int bound_loop_statement(Statement *s)
{
    CodegenCheckpoint *saved;

    unsigned i;
    int result;

    if (cg.parser->no_register_cursors || cg.switch_depth || cg.stack_leaf || cg.scalar_leaf ||
        cg.scalar_first || cg.leaf_count || bound_state.cursor || bound_state.pending ||
        volatile_statement(s) || bound_contains_loop(s->body))
        return emit_loop(s);

    saved = malloc(sizeof *saved);

    if (!saved) {
        fputs("out of memory emitting assembly\n", stderr);
        exit(EXIT_FAILURE);
    }

    for (i = 0; i < cg.cursor_count; ++i) {
        InductionCursor *c = &cg.cursors[i];
        BoundDeltas d = {{0}, {0}, 0};

        unsigned k, j;
        size_t start = cg.length;

        bound_deltas_expr(s->expression, c, &d);
        bound_deltas_expr(s->step, c, &d);
        bound_deltas(s->body, c, &d);

        for (k = 1; k < d.count; ++k) {
            for (j = k; j && d.uses[j - 1] < d.uses[j]; --j) {
                unsigned t = d.delta[j];
                int u = d.uses[j];

                d.delta[j] = d.delta[j - 1];
                d.uses[j] = d.uses[j - 1];
                d.delta[j - 1] = t;
                d.uses[j - 1] = u;
            }
        }

        for (k = 0; k < d.count; ++k) {
            cg_checkpoint_save(saved);
            bound_state.pending = c;
            bound_state.delta = d.delta[k] & 0xFFFF;
            bound_state.mark_count = 0;
            bound_state.failed = 0;
            bound_state.entered = 0;
            result = emit_loop(s);

            if (bound_state.cursor)
                bound_state.failed = 1; /* entered without reaching the end label */

#ifdef BOUND_DRYRUN
            bound_state.failed = 1;
#endif

            if (bound_state.entered && !bound_state.failed && bound_scan()) {
                bound_state.pending = NULL;
                bound_state.entered = 0;
                free(saved);
                return result;
            }

            cg_checkpoint_restore(saved, start);
        }
    }

    free(saved);
    return emit_loop(s);
}
