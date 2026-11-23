// Translation-unit emission driver, wide validation, WRAM/SRAM/RODATA, and relaxation

#include "line_passes.inc"

static int lto_provided_function(Parser *p, Symbol *s)
{
    Function *f;

    if (!p->source_lto || !s->function)
        return 0;

    for (f = p->functions; f; f = f->next)
        if (!strcmp(f->symbol->asm_name, s->asm_name) && !f->symbol->inline_omit &&
            (!f->symbol->inline_hint || f->symbol->internal || f->symbol->inline_external))
            return 1;
    return 0;
}

/* Some near lvalues use an immediate object address followed by an indexed
 * memory instruction. Distinguish those from addresses passed to hardware. */
static Symbol *interrupt_address_base(Expr *e)
{
    unsigned offset;

    if (!e || far_pointer(value_type(e->type)))
        return NULL;
    if (e->kind == EX_CAST)
        return interrupt_address_base(e->left);
    if (e->kind == EX_BINARY && (e->op == '+' || e->op == '-'))
        return interrupt_address_base(value_type(e->left->type).pointers ? e->left : e->right);
    return near_object_address(e, &offset);
}

static void interrupt_lvalues(Expr *e, int access)
{
    Symbol *s = NULL;
    unsigned i, offset;

    if (!e)
        return;
    if (access) {
        if (e->kind == EX_OBJECT && !e->type.array)
            s = e->symbol;
        if (e->kind == EX_DEREF)
            s = interrupt_address_base(e->left);
        if (e->kind == EX_MEMBER && !e->type.array) {
            int pointer;
            Expr *root = member_root(e, &offset, &pointer);
            if (pointer)
                s = interrupt_address_base(root);
            else if (root->kind == EX_DEREF)
                s = interrupt_address_base(root->left);
            else if (root->kind == EX_OBJECT)
                s = root->symbol;
        }
        if (s && !s->owner && !s->function && !s->dpage && !s->type.banked)
            code("; interrupt lvalue _%s\n", s->asm_name);
    }
    interrupt_lvalues(e->left,
                      e->kind != EX_ADDRESS && (e->kind != EX_MEMBER || e->op == TOK_ARROW));
    interrupt_lvalues(e->right, 1);
    interrupt_lvalues(e->third, 1);

    for (i = 0; i < e->arg_count; ++i)
        interrupt_lvalues(e->args[i], 1);
}

static void interrupt_statement_lvalues(Statement *s)
{
    for (; s; s = s->next) {
        interrupt_lvalues(s->expression, 1);
        interrupt_lvalues(s->step, 1);
        interrupt_statement_lvalues(s->initial);
        interrupt_statement_lvalues(s->body);
        interrupt_statement_lvalues(s->alternate);
    }
}

/* Keep unsupported wide value uses out of 32-bit optimizers until the full
 * eight-byte ABI and general expression lowering are implemented. */
static int validate_wide_expression(Expr *e)
{
    unsigned i;
    int used = 0;

    if (!e)
        return 0;
    if (e->kind == EX_ADDRESS && e->left) {
        if (e->left->kind == EX_OBJECT)
            return 0;
        if (e->left->kind == EX_DEREF || e->left->kind == EX_MEMBER)
            return validate_wide_expression(e->left->left);
    }
    if (wide_compare_supported(e) || wide_narrow_supported(e) || wide_pointer_supported(e) ||
        wide_call_used(e) || narrow_wide_compound_supported(e))
        return 1;
    if (!wide_address_safe(e) && wide_mixed_narrow_supported(e))
        return 1;
    if (!e->type.pointers && !e->type.array && e->type.base == TY_DOUBLE)
        error_at(e->location, "binary64 runtime values are not implemented yet");
    if (!e->type.pointers && !e->type.array && e->type.base == TY_LONGLONG)
        error_at(e->location, "64-bit runtime values are not implemented yet");
    used |= validate_wide_expression(e->left);
    used |= validate_wide_expression(e->right);
    used |= validate_wide_expression(e->third);

    for (i = 0; i < e->arg_count; ++i)
        used |= validate_wide_expression(e->args[i]);
    if (used &&
        (((e->type.pointers || e->type.array) && !wide_pointer_supported(e) &&
          !(e->type.array && e->kind == EX_DEREF && wide_lvalue_address_supported(e)) &&
          !(e->kind == EX_ASSIGN && e->left->kind == EX_OBJECT &&
            ((!e->op && (wide_pointer_supported(e->right) || wide_narrow_supported(e->right) ||
                         wide_address_expression_supported(e->right))) ||
             ((e->op == '+' || e->op == '-') && wide_narrow_supported(e->right))))) ||
         (e->kind != EX_BINARY && e->kind != EX_UNARY && e->kind != EX_CAST &&
          e->kind != EX_CHOOSE && e->kind != EX_COMMA && e->kind != EX_CALL &&
          e->kind != EX_ASSIGN &&
          !(e->kind == EX_DEREF &&
            (wide_pointer_supported(e->left) || wide_narrow_supported(e->left))) &&
          !((e->kind == EX_MEMBER || e->kind == EX_BITFIELD) && wide_lvalue_address_supported(e)))))
        error_at(e->location, "64-bit runtime values in this expression are not implemented yet");
    if (used && e->kind == EX_ASSIGN &&
        (!e->left ||
         (e->left->kind != EX_OBJECT && ((!wide_lvalue_address_supported(e->left)) ||
                                         (e->op && !wide_mixed_narrow_supported(e->right))))))
        error_at(e->location, "64-bit runtime values in this assignment are not implemented yet");
    return used;
}

static int validate_wide_condition(Expr *e)
{
    if (!e)
        return 0;
    if (wide_compare_supported(e) || (wide_scalar(value_type(e->type)) && wide_value_supported(e)))
        return 1;
    if (e->kind == EX_BINARY && (e->op == TOK_LAND || e->op == TOK_LOR)) {
        int a = validate_wide_condition(e->left), b = validate_wide_condition(e->right);
        return a || b;
    }
    if (e->kind == EX_UNARY && e->op == '!')
        return validate_wide_condition(e->left);
    if (e->kind == EX_CAST && e->type.is_bool && !e->type.pointers)
        return validate_wide_condition(e->left);
    return validate_wide_expression(e);
}

static int wide_discard_supported(Expr *e)
{
    if (!e)
        return 0;
    if (e->kind == EX_CAST && !e->type.pointers && e->type.base == TY_VOID)
        return wide_discard_supported(e->left);
    if (e->kind == EX_COMMA && !e->type.pointers && e->type.base == TY_VOID &&
        !wide_address_safe(e))
        return (wide_address_safe(e->left) || wide_discard_supported(e->left)) &&
               (wide_address_safe(e->right) || wide_discard_supported(e->right));
    if (wide_scalar(value_type(e->type)))
        return wide_value_supported(e);
    return !wide_address_safe(e) && wide_mixed_narrow_supported(e);
}

static int validate_wide_statements(Statement *s, int wide_result)
{
    int used = 0;

    for (; s; s = s->next) {
        if (s->kind == ST_EXPR &&
            (wide_assignment_supported(s->expression) || wide_update_supported(s->expression) ||
             wide_narrow_assignment(s->expression) || wide_discard_supported(s->expression)))
            used = 1;
        else if (s->kind == ST_SWITCH && wide_scalar(value_type(s->expression->type)) &&
                 wide_value_supported(s->expression))
            used = 1;
        else if (s->kind == ST_IF || s->kind == ST_WHILE || s->kind == ST_FOR || s->kind == ST_DO)
            used |= validate_wide_condition(s->expression);
        else if (s->kind == ST_RETURN && wide_result && wide_value_supported(s->expression))
            used = 1;
        else if ((s->kind == ST_EXPR || s->kind == ST_RETURN) && wide_call_used(s->expression))
            used = 1;
        else if (s->kind == ST_RETURN &&
                 (wide_compare_supported(s->expression) || wide_narrow_supported(s->expression)))
            used = 1;
        else
            used |= validate_wide_expression(s->expression);
        if (wide_assignment_supported(s->step) || wide_update_supported(s->step) ||
            wide_narrow_assignment(s->step) || wide_discard_supported(s->step))
            used = 1;
        else
            used |= validate_wide_expression(s->step);
        used |= validate_wide_statements(s->body, wide_result);
        used |= validate_wide_statements(s->alternate, wide_result);
        used |= validate_wide_statements(s->initial, wide_result);
    }
    return used;
}

static int function_uses_wide(Function *f)
{
    Symbol *s = f->symbol;
    int signature = wide_scalar(value_type(s->type));

    for (int i = 0; i < s->param_count; ++i)
        if (wide_scalar(value_type(s->params[i])))
            signature = 1;
    return validate_wide_statements(f->body, wide_scalar(value_type(s->type))) | signature;
}

static void resolve_near_memcpy(Parser *p)
{
    for (unsigned i = 0; i < p->symbol_count; ++i) {
        Symbol *s = &p->symbols[i];
        Type result, source, count;
        if (!s->function || s->defined || s->internal || s->old_style || s->variadic ||
            s->param_count != 3 || strcmp(s->asm_name, "memcpy"))
            continue;
        result = value_type(s->type);
        source = value_type(s->params[1]);
        count = value_type(s->params[2]);
        if (result.base == TY_VOID && result.pointers == 1 && !far_pointer(result) &&
            same_type(result, value_type(s->params[0])) && source.base == TY_VOID &&
            source.pointers == 1 && !far_pointer(source) && object_constant(pointed_type(source)) &&
            count.base == TY_INT && !count.pointers && count.is_unsigned)
            strcpy(s->asm_name, "_zicc_memcpy_near");
    }
}

#include "narrow_rodata.inc"

static void wram_object_segment(Symbol *s, unsigned part)
{
    const char *kind = s->wram == WRAM_HIRAM ? "H" : "X";

    if (s->initializer)
        code(".segment \"ZWRAM_D_%s_%u_%s\"\n", kind, part, s->asm_name);
    else
        code(".segment \"ZWRAM_B_%s_0_%s\"\n", kind, s->asm_name);
}

static void emit_sram_object(Symbol *s)
{
    unsigned size = width(s->type), bank = (unsigned)(s->wram - WRAM_SRAM_FIRST);
    unsigned remaining = size;

    for (unsigned part = 0; remaining; part++) {
        unsigned bytes = remaining < sram_window_size ? remaining : sram_window_size;
        code(".segment \"ZSRAM_%u_%u_%u_%u_%u_%s\"\n", sram_first_bank, sram_window_size,
             sram_capacity, bank, part, s->asm_name);
        if (alignment(s->type) == 2)
            code(".align 2\n");
        if (!part)
            code("_%s:\n", s->asm_name);
        code("    .res %u\n", bytes);
        remaining -= bytes;
    }
    if (!s->internal) {
        code(".export _%s\n", s->asm_name);
        code("__zicc_sram_window_%s = %u\n.export __zicc_sram_window_%s: absolute\n", s->asm_name,
             bank, s->asm_name);
        code("__zicc_sram_bound_%s = %u\n.export __zicc_sram_bound_%s: far\n", s->asm_name,
             s->type.array, s->asm_name);
        code("__zicc_object_size_%s = %u\n.export __zicc_object_size_%s: far\n", s->asm_name, size,
             s->asm_name);
    }
}

static int wram_placement_known(Parser *p, Symbol *s)
{
    const char *item = p->near_wram_objects;
    size_t length = strlen(s->asm_name);

    while (item && *item) {
        const char *end = strchr(item, ',');
        if ((end ? (size_t)(end - item) : strlen(item)) == length &&
            !memcmp(item, s->asm_name, length))
            return 1;
        item = end ? end + 1 : NULL;
    }
    return 0;
}

static void emit_program(FILE *out, Parser *p)
{
    Function *f;

    String *string;
    unsigned i, runtime_size = 0;
    cg_reset_program(p);

    for (f = p->functions; f; f = f->next)
        f->uses_wide = function_uses_wide(f);
    inline_translation_unit(p);
    narrow_rodata_struct_arrays(p);
    resolve_near_memcpy(p);

    for (i = 0; i < p->symbol_count; ++i) {
        Symbol *s = &p->symbols[i];
        if (s->wram && s->wram < WRAM_SRAM_FIRST && !s->owner)
            s->wram_near = wram_placement_known(p, s);
    }
    code("; ABI: near7e-far24pad32\n");

    /* Debugger names describe source objects, never linker bookkeeping */
    for (i = 0; i < p->symbol_count; ++i) {
        Symbol *s = &p->symbols[i];
        if (s->owner || !s->defined)
            continue;
        code("; debug symbol _%s %s\n", s->asm_name,
             s->internal && !strncmp(s->asm_name, "__lto_", 6) ? s->asm_name + 2 : s->asm_name);
    }
    code(".setcpu \"65816\"\n.a16\n.i16\n.import main_exit\n");

    for (i = 0; i < p->symbol_count; ++i) {
        Symbol *s = &p->symbols[i];
        if (s->owner || s->function || !s->defined)
            continue;
        unsigned size = width(s->type);
        if (s->wram >= WRAM_SRAM_FIRST) {
            emit_sram_object(s);
            continue;
        }
        if (s->wram)
            wram_object_segment(s, 0);
        else
            code(".segment \"%s\"%s\n",
                 s->runtime_ram   ? "RUNTIME_BSS"
                 : s->loram       ? (s->initializer ? "LORAM_DATA" : "LORAM_BSS")
                 : s->initializer ? (s->type.banked ? (s->embedded ? "EMBED" : "RODATA") : "DATA")
                 : s->dpage       ? "ZEROPAGE"
                                  : "BSS",
                 s->dpage ? ": zeropage" : "");
        if (!s->runtime_ram && !s->loram && !s->dpage && !s->type.banked)
            code("; allocation object _%s %s\n", s->asm_name, s->internal ? "local" : "global");
        if (s->runtime_ram) {
            unsigned a = alignment(s->type);
            runtime_size = (runtime_size + a - 1) & ~(a - 1);
            runtime_size += size;
        }
        if (!s->internal)
            code(".%s _%s\n", s->dpage ? "exportzp" : "export", s->asm_name);
        code("__zicc_object_size_%s = %u\n", s->asm_name, size);
        if (!s->internal)
            code(".export __zicc_object_size_%s: %s\n", s->asm_name,
                 size > 65536 || (s->wram && size > 65535) ? "far" : "absolute");
        if (s->wram && !s->internal) {
            const char *kind = s->wram == WRAM_HIRAM ? "H" : "X";
            code("__zicc_wram_%s_%s = %u\n.export __zicc_wram_%s_%s: far\n", kind, s->asm_name,
                 size, kind, s->asm_name);
        }
        if (structure_object(s->type) ||
            ((s->initializer || s->runtime_ram || s->wram) && alignment(s->type) == 2))
            code(".align 2\n");
        if (s->initializer) {
            unsigned j, part = 0, boundary = s->wram ? 0x4000 : size;
            Relocation *r = s->relocations;
            code("_%s:\n", s->asm_name);
            for (j = 0; j < size;) {
                /* Keep relocations intact so a manual LoROM link can place
                 * each copy span in a single physical source window. */
                if (r && r->offset == j && j < boundary && j + r->size > boundary)
                    boundary = j;
                if (j == boundary) {
                    wram_object_segment(s, ++part);
                    boundary = j + 0x4000;
                }
                if (r && r->offset == j) {
                    char target[160];
                    if (r->symbol) {
                        snprintf(target, sizeof target,
                                 r->symbol->function
                                     ? (wide_scalar(value_type(r->symbol->type)) ? "__fnptr64_%s"
                                                                                 : "__fnptr_%s")
                                     : "_%s",
                                 r->symbol->asm_name);
                        r->symbol->used = 1;
                        if (r->symbol->function)
                            r->symbol->adapter_used = 1;
                    } else {
                        snprintf(target, sizeof target, "str_%s_%u", p->unit, r->string->id);
                        r->string->used = 1;
                    }
                    code("    .word .loword(%s%+ld)\n", target, (long)r->addend);
                    if (r->far_value) {
                        if (r->symbol && !r->symbol->function && !r->symbol->type.banked)
                            code("    .byte $7E, $00\n");
                        else
                            code("    .byte .bankbyte(%s%+ld), $00\n", target, (long)r->addend);
                    }
                    if (r->symbol && !r->symbol->function && !r->symbol->type.banked &&
                        !r->symbol->dpage)
                        code(".assert %s%+ld >= $7E0001 .and %s%+ld <= $7EFFFF, lderror, \"near "
                             "address initializer exceeds bank $7E\"\n",
                             target, (long)r->addend, target, (long)r->addend);
                    j += r->size;
                    r = r->next;
                } else {
                    unsigned end = boundary < size ? boundary : size;
                    if (r && end > r->offset)
                        end = r->offset;
                    if (!s->wram && size > 65536 && s->initializer[j] == 0) {
                        unsigned limit = end < j + 65535 ? end : j + 65535;
                        unsigned zero = j + 1;
                        while (zero < limit && s->initializer[zero] == 0)
                            ++zero;
                        if (zero - j >= 16) {
                            code("    .res %u, 0\n", zero - j);
                            j = zero;
                            continue;
                        }
                    }
                    if (end > j + 16)
                        end = j + 16;
                    code("    .byte ");
                    for (; j < end; ++j) {
                        code("$%02X", s->initializer[j]);
                        if (j + 1 < end)
                            code(",");
                    }
                    code("\n");
                }
            }
        } else if (s->wram && size > 65535) {
            unsigned remaining = size;
            code("_%s:\n", s->asm_name);
            while (remaining > 65535) {
                code("    .res 65535\n");
                remaining -= 65535;
            }
            code("    .res %u\n", remaining);
        } else
            code("_%s: .res %u\n", s->asm_name, size);
        if (s->runtime_ram)
            code(".assert _%s >= $7F0000 .and _%s + %u <= $800000, lderror, \"runtime object "
                 "exceeds bank $7F\"\n",
                 s->asm_name, s->asm_name, size);
    }
    if (runtime_size)
        code(".export __runtime_runtime_bss_size := %u\n", runtime_size);
    static_ipa_prepare(p);
    bank_prepare();

    for (f = p->functions; f; f = f->next) {
        size_t at;
        if (f->symbol->inline_omit ||
            (f->symbol->inline_hint && !f->symbol->internal && !f->symbol->inline_external))
            continue;
        code("; allocation function %u begin\n", f->id);
        if (frame_address_visible(f->body))
            code("%s", frame_address_marker);
        at = cg.length;
        emit_function(f);

        /* These passes currently treat arithmetic scratch as dead at a C
         * return; an eight-byte result deliberately lives there across it. */
        if (!f->uses_wide) {
            if (!volatile_statements(f->body))
                drop_reloads(at);
            drop_push_pairs(at);
            merge_byte_stores(at);
            if (stack_frames(f, at) && lp_prune_before_frames(f, at))
                stack_frames(f, at);
            line_passes(f, at);
        } else
            lp_wide_runtime_exit(f, at);

        /* Summarized last: line passes may give the function workspace words */
        dp_summarize(f, at);
        emit_block_copy_payloads(at);
        if (f->symbol->interrupt)
            interrupt_statement_lvalues(f->body);
        code("; allocation function %u end\n", f->id);
    }
    bank_emit();
    emit_near_library();

    for (i = 0; i < p->symbol_count; ++i)
        if (p->symbols[i].adapter_used)
            code(".import %s%s\n",
                 wide_scalar(value_type(p->symbols[i].type)) ? "__fnptr64_" : "__fnptr_",
                 p->symbols[i].asm_name);

    for (i = 0; i < p->symbol_count; ++i) {
        Symbol *s = &p->symbols[i];
        if (!s->owner && s->used &&
            (!s->defined ||
             (s->function && s->inline_hint && !s->internal && !s->inline_external)) &&
            !lto_provided_function(p, s))
            code(".import%s _%s\n", s->dpage ? "zp" : "", s->asm_name);
    }

    /* A zero-byte segment records an unqualified object reference in the
     * ca65 object. Manual links can check selected prebuilt members too. */
    for (i = 0; i < p->symbol_count; ++i) {
        Symbol *s = &p->symbols[i];
        if (!s->owner && !s->function && !s->defined && s->used && !s->wram)
            code(".segment \"ZICC_WRAM_UNQUAL_%s\"\n", s->asm_name);
    }

    for (i = 0; i < p->symbol_count; ++i) {
        Symbol *s = &p->symbols[i];
        const char *kind;
        if (!s->wram || s->wram >= WRAM_SRAM_FIRST || s->owner || (!s->defined && !s->used))
            continue;
        kind = s->wram == WRAM_HIRAM ? "H" : "X";
        if (!s->defined) {
            code(".import __zicc_wram_%s_%s: far\n", kind, s->asm_name);
            if (width(s->type))
                code(
                    ".assert __zicc_wram_%s_%s = %u, lderror, \"conflicting WRAM object extent\"\n",
                    kind, s->asm_name, width(s->type));
        }
        if (s->wram_near) {
            if (!s->defined)
                code(".assert _%s >= $7E0000 .and _%s + __zicc_wram_%s_%s <= $7F0000, lderror, "
                     "\"invalid near WRAM placement\"\n",
                     s->asm_name, s->asm_name, kind, s->asm_name);
            else
                code(".assert _%s >= $7E0000 .and _%s + %u <= $7F0000, lderror, \"invalid near "
                     "WRAM placement\"\n",
                     s->asm_name, s->asm_name, width(s->type));
        }
    }
    int sram_bounds = 0;

    for (i = 0; i < p->symbol_count; ++i) {
        Symbol *s = &p->symbols[i];
        if (s->wram < WRAM_SRAM_FIRST || s->owner ||
            (!s->defined && !s->used && !s->placement_used))
            continue;
        if (!sram_bounds) {
            code(".import __sram_first_bank, __sram_window_size, __sram_capacity: far\n");
            code(".assert __sram_first_bank = %u .and __sram_window_size = %u .and __sram_capacity "
                 "= %u, "
                 "lderror, \"SRAM declaration was compiled with a different cartridge layout\"\n",
                 sram_first_bank, sram_window_size, sram_capacity);
            sram_bounds = 1;
        }
        if (!s->defined) {
            code(".import __zicc_sram_window_%s: absolute, __zicc_sram_bound_%s: far, "
                 "__zicc_object_size_%s: far\n",
                 s->asm_name, s->asm_name, s->asm_name);
            code(".assert __zicc_sram_window_%s = %u .and __zicc_sram_bound_%s = %u .and "
                 "__zicc_object_size_%s = %u, "
                 "lderror, \"conflicting SRAM declaration for %s\"\n",
                 s->asm_name, (unsigned)(s->wram - WRAM_SRAM_FIRST), s->asm_name, s->type.array,
                 s->asm_name, width(s->type), s->name);
        }
    }
    int dp_bounds = 0;

    for (i = 0; i < p->symbol_count; ++i) {
        Symbol *s = &p->symbols[i];
        if (s->owner || !s->dpage || !s->type.pointers || s->type.array ||
            (!s->defined && !s->used))
            continue;
        if (!dp_bounds) {
            code(".import __DP_START__, __DP_SIZE__\n");
            dp_bounds = 1;
        }
        code(".assert _%s >= __DP_START__ .and _%s + %u <= __DP_START__ + __DP_SIZE__, lderror, "
             "\"__dpage pointer exceeds allocated direct page\"\n",
             s->asm_name, s->asm_name, width(s->type));
    }
    int loram_bounds = 0;

    for (i = 0; i < p->symbol_count; ++i) {
        Symbol *s = &p->symbols[i];
        if (s->owner || s->function || !s->loram || (!s->defined && !s->used))
            continue;
        if (!loram_bounds) {
            code(".import __NEAR_START__\n");
            loram_bounds = 1;
        }
        if (!s->defined)
            code(".import __zicc_object_size_%s\n", s->asm_name);
        code(".assert _%s >= __NEAR_START__ .and _%s + __zicc_object_size_%s <= $7E2000, lderror, "
             "\"__loram object %s exceeds available LoRAM\"\n",
             s->asm_name, s->asm_name, s->asm_name, s->name);
    }

    /* Speculative emission and later line passes may remove every workspace
     * reference. Do not keep an otherwise unused runtime archive member. */
    if (cg.arithmetic && (strstr(cg.assembly, "__arith_lhs") || strstr(cg.assembly, "__arith_rhs")))
        code(".importzp __arith_lhs, __arith_rhs\n");
    if (strstr(cg.assembly, "__fp_round_mode"))
        code(".import __fp_round_mode\n");
    if (strstr(cg.assembly, "a:.loword(__fp_exceptions)"))
        code(".import __fp_exceptions\n");

    for (i = 0; i < cg.helper_count; ++i)
        code(".import %s\n", cg.helpers[i]);
    if (cg.require_float_format)
        code(".import __require_float_format\n.assert __require_float_format <> 0, lderror, "
             "\"float formatter is unavailable\"\n");
    if (cg.require_int64_format)
        code(".import __require_int64_format\n.assert __require_int64_format <> 0, lderror, "
             "\"64-bit integer formatter is unavailable\"\n");
    code(".segment \"RODATA\"\n");

    for (string = p->strings; string; string = string->next)
        if (string->used) {
            /* Literals are read-only and C leaves their sharing unspecified. A
         * literal that ends another (including an identical one) aliases the
         * longest such literal, lowest id first; owners emit the bytes. */
            String *owner = string, *other;
            size_t j;
            for (other = p->strings; other; other = other->next)
                if (other->used && other != string && other->size >= string->size &&
                    !memcmp(other->bytes + other->size - string->size, string->bytes,
                            string->size) &&
                    (other->size > owner->size ||
                     (other->size == owner->size && other->id < owner->id)))
                    owner = other;
            if (owner != string) {
                code("str_%s_%u = str_%s_%u+$%04X\n", p->unit, string->id, p->unit, owner->id,
                     (unsigned)(owner->size - string->size));
                continue;
            }
            code("str_%s_%u:\n", p->unit, string->id);
            for (j = 0; j < string->size; ++j) {
                if (!(j % 16))
                    code("    .byte ");
                else
                    code(",");
                code("$%02X", string->bytes[j]);
                if (j % 16 == 15 || j + 1 == string->size)
                    code("\n");
            }
        }
    near_relocations();
    if (!relax_assembly(out, cg.assembly, p->unit, !p->no_branch_relaxation))
        exit(EXIT_FAILURE);
    free(cg.assembly);
}
