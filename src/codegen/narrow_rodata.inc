/* Narrow internal read-only arrays of small structs whose 16-bit integer
 * fields all fit in 8 bits and are only read as rvalue member accesses. */
static Member *narrow_member_by_offset(Structure *st, unsigned offset)
{
    for (Member *m = st->members; m; m = m->next) {
        if (m->offset == offset && !m->bit_width)
            return m;
    }

    return NULL;
}

static Expr **narrow_match_access(Symbol *s, Expr *e)
{
    Expr *addr;

    if (!e || e->kind != EX_MEMBER || object_volatile(e->type) || e->type.array ||
        e->type.pointers || (e->type.base != TY_INT && e->type.base != TY_CHAR))
        return NULL;

    if (e->op == '.') {
        if (!e->left || e->left->kind != EX_DEREF)
            return NULL;

        addr = e->left->left;
    } else if (e->op == TOK_ARROW) {
        addr = e->left;
    } else
        return NULL;

    if (!addr)
        return NULL;
    if (addr->kind == EX_OBJECT && addr->symbol == s)
        return &e->left;
    if (addr->kind == EX_BINARY && addr->op == '+') {
        if (addr->left && addr->left->kind == EX_OBJECT && addr->left->symbol == s)
            return &addr->right;
        if (addr->right && addr->right->kind == EX_OBJECT && addr->right->symbol == s)
            return &addr->left;
    }

    return NULL;
}

static int narrow_check_expr(Symbol *s, Expr *e, int lvalue)
{
    if (!e)
        return 1;

    if (!lvalue) {
        Expr **idx = narrow_match_access(s, e);

        if (idx) {
            if (!narrow_member_by_offset(s->type.structure, e->value))
                return 0;

            return (*idx == e->left) ? 1 : narrow_check_expr(s, *idx, 0);
        }
    }

    if (e->kind == EX_OBJECT && e->symbol == s)
        return 0;
    if (!narrow_check_expr(s, e->left,
                           e->kind == EX_ADDRESS || e->kind == EX_ASSIGN || e->kind == EX_PRE ||
                               e->kind == EX_POST))
        return 0;
    if (!narrow_check_expr(s, e->right, 0))
        return 0;
    if (!narrow_check_expr(s, e->third, 0))
        return 0;

    for (unsigned i = 0; i < e->arg_count; ++i) {
        if (!narrow_check_expr(s, e->args[i], 0))
            return 0;
    }

    return 1;
}

static int narrow_check_statements(Symbol *s, Statement *st)
{
    for (; st; st = st->next) {
        if (!narrow_check_expr(s, st->expression, 0) || !narrow_check_expr(s, st->step, 0) ||
            !narrow_check_statements(s, st->initial) || !narrow_check_statements(s, st->body) ||
            !narrow_check_statements(s, st->alternate))
            return 0;
    }

    return 1;
}

static void narrow_rewrite_expr(Symbol *s, Structure *old_st, Structure *new_st, unsigned new_tag,
                                Expr **at)
{
    Expr *e = *at;
    Expr **idx;

    if (!e)
        return;

    if ((idx = narrow_match_access(s, e)) != NULL) {
        Member *om = old_st->members, *nm = new_st->members;
        Type orig = e->type;

        if (*idx != e->left)
            narrow_rewrite_expr(s, old_st, new_st, new_tag, idx);

        while (om && nm && om->offset != e->value) {
            om = om->next;
            nm = nm->next;
        }

        Expr *addr = e->op == '.' ? e->left->left : e->left;

        if (addr->kind == EX_OBJECT) {
            addr->type = s->type;
        } else {
            if (addr->left->kind == EX_OBJECT && addr->left->symbol == s)
                addr->left->type = s->type;
            else
                addr->right->type = s->type;

            addr->type = value_type(s->type);
        }

        if (e->op == '.') {
            Type deref_t = pointed_type(value_type(s->type));

            deref_t.banked = e->left->type.banked;
            deref_t.constant = e->left->type.constant;
            e->left->type = deref_t;
        }

        e->value = nm->offset;
        Type nt = nm->type;

        nt.constant = orig.constant;
        nt.banked = orig.banked;
        e->type = nt;

        if (orig.base == TY_INT && nt.base == TY_CHAR) {
            Expr *cast = allocate(sizeof *cast);

            cast->kind = EX_CAST;
            cast->type = unqualified_value(orig);
            cast->type.banked = 0;
            cast->location = e->location;
            cast->left = e;
            *at = cast;
        }

        return;
    }

    narrow_rewrite_expr(s, old_st, new_st, new_tag, &e->left);
    narrow_rewrite_expr(s, old_st, new_st, new_tag, &e->right);
    narrow_rewrite_expr(s, old_st, new_st, new_tag, &e->third);

    for (unsigned i = 0; i < e->arg_count; ++i) {
        narrow_rewrite_expr(s, old_st, new_st, new_tag, &e->args[i]);
    }
}

static void narrow_rewrite_statements(Symbol *s, Structure *old_st, Structure *new_st,
                                      unsigned new_tag, Statement *st)
{
    for (; st; st = st->next) {
        narrow_rewrite_expr(s, old_st, new_st, new_tag, &st->expression);
        narrow_rewrite_expr(s, old_st, new_st, new_tag, &st->step);
        narrow_rewrite_statements(s, old_st, new_st, new_tag, st->initial);
        narrow_rewrite_statements(s, old_st, new_st, new_tag, st->body);
        narrow_rewrite_statements(s, old_st, new_st, new_tag, st->alternate);
    }
}

static void narrow_rodata_struct_arrays(Parser *p)
{
    if (!p || p->no_body_optimizations || p->no_strength_reduction)
        return;

    for (unsigned i = 0; i < p->symbol_count; ++i) {
        Symbol *s = &p->symbols[i];
        Structure *old_st, *new_st;

        unsigned new_size = 0, align = 1, mcount = 0, idx;
        unsigned char can_narrow[64];

        if (!s->internal || s->owner || s->function || !s->defined || !s->initializer ||
            s->relocations || s->loram || s->dpage || s->wram || s->runtime_ram ||
            !object_constant(s->type) || object_volatile(s->type) || !s->type.array ||
            s->type.array == ~0u || s->type.pointers ||
            (s->type.element && s->type.element->array) || s->type.base != TY_STRUCT ||
            !s->type.structure || !s->type.structure->complete || s->type.structure->is_union ||
            s->type.structure->is_enum || p->tag_count >= 64)
            continue;

        old_st = s->type.structure;

        if (!old_st->members || width(s->type) != s->type.array * old_st->size)
            continue;

        int reloc_ref = 0;

        for (unsigned j = 0; j < p->symbol_count && !reloc_ref; ++j) {
            for (Relocation *r = p->symbols[j].relocations; r; r = r->next) {
                if (r->symbol == s) {
                    reloc_ref = 1;
                    break;
                }
            }
        }

        if (reloc_ref)
            continue;

        int ok = 1;

        for (Member *m = old_st->members; m; m = m->next) {
            if (mcount >= 64 || m->bit_width || m->type.pointers || m->type.array ||
                object_volatile(m->type) || (m->type.base != TY_CHAR && m->type.base != TY_INT) ||
                (m->type.base == TY_INT && width(m->type) != 2)) {
                ok = 0;
                break;
            }

            unsigned fw = 1;
            can_narrow[mcount] = 0;

            if (m->type.base == TY_INT) {
                int fits = 1;

                for (unsigned k = 0; k < s->type.array && fits; ++k) {
                    unsigned off = k * old_st->size + m->offset;
                    uint16_t raw =
                        (uint16_t)s->initializer[off] | ((uint16_t)s->initializer[off + 1] << 8);

                    if (m->type.is_unsigned) {
                        if (raw > 255)
                            fits = 0;
                    } else {
                        int16_t sv = (int16_t)raw;

                        if (sv < -128 || sv > 127)
                            fits = 0;
                    }
                }

                if (fits)
                    can_narrow[mcount] = 1;
                else {
                    fw = 2;
                    align = 2;
                }
            }

            if (fw == 2 && (new_size & 1u))
                ++new_size;

            new_size += fw;
            ++mcount;
        }

        if (align == 2 && (new_size & 1u))
            ++new_size;
        if (!ok || !mcount || !new_size || new_size >= old_st->size)
            continue;

        for (Function *f = p->functions; f && ok; f = f->next) {
            if (!narrow_check_statements(s, f->body))
                ok = 0;
        }

        if (!ok)
            continue;

        unsigned new_tag = p->tag_count + 1;
        new_st = &p->tags[p->tag_count++];
        *new_st = *old_st;
        new_st->members = NULL;
        Member **tail = &new_st->members;

        new_size = 0;
        idx = 0;

        for (Member *m = old_st->members; m; m = m->next, ++idx) {
            Member *nm = allocate(sizeof *nm);

            *nm = *m;
            nm->next = NULL;

            if (can_narrow[idx]) {
                nm->type.base = TY_CHAR;
                nm->type.is_short = 0;
                nm->type.is_plain_char = 0;
            }

            unsigned fw = width(nm->type);

            if (fw == 2 && (new_size & 1u))
                ++new_size;

            nm->offset = new_size;
            new_size += fw;
            *tail = nm;
            tail = &nm->next;
        }

        if (align == 2 && (new_size & 1u))
            ++new_size;

        new_st->size = new_size;

        unsigned char *nb = allocate(s->type.array * new_st->size);

        for (unsigned k = 0; k < s->type.array; ++k) {
            for (Member *om = old_st->members, *nm = new_st->members; om && nm;
                 om = om->next, nm = nm->next) {
                unsigned fw = width(nm->type);
                memcpy(nb + k * new_st->size + nm->offset,
                       s->initializer + k * old_st->size + om->offset, fw);
            }
        }

        free(s->initializer);
        s->initializer = nb;
        s->type.tag = new_tag;
        s->type.structure = new_st;

        if (s->type.element) {
            Type *ne = type_copy(*s->type.element);

            ne->tag = new_tag;
            ne->structure = new_st;
            s->type.element = ne;
        }

        for (Function *f = p->functions; f; f = f->next) {
            narrow_rewrite_statements(s, old_st, new_st, new_tag, f->body);
        }
    }
}
