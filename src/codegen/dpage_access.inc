/* Access selection only: __dpage still qualifies the pointer object's storage,
 * never its target or representation. Recognition has no codegen side effects. */
typedef struct {
    Symbol *pointer;
    Expr *index;
    Type transfer;
    unsigned offset,scale,width;
    int far,indexed;
} DpageAccess;

static int dpage_index_bound(Expr *e,unsigned *maximum)
{
    Type t=value_type(e->type);
    if(t.pointers||t.base==TY_FLOAT||!home_rhs_pure(e))return 0;
    if(e->kind==EX_INT){
        int64_t n=t.is_unsigned?e->value:reg_width(t)==4?(int32_t)e->value:(int16_t)e->value;
        if(n<0||n>65535)return 0;
        *maximum=(unsigned)n;return 1;
    }
    if(e->kind==EX_BINARY&&e->op=='&'){
        Expr *mask=e->right->kind==EX_INT?e->right:e->left;
        if(mask->kind==EX_INT&&mask->value<=32767){*maximum=mask->value;return 1;}
    }
    if(t.is_unsigned&&reg_width(t)==2){*maximum=width(t)==1?255:65535;return 1;}
    return 0;
}

static int dpage_access(Expr *e,DpageAccess *out)
{
    DpageAccess d={0};Expr *address,*base,*index=NULL;unsigned offset=0,maximum=0,limit;int pointer=0;
    if(cg.parser->no_direct_dpage||e->type.array||structure_object(e->type))return 0;
    d.width=width(e->type);d.transfer=e->type;
    if(d.width!=1&&d.width!=2&&d.width!=4)return 0;
    if(e->kind==EX_MEMBER){
        address=member_root(e,&offset,&pointer);
        if(!pointer){if(address->kind!=EX_DEREF)return 0;address=address->left;}
    }else if(e->kind==EX_DEREF)address=e->left;
    else return 0;
    base=address;
    if(address->kind==EX_BINARY&&address->op=='+'){
        base=address->left;index=address->right;
        if(!value_type(base->type).pointers){base=address->right;index=address->left;}
    }
    /* Do not strip casts: even an equal-width cast can change pointee scaling
     * or near/far address interpretation. No automatic object is eligible. */
    if(base->kind!=EX_OBJECT||base->type.array||!base->type.pointers)return 0;
    d.pointer=base->symbol;
    if(!d.pointer->dpage||d.pointer->owner||d.pointer->type.banked||object_volatile(d.pointer->type))return 0;
    d.far=far_pointer(value_type(base->type));d.scale=width(pointed_type(value_type(base->type)));
    if(d.far!=!!e->type.banked||!d.scale)return 0;
    /* Whole-loop/address-cursor selectors own their established address homes.
     * Do not recover an index they deliberately eliminated or bypass a cursor. */
    if(d.far&&(cg.affine_active||bound_state.cursor||cg.cursor_count||lftr_state.active||cg.dead_index_count))return 0;
    limit=d.width==4?65533:65535;
    if(offset>limit)return 0;
    if(index){
        if(!dpage_index_bound(index,&maximum)||maximum>(limit-offset)/d.scale)return 0;
        if(index->kind==EX_INT)offset+=maximum*d.scale;
        else d.index=index;
    }
    /* Near pointer arithmetic wraps its base before the transfer. Indirect,Y
     * can instead carry into the next bank. Nonzero near offsets also cost
     * more than the existing X-based member lowering. Near wide loads likewise
     * lose after the required Y save/restore; leave all three on fallback. */
    if(!d.far&&(offset||d.index||d.width==4))return 0;
    d.offset=offset;d.indexed=offset||d.index||d.width==4;
    *out=d;return 1;
}

static void dpage_operand(DpageAccess *d,const char *instruction,int indexed)
{
    code("    %s %c_%s%c%s\n",instruction,d->far?'[':'(',d->pointer->asm_name,d->far?']':')',indexed?",y":"");
}

static void dpage_displacement(DpageAccess *d)
{
    if(d->index){
        emit_value(d->index);strength_scale(d->scale,d->index);
        if(d->offset)code("    clc\n    adc #$%04X\n",d->offset);
    }else code("    lda #$%04X\n",d->offset);
}

static int direct_dpage_load(Expr *e)
{
    DpageAccess d;
    if(!dpage_access(e,&d))return 0;
    d.pointer->used=1;
    if(d.width==4&&!d.index){
        code("    phy\n");
        if(object_volatile(e->type)){
            if(d.offset)code("    ldy #$%04X\n",d.offset);
            dpage_operand(&d,"lda",d.offset!=0);code("    pha\n    ldy #$%04X\n",d.offset+2);
            dpage_operand(&d,"lda",1);code("    tax\n    pla\n");
        }else{
            code("    ldy #$%04X\n",d.offset+2);dpage_operand(&d,"lda",1);code("    tax\n");
            if(d.offset)code("    ldy #$%04X\n",d.offset);
            dpage_operand(&d,"lda",d.offset!=0);
        }
        code("    ply\n");return 1;
    }
    if(d.indexed){
        if(d.index){dpage_displacement(&d);code("    phy\n    tay\n");}
        else code("    phy\n    ldy #$%04X\n",d.offset);
    }
    if(d.width==4){
        /* Preserve the fallback's low/high volatile ordering and A/X result.
         * The bound proof leaves room for Y+2, even at a bank/24-bit edge. */
        if(object_volatile(e->type)){
            dpage_operand(&d,"lda",1);code("    pha\n    iny\n    iny\n");
            dpage_operand(&d,"lda",1);code("    tax\n    pla\n");
        }else{
            code("    iny\n    iny\n");dpage_operand(&d,"lda",1);
            code("    tax\n    dey\n    dey\n");dpage_operand(&d,"lda",1);
        }
    }else{
        /* Keep the established nonvolatile near-byte LDA/narrow sequence.
         * Far and volatile bytes use exactly one byte-wide target read. */
        int byte=d.width==1&&(d.far||object_volatile(e->type));
        if(byte)code("    sep #$20\n.a8\n");
        dpage_operand(&d,"lda",d.indexed);
        if(byte)code("    rep #$20\n.a16\n");
    }
    if(d.indexed)code("    ply\n");
    narrow_char(e->type);return 1;
}

static int direct_dpage_store(Expr *e)
{
    DpageAccess d;
    if(cg.affine_active||bound_state.cursor||cg.cursor_count||lftr_state.active||cg.dead_index_count)return 0;
    if(e->kind!=EX_ASSIGN||e->op||!dpage_access(e->left,&d)||d.width==4||!home_rhs_pure(e->right))return 0;
    /* Pure index/RHS evaluation cannot change the destination pointer. A
     * single target transfer may alias the pointer itself: address fetch is
     * complete before STA writes. Wide stores cannot make that guarantee. */
    d.pointer->used=1;
    if(d.index){dpage_displacement(&d);push_value(type(TY_INT,0));}
    emit_value(e->right);
    if(d.indexed){
        code("    phy\n");
        if(d.index)code("    pha\n    lda 5,s\n    tay\n    pla\n");else code("    ldy #$%04X\n",d.offset);
    }
    if(d.width==1)code("    sep #$20\n.a8\n");
    dpage_operand(&d,"sta",d.indexed);
    if(d.width==1)code("    rep #$20\n.a16\n");
    if(d.indexed)code("    ply\n");
    if(d.index){code("    plx\n");if(cg.stack_leaf)cg.stack_bias-=2;}
    divmod_written(e->left);return 1;
}

/* A private near cursor in direct page can keep A intact while X addresses
 * the old element and advances to the next one. The pointed-to object
 * cannot alias the unescaped cursor itself. */
static Expr *post_cursor(Expr *e)
{
    Expr *update;
    Symbol *s;
    unsigned word;
    if(!dp_state.homes||cg.parser->no_direct_dpage||cg.numeric_index||cg.retained_index||
       cg.scan_cursor||cg.affine_active||bound_state.cursor||lftr_state.active||
       e->kind!=EX_DEREF||e->type.pointers||e->type.base!=TY_INT||
       width(e->type)!=2||e->type.banked||volatile_expression(e))return NULL;
    update=e->left;
    if(update->kind!=EX_POST||(update->op!=TOK_INC&&update->op!=TOK_DEC)||
       update->left->kind!=EX_OBJECT||far_pointer(value_type(update->type)))return NULL;
    s=update->left->symbol;
    if(!s->offset||!(s->offset&1)||!loop_private(s))return NULL;
    word=(s->offset-1)/2;
    return word<dp_state.words&&dp_state.map[word]?update:NULL;
}
static const char post_cursor_marker[]="; private post-update word cursor\n";
static void post_cursor_transfer(Expr *update,const char *instruction)
{
    Symbol *s=update->left->symbol;
    const char *step=update->op==TOK_INC?"inx":"dex";
    if(!cg.parser->no_line_passes&&!cg.parser->no_register_cursors)code("%s",post_cursor_marker);
    code("    ldx ");array_operand(s,0);
    code("\n    %s a:$0000,x\n    %s\n    %s\n    stx ",instruction,step,step);
    array_operand(s,0);code("\n");
    divmod_written(update->left);
}
static int post_cursor_load(Expr *e)
{
    Expr *update=post_cursor(e);
    if(!update)return 0;
    post_cursor_transfer(update,"lda");
    return 1;
}
static int post_cursor_store(Expr *e)
{
    Expr *update;
    if(e->op||!home_rhs_pure(e->right)||!(update=post_cursor(e->left)))return 0;
    emit_value(e->right);
    post_cursor_transfer(update,"sta");
    divmod_written(e->left);
    return 1;
}
static int post_cursor_binary(Expr *left,Expr *right,int op,Type t)
{
    Expr *update;
    if(t.pointers||t.base!=TY_INT||reg_width(t)!=2||!basic_integer_op(op)||
       !(update=post_cursor(right)))return 0;
    convert_registers(value_type(left->type),t);
    if(op=='+'||op=='-')code("    %s\n",op=='+'?"clc":"sec");
    post_cursor_transfer(update,op=='+'?"adc":op=='-'?"sbc":op=='&'?"and":op=='|'?"ora":"eor");
    return 1;
}

static int near_dpage_binary(Expr *left,Expr *right,int op,Type t)
{
    if(cg.parser->no_direct_dpage||t.pointers||t.base!=TY_INT||!basic_integer_op(op)||
       right->kind!=EX_DEREF||width(right->type)!=2||right->type.banked||
       volatile_expression(right))return 0;
    Expr *pointer=right->left;
    if(pointer->kind!=EX_OBJECT||pointer->type.array||!pointer->type.pointers||
       far_pointer(pointer->type))return 0;
    Symbol *home=pointer->symbol;
    if(home==cg.scan_cursor||home==cg.scalar_first||
       (home->owner?(!mapped_word_home(home)||
        (dp_state.zero_stack&&home->offset>=dp_state.incoming_base)):!home->dpage))return 0;
    convert_registers(value_type(left->type),t);
    if(op=='+'||op=='-')code(op=='+'?"    clc\n":"    sec\n");
    code("    %s (",op=='+'?"adc":op=='-'?"sbc":op=='&'?"and":op=='|'?"ora":"eor");
    if(home->owner)code("__dp_home_%02u",dp_state.map[(home->offset-1)/2]-1u);
    else code("_%s",home->asm_name);
    code(")\n");
    home->used=1;
    return 1;
}
