/* Loop strength reduction. Keep C indices unchanged and give each invariant
 * base/index pair a private near cursor in the invocation's stack frame. */
/* X-writing instructions of a bound cursor are recorded so the region scan
 * can tell them from any other write to X. */
static void bound_mark(void)
{
    if(cg.bound_mark_count<sizeof cg.bound_marks/sizeof *cg.bound_marks)cg.bound_marks[cg.bound_mark_count++]=cg.length;
    else cg.bound_failed=1;
}
static void bound_emit(const char *instruction,const char *operand)
{
    bound_mark();
    code("    %s%s%s\n",instruction,operand?" ":"",operand?operand:"");
}
/* Add step to the bound X. Up to four INX/DEX (two cycles each) beat
 * TXA/CLC/ADC #/TAX (nine cycles). */
static void bound_step(unsigned step)
{
    unsigned i;step&=0xFFFF;
    if(step<=4)for(i=0;i<step;++i)bound_emit("inx",NULL);
    else if(step>=0xFFFC)for(i=step;i<0x10000;++i)bound_emit("dex",NULL);
    else{code("    txa\n    clc\n    adc #$%04X\n",step);bound_emit("tax",NULL);}
}
static int lftr_dead(Symbol *v);
static int strength_affine(Expr *e,Symbol **index,unsigned *delta)
{
    if(e->kind==EX_CAST&&value_width(e->type)==2&&value_width(e->left->type)==2)
        return strength_affine(e->left,index,delta);
    if(e->kind==EX_OBJECT&&e->type.base==TY_INT&&!e->type.pointers&&!e->type.array){
        *index=e->symbol;*delta=0;return 1;
    }
    if(e->kind==EX_BINARY&&(e->op=='+'||e->op=='-')&&reg_width(e->type)==2&&
       e->right->kind==EX_INT&&!e->right->type.pointers&&e->right->type.base!=TY_FLOAT&&
       strength_affine(e->left,index,delta)){
        *delta=(*delta+(e->op=='+'?e->right->value:0u-e->right->value))&0xFFFF;return 1;
    }
    return 0;
}
static InductionCursor *strength_find(Symbol *base,Symbol *index)
{
    unsigned i;for(i=0;i<cg.cursor_count;++i)
        if(cg.cursors[i].base==base&&cg.cursors[i].index==index)return &cg.cursors[i];
    return NULL;
}
static InductionCursor *strength_pointer_plan(Expr *e,unsigned *delta)
{
    Symbol *index;InductionCursor *c;
    if(e->kind!=EX_BINARY||e->op!='+'||e->left->kind!=EX_OBJECT||
       !strength_affine(e->right,&index,delta))return NULL;
    c=strength_find(e->left->symbol,index);if(!c)return NULL;
    *delta=(*delta*c->scale)&0xFFFF;return c;
}
static int strength_cursor_reads_expr(Expr *e,InductionCursor *c)
{
    unsigned i,delta;
    if(!e||volatile_expression(e))return 0;
    if(e->kind==EX_ASSIGN){
        IndexedOperand operand;
        if(indexed_operand(e->left,&operand))
            return strength_cursor_reads_expr(e->right,c);
    }
    if(e->kind==EX_PRE||e->kind==EX_POST){
        IndexedOperand operand;
        if(indexed_operand(e->left,&operand))return 0;
    }
    if(e->kind==EX_MEMBER||e->kind==EX_DEREF){
        IndexedOperand operand;
        if(indexed_operand(e,&operand))return 0;
    }
    InductionCursor *p=strength_pointer_plan(e,&delta);
    if(p&&p->base==c->base&&p->index==c->index)return 1;
    if(strength_cursor_reads_expr(e->left,c)||strength_cursor_reads_expr(e->right,c)||
       strength_cursor_reads_expr(e->third,c))return 1;
    for(i=0;i<e->arg_count;++i)if(strength_cursor_reads_expr(e->args[i],c))return 1;
    return 0;
}
static int strength_cursor_reads(Statement *s,InductionCursor *c)
{
    for(;s;s=s->next)
        if(strength_cursor_reads_expr(s->expression,c)||
           strength_cursor_reads_expr(s->step,c)||
           strength_cursor_reads(s->initial,c)||
           strength_cursor_reads(s->body,c)||
           strength_cursor_reads(s->alternate,c))return 1;
    return 0;
}
static int strength_cursor_read_count_expr(Expr *e,InductionCursor *c)
{
    unsigned i,delta,count=0;
    if(!e||volatile_expression(e))return 0;
    if(e->kind==EX_ASSIGN){
        IndexedOperand operand;
        if(indexed_operand(e->left,&operand))
            return strength_cursor_read_count_expr(e->right,c);
    }
    if(e->kind==EX_PRE||e->kind==EX_POST){
        IndexedOperand operand;
        if(indexed_operand(e->left,&operand))return 0;
    }
    if(e->kind==EX_MEMBER||e->kind==EX_DEREF){
        IndexedOperand operand;
        if(indexed_operand(e,&operand))return 0;
    }
    InductionCursor *p=strength_pointer_plan(e,&delta);
    if(p&&p->base==c->base&&p->index==c->index)count=1;
    count+=strength_cursor_read_count_expr(e->left,c)+strength_cursor_read_count_expr(e->right,c)+
           strength_cursor_read_count_expr(e->third,c);
    for(i=0;i<e->arg_count;++i)count+=strength_cursor_read_count_expr(e->args[i],c);
    return (int)count;
}
static int strength_cursor_read_count(Statement *s,InductionCursor *c)
{
    int count=0;
    for(;s;s=s->next)
        count+=strength_cursor_read_count_expr(s->expression,c)+
               strength_cursor_read_count_expr(s->step,c)+
               strength_cursor_read_count(s->initial,c)+
               strength_cursor_read_count(s->body,c)+
               strength_cursor_read_count(s->alternate,c);
    return count;
}
static int strength_has_step_expr(Expr *e,Symbol *index)
{
    unsigned i;
    if(!e)return 0;
    if((e->kind==EX_PRE||e->kind==EX_POST)&&
       e->left->kind==EX_OBJECT&&e->left->symbol==index)return 1;
    if(e->kind==EX_ASSIGN&&e->left->kind==EX_OBJECT&&e->left->symbol==index&&
       (e->op||expression_references(e->right,index)))return 1;
    if(strength_has_step_expr(e->left,index)||strength_has_step_expr(e->right,index)||
       strength_has_step_expr(e->third,index))return 1;
    for(i=0;i<e->arg_count;++i)if(strength_has_step_expr(e->args[i],index))return 1;
    return 0;
}
static int strength_has_step(Statement *s,Symbol *index,unsigned depth)
{
    for(;s;s=s->next){
        unsigned nested=depth+(s->kind==ST_FOR||s->kind==ST_WHILE||s->kind==ST_DO);
        if(nested&&(strength_has_step_expr(s->expression,index)||strength_has_step_expr(s->step,index)))return 1;
        if(strength_has_step(s->initial,index,depth)||strength_has_step(s->body,index,nested)||
           strength_has_step(s->alternate,index,nested))return 1;
    }
    return 0;
}
static int strength_cursor_needed(Function *f,InductionCursor *c)
{
    if(strength_cursor_reads(f->body,c))return 1;
    /* Wide functions skip the later line passes that retain scaled indices */
    if(f->uses_wide)return 1;
    if(c->scale<=2&&!c->index->type.is_unsigned&&c->index->scope&&
       !c->base->type.banked&&!(c->base->type.array&&c->base->owner))return 1;
    return 0;
}
static void strength_collect_expr(Expr *e,unsigned depth)
{
    unsigned i,delta;Symbol *index,*base;Type element;
    if(!e||volatile_expression(e))return;
    if(depth&&e->kind==EX_BINARY&&e->op=='+'&&e->left->kind==EX_OBJECT&&
       value_type(e->left->type).pointers&&!far_pointer(value_type(e->left->type))&&strength_affine(e->right,&index,&delta)){
        base=e->left->symbol;element=pointed_type(value_type(base->type));
        if(index->owner==cg.function->id&&
           (base->type.array||(base->owner==cg.function->id&&base->scope==0))&&
           (width(element)==2||width(element)==4||
            ((element.array||structure_object(element))&&width(element)>0))&&!strength_find(base,index)&&cg.cursor_count<32){
            InductionCursor *c=&cg.cursors[cg.cursor_count++];
            c->base=base;c->index=index;c->scale=width(element);
        }
    }
    strength_collect_expr(e->left,depth);strength_collect_expr(e->right,depth);strength_collect_expr(e->third,depth);
    for(i=0;i<e->arg_count;++i)strength_collect_expr(e->args[i],depth);
}
static void strength_collect(Statement *s,unsigned depth)
{
    for(;s;s=s->next){
        unsigned nested=depth+(s->kind==ST_FOR||s->kind==ST_WHILE||s->kind==ST_DO);
        strength_collect(s->initial,depth);strength_collect_expr(s->expression,nested);
        strength_collect_expr(s->step,nested);strength_collect(s->body,nested);strength_collect(s->alternate,nested);
    }
}
static int strength_invalid_expr(Expr *e,InductionCursor *c)
{
    unsigned i;if(!e)return 0;
    if(cg.function->uses_wide&&!wide_address_safe(e)&&
       (expression_references(e,c->index)||expression_references(e,c->base)))return 1;
    if(e->kind==EX_ADDRESS&&e->left->kind==EX_OBJECT&&
       (e->left->symbol==c->index||(!c->base->type.array&&e->left->symbol==c->base)))return 1;
    if((e->kind==EX_ASSIGN||e->kind==EX_PRE||e->kind==EX_POST)&&
       e->left->kind==EX_OBJECT&&e->left->symbol==c->base)return 1;
    if(strength_invalid_expr(e->left,c)||strength_invalid_expr(e->right,c)||strength_invalid_expr(e->third,c))return 1;
    for(i=0;i<e->arg_count;++i)if(strength_invalid_expr(e->args[i],c))return 1;
    return 0;
}
static int strength_invalid(Statement *s,InductionCursor *c)
{
    for(;s;s=s->next)if(strength_invalid_expr(s->expression,c)||strength_invalid_expr(s->step,c)||
        strength_invalid(s->initial,c)||strength_invalid(s->body,c)||strength_invalid(s->alternate,c))return 1;
    return 0;
}
static int strength_writes_expr(Expr *e,Symbol *base)
{
    unsigned i;Expr *address;if(!e)return 0;
    if((e->kind==EX_ASSIGN||e->kind==EX_PRE||e->kind==EX_POST)&&e->left->kind==EX_DEREF){
        address=e->left->left;
        if(address->kind==EX_OBJECT&&address->symbol==base)return 1;
        if(address->kind==EX_BINARY&&(address->op=='+'||address->op=='-')&&
           address->left->kind==EX_OBJECT&&address->left->symbol==base)return 1;
    }
    if(strength_writes_expr(e->left,base)||strength_writes_expr(e->right,base)||strength_writes_expr(e->third,base))return 1;
    for(i=0;i<e->arg_count;++i)if(strength_writes_expr(e->args[i],base))return 1;
    return 0;
}
static int strength_writes(Statement *s,Symbol *base)
{
    for(;s;s=s->next)if(strength_writes_expr(s->expression,base)||strength_writes_expr(s->step,base)||
        strength_writes(s->initial,base)||strength_writes(s->body,base)||strength_writes(s->alternate,base))return 1;
    return 0;
}
/* A cursor rebuilt from a wrapped index on every step adds a second
 * recurrence without eliminating the original one. Prefer direct indexing. */
static int strength_wrapped_step(Statement *s,Symbol *index)
{
    for(;s;s=s->next){
        Expr *assign=s->expression,*rhs,*add;
        Symbol *source;
        unsigned delta;
        uint32_t mask;
        if(assign&&assign->kind==EX_ASSIGN&&!assign->op&&assign->left->kind==EX_OBJECT&&
           assign->left->symbol==index){
            rhs=assign->right;
            while(rhs->kind==EX_CAST&&reg_width(rhs->type)==2&&reg_width(rhs->left->type)==2)
                rhs=rhs->left;
            if(rhs->kind==EX_BINARY&&rhs->op=='&'&&integer_constant(rhs->right,&mask)&&
               mask<65535&&!(mask&(mask+1))){
                add=rhs->left;
                if(strength_affine(add,&source,&delta)&&source==index&&delta)return 1;
            }
        }
        if(strength_wrapped_step(s->initial,index)||strength_wrapped_step(s->body,index)||
           strength_wrapped_step(s->alternate,index))return 1;
    }
    return 0;
}
static void strength_prepare(Function *f)
{
    unsigned i,n=0;cg.cursor_count=0;
    if(cg.parser->no_strength_reduction)return;
    strength_collect(f->body,0);
    for(i=0;i<cg.cursor_count;++i){
        InductionCursor *c=&cg.cursors[i];
        if(!strength_cursor_needed(f,c))continue;
        if(c->index->scope&&!strength_has_step(f->body,c->index,0)&&strength_cursor_read_count(f->body,c)<=1)continue;
        if(strength_invalid(f->body,c)||strength_wrapped_step(f->body,c->index)||f->slots+6>768)continue;
        c->wram=c->base->type.array&&(c->base->dpage||c->base->owner);
        c->offset=f->slots+1;f->slots+=2;cg.cursors[n++]=*c;
    }
    cg.cursor_count=n;if(n)f->frame=f->slots+4;
}
static void strength_adjust(unsigned delta)
{
    delta&=0xFFFF;
    if(delta==1||delta==2){code("    inc a\n");if(delta==2)code("    inc a\n");}
    else if(delta==0xFFFF||delta==0xFFFE){code("    dec a\n");if(delta==0xFFFE)code("    dec a\n");}
    else if(delta)code("    clc\n    adc #$%04X\n",delta);
}
static void strength_add_base(InductionCursor *c)
{
    Symbol *s=c->base;s->used=1;
    if(s->type.array){
        if(s->owner){
            if(cg.dp_homes)cg.dp_failed=1;
            cg.arithmetic=1;code("    sta z:__arith_lhs\n    tya\n    clc\n    adc z:__arith_lhs\n");
            strength_adjust(frame_offset(s->offset));
        }else code("    clc\n    adc #.loword(_%s)\n",s->asm_name);
    }else if(s->owner)code("    clc\n    adc %s\n",frame_operand(s->offset));
    else code("    clc\n    adc %s:_%s\n",s->dpage?"z":"a",s->asm_name);
}
/* Form byte displacements modulo the near pointer width, sharing the costed
 * word constant-multiply selector with ordinary arithmetic and pointer setup. */
static void strength_scale(unsigned scale,Expr *value)
{
    if(!(scale&(scale-1))){while(scale>1){code("    asl a\n");scale>>=1;}}
    else{
        Expr factor={0};
        factor.kind=EX_INT;factor.type=type(TY_INT,0);factor.value=scale;
        if(!word_multiply_loaded(value,&factor,type(TY_INT,0))){
            stage(0,type(TY_INT,0));code("    lda #$%04X\n",scale);
            stage(1,type(TY_INT,0));helper("__mul16");
        }
    }
}
static void strength_sync(Symbol *index,Expr *rhs)
{
    unsigned i,delta=0;Symbol *source=NULL;
    if(rhs)strength_affine(rhs,&source,&delta);
    for(i=0;i<cg.cursor_count;++i)if(cg.cursors[i].index==index){
        InductionCursor *c=&cg.cursors[i],*other=source?strength_find(c->base,source):NULL;
        if(c==cg.bound)cg.bound_failed=1;
        if(other){code("    lda %s\n",frame_operand(other->offset));strength_adjust(delta*c->scale);}
        else if(rhs&&rhs->kind==EX_INT&&rhs->type.base!=TY_FLOAT&&!rhs->type.pointers){
            Expr base={0};base.kind=EX_OBJECT;base.symbol=c->base;base.type=c->base->type;
            if(c->base->type.array)emit_address(&base);else load_symbol(c->base);
            strength_adjust(rhs->value*c->scale);
        }else{
            Expr value={0};value.kind=EX_OBJECT;value.symbol=index;value.type=index->type;
            load_symbol(index);strength_scale(c->scale,&value);strength_add_base(c);
        }
        code("    sta %s\n",frame_operand(c->offset));
    }
}
static void strength_parameters(void)
{
    unsigned i,j;
    for(i=0;i<cg.cursor_count;++i){
        InductionCursor *c=&cg.cursors[i];
        code("; strength cursor %s[%s], stride %u, frame $%04X\n",c->base->name,c->index->name,c->scale,c->offset);
        if(c->index->scope)continue;
        if(!parameter_incoming_live(c->index)){
            code("; cursor entry deferred to defining write\n");continue;
        }
        for(j=0;j<i;++j)if(cg.cursors[j].index==c->index)break;
        if(j==i)strength_sync(c->index,NULL);
    }
}

static int strength_pointer(Expr *e,int in_x)
{
    unsigned delta;InductionCursor *c=strength_pointer_plan(e,&delta);
    if(!c)return 0;
    if(c==cg.bound){
        /* X already holds the cursor plus the region's single displacement */
        if(in_x&&delta==cg.bound_delta)return 1;
        if(!in_x){code("    txa\n");strength_adjust(delta-cg.bound_delta);return 1;}
        cg.bound_failed=1;
    }
    if(in_x&&(delta<=3||delta>=0xFFFD)){
        unsigned i,count=delta<=3?delta:0x10000-delta;
        code("    ldx %s\n",frame_operand(c->offset));
        for(i=0;i<count;++i)code("    %s\n",delta<=3?"inx":"dex");
    }else{
        code("    lda %s\n",frame_operand(c->offset));strength_adjust(delta);if(in_x)code("    tax\n");
    }
    return 1;
}
static int strength_wram_pointer(Expr *e)
{
    Symbol *index;unsigned delta;InductionCursor *c;
    if(cg.parser->no_indexed_dpage||e->kind!=EX_BINARY||e->op!='+'||
       e->left->kind!=EX_OBJECT||!strength_affine(e->right,&index,&delta))return 0;
    c=strength_find(e->left->symbol,index);return c&&c->wram;
}
static int strength_update_cursors_only(Expr *e)
{
    Symbol *index;unsigned i;int is_increment=e->kind==EX_PRE||e->kind==EX_POST;
    if((e->kind!=EX_ASSIGN&&!is_increment)||e->left->kind!=EX_OBJECT)return 0;
    index=e->left->symbol;
    int step_form=is_increment||((e->op=='+'||e->op=='-')&&e->right->kind==EX_INT&&e->right->type.base!=TY_FLOAT);
    if(!step_form)return 0;
    unsigned amount=is_increment?1u:e->right->value;
    if(is_increment?e->op==TOK_DEC:e->op=='-')amount=0u-amount;
    code("; eliminated index %s: cursors only\n",index->name);
    for(i=0;i<cg.cursor_count;++i)if(cg.cursors[i].index==index){
        InductionCursor *c=&cg.cursors[i];unsigned step=amount*c->scale;
        if(c==cg.bound){bound_step(step);continue;}
        code("    lda %s\n",frame_operand(c->offset));strength_adjust(step);code("    sta %s\n",frame_operand(c->offset));
    }
    return 1;
}
static int strength_update(Expr *e,int preserve)
{
    Symbol *index;unsigned i;int tracked=0,is_increment=e->kind==EX_PRE||e->kind==EX_POST;
    if((e->kind!=EX_ASSIGN&&!is_increment)||e->left->kind!=EX_OBJECT)return 0;
    index=e->left->symbol;
    for(i=0;i<cg.cursor_count;++i)if(cg.cursors[i].index==index)tracked=1;
    if(!tracked)return 0;
    if(lftr_dead(index)){
        int step_form=is_increment||((e->op=='+'||e->op=='-')&&e->right->kind==EX_INT&&e->right->type.base!=TY_FLOAT);
        if(!preserve&&step_form){
            unsigned amount=is_increment?1u:e->right->value;
            if(is_increment?e->op==TOK_DEC:e->op=='-')amount=0u-amount;
            code("; eliminated index %s: cursors only\n",index->name);
            for(i=0;i<cg.cursor_count;++i)if(cg.cursors[i].index==index){
                InductionCursor *c=&cg.cursors[i];unsigned step=amount*c->scale;
                if(c==cg.bound){bound_step(step);continue;}
                code("    lda %s\n",frame_operand(c->offset));strength_adjust(step);code("    sta %s\n",frame_operand(c->offset));
            }
            return 1;
        }
        if(!preserve&&!e->op){
            code("; eliminated index %s: cursors only\n",index->name);
            if(e->right->kind==EX_OBJECT){
                /* Cursors without a source cursor are rebuilt from the source
                 * index itself, never from the eliminated home. */
                Symbol *source=e->right->symbol;
                for(i=0;i<cg.cursor_count;++i)if(cg.cursors[i].index==index){
                    InductionCursor *c=&cg.cursors[i],*other=strength_find(c->base,source);
                    if(c==cg.bound)cg.bound_failed=1;
                    if(other)code("    lda %s\n",frame_operand(other->offset));
                    else{load_symbol(source);strength_scale(c->scale,e->right);strength_add_base(c);}
                    code("    sta %s\n",frame_operand(c->offset));
                }
            }else strength_sync(index,e->right);
            return 1;
        }
        cg.lftr_failed=1;
    }
    if(is_increment){
        load_symbol(index);if(preserve&&e->kind==EX_POST)code("    pha\n");
        code("    %s a\n",e->op==TOK_INC?"inc":"dec");store_symbol(index);
        if(preserve&&e->kind==EX_PRE)code("    pha\n");
        for(i=0;i<cg.cursor_count;++i)if(cg.cursors[i].index==index){
            InductionCursor *c=&cg.cursors[i];
            if(c==cg.bound){bound_step(e->op==TOK_INC?c->scale:0u-c->scale);continue;}
            code("    lda %s\n",frame_operand(c->offset));
            strength_adjust(e->op==TOK_INC?c->scale:0u-c->scale);code("    sta %s\n",frame_operand(c->offset));
        }
    }else{
        if(e->op){load_symbol(index);binary_after_left(e->left,e->right,e->op);
            convert_registers(binary_operands(e->left,e->right,e->op),e->type);}
        else emit_value(e->right);
        store_symbol(index);if(preserve)code("    pha\n");
        if((e->op=='+'||e->op=='-')&&e->right->kind==EX_INT&&e->right->type.base!=TY_FLOAT){
            for(i=0;i<cg.cursor_count;++i)if(cg.cursors[i].index==index){
                InductionCursor *c=&cg.cursors[i];unsigned step=e->right->value*c->scale;
                if(c==cg.bound){bound_step(e->op=='+'?step:0u-step);continue;}
                code("    lda %s\n",frame_operand(c->offset));strength_adjust(e->op=='+'?step:0u-step);code("    sta %s\n",frame_operand(c->offset));
            }
        }else strength_sync(index,e->op?NULL:e->right);
    }
    if (preserve) {
        code("    pla\n");
    }
    return 1;
}
