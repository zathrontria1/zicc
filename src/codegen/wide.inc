/* Select native word operations before falling back to the helper ABI */
static int basic_integer_op(int op)
{
    return op=='+'||op=='-'||op=='&'||op=='|'||op=='^';
}
static int integer_constant(Expr *e,uint32_t *value)
{
    uint32_t v;Type t=e->type;
    if(t.pointers||t.array||t.base==TY_FLOAT)return 0;
    if(e->kind==EX_INT)v=e->value;
    else if(e->kind==EX_CAST){if(!integer_constant(e->left,&v))return 0;}
    else return 0;
    if(t.base==TY_CHAR){v&=255;if(!t.is_unsigned&&(v&128))v|=0xFFFFFF00u;}
    else if(reg_width(t)==2){v&=65535;if(!t.is_unsigned&&(v&32768))v|=0xFFFF0000u;}
    *value=v;return 1;
}
static int known_high_word(Expr *e,uint32_t *high)
{
    uint32_t value;
    if(integer_constant(e,&value)){*high=value>>16;return 1;}
    if(!e->type.pointers&&e->type.base!=TY_FLOAT&&reg_width(e->type)==2&&e->type.is_unsigned){*high=0;return 1;}
    if(e->kind==EX_CAST&&!e->type.pointers&&e->type.base==TY_LONG){
        Type source=value_type(e->left->type);
        if(reg_width(source)==2&&(source.pointers||(known_integer(source)&&source.is_unsigned))){
            *high=0;return 1;
        }
    }
    if(e->kind==EX_BINARY){
        if(e->op==TOK_SHR&&promoted(e->left->type).is_unsigned&&e->right->kind==EX_INT&&
           e->right->value>=16&&e->right->value<32){*high=0;return 1;}
        if(e->op=='&'&&((integer_constant(e->left,&value)&&!(value>>16))||
            (integer_constant(e->right,&value)&&!(value>>16)))){*high=0;return 1;}
    }
    return 0;
}
static int identity_binary_operand(Expr *e,Expr **keep)
{
    Type t;uint32_t lv=0,rv=0,mask;
    if(!e||e->kind!=EX_BINARY)return 0;
    t=binary_operands(e->left,e->right,e->op);
    if(t.base==TY_FLOAT)return 0;
    if(t.pointers){
        if(!value_type(e->right->type).pointers&&integer_constant(e->right,&rv)&&!rv&&
           (e->op=='+'||e->op=='-')){*keep=e->left;return 1;}
        if(!value_type(e->left->type).pointers&&integer_constant(e->left,&lv)&&!lv&&
           e->op=='+'){*keep=e->right;return 1;}
        return 0;
    }
    mask=reg_width(t)==2?65535u:UINT32_MAX;
    if(integer_constant(e->right,&rv)){
        uint32_t m=rv&mask;
        if((!m&&(e->op=='+'||e->op=='-'||e->op=='|'||e->op=='^'||e->op==TOK_SHL||e->op==TOK_SHR))||
           (m==mask&&e->op=='&')||(m==1&&(e->op=='*'||e->op=='/')))
        {*keep=e->left;return 1;}
    }
    if(integer_constant(e->left,&lv)){
        uint32_t m=lv&mask;
        if((!m&&(e->op=='+'||e->op=='|'||e->op=='^'))||
           (m==mask&&e->op=='&')||(m==1&&e->op=='*'))
        {*keep=e->right;return 1;}
    }
    return 0;
}
/* Check or emit a word of an immediate, scalar home or fixed array element.
 * Widened signed word objects need runtime sign extension and use fallback. */
static int direct_operand(Expr *e,Type target,unsigned high,int emit)
{
    if(volatile_expression(e))return 0;
    uint32_t v;Symbol *s;unsigned offset=0;
    if(e->type.pointers||e->type.array||e->type.base==TY_FLOAT){
        if(value_type(e->type).pointers&&!far_pointer(value_type(e->type))&&reg_width(target)==2&&!high){
            s=near_object_address(e,&offset);
            if(s&&!s->owner&&!s->type.banked){
                if(emit){s->used=1;code("#.loword(_%s+$%04X)",s->asm_name,offset);}
                return 1;
            }
        }
        return 0;
    }
    if(integer_constant(e,&v)){
        if (emit) {
            code("#$%04X", (v >> (high ? 16 : 0)) & 65535);
        }
        return 1;
    }
    if(reg_width(target)==2&&!high){
        Expr *sh=e;
        if(sh->kind==EX_CAST&&!sh->type.pointers&&!sh->type.is_bool&&width(sh->type)==2&&
           sh->type.base==TY_INT)sh=sh->left;
        if(sh->kind==EX_BINARY&&sh->op==TOK_SHR&&sh->right->kind==EX_INT&&sh->right->value==16&&
           !sh->left->type.pointers&&width(sh->left->type)==4&&sh->left->type.base==TY_LONG&&
           direct_operand(sh->left,sh->left->type,1,0))
            return direct_operand(sh->left,sh->left->type,1,emit);
    }
    if(e->kind==EX_CAST){
        if(reg_width(e->type)!=reg_width(e->left->type)||e->type.base==TY_CHAR)return 0;
        /* A word cast can change the extension required by a wider use */
        if(reg_width(target)==4&&reg_width(e->type)==2&&
           e->type.is_unsigned!=e->left->type.is_unsigned)return 0;
        return direct_operand(e->left,target,high,emit);
    }
    if(width(e->type)==1)return 0;
    if(reg_width(target)==4&&reg_width(e->type)==2){
        int negative=0;
        if(!e->type.is_unsigned){
            if(e->kind!=EX_OBJECT||!e->known.valid||(e->known.min<0&&e->known.max>=0))return 0;
            negative=e->known.max<0;
        }
        if(high){if(emit)code(negative?"#$FFFF":"#$0000");return 1;}
    }
    s=e->kind==EX_OBJECT?e->symbol:fixed_memory_object(e,&offset);
    if(!s)return 0;
    if(s==cg.scalar_first||s==cg.numeric_index||s==cg.numeric_recurrence||(s==cg.retained_index&&(cg.retained_y==1||cg.retained_y==2)))return 0;
    if(emit){if(s==cg.leaf_count)code("z:__arith_rhs");else array_operand(s,offset+high*2);}
    return 1;
}
static void register_binary(int op,Type t,Expr *right)
{
    const char *instruction=op=='+'?"adc":op=='-'?"sbc":op=='&'?"and":op=='|'?"ora":"eor";
    if(op=='+'||op=='-')code("    %s\n",op=='+'?"clc":"sec");
    code("    %s ",instruction);
    if(!right)code("z:__arith_rhs");
    else if(volatile_expression(right))fixed_memory_word(right,reg_width(t),0,1);
    else direct_operand(right,t,0,1);
    code("\n");
    if(reg_width(t)==4){
        code("    pha\n    txa\n");cg.stack_bias+=2;
        code("    %s ",instruction);
        if(!right)code("z:__arith_rhs+2");
        else if(volatile_expression(right))fixed_memory_word(right,reg_width(t),2,1);
        else direct_operand(right,t,1,1);
        code("\n");
        cg.stack_bias-=2;code("    tax\n    pla\n");
    }
}
/* A contains the surviving source word for a shift of at least 16 bits */
static void large_shift32(int op,Type t,unsigned count)
{
    unsigned i=16;
    if(op==TOK_SHR){
        code("    ldx #0\n");
        if(!t.is_unsigned)code("    cmp #$8000\n    bcc :+\n    ldx #$FFFF\n:\n");
        if(count>=24&&!cg.parser->no_byte_shuffles){
            code("    xba\n    and #$00FF\n");
            if(!t.is_unsigned)code("    eor #$0080\n    sec\n    sbc #$0080\n");
            i=24;
        }
        for(;i<count;++i)code(t.is_unsigned?"    lsr a\n":"    cmp #$8000\n    ror a\n");
    }else{
        if(count>=24&&!cg.parser->no_byte_shuffles){
            code("    xba\n    and #$FF00\n");
            i=24;
        }
        for(;i<count;++i)code("    asl a\n");
        code("    tax\n    lda #0\n");
    }
}
static int direct_large_shift(Expr *e)
{
    Type t;unsigned count,high,offset=0;
    Expr *source,*address;
    if(e->kind!=EX_BINARY||(e->op!=TOK_SHL&&e->op!=TOK_SHR)||e->right->kind!=EX_INT)return 0;
    source=e->left;t=promoted(source->type);count=e->right->value;high=e->op==TOK_SHR;
    if(t.pointers||t.base!=TY_LONG||count>=32)return 0;
    if(high&&count==8&&!cg.parser->no_strength_reduction&&!cg.parser->no_byte_shuffles&&
       !volatile_expression(source)){
        Symbol *home=direct_memory_object(source,&offset);
        if(home&&!home->owner&&!home->type.banked){
            code("    lda ");array_operand(home,offset+2);code("\n    xba\n    and #$00FF\n");
            if(!t.is_unsigned)code("    eor #$0080\n    sec\n    sbc #$0080\n");
            code("    tax\n    lda ");array_operand(home,offset+1);code("\n");
            return 1;
        }
    }
    if(count<16)return 0;
    if(direct_operand(source,t,high,0)){
        code("    lda ");direct_operand(source,t,high,1);code("\n");
    }else{
        if(cg.parser->no_strength_reduction||source->kind!=EX_DEREF||source->type.banked||
           far_pointer(value_type(source->left->type))||volatile_expression(source))return 0;
        /* Evaluate the address even when only one of the two words is needed */
        address=near_displaced_deref(source,&offset);
        if(!address)address=source->left;
        emit_value_x(address);
        code("    lda %s:$%04X,x\n",strength_wram_pointer(address)?"z":"a",offset+2*high);
    }
    large_shift32(e->op,t,count);return 1;
}
static void constant_shift32_mode(int op,Type t,unsigned count,int zero_high)
{
    unsigned i;
    if(!count)return;
    if(count>=16){if(op==TOK_SHR)code("    txa\n");large_shift32(op,t,count);return;}
    if(op!=TOK_SHR&&count>=8&&!cg.parser->no_byte_shuffles){
        unsigned steps=count-8;
        if(zero_high&&!steps){
            code("    pha\n    xba\n    and #$00FF\n    tax\n    pla\n    xba\n    and #$FF00\n");
            return;
        }
        cg.arithmetic=1;
        if(zero_high){
            code("    sta z:__arith_lhs\n    xba\n    and #$00FF\n    sta z:__arith_lhs+2\n");
        }else{
            code("    sta z:__arith_lhs\n    txa\n    xba\n    and #$FF00\n    sta z:__arith_lhs+2\n"
                 "    lda z:__arith_lhs\n    xba\n    and #$00FF\n    ora z:__arith_lhs+2\n    sta z:__arith_lhs+2\n");
        }
        code("    lda z:__arith_lhs\n    xba\n    and #$FF00\n");
        for(i=0;i<steps;++i)code("    asl a\n    rol z:__arith_lhs+2\n");
        code("    ldx z:__arith_lhs+2\n");
        return;
    }
    cg.arithmetic=1;
    if(op==TOK_SHR&&t.is_unsigned&&count>=7&&!cg.parser->no_byte_shuffles){
        code("    sta z:__arith_lhs\n    stx z:__arith_lhs+2\n");
        /* The unaligned middle word is the low word of the byte shift.
         * A seven-bit shift also brings back bit 7 through the carry. */
        if(count==7)code("    xba\n    asl a\n");
        code("    lda z:__arith_lhs+1\n");
        if(count==7)code("    rol a\n");
        code("    sta z:__arith_lhs\n    txa\n    xba\n    and #$00FF\n");
        if(count==7)code("    rol a\n");
        for(i=8;i<count;++i)code("    lsr a\n    ror z:__arith_lhs\n");
        code("    tax\n    lda z:__arith_lhs\n");
        return;
    }
    if(op!=TOK_SHR){
        code("    stx z:__arith_lhs+2\n");
        for(i=0;i<count;++i)code("    asl a\n    rol z:__arith_lhs+2\n");
        code("    ldx z:__arith_lhs+2\n");
    }else if(count==1){
        code("    pha\n    txa\n");code(t.is_unsigned?"    lsr a\n":"    cmp #$8000\n    ror a\n");
        code("    tax\n    pla\n    ror a\n");
    }else{
        code("    sta z:__arith_lhs\n    txa\n");
        int fill=!t.is_unsigned&&count>=3&&!cg.parser->no_strength_reduction;
        for(i=0;i<count;++i){
            code(t.is_unsigned||fill?"    lsr a\n":"    cmp #$8000\n    ror a\n");
            code("    ror z:__arith_lhs\n");
        }
        if(fill){
            /* The original sign now sits below the vacated high bits */
            code("    bit #$%04X\n    beq :+\n    ora #$%04X\n:\n",
                 0x8000u>>count,(0xffffu<<(16-count))&0xffffu);
        }
        code("    tax\n    lda z:__arith_lhs\n");
    }
}
static void constant_shift32(int op,Type t,unsigned count)
{
    constant_shift32_mode(op,t,count,0);
}
static int stage_expression(Expr *e,Type t,unsigned right,int emit)
{
    if(t.base==TY_FLOAT&&!t.pointers){
        int literal=!cg.parser->no_strength_reduction&&e->kind==EX_INT&&
                    e->type.base==TY_FLOAT&&!e->type.pointers;
        int indirect=!cg.parser->no_strength_reduction&&e->kind==EX_DEREF&&!e->type.banked&&
                     e->left->kind==EX_OBJECT&&e->left->type.pointers==1&&
                     !far_pointer(e->left->type)&&!volatile_expression(e);
        const char *slot=right?"rhs":"lhs";
        unsigned part;
        if(!literal&&(value_type(e->type).base!=TY_FLOAT||(!indirect&&!fixed_memory_word(e,4,0,0))))return 0;
        if(!emit)return 1;
        cg.arithmetic=1;
        if(indirect){
            /* Keep X on the source while each word goes into helper scratch */
            const char *mode=strength_wram_pointer(e->left)?"z":"a";
            emit_value_x(e->left);
            code("    lda %s:$0002,x\n    sta z:__arith_%s+2\n"
                 "    lda %s:$0000,x\n    sta z:__arith_%s\n",mode,slot,mode,slot);
            return 1;
        }
        for(part=0;part<4;part+=2){
            if(literal){
                unsigned word=(e->value>>(part*8))&65535;
                if(!word){code("    stz z:__arith_%s+%u\n",slot,part);continue;}
                code("    lda #$%04X",word);
            }else{code("    lda ");fixed_memory_word(e,4,part,1);}
            code("\n    sta z:__arith_%s+%u\n",slot,part);
        }
        return 1;
    }
    if(volatile_expression(e))return 0;
    const char *slot=right?"rhs":"lhs";uint32_t v;unsigned i;
    if(!direct_operand(e,t,0,0)||!direct_operand(e,t,reg_width(t)==4?1:0,0))return 0;
    if(!emit)return 1;
    cg.arithmetic=1;
    if(right&&e->kind==EX_OBJECT&&e->symbol==cg.leaf_count&&reg_width(t)==2)return 1;
    for(i=0;i<reg_width(t)/2;++i){
        if(integer_constant(e,&v)&&!((v>>(i*16))&65535))code("    stz z:__arith_%s+%u\n",slot,i*2);
        else{code("    lda ");direct_operand(e,t,i,1);code("\n    sta z:__arith_%s+%u\n",slot,i*2);}
    }
    return 1;
}
static int staged_binary(Expr *e)
{
    Type t,rhs;int shift=e->op==TOK_SHL||e->op==TOK_SHR,inputs;
    if(e->kind!=EX_BINARY||e->type.pointers||e->type.base==TY_FLOAT||
       (e->op!='*'&&e->op!='/'&&e->op!='%'&&!shift))return 0;
    if(shift&&!cg.parser->no_strength_reduction&&promoted(e->left->type).base==TY_INT&&
       !promoted(e->left->type).pointers)return 0;
    /* Keep the inline constant shift/power-of-two multiply selector */
    if(e->right->kind==EX_INT&&(shift||(e->op=='*'&&e->right->value&&
       !(e->right->value&(e->right->value-1)))))return 0;
    t=binary_operands(e->left,e->right,e->op);rhs=shift?type(TY_INT,0):t;
    if(!stage_expression(e->left,t,0,0)||!stage_expression(e->right,rhs,1,0))return 0;
    inputs=arithmetic_byte_inputs(e->op,t,e->left,e->right);
    if(e->op=='*'&&(inputs==MUL_TWO_BIT_RIGHT||inputs==MUL_TWO_BIT_LEFT)){
        two_bit_word_product(t,inputs,e->left,e->right);return 1;
    }
    stage_expression(e->left,t,0,1);stage_expression(e->right,rhs,1,1);
    binary_loaded(e->op,t,inputs);return 1;
}
/* Delay fixed loads only across arithmetic that cannot write memory or call.
 * In particular a call on the right might change a global on the left. */
static int readonly_integer_expression(Expr *e)
{
    unsigned offset=0;
    if(e->type.pointers||e->type.array||e->type.base==TY_FLOAT)return 0;
    if(e->kind==EX_INT||e->kind==EX_OBJECT)return 1;
    if(e->kind==EX_MEMBER||e->kind==EX_DEREF)return fixed_memory_object(e,&offset)!=NULL;
    if(e->kind==EX_CAST)return readonly_integer_expression(e->left);
    if(e->kind==EX_UNARY&&(e->op=='+'||e->op=='-'||e->op=='~'))
        return readonly_integer_expression(e->left);
    return e->kind==EX_BINARY&&(basic_integer_op(e->op)||e->op=='*'||
        e->op=='/'||e->op=='%'||e->op==TOK_SHL||e->op==TOK_SHR)&&
        readonly_integer_expression(e->left)&&readonly_integer_expression(e->right);
}
static int deferred_binary(Expr *e)
{
    Type t=e->type;
    if(!cg.parser->no_strength_reduction&&t.base==TY_FLOAT&&!t.pointers&&
       (e->op=='+'||e->op=='-'||e->op=='*'||e->op=='/')&&
       stage_expression(e->left,t,0,0)&&!stage_expression(e->right,t,1,0)&&!body_effect(e->right)){
        /* Evaluate the temporary first without reversing the helper operands */
        emit_value(e->right);convert_registers(value_type(e->right->type),t);
        stage(1,t);stage_expression(e->left,t,0,1);
        binary_loaded(e->op,t,0);return 1;
    }
    if(e->kind!=EX_BINARY||t.pointers||t.base!=TY_LONG||
       (e->op!='+'&&e->op!='&'&&e->op!='|'&&e->op!='^')||
       !direct_operand(e->left,t,0,0)||!direct_operand(e->left,t,1,0)||
       (direct_operand(e->right,t,0,0)&&direct_operand(e->right,t,1,0))||
       (e->left->kind!=EX_INT&&!readonly_integer_expression(e->right)))return 0;
    emit_value(e->right);convert_registers(value_type(e->right->type),t);
    register_binary(e->op,t,e->left);return 1;
}
/* Only peel widening integer casts. Truncations and word signedness changes
 * remain in the source expression, determining its eventual extension. */
static Expr *widened_word(Expr *e)
{
    while(e->kind==EX_CAST&&!e->type.pointers&&e->type.base==TY_LONG&&
          !e->left->type.pointers&&e->left->type.base!=TY_FLOAT)e=e->left;
    return !e->type.pointers&&!e->type.array&&e->type.base!=TY_FLOAT&&
        reg_width(e->type)==2?e:NULL;
}
static int widened_word_product(Expr *e)
{
    Expr *left,*right,*first,*second,*other=NULL;Type t=e->type;int swap;uint32_t factor=0;
    Expr left_constant,right_constant;
    if(e->kind!=EX_BINARY||e->op!='*'||t.pointers||t.base!=TY_LONG)return 0;
    if(integer_constant(e->right,&factor)&&factor&&!(factor&(factor-1)))other=e->left;
    else if(integer_constant(e->left,&factor)&&factor&&!(factor&(factor-1)))other=e->right;
    if(!cg.parser->no_strength_reduction&&other){
        Expr *word=widened_word(other);
        unsigned count=0;uint32_t hi=0;int zero_high;
        if(word)other=word;
        zero_high=(known_high_word(other,&hi)&&!hi)||
            (other->known.valid&&other->known.min>=0&&reg_width(other->type)<=2);
        while((UINT32_C(1)<<count)<factor&&count<31)++count;
        emit_value(other);
        if(!count){
            if(zero_high&&reg_width(other->type)<=2)code("    ldx #$0000\n");
            else convert_registers(value_type(other->type),t);
            return 1;
        }
        if(count>=16||(zero_high&&count>=8&&!cg.parser->no_byte_shuffles)){
            /* Shifts >= 8 with zero high word (and shifts >= 16) overwrite X without reading it */
            if(count>=16)large_shift32(TOK_SHL,t,count);
            else constant_shift32_mode(TOK_SHL,t,count,1);
            return 1;
        }
        if(zero_high&&reg_width(other->type)<=2)code("    ldx #$0000\n");
        else convert_registers(value_type(other->type),t);
        constant_shift32_mode(TOK_SHL,t,count,zero_high);
        return 1;
    }
    left=widened_word(e->left);right=widened_word(e->right);
    if(!cg.parser->no_strength_reduction&&!left&&e->left->kind==EX_INT&&
       integer_constant(e->left,&factor)&&factor<=65535){
        left_constant=*e->left;
        left_constant.type=type(TY_INT,1);
        left=&left_constant;
    }
    if(!cg.parser->no_strength_reduction&&!right&&e->right->kind==EX_INT&&
       integer_constant(e->right,&factor)&&factor<=65535){
        right_constant=*e->right;
        right_constant.type=type(TY_INT,1);
        right=&right_constant;
    }
    if(!left&&!right)return 0;
    first=left?left:e->left;second=right?right:e->right;swap=!left;
    /* Preserve evaluation order even when the word is the right operand.
     * Normalize only the helper's scratch slots, keeping its word in L. */
    emit_value(first);convert_registers(value_type(first->type),t);
    if(direct_operand(second,second->type,0,0)){
        stage(swap?1:0,t);emit_value(second);convert_registers(value_type(second->type),t);stage(swap?0:1,t);
    }else{
        push_value(t);emit_value(second);convert_registers(value_type(second->type),t);
        stage(swap?0:1,t);pop_value(t);stage(swap?1:0,t);
    }
    helper(left&&right?"__mul16wide":"__mul16x32");return 1;
}

static void wide_compare_branch(Expr *e,unsigned yes,unsigned no,unsigned fallthrough);
static Symbol *leaf_parameter(Function *f,unsigned index)
{
    unsigned j;
    for(j=0;j<cg.parser->symbol_count;++j){Symbol *v=&cg.parser->symbols[j];
        if(v->owner==f->id&&v->scope==0&&!strcmp(v->name,f->symbol->param_names[index]))return v;
    }
    return NULL;
}
static int word_register(Expr *e,Symbol *first,Symbol *second)
{
    while(e->kind==EX_CAST&&e->type.base==TY_INT&&!e->type.pointers&&
          e->left->type.base==TY_INT&&!e->left->type.pointers)e=e->left;
    if(e->kind!=EX_OBJECT)return 0;
    if(first&&e->symbol==first)return 1;
    if(second&&e->symbol==second)return 2;
    return 0;
}
static int word_leaf(Function *f)
{
    Statement *s=f->body;Expr *e,*lhs,*rhs;Symbol *fn=f->symbol,*first=NULL,*second=NULL;
    unsigned i;int left,right;const char *instruction;
    if(s->kind==ST_BLOCK)s=s->body;
    if(!s||s->next||s->kind!=ST_RETURN||!s->expression||fn->param_count<0||fn->param_count>2||
       !strcmp(fn->name,"main")||f->slots!=(unsigned)fn->param_count*2)return 0;
    e=s->expression;
    while(e->kind==EX_CAST&&e->type.base==TY_INT&&!e->type.pointers&&
          e->left->type.base==TY_INT&&!e->left->type.pointers)e=e->left;
    if(e->kind!=EX_BINARY||e->type.base!=TY_INT||e->type.pointers||!basic_integer_op(e->op))return 0;
    for(i=0;i<(unsigned)fn->param_count;++i)
        if(fn->params[i].base!=TY_INT||fn->params[i].pointers)return 0;
    if(fn->param_count>0)first=leaf_parameter(f,0);
    if(fn->param_count>1)second=leaf_parameter(f,1);
    left=word_register(e->left,first,second);right=word_register(e->right,first,second);
    if((!left&&!direct_operand(e->left,e->type,0,0))||
       (!right&&!direct_operand(e->right,e->type,0,0)))return 0;
    lhs=e->left;rhs=e->right;
    if(e->op!='-'&&right&&(!left||(left==1&&right==2))){
        Expr *swap=lhs;int reg=left;lhs=rhs;rhs=swap;left=right;right=reg;
    }
    instruction=e->op=='+'?"adc":e->op=='-'?"sbc":e->op=='&'?"and":e->op=='|'?"ora":"eor";
    code(".segment \"CODE\"\n.export _%s\n_%s:\n; native word leaf\n",fn->asm_name,fn->asm_name);
    if(right){
        cg.arithmetic=1;code("    %s z:__arith_rhs\n",right==1?"stx":"sta");
    }
    if(left==1)code("    txa\n");
    else if(!left){code("    lda ");direct_operand(lhs,e->type,0,1);code("\n");}
    if(e->op=='+'||e->op=='-')code("    %s\n",e->op=='+'?"clc":"sec");
    code("    %s ",instruction);
    if(right)code("z:__arith_rhs");else direct_operand(rhs,e->type,0,1);code("\n");
    code("    rts\n__size_%s = * - _%s\n",fn->asm_name,fn->asm_name);return 1;
}
static int wide_leaf(Function *f)
{
    Statement *s=f->body;Expr *e,*shift=NULL;Symbol *fn=f->symbol,*count=NULL;unsigned i,j,slots=0,offset=3+cg.parser->long_return;
    if(s->kind==ST_BLOCK)s=s->body;
    if(!s||s->next||s->kind!=ST_RETURN||!s->expression)return 0;
    e=s->expression;
    if(e->kind!=EX_BINARY||e->type.base!=TY_LONG||e->type.pointers)return 0;
    if(e->op=='^'&&e->left->kind==EX_BINARY&&e->right->kind==EX_BINARY&&
       ((e->left->op==TOK_SHL&&e->right->op==TOK_SHR)||(e->left->op==TOK_SHR&&e->right->op==TOK_SHL))&&
       e->left->left->kind==EX_OBJECT&&e->right->left->kind==EX_OBJECT&&
       e->left->left->symbol==e->right->left->symbol&&
       e->left->right->kind==EX_OBJECT&&e->right->right->kind==EX_OBJECT&&
       e->left->right->symbol==e->right->right->symbol)shift=e->left;
    else if(e->op==TOK_SHL||e->op==TOK_SHR)shift=e;
    if(shift&&shift->right->kind==EX_OBJECT){
        count=shift->right->symbol;
        if(fn->param_count!=2||reg_width(fn->params[0])!=4||reg_width(fn->params[1])!=2||
           count->owner!=f->id||count->scope||strcmp(count->name,fn->param_names[1])||
           shift->left->kind!=EX_OBJECT||shift->left->symbol->owner!=f->id||
           strcmp(shift->left->symbol->name,fn->param_names[0]))return 0;
    }else{
        if(!basic_integer_op(e->op)&&e->op!='*'&&e->op!='/'&&e->op!='%'&& !shift)return 0;
        if(!direct_operand(e->left,e->type,0,0)||!direct_operand(e->left,e->type,1,0)||
           !direct_operand(e->right,e->type,0,0)||!direct_operand(e->right,e->type,1,0))return 0;
    }
    for(i=0;i<(unsigned)fn->param_count;++i){
        if(reg_width(fn->params[i])!=4&&!(count&&i==1))return 0;
        slots+=reg_width(fn->params[i]);
    }
    if(f->slots!=slots||!strcmp(fn->name,"main"))return 0;
    for(i=0;i<(unsigned)fn->param_count;++i){
        if(count&&i==1)continue;
        for(j=0;j<cg.parser->symbol_count;++j){Symbol *v=&cg.parser->symbols[j];
            if(v->owner==f->id&&v->scope==0&&!strcmp(v->name,fn->param_names[i])){v->offset=offset;break;}
        }
        offset+=4;
    }
    cg.stack_leaf=1;cg.stack_bias=0;
    cg.leaf_count=count;
    code(".segment \"CODE\"\n.export _%s\n_%s:\n; native stack leaf\n",fn->asm_name,fn->asm_name);
    if(count){cg.arithmetic=1;code("    sta z:__arith_rhs\n    stz z:__arith_rhs+2\n");}
    if(!shift&&basic_integer_op(e->op)){
        const char *instruction=e->op=='+'?"adc":e->op=='-'?"sbc":e->op=='&'?"and":e->op=='|'?"ora":"eor";
        code("    lda ");direct_operand(e->left,e->type,0,1);code("\n");
        if(e->op=='+'||e->op=='-')code("    %s\n",e->op=='+'?"clc":"sec");
        code("    %s ",instruction);direct_operand(e->right,e->type,0,1);code("\n    pha\n");
        cg.stack_bias+=2;
        code("    lda ");direct_operand(e->left,e->type,1,1);code("\n    %s ",instruction);
        direct_operand(e->right,e->type,1,1);code("\n    tax\n    pla\n");cg.stack_bias-=2;
    }else emit_value(e);
    code("    rts\n__size_%s = * - _%s\n",fn->asm_name,fn->asm_name);
    cg.stack_leaf=0;cg.leaf_count=NULL;return 1;
}
