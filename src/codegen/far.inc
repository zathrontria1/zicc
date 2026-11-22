/* An evaluated far lvalue is A:low16/X:bank. Recursive evaluations keep
 * addresses on their own stack; DP scratch is live only in leaf transfers. */
/* Emit a DP long-indirect load; byte accesses always keep an 8-bit bus read */
static void emit_far_dp_load(const char *home,Type t,int indexed)
{
    int narrow=width(t)==1;
    if(narrow)code("    sep #$20\n.a8\n");
    code("    lda [%s]%s\n",home,indexed?",y":"");
    if(narrow)code("    rep #$20\n.a16\n");
}
static void far_load(Type t)
{
    cg.arithmetic=1;code("    sta z:__arith_lhs\n    stx z:__arith_lhs+2\n");
    if(width(t)==1){emit_far_dp_load("__arith_lhs",t,0);narrow_char(t);}
    else if(object_volatile(t)&&reg_width(t)==4)code("    phy\n    lda [__arith_lhs]\n    pha\n    ldy #2\n    lda [__arith_lhs],y\n    tax\n    pla\n    ply\n");
    else if(reg_width(t)==4)code("    phy\n    ldy #2\n    lda [__arith_lhs],y\n    tax\n    lda [__arith_lhs]\n    ply\n");
    else code("    lda [__arith_lhs]\n");
}
static void far_store(Type t,unsigned skip)
{
    stage(1,t);
    code("    lda %u,s\n    sta z:__arith_lhs\n    lda %u,s\n    sta z:__arith_lhs+2\n    lda z:__arith_rhs\n",skip+1,skip+3);
    if(width(t)==1)code("    sep #$20\n.a8\n");
    code("    sta [__arith_lhs]\n");
    if(width(t)==1)code("    rep #$20\n.a16\n");
    if(reg_width(t)==4)code("    phy\n    ldy #2\n    txa\n    sta [__arith_lhs],y\n    ply\n    lda z:__arith_rhs\n");
}
/* A named ROM object has a fixed full base. A valid subscript is contained
 * in that object, so its byte displacement fits in the 16-bit X register. */
/* Recover a declared ROM array through far pointer casts and additions.
 * Keep the dynamic term separate from the byte displacement. A valid access
 * within the declared object fits in X even when the term itself is signed. */
static Symbol *rom_index_base(Expr *address, Expr **index, unsigned *scale, int64_t *offset)
{
    Type t=value_type(address->type);
    Expr *term;
    unsigned stride;
    int64_t n;
    if(address->kind==EX_OBJECT&&address->type.array&&address->type.banked&&!address->symbol->wram&&
       width(address->type)<=65536)return address->symbol;
    if(!far_pointer(t))return NULL;
    if(address->kind==EX_CAST&&far_pointer(value_type(address->left->type)))
        return rom_index_base(address->left,index,scale,offset);
    if(address->kind!=EX_BINARY||(address->op!='+'&&address->op!='-')||
       !far_pointer(value_type(address->left->type)))return NULL;
    term=address->right;
    if(term->type.pointers||term->type.array||term->type.base==TY_FLOAT)return NULL;
    stride=width(pointed_type(value_type(address->left->type)));
    if(!stride||stride>65535)return NULL;
    if(term->kind==EX_INT){
        n=term->type.is_unsigned?(int64_t)term->value:
            reg_width(term->type)==4?(int32_t)term->value:(int16_t)term->value;
        *offset+=(address->op=='+'?n:-n)*stride;
    }else{
        if(*index||address->op!='+'||reg_width(term->type)!=2)return NULL;
        *index=term;*scale=stride;
    }
    return rom_index_base(address->left,index,scale,offset);
}
static const char *symbol_load_operand(Symbol *s, unsigned offset)
{
    static char buf[32];
    unsigned word=(s->offset+offset-1)/2;
    if(s->owner){
        if(cg.dp_homes&&cg.dp_zero_stack&&s->offset+offset>=cg.dp_incoming_base){
            snprintf(buf,sizeof buf,"a:$%04X,y",s->offset+offset-cg.dp_incoming_base+5+cg.parser->long_return);
            return buf;
        }
        if(cg.dp_homes&&s->offset&&word<cg.dp_words&&cg.dp_map[word]&&!((s->offset+offset-1)&1)){
            snprintf(buf,sizeof buf,"z:__dp_home_%02u",cg.dp_map[word]-1u);
            return buf;
        }
        snprintf(buf,sizeof buf,"a:$%04X,y",frame_offset(s->offset+offset));
        return buf;
    }
    if(s->dpage){
        if(offset)snprintf(buf,sizeof buf,"z:_%s+$%04X",s->asm_name,offset);
        else snprintf(buf,sizeof buf,"z:_%s",s->asm_name);
        return buf;
    }
    if(s->type.banked){
        if(offset)snprintf(buf,sizeof buf,"f:_%s+$%04X",s->asm_name,offset);
        else snprintf(buf,sizeof buf,"f:_%s",s->asm_name);
        return buf;
    }
    if(offset)snprintf(buf,sizeof buf,"a:.loword(_%s+$%04X)",s->asm_name,offset);
    else snprintf(buf,sizeof buf,"a:.loword(_%s)",s->asm_name);
    return buf;
}
static int far_base_in_arith_lhs(Expr *base)
{
    size_t at=cg.length,length;
    Symbol *s;
    char target[64];
    int n;
    if(!base||base->kind!=EX_OBJECT||(base->type.array&&base->symbol->wram))return 0;
    s=base->symbol;
    if(object_volatile(base->type)||cg.scan_cursor)return 0;
    n=snprintf(target,sizeof target,"    lda %s",symbol_load_operand(s,0));
    while(at){
        at=previous_instruction(at,&length);
        if(!length)return 0;
        if(length>=23&&(!strncmp(cg.assembly+at,"    stx z:__arith_lhs+2",23)||
                        !strncmp(cg.assembly+at,"    sta z:__arith_lhs+2",23))){
            size_t p1_at,p1_len,p2_at,p2_len;
            p1_at=previous_instruction(at,&p1_len);
            p2_at=previous_instruction(p1_at,&p2_len);
            if(p1_len>=21&&!strncmp(cg.assembly+p1_at,"    sta z:__arith_lhs",21)){
                if(p2_len>=(size_t)n&&!strncmp(cg.assembly+p2_at,target,n))return 1;
                if(s->owner&&cg.stack_leaf&&p2_len>8&&!strncmp(cg.assembly+p2_at,"    lda ",8)){
                    unsigned off=(unsigned)atoi(cg.assembly+p2_at+8);
                    if(off>=s->offset&&!((off-s->offset)&1))return 1;
                }
            }
            return 0;
        }
        if(length>=21&&!strncmp(cg.assembly+at,"    sta z:__arith_lhs",21)){
            size_t prev_at,prev_len;
            prev_at=previous_instruction(at,&prev_len);
            if(prev_len>=(size_t)n&&!strncmp(cg.assembly+prev_at,target,n))return 1;
            if(s->owner&&cg.stack_leaf&&prev_len>8&&!strncmp(cg.assembly+prev_at,"    lda ",8)){
                unsigned off=(unsigned)atoi(cg.assembly+prev_at+8);
                if(off>=s->offset&&!((off-s->offset)&1))return 1;
            }
            return 0;
        }
        if(cg.assembly[at]=='c'&&!strncmp(cg.assembly+at,"cg_",3))return 0;
        if(cg.assembly[at]==':'||cg.assembly[at]=='_')return 0;
        if(!strncmp(cg.assembly+at,"    jsr ",8)||!strncmp(cg.assembly+at,"    jsl ",8))return 0;
        if(!strncmp(cg.assembly+at,"    jmp ",8)||(length>4&&cg.assembly[at+4]=='b'))return 0;
        if(length>=21&&!memcmp(cg.assembly+at+8,"z:__arith_lhs",13)){
            const char *p=cg.assembly+at+21;
            if(*p=='+'){
                unsigned off=0;
                while(*++p>='0'&&*p<='9')off=off*10+(*p-'0');
                if(off<4)return 0;
            }else return 0;
        }
        if(s->owner){
            char store[48];int ns=snprintf(store,sizeof store,"    sta %s",symbol_load_operand(s,0));
            if(length>=(size_t)ns&&!strncmp(cg.assembly+at,store,ns))return 0;
            if(cg.stack_leaf&&length>8&&!strncmp(cg.assembly+at,"    sta ",8)){
                unsigned off=(unsigned)atoi(cg.assembly+at+8);
                if(off>=s->offset&&off<s->offset+4)return 0;
            }
        }else{
            char store[48];int ns=snprintf(store,sizeof store,"_%s",s->asm_name);
            if(length>8&&!strncmp(cg.assembly+at,"    sta ",8)){
                size_t k;
                for(k=8;k+ns<=length;++k){
                    if(!memcmp(cg.assembly+at+k,store,ns))return 0;
                }
            }
        }
    }
    return 0;
}
/* An indexed ROM load and a fixed WRAM store leave a private word index
 * intact in X. Stop at any other instruction or control-flow boundary. */
static int rom_index_in_x(Expr *index)
{
    char load[48],store[48];
    size_t at=cg.length,length;
    int n,n_store;
    if(index->kind!=EX_OBJECT||!index->symbol->owner||width(index->type)!=2||
       object_volatile(index->type)||cg.stack_leaf||index->symbol==cg.scan_cursor)return 0;
    n=snprintf(load,sizeof load,"    ldx %s",frame_operand(index->symbol->offset));
    n_store=snprintf(store,sizeof store,"    sta %s",frame_operand(index->symbol->offset));
    while(at){
        at=previous_instruction(at,&length);
        if(length==(size_t)n&&!memcmp(cg.assembly+at,load,length))return 1;
        if(length==7&&!memcmp(cg.assembly+at,"    tax",7)){
            size_t prev_at,prev_len;
            prev_at=previous_instruction(at,&prev_len);
            if(prev_len==(size_t)n_store&&!memcmp(cg.assembly+prev_at,store,prev_len))return 1;
        }
        if(length<19||strncmp(cg.assembly+at,"    sta a:.loword(_",19))return 0;
        at=previous_instruction(at,&length);
        if(length<14||strncmp(cg.assembly+at,"    lda f:_",11)||
           memcmp(cg.assembly+at+length-2,",x",2))return 0;
    }
    return 0;
}
static int rom_load(Expr *e)
{
    Symbol *s;Expr *root=e,*address;unsigned offset=0,scale;int pointer;
    if(volatile_expression(e)||(e->kind!=EX_MEMBER&&e->kind!=EX_DEREF))return 0;
    s=fixed_memory_object(e,&offset);
    if(s&&s->type.banked&&!s->wram){load_array_element(s,offset,e->type);return 1;}
    if(e->kind==EX_MEMBER)root=member_root(e,&offset,&pointer);
    else pointer=0;
    if(pointer)address=root;
    else if(root->kind==EX_DEREF)address=root->left;
    else return 0;
    if(address->kind!=EX_BINARY||address->op!='+'||address->left->kind!=EX_OBJECT||
       !address->left->symbol->type.array||!address->left->symbol->type.banked){
        Expr *index=NULL;
        int64_t displacement=offset;
        if(cg.parser->no_indexed_operands||
           !(s=rom_index_base(address,&index,&scale,&displacement)))return 0;
        if(!index){
            if(displacement<0||(width(s->type)?displacement+width(e->type)>width(s->type):displacement+width(e->type)>65536))return 0;
            load_array_element(s,(unsigned)displacement,e->type);return 1;
        }
        /* For unsigned byte displacements keep a nonnegative constant in
         * the operand. Otherwise form the complete displacement modulo 64K. */
        offset=0;
        if(index->type.is_unsigned&&displacement>=0&&
           (width(s->type)?displacement+width(e->type)<=width(s->type):displacement+width(e->type)<=65536)){
            offset=(unsigned)displacement;displacement=0;
        }
        if(scale==1&&!(displacement&65535)){
            if(!rom_index_in_x(index))emit_value_x(index);
        }
        else{
            emit_value(index);strength_scale(scale,index);
            if(displacement&65535)code("    clc\n    adc #$%04X\n",(unsigned)displacement&65535);
            code("    tax\n");
        }
        goto load_indexed_rom;
    }
    s=address->left->symbol;
    if(!s->type.array||!s->type.banked||s->wram)return 0;
    scale=width(pointed_type(value_type(s->type)));
    if(cg.retained_index&&cg.retained_y!=5&&reg_width(e->type)==2){
        IndexedOperand operand={0};operand.base=s;operand.index=address->right;operand.scale=scale;operand.offset=offset;
        indexed_index_mode(&operand,0);s->used=1;
        code("    lda f:_%s+$%04X,x\n",s->asm_name,operand.offset);
        indexed_finish(&operand);narrow_char(e->type);return 1;
    }
    if(scale==1&&!rom_index_in_x(address->right))emit_value_x(address->right);
    else if(scale!=1){
        emit_value(address->right);strength_scale(scale,address->right);code("    tax\n");
    }
load_indexed_rom:
    s->used=1;
    if(reg_width(e->type)==4)code("    lda f:_%s+$%04X,x\n    pha\n",s->asm_name,offset+2);
    code("    lda f:_%s+$%04X,x\n",s->asm_name,offset);
    if(reg_width(e->type)==4)code("    plx\n");narrow_char(e->type);return 1;
}
/* Constant full addresses need neither a pointer spill nor DP staging. This
 * applies to every bank, including explicit bank-zero hardware registers. */
static void constant_far_load(Type t,uint32_t address)
{
    if(object_volatile(t)&&reg_width(t)==4){code("    lda f:$%06X\n    pha\n    lda f:$%06X\n    tax\n    pla\n",address,(address+2)&0xffffffu);return;}
    if(reg_width(t)==4)code("    lda f:$%06X\n    tax\n",(address+2)&0xffffffu);
    if(width(t)==1)code("    sep #$20\n.a8\n");
    code("    lda f:$%06X\n",address);
    if(width(t)==1)code("    rep #$20\n.a16\n");narrow_char(t);
}
static void constant_far_store(Type t,uint32_t address)
{
    if(width(t)==1)code("    sep #$20\n.a8\n");
    code("    sta f:$%06X\n",address);
    if(width(t)==1)code("    rep #$20\n.a16\n");
    if(reg_width(t)==4)code("    pha\n    txa\n    sta f:$%06X\n    pla\n",(address+2)&0xffffffu);
}
static int constant_far(Expr *e)
{
    Expr *object=(e->kind==EX_ASSIGN||e->kind==EX_PRE||e->kind==EX_POST)?e->left:e;
    uint32_t address;
    if(object->kind!=EX_DEREF||!object->type.banked||object->type.array||
       object->left->kind!=EX_INT||!far_pointer(object->left->type))return 0;
    address=object->left->value&0xffffffu;
    if(e->kind==EX_ASSIGN){
        if(e->op){constant_far_load(e->type,address);binary_after_left(e->left,e->right,e->op);convert_registers(binary_operands(e->left,e->right,e->op),e->type);}
        else emit_value(e->right);
        constant_far_store(e->type,address);divmod_written(e->left);
    }else if(e->kind==EX_PRE||e->kind==EX_POST){
        constant_far_load(e->type,address);if(e->kind==EX_POST)push_value(e->type);
        increment_value(e->type,e->op);constant_far_store(e->type,address);
        if(e->kind==EX_POST)pop_value(e->type);divmod_written(e->left);
    }else if(e->kind==EX_DEREF)constant_far_load(e->type,address);
    else return 0;
    return 1;
}
static int expression_uses_arith_lhs(Expr *e)
{
    unsigned i;
    if(!e)return 0;
    if(e->kind==EX_CALL)return 1;
    if(far_pointer(value_type(e->type)))return 1;
    if(e->kind==EX_DEREF&&far_pointer(value_type(e->left->type)))return 1;
    if(e->kind==EX_MEMBER&&far_pointer(value_type(e->left->type)))return 1;
    if(reg_width(e->type)>2)return 1;
    if(e->kind==EX_BINARY&&(e->op=='*'||e->op=='/'||e->op=='%'))return 1;
    if(expression_uses_arith_lhs(e->left)||expression_uses_arith_lhs(e->right)||expression_uses_arith_lhs(e->third))return 1;
    for(i=0;i<e->arg_count;++i)if(expression_uses_arith_lhs(e->args[i]))return 1;
    return 0;
}
/* Long-indirect,Y supplies the low-word carry into the bank. A negative
 * signed word index is represented in Y modulo 65536, so first subtract
 * one bank from the base. Evaluate both operands before borrowing frame Y;
 * the invocation stack protects the base across nested index evaluations. */
static int indexed_far_byte_load(Expr *e)
{
    Expr *address,*base,*index;Type t;int base_in_lhs;
    if(cg.parser->no_strength_reduction||e->kind!=EX_DEREF||width(e->type)!=1)return 0;
    address=e->left;
    if(address->kind!=EX_BINARY||address->op!='+')return 0;
    base=address->left;index=address->right;
    if(!far_pointer(value_type(base->type))){base=address->right;index=address->left;}
    t=value_type(index->type);
    if(!far_pointer(value_type(base->type))||width(pointed_type(value_type(base->type)))!=1||
       index->kind==EX_INT||t.pointers||t.base==TY_FLOAT||reg_width(t)!=2)return 0;
    base_in_lhs=far_base_in_arith_lhs(base);
    if(base_in_lhs&&!expression_uses_arith_lhs(index)){
        code("; indexed far byte load: word displacement in Y\n");
        emit_value(index);
        code("    phy\n    tay\n");
        emit_far_dp_load("__arith_lhs",e->type,1);
        code("    ply\n");
        narrow_char(e->type);return 1;
    }
    if((base->kind==EX_OBJECT||fixed_memory_word(base,4,0,0))&&
       (fixed_memory_word(index,2,0,0)||!expression_uses_arith_lhs(index))){
        emit_value(base);cg.arithmetic=1;
        code("; indexed far byte load: word displacement in Y\n"
             "    sta z:__arith_lhs\n    stx z:__arith_lhs+2\n");
        emit_value(index);
        if(!t.is_unsigned)code("    tax\n    cpx #$8000\n    bcc :+\n    dec z:__arith_lhs+2\n:\n    phy\n    txy\n");
        else code("    phy\n    tay\n");
        emit_far_dp_load("__arith_lhs",e->type,1);
        code("    ply\n");
        narrow_char(e->type);return 1;
    }
    emit_value(base);push_value(base->type);emit_value(index);
    cg.arithmetic=1;
    code("; indexed far byte load: word displacement in Y\n"
         "    tax\n    pla\n    sta z:__arith_lhs\n    pla\n    sta z:__arith_lhs+2\n");
    if(cg.stack_leaf)cg.stack_bias-=4;
    if(!t.is_unsigned)code("    cpx #$8000\n    bcc :+\n    dec z:__arith_lhs+2\n:\n");
    code("    phy\n    txy\n");
    emit_far_dp_load("__arith_lhs",e->type,1);
    code("    ply\n");
    narrow_char(e->type);return 1;
}
/* A promoted far pointer can be used directly if its words are adjacent */
static const char *far_pointer_dp_home(Expr *base)
{
    Symbol *s;
    unsigned word;
    const char *home;
    if(!cg.dp_homes||base->kind!=EX_OBJECT||!far_pointer(value_type(base->type))||
       !(s=base->symbol)->owner||!s->offset||object_volatile(base->type))return NULL;
    word=(s->offset-1)/2;
    if(word+1>=cg.dp_words||!cg.dp_map[word]||cg.dp_map[word+1]!=cg.dp_map[word]+1)return NULL;
    home=frame_operand(s->offset);
    return !strncmp(home,"z:",2)?home+2:NULL;
}
/* Form the scaled displacement and add the base directly into a pointer
 * home. The bank word serves as the high half of the displacement until
 * the low-word add supplies the final carry */
static int discarded_scaled_far_home(Expr *e)
{
    Expr *sum,*base,*index;
    Symbol *dest;
    unsigned stride,shifts=0;
    int high;
    if(cg.parser->no_strength_reduction||cg.parser->no_indexed_operands||
       e->kind!=EX_ASSIGN||e->op||e->left->kind!=EX_OBJECT||
       (sum=e->right)->kind!=EX_BINARY||sum->op!='+'||
       !far_pointer(value_type(sum->type))||volatile_expression(e)||
       !far_pointer_dp_home(e->left))return 0;
    dest=e->left->symbol;
    base=sum->left;index=sum->right;
    if(base->kind!=EX_OBJECT||base->symbol==dest||base->type.array||
       !far_pointer(value_type(base->type))||index->kind!=EX_OBJECT||
       index->type.pointers||!index->type.is_unsigned||!word_integer(index->type))return 0;
    if(base->symbol->owner&&base->symbol->offset){
        unsigned word=(base->symbol->offset-1)/2,home=cg.dp_map[(dest->offset-1)/2];
        for(unsigned i=word;i<=word+1&&i<cg.dp_words;++i)
            if(cg.dp_map[i]==home||cg.dp_map[i]==home+1)return 0;
    }
    stride=width(pointed_type(value_type(base->type)));
    if(stride<2||stride>16||(stride&(stride-1)))return 0;
    for(;stride>1;stride>>=1)++shifts;
    high=!narrow_unsigned_value(index,16-shifts);
    code("; scaled far address directly into pointer home\n");
    emit_value(index);
    if(high)code("    stz %s\n",frame_operand(dest->offset+2));
    for(unsigned i=0;i<shifts;++i){
        code("    asl a\n");
        if(high)code("    rol %s\n",frame_operand(dest->offset+2));
    }
    code("    clc\n    adc ");array_operand(base->symbol,0);
    code("\n    sta %s\n    lda ",frame_operand(dest->offset));
    array_operand(base->symbol,2);
    if(high)code("\n    adc %s\n",frame_operand(dest->offset+2));
    else code("\n    adc #0\n");
    code("    and #$00FF\n    sta %s\n",frame_operand(dest->offset+2));
    return 1;
}
/* The hardware adds Y to a 24-bit base. Account separately for the
 * seventeenth displacement bit when scaling an unsigned word index. */
static int indexed_far_word_load(Expr *e)
{
    Expr *address=e->left,*base,*index;
    if(cg.parser->no_indexed_operands||cg.parser->no_strength_reduction||
       e->kind!=EX_DEREF||width(e->type)!=2||volatile_expression(e)||
       address->kind!=EX_BINARY||address->op!='+')return 0;
    base=address->left;index=address->right;
    if(base->kind!=EX_OBJECT||base->type.array||!far_pointer(value_type(base->type))||
       width(pointed_type(value_type(base->type)))!=2||index->type.pointers||
       index->type.base==TY_FLOAT||!value_type(index->type).is_unsigned||reg_width(index->type)!=2||
       expression_uses_arith_lhs(index))return 0;
    emit_value(index);cg.arithmetic=1;
    code("; indexed far word load: scaled displacement in Y\n    asl a\n    tax\n");
    code("    lda ");array_operand(base->symbol,0);
    code("\n    sta z:__arith_lhs\n    lda ");array_operand(base->symbol,2);
    code("\n    adc #0\n    sta z:__arith_lhs+2\n    phy\n    txy\n    lda [__arith_lhs],y\n    ply\n");
    return 1;
}
static void load_far_pointer_home(const char *home,Type type,unsigned displacement)
{
    if(displacement)code("    phy\n    ldy #$%04X\n",displacement);
    emit_far_dp_load(home,type,displacement!=0);
    if(displacement)code("    ply\n");
    narrow_char(type);
}
/* Adjacent promoted words are already a native long-indirect pointer.
 * A constant nonnegative offset fits the indexed form as well. */
static int displaced_far_home_load(Expr *e)
{
    Expr *address=e->left,*base;
    unsigned size=width(e->type),stride;
    uint32_t n;
    const char *home;
    if(cg.parser->no_indexed_operands||e->kind!=EX_DEREF||
       (size!=1&&size!=2)||volatile_expression(e))return 0;
    if((home=far_pointer_dp_home(address))){
        load_far_pointer_home(home,e->type,0);
        return 1;
    }
    if(address->kind!=EX_BINARY||
       address->op!='+'||!integer_constant(address->right,&n))return 0;
    base=address->left;
    if(!(home=far_pointer_dp_home(base)))return 0;
    stride=width(pointed_type(value_type(base->type)));
    if(!stride||n>65535/stride||
       (!address->right->type.is_unsigned&&reg_width(address->right->type)==2&&(int16_t)n<0))return 0;
    load_far_pointer_home(home,e->type,(unsigned)n*stride);
    return 1;
}
/* A member displacement belongs in the indexed load. In particular, a
 * far view of a near object still accesses that object's WRAM bank. */
static int indexed_far_member(Expr *e)
{
    Expr *base,*index=NULL;
    unsigned offset,size=width(e->type);
    unsigned stride=1;
    int pointer;
    int base_in_lhs;
    if(cg.parser->no_indexed_operands||e->kind!=EX_MEMBER||
       (size!=1&&size!=2)||volatile_expression(e))return 0;
    base=member_root(e,&offset,&pointer);
    if(!pointer){
        if(base->kind!=EX_DEREF)return 0;
        base=base->left;
    }
    if(offset>65535)return 0;
    if(base->kind==EX_CAST&&value_type(base->left->type).pointers&&
       !far_pointer(value_type(base->left->type))){
        emit_value_x(base->left);load_indirect_at(e->type,0,offset);return 1;
    }
    if(!far_pointer(value_type(base->type)))return 0;
    if(base->kind==EX_BINARY&&base->op=='+'&&far_pointer(value_type(base->left->type))&&
       !base->right->type.pointers&&base->right->type.is_unsigned&&
       base->right->type.base!=TY_FLOAT&&reg_width(base->right->type)==2){
        stride=width(pointed_type(value_type(base->left->type)));
        if(stride&&stride<=8&&!(stride&(stride-1))){
            index=base->right;base=base->left;
        }
    }
    if(!index){
        const char *home=far_pointer_dp_home(base);
        if(home){load_far_pointer_home(home,e->type,offset);return 1;}
    }
    base_in_lhs=far_base_in_arith_lhs(base);
    if(index){
        unsigned limit=(65535-offset)/stride;
        int high=!(index->known.valid&&index->known.min>=0&&
                   (uint32_t)index->known.max<=limit)&&
                 !(limit>=255&&unsigned_byte_value(index))&&limit<65535;
        if(base_in_lhs&&!high&&!expression_uses_arith_lhs(index)){
            emit_value(index);
            while(stride>1){code("    asl a\n");stride>>=1;}
            if(offset)code("    clc\n    adc #$%04X\n",offset);
            code("    phy\n    tay\n");
            goto emit_member_load;
        }
        if(base->kind==EX_OBJECT&&!(base->type.array&&base->symbol->wram)&&!expression_uses_arith_lhs(index)){
            emit_value(index);
            if(high)code("    stz z:__arith_rhs\n");
            while(stride>1){
                code("    asl a\n");
                if(high)code("    rol z:__arith_rhs\n");
                stride>>=1;
            }
            if(offset){
                code("    clc\n    adc #$%04X\n",offset);
                if(high)code("    bcc :+\n    inc z:__arith_rhs\n:\n");
            }
            code("    tax\n    lda ");
            array_operand(base->symbol,0);
            code("\n    sta z:__arith_lhs\n    lda ");
            array_operand(base->symbol,2);
            if(high)code("\n    clc\n    adc z:__arith_rhs");
            code("\n    sta z:__arith_lhs+2\n    phy\n    txy\n");
            goto emit_member_load;
        }
        emit_value(base);cg.arithmetic=1;
        push_value(value_type(base->type));
        emit_value(index);
        if(high)code("    stz z:__arith_rhs\n");
        while(stride>1){
            code("    asl a\n");
            if(high)code("    rol z:__arith_rhs\n");
            stride>>=1;
        }
        if(offset){
            code("    clc\n    adc #$%04X\n",offset);
            if(high)code("    bcc :+\n    inc z:__arith_rhs\n:\n");
        }
        code("    tax\n    pla\n    sta z:__arith_lhs\n    pla\n");
        if(cg.stack_leaf)cg.stack_bias-=4;
        if(high)code("    clc\n    adc z:__arith_rhs\n");
        code("    sta z:__arith_lhs+2\n    phy\n    txy\n");
    }else{
        if(!base_in_lhs){
            emit_value(base);cg.arithmetic=1;
            code("    sta z:__arith_lhs\n    stx z:__arith_lhs+2\n");
        }
        if(offset)code("    phy\n    ldy #$%04X\n",offset);
    }
emit_member_load:
    emit_far_dp_load("__arith_lhs",e->type,index||offset);
    if(index||offset)code("    ply\n");
    narrow_char(e->type);
    return 1;
}
static Symbol *far_update_home(Expr *e)
{
    Symbol *s;unsigned step=increment_step(e->type);
    if(volatile_expression(e)||cg.parser->no_strength_reduction||(e->kind!=EX_PRE&&e->kind!=EX_POST)||
       e->left->kind!=EX_OBJECT||!far_pointer(value_type(e->type))||!step||step>65535)return NULL;
    s=e->left->symbol;return s->type.banked?NULL:s;
}
/* Repair the bank only when the low word carries/borrows, including wrap */
static void far_update_memory(Symbol *s,unsigned step,int increment,int low_ready)
{
    unsigned done=++cg.label;
    if(!low_ready){code("    lda ");array_operand(s,0);code("\n");}
    if(increment&&step==1)code("    inc a\n");
    else code("    %s\n    %s #$%04X\n",increment?"clc":"sec",increment?"adc":"sbc",step);
    code("    sta ");array_operand(s,0);code("\n    %s cg_%s_%u\n    lda ",
         increment?(step==1?"bne":"bcc"):"bcs",cg.parser->unit,done);
    array_operand(s,2);code("\n    %s a\n    and #$00FF\n    sta ",increment?"inc":"dec");array_operand(s,2);code("\n");label(done);
}
static int discarded_far_update(Expr *e)
{
    Symbol *s=far_update_home(e);unsigned step;
    if(!s)return 0;
    step=increment_step(e->type);
    code("; discarded far-%s pointer update\n",step==1?"byte":"element");
    far_update_memory(s,step,e->op==TOK_INC,0);return 1;
}
static void stage_far_home(Symbol *s)
{
    cg.arithmetic=1;
    code("    lda ");array_operand(s,0);code("\n    sta z:__arith_lhs\n    lda ");
    array_operand(s,2);code("\n    sta z:__arith_lhs+2\n");
}
/* The dereference consumes the cursor directly. No pointer lvalue address or
 * four-byte result needs to survive on the stack. */
static int updated_far_load(Expr *e)
{
    Expr *address=e->left;Symbol *s;
    const char *home;
    if(e->kind!=EX_DEREF||(width(e->type)!=1&&width(e->type)!=2)||
       volatile_expression(e)||!(s=far_update_home(address)))return 0;
    code("; far load through updated cursor\n");
    home=far_pointer_dp_home(address->left);
    if(home){
        if(address->kind==EX_POST){
            load_far_pointer_home(home,e->type,0);
            code("    tax\n");
        }
        far_update_memory(s,increment_step(address->type),address->op==TOK_INC,0);
        if(address->kind==EX_PRE)load_far_pointer_home(home,e->type,0);
        else code("    txa\n");
        divmod_written(address->left);return 1;
    }
    if(address->kind==EX_POST){
        /* Stage the address high word first so A can update its low word */
        cg.arithmetic=1;
        code("    lda ");array_operand(s,2);code("\n    sta z:__arith_lhs+2\n    lda ");
        array_operand(s,0);code("\n    sta z:__arith_lhs\n");
    }
    far_update_memory(s,increment_step(address->type),address->op==TOK_INC,address->kind==EX_POST);
    if(address->kind==EX_PRE)stage_far_home(s);
    divmod_written(address->left);
    load_far_pointer_home("__arith_lhs",e->type,0);
    return 1;
}
/* An in-bounds element or one-past address in a small declared array has
 * a word-sized displacement. Add it to the link-time base and retain the
 * bank carry, including when a ROM allocation crosses a 64 KiB boundary. */
static int rom_array_address(Expr *base,Expr *index,int op)
{
    Symbol *s;
    Type t=value_type(index->type);
    unsigned scale;
    if(cg.parser->no_indexed_operands||cg.parser->no_strength_reduction||
       op!='+'||base->kind!=EX_OBJECT||!base->type.array||!base->type.banked||
       !width(base->type)||width(base->type)>65535||
       t.pointers||t.base==TY_FLOAT||reg_width(t)!=2||index->kind==EX_INT)return 0;
    s=base->symbol;if(s->wram)return 0;
    scale=width(pointed_type(value_type(base->type)));
    emit_value(index);strength_scale(scale,index);s->used=1;
    code("; indexed ROM address with bank carry\n"
         "    clc\n    adc #.loword(_%s)\n    ldx #.bankbyte(_%s)\n    bcc :+\n"
         "    ldx #.bankbyte(_%s+$FFFF)\n:\n",s->asm_name,s->asm_name,s->asm_name);
    return 1;
}
/* Keep the far type on the expression. Only the actual memory operand can
 * become absolute, and only with a whole-object bank-$7E proof. */
static Symbol *wram_index(Expr *e,Expr **index,unsigned *scale,unsigned *offset)
{
    int pointer=0;
    Expr *root=e,*address,*base;
    unsigned extent,bytes;
    if(cg.parser->no_indexed_operands||e->type.array||structure_object(e->type))return NULL;
    if(e->kind==EX_MEMBER)root=member_root(e,offset,&pointer);
    address=pointer?root:root->kind==EX_DEREF?root->left:NULL;
    if(!address||address->kind!=EX_BINARY||address->op!='+')return NULL;
    base=address->left;
    if(base->kind!=EX_OBJECT||!base->type.array||!base->symbol->wram)return NULL;
    *index=address->right;*scale=width(pointed_type(value_type(base->type)));
    if(reg_width((*index)->type)!=2||!numeric((*index)->type)||(*index)->type.pointers)return NULL;
    bytes=width(e->type);extent=width(base->type);
    if(!extent||!bytes||*offset+bytes>*scale)return NULL;
    /* An in-bounds index into a complete object bounds the whole byte
     * access. For larger objects, prove that the scaled index fits in X. */
    if(extent>65536){
        KnownValue known=(*index)->known;
        unsigned max=known.valid&&known.min>=0?(unsigned)known.max:(*index)->type.is_unsigned?65535:32767;
        if((uint64_t)max * *scale+*offset>65535)return NULL;
    }
    return base->symbol;
}
static void emit_wram_index(Expr *index,unsigned scale)
{
    if(scale==1)emit_value_x(index);
    else{emit_value(index);strength_scale(scale,index);code("    tax\n");}
}
static void emit_wram_rmw(Expr *e,Symbol *s,unsigned offset,const char *suffix,int needed)
{
    int byte=width(e->type)==1,post=e->kind==EX_POST;
    if(byte)code("    sep #$20\n.a8\n");
    if(needed&&post){code("    lda ");array_operand(s,offset);code("%s\n",suffix);}
    code(e->op==TOK_INC?"    inc ":"    dec ");array_operand(s,offset);code("%s\n",suffix);
    if(needed&&!post){code("    lda ");array_operand(s,offset);code("%s\n",suffix);}
    if(byte){code("    rep #$20\n.a16\n");if(needed)narrow_char(e->type);}
}
static int direct_wram_access(Expr *e,int needed)
{
    Expr *target=e,*index;
    unsigned offset=0,scale,bytes,regs;
    Symbol *s;
    int store=e->kind==EX_ASSIGN, update=e->kind==EX_PRE||e->kind==EX_POST,rmw;
    if(store||update)target=e->left;
    else if(e->kind!=EX_DEREF&&e->kind!=EX_MEMBER)return 0;
    bytes=width(target->type);regs=reg_width(target->type);
    if(target->type.array||structure_object(target->type)||regs>4)return 0;
    rmw=update&&bytes<=2&&!target->type.pointers&&!target->type.is_bool&&!volatile_expression(target);
    s=direct_memory_object(target,&offset);
    if(s&&s->wram){
        if(rmw&&wram_near(s))emit_wram_rmw(e,s,offset,"",needed);
        else if(update){
            load_array_element(s,offset,target->type);
            if(needed&&e->kind==EX_POST)push_value(e->type);
            increment_value(e->type,e->op);
            store_array_element(s,offset,e->type);
            if(needed&&e->kind==EX_POST)pop_value(e->type);
        }else if(store){
            if(e->op){
                load_array_element(s,offset,target->type);
                binary_after_left(target,e->right,e->op);
                convert_registers(binary_operands(target,e->right,e->op),e->type);
            }else emit_value(e->right);
            store_array_element(s,offset,e->type);
        }else load_array_element(s,offset,e->type);
        if(store||update)divmod_written(target);
        return 1;
    }
    if((store&&(e->op||regs>2))||!(s=wram_index(target,&index,&scale,&offset)))return 0;
    if(update&&(!rmw||!wram_near(s)))return 0;
    emit_wram_index(index,scale);
    if(update){
        emit_wram_rmw(e,s,offset,",x",needed);
        divmod_written(target);return 1;
    }
    if(store){
        code("    phx\n");if(cg.stack_leaf)cg.stack_bias+=2;
        emit_value(e->right);
        code("    plx\n");if(cg.stack_leaf)cg.stack_bias-=2;
    }
    if(bytes==1)code("    sep #$20\n.a8\n");
    code(store?"    sta ":"    lda ");array_operand(s,offset);code(",x\n");
    if(bytes==1)code("    rep #$20\n.a16\n");
    if(!store&&regs==4){
        code("    pha\n    lda ");array_operand(s,offset+2);code(",x\n    tax\n    pla\n");
    }
    if(store)divmod_written(target);
    else narrow_char(e->type);
    return 1;
}
static int emit_far(Expr *e,int narrow)
{
    Type address=far_type(type(TY_CHAR,1));
    if(narrow&&constant_far(e))return 1;
    if(narrow&&(e->type.banked||(e->left&&e->left->type.banked))&&direct_wram_access(e,1))return 1;
    if((e->kind==EX_DEREF||e->kind==EX_MEMBER)&&e->type.banked&&!e->type.array){
        if(!narrow||(!rom_load(e)&&!direct_dpage_load(e)&&!displaced_far_home_load(e)&&!updated_far_load(e)&&
           !indexed_far_member(e)&&!indexed_far_byte_load(e)&&!indexed_far_word_load(e))){
            emit_address(e);far_load(e->type);
        }return 1;
    }
    if(e->kind==EX_ASSIGN&&e->left->type.banked){
        if(narrow&&direct_dpage_store(e))return 1;
        emit_address(e->left);push_value(address);
        if(e->op){far_load(e->left->type);binary_after_left(e->left,e->right,e->op);convert_registers(binary_operands(e->left,e->right,e->op),e->type);}
        else emit_value(e->right);
        far_store(e->type,0);cleanup(4,e->type);if(cg.stack_leaf)cg.stack_bias-=4;
        divmod_written(e->left);return 1;
    }
    if((e->kind==EX_PRE||e->kind==EX_POST)&&e->left->type.banked){
        emit_address(e->left);push_value(address);far_load(e->type);
        if(e->kind==EX_POST)push_value(e->type);
        increment_value(e->type,e->op);far_store(e->type,e->kind==EX_POST?reg_width(e->type):0);
        if(e->kind==EX_POST)pop_value(e->type);
        cleanup(4,e->type);if(cg.stack_leaf)cg.stack_bias-=4;
        divmod_written(e->left);return 1;
    }
    if(e->kind==EX_BINARY&&far_pointer(common_type(e->left->type,e->right->type))&&
       (e->op=='+'||e->op=='-')){
        Expr *left=e->left,*right=e->right;
        unsigned offset;
        String *literal;
        if(narrow&&!cg.parser->no_strength_reduction&&(literal=scalar_string_address(e,&offset,0))){
            /* Relocate both words of the final address, including a bank carry */
            literal->used=1;
            code("    lda #.loword(str_%s_%u+$%X)\n    ldx #.bankbyte(str_%s_%u+$%X)\n",
                 cg.parser->unit,literal->id,offset,cg.parser->unit,literal->id,offset);
            return 1;
        }
        if(!value_type(left->type).pointers){left=e->right;right=e->left;}
        if(narrow&&rom_array_address(left,right,e->op))return 1;
        emit_value(left);far_after_left(left,right,e->op);return 1;
    }
    return 0;
}
