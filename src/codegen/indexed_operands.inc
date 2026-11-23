/* Fixed near objects keep their symbol base in the memory operand. Only the
 * subscript displacement is evaluated into X, or supplied by a validated
 * retained X/Y loop binding. Pointer variables, locals, volatile accesses and wide values keep
 * their established lowering. Valid array accesses stay in the near bank. */
typedef struct { Symbol *base;Expr *index;unsigned scale,offset;int reg,save_x;unsigned cursor_word; } IndexedOperand;
static void strength_scale(unsigned scale,Expr *value);
static void binary_after_left(Expr *left,Expr *right,int op);
static int word_preserves_x(Expr *e);
static void emit_m8_byte_value(Expr *e);
static void indexed_store_m8(IndexedOperand *operand);
/* Byte-offset expressions often cross a pointer cast on their way to the
 * final lvalue. Walk the pointer side with its original element stride. */
static Symbol *indexed_near_base(Expr *e,Expr **index,unsigned *scale,unsigned *offset)
{
    Expr *term;
    unsigned stride;
    uint32_t constant;
    if(e->kind==EX_OBJECT&&e->type.array&&!e->type.banked&&width(e->type)<=65536)
        return e->symbol;
    if(far_pointer(value_type(e->type)))return NULL;
    if(e->kind==EX_CAST&&value_type(e->type).pointers&&
       value_type(e->left->type).pointers&&!far_pointer(value_type(e->left->type)))
        return indexed_near_base(e->left,index,scale,offset);
    if(e->kind!=EX_BINARY||e->op!='+'||!value_type(e->left->type).pointers)return NULL;
    term=e->right;stride=width(pointed_type(value_type(e->left->type)));
    if(!stride||stride>65535||term->type.pointers||term->type.array||
       term->type.base==TY_FLOAT||reg_width(term->type)!=2)return NULL;
    if(integer_constant(term,&constant)){
        if((!term->type.is_unsigned&&(int16_t)constant<0)||constant>(65535-*offset)/stride)return NULL;
        *offset+=constant*stride;
    }else{
        if(*index||(!term->type.is_unsigned&&(!term->known.valid||term->known.min<0)))return NULL;
        *index=term;*scale=stride;
    }
    return indexed_near_base(e->left,index,scale,offset);
}
static int indexed_operand(Expr *e,IndexedOperand *out)
{
    Expr *root=e,*address,*base;Symbol *symbol;unsigned offset=0,base_offset=0,scale;uint32_t constant;int pointer;
    if(cg.parser->no_indexed_operands||volatile_expression(e)||e->type.array||
       e->type.banked||structure_object(e->type)||e->type.base==TY_FLOAT||reg_width(e->type)!=2)return 0;
    if(e->kind==EX_MEMBER)root=member_root(e,&offset,&pointer);
    else pointer=0;
    if(!pointer&&root->kind!=EX_DEREF)return 0;
    address=pointer?root:root->left;
    /* Wide functions retain this cursor without the later line passes */
    if(cg.function->uses_wide&&bound_state.cursor&&strength_pointer_plan(address,&scale)==bound_state.cursor)return 0;
    if(address->kind!=EX_BINARY||address->op!='+'||
       !address->left->type.array||address->left->type.banked){
        Expr *index=NULL;
        if(offset>65535||!(symbol=indexed_near_base(address,&index,&scale,&offset))||
           !index||symbol->owner||symbol->dpage||
           (width(symbol->type)&&offset+width(e->type)>width(symbol->type))||
           offset+width(e->type)>65536)return 0;
        *out=(IndexedOperand){symbol,index,scale,offset,0,0};return 1;
    }
    base=address->left;
    if(integer_constant(address->right,&constant))return 0;
    if(!base->type.array||base->type.banked||address->right->type.pointers||
       address->right->type.array||address->right->type.base==TY_FLOAT||reg_width(address->right->type)!=2)return 0;
    symbol=base->kind==EX_OBJECT?base->symbol:fixed_memory_object(base,&base_offset);
    if(!symbol||symbol->owner||symbol->dpage||symbol->type.banked)return 0;
    scale=width(pointed_type(value_type(base->type)));
    if(!scale||scale>65535||width(base->type)>65536||offset+width(e->type)>scale)return 0;
    out->base=symbol;out->index=address->right;out->scale=scale;out->offset=base_offset+offset;out->reg=out->save_x=0;out->cursor_word=0;return 1;
}
/* Retained displacements are affine in one private loop counter. Narrowing
 * casts, other variables and side effects retain the ordinary evaluated path. */
static int word_left_shift_factor(Expr *e,uint32_t *factor)
{
    uint32_t count;
    if(e->kind!=EX_BINARY||e->op!=TOK_SHL||e->type.base!=TY_INT||e->type.pointers||
       reg_width(e->type)!=2||reg_width(e->right->type)>4||
       !integer_constant(e->right,&count)||count>=16)return 0;
    *factor=1u<<count;return 1;
}
static int retained_affine_for(Expr *e,Symbol *index,unsigned *a,unsigned *b)
{
    unsigned x,y,z,w;uint32_t n;
    if(integer_constant(e,&n)){*a=0;*b=n&65535;return 1;}
    if(e->kind==EX_OBJECT&&e->symbol==index){*a=1;*b=0;return 1;}
    if(e->kind==EX_CAST&&width(e->type)==2&&reg_width(e->left->type)==2)
        return retained_affine_for(e->left,index,a,b);
    if(word_left_shift_factor(e,&n)&&retained_affine_for(e->left,index,&x,&y)){
        *a=(x*n)&65535;*b=(y*n)&65535;return 1;
    }
    if(e->kind!=EX_BINARY||!retained_affine_for(e->left,index,&x,&y)||!retained_affine_for(e->right,index,&z,&w))return 0;
    if(e->op=='+'||e->op=='-'){*a=(x+(e->op=='+'?z:0u-z))&65535;*b=(y+(e->op=='+'?w:0u-w))&65535;return 1;}
    if(e->op=='*'&&(!x||!z)){*a=(x*w+z*y)&65535;*b=(y*w)&65535;return 1;}return 0;
}
static int retained_affine(Expr *e,unsigned *a,unsigned *b)
{
    if(!retained_affine_for(e,cg.retained_index,a,b))return 0;
    if(cg.retained_bias){
        uint32_t shifted=(uint32_t)*b+(uint32_t)*a*cg.retained_bias;
        if(shifted>65535u)return 0;
        *b=(unsigned)shifted;
    }
    return 1;
}
static int indexed_retained(IndexedOperand *operand,int allow_y)
{
    unsigned a,b,scale,offset,i,steps;
    if(allow_y&&cg.retained_second&&retained_affine_for(operand->index,cg.retained_second,&a,&b)&&a&&b==0&&
       a*operand->scale==cg.retained_second_scale&&operand->offset==0){operand->reg='y';return 1;}
    if(!cg.retained_index)return 0;
    if(!retained_affine(operand->index,&a,&b)||!a||(int16_t)b<0)return 0;
    scale=a*operand->scale;offset=b*operand->scale+operand->offset;
    /* Folding into an absolute indexed operand must not remove the
     * original 16-bit subscript wrap. Otherwise evaluate it normally. */
    steps=cg.retained_limit>(cg.retained_unroll?cg.retained_unroll:1u)?
          cg.retained_limit-(cg.retained_unroll?cg.retained_unroll:1u):0u;
    if(offset>65535||(steps&&scale>(65535-offset)/steps))return 0;
    if(cg.retained_y==5){
        if(!allow_y||scale!=cg.retained_scale)return 0;
        operand->reg='y';operand->offset=offset;return 1;
    }
    if(!cg.retained_scratch&&scale==cg.retained_scale)operand->reg='x';
    else if(allow_y&&cg.retained_y==1&&scale==1)operand->reg='y';
    else if(allow_y&&cg.retained_second==cg.retained_index&&scale==cg.retained_second_scale)operand->reg='y';
    else if(allow_y&&cg.retained_y==1){
        for(i=0;i<cg.retained_cursor_count;++i){
            if(cg.retained_cursors[i].base==operand->base&&
               cg.retained_cursors[i].offset==offset&&
               cg.retained_cursors[i].scale==scale){
                operand->reg='c';
                operand->cursor_word=cg.retained_cursors[i].dp_word+1u;
                break;
            }
        }
        if(!operand->cursor_word)return 0;
    }
    else return 0;
    operand->offset=offset;return 1;
}
static int indexed_available(IndexedOperand *operand)
{
    return !cg.retained_index||indexed_retained(operand,1);
}
static void indexed_index_mode(IndexedOperand *operand,int allow_y)
{
    if(allow_y&&!operand->reg&&cg.scaled_ring_head&&cg.loop_y_borrowed&&
       operand->scale==1&&operand->index->kind==EX_OBJECT&&
       operand->index->symbol==cg.scaled_ring_head){
        code("    ldy %s\n",frame_operand(cg.scaled_ring_head->offset));
        operand->reg='y';
        return;
    }
    if(operand->reg||indexed_retained(operand,allow_y)){
        code("; direct indexed operand: retained %c\n",operand->reg);return;
    }
    if(cg.retained_index&&cg.retained_y!=5){
        code("; retained scratch begin\n    phx\n");if(cg.stack_leaf)cg.stack_bias+=2;
        ++cg.retained_scratch;operand->save_x=1;
    }
    code("; direct indexed operand\n");
    if(operand->scale==1)emit_value_x(operand->index);
    else{emit_value(operand->index);strength_scale(operand->scale,operand->index);code("    tax\n");}
}
static void indexed_finish(IndexedOperand *operand)
{
    if(operand->save_x){
        --cg.retained_scratch;if(cg.stack_leaf)cg.stack_bias-=2;
        code("    plx\n; retained scratch end\n");
    }
}
static void indexed_text(IndexedOperand *operand)
{
    operand->base->used=1;
    if(operand->cursor_word){
        code("(__arith_lhs+%u),y",(operand->cursor_word-1u)*2u);
        return;
    }
    code("a:.loword(_%s+$%04X),%c",operand->base->asm_name,operand->offset,operand->reg?operand->reg:'x');
}
static void indexed_index(IndexedOperand *operand)
{
    indexed_index_mode(operand,1);
}
static void indexed_preserve_a(IndexedOperand *operand)
{
    if(operand->reg||indexed_retained(operand,1))return;
    push_value(type(TY_INT,0));indexed_index(operand);pop_value(type(TY_INT,0));
}
static void indexed_load(IndexedOperand *operand,Type t)
{
    code("    lda ");indexed_text(operand);code("\n");narrow_char(t);
}
static void indexed_store_m8(IndexedOperand *operand)
{
    code("    sta ");indexed_text(operand);code("\n");
}
static void indexed_store(IndexedOperand *operand,Type t)
{
    if(width(t)==1)code("    sep #$20\n.a8\n");
    indexed_store_m8(operand);
    if(width(t)==1)code("    rep #$20\n.a16\n");
}
static int indexed_binary_loaded(Expr *left,Expr *right,int op)
{
    IndexedOperand operand;Type t=binary_operands(left,right,op);
    if(t.pointers||t.base==TY_FLOAT||reg_width(t)!=2||!basic_integer_op(op)||
       width(right->type)!=2||!indexed_operand(right,&operand)||!indexed_available(&operand))return 0;
    convert_registers(value_type(left->type),t);indexed_preserve_a(&operand);
    if(op=='+'||op=='-')code("    %s\n",op=='+'?"clc":"sec");
    code("    %s ",op=='+'?"adc":op=='-'?"sbc":op=='&'?"and":op=='|'?"ora":"eor");
    indexed_text(&operand);code("\n");return 1;
}
/* Pure nonvolatile arithmetic may commute a memory add/bitwise operation.
 * The destination subscript is still selected before evaluating its RHS. */
static int indexed_pure(Expr *e)
{
    if(!e||volatile_expression(e)||e->kind==EX_CALL||e->kind==EX_ASSIGN||e->kind==EX_PRE||e->kind==EX_POST||e->kind==EX_ADDRESS||
       (!e->type.pointers&&!e->type.array&&(e->type.base==TY_FLOAT||reg_width(e->type)>2)))return 0;
    return (!e->left||indexed_pure(e->left))&&(!e->right||indexed_pure(e->right))&&(!e->third||indexed_pure(e->third));
}
static int indexed_pair_binary(Expr *e)
{
    IndexedOperand left,right;
    int op=e->op;
    if(!basic_integer_op(op)||width(e->left->type)!=2||width(e->right->type)!=2||
       e->type.pointers||e->type.base!=TY_INT||!indexed_operand(e->left,&left)||
       !indexed_operand(e->right,&right)||left.scale!=right.scale||
       !body_equal(left.index,right.index)||!indexed_pure(left.index))return 0;
    indexed_retained(&left,1);indexed_retained(&right,1);
    if(left.reg!=right.reg)return 0;
    indexed_index(&left);
    indexed_load(&left,e->left->type);
    if(op=='+'||op=='-')code("    %s\n",op=='+'?"clc":"sec");
    code("    %s ",op=='+'?"adc":op=='-'?"sbc":op=='&'?"and":op=='|'?"ora":"eor");
    indexed_text(&right);code("\n");indexed_finish(&left);
    return 1;
}
/* Combine a word array operand with an immediate operation on a
 * second word at the same displacement. Evaluate the shared index once
 * and keep the intermediate in A instead of spilling the first word. */
static int indexed_immediate_pair(Expr *e)
{
    IndexedOperand left,right;
    Expr *inner=e->right,*memory;
    uint32_t literal;
    const char *mnemonic;
    int op=e->op,constant_left;
    if(cg.parser->no_body_optimizations||
       (op!='+'&&op!='&'&&op!='|'&&op!='^')||e->type.pointers||e->type.base!=TY_INT||
       width(e->left->type)!=2||!indexed_operand(e->left,&left)||
       inner->kind!=EX_BINARY||inner->type.pointers||inner->type.base!=TY_INT||
       !basic_integer_op(inner->op))return 0;
    constant_left=integer_constant(inner->left,&literal);
    if(constant_left)memory=inner->right;
    else{
        if(!integer_constant(inner->right,&literal))return 0;
        memory=inner->left;
    }
    if(width(memory->type)!=2||!indexed_operand(memory,&right)||
       left.scale!=right.scale||!body_equal(left.index,right.index)||!indexed_pure(left.index))return 0;
    indexed_retained(&left,1);indexed_retained(&right,1);
    if(left.reg!=right.reg)return 0;
    indexed_index(&left);
    if(constant_left)code("    lda #$%04X\n",literal&65535);
    else indexed_load(&right,memory->type);
    if(inner->op=='+'||inner->op=='-')code("    %s\n",inner->op=='+'?"clc":"sec");
    mnemonic=inner->op=='+'?"adc":inner->op=='-'?"sbc":inner->op=='&'?"and":inner->op=='|'?"ora":"eor";
    if(constant_left){code("    %s ",mnemonic);indexed_text(&right);code("\n");}
    else code("    %s #$%04X\n",mnemonic,literal&65535);
    if(op=='+')code("    clc\n");
    code("    %s ",op=='+'?"adc":op=='&'?"and":op=='|'?"ora":"eor");
    indexed_text(&left);code("\n");indexed_finish(&left);
    return 1;
}

static int indexed_update_rhs_first(Expr *e,IndexedOperand *operand)
{
    Type t;int save_x,byte_rmw;uint32_t constant;
    if(cg.parser->no_body_optimizations||(width(e->type)!=2&&width(e->type)!=1)||
       e->type.pointers||e->type.is_bool||
       (e->op!='+'&&e->op!='&'&&e->op!='|'&&e->op!='^')||!indexed_pure(e->right))return 0;
    byte_rmw=width(e->type)==1;
    if(byte_rmw&&integer_constant(e->right,&constant))return 0;
    t=binary_operands(e->left,e->right,e->op);if(t.pointers||t.base!=TY_INT)return 0;
    code("; commuted indexed update\n");indexed_index(operand);
    save_x=!operand->reg&&!word_preserves_x(e->right);
    if(save_x){code("    phx\n");if(cg.stack_leaf)cg.stack_bias+=2;}
    if(byte_rmw)emit_m8_byte_value(e->right);
    else{emit_value(e->right);convert_registers(value_type(e->right->type),t);}
    if(save_x){if(cg.stack_leaf)cg.stack_bias-=2;code("    plx\n");}
    if(e->op=='+')code("    clc\n");
    code("    %s ",e->op=='+'?"adc":e->op=='&'?"and":e->op=='|'?"ora":"eor");indexed_text(operand);code("\n");
    if(byte_rmw){
        indexed_store_m8(operand);
        code("    rep #$20\n.a16\n");
        narrow_char(e->type);
        indexed_finish(operand);
        return 1;
    }
    if(!e->known_no_conversion)convert_registers(t,e->type);
    indexed_store(operand,e->type);indexed_finish(operand);return 1;
}
static int indexed_result_in_a(IndexedOperand *operand,Type t)
{
    char store[256];size_t at=cg.length,start,n,old;int length;
    if(cg.parser->no_body_optimizations||width(t)!=2||!operand->reg)return 0;
    /* Construct the same typed operand spelling, without changing assembly */
    code("    sta ");indexed_text(operand);code("\n");
    length=(int)(cg.length-at-1);if((unsigned)length>=sizeof store){cg.length=at;cg.assembly[at]=0;return 0;}
    memcpy(store,cg.assembly+at,length);cg.length=at;cg.assembly[at]=0;
    start=previous_instruction(at,&n);
    if(n!=(size_t)length||memcmp(store,cg.assembly+start,n))return 0;
    old=previous_instruction(start,&n);
    return full_accumulator_flags(cg.assembly+old,n);
}
static Expr *indexed_repeated_word_update(Expr *e)
{
    if(cg.parser->no_body_optimizations||!e||e->kind!=EX_ASSIGN||e->op||width(e->type)!=2)return NULL;
    Expr *rhs=word_bits(e->right);
    if(rhs->kind!=EX_BINARY||rhs->type.base!=TY_INT||rhs->type.pointers||
       !basic_integer_op(rhs->op)||!indexed_pure(e->left)||!indexed_pure(rhs->right)||
       !body_equal(e->left,rhs->left))return NULL;
    return rhs;
}
static int indexed_expr_writes_symbol(Expr *e,Symbol *s)
{
    unsigned i;
    if(!e)return 0;
    if((e->kind==EX_ASSIGN||e->kind==EX_PRE||e->kind==EX_POST)&&
       e->left&&e->left->kind==EX_OBJECT&&e->left->symbol==s)return 1;
    if(indexed_expr_writes_symbol(e->left,s)||
       indexed_expr_writes_symbol(e->right,s)||
       indexed_expr_writes_symbol(e->third,s))return 1;
    for(i=0;i<e->arg_count;++i)if(indexed_expr_writes_symbol(e->args[i],s))return 1;
    return 0;
}
static int indexed_affine_owned(Expr *deref)
{
    AffineLoop *loop=cg.affine_active;unsigned i;
    if(!loop||!deref||deref->kind!=EX_DEREF)return 0;
    for(i=0;i<loop->count;++i)if(loop->accesses[i].address==deref->left)return 1;
    return 0;
}
static int indexed_access(Expr *e)
{
    IndexedOperand operand;
    if(e->kind==EX_ASSIGN){
        Expr update;int save_x;
        if(indexed_affine_owned(e->left)||!indexed_operand(e->left,&operand)||volatile_expression(e))return 0;
        /* A pure repeated element uses the destination offset already in X */
        Expr *rhs=indexed_repeated_word_update(e);
        if(rhs){
            update=*e;update.op=rhs->op;update.right=rhs->right;e=&update;
        }
        if(indexed_update_rhs_first(e,&operand))return 1;
        if(!e->op&&!indexed_retained(&operand,1)&&!word_preserves_x(e->right)&&
           reg_width(e->right->type)<=2&&!e->right->type.pointers&&
           operand.index->kind==EX_OBJECT&&operand.index->symbol->scope&&
           body_private(operand.index->symbol)&&
           operand.index->symbol!=cg.scan_cursor&&
           operand.index->symbol!=cg.numeric_index&&
           operand.index->symbol!=cg.numeric_recurrence&&
           operand.index->symbol!=cg.leaf_count&&
           operand.index->type.base==TY_INT&&!operand.index->type.pointers&&
           !indexed_expr_writes_symbol(e->right,operand.index->symbol)){
            if(!cg.retained_index&&!cg.stack_leaf&&operand.scale==1){
                emit_value(e->right);
                indexed_index(&operand);
                indexed_store(&operand,e->type);
                indexed_finish(&operand);
                return 1;
            }
            if(cg.retained_index&&cg.retained_y!=5&&!cg.retained_scratch&&
               !(operand.index->symbol==cg.retained_index&&cg.retained_y==4)&&
               !volatile_expression(operand.index)){
                emit_value(e->right);
                code("; retained scratch begin\n    phx\n");
                if(cg.stack_leaf)cg.stack_bias+=2;
                ++cg.retained_scratch;
                if(operand.scale==1&&operand.index->symbol!=cg.retained_index){
                    emit_value_x(operand.index);
                }else{
                    code("    pha\n");
                    if(cg.stack_leaf)cg.stack_bias+=2;
                    emit_value(operand.index);
                    strength_scale(operand.scale,operand.index);
                    code("    tax\n");
                    if(cg.stack_leaf)cg.stack_bias-=2;
                    code("    pla\n");
                }
                indexed_store(&operand,e->type);
                --cg.retained_scratch;
                if(cg.stack_leaf)cg.stack_bias-=2;
                code("    plx\n; retained scratch end\n");
                return 1;
            }
        }
        /* Snapshot the selected element before evaluating an arbitrary RHS.
         * Calls/writes in that RHS may change the original subscript/home. */
        indexed_index(&operand);
        save_x=!operand.reg&&(e->op||!word_preserves_x(e->right));
        if(save_x){code("    phx\n");if(cg.stack_leaf)cg.stack_bias+=2;}
        if(e->op){
            indexed_load(&operand,e->left->type);binary_after_left(e->left,e->right,e->op);
            if(!e->known_no_conversion)convert_registers(binary_operands(e->left,e->right,e->op),e->type);
        }else emit_value(e->right);
        if(save_x){if(cg.stack_leaf)cg.stack_bias-=2;code("    plx\n");}
        indexed_store(&operand,e->type);indexed_finish(&operand);return 1;
    }
    if(indexed_affine_owned(e)||!indexed_operand(e,&operand))return 0;
    indexed_index(&operand);if(!indexed_result_in_a(&operand,e->type))indexed_load(&operand,e->type);indexed_finish(&operand);if(operand.save_x)narrow_char(e->type);return 1;
}
