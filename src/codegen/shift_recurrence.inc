/* A constant-trip scalar shift can branch on the bit the shift puts in C.
 * Keep the shifting word in A across iterations and publish it at the end. */
static int constant_loop_trip_count(Statement *s,Symbol **index_out,unsigned *trips,unsigned *final)
{
    Statement *initial=body_single(s->initial);
    Expr *init,*test=s->expression,*left;
    Symbol *index;
    uint32_t first,end,limit;
    if(!initial||initial->next||initial->kind!=ST_EXPR)return 0;
    init=initial->expression;
    if(!init||init->kind!=EX_ASSIGN||init->op||init->left->kind!=EX_OBJECT||
       !integer_constant(init->right,&first))return 0;
    index=init->left->symbol;
    if(!known_integer(index->type)||index->type.is_bool||object_volatile(index->type)||
       !loop_private(index))return 0;
    if(test&&test->kind==EX_BINARY&&reg_width(common_type(test->left->type,test->right->type))!=2)return 0;
    limit=index->type.base==TY_CHAR?(index->type.is_unsigned?255u:127u):
                                  (index->type.is_unsigned?65535u:32767u);
    first=initializer_cast(first,index->type);
    if(first>limit)return 0;
    if(for_countdown_index(s,NULL)==index){
        if(!first)return 0;
        *trips=first;
        *final=0;
    }else{
        if(!test||test->kind!=EX_BINARY||(test->op!='<'&&test->op!=TOK_LE)||
           body_step_direction(s->step,index)!=1||
           !integer_constant(test->right,&end)||end>limit)return 0;
        left=test->left;
        while(left->kind==EX_CAST&&reg_width(left->type)==2&&
              !left->type.pointers&&!left->type.is_bool&&left->type.base==TY_INT)left=left->left;
        if(left->kind!=EX_OBJECT||left->symbol!=index)return 0;
        end+=test->op==TOK_LE;
        if(first>=end||end>limit)return 0;
        *trips=end-first;
        *final=end;
    }
    *index_out=index;
    return 1;
}

static int shift_recurrence_arm(Statement *arm,Symbol *home,int marked,int *op,uint32_t *mask)
{
    Expr *update,*value;
    uint32_t amount;
    arm=body_single(arm);
    if(!arm||arm->next||arm->inline_callee||arm->kind!=ST_EXPR)return 0;
    update=arm->expression;
    if(!update||update->kind!=EX_ASSIGN||!reduction_object(update->left,home))return 0;
    value=update->right;
    if(update->op){
        if(marked)return 0;
        *op=update->op;
    }else{
        if(marked){
            if(value->kind!=EX_BINARY||value->op!='^')return 0;
            if(integer_constant(value->right,mask))value=value->left;
            else if(integer_constant(value->left,mask))value=value->right;
            else return 0;
        }
        if(value->kind!=EX_BINARY||!reduction_object(value->left,home))return 0;
        *op=value->op;
        value=value->right;
    }
    return (*op==TOK_SHL||*op==TOK_SHR)&&reg_width(value->type)<=4&&
           integer_constant(value,&amount)&&amount==1;
}

static int register_loop_state_available(Statement *s)
{
    return !cg.parser->no_strength_reduction&&!cg.parser->no_body_optimizations&&
        !cg.parser->no_register_loops&&!cg.parser->no_register_cursors&&!cg.function->jump_label_count&&
        !cg.function->symbol->interrupt&&!cg.switch_depth&&!cg.retained_index&&!cg.retained_second&&
        !cg.affine_active&&!lftr_state.active&&!cg.scan_cursor&&!cg.numeric_index&&!bound_state.cursor&&!bound_state.pending&&
        !cg.scalar_leaf&&!cg.scalar_first&&!volatile_statement(s);
}

static int register_loop_available(Statement *s)
{
    return register_loop_state_available(s)&&!statement_inline_markers(s->body);
}

static int shift_recurrence_loop(Statement *s)
{
    Statement *body;
    Expr *test,*value;
    Symbol *home,*index;
    uint32_t flag,mask=0;
    unsigned trips,final,unroll,begin=0,skip,bytes,w,primary,secondary;
    int inverted=0,direction,plain_direction;
    if(s->kind!=ST_FOR||!register_loop_available(s))return 0;
    body=body_single(s->body);
    if(!body||body->next||body->inline_callee||body->kind!=ST_IF||!body->alternate)return 0;
    test=body->expression;
    if(test->kind==EX_UNARY&&test->op=='!'){inverted=1;test=test->left;}
    else if(test->kind==EX_BINARY&&(test->op==TOK_EQ||test->op==TOK_NE)){
        inverted=test->op==TOK_EQ;
        if(reg_width(test->right->type)<=4&&reduction_zero(test->right))test=test->left;
        else if(reg_width(test->left->type)<=4&&reduction_zero(test->left))test=test->right;
        else return 0;
    }
    if(test->kind!=EX_BINARY||test->op!='&')return 0;
    if(integer_constant(test->right,&flag))value=test->left;
    else if(integer_constant(test->left,&flag))value=test->right;
    else return 0;
    if(value->kind!=EX_OBJECT||!value->type.is_unsigned||value->type.pointers||
       value->type.is_bool||(value->type.base!=TY_INT&&value->type.base!=TY_LONG))return 0;
    home=value->symbol;w=width(value->type);
    if(!loop_private(home)||
       !shift_recurrence_arm(inverted?body->alternate:body->body,home,1,&direction,&mask)||
       !shift_recurrence_arm(inverted?body->body:body->alternate,home,0,&plain_direction,&mask)||
       direction!=plain_direction||flag!=(direction==TOK_SHR?1u:(UINT32_C(1)<<(w*8-1)))||
       !constant_loop_trip_count(s,&index,&trips,&final)||home==index)return 0;
    primary=(unsigned)(direction==TOK_SHR&&w==4?mask>>16:mask)&65535;
    secondary=w==2?0:(unsigned)(direction==TOK_SHR?mask:mask>>16)&65535;
    bytes=3+(w==4?2:0)+(primary?3:0)+(secondary?9:0);
    unroll=1;
    if(!cg.parser->no_loop_unroll){
        if(trips<=UNROLL_BYTE_BUDGET/bytes)unroll=trips;
        else while(trips%(unroll*2)==0&&unroll*2<=UNROLL_BYTE_BUDGET/bytes)unroll*=2;
    }
    code("; carry-tested shift recurrence\n");
    load_symbol(home);
    if(w==4){
        cg.arithmetic=1;
        if(direction==TOK_SHL)code("    stx z:__arith_lhs\n");
        else code("    sta z:__arith_lhs\n    txa\n");
    }
    if(trips>unroll){
        begin=++cg.label;
        code("    ldx #$%04X\n",trips/unroll);label(begin);
    }
    for(unsigned i=0;i<unroll;++i){
        code(direction==TOK_SHL?"    asl a\n":"    lsr a\n");
        if(w==4)code(direction==TOK_SHL?"    rol z:__arith_lhs\n":"    ror z:__arith_lhs\n");
        skip=++cg.label;
        code("    bcc cg_%s_%u\n",cg.parser->unit,skip);
        if(primary)code("    eor #$%04X\n",primary);
        if(secondary)code("    pha\n    lda z:__arith_lhs\n    eor #$%04X\n    sta z:__arith_lhs\n    pla\n",secondary);
        label(skip);
    }
    if(begin){
        code("    dex\n");
        flag_branch("bne","beq",begin,0,0);
    }
    if(w==4){
        if(direction==TOK_SHL)code("    ldx z:__arith_lhs\n");
        else code("    tax\n    lda z:__arith_lhs\n");
    }
    store_symbol(home);
    if(loop_observed_outside(cg.function->body,s,index)){
        code("    lda #$%04X\n",final);
        store_symbol(index);
    }
    divmod_state.available=0;
    return 1;
}

/* For an unsigned low-bit sum, LSR provides both the addend and the loop test */
static int low_bit_sum_loop(Statement *s)
{
    Statement *body,*tail;
    Expr *test=s->expression,*add,*shift,*term,*bit;
    Symbol *value,*sum;
    uint32_t operand;
    unsigned loop,even,done;
    int op;
    if(s->kind!=ST_WHILE||!test||!register_loop_available(s))return 0;
    if(test->kind==EX_BINARY&&test->op==TOK_NE){
        if(reg_width(test->right->type)<=4&&reduction_zero(test->right))test=test->left;
        else if(reg_width(test->left->type)<=4&&reduction_zero(test->left))test=test->right;
        else return 0;
    }
    if(test->kind!=EX_OBJECT||!known_integer(test->type)||test->type.is_bool||
       (!test->type.is_unsigned&&(!test->known.valid||test->known.min<0)))return 0;
    value=test->symbol;
    body=body_single(s->body);
    if(!body||body->kind!=ST_EXPR||!(tail=body->next)||tail->next||tail->kind!=ST_EXPR)return 0;
    add=body->expression;shift=tail->expression;
    if(add->kind!=EX_ASSIGN||add->left->kind!=EX_OBJECT||
       !reduction_object(shift->left,value)||shift->kind!=EX_ASSIGN)return 0;
    sum=add->left->symbol;
    if(sum==value||!word_integer(sum->type)||!sum->type.is_unsigned||sum->type.is_bool||
       !loop_private(value)||!loop_private(sum))return 0;
    op=shift->op;term=shift->right;
    if(!op){
        if(term->kind!=EX_BINARY||!reduction_object(term->left,value))return 0;
        op=term->op;term=term->right;
    }
    if(reg_width(term->type)>4||!integer_constant(term,&operand)||
       !((op==TOK_SHR&&operand==1)||(op=='/'&&operand==2)))return 0;
    bit=add->right;
    if(!add->op){
        if(bit->kind!=EX_BINARY||bit->op!='+')return 0;
        if(reduction_object(bit->left,sum))bit=bit->right;
        else if(reduction_object(bit->right,sum))bit=bit->left;
        else return 0;
    }else if(add->op!='+')return 0;
    if(bit->kind!=EX_BINARY||(bit->op!='&'&&bit->op!='%'))return 0;
    if(reg_width(bit->right->type)<=4&&integer_constant(bit->right,&operand))term=bit->left;
    else if(bit->op=='&'&&integer_constant(bit->left,&operand))term=bit->right;
    else return 0;
    if(operand!=(bit->op=='&'?1u:2u)||!reduction_object(term,value))return 0;
    loop=++cg.label;even=++cg.label;done=++cg.label;
    code("; register low-bit sum\n");
    load_symbol(sum);code("    tax\n");load_symbol(value);
    code("    beq cg_%s_%u\n",cg.parser->unit,done);label(loop);
    code("    lsr a\n    bcc cg_%s_%u\n"
         "    inx\n    cmp #$0000\n",cg.parser->unit,even);label(even);
    code("    bne cg_%s_%u\n",cg.parser->unit,loop);label(done);
    if(loop_observed_outside(cg.function->body,s,value))store_symbol(value);
    code("    txa\n");store_symbol(sum);
    divmod_state.available=0;
    return 1;
}
