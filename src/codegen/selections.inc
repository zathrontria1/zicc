/* Pure word min/max selections. A direct operand never needs arithmetic
 * workspace or a temporary index; this also makes two selections safe to
 * evaluate in reverse order for a following subtraction. */
static int selection_operand(Expr *e,int emit)
{
    IndexedOperand operand={0};
    if(width(e->type)!=2||!word_integer(e->type)||!indexed_pure(e))return 0;
    if(direct_operand(e,e->type,0,0)){
        if(emit)direct_operand(e,e->type,0,1);return 1;
    }
    if(!indexed_operand(e,&operand)||!indexed_retained(&operand,1))return 0;
    if(emit)indexed_text(&operand);return 1;
}
static int selection_minmax(Expr *e,int *minimum)
{
    Expr *test,*yes,*no;int normal;
    e=word_uncast(e);
    if(e->kind!=EX_CHOOSE||!word_integer(e->type)||volatile_expression(e))return 0;
    test=e->left;yes=word_uncast(e->right);no=word_uncast(e->third);
    if(test->kind!=EX_BINARY||(test->op!='<'&&test->op!='>'&&test->op!=TOK_LE&&test->op!=TOK_GE)||
       !selection_operand(test->left,0)||!selection_operand(test->right,0))return 0;
    normal=body_equal(word_uncast(test->left),yes)&&body_equal(word_uncast(test->right),no);
    if(!normal&&!(body_equal(word_uncast(test->right),yes)&&body_equal(word_uncast(test->left),no)))return 0;
    *minimum=normal==(test->op=='<'||test->op==TOK_LE);return 1;
}
static void selection_emit(Expr *e,int minimum)
{
    Expr *test;Type t;unsigned left=++cg.label,done=++cg.label;int ordered,bounded;
    e=word_uncast(e);test=e->left;t=common_type(test->left->type,test->right->type);
    ordered=t.is_unsigned||(test->left->known.valid&&test->right->known.valid&&
        ((test->left->known.min>=0&&test->right->known.min>=0)||
         (test->left->known.max<0&&test->right->known.max<0)));
    bounded=!ordered&&word_difference_safe(test->left,test->right);
    code("; direct word min/max selection\n");emit_value(test->left);
    if(ordered||bounded){
        /* CMP preserves A. N orders signed values when A-rhs cannot overflow;
         * carry orders unsigned/same-sign values. Equality may choose either. */
        const char *take=ordered?(minimum?"bcc":"bcs"):(minimum?"bmi":"bpl");
        if(bounded)code("; bounded signed min/max: CMP/N\n");
        code("    cmp ");selection_operand(test->right,1);code("\n    %s cg_%s_%u\n",take,cg.parser->unit,done);
        emit_value(test->right);
    }else{
        code("    sec\n    sbc ");selection_operand(test->right,1);
        code("\n    bvc :+\n    eor #$8000\n:\n");
        code("    %s cg_%s_%u\n",minimum?"bmi":"bpl",cg.parser->unit,left);
        emit_value(test->right);jump(done);label(left);emit_value(test->left);
    }
    label(done);code("    ora #$0000\n");
}
/* Short bit projections avoid branches and still evaluate the input once */
static int selection_bit(Expr *e)
{
    uint32_t yes,no,mask;
    Expr *test=e->left;
    if(e->kind!=EX_CHOOSE||!word_integer(e->type)||test->kind!=EX_BINARY||test->op!='&'||
       !word_integer(test->type)||!integer_constant(test->right,&mask)||
       !integer_constant(e->right,&yes)||!integer_constant(e->third,&no)||yes>1||no!=(1-yes))return 0;
    switch(mask){
    case 1:case 2:case 4:case 256:case 512:case 1024:case 32768:break;
    default:return 0;
    }
    emit_value(test->left);
    if(mask==32768)code("    asl a\n    lda #0\n    rol a\n");
    else{
        if(mask>=256){code("    xba\n");mask>>=8;}
        for(;mask>1;mask>>=1)code("    lsr a\n");
        code("    and #1\n");
    }
    if(!yes)code("    eor #1\n");
    return 1;
}
static int selection_saturating_sub(Expr *e,int byte_target);
static int selection_value(Expr *e)
{
    int a,b;
    if(cg.parser->no_body_optimizations)return 0;
    if(!cg.parser->no_strength_reduction&&selection_bit(e))return 1;
    if(selection_saturating_sub(e,0))return 1;
    if(selection_minmax(e,&a)){selection_emit(e,a);return 1;}
    if(e->kind!=EX_BINARY||e->op!='-'||!word_integer(e->type)||
       !selection_minmax(e->left,&a)||!selection_minmax(e->right,&b))return 0;
    code("; fused selection subtraction\n");selection_emit(e->right,b);
    cg.arithmetic=1;code("    sta z:__arith_rhs+2\n");selection_emit(e->left,a);
    code("    sec\n    sbc z:__arith_rhs+2\n");return 1;
}
