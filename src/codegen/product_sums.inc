/* In a sum of two widened products, one factor pair can use four byte
 * multiplies when the long fits a word and both variable factors fit a
 * byte. Keep the original expression on the out-of-range path. */
static int narrow_product_sum(Expr *e)
{
    Expr *scaled=e->right,*product=e->left,*word,*factor,*wide,*value;
    Type t=e->type,word_type=type(TY_INT,1);
    IndexedOperand indexed;
    uint32_t constant;
    unsigned low,high,largest,limit,slow,done;
    if(cg.parser->no_body_optimizations||cg.parser->no_strength_reduction||
       cg.function->symbol->interrupt||cg.retained_index||cg.retained_second||
       t.base!=TY_LONG||!t.is_unsigned||t.pointers||e->op!='+'||
       product->kind!=EX_BINARY||product->op!='*'||scaled->kind!=EX_BINARY||scaled->op!='*'||
       reg_width(product->type)!=4||reg_width(scaled->type)!=4||body_effect(e))return 0;
    if(!integer_constant(scaled->left,&constant)&&!integer_constant(scaled->right,&constant)){
        scaled=e->left;product=e->right;
    }
    if(integer_constant(scaled->left,&constant))word=scaled->right;
    else if(integer_constant(scaled->right,&constant))word=scaled->left;
    else return 0;
    low=(unsigned)constant&255;high=(unsigned)(constant>>8);
    if(!low||!high||high>255)return 0;
    largest=low>high?low:high;
    /* Bound both 16-bit columns, including the carry byte into the upper
     * column. The products and their sum then fit in 24 bits. */
    limit=(65535u-255u*largest-255u)/255u;
    if(limit<32)return 0;
    factor=widened_word(product->left);
    wide=product->right;
    if(!factor){factor=widened_word(product->right);wide=product->left;}
    value=widened_word(word);
    if(!factor||!factor->type.is_unsigned||!direct_operand(factor,word_type,0,0)||
       !value||!value->type.is_unsigned||
       (!direct_operand(value,word_type,0,0)&&!indexed_operand(value,&indexed))||
       widened_word(wide)||!direct_operand(wide,t,0,0)||!direct_operand(wide,t,1,0))return 0;
    slow=++cg.label;done=++cg.label;
    cg.arithmetic=1;divmod_state.available=0;
    code("; guarded narrow sum of widened products\n    lda ");
    direct_operand(wide,t,1,1);code("\n");
    flag_branch("bne","beq",slow,0,0);
    code("    lda ");direct_operand(factor,word_type,0,1);
    code("\n    cmp #$%04X\n",limit+1);
    flag_branch("bcs","bcc",slow,0,0);
    emit_value(value);
    code("    cmp #$0100\n");
    flag_branch("bcs","bcc",slow,0,0);
    code("    sta z:__arith_lhs\n    lda ");direct_operand(wide,t,0,1);
    code("\n    sta z:__arith_rhs\n    lda ");direct_operand(factor,word_type,0,1);
    code("\n    sta z:__arith_rhs+2\n    lda z:__arith_lhs\n");
    /* Absolute hardware accesses require a system DBR. All application
     * operand loads are complete before switching banks, and IRQ/NMI keep DBR. */
    code("    phb\n    pea $0000\n    plb\n    plb\n    sep #$20\n.a8\n"
         "    sta a:$4202\n    lda #$%02X\n    sta a:$4203\n    lda #$%02X\n"
         "    nop\n    nop\n    ldx a:$4216\n    sta a:$4203\n    stx z:__arith_lhs\n"
         "    lda z:__arith_rhs+2\n    ldx a:$4216\n    sta a:$4202\n"
         "    lda z:__arith_rhs\n    sta a:$4203\n    stx z:__arith_lhs+2\n"
         "    lda z:__arith_rhs+1\n    ldx a:$4216\n    sta a:$4203\n"
         "    rep #$20\n.a16\n    txa\n    clc\n    adc z:__arith_lhs\n    sta z:__arith_rhs\n"
         "    stz z:__arith_rhs+2\n    lda a:$4216\n    adc z:__arith_lhs+2\n"
         "    adc z:__arith_rhs+1\n    sta z:__arith_rhs+1\n    plb\n"
         "    ldx z:__arith_rhs+2\n    lda z:__arith_rhs\n",low,high);
    jump(done);
    label(slow);
    emit_value(e->left);binary_after_left(e->left,e->right,'+');
    label(done);
    divmod_state.available=0;
    return 1;
}
