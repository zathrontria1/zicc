/* Word-expression selection. Plans describe arithmetic, never source names */
typedef struct { unsigned factor,shifts,cost;int subtract,negate; } WordScale;
enum { SCALE_SHIFT,SCALE_BYTE_SHIFT,SCALE_ADD,SCALE_SUBTRACT,SCALE_NEGATE,SCALE_ZERO };
static WordScale word_scale_candidate(unsigned factor,int negate,int save)
{
    WordScale p={0};unsigned n=factor,bits=0,ones=0;
    p.factor=factor;p.negate=negate;
    while(n){++bits;ones+=n&1;n>>=1;}
    p.shifts=bits?bits-1:0;
    p.cost=factor?p.shifts*2+(ones-1)*8+(negate?4:0)+(ones>1&&save?4:0):3;
    if(factor>1&&!(factor&(factor+1))){
        unsigned cost=bits*2+8+(negate?4:0)+(save?4:0);
        if(cost<p.cost){p.subtract=1;p.shifts=bits;p.cost=cost;}
    }
    if(p.shifts>=8&&!(cg.parser&&cg.parser->no_byte_shuffles)&&(p.subtract||!(factor&0xFEu))){
        p.cost=p.cost>=11?p.cost-11:1;
    }
    return p;
}
static int word_scale_plan(unsigned factor,int save,WordScale *out)
{
    WordScale p=word_scale_candidate(factor&65535,0,save),negative;
    if(factor&65535){
        negative=word_scale_candidate((0u-factor)&65535,1,save);
        if(negative.cost<p.cost)p=negative;
    }
    /* A bounded inline chain beats even the byte helper plus call/setup.
     * Eight cycles per add/sub conservatively includes its word operand. */
    if(p.cost>40)return 0;
    *out=p;return 1;
}
static int word_scale_needs_base(WordScale *p)
{
    return p->subtract||(p->factor&&(p->factor&(p->factor-1)));
}
static void word_scale_emit_shifts(unsigned count,void (*step)(void *,int),void *context)
{
    if(count>=8&&!(cg.parser&&cg.parser->no_byte_shuffles)){
        step(context,SCALE_BYTE_SHIFT);
        count-=8;
    }
    while(count--)step(context,SCALE_SHIFT);
}
static void word_scale_steps(WordScale *p,void (*step)(void *,int),void *context)
{
    unsigned bit,pending=0;
    if(!p->factor){step(context,SCALE_ZERO);return;}
    if(p->subtract){
        word_scale_emit_shifts(p->shifts,step,context);
        step(context,SCALE_SUBTRACT);
    }else{
        for(bit=p->shifts;bit;){
            --bit;++pending;
            if(p->factor&(1u<<bit)){
                word_scale_emit_shifts(pending,step,context);
                pending=0;
                step(context,SCALE_ADD);
            }
        }
        if(pending)word_scale_emit_shifts(pending,step,context);
    }
    if(p->negate)step(context,SCALE_NEGATE);
}
typedef struct { Expr *base;Type type;int scratch; } WordScaleEmission;
static void word_scale_emit(void *context,int step)
{
    WordScaleEmission *e=context;
    if(step==SCALE_SHIFT)code("    asl a\n");
    else if(step==SCALE_BYTE_SHIFT)code("    xba\n    and #$FF00\n");
    else if(step==SCALE_ZERO)code("    lda #$0000\n");
    else if(step==SCALE_NEGATE)code("    eor #$FFFF\n    inc a\n");
    else{
        code("    %s\n    %s ",step==SCALE_ADD?"clc":"sec",step==SCALE_ADD?"adc":"sbc");
        if(e->scratch)code("z:__arith_rhs");else direct_operand(e->base,e->type,0,1);
        code("\n");
    }
}
static int word_multiply_loaded(Expr *left,Expr *right,Type t)
{
    uint32_t factor;WordScale p;WordScaleEmission emission;
    if(t.pointers||t.base!=TY_INT||!integer_constant(right,&factor))return 0;
    if(!cg.parser->no_strength_reduction&&factor&&!(factor&(factor-1))){
        unsigned count=0;
        while((1u<<count)!=factor&&count<16)++count;
        if(count<16&&word_shift_loaded(left,TOK_SHL,t,count))return 1;
    }
    if(!(cg.parser&&cg.parser->no_byte_shuffles)&&(factor&65535)==0x0101&&unsigned_byte_value(left)){
        cg.arithmetic=1;code("    sta z:__arith_rhs\n    xba\n    ora z:__arith_rhs\n");
        return 1;
    }
    emission.base=left;emission.type=t;emission.scratch=!direct_operand(left,t,0,0);
    if(!word_scale_plan(factor,emission.scratch,&p))return 0;
    if(emission.scratch&&word_scale_needs_base(&p)){
        cg.arithmetic=1;code("    sta z:__arith_rhs\n");
    }
    word_scale_steps(&p,word_scale_emit,&emission);return 1;
}
static int word_constant_product(Expr *e)
{
    Expr *base,*constant;Type t;uint32_t factor;WordScale p;
    if(e->kind!=EX_BINARY||e->op!='*')return 0;
    t=common_type(e->left->type,e->right->type);
    if(t.pointers||t.base!=TY_INT)return 0;
    base=e->left;constant=e->right;
    if(!integer_constant(constant,&factor)){
        base=e->right;constant=e->left;
        if(!integer_constant(constant,&factor))return 0;
    }
    if(!word_scale_plan(factor,!direct_operand(base,t,0,0),&p))return 0;
    emit_value(base);convert_registers(value_type(base->type),t);
    return word_multiply_loaded(base,constant,t);
}

enum { WORD_NONE,WORD_IMMEDIATE,WORD_MEMORY,WORD_X,WORD_SECOND,WORD_TEMP,WORD_ACCUMULATOR };
typedef struct { int kind;unsigned value;Expr *expression; } WordOperand;
typedef struct { const char *op;WordOperand operand;int carry_clear; } WordInstruction;
typedef struct {
    WordInstruction instructions[128];unsigned count,slots,second_left;
    Symbol *first,*second;int failed,leaf,a_second,second_slot;
} WordPlan;
static unsigned expression_references(Expr *e,Symbol *v);
static WordOperand word_operand_value(int kind,unsigned value)
{
    WordOperand operand={0};operand.kind=kind;operand.value=value;return operand;
}
static int word_integer(Type t)
{
    return t.base==TY_INT&&!t.pointers&&!t.array;
}
static int word_operand(WordPlan *p,Expr *e,WordOperand *out)
{
    uint32_t value;
    if(!word_integer(e->type))return 0;
    if(integer_constant(e,&value)){*out=word_operand_value(WORD_IMMEDIATE,value&65535);return 1;}
    while(e->kind==EX_CAST&&word_integer(e->left->type))e=e->left;
    if(p->leaf&&e->kind==EX_OBJECT){
        if(e->symbol==p->first){*out=word_operand_value(WORD_X,0);return 1;}
        if(e->symbol==p->second){*out=word_operand_value(WORD_SECOND,0);return 1;}
    }
    if(!direct_operand(e,e->type,0,0))return 0;
    *out=word_operand_value(WORD_MEMORY,0);out->expression=e;return 1;
}
static int word_product(WordPlan *p,Expr *e,Expr **base,WordScale *scale)
{
    uint32_t factor;WordOperand operand;int save;
    if(e->kind!=EX_BINARY||e->op!='*'||!word_integer(e->type))return 0;
    *base=e->left;
    if(!integer_constant(e->right,&factor)){
        *base=e->right;if(!integer_constant(e->left,&factor))return 0;
    }
    save=!word_operand(p,*base,&operand)||operand.kind==WORD_X||operand.kind==WORD_SECOND;
    return word_scale_plan(factor,save,scale);
}
static int word_supported(WordPlan *p,Expr *e)
{
    WordOperand operand;WordScale scale;Expr *base,*keep;uint32_t count;
    if(!word_integer(e->type))return 0;
    if(identity_binary_operand(e,&keep)&&word_integer(keep->type))return word_supported(p,keep);
    if(word_operand(p,e,&operand))return 1;
    if(e->kind==EX_CAST)return word_integer(e->left->type)&&word_supported(p,e->left);
    if(e->kind==EX_UNARY&&(e->op=='+'||e->op=='-'||e->op=='~'))return word_supported(p,e->left);
    if(e->kind!=EX_BINARY)return 0;
    if(basic_integer_op(e->op))return word_supported(p,e->left)&&word_supported(p,e->right);
    if(word_product(p,e,&base,&scale))return word_supported(p,base);
    return (e->op==TOK_SHL||e->op==TOK_SHR)&&integer_constant(e->right,&count)&&count<16&&word_supported(p,e->left);
}
static void word_instruction(WordPlan *p,const char *op,WordOperand operand)
{
    if(p->failed)return;
    if(p->count==sizeof p->instructions/sizeof p->instructions[0]){p->failed=1;return;}
    p->instructions[p->count].op=op;p->instructions[p->count++].operand=operand;
}
static void word_implied(WordPlan *p,const char *op)
{
    word_instruction(p,op,word_operand_value(WORD_NONE,0));
}
static int word_slot(WordPlan *p)
{
    unsigned slot;for(slot=0;slot<4;++slot)if(!(p->slots&(1u<<slot))){p->slots|=1u<<slot;return (int)slot;}
    p->failed=1;return -1;
}
static void word_release(WordPlan *p,int slot)
{
    if(slot>=0)p->slots&=~(1u<<(unsigned)slot);
}
static void word_save_second(WordPlan *p)
{
    if(p->second_slot>=0)return;
    if(!p->a_second){p->failed=1;return;}
    p->second_slot=word_slot(p);
    word_instruction(p,"sta",word_operand_value(WORD_TEMP,(unsigned)p->second_slot));
}
static void word_clobber_a(WordPlan *p)
{
    if(p->a_second&&p->second_left)word_save_second(p);
    p->a_second=0;
}
/* Resolve a direct input without changing A. X is never used for temporaries,
 * so parameter 0 can be materialized at any use. Parameter 1 is saved lazily
 * only if a write to A would otherwise destroy a future use. */
static WordOperand word_resolve(WordPlan *p,WordOperand operand,int consume,int *slot)
{
    *slot=-1;
    if(operand.kind==WORD_X){
        *slot=word_slot(p);operand=word_operand_value(WORD_TEMP,(unsigned)*slot);
        word_instruction(p,"stx",operand);
    }else if(operand.kind==WORD_SECOND){
        word_save_second(p);operand=word_operand_value(WORD_TEMP,(unsigned)p->second_slot);
        if(consume&&p->second_left)--p->second_left;
    }
    return operand;
}
static void word_load(WordPlan *p,WordOperand operand)
{
    if(operand.kind==WORD_SECOND){
        if(!p->a_second&&p->second_slot<0){p->failed=1;return;}
        if(!p->a_second)word_instruction(p,"lda",word_operand_value(WORD_TEMP,(unsigned)p->second_slot));
        if (p->second_left) {
            --p->second_left;
        }
        p->a_second = 1;
        return;
    }
    word_clobber_a(p);
    if(operand.kind==WORD_X)word_implied(p,"txa");else word_instruction(p,"lda",operand);
}
static void word_arithmetic(WordPlan *p,int op,WordOperand operand)
{
    word_clobber_a(p);
    if(op=='+'||op=='-')word_implied(p,op=='+'?"clc":"sec");
    word_instruction(p,op=='+'?"adc":op=='-'?"sbc":op=='&'?"and":op=='|'?"ora":"eor",operand);
}
typedef struct { WordPlan *plan;WordOperand base; } WordScalePlan;
static void word_scale_instruction(void *context,int step)
{
    WordScalePlan *scale=context;WordPlan *p=scale->plan;
    if(step==SCALE_ADD||step==SCALE_SUBTRACT){word_arithmetic(p,step==SCALE_ADD?'+':'-',scale->base);return;}
    word_clobber_a(p);
    if(step==SCALE_SHIFT)word_instruction(p,"asl",word_operand_value(WORD_ACCUMULATOR,0));
    else if(step==SCALE_BYTE_SHIFT){
        word_implied(p,"xba");
        word_instruction(p,"and",word_operand_value(WORD_IMMEDIATE,65280));
    }else if(step==SCALE_ZERO)word_instruction(p,"lda",word_operand_value(WORD_IMMEDIATE,0));
    else{
        word_instruction(p,"eor",word_operand_value(WORD_IMMEDIATE,65535));
        word_instruction(p,"inc",word_operand_value(WORD_ACCUMULATOR,0));
    }
}
static void word_evaluate(WordPlan *p,Expr *e);
static void word_emit_shift(WordPlan *p,Expr *left,int op,Type result,unsigned count,unsigned mask_after)
{
    WordShift shift;Expr *inner;unsigned diff,sub_mask,sign;
    if(mask_after==65535u&&word_shift_combine(left,op,result,count,&inner,&diff,&sub_mask)){
        word_emit_shift(p,inner,TOK_SHL,result,diff,sub_mask);
        return;
    }
    word_evaluate(p,left);
    sign=word_shift_sign(left,op,result,count);
    if(sign){
        WordOperand mask=word_operand_value(WORD_IMMEDIATE,sign);
        word_clobber_a(p);
        if(count>=8&&!(cg.parser&&cg.parser->no_byte_shuffles)){
            word_implied(p,"xba");
            word_instruction(p,"and",word_operand_value(WORD_IMMEDIATE,255));
            count-=8;
        }
        while(count--)word_instruction(p,"lsr",word_operand_value(WORD_ACCUMULATOR,0));
        word_instruction(p,"eor",mask);
        word_implied(p,"sec");
        word_instruction(p,"sbc",mask);
    }else if(word_shift_plan(left,op,result,count,&shift)){
        word_clobber_a(p);word_implied(p,"xba");
        if(op==TOK_SHL&&mask_after!=65535u&&count>=8){
            while(shift.steps--)word_instruction(p,shift.left?"asl":"lsr",word_operand_value(WORD_ACCUMULATOR,0));
            word_instruction(p,"and",word_operand_value(WORD_IMMEDIATE,mask_after));
            return;
        }
        if(shift.mask)word_instruction(p,"and",word_operand_value(WORD_IMMEDIATE,shift.mask));
        while(shift.steps--)word_instruction(p,shift.left?"asl":"lsr",word_operand_value(WORD_ACCUMULATOR,0));
    }else{
        while(count--){
            word_clobber_a(p);
            if(op==TOK_SHR&&!result.is_unsigned&&!(left->known.valid&&left->known.min>=0)){
                word_instruction(p,"cmp",word_operand_value(WORD_IMMEDIATE,32768));
                word_instruction(p,"ror",word_operand_value(WORD_ACCUMULATOR,0));
            }else word_instruction(p,op==TOK_SHL?"asl":"lsr",word_operand_value(WORD_ACCUMULATOR,0));
        }
    }
    if(mask_after!=65535u){
        word_clobber_a(p);
        word_instruction(p,"and",word_operand_value(WORD_IMMEDIATE,mask_after));
    }
}
static void word_evaluate(WordPlan *p,Expr *e)
{
    WordOperand left,right,operand;WordScale scale;WordScalePlan scaled;Expr *base,*keep;
    uint32_t count;int lhs,rhs,slot=-1,temporary;
    if(p->failed)return;
    if(identity_binary_operand(e,&keep)&&word_integer(keep->type)){word_evaluate(p,keep);return;}
    if(word_operand(p,e,&operand)){word_load(p,operand);return;}
    if(e->kind==EX_CAST){word_evaluate(p,e->left);return;}
    if(e->kind==EX_UNARY){
        word_evaluate(p,e->left);if(e->op=='+')return;word_clobber_a(p);
        word_instruction(p,"eor",word_operand_value(WORD_IMMEDIATE,65535));
        if (e->op == '-') {
            word_instruction(p, "inc", word_operand_value(WORD_ACCUMULATOR, 0));
        }
        return;
    }
    if(word_product(p,e,&base,&scale)){
        if(!cg.parser->no_strength_reduction&&!scale.negate&&scale.factor&&!(scale.factor&(scale.factor-1))){
            word_emit_shift(p,base,TOK_SHL,e->type,scale.shifts,65535u);return;
        }
        if(!(cg.parser&&cg.parser->no_byte_shuffles)&&(scale.factor&65535)==0x0101&&unsigned_byte_value(base)){
            word_evaluate(p,base);word_clobber_a(p);
            slot=word_slot(p);operand=word_operand_value(WORD_TEMP,(unsigned)slot);
            word_instruction(p,"sta",operand);word_implied(p,"xba");
            word_instruction(p,"ora",operand);word_release(p,slot);return;
        }
        word_evaluate(p,base);scaled.plan=p;scaled.base=word_operand_value(WORD_NONE,0);
        if(word_scale_needs_base(&scale)){
            if(word_operand(p,base,&operand))scaled.base=word_resolve(p,operand,0,&slot);
            else{slot=word_slot(p);scaled.base=word_operand_value(WORD_TEMP,(unsigned)slot);word_instruction(p,"sta",scaled.base);}
        }
        word_scale_steps(&scale,word_scale_instruction,&scaled);word_release(p,slot);return;
    }
    if(e->op==TOK_SHL||e->op==TOK_SHR){
        integer_constant(e->right,&count);
        word_emit_shift(p,e->left,e->op,promoted(e->left->type),(unsigned)count,65535u);
        return;
    }
    lhs=word_operand(p,e->left,&left);rhs=word_operand(p,e->right,&right);
    if(rhs){word_evaluate(p,e->left);operand=word_resolve(p,right,1,&slot);}
    else if(lhs&&e->op!='-'){word_evaluate(p,e->right);operand=word_resolve(p,left,1,&slot);}
    else{
        word_evaluate(p,e->op=='-'?e->right:e->left);
        temporary=word_slot(p);operand=word_operand_value(WORD_TEMP,(unsigned)temporary);
        word_instruction(p,"sta",operand);word_evaluate(p,e->op=='-'?e->left:e->right);slot=temporary;
    }
    word_arithmetic(p,e->op,operand);
    if(!p->failed&&e->op=='+'&&e->type.is_unsigned&&e->left->known.valid&&e->right->known.valid&&
       e->left->known.min>=0&&e->right->known.min>=0&&
       e->left->known.max+e->right->known.max<=65535)
        p->instructions[p->count-1].carry_clear=1;
    word_release(p,slot);
}
static void word_emit_plan(WordPlan *p)
{
    unsigned i;
    for(i=0;i<p->count;++i){
        WordInstruction *instruction=&p->instructions[i];WordOperand *o=&instruction->operand;
        if(instruction->carry_clear)code("; ADC cannot carry\n");
        if(!strcmp(instruction->op,"lda")&&o->kind==WORD_MEMORY){emit_value(o->expression);continue;}
        code("    %s",instruction->op);
        if(o->kind==WORD_IMMEDIATE)code(" #$%04X",o->value);
        else if(o->kind==WORD_MEMORY){code(" ");direct_operand(o->expression,o->expression->type,0,1);}
        else if(o->kind==WORD_TEMP){cg.arithmetic=1;code(" z:__arith_%s%s",o->value<2?"lhs":"rhs",o->value&1?"+2":"");}
        else if(o->kind==WORD_ACCUMULATOR)code(" a");
        code("\n");
    }
}
static WordPlan *word_plan(Expr *e,Function *f,int leaf)
{
    WordPlan *p=allocate(sizeof *p);p->leaf=leaf;p->second_slot=-1;
    if(leaf){
        if(f->symbol->param_count>0)p->first=leaf_parameter(f,0);
        if(f->symbol->param_count>1)p->second=leaf_parameter(f,1);
        if(p->second){p->a_second=1;p->second_left=expression_references(e,p->second);}
    }
    if(!word_supported(p,e)){free(p);return NULL;}
    word_evaluate(p,e);
    if(p->failed){free(p);return NULL;}
    return p;
}
static int word_expression(Expr *e)
{
    WordPlan *p;
    if(cg.stack_leaf||cg.leaf_count)return 0;
    p=word_plan(e,cg.function,0);if(!p)return 0;
    word_emit_plan(p);free(p);return 1;
}
static int word_expression_leaf(Function *f)
{
    Statement *s=f->body;Symbol *fn=f->symbol;WordPlan *p;unsigned i,offset=3+cg.parser->long_return,saved[MAX_PARAMETERS];
    if(!strcmp(fn->name,"main")||fn->param_count<0||!word_integer(fn->type)||
       f->slots!=(unsigned)fn->param_count*2)return 0;
    for(i=0;i<(unsigned)fn->param_count;++i)if(!word_integer(fn->params[i]))return 0;
    if(s->kind==ST_BLOCK)s=s->body;
    while(s&&(s->kind==ST_EMPTY||(s->kind==ST_BLOCK&&!s->body)))s=s->next;
    if(!s||s->next||s->kind!=ST_RETURN||!s->expression)return 0;
    p=word_plan(s->expression,f,1);if(!p)return 0;
    for(i=2;i<(unsigned)fn->param_count;++i){Symbol *v=leaf_parameter(f,i);saved[i]=v->offset;v->offset=offset;offset+=2;}
    cg.stack_leaf=1;cg.stack_bias=0;
    code(".segment \"CODE\"\n.export _%s\n_%s:\n; native word expression leaf\n",fn->asm_name,fn->asm_name);
    {Statement *prefix=f->body;if(prefix->kind==ST_BLOCK)prefix=prefix->body;
     for(;prefix&&prefix!=s;prefix=prefix->next)inline_marker(prefix);}
    word_emit_plan(p);code("    rts\n__size_%s = * - _%s\n",fn->asm_name,fn->asm_name);
    cg.stack_leaf=0;
    for(i=2;i<(unsigned)fn->param_count;++i)leaf_parameter(f,i)->offset=saved[i];
    free(p);return 1;
}

static Expr *word_uncast(Expr *e)
{
    while (e->kind == EX_CAST && known_conversion(e->left, e->type)) {
        e = e->left;
    }
    return e;
}
static Expr *word_bits(Expr *e);
static Symbol *fixed_byte_home(Expr *e,unsigned byte,unsigned *offset);

/* CMP leaves the selected input in A. A signed zero test on the other
 * path can use the same bits, even when the outer comparison is unsigned. */
static int accumulator_constant_choose(Expr *e)
{
    Expr *test=e->left,*value,*keep,*other;
    Type t;
    uint32_t limit,lo=0,hi;
    unsigned done;
    const char *keep_branch="bcc";
    int below,sign=0,equality,compare_sign=0;
    if(!word_integer(e->type)||!test||body_effect(e)||test->kind!=EX_BINARY||
       !integer_constant(test->right,&limit))return 0;
    t=common_type(test->left->type,test->right->type);
    if(!word_integer(t))return 0;
    equality=test->op==TOK_EQ||test->op==TOK_NE;
    if(equality)keep_branch=test->op==TOK_EQ?"beq":"bne";
    else if(!t.is_unsigned||
            (test->op!='<'&&test->op!=TOK_GE&&test->op!=TOK_LE&&test->op!='>'))return 0;
    limit&=65535;
    below=equality||test->op=='<'||test->op==TOK_LE;
    if(test->op==TOK_LE||test->op=='>'){
        if(limit==65535)return 0;
        ++limit;
    }
    value=word_bits(test->left);
    keep=below?e->right:e->third;
    other=below?e->third:e->right;
    if(equality&&body_equal(value,word_bits(other))){
        Expr *swap=keep;
        keep=other;other=swap;
        keep_branch=test->op==TOK_EQ?"bne":"beq";
    }
    if(!word_integer(value->type)||!body_equal(value,word_bits(keep)))return 0;
    if(!integer_constant(other,&hi)){
        Expr *branch=word_bits(other),*condition;
        if(branch->kind!=EX_CHOOSE)return 0;
        condition=branch->left;
        if(condition->kind!=EX_BINARY||condition->op!='<')return 0;
        t=common_type(condition->left->type,condition->right->type);
        if(!word_integer(t)||t.is_unsigned||
           !integer_constant(condition->right,&lo)||lo||
           !body_equal(value,word_bits(condition->left))||
           !integer_constant(branch->right,&lo)||!integer_constant(branch->third,&hi))return 0;
        sign=1;
        /* N after CMP agrees with the original sign if subtracting the
         * threshold cannot cross INT_MIN. On the out-of-range edge a
         * nonnegative input is necessarily at least the threshold. */
        compare_sign=below&&!equality&&limit<=32767&&value->known.valid&&
            value->known.min>=(int32_t)limit-32768&&value->known.max<=32767;
    }
    done=++cg.label;
    code("; accumulator conditional join\n");
    emit_value(value);
    code("    cmp #$%04X\n    %s cg_%s_%u\n",limit,keep_branch,cg.parser->unit,done);
    if(sign){
        if(compare_sign)code("    bpl :+\n");
        else code("    bit #$8000\n    beq :+\n");
        code("    lda #$%04X\n",lo&65535);
        jump(done);
        code(":\n");
    }
    code("    lda #$%04X\n",hi&65535);
    /* Set N and Z from the chosen value, even when CMP last set the flags */
    label(done);code("    ora #$0000\n");
    return 1;
}
static int word_unit_offset(Expr *e,Expr **base)
{
    uint32_t n;
    e=word_bits(e);
    if(e->kind!=EX_BINARY||!word_integer(e->type)||(e->op!='+'&&e->op!='-'))return 0;
    if(integer_constant(e->right,&n)&&(n&65535)==1){
        *base=word_bits(e->left);
        return e->op=='+'?1:-1;
    }
    if(e->op=='+'&&integer_constant(e->left,&n)&&(n&65535)==1){*base=word_bits(e->right);return 1;}
    return 0;
}
/* Rotate the unit offset across equality so the compared value can also be
 * the result. The full word matters when the limit is an unsigned byte. */
static int accumulator_step_choose(Expr *e)
{
    Expr *test=e->left,*base,*limit,*plain,*arms[2];
    Symbol *byte=NULL;
    unsigned offset=0,done;
    uint32_t replacement;
    int step,equal;
    if(!word_integer(e->type)||e->type.is_bool||test->kind!=EX_BINARY||
       (test->op!=TOK_EQ&&test->op!=TOK_NE)||
       !word_integer(common_type(test->left->type,test->right->type))||body_effect(e))return 0;
    equal=test->op==TOK_EQ;
    arms[0]=word_bits(test->left);arms[1]=word_bits(test->right);
    step=word_unit_offset(equal?e->third:e->right,&base);
    if(!step||!word_integer(base->type)||!integer_constant(equal?e->right:e->third,&replacement))return 0;
    if(body_equal(base,arms[0]))limit=arms[1];
    else if(body_equal(base,arms[1]))limit=arms[0];
    else return 0;
    if(word_unit_offset(limit,&plain)!=-step)return 0;
    limit=word_uncast(plain);
    if(!compare_memory_operand(limit,0)){
        if(limit->type.base!=TY_CHAR||!limit->type.is_unsigned||
           !(byte=fixed_byte_home(limit,0,&offset)))return 0;
    }
    done=++cg.label;
    code("; accumulator stepped conditional join\n");
    emit_value(base);
    code(step>0?"    inc a\n":"    dec a\n");
    if(byte){
        code("    cmp #$0100\n    bcs cg_%s_%u\n    sep #$20\n.a8\n    cmp ",cg.parser->unit,done);
        array_operand(byte,offset);code("\n    rep #$20\n.a16\n");
    }else{code("    cmp ");compare_memory_operand(limit,1);code("\n");}
    code("    bne cg_%s_%u\n    lda #$%04X\n",cg.parser->unit,done,replacement&65535);
    label(done);code("    ora #$0000\n");
    return 1;
}
static int word_compare_loaded(Expr *e,unsigned yes,unsigned no,unsigned fallthrough);
static int load_raw_signed_byte(Expr *input);
/* A comparison with zero leaves the sign-extended input available on the
 * selected arm. Evaluate any alternative only on its original path. */
static int accumulator_zero_choose(Expr *e,Type result)
{
    Expr *test=e->left,*value,*other;
    Expr converted={0};
    Type t;
    unsigned done,replace;
    int keep_yes;
    if(cg.parser->no_body_optimizations||cg.parser->no_strength_reduction||!word_integer(e->type)||
       test->kind!=EX_BINARY||!comparison(test->op)||
       test->right->kind!=EX_INT||test->right->value)return 0;
    value=word_uncast(test->left);
    t=common_type(test->left->type,test->right->type);
    if(!word_integer(t)||!known_integer(value->type)||volatile_expression(value)||body_effect(value))return 0;
    if(!word_integer(result)&&!known_conversion(value,result))return 0;
    keep_yes=body_equal(value,word_uncast(e->right));
    if(!keep_yes&&!body_equal(value,word_uncast(e->third)))return 0;
    other=keep_yes?e->third:e->right;
    if(!word_integer(result)){
        converted.kind=EX_CAST;converted.type=result;converted.left=other;
        other=&converted;
    }
    done=++cg.label;replace=++cg.label;
    if(!t.is_unsigned&&(test->op==TOK_LE||test->op=='>')&&load_raw_signed_byte(value))
        code("    and #$00FF\n    eor #$0080\n    sec\n    sbc #$0080\n");
    else emit_value(value);
    word_compare_loaded(test,keep_yes?done:replace,keep_yes?replace:done,replace);
    label(replace);emit_value(other);
    label(done);code("    ora #$0000\n");
    divmod_state.available=0;
    return 1;
}
static int accumulator_choose(Expr *e)
{
    Expr *test=e->left,*value,*keep,*other,*operand;uint32_t limit,constant;Type t;unsigned done;
    int op;
    if(cg.parser->no_body_optimizations)return 0;
    if(accumulator_constant_choose(e)||accumulator_step_choose(e)||accumulator_zero_choose(e,e->type))return 1;
    if(volatile_expression(e)||!test||test->kind!=EX_BINARY||
       !integer_constant(test->right,&limit)||reg_width(e->type)!=2)return 0;
    op=test->op;
    if(op!='<'&&op!='>'&&op!=TOK_LE&&op!=TOK_GE)return 0;
    value=word_uncast(test->left);keep=word_uncast(e->right);other=word_uncast(e->third);
    t=common_type(test->left->type,test->right->type);
    if(!word_integer(t)||body_effect(value)||
       (!t.is_unsigned&&(!value->known.valid||value->known.min<0||value->known.max>32767||limit>32767)))return 0;
    if(!body_equal(value,keep)){
        if(!body_equal(value,other))return 0;
        other=keep;
        op=op=='<'?TOK_GE:op==TOK_GE?'<':op=='>'?TOK_LE:'>';
    }
    if(other->kind!=EX_BINARY||!word_integer(other->type)||!basic_integer_op(other->op)||other->op=='-'||
       !integer_constant(other->right,&constant))return 0;
    operand=word_uncast(other->left);if(!body_equal(value,operand))return 0;
    limit&=65535;
    if(op=='>'||op==TOK_LE){
        if(limit==65535)return 0;
        ++limit;
    }
    done=++cg.label;code("; accumulator conditional join\n");emit_value(value);
    code("    cmp #$%04X\n    %s cg_%s_%u\n",limit,op=='<'||op==TOK_LE?"bcc":"bcs",cg.parser->unit,done);
    if(other->op=='+')code("    clc\n");
    code("    %s #$%04X\n",other->op=='+'?"adc":other->op=='&'?"and":other->op=='|'?"ora":"eor",constant&65535);
    label(done);code("    ora #$0000\n");convert_registers(value_type(other->type),e->type);return 1;
}
