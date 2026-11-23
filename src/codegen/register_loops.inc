/* Local loop IR: allocate private running byte pointers to X/Y and select
 * one accumulator width for the region. Ordinary frame homes are restored
 * at its boundary. No AST rewriting or function/name-specific recognition. */
enum { LOOP_LOAD, LOOP_LITERAL, LOOP_ALU, LOOP_STORE, LOOP_STEP, LOOP_SAVE, LOOP_RESTORE };
typedef struct { int kind,reg,op;unsigned value; } LoopInstruction;
enum { LOOP_TEST, LOOP_COMPARE };
typedef struct { int kind,reg,other,op; } LoopPredicate;
typedef struct {
    Symbol *pointers[2],*counters[8],*remaining;
    int strides[2],deltas[8],sentinel,anchor;
    unsigned pointer_count,counter_count,instruction_count;
    LoopInstruction instructions[128];
    Symbol *indices[2],*temporary;
    Expr *addresses[2];Statement *statement;
    int indexed,temporary_live;
    LoopPredicate predicates[8];unsigned predicate_count;
} RegisterLoop;

static int loop_mentions(Expr *e,Symbol *symbol)
{
    unsigned i;if(!e)return 0;
    if(e->kind==EX_OBJECT&&e->symbol==symbol)return 1;
    if(loop_mentions(e->left,symbol)||loop_mentions(e->right,symbol)||loop_mentions(e->third,symbol))return 1;
    for(i=0;i<e->arg_count;++i)if(loop_mentions(e->args[i],symbol))return 1;
    return 0;
}
static int loop_escapes_expr(Expr *e,Symbol *symbol)
{
    unsigned i;if(!e)return 0;
    if(e->kind==EX_ADDRESS){
        if(symbol->type.array||structure_object(symbol->type))return loop_mentions(e->left,symbol);
        /* Taking &array[i] or &p->member reads a scalar index or pointer */
        Expr *object=e->left;
        while(object->kind==EX_MEMBER&&object->op!=TOK_ARROW)object=object->left;
        if(object->kind==EX_OBJECT&&object->symbol==symbol)return 1;
    }
    if(loop_escapes_expr(e->left,symbol)||loop_escapes_expr(e->right,symbol)||loop_escapes_expr(e->third,symbol))return 1;
    for(i=0;i<e->arg_count;++i)if(loop_escapes_expr(e->args[i],symbol))return 1;
    return 0;
}
static int loop_escapes(Statement *s,Symbol *symbol)
{
    for(;s;s=s->next)if(loop_escapes_expr(s->expression,symbol)||loop_escapes_expr(s->step,symbol)||
        loop_escapes(s->initial,symbol)||loop_escapes(s->body,symbol)||loop_escapes(s->alternate,symbol))return 1;
    return 0;
}
static int loop_private(Symbol *s)
{
    return s->owner==cg.function->id&&!s->type.array&&!loop_escapes(cg.function->body,s);
}
static int loop_pointer(RegisterLoop *loop,Symbol *s)
{
    unsigned i;
    if(loop->indexed)return -1;
    for(i=0;i<loop->pointer_count;++i)if(loop->pointers[i]==s)return (int)i;
    if(loop->pointer_count==2||s->type.element||s->type.pointers!=1||s->type.base!=TY_CHAR||!loop_private(s))return -1;
    i=loop->pointer_count++;loop->pointers[i]=s;return (int)i;
}
static int loop_index(RegisterLoop *loop,Symbol *s)
{
    if(!loop->indexed)return -1;
    if (loop->indices[0] == s) return 0;
    if (loop->indices[1] == s) return 1;
    return -1;
}
static Symbol *loop_address(Expr *e,int *pre,int *post);
static int loop_cursor(RegisterLoop *loop,Expr *address,int *pre,int *post)
{
    Symbol *s,*index;unsigned delta;int reg;Type element;
    if(!loop->indexed){s=loop_address(address,pre,post);return s?loop_pointer(loop,s):-1;}
    *pre=*post=0;
    if(address->kind!=EX_BINARY||address->op!='+'||address->left->kind!=EX_OBJECT||
       !strength_affine(address->right,&index,&delta)||delta||(reg=loop_index(loop,index))<0)return -1;
    s=address->left->symbol;element=value_type(s->type);
    if(far_pointer(element)||element.pointers!=1||width(pointed_type(element))!=1||element.base!=TY_CHAR||(!s->type.array&&!loop_private(s)))return -1;
    if(loop->pointers[reg]&&loop->pointers[reg]!=s)return -1;
    loop->pointers[reg]=s;loop->addresses[reg]=address;return reg;
}
static int loop_instruction(RegisterLoop *loop,int kind,int reg,int op,unsigned value)
{
    LoopInstruction *instruction;
    if(loop->instruction_count==128)return 0;
    instruction=&loop->instructions[loop->instruction_count++];
    instruction->kind=kind;instruction->reg=reg;instruction->op=op;instruction->value=value;
    if(kind==LOOP_STEP)loop->strides[reg]+=op;
    return 1;
}
/* Return a private pointer and its optional prefix/postfix unit update */
static Symbol *loop_address(Expr *e,int *pre,int *post)
{
    *pre=*post=0;
    if(e->kind==EX_PRE||e->kind==EX_POST){
        int delta=e->op==TOK_INC?1:-1;
        if(e->kind==EX_PRE)*pre=delta;else *post=delta;e=e->left;
    }
    return e->kind==EX_OBJECT?e->symbol:NULL;
}
static int loop_byte_expression(RegisterLoop *loop,Expr *e)
{
    int reg,pre,post;
    if(e->kind==EX_CAST&&!e->type.pointers&&reg_width(e->type)==2)
        return loop_byte_expression(loop,e->left);
    if(e->kind==EX_INT&&!e->type.pointers&&e->type.base!=TY_FLOAT)
        return loop_instruction(loop,LOOP_LITERAL,0,0,e->value&255);
    if(e->kind==EX_OBJECT&&e->symbol==loop->temporary&&loop->temporary_live){
        loop->temporary_live=0;return loop_instruction(loop,LOOP_RESTORE,0,0,0);
    }
    if(e->kind==EX_DEREF&&width(e->type)==1){
        reg=loop_cursor(loop,e->left,&pre,&post);if(reg<0)return 0;
        if(pre&&!loop_instruction(loop,LOOP_STEP,reg,pre,0))return 0;
        if(!loop_instruction(loop,LOOP_LOAD,reg,0,0))return 0;
        return !post||loop_instruction(loop,LOOP_STEP,reg,post,0);
    }
    if(e->kind==EX_BINARY&&(e->op=='+'||e->op=='-'||e->op=='&'||e->op=='|'||e->op=='^')&&
       !e->type.pointers&&e->type.base!=TY_FLOAT&&e->right->kind==EX_INT&&
       !e->right->type.pointers&&e->right->type.base!=TY_FLOAT&&loop_byte_expression(loop,e->left))
        return loop_instruction(loop,LOOP_ALU,0,e->op,e->right->value&255);
    return 0;
}
static int loop_counter(RegisterLoop *loop,Symbol *s,int delta)
{
    unsigned i;
    if(s->type.pointers||s->type.base!=TY_INT||!loop_private(s))return 0;
    /* Existing affine cursors must not be left stale by a deferred update */
    for(i=0;i<cg.cursor_count;++i)if(cg.cursors[i].index==s)return 0;
    for(i=0;i<loop->counter_count;++i)if(loop->counters[i]==s)break;
    if(i==loop->counter_count){if(i==8)return 0;loop->counters[loop->counter_count++]=s;}
    loop->deltas[i]+=delta;return 1;
}
static int loop_expression(RegisterLoop *loop,Expr *e)
{
    Symbol *s;int reg,delta,pre,post;
    if((e->kind==EX_PRE||e->kind==EX_POST)&&e->left->kind==EX_OBJECT){
        s=e->left->symbol;delta=e->op==TOK_INC?1:-1;
        reg=loop_index(loop,s);if(reg>=0)return loop_instruction(loop,LOOP_STEP,reg,delta,0);
        if(!s->type.pointers)return loop_counter(loop,s,delta);
        reg=loop_pointer(loop,s);return reg>=0&&loop_instruction(loop,LOOP_STEP,reg,delta,0);
    }
    if(e->kind!=EX_ASSIGN)return 0;
    if(e->left->kind==EX_OBJECT&&e->right->kind==EX_INT&&e->right->type.base!=TY_FLOAT&&
       !e->right->type.pointers&&(e->op=='+'||e->op=='-')&&(e->right->value==1||e->right->value==0xFFFFu)){
        s=e->left->symbol;delta=e->right->value==1?1:-1;if(e->op=='-')delta=-delta;
        reg=loop_index(loop,s);if(reg>=0)return loop_instruction(loop,LOOP_STEP,reg,delta,0);
        if(!s->type.pointers)return loop_counter(loop,s,delta);
        reg=loop_pointer(loop,s);return reg>=0&&loop_instruction(loop,LOOP_STEP,reg,delta,0);
    }
    if(!e->op&&e->left->kind==EX_OBJECT&&width(e->left->type)==1&&loop_private(e->left->symbol)){
        s=e->left->symbol;
        if(loop->temporary_live||(loop->temporary&&loop->temporary!=s)||!loop_byte_expression(loop,e->right))return 0;
        loop->temporary=s;loop->temporary_live=1;return loop_instruction(loop,LOOP_SAVE,0,0,0);
    }
    if(e->op||e->left->kind!=EX_DEREF||width(e->left->type)!=1)return 0;
    if(loop->indexed){
        reg=loop_cursor(loop,e->left->left,&pre,&post);if(reg<0)return 0;
        if(!loop_byte_expression(loop,e->right))return 0;
        return loop_instruction(loop,LOOP_STORE,reg,0,0);
    }
    s=loop_address(e->left->left,&pre,&post);if(!s||pre)return 0;
    /* Delay the destination postfix update until after the store only when
     * the RHS cannot observe it. A plain destination may be read, but its
     * address must not change while evaluating the RHS. */
    if(loop_mentions(e->right,s)){
        if(post)return 0;
        {unsigned before=loop->instruction_count,i;
            if(!loop_byte_expression(loop,e->right))return 0;
            reg=loop_pointer(loop,s);if(reg<0)return 0;
            for(i=before;i<loop->instruction_count;++i)
                if(loop->instructions[i].kind==LOOP_STEP&&loop->instructions[i].reg==reg)return 0;
        }
    }else{if(!loop_byte_expression(loop,e->right))return 0;reg=loop_pointer(loop,s);if(reg<0)return 0;}
    if(!loop_instruction(loop,LOOP_STORE,reg,0,0))return 0;
    return !post||loop_instruction(loop,LOOP_STEP,reg,post,0);
}
static int loop_body(RegisterLoop *loop,Statement *s)
{
    for(;s;s=s->next){
        if(s->kind==ST_BLOCK){if(!loop_body(loop,s->body))return 0;}
        else if(s->kind!=ST_EMPTY&&(s->kind!=ST_EXPR||!loop_expression(loop,s->expression)))return 0;
    }
    return 1;
}
static int loop_accessed_outside(Statement *s,Statement *region,Symbol *symbol,int reads_only)
{
    for(;s;s=s->next){
        if(s==region)continue;
        Expr *e=s->expression;
        if(reads_only&&s->kind==ST_EXPR&&e&&e->kind==EX_ASSIGN&&!e->op&&
           e->left->kind==EX_OBJECT&&e->left->symbol==symbol)e=e->right;
        if(loop_mentions(e,symbol)||loop_mentions(s->step,symbol)||
           loop_accessed_outside(s->initial,region,symbol,reads_only)||
           loop_accessed_outside(s->body,region,symbol,reads_only)||
           loop_accessed_outside(s->alternate,region,symbol,reads_only))return 1;
    }
    return 0;
}
static int loop_observed_outside(Statement *s,Statement *region,Symbol *symbol)
{
    return loop_accessed_outside(s,region,symbol,0);
}
/* A byte's extension matters for equality: signed -1 and unsigned 255 must
 * not compare equal merely because their low bytes match. Word casts keep
 * that representation; an explicit char cast selects a new extension. */
static int loop_read_byte(RegisterLoop *loop,Expr *e,int *extension)
{
    int reg;
    if(e->kind==EX_CAST&&!e->type.pointers&&reg_width(e->type)==2&&
       (e->type.base==TY_INT||e->type.base==TY_CHAR)){
        reg=loop_read_byte(loop,e->left,extension);
        if (e->type.base == TY_CHAR) {
            *extension = !e->type.is_unsigned;
        }
        return reg;
    }
    if(e->kind!=EX_DEREF||width(e->type)!=1||e->left->kind!=EX_OBJECT)return -1;
    *extension=!e->type.is_unsigned;return loop_pointer(loop,e->left->symbol);
}
static int loop_predicate(RegisterLoop *loop,Expr *e,int invert,LoopPredicate *predicate)
{
    int reg,other,extension,other_extension;uint32_t value;
    if(e->kind==EX_UNARY&&e->op=='!')return loop_predicate(loop,e->left,!invert,predicate);
    if(e->kind==EX_BINARY&&(e->op==TOK_EQ||e->op==TOK_NE)){
        Expr *left=e->left,*right=e->right;
        if(integer_constant(left,&value)&&!value){Expr *swap=left;left=right;right=swap;}
        reg=loop_read_byte(loop,left,&extension);if(reg<0)return 0;
        predicate->reg=reg;predicate->op=invert?(e->op==TOK_EQ?TOK_NE:TOK_EQ):e->op;
        if(integer_constant(right,&value)&&!value){predicate->kind=LOOP_TEST;predicate->other=0;return 1;}
        other=loop_read_byte(loop,right,&other_extension);
        if(other<0||extension!=other_extension)return 0;
        predicate->kind=LOOP_COMPARE;predicate->other=other;return 1;
    }
    reg=loop_read_byte(loop,e,&extension);if(reg<0)return 0;
    predicate->kind=LOOP_TEST;predicate->reg=reg;predicate->other=0;predicate->op=invert?TOK_EQ:TOK_NE;return 1;
}
static int loop_predicates(RegisterLoop *loop,Expr *e)
{
    LoopPredicate predicate;
    if(e->kind==EX_BINARY&&e->op==TOK_LAND)
        return loop_predicates(loop,e->left)&&loop_predicates(loop,e->right);
    if(loop->predicate_count==8||!loop_predicate(loop,e,0,&predicate))return 0;
    loop->predicates[loop->predicate_count++]=predicate;return 1;
}
static int loop_plan(RegisterLoop *loop,Statement *s)
{
    Expr *condition=s->expression;Symbol *symbol;unsigned i;int pre,post;
    memset(loop,0,sizeof *loop);loop->sentinel=-1;loop->anchor=-1;
    loop->statement=s;
    if(cg.parser->no_register_loops||(s->kind!=ST_WHILE&&s->kind!=ST_FOR)||!condition)return 0;
    if(condition->kind==EX_BINARY&&condition->op==TOK_NE&&condition->right->kind==EX_INT&&
       !condition->right->value)condition=condition->left;
    if((condition->kind==EX_BINARY&&(condition->op==TOK_LAND||condition->op==TOK_EQ||condition->op==TOK_NE))||
       (condition->kind==EX_UNARY&&condition->op=='!')){
        if(!loop_predicates(loop,condition))return 0;
    }else if(condition->kind==EX_DEREF&&width(condition->type)==1){
        symbol=loop_address(condition->left,&pre,&post);
        if(!symbol||pre||post||(loop->sentinel=loop_pointer(loop,symbol))<0)return 0;
    }else if(condition->kind==EX_BINARY&&condition->op=='<'&&condition->left->kind==EX_OBJECT&&
             condition->right->kind==EX_OBJECT&&condition->left->type.base==TY_INT&&condition->right->type.base==TY_INT&&
             !condition->left->type.pointers&&!condition->right->type.pointers&&
             condition->left->type.is_unsigned==condition->right->type.is_unsigned){
        loop->indexed=1;loop->pointer_count=2;loop->indices[0]=condition->left->symbol;loop->indices[1]=condition->right->symbol;
        if(loop->indices[0]==loop->indices[1]||!loop_private(loop->indices[0])||!loop_private(loop->indices[1]))return 0;
        for(i=0;i<cg.cursor_count;++i)if(cg.cursors[i].index==loop->indices[0]||cg.cursors[i].index==loop->indices[1])return 0;
    }else if(condition->kind==EX_OBJECT&&condition->type.base==TY_INT&&!condition->type.pointers&&
             loop_private(condition->symbol))loop->remaining=condition->symbol;
    else return 0;
    if(!loop_body(loop,s->body)||(s->step&&!loop_expression(loop,s->step))||!loop->pointer_count)return 0;
    if(loop->temporary_live||(loop->temporary&&loop_observed_outside(cg.function->body,s,loop->temporary)))return 0;
    if(loop->indexed&&(!loop->pointers[0]||!loop->pointers[1]||loop->strides[0]!=1||loop->strides[1]!=-1))return 0;
    for(i=0;i<loop->pointer_count;++i)if(loop->strides[i]==1||loop->strides[i]==-1){loop->anchor=(int)i;break;}
    if(loop->counter_count&&loop->anchor<0)return 0;
    for(i=0;i<loop->counter_count;++i)if(loop->deltas[i]<-4||loop->deltas[i]>4)return 0;
    if(loop->remaining){
        for(i=0;i<loop->counter_count;++i)if(loop->counters[i]==loop->remaining)break;
        if(i==loop->counter_count||loop->deltas[i]!=-1)return 0;
    }
    return 1;
}
static int loop_has_far(RegisterLoop *loop)
{
    unsigned i;for(i=0;i<loop->pointer_count;++i)if(far_pointer(loop->pointers[i]->type))return 1;
    return 0;
}
static void loop_emit_predicate(LoopPredicate *predicate,int *cached,int *zero_flags)
{
    if(*cached!=predicate->reg){code("    lda a:$0000,%s\n",predicate->reg?"y":"x");*cached=predicate->reg;*zero_flags=1;}
    if(predicate->kind==LOOP_COMPARE){code("    cmp a:$0000,%s\n",predicate->other?"y":"x");*zero_flags=0;}
    else if(!*zero_flags){code("    cmp #$00\n");*zero_flags=1;}
}
static void loop_predicate_branch(LoopPredicate *predicate,unsigned failure)
{
    code("    %s :+\n",predicate->op==TOK_EQ?"beq":"bne");jump(failure);code(":\n");
}
static void loop_emit_instructions(RegisterLoop *plan,int cached)
{
    RegisterLoop loop=*plan;unsigned i;const char *index;
    for(i=0;i<loop.instruction_count;++i){
        LoopInstruction *instruction=&loop.instructions[i];index=instruction->reg?"y":"x";
        switch(instruction->kind){
        case LOOP_LOAD:
            if(cached!=instruction->reg)code("    lda a:$0000,%s\n",index);
            cached=instruction->reg;break;
        case LOOP_LITERAL:code("    lda #$%02X\n",instruction->value);cached=-1;break;
        case LOOP_ALU:
            if(instruction->op=='+'||instruction->op=='-')code("    %s\n",instruction->op=='+'?"clc":"sec");
            code("    %s #$%02X\n",instruction->op=='+'?"adc":instruction->op=='-'?"sbc":
                instruction->op=='&'?"and":instruction->op=='|'?"ora":"eor",instruction->value);cached=-1;break;
        case LOOP_STORE:code("    sta a:$0000,%s\n",index);cached=-1;break;
        case LOOP_STEP:
            code("    %s%s\n",instruction->op>0?"in":"de",index);
            if (cached == instruction->reg) {
                cached = -1;
            }
            break;
        case LOOP_SAVE:case LOOP_RESTORE:code("    xba\n");cached=-1;break;
        }
    }
}
static void loop_emit_region(RegisterLoop *plan)
{
    RegisterLoop loop=*plan;unsigned i,start=++cg.label,end=++cg.label;int cached=-1,zero_flags=0;
    code("    sep #$20\n.a8\n");label(start);
    if(loop.predicate_count){
        for(i=0;i<loop.predicate_count;++i){loop_emit_predicate(&loop.predicates[i],&cached,&zero_flags);loop_predicate_branch(&loop.predicates[i],end);}
    }else{
        if(loop.remaining||loop.indexed)code("    cp%s z:__arith_lhs+2\n",loop.anchor?"y":"x");
        else{code("    lda a:$0000,%s\n",loop.sentinel?"y":"x");cached=loop.sentinel;}
        code("    bne :+\n");jump(end);code(":\n");
    }
    loop_emit_instructions(&loop,cached);
    jump(start);label(end);
}
static int register_loop(Statement *s)
{
    RegisterLoop loop;unsigned i,j,enter=0,done=0;
    if(!loop_plan(&loop,s)||loop_has_far(&loop))return 0;
    cg.arithmetic=1;divmod_state.available=0;
    code("; register loop: X=%s",loop.pointers[0]->name);
    if(loop.pointer_count==2)code(", Y=%s",loop.pointers[1]->name);
    code("; A8, indices16\n");
    if(loop.indexed){
        enter=++cg.label;done=++cg.label;branch(s->expression,enter,done,enter);label(enter);
        load_symbol(loop.indices[1]);code("    sec\n    sbc %s\n    lsr a\n    adc #0\n    sta z:__arith_lhs\n",frame_operand(loop.indices[0]->offset));
        code("    pha\n    phy\n");emit_value(loop.addresses[1]);code("    pha\n");emit_value(loop.addresses[0]);code("    tax\n    pla\n    tay\n    lda 3,s\n    sta z:__arith_lhs\n");
        code("    txa\n    clc\n    adc z:__arith_lhs\n    sta z:__arith_lhs+2\n");
        loop_emit_region(&loop);code("    rep #$20\n.a16\n    ply\n    pla\n");
        for(i=0;i<2;++i){load_symbol(loop.indices[i]);code("    %s\n    %s z:__arith_lhs\n",i?"sec":"clc",i?"sbc":"adc");store_symbol(loop.indices[i]);}
        for(i=0;i<loop.counter_count;++i){
            int delta=loop.deltas[i];if(!delta)continue;load_symbol(loop.counters[i]);
            for(j=0;j<(unsigned)(delta>0?delta:-delta);++j)code("    %s\n    %s z:__arith_lhs\n",delta>0?"clc":"sec",delta>0?"adc":"sbc");
            store_symbol(loop.counters[i]);
        }
        label(done);return 1;
    }
    code("    phy\n");
    if(loop.remaining){load_symbol(loop.remaining);code("    sta z:__arith_lhs+2\n");}
    loop.pointers[0]->used=1;code("    ldx %s\n",frame_operand(loop.pointers[0]->offset));
    if(loop.pointer_count==2){load_symbol(loop.pointers[1]);code("    tay\n");}
    if(loop.counter_count)code("    %s\n    pha\n",loop.anchor?"tya":"txa");
    if(loop.remaining){
        code("    %s\n    %s\n    %s z:__arith_lhs+2\n    sta z:__arith_lhs+2\n",
            loop.anchor?"tya":"txa",loop.strides[loop.anchor]>0?"clc":"sec",loop.strides[loop.anchor]>0?"adc":"sbc");
    }
    loop_emit_region(&loop);code("    rep #$20\n.a16\n");
    code("    stx z:__arith_rhs\n");if(loop.pointer_count==2)code("    sty z:__arith_rhs+2\n");
    if(loop.counter_count){
        if(loop.strides[loop.anchor]>0)code("    %s\n    sec\n    sbc 1,s\n",loop.anchor?"tya":"txa");
        else code("    lda 1,s\n    sec\n    sbc z:__arith_rhs+%u\n",loop.anchor*2);
        code("    sta z:__arith_lhs\n    pla\n");
    }
    code("    ply\n");
    for(i=0;i<loop.pointer_count;++i){code("    lda z:__arith_rhs+%u\n",i*2);store_symbol(loop.pointers[i]);}
    for(i=0;i<loop.counter_count;++i){
        int delta=loop.deltas[i];if(!delta)continue;
        load_symbol(loop.counters[i]);
        for(j=0;j<(unsigned)(delta>0?delta:-delta);++j)
            code("    %s\n    %s z:__arith_lhs\n",delta>0?"clc":"sec",delta>0?"adc":"sbc");
        store_symbol(loop.counters[i]);
    }
    divmod_state.available=0;return 1;
}
/* Lifetime boundary analysis for leaf functions containing one planned loop.
 * If only a scalar result and final byte stores survive, frame homes and
 * deferred counters need not be materialized at all. Parameter snapshots
 * also provide the initial cursor used to recover an induction result. */
static int loop_flatten(Statement *s,Statement **statements,unsigned *count)
{
    for(;s;s=s->next){
        if(s->kind==ST_BLOCK){if(!loop_flatten(s->body,statements,count))return 0;}
        else if(s->kind!=ST_EMPTY){if(*count==128)return 0;statements[(*count)++]=s;}
    }
    return 1;
}
static int loop_parameter(Function *f,Symbol *s)
{
    unsigned i;for(i=0;i<(unsigned)f->symbol->param_count;++i)if(leaf_parameter(f,i)==s)return (int)i;
    return -1;
}
static unsigned loop_argument_offset(unsigned parameter,unsigned saved)
{
    return parameter==0?saved-1:parameter==1?1:saved+5+cg.parser->long_return+(parameter-2)*2;
}
typedef struct { int parameter;unsigned constant; } LoopBound;
static int loop_bound(Function *f,Expr *e,Symbol **symbols,LoopBound *bounds,unsigned count,LoopBound *bound)
{
    unsigned i;uint32_t value;LoopBound left,right;int parameter;
    if(integer_constant(e,&value)){bound->parameter=-1;bound->constant=value&65535;return 1;}
    if(e->type.pointers||e->type.base!=TY_INT)return 0;
    if(e->kind==EX_CAST&&reg_width(e->type)==2&&e->left->type.base==TY_INT&&reg_width(e->left->type)==2)
        return loop_bound(f,e->left,symbols,bounds,count,bound);
    if(e->kind==EX_OBJECT){
        for(i=0;i<count;++i)if(symbols[i]==e->symbol){*bound=bounds[i];return 1;}
        parameter=loop_parameter(f,e->symbol);if(parameter<0)return 0;
        bound->parameter=parameter;bound->constant=0;return 1;
    }
    if(e->kind!=EX_BINARY||(e->op!='+'&&e->op!='-')||
       !loop_bound(f,e->left,symbols,bounds,count,&left)||!loop_bound(f,e->right,symbols,bounds,count,&right)||
       (left.parameter>=0&&right.parameter>=0)||(e->op=='-'&&right.parameter>=0))return 0;
    bound->parameter=left.parameter>=0?left.parameter:right.parameter;
    bound->constant=(left.constant+(e->op=='+'?right.constant:0u-right.constant))&65535;return 1;
}
static int loop_bound_initializers(Function *f,Statement **statements,unsigned count,Symbol **symbols,LoopBound *bounds,unsigned *n)
{
    unsigned i,j;Expr *e;LoopBound bound;
    for(i=0;i<count;++i){
        if (statements[i]->kind != ST_EXPR) {
            return 0;
        }
        e = statements[i]->expression;
        if(e->kind!=EX_ASSIGN||e->op||e->left->kind!=EX_OBJECT||!e->left->symbol->scope||
           e->left->symbol->owner!=f->id||!loop_bound(f,e->right,symbols,bounds,*n,&bound))return 0;
        for(j=0;j<*n;++j)if(symbols[j]==e->left->symbol)break;
        if(j==*n){if(j==128)return 0;symbols[(*n)++]=e->left->symbol;}
        bounds[j]=bound;
    }
    return 1;
}
static void loop_emit_bound(LoopBound bound,unsigned saved,unsigned pushed)
{
    if(bound.parameter<0)code("    lda #$%04X\n",bound.constant);
    else{
        code("    lda %u,s\n",loop_argument_offset((unsigned)bound.parameter,saved)+pushed);
        if(bound.constant)code("    clc\n    adc #$%04X\n",bound.constant);
    }
}
/* The same indexed loop IR can omit all frame homes when its only live
 * outputs are memory writes and a constant/void return. Bound initializers
 * are pure affine parameter expressions, evaluated before entering A8. */
static int indexed_loop_leaf(Function *f)
{
    Statement *statements[128],*initial[128],*region;Symbol *symbols[128];LoopBound bounds[128],ends[2];
    RegisterLoop loop;unsigned count=0,n=0,initial_count=0,position=128,i,j,saved,done;
    uint32_t result=0;
    if(cg.parser->no_register_loops||!strcmp(f->symbol->name,"main")||f->symbol->param_count<0||
       reg_width(f->symbol->type)!=2||f->symbol->type.base==TY_FLOAT||cg.cursor_count||divmod_state.count)return 0;
    for(i=0;i<(unsigned)f->symbol->param_count;++i)if(width(f->symbol->params[i])!=2)return 0;
    if(!loop_flatten(f->body,statements,&count))return 0;
    for(i=0;i<count;++i)if(statements[i]->kind==ST_WHILE||statements[i]->kind==ST_FOR){position=i;break;}
    if(position==128||!loop_bound_initializers(f,statements,position,symbols,bounds,&n))return 0;
    region=statements[position];
    if(!loop_flatten(region->initial,initial,&initial_count)||
       !loop_bound_initializers(f,initial,initial_count,symbols,bounds,&n)||!loop_plan(&loop,region)||loop_has_far(&loop)||!loop.indexed)return 0;
    for(i=0;i<2;++i){
        if(loop_parameter(f,loop.pointers[i])<0)return 0;
        for(j=0;j<n;++j)if(symbols[j]==loop.indices[i])break;
        if (j == n) {
            return 0;
        }
        ends[i] = bounds[j];
    }
    if(position+1<count){
        Statement *tail=statements[position+1];
        if(position+2!=count||tail->kind!=ST_RETURN||(tail->expression&&!integer_constant(tail->expression,&result)))return 0;
    }else if(f->symbol->type.base!=TY_VOID)return 0;
    /* Fold a zero-origin cursor and consume the live ABI inputs directly.
     * No parameter/index homes are needed when their final values are dead. */
    if(ends[0].parameter<0&&!ends[0].constant&&ends[1].parameter==1&&
       loop_parameter(f,loop.pointers[0])==0&&loop_parameter(f,loop.pointers[1])==0){
        done=++cg.label;cg.arithmetic=1;
        code(".segment \"CODE\"\n.export _%s\n_%s:\n; native indexed loop leaf\n; register loop: indexed X/Y, A8, indices16\n    phy\n    phx\n",
            f->symbol->asm_name,f->symbol->asm_name);
        strength_adjust(ends[1].constant);
        if(!ends[1].constant)code("    cmp #0\n");
        code("    bne :+\n");jump(done);code(":\n");
        if(!loop.indices[0]->type.is_unsigned){code("    bpl :+\n");jump(done);code(":\n");}
        /* LSR's carry rounds the half-distance up while adding the base.
         * Y can hold the right index until it becomes the right cursor. */
        code("    tay\n    lsr a\n    adc 1,s\n    sta z:__arith_lhs+2\n    tya\n    clc\n    adc 1,s\n    tay\n");
        loop_emit_region(&loop);code("    rep #$20\n.a16\n");label(done);
        if(f->symbol->type.base!=TY_VOID)code("    lda #$%04X\n",result&65535);
        narrow_char(f->symbol->type);
        code("    plx\n    ply\n    rts\n__size_%s = * - _%s\n",f->symbol->asm_name,f->symbol->asm_name);return 1;
    }
    saved=(unsigned)(f->symbol->param_count>2?2:f->symbol->param_count)*2;done=++cg.label;cg.arithmetic=1;
    code(".segment \"CODE\"\n.export _%s\n_%s:\n; native indexed loop leaf\n; register loop: indexed X/Y, A8, indices16\n    phy\n",
        f->symbol->asm_name,f->symbol->asm_name);
    if (saved) {
        code("    phx\n");
    }
    if (saved == 4) {
        code("    pha\n");
    }
    loop_emit_bound(ends[0],saved,0);code("    pha\n");loop_emit_bound(ends[1],saved,2);code("    pha\n");
    code("    lda 3,s\n");
    if(loop.indices[0]->type.is_unsigned){code("    cmp 1,s\n    bcc :+\n");jump(done);code(":\n");}
    else{code("    sec\n    sbc 1,s\n    bvc :+\n    eor #$8000\n:\n    bmi :+\n");jump(done);code(":\n");}
    code("    lda 1,s\n    sec\n    sbc 3,s\n    lsr a\n    adc #0\n    sta z:__arith_lhs\n");
    for(i=0;i<2;++i){
        unsigned parameter=(unsigned)loop_parameter(f,loop.pointers[i]);
        code("    lda %u,s\n    clc\n    adc %u,s\n    %s\n",loop_argument_offset(parameter,saved)+4,i?1:3,i?"tay":"tax");
    }
    code("    txa\n    clc\n    adc z:__arith_lhs\n    sta z:__arith_lhs+2\n");
    loop_emit_region(&loop);code("    rep #$20\n.a16\n");label(done);
    code("    lda #$%04X\n",result&65535);narrow_char(f->symbol->type);
    for(i=0;i<saved+4;i+=2)code("    plx\n");
    code("    ply\n    rts\n__size_%s = * - _%s\n",f->symbol->asm_name,f->symbol->asm_name);return 1;
}
/* Parallel input moves: consume X/A before loading stack parameters into A.
 * Y is already saved and is free for the second allocated pointer. */
static void loop_input_moves(Function *f,RegisterLoop *loop,unsigned pushed)
{
    int x=loop_parameter(f,loop->pointers[0]);
    int y=loop->pointer_count==2?loop_parameter(f,loop->pointers[1]):-1;
    if(y==0)code("    txy\n");
    if(y==1)code("    tay\n");
    if(x==1)code("    tax\n");
    if(x>=2)code("    lda %u,s\n    tax\n",5+pushed+((unsigned)x-2)*2);
    if(y>=2)code("    lda %u,s\n    tay\n",5+pushed+((unsigned)y-2)*2);
}
static int loop_initializers(Statement **statements,unsigned count,Symbol **symbols,unsigned *values,unsigned *n)
{
    unsigned i,j;Expr *e;uint32_t value;
    for(i=0;i<count;++i){
        if (statements[i]->kind != ST_EXPR) {
            return 0;
        }
        e = statements[i]->expression;
        if(e->kind!=EX_ASSIGN||e->op||e->left->kind!=EX_OBJECT||!integer_constant(e->right,&value)||
           e->left->symbol->owner!=cg.function->id||!e->left->symbol->scope||
           e->left->type.pointers||e->left->type.base!=TY_INT||e->right->type.base==TY_FLOAT)return 0;
        for(j=0;j<*n;++j)if(symbols[j]==e->left->symbol)break;
        if(j==*n){if(j==128)return 0;symbols[(*n)++]=e->left->symbol;}
        values[j]=value&65535;
    }
    return 1;
}
static int loop_same_test(LoopPredicate *a,LoopPredicate *b)
{
    if(a->kind!=b->kind)return 0;
    if(a->kind==LOOP_TEST)return a->reg==b->reg;
    return (a->reg==b->reg&&a->other==b->other)||(a->reg==b->other&&a->other==b->reg);
}
/* Carry the loop's failure edge, available byte and comparison flags into a
 * Boolean return. Earlier short-circuit exits evaluate any missing final
 * comparison; matching comparison exits reuse Z without reloading memory. */
static int predicate_loop_leaf(Function *f)
{
    Statement *statements[128],*initial[128],*region,*tail;Symbol *symbols[128];unsigned values[128];
    RegisterLoop loop;LoopPredicate result;Expr *expression;
    unsigned count=0,n=0,initial_count=0,position=128,i,start,evaluate,flags,done;
    int evaluation=0,reload=0,cached=-1,zero_flags=0;
    if(cg.parser->no_register_loops||!strcmp(f->symbol->name,"main")||f->symbol->param_count<0||
       f->symbol->type.pointers||(f->symbol->type.base!=TY_INT&&f->symbol->type.base!=TY_CHAR)||
       cg.cursor_count||divmod_state.count)return 0;
    for(i=0;i<(unsigned)f->symbol->param_count;++i)if(width(f->symbol->params[i])!=2)return 0;
    if(!loop_flatten(f->body,statements,&count))return 0;
    for(i=0;i<count;++i)if(statements[i]->kind==ST_WHILE||statements[i]->kind==ST_FOR){position=i;break;}
    if(position==128||position+2!=count||!loop_initializers(statements,position,symbols,values,&n))return 0;
    region=statements[position];tail=statements[position+1];
    if(tail->kind!=ST_RETURN||!tail->expression||!loop_flatten(region->initial,initial,&initial_count)||
       !loop_initializers(initial,initial_count,symbols,values,&n)||!loop_plan(&loop,region)||loop_has_far(&loop)||loop.indexed||loop.remaining)return 0;
    expression=tail->expression;
    while(expression->kind==EX_CAST&&!expression->type.pointers&&expression->type.base!=TY_FLOAT)expression=expression->left;
    if(!((expression->kind==EX_BINARY&&(expression->op==TOK_EQ||expression->op==TOK_NE))||
         (expression->kind==EX_UNARY&&expression->op=='!'))||!loop_predicate(&loop,expression,0,&result))return 0;
    for(i=0;i<loop.pointer_count;++i)if(loop_parameter(f,loop.pointers[i])<0)return 0;
    if(!loop.predicate_count){
        LoopPredicate *p=&loop.predicates[loop.predicate_count++];
        p->kind=LOOP_TEST;p->reg=loop.sentinel;p->other=0;p->op=TOK_NE;
    }
    for(i=0;i<loop.predicate_count;++i)if(!loop_same_test(&loop.predicates[i],&result)){
        evaluation=1;if(loop.predicates[i].reg!=result.reg)reload=1;
    }
    start=++cg.label;evaluate=++cg.label;flags=++cg.label;done=++cg.label;
    code(".segment \"CODE\"\n.export _%s\n_%s:\n; native predicate loop leaf\n; register loop: byte predicates, X/Y, A8\n    phy\n",
        f->symbol->asm_name,f->symbol->asm_name);
    loop_input_moves(f,&loop,0);code("    sep #$20\n.a8\n");label(start);
    for(i=0;i<loop.predicate_count;++i){
        LoopPredicate *p=&loop.predicates[i];loop_emit_predicate(p,&cached,&zero_flags);
        loop_predicate_branch(p,loop_same_test(p,&result)?flags:evaluate);
    }
    loop_emit_instructions(&loop,cached);jump(start);
    if(evaluation){label(evaluate);cached=reload?-1:result.reg;zero_flags=0;loop_emit_predicate(&result,&cached,&zero_flags);}
    label(flags);code("    rep #$20\n.a16\n    %s :+\n    lda #1\n",result.op==TOK_EQ?"bne":"beq");
    jump(done);code(":\n    lda #0\n");label(done);
    code("    ply\n    rts\n__size_%s = * - _%s\n",f->symbol->asm_name,f->symbol->asm_name);return 1;
}
/* Reduce pure scalar results to coefficient * iterations + constant, modulo
 * the target word width. Narrowing casts are boundaries, not affine maps. */
static int loop_affine_result(RegisterLoop *loop,Expr *e,Symbol **symbols,unsigned *values,unsigned n,
                              unsigned *coefficient,unsigned *constant)
{
    unsigned i,j,a,b,c,d;uint32_t value;
    if(integer_constant(e,&value)){*coefficient=0;*constant=value&65535;return 1;}
    if(e->type.pointers||e->type.base==TY_FLOAT)return 0;
    if(e->kind==EX_CAST&&e->type.base!=TY_CHAR)
        return loop_affine_result(loop,e->left,symbols,values,n,coefficient,constant);
    if(e->kind==EX_OBJECT&&e->type.base==TY_INT){
        if(e->symbol==loop->remaining){*coefficient=*constant=0;return 1;}
        for(i=0;i<n;++i)if(symbols[i]==e->symbol)break;
        if(i==n)return 0;
        for(j=0;j<loop->counter_count;++j)if(loop->counters[j]==e->symbol)break;
        *coefficient=j==loop->counter_count?0:(unsigned)loop->deltas[j]&65535;
        *constant=values[i];return 1;
    }
    if(e->kind!=EX_BINARY||(e->op!='+'&&e->op!='-'&&e->op!='*')||
       !loop_affine_result(loop,e->left,symbols,values,n,&a,&b)||
       !loop_affine_result(loop,e->right,symbols,values,n,&c,&d))return 0;
    if(e->op=='+'){*coefficient=(a+c)&65535;*constant=(b+d)&65535;}
    else if(e->op=='-'){*coefficient=(a-c)&65535;*constant=(b-d)&65535;}
    else{if(a&&c)return 0;*coefficient=(a*d+b*c)&65535;*constant=(b*d)&65535;}
    return 1;
}
static int register_loop_leaf(Function *f)
{
    Statement *statements[128],*initial[128],*stores[128],*loop_statement;RegisterLoop loop;
    Symbol *symbols[128];Expr *result=NULL;unsigned values[128];
    unsigned count=0,n=0,initial_count=0,i,j,k,position=128,store_count=0,saved,coefficient=0,constant=0;
    int return_pointer=-1,remaining_parameter=-1;unsigned remaining_value=0;int parameter;
    uint32_t value=0;int fast_inputs,snapshot,anchor_parameter=-1;unsigned initial_offset=0;
    if(cg.parser->no_register_loops||!strcmp(f->symbol->name,"main")||f->symbol->param_count<0||
       reg_width(f->symbol->type)!=2||f->symbol->type.base==TY_FLOAT||cg.cursor_count||divmod_state.count)return 0;
    for(i=0;i<(unsigned)f->symbol->param_count;++i)if(width(f->symbol->params[i])!=2)return 0;
    if(!loop_flatten(f->body,statements,&count))return 0;
    for(i=0;i<count;++i)if(statements[i]->kind==ST_WHILE||statements[i]->kind==ST_FOR){position=i;break;}
    if(position==128||!loop_initializers(statements,position,symbols,values,&n))return 0;
    loop_statement=statements[position];
    if(!loop_flatten(loop_statement->initial,initial,&initial_count)||
       !loop_initializers(initial,initial_count,symbols,values,&n)||!loop_plan(&loop,loop_statement)||loop_has_far(&loop)||loop.indexed)return 0;
    for(i=0;i<loop.pointer_count;++i)if(loop_parameter(f,loop.pointers[i])<0)return 0;
    if(loop.remaining){
        remaining_parameter=loop_parameter(f,loop.remaining);
        if(remaining_parameter<0){
            for(i=0;i<n;++i)if(symbols[i]==loop.remaining)break;
            if (i == n) {
                return 0;
            }
            remaining_value = values[i];
        }
    }
    for(i=position+1;i<count;++i){
        Statement *s=statements[i];Expr *e=s->expression;
        if(s->kind==ST_RETURN){if(i+1!=count)return 0;result=e;break;}
        if(s->kind!=ST_EXPR||e->kind!=EX_ASSIGN||e->op||e->left->kind!=EX_DEREF||
           width(e->left->type)!=1||e->left->left->kind!=EX_OBJECT||!integer_constant(e->right,&value))return 0;
        for(j=0;j<loop.pointer_count;++j)if(loop.pointers[j]==e->left->left->symbol)break;
        if (j == loop.pointer_count) {
            return 0;
        }
        stores[store_count++] = s;
    }
    if(!result&&f->symbol->type.base!=TY_VOID)return 0;
    while(result&&result->kind==EX_CAST&&reg_width(result->type)==2&&
          ((result->type.base==TY_INT&&!result->type.pointers&&result->left->type.base==TY_INT&&!result->left->type.pointers)||
           (result->type.pointers&&result->left->type.pointers)))result=result->left;
    if(result&&result->kind==EX_OBJECT)
        for(i=0;i<loop.pointer_count;++i)if(loop.pointers[i]==result->symbol)return_pointer=(int)i;
    if(result&&return_pointer<0&&!loop_affine_result(&loop,result,symbols,values,n,&coefficient,&constant))return 0;
    fast_inputs=!loop.remaining||remaining_parameter<0||remaining_parameter>=2;
    snapshot=coefficient!=0;
    if(snapshot)anchor_parameter=loop_parameter(f,loop.pointers[loop.anchor]);
    saved=fast_inputs?(snapshot?2u:0u):(unsigned)(f->symbol->param_count>2?2:f->symbol->param_count)*2;
    code(".segment \"CODE\"\n.export _%s\n_%s:\n; native loop leaf\n; register loop: X=%s",
        f->symbol->asm_name,f->symbol->asm_name,loop.pointers[0]->name);
    if(loop.pointer_count==2)code(", Y=%s",loop.pointers[1]->name);
    code("; A8, indices16\n    phy\n");
    if(fast_inputs){
        if(snapshot&&anchor_parameter<2)code("    %s\n",anchor_parameter?"pha":"phx");
        loop_input_moves(f,&loop,snapshot&&anchor_parameter<2?2:0);
        if(snapshot&&anchor_parameter>=2)code("    %s\n    pha\n",loop.anchor?"tya":"txa");
        initial_offset=1;
        if(loop.remaining){
            cg.arithmetic=1;
            if(remaining_parameter<0)code("    lda #$%04X\n",remaining_value);
            else code("    lda %u,s\n",5+saved+((unsigned)remaining_parameter-2)*2);
            code("    sta z:__arith_lhs+2\n");
        }
    }else{
        if (saved) {
            code("    phx\n");
        }
        if (saved == 4) {
            code("    pha\n");
        }
        cg.arithmetic=1;code("    lda %u,s\n    sta z:__arith_lhs+2\n",loop_argument_offset((unsigned)remaining_parameter,saved));
        for(i=0;i<loop.pointer_count;++i){
            parameter=loop_parameter(f,loop.pointers[i]);
            code("    lda %u,s\n    %s\n",loop_argument_offset((unsigned)parameter,saved),i?"tay":"tax");
        }
        if(snapshot)initial_offset=loop_argument_offset((unsigned)anchor_parameter,saved);
    }
    if(loop.remaining)code("    %s\n    %s\n    %s z:__arith_lhs+2\n    sta z:__arith_lhs+2\n",
        loop.anchor?"tya":"txa",loop.strides[loop.anchor]>0?"clc":"sec",loop.strides[loop.anchor]>0?"adc":"sbc");
    loop_emit_region(&loop);
    for(i=0;i<store_count;++i){
        Expr *e=stores[i]->expression;integer_constant(e->right,&value);value&=255;
        for(j=0;j<loop.pointer_count;++j)if(loop.pointers[j]==e->left->left->symbol)break;
        if(i||loop.remaining||loop.predicate_count||value)code("    lda #$%02X\n",value);
        code("    sta a:$0000,%s\n",j?"y":"x");
    }
    code("    rep #$20\n.a16\n");
    if(return_pointer>=0)code("    %s\n",return_pointer?"tya":"txa");
    else if(coefficient){
        int delta=(int16_t)coefficient;unsigned magnitude=(unsigned)(delta>0?delta:-delta);
        if(loop.strides[loop.anchor]>0)code("    %s\n    sec\n    sbc %u,s\n",loop.anchor?"tya":"txa",initial_offset);
        else{cg.arithmetic=1;code("    st%s z:__arith_lhs\n    lda %u,s\n    sec\n    sbc z:__arith_lhs\n",loop.anchor?"y":"x",initial_offset);}
        if(magnitude>1){
            for(k=1;k<=magnitude/2;k*=2){}
            if(magnitude&(magnitude-1)){cg.arithmetic=1;code("    sta z:__arith_lhs\n");}
            for(k/=2;k;k/=2){code("    asl a\n");if(magnitude&k)code("    clc\n    adc z:__arith_lhs\n");}
        }
        if(delta<0)code("    eor #$FFFF\n    inc a\n");
        if(constant)code("    clc\n    adc #$%04X\n",constant);
    }else code("    lda #$%04X\n",constant);
    narrow_char(f->symbol->type);
    for(i=0;i<saved;i+=2)code("    plx\n");
    code("    ply\n    rts\n__size_%s = * - _%s\n",f->symbol->asm_name,f->symbol->asm_name);
    return 1;
}
