/* Region direct-page homes (Phase A v2). A function that keeps its Y frame
 * because it makes unresolved calls may still move hot frame words into free
 * 32-byte words for the duration of one outermost loop whose body makes no
 * unresolved call (helpers and summarized same-unit callees are allowed).
 * Each promoted word is copied in before the loop and written back at the
 * loop's end label, which every exit through the loop reaches; a return
 * leaves the frame dead.
 *
 * A trial emission measures each frame word's use inside the loop and the
 * workspace words, helpers and callees the loop needs. Words used at least
 * twice per iteration of the outermost loop are mapped to the remaining
 * workspace words; the loop is emitted again and kept only if it re-validates
 * (no address of a frame object, no other use of a mapped word). */
static int dp_scan_range(size_t start,size_t stop,unsigned *taken);
static void dp_resolve(size_t start);
static void region_home_liveness(Function *f,Statement *s,unsigned offset,int *in,int *out);
/* The region is the text between region_enter and region_exit of
 * region_loop: mapping (or, in the measuring trial, counting) is active only
 * there, after the copies in and before the copies out. */
static Statement *region_loop;
static Statement *region_initializers;
static unsigned region_words[16],region_slots[16],region_count;
static int region_in[16],region_out[16];
static size_t region_begin,region_end;static int region_entered;
static void region_copy(int in)
{
    unsigned i;
    for(i=0;i<region_count;++i){
        if(!(in?region_in[i]:region_out[i]))continue;
        if(in)code("    lda %s\n    sta z:__dp_home_%02u\n",frame_operand(region_slots[i]*2+1),region_words[i]);
        else code("    lda z:__dp_home_%02u\n    sta %s\n",region_words[i],frame_operand(region_slots[i]*2+1));
    }
}
static void region_enter(Statement *s)
{
    if(s!=region_loop)return;
    region_entered=1;region_begin=cg.length;
    if(region_count){
        code("; region direct-page homes: %u frame words\n",region_count);region_copy(1);
        cg.dp_homes=1;cg.dp_frameless=0;cg.dp_failed=0;
        if(region_initializers){
            Statement *previous=loop_previous,*current=loop_current;
            code("; initialize promoted loop homes directly\n");
            emit_statements(region_initializers);
            loop_previous=previous;loop_current=current;
        }
    }else cg.dp_trial=1;
}
static void region_exit(Statement *s)
{
    if(s!=region_loop)return;
    if(region_count){cg.dp_homes=0;region_copy(0);}else cg.dp_trial=0;
    region_end=cg.length;
}
/* An int expression as base+k: a constant (base NULL) or object +/- constant */
static int region_offset(Expr *e,Symbol **base,int *k)
{
    int c;
    while(e&&e->kind==EX_CAST&&value_width(e->type)==2&&value_width(e->left->type)==2)e=e->left;
    if(!e)return 0;
    if(lftr_constant(e,k)){*base=NULL;return 1;}
    if(e->kind==EX_OBJECT&&!e->type.pointers&&value_width(e->type)==2){*base=e->symbol;*k=0;return 1;}
    if(e->kind==EX_BINARY&&(e->op=='+'||e->op=='-')&&!e->type.pointers&&e->left->kind==EX_OBJECT&&
       lftr_constant(e->right,&c)&&region_offset(e->left,base,k)){*k=e->op=='+'?c:-c;return 1;}
    return 0;
}
/* Iterations per entry of a loop testing v < bound or v <= bound when v's
 * entry value (a for initializer, or an assignment just before the loop) and
 * the bound differ by a constant; otherwise the 8 that frame_operand's
 * per-level weight already assumes. */
static unsigned region_trips(Statement *s)
{
    Expr *c=s->expression;Statement *init;Symbol *v,*from_base=NULL,*to_base;int from=0,to,found=0;
    if(s->kind==ST_DO||!c||c->kind!=EX_BINARY||(c->op!='<'&&c->op!=TOK_LE)||c->left->kind!=EX_OBJECT||
       !region_offset(c->right,&to_base,&to))return 8;
    if(c->left->type.is_unsigned||c->right->type.is_unsigned)return 8; /* bounds are read as signed words */
    v=c->left->symbol;
    for(init=s->kind==ST_FOR?s->initial:NULL;init;init=init->next)
        if(init->kind==ST_EXPR&&init->expression&&init->expression->kind==EX_ASSIGN&&!init->expression->op&&
           lftr_object(init->expression->left,v)&&region_offset(init->expression->right,&from_base,&from))found=1;
    if(!found&&!(s->kind==ST_FOR&&s->initial)){
        Statement *before=loop_current&&loop_current->next==s?loop_current:loop_previous&&loop_previous->next==s?loop_previous:NULL;
        Expr *e=before&&before->kind==ST_EXPR?before->expression:NULL;
        if(e&&e->kind==EX_ASSIGN&&!e->op&&lftr_object(e->left,v)&&region_offset(e->right,&from_base,&from))found=1;
    }
    if(!found||from_base!=to_base||from_base==v)return 8;
    if(c->op==TOK_LE)++to;
    return to>from?(unsigned)(to-from):0;
}
static int bound_loop_statement(Statement *s);

/* Fuse the sentinel read with a bounded byte-to-word store. The three
 * private cursors have no observable homes inside this call-free region. */
static int far_sentinel_word_loop(Statement *s)
{
    Expr *guard=s->expression,*test,*store,*load,*decrement;
    Statement *body,*tail;
    Symbol *src,*dest,*count;
    uint32_t bits;
    unsigned start,advanced,done;
    int pre,post;

    if(s->kind!=ST_WHILE||cg.parser->no_register_loops||cg.parser->no_strength_reduction||
       cg.stack_leaf||cg.scalar_leaf||cg.scalar_first||cg.leaf_count||
       cg.retained_index||cg.scan_cursor||cg.bound||cg.bound_pending||cg.dead_index_count||
       cg.omitted_parameter_count||!cg.function||cg.function->symbol->interrupt||
       !guard||guard->kind!=EX_BINARY||guard->op!=TOK_LAND||volatile_expression(guard))return 0;
    if(guard->left->kind!=EX_OBJECT)return 0;
    count=guard->left->symbol;test=guard->right;
    if(count->type.base!=TY_INT||count->type.pointers||width(count->type)!=2||
       !count->type.is_unsigned||test->kind!=EX_DEREF||width(test->type)!=1||
       test->left->kind!=EX_OBJECT)return 0;
    src=test->left->symbol;
    body=s->body;
    if(body&&body->kind==ST_BLOCK&&!body->inline_callee)body=body->body;
    tail=body?body->next:NULL;
    if(!tail||tail->next||body->kind!=ST_EXPR||tail->kind!=ST_EXPR||volatile_statements(body))return 0;
    store=body->expression;decrement=tail->expression;
    if(store->kind!=EX_ASSIGN||store->op||store->left->kind!=EX_DEREF||
       store->left->type.base!=TY_INT||store->left->type.pointers||width(store->left->type)!=2||
       store->left->type.is_bool)return 0;
    dest=loop_address(store->left->left,&pre,&post);
    if(!dest||pre||post!=1||far_pointer(dest->type)||width(dest->type)!=2||
       !far_pointer(src->type)||src->type.pointers!=1||src->type.base!=TY_CHAR||
       !loop_private(src)||!loop_private(dest)||!loop_private(count))return 0;
    if((decrement->kind!=EX_PRE&&decrement->kind!=EX_POST)||decrement->op!=TOK_DEC||
       decrement->left->kind!=EX_OBJECT||decrement->left->symbol!=count)return 0;
    load=store->right;
    bits=0;
    for(;;){
        if(load->kind==EX_CAST&&load->type.base==TY_INT&&!load->type.pointers&&
           !load->type.is_bool){
            load=load->left;
        }else if(load->kind==EX_BINARY&&load->op=='|'){
            uint32_t part;
            if(integer_constant(load->right,&part))load=load->left;
            else if(integer_constant(load->left,&part))load=load->right;
            else return 0;
            if(part>0xffff||(part&0xff))return 0;
            bits|=part;
        }else break;
    }
    if(!load->type.is_unsigned||load->type.is_bool||width(load->type)!=1)return 0;
    if(load->kind==EX_CAST)load=load->left;
    if(load->kind!=EX_DEREF||width(load->type)!=1||
       loop_address(load->left,&pre,&post)!=src||pre||post!=1)return 0;

    start=++cg.label;advanced=++cg.label;done=++cg.label;
    code("; bounded far sentinel word loop: reuse tested byte\n    lda ");
    array_operand(src,0);code("\n    sta z:__arith_lhs\n    lda ");
    array_operand(src,2);code("\n    sta z:__arith_lhs+2\n    lda ");
    array_operand(dest,0);code("\n    tax\n    lda ");
    array_operand(count,0);
    code("\n    phy\n    tay\n    lda #$%04X\n    sep #$20\n.a8\n    cpy #0\n    beq cg_%s_%u\n",
         (unsigned)bits,cg.parser->unit,done);
    label(start);
    code("    lda [__arith_lhs]\n    beq cg_%s_%u\n"
         "    rep #$20\n.a16\n    sta a:$0000,x\n    sep #$20\n.a8\n"
         "    inx\n    inx\n    inc z:__arith_lhs\n    bne cg_%s_%u\n"
         "    inc z:__arith_lhs+1\n    bne cg_%s_%u\n    inc z:__arith_lhs+2\n",
         cg.parser->unit,done,cg.parser->unit,advanced,cg.parser->unit,advanced);
    label(advanced);
    code("    dey\n    bne cg_%s_%u\n",cg.parser->unit,start);
    label(done);
    code("    rep #$20\n.a16\n    tya\n    ply\n    sta ");
    array_operand(count,0);code("\n    txa\n    sta ");
    array_operand(dest,0);code("\n");
    if(loop_observed_outside(cg.function->body,s,src)){
        code("    lda z:__arith_lhs\n    sta ");array_operand(src,0);
        code("\n    lda z:__arith_lhs+2\n    sta ");array_operand(src,2);code("\n");
    }
    cg.divmod_available=0;
    return 1;
}

/* A bounded post-test loop can dispatch once on a private invariant
 * divisor. Keep the same quotient/remainder cache and loop lowering in
 * both versions, including the original countdown and cursor rules. */
typedef struct {
    DivmodCache *pair;
    Symbol *divisor;
    unsigned operations,remaining;
} LoopDivmod;

static void loop_divmod_expression(Expr *e,LoopDivmod *plan)
{
    DivmodCache *pair;
    unsigned i;
    if(!e)return;
    pair=divmod_find(e);
    if(pair&&(!plan->pair||plan->pair==pair)&&e->right->kind==EX_OBJECT&&
       body_private(e->right->symbol)&&divmod_byte_guard(e,common_type(e->left->type,e->right->type))){
        plan->pair=pair;
        plan->divisor=e->right->symbol;
        plan->operations|=e->op=='/'?1u:2u;
    }
    loop_divmod_expression(e->left,plan);
    loop_divmod_expression(e->right,plan);
    loop_divmod_expression(e->third,plan);
    for(i=0;i<e->arg_count;++i)loop_divmod_expression(e->args[i],plan);
}
static int loop_divmod_scan(Statement *s,LoopDivmod *plan)
{
    for(;s;s=s->next){
        if(s->inline_callee)return 0;
        switch(s->kind){
        case ST_BLOCK:case ST_EMPTY:break;
        case ST_IF:case ST_EXPR:case ST_BREAK:case ST_CONTINUE:case ST_RETURN:
            if(!plan->remaining)return 0;
            --plan->remaining;
            break;
        default:return 0;
        }
        loop_divmod_expression(s->expression,plan);
        if(!loop_divmod_scan(s->body,plan)||!loop_divmod_scan(s->alternate,plan))return 0;
    }
    return 1;
}
static Symbol *loop_divmod_version(Statement *s)
{
    LoopDivmod plan={0};
    plan.remaining=16;
    if(!cg.divmod_count||cg.divmod_version||s->kind!=ST_DO||cg.function->jump_label_count||
       cg.function->symbol->interrupt||cg.switch_depth||cg.parser->no_strength_reduction||
       cg.parser->no_body_optimizations||volatile_statement(s))return NULL;
    if(!loop_divmod_scan(s->body,&plan)||plan.operations!=3||
       scalar_writes(s->body,plan.divisor)||scalar_writes_expr(s->expression,plan.divisor))return NULL;
    return plan.divisor;
}
static int emit_region_loop(Statement *s,Statement *initializers)
{
    Codegen *saved;size_t start=cg.length;unsigned taken=0,mapped=0,i,j,count=0,free_words[16],free_count=0,words,trips;
    static unsigned weight[384],order[384];int result;
    Function *f=cg.function;
    Symbol *divisor=loop_divmod_version(s);
    if(initializers&&(divisor||cg.dot_count))return -1;
    if(divisor){
        unsigned wide=++cg.label,done=++cg.label;
        code("; loop version for invariant divmod divisor\n");
        load_symbol(divisor);
        code("    cmp #$0100\n");
        flag_branch("bcs","bcc",wide,0,0);
        cg.divmod_version=divisor;
        emit_loop_statement(s);
        jump(done);label(wide);
        cg.divmod_available=0;cg.divmod_wide_version=1;
        emit_loop_statement(s);
        cg.divmod_available=0;cg.divmod_version=NULL;cg.divmod_wide_version=0;
        label(done);return 1;
    }
    if(!initializers&&far_sentinel_word_loop(s))return 1;
    if(cg.parser->no_region_homes||cg.parser->no_dp_homes||region_loop||cg.dp_homes||cg.dp_trial||cg.stack_leaf||cg.scalar_leaf||
       cg.scalar_first||cg.leaf_count||cg.switch_depth||!f||f->symbol->interrupt||!f->slots||volatile_statement(s))
        return initializers?-1:bound_loop_statement(s);
    trips=region_trips(s); /* before any emission moves loop_current */
    saved=malloc(sizeof *saved);
    if(!saved){fputs("out of memory emitting assembly\n",stderr);exit(EXIT_FAILURE);}
    words=(f->slots+1)/2;if(words>384)words=384;
    *saved=cg;region_loop=s;region_initializers=NULL;region_count=0;region_entered=0;
    memset(cg.dp_weight,0,sizeof cg.dp_weight);
    bound_loop_statement(s);cg.dp_trial=0;
    i=region_entered&&dp_scan_range(region_begin,region_end,&taken);memcpy(weight,cg.dp_weight,sizeof weight);
    {char *assembly=cg.assembly;size_t capacity=cg.capacity;
     cg=*saved;cg.assembly=assembly;cg.capacity=capacity;cg.length=start;cg.assembly[start]=0;}
    region_loop=NULL;
    if(!i){free(saved);return initializers?-1:bound_loop_statement(s);}
    for(i=0;i<16;++i)if(!(taken&(1u<<i)))free_words[free_count++]=i;
    /* A frame access inside a loop weighs 8 per nesting level, so weight/8
     * times the trip count estimates accesses per region entry. Each saves 12
     * master clocks (abs,y 40 -> dp 28); copying a word in and out costs 136. */
    for(i=0;i<words;++i)if((unsigned long)weight[i]*trips*12>136ul*8){
        for(j=count;j&&weight[order[j-1]]<weight[i];--j)order[j]=order[j-1];
        order[j]=i;++count;
    }
    if(!count||!free_count){free(saved);return initializers?-1:bound_loop_statement(s);}
    if(initializers)s->initial=initializers;
    memset(cg.dp_map,0,sizeof cg.dp_map);
    for(i=0;i<count&&i<free_count;++i){
        cg.dp_map[order[i]]=(unsigned char)(free_words[i]+1);mapped|=1u<<free_words[i];
        region_slots[i]=order[i];region_words[i]=free_words[i];
        region_home_liveness(f,s,order[i]*2+1,&region_in[i],&region_out[i]);
    }
    if(initializers)s->initial=NULL;
    if(initializers){
        Statement *init;
        for(init=initializers;init;init=init->next){
            unsigned offset=init->expression->left->symbol->offset;
            if(offset&&(offset&1)&&(offset-1)/2<words&&cg.dp_map[(offset-1)/2])break;
        }
        if(!init){
            memcpy(cg.dp_map,saved->dp_map,sizeof cg.dp_map);
            free(saved);
            return -1;
        }
    }
    region_count=i;region_loop=s;region_entered=0;
    region_initializers=initializers;
    cg.dp_words=words;cg.dp_failed=0;
    result=bound_loop_statement(s);
    i=region_entered&&!cg.dp_failed&&dp_scan_range(region_begin,region_end,&taken)&&!(taken&mapped);
    cg.dp_homes=0;region_loop=NULL;region_initializers=NULL;
#ifdef REGION_DRYRUN
    i=0;
#endif
    if(!i){
        {char *assembly=cg.assembly;size_t capacity=cg.capacity;
         cg=*saved;cg.assembly=assembly;cg.capacity=capacity;cg.length=start;cg.assembly[start]=0;}
        free(saved);region_count=0;return initializers?-1:bound_loop_statement(s);
    }
    region_count=0;free(saved);dp_resolve(region_begin);return result;
}

static int emit_loop_statement(Statement *s)
{
    return emit_region_loop(s,NULL);
}

/* A straight-line suffix of existing word initializers can write the
 * promoted home on entry. If the region trial fails, emit the original
 * statements with their ordinary frame homes */
static int emit_region_initializers(Statement *first,Statement **loop)
{
    Statement copies[4],*s=first,*previous=loop_previous,*current=loop_current;
    unsigned count=0;
    int result;
    if(region_loop||cg.dp_homes||cg.dp_trial||cg.parser->no_region_homes||
       cg.parser->no_dp_homes||cg.parser->no_body_optimizations||
       cg.parser->no_private_regions||cg.function->jump_label_count)return -1;
    for(;s&&count<4;s=s->next){
        Expr *set=plain_assignment(s),*target,*value;
        if(!set||s->inline_callee)break;
        target=set->left;value=set->right;
        if(!body_private(target->symbol)||!word_integer(target->type)||
           !word_integer(value->type)||(value->kind!=EX_INT&&value->kind!=EX_OBJECT)||
           volatile_expression(set))break;
        copies[count]=*s;
        if(count)copies[count-1].next=&copies[count];
        ++count;
    }
    if(!count||!s||s->kind!=ST_DO||s->initial||body_asm_statements(cg.function->body))return -1;
    copies[count-1].next=NULL;
    loop_current=s;
    result=emit_region_loop(s,copies);
    loop_previous=previous;loop_current=current;
    if(result>=0)*loop=s;
    return result;
}
