/* Exact modular recurrences. A dead copied home can share the recurrence;
 * byte recurrences may widen only when all observations discard high bits. */
static int recurrence_demand(Expr *e,Symbol *v,unsigned demand)
{
    unsigned i,left=65535,right=65535,third=65535;uint32_t n;
    if(!e)return 1;
    if(e->kind==EX_OBJECT&&e->symbol==v)return demand<=255;
    if(e->kind==EX_CAST&&!e->type.pointers&&!e->type.is_bool&&reg_width(e->type)==2){
        left=width(e->type)==1?255:demand;
    }else if(e->kind==EX_BINARY){
        if(e->op=='&'){
            left=right=demand;
            if(integer_constant(e->right,&n))left&=n;
            if(integer_constant(e->left,&n))right&=n;
        }else if(e->op=='+'||e->op=='-'||e->op=='|'||e->op=='^')left=right=demand;
    }else if(e->kind==EX_UNARY&&(e->op=='+'||e->op=='-'||e->op=='~'))left=demand;
    else if(e->kind==EX_CHOOSE)right=third=demand;
    /* A plain write is not an observation of the old value */
    if(!(e->kind==EX_ASSIGN&&!e->op&&e->left->kind==EX_OBJECT)&&!recurrence_demand(e->left,v,left))return 0;
    if(!recurrence_demand(e->right,v,right)||!recurrence_demand(e->third,v,third))return 0;
    for(i=0;i<e->arg_count;++i)if(!recurrence_demand(e->args[i],v,65535))return 0;
    return 1;
}
static int recurrence_observations(Statement *s,Symbol *v)
{
    for(;s;s=s->next)if(!recurrence_demand(s->expression,v,65535)||!recurrence_demand(s->step,v,65535)||
       !recurrence_observations(s->initial,v)||!recurrence_observations(s->body,v)||!recurrence_observations(s->alternate,v))return 0;
    return 1;
}
static void recurrence_replace(Expr *e,Symbol *from,Symbol *to)
{
    unsigned i;if(!e)return;
    if(e->kind==EX_OBJECT&&e->symbol==from){e->symbol=to;e->type=to->type;return;}
    recurrence_replace(e->left,from,to);recurrence_replace(e->right,from,to);recurrence_replace(e->third,from,to);
    for(i=0;i<e->arg_count;++i)recurrence_replace(e->args[i],from,to);
}
static void recurrence_replace_body(Statement *s,Symbol *from,Symbol *to)
{
    for(;s;s=s->next){recurrence_replace(s->expression,from,to);recurrence_replace(s->step,from,to);
        recurrence_replace_body(s->initial,from,to);recurrence_replace_body(s->body,from,to);recurrence_replace_body(s->alternate,from,to);}
}
static int recurrence_control(Statement *s)
{
    for(;s;s=s->next){
        if(s->kind!=ST_EXPR&&s->kind!=ST_BLOCK&&s->kind!=ST_EMPTY&&s->kind!=ST_IF)return 0;
        if(!recurrence_control(s->body)||!recurrence_control(s->alternate))return 0;
    }return 1;
}
/* A bounded constant-seed shift can advance once per trip. Keep the C index
 * for its other uses and the original condition for early termination. */
static void bounded_shift_recurrence(Function *f,Statement *s)
{
    Statement *initial=body_single(s->initial),*body=body_single(s->body),*init;
    Expr *bound=s->expression,*start,*test,**shift,*value,*e,*next,*step;
    Symbol *index,*temp;
    Type word=type(TY_INT,0);
    uint32_t first,last,seed;
    char name[64];
    if(s->kind!=ST_FOR||!initial||initial->next||initial->kind!=ST_EXPR||
       !body||body->kind!=ST_IF||body->inline_callee||!bound||
       cg.parser->symbol_count==1024||f->slots+2>768)return;
    start=initial->expression;
    if(!start||start->kind!=EX_ASSIGN||start->op||start->left->kind!=EX_OBJECT||
       !integer_constant(start->right,&first))return;
    index=start->left->symbol;
    if(!word_integer(index->type)||!body_private(index)||first>=16||
       body_step_direction(s->step,index)!=1||scalar_writes(s->body,index)||
       body_effect(bound))return;
    while(bound->kind==EX_BINARY&&bound->op==TOK_LAND)bound=bound->left;
    if(bound->kind!=EX_BINARY||(bound->op!='<'&&bound->op!=TOK_LE)||
       bound->left->kind!=EX_OBJECT||bound->left->symbol!=index||
       !integer_constant(bound->right,&last)||last>16||last<=first)return;
    if(bound->op=='<')--last;
    test=body->expression;
    if(test->kind!=EX_BINARY||(test->op!=TOK_EQ&&test->op!=TOK_NE))return;
    shift=&test->left;value=test->right;
    if(value->kind==EX_BINARY&&value->op==TOK_SHL){shift=&test->right;value=test->left;}
    e=*shift;
    if(e->kind!=EX_BINARY||e->op!=TOK_SHL||e->type.pointers||!e->type.is_unsigned||
       (e->type.base!=TY_INT&&e->type.base!=TY_LONG)||e->right->kind!=EX_OBJECT||
       e->right->symbol!=index||!integer_constant(e->left,&seed)||!seed||last>=16||
       seed>(65535u>>last)||!word_integer(value->type)||!value->type.is_unsigned)return;
    word.is_unsigned=1;
    snprintf(name,sizeof name,"__shift_%u_%u",f->id,cg.parser->symbol_count);
    temp=new_symbol(cg.parser,name,word,e->location);
    temp->owner=f->id;temp->scope=1;temp->active=1;temp->internal=1;temp->offset=f->slots+1;f->slots+=2;
    init=body_statement(ST_EXPR,e->location);
    init->expression=new_expr(EX_ASSIGN,e->location,word);
    init->expression->left=body_object(temp,e->location);
    init->expression->right=new_expr(EX_INT,e->location,word);
    init->expression->right->value=seed<<first;
    initial->next=init;
    next=new_expr(EX_ASSIGN,e->location,word);next->op=TOK_SHL;
    next->left=body_object(temp,e->location);
    next->right=new_expr(EX_INT,e->location,type(TY_INT,0));next->right->value=1;
    step=new_expr(EX_COMMA,e->location,word);step->left=s->step;step->right=next;s->step=step;
    *shift=body_object(temp,e->location);free_expression(e);
    code("; bounded word shift recurrence\n");
}
static void value_recurrences(Function *f,Statement *s)
{
    for(;s;s=s->next){Expr *test=s->expression,*step=s->step,*rhs,*sum;Statement *first,*init,*advance;Symbol *index,*temp;VrEffects effects={0};unsigned n;int casts_ok=1;char name[64];
        value_recurrences(f,s->body);value_recurrences(f,s->alternate);
        if(!f->jump_label_count)bounded_shift_recurrence(f,s);
        if(s->kind!=ST_FOR||!test||test->kind!=EX_BINARY||test->op!='<'||test->left->kind!=EX_OBJECT||
           test->right->kind!=EX_INT||!step||(step->kind!=EX_POST&&step->kind!=EX_PRE)||step->op!=TOK_INC||
           step->left->kind!=EX_OBJECT||step->left->symbol!=test->left->symbol||!recurrence_control(s->body))continue;
        index=test->left->symbol;if(!body_private(index)||scalar_writes(s->body,index))continue;
        if(width(index->type)==1){if(!index->type.is_unsigned)continue;}
        else if(index->type.base!=TY_INT||index->type.pointers)continue;
        first=s->body;while(first&&first->kind==ST_BLOCK&&!first->next)first=first->body;
        if(!first||first->kind!=ST_EXPR||!first->expression||first->expression->kind!=EX_ASSIGN||first->expression->op||
           first->expression->left->kind!=EX_OBJECT||!body_private(first->expression->left->symbol))continue;
        rhs=first->expression->right;sum=rhs;
        while(sum->kind==EX_CAST){
            if(sum->type.is_bool||sum->type.pointers||width(sum->type)<width(rhs->type))casts_ok=0;
            sum=sum->left;
        }
        if(!casts_ok)continue;
        if(sum->kind!=EX_BINARY||sum->op!='+'||sum->left->kind!=EX_OBJECT||sum->left->symbol!=index||
           (rhs->type.base!=TY_CHAR&&rhs->type.base!=TY_INT)||!rhs->type.is_unsigned||rhs->type.pointers||
           sum->right->kind!=EX_OBJECT||object_volatile(sum->right->type)||sum->right->type.pointers||sum->right->type.array||
           !sum->right->type.is_unsigned||reg_width(sum->right->type)!=2)continue;
        n=test->right->value;
        /* The original addition must not overflow signed promotion. The final
         * unused recurrence increment may wrap, but remains unsigned. */
        if(!n||n>255||width(sum->right->type)!=1)continue;
        if(width(index->type)!=1){
            Statement *st=body_single(s->initial);
            Expr *init_e=st&&!st->next&&st->kind==ST_EXPR?st->expression:NULL;
            uint32_t start_v;
            int init_ok=init_e&&init_e->kind==EX_ASSIGN&&!init_e->op&&init_e->left->kind==EX_OBJECT&&
                        init_e->left->symbol==index&&
                        ((integer_constant(init_e->right,&start_v)&&start_v<=255)||
                         (init_e->right->known.valid&&init_e->right->known.min>=0&&init_e->right->known.max<=255));
            if(!init_ok&&!(test->left->known.valid&&test->left->known.min>=0&&test->left->known.max<=255))continue;
        }
        vr_effect_statements(&effects,s->body);
        if(effects.unknown||effects.symbols[body_symbol(sum->right->symbol)]||cg.parser->symbol_count==1024||f->slots+2>768)continue;
        snprintf(name,sizeof name,"__recurrence_%u_%u",f->id,cg.parser->symbol_count);
        temp=new_symbol(cg.parser,name,rhs->type,rhs->location);temp->owner=f->id;temp->scope=1;temp->active=1;temp->internal=1;temp->offset=f->slots+1;f->slots+=2;
        {Symbol *copy=first->expression->left->symbol;int in,out;
            region_home_liveness(f,s,copy->offset,&in,&out);
            if(!out&&same_type(copy->type,rhs->type)&&scalar_writes(s->body,copy)==1){
                int wide=width(copy->type)==1&&recurrence_observations(s->body,copy);
                if(wide){temp->type=type(TY_INT,0);temp->type.is_unsigned=1;}
                code("; coalesced recurrence home%s\n",wide?": low-byte observations":"");
                /* Preserve this statement's location/markers for execution probes */
                first->expression->right=NULL;free_expression(first->expression);first->expression=NULL;first->kind=ST_EMPTY;
                recurrence_replace_body(s->body,copy,temp);
            }
        }
        code("; exact modular value recurrence\n");
        init=body_statement(ST_EXPR,rhs->location);init->expression=new_expr(EX_ASSIGN,rhs->location,temp->type);
        init->expression->left=body_object(temp,rhs->location);init->expression->right=body_clone(rhs);
        while(s->initial&&s->initial->kind==ST_BLOCK&&!s->initial->next)s->initial=s->initial->body;
        {Statement **tail=&s->initial;while(*tail)tail=&(*tail)->next;*tail=init;}
        if (first->expression) {
            first->expression->right = body_object(temp, rhs->location);
        }
        free_expression(rhs);
        advance=body_statement(ST_EXPR,s->location);advance->expression=new_expr(EX_PRE,s->location,temp->type);
        advance->expression->op=TOK_INC;advance->expression->left=body_object(temp,s->location);
        {Statement **tail=&s->body;while(*tail)tail=&(*tail)->next;*tail=advance;}
    }
}
static void value_recurrences_prepare(Function *f)
{
    if(!cg.parser->no_body_optimizations&&!cg.parser->no_strength_reduction&&!f->symbol->interrupt&&!statement_has_case(f->body))value_recurrences(f,f->body);
}
