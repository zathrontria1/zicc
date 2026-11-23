/* Bounded structured IR simplification. Facts describe only unescaped private
 * scalar objects: indirect stores and arbitrary callees cannot change them.
 * No object names, dimensions or benchmark inputs participate in selection. */
typedef struct { Expr *value[1024]; } BodyFacts;
static int body_private(Symbol *v)
{
    return loop_private(v)&&!object_volatile(v->type)&&!structure_object(v->type)&&
        !v->type.array&&value_width(v->type)<=2;
}
static unsigned body_symbol(Symbol *v){return (unsigned)(v-cg.parser->symbols);}
static Expr *body_clone(Expr *e)
{
    Expr *n;unsigned i;if(!e)return NULL;n=allocate(sizeof *n);*n=*e;
    n->left=body_clone(e->left);n->right=body_clone(e->right);n->third=body_clone(e->third);
    for (i = 0; i < e->arg_count; ++i) {
        n->args[i] = body_clone(e->args[i]);
    }
    return n;
}
static Expr *body_object(Symbol *v,Location at)
{
    Expr *e=new_expr(EX_OBJECT,at,v->type);e->symbol=v;return e;
}
static Expr *body_literal(Type t,uint32_t value,Location at)
{
    Expr *e=new_expr(EX_INT,at,t);e->value=initializer_cast(value,t);return e;
}
static int body_private_callback(Symbol *v)
{
    return function_pointer(v->type)&&!object_volatile(v->type)&&loop_private(v)&&
        !cg.function->jump_label_count&&!find_symbol(cg.parser,"$basic_asm");
}
static int body_fact_home(Symbol *v)
{
    return body_private(v)||body_private_callback(v)||(loop_private(v)&&!object_volatile(v->type)&&
           !v->type.array&&(far_pointer(v->type)||(!v->type.pointers&&
           (v->type.base==TY_LONG||v->type.base==TY_LONGLONG||v->type.base==TY_FLOAT))));
}
static Statement *body_statement(StatementKind kind,Location at)
{
    Statement *s=allocate(sizeof *s);s->kind=kind;s->location=at;return s;
}
static Statement *body_clone_statements(Statement *s)
{
    Statement *head=NULL,**tail=&head;
    for(;s;s=s->next){Statement *n=allocate(sizeof *n);*n=*s;n->next=NULL;
        n->expression=body_clone(s->expression);n->step=body_clone(s->step);
        n->body=body_clone_statements(s->body);n->alternate=body_clone_statements(s->alternate);
        n->initial=body_clone_statements(s->initial);*tail=n;tail=&n->next;
    }return head;
}
static int body_equal(Expr *a,Expr *b)
{
    unsigned i;if(!a||!b)return a==b;
    if(a->kind!=b->kind||a->op!=b->op||a->value!=b->value||a->value_high!=b->value_high||a->symbol!=b->symbol||
       a->string!=b->string||a->arg_count!=b->arg_count||!same_type(a->type,b->type))return 0;
    if(!body_equal(a->left,b->left)||!body_equal(a->right,b->right)||!body_equal(a->third,b->third))return 0;
    for (i = 0; i < a->arg_count; ++i) {
        if (!body_equal(a->args[i], b->args[i])) {
            return 0;
        }
    }
    return 1;
}
static int body_effect(Expr *e)
{
    unsigned i;if(!e)return 0;
    if(e->kind==EX_CALL||e->kind==EX_ASSIGN||e->kind==EX_PRE||e->kind==EX_POST||volatile_expression(e))return 1;
    if(body_effect(e->left)||body_effect(e->right)||body_effect(e->third))return 1;
    for (i = 0; i < e->arg_count; ++i) {
        if (body_effect(e->args[i])) {
            return 1;
        }
    }
    return 0;
}
static int body_mutating(Expr *e)
{
    unsigned i;if(!e)return 0;
    if(e->kind==EX_ASSIGN||e->kind==EX_PRE||e->kind==EX_POST)return 1;
    if(body_mutating(e->left)||body_mutating(e->right)||body_mutating(e->third))return 1;
    for (i = 0; i < e->arg_count; ++i) {
        if (body_mutating(e->args[i])) {
            return 1;
        }
    }
    return 0;
}
static int body_nested_updates(Expr *e)
{
    if(e&&(e->kind==EX_ASSIGN||e->kind==EX_PRE||e->kind==EX_POST))
        return body_mutating(e->left)||body_mutating(e->right);
    return body_mutating(e);
}
static int body_has_deref(Expr *e)
{
    unsigned i;if(!e)return 0;
    if(e->kind==EX_DEREF)return 1;
    if(body_has_deref(e->left)||body_has_deref(e->right)||body_has_deref(e->third))return 1;
    for (i = 0; i < e->arg_count; ++i) {
        if (body_has_deref(e->args[i])) {
            return 1;
        }
    }
    return 0;
}
static int body_pointer_post_store(Statement *s,Expr **target_out,Symbol **home_out,unsigned *offset_out,unsigned *stride_out,Expr **val)
{
    Expr *e,*target,*lhs;Symbol *home=NULL;unsigned offset=0;
    if(!s||s->kind!=ST_EXPR||!s->expression)return 0;
    e=s->expression;
    if(e->kind!=EX_ASSIGN||e->op||!e->left||e->left->kind!=EX_DEREF)return 0;
    target=e->left->left;
    if(!target||target->kind!=EX_POST||target->op!=TOK_INC||!target->left)return 0;
    lhs=target->left;
    if(lhs->kind==EX_OBJECT&&body_private(lhs->symbol)){
        home=lhs->symbol;
    }else{
        home=fixed_memory_object(lhs,&offset);
        if(!home||home->type.banked||object_volatile(home->type))return 0;
    }
    if(!value_type(lhs->type).pointers||far_pointer(value_type(lhs->type))||object_volatile(lhs->type))return 0;
    *stride_out=width(pointed_type(value_type(lhs->type)));
    if(!*stride_out||*stride_out>65535||loop_mentions(e->right,home)||body_effect(e->right)||body_has_deref(e->right))return 0;
    *target_out=lhs;*home_out=home;*offset_out=offset;*val=e->right;return 1;
}
static int body_pointer_term_store(Statement *s,Expr *base_target,Symbol *home,Expr **val)
{
    Expr *e;
    if(!s||s->kind!=ST_EXPR||!s->expression)return 0;
    e=s->expression;
    if(e->kind!=EX_ASSIGN||e->op||!e->left||e->left->kind!=EX_DEREF)return 0;
    if(!e->left->left||!body_equal(e->left->left,base_target))return 0;
    if(loop_mentions(e->right,home)||body_effect(e->right)||body_has_deref(e->right))return 0;
    *val=e->right;return 1;
}
static void body_pointer_store_sequences(Function *f,Statement *s,unsigned *temps)
{
    for(;s;s=s->next){
        Expr *target=NULL,*val=NULL;Symbol *home=NULL;unsigned offset=0,stride=0;
        body_pointer_store_sequences(f,s->initial,temps);
        body_pointer_store_sequences(f,s->body,temps);
        body_pointer_store_sequences(f,s->alternate,temps);
        if(!body_pointer_post_store(s,&target,&home,&offset,&stride,&val))continue;
        {
            Statement *p=s->next,*last=s;
            unsigned count=1;int has_terminal=0,priv=(target->kind==EX_OBJECT&&body_private(home));
            while(p){
                Expr *next_target=NULL,*next_val=NULL;Symbol *next_home=NULL;unsigned next_off=0,next_stride=0;
                if(body_pointer_post_store(p,&next_target,&next_home,&next_off,&next_stride,&next_val)&&
                   next_home==home&&next_off==offset&&next_stride==stride&&body_equal(next_target,target)){
                    count++;last=p;p=p->next;continue;
                }
                if(body_pointer_term_store(p,target,home,&next_val)){
                    has_terminal=1;last=p;p=p->next;
                }
                break;
            }
            if(count+has_terminal>=2&&count<=65535/stride){
                Symbol *cursor=priv?home:NULL;
                if(!priv){
                    char name[64];Type t=unqualified_value(target->type);
                    if(*temps>=16||cg.parser->symbol_count==1024||f->slots+2>768)continue;
                    t.banked=0;
                    snprintf(name,sizeof name,"__seq_%u_%u",f->id,++*temps);
                    cursor=new_symbol(cg.parser,name,t,s->location);
                    cursor->owner=f->id;cursor->scope=1;cursor->active=1;cursor->internal=1;
                    cursor->offset=f->slots+1;f->slots+=2;
                }
                {
                    Statement *curr=s;unsigned i;
                    Expr *base_copy=priv?NULL:body_clone(target);
                    for(i=0;i<count;++i){
                        Expr *ptr_use=body_object(cursor,curr->location);
                        if(priv||i){
                            Expr *add=new_expr(EX_BINARY,curr->location,cursor->type);
                            add->op='+';add->left=ptr_use;
                            add->right=body_literal(type(TY_INT,0),i,curr->location);
                            ptr_use=add;
                        }
                        free_expression(curr->expression->left->left);
                        curr->expression->left->left=ptr_use;
                        curr=curr->next;
                    }
                    if(has_terminal){
                        Expr *add=new_expr(EX_BINARY,curr->location,cursor->type);
                        add->op='+';add->left=body_object(cursor,curr->location);
                        add->right=body_literal(type(TY_INT,0),count,curr->location);
                        free_expression(curr->expression->left->left);
                        curr->expression->left->left=add;
                    }
                    if(!priv){
                        Statement *first_store=allocate(sizeof *first_store);
                        Expr *init=new_expr(EX_ASSIGN,s->location,cursor->type);
                        *first_store=*s;
                        init->left=body_object(cursor,s->location);init->right=base_copy;
                        s->expression=init;s->next=first_store;
                    }
                    {
                        Statement *adv=body_statement(ST_EXPR,last->location);
                        Expr *add=new_expr(EX_BINARY,last->location,cursor->type);
                        adv->expression=new_expr(EX_ASSIGN,last->location,cursor->type);
                        adv->expression->left=priv?body_object(home,last->location):body_clone(base_copy);
                        add->op='+';add->left=body_object(cursor,last->location);
                        add->right=body_literal(type(TY_INT,0),count,last->location);
                        adv->expression->right=add;
                        adv->next=last->next;
                        last->next=adv;
                        s=adv;
                    }
                }
            }
        }
    }
}
static int body_fact_reads(Expr *e,Symbol *v)
{
    unsigned offset;
    if(!e)return 0;
    if(e->kind==EX_ADDRESS&&direct_memory_object(e->left,&offset))return 0;
    if(e->kind==EX_OBJECT)return e->symbol==v&&!e->type.array;
    return body_fact_reads(e->left,v)||body_fact_reads(e->right,v)||body_fact_reads(e->third,v);
}
static void body_forget(BodyFacts *facts,Symbol *v)
{
    unsigned i;
    for(i=0;i<cg.parser->symbol_count;++i)if(facts->value[i]&&
       (i==body_symbol(v)||body_fact_reads(facts->value[i],v))){free_expression(facts->value[i]);facts->value[i]=NULL;}
}
static void body_clear(BodyFacts *facts)
{
    unsigned i;for(i=0;i<1024;++i){free_expression(facts->value[i]);facts->value[i]=NULL;}
}
static BodyFacts *body_copy_facts(BodyFacts *facts)
{
    BodyFacts *copy=allocate(sizeof *copy);unsigned i;
    for (i = 0; i < 1024; ++i) {
        copy->value[i] = body_clone(facts->value[i]);
    }
    return copy;
}
/* Conservative within an expression: forget every assignment before replacing
 * any read. This avoids imposing an evaluation order on C operands/arguments. */
static void body_kill_expr(BodyFacts *facts,Expr *e)
{
    unsigned i;if(!e)return;
    if((e->kind==EX_ASSIGN||e->kind==EX_PRE||e->kind==EX_POST)&&e->left->kind==EX_OBJECT)
        body_forget(facts,e->left->symbol);
    body_kill_expr(facts,e->left);body_kill_expr(facts,e->right);body_kill_expr(facts,e->third);
    for(i=0;i<e->arg_count;++i)body_kill_expr(facts,e->args[i]);
}
static void body_kill_statements(BodyFacts *facts,Statement *s)
{
    for(;s;s=s->next){body_kill_expr(facts,s->expression);body_kill_expr(facts,s->step);
        body_kill_statements(facts,s->initial);body_kill_statements(facts,s->body);body_kill_statements(facts,s->alternate);}
}
static void body_direct_callback(Expr *call,Expr *known)
{
    Expr *target=known&&known->kind==EX_ADDRESS?known->left:known;
    FunctionType *signature=call->left->type.signature;
    if(!target||target->kind!=EX_OBJECT||!target->symbol->function||
       signature->count<0||target->symbol->old_style||
       target->symbol->param_count!=signature->count||
       !same_type(unqualified_value(call->left->type),unqualified_value(target->type)))return;
    call->symbol=target->symbol;
    free_expression(call->left);call->left=NULL;
}
/* Negation already produces zero on the zero arm of a pure conditional */
static int body_fold_zero_negation(Expr **at)
{
    Expr *e=*at,*test=e->left,*value,*zero,*negation,*operand;
    uint32_t n;
    if(cg.parser->no_strength_reduction||!word_integer(e->type)||
       test->kind!=EX_BINARY||(test->op!=TOK_EQ&&test->op!=TOK_NE)||
       !word_integer(common_type(test->left->type,test->right->type)))return 0;
    value=test->left;
    if(!integer_constant(test->right,&n)||n){
        if(!integer_constant(test->left,&n)||n)return 0;
        value=test->right;
    }
    zero=test->op==TOK_EQ?e->right:e->third;
    negation=test->op==TOK_EQ?e->third:e->right;
    if(!integer_constant(zero,&n)||n)return 0;
    operand=word_bits(negation);
    if(operand->kind==EX_UNARY&&operand->op=='-')operand=operand->left;
    else if(operand->kind==EX_BINARY&&operand->op=='-'&&integer_constant(operand->left,&n)&&!n)
        operand=operand->right;
    else return 0;
    if(body_effect(e)||!body_equal(word_bits(value),word_bits(operand)))return 0;
    if(negation==e->right)e->right=NULL;else e->third=NULL;
    free_expression(e);*at=negation;return 1;
}
static Expr *body_near_pointee(Expr *e)
{
    while(e->kind==EX_CAST&&value_type(e->type).pointers&&!far_pointer(value_type(e->type))&&
          value_type(e->left->type).pointers&&!far_pointer(value_type(e->left->type)))e=e->left;
    return e;
}
static int body_repeatable_address(Expr *e)
{
    unsigned offset;
    e=body_near_pointee(e);
    if(!value_type(e->type).pointers||far_pointer(value_type(e->type))||body_effect(e))return 0;
    if(near_object_address(e,&offset))return 1;
    if(e->kind==EX_BINARY&&e->op=='+'&&
       (e->right->kind==EX_INT||(e->right->kind==EX_OBJECT&&word_integer(e->right->type)&&
        body_private(e->right->symbol))))return body_repeatable_address(e->left);
    return e->kind==EX_OBJECT&&body_private(e->symbol);
}
/* Follow static far relocations without evaluating any subexpression or
 * resolving a link-time bank. A byte offset is useful only inside its object. */
static Symbol *body_rom_home(Expr *e,int address,int64_t *offset)
{
    if(e->kind==EX_OBJECT){
        Symbol *s=e->symbol;
        Relocation *r=s->relocations;
        if(s->owner)return NULL;
        if(address||e->type.array)return s;
        if(far_pointer(e->type)&&s->type.banked&&object_constant(s->type)&&
           !object_volatile(s->type)&&s->defined&&r&&r->symbol&&!r->symbol->function&&
           !r->next&&!r->offset&&r->size==width(s->type)&&r->far_value){
            *offset+=r->addend;
            return r->symbol;
        }
    }else if(e->kind==EX_ADDRESS){
        return body_rom_home(e->left,1,offset);
    }else if(e->kind==EX_MEMBER&&(address||e->type.array)){
        *offset+=e->value;
        return body_rom_home(e->left,e->op=='.',offset);
    }else if(e->kind==EX_DEREF&&(address||e->type.array)){
        return body_rom_home(e->left,0,offset);
    }else if(!address&&far_pointer(value_type(e->type))&&e->kind==EX_CAST&&
             far_pointer(value_type(e->left->type))){
        return body_rom_home(e->left,0,offset);
    }else if(!address&&far_pointer(value_type(e->type))&&e->kind==EX_BINARY&&
             (e->op=='+'||e->op=='-')&&far_pointer(value_type(e->left->type))&&
             e->right->kind==EX_INT&&known_integer(e->right->type)){
        int n=e->right->type.is_unsigned?(int)(uint16_t)e->right->value:(int)(int16_t)e->right->value;
        int64_t bytes=(int64_t)n*width(pointed_type(value_type(e->left->type)));
        *offset+=e->op=='+'?bytes:-bytes;
        return body_rom_home(e->left,0,offset);
    }
    return NULL;
}
static int body_rom_integer(Expr *e,uint32_t *bits)
{
    int64_t offset=0;
    Symbol *home;
    unsigned n;
    if(cg.parser->no_known_values||!known_integer(e->type)||volatile_expression(e)||
       (e->kind!=EX_MEMBER&&e->kind!=EX_DEREF))return 0;
    home=body_rom_home(e,1,&offset);
    n=width(e->type);
    if(!home||!home->type.banked||!home->defined||!home->initializer||home->relocations||
       !object_constant(home->type)||volatile_type(home->type)||offset<0||offset+n>width(home->type))return 0;
    *bits=home->initializer[offset];
    if(n==2)*bits|=(uint32_t)home->initializer[offset+1]<<8;
    return 1;
}
static void body_fold_literal_arguments(Expr *call,int unused);
static void body_replace(Expr **at,BodyFacts *facts,int lvalue_context)
{
    Expr *e=*at;unsigned i;if(!e)return;
    if(e->kind==EX_CALL&&e->left&&e->left->kind==EX_OBJECT&&function_pointer(e->left->type))
        body_direct_callback(e,facts->value[body_symbol(e->left->symbol)]);
    if(!lvalue_context&&e->kind==EX_OBJECT&&facts->value[body_symbol(e->symbol)]){
        Expr *n=body_clone(facts->value[body_symbol(e->symbol)]);free_expression(e);*at=n;return;
    }
    if(!lvalue_context&&e->kind==EX_OBJECT&&!e->type.pointers&&!e->type.array&&e->type.base==TY_FLOAT){
        Symbol *object=e->symbol;
        if(object->internal&&object->defined&&object->initializer&&!object->relocations&&
           object_constant(object->type)&&!object_volatile(object->type)){
            uint32_t bits=0;
            for(i=0;i<4;++i)bits|=(uint32_t)object->initializer[i]<<(8*i);
            e->kind=EX_INT;e->symbol=NULL;e->type=type(TY_FLOAT,0);e->value=bits;
            return;
        }
    }
    /* A bit-field node still needs the address of its enclosing storage word */
    body_replace(&e->left,facts,e->kind==EX_ADDRESS||e->kind==EX_ASSIGN||e->kind==EX_PRE||
                 e->kind==EX_POST||e->kind==EX_BITFIELD);
    body_replace(&e->right,facts,0);body_replace(&e->third,facts,0);
    for(i=0;i<e->arg_count;++i)body_replace(&e->args[i],facts,0);
    if(e->kind==EX_CALL&&e->symbol&&!e->left&&known_integer(e->type)){
        for(i=0;i<e->arg_count&&e->args[i]->kind==EX_INT;++i){}
        if(i==e->arg_count)body_fold_literal_arguments(e,0);
    }
    uint32_t bits;
    if(!lvalue_context&&body_rom_integer(e,&bits)){
        Expr *literal=body_literal(unqualified_value(e->type),bits,e->location);
        free_expression(e);*at=literal;return;
    }
    if(e->kind==EX_CHOOSE&&body_fold_zero_negation(at))return;
    if(e->kind==EX_DEREF){
        if(!lvalue_context&&!cg.parser->no_strength_reduction&&
           e->type.base==TY_CHAR&&!e->type.pointers&&!e->type.array&&!volatile_expression(e)){
            unsigned byte;
            String *string=scalar_string_offset(e->left,&byte);
            if(string&&byte<string->size){
                Expr *literal=body_literal(unqualified_value(e->type),string->bytes[byte],e->location);
                free_expression(e);*at=literal;return;
            }
        }
        Expr *address=body_near_pointee(e->left);
        if(address->kind==EX_ADDRESS&&!far_pointer(address->type)){
            Expr *object=address->left;
            if(e->type.banked==object->type.banked&&
               (same_type(e->type,object->type)||
                (!e->type.array&&!object->type.array&&object_volatile(e->type)==object_volatile(object->type)&&
                 same_type(unqualified_value(e->type),unqualified_value(object->type))))){
                object->location=e->location;
                address->left=NULL;
                free_expression(e);
                *at=object;
                body_replace(at,facts,lvalue_context);
                return;
            }
        }
    }
    if(e->kind==EX_MEMBER&&e->op==TOK_ARROW&&e->left->kind==EX_ADDRESS&&
       e->left->left->kind==EX_OBJECT&&!far_pointer(e->left->type)){
        Expr *address=e->left;
        e->left=address->left;
        address->left=NULL;
        free_expression(address);
        e->op='.';
    }
    if(e->kind==EX_BINARY&&(e->op==TOK_EQ||e->op==TOK_NE)&&!cg.parser->no_strength_reduction&&
       value_type(e->left->type).pointers&&value_type(e->right->type).pointers&&
       !far_pointer(value_type(e->left->type))&&!far_pointer(value_type(e->right->type))){
        Expr *left=body_near_pointee(e->left),*right=body_near_pointee(e->right);
        if(body_equal(left,right)&&body_repeatable_address(left)){
            free_expression(e->left);free_expression(e->right);
            fold_literal(e,e->op==TOK_EQ);return;
        }
    }
    scalar_refold_expr(e);
}
typedef struct { uint32_t value; Expr *expr; int written, varies; } BodyDefinition;
static void body_record_definitions(Expr *e,BodyDefinition *defs)
{
    if(!e)return;
    if((e->kind==EX_ASSIGN||e->kind==EX_PRE||e->kind==EX_POST)&&e->left->kind==EX_OBJECT){
        Symbol *v=e->left->symbol;
        BodyDefinition *d=&defs[body_symbol(v)];
        uint32_t value;
        unsigned offset;
        Symbol *addr;
        if(e->kind==EX_ASSIGN&&!e->op&&known_integer(v->type)&&integer_constant(e->right,&value)){
            value=initializer_cast(value,v->type);
            if(d->written&&d->value!=value)d->varies=1;
            d->value=value;d->written=1;
        }else if(e->kind==EX_ASSIGN&&!e->op&&v->type.pointers&&!far_pointer(v->type)&&
                 body_private(v)&&(addr=near_object_address(e->right,&offset))!=NULL&&!addr->owner){
            if(d->written&&(!d->expr||!body_equal(d->expr,e->right)))d->varies=1;
            d->expr=e->right;d->written=1;
        }else{
            d->varies=1;
        }
    }
    body_record_definitions(e->left,defs);body_record_definitions(e->right,defs);body_record_definitions(e->third,defs);
    for(unsigned i=0;i<e->arg_count;++i)body_record_definitions(e->args[i],defs);
}
static void body_constant_definitions(Statement *s,BodyDefinition *defs,BodyFacts *facts)
{
    for(;s;s=s->next){
        if(facts){body_replace(&s->expression,facts,0);body_replace(&s->step,facts,0);}
        else{body_record_definitions(s->expression,defs);body_record_definitions(s->step,defs);}
        body_constant_definitions(s->initial,defs,facts);
        body_constant_definitions(s->body,defs,facts);
        body_constant_definitions(s->alternate,defs,facts);
    }
}
/* An uninitialized read of a non-addressed automatic scalar is undefined.
 * Every defined read of such a scalar with one written value sees that value. */
static void body_propagate_constant_definitions(Function *f,BodyFacts *facts)
{
    for(int pass=0;pass<4;++pass){
        BodyDefinition defs[1024]={0};int found=0;
        body_constant_definitions(f->body,defs,NULL);
        for(unsigned i=0;i<cg.parser->symbol_count;++i){
            Symbol *v=&cg.parser->symbols[i];
            if(defs[i].written&&!defs[i].varies&&v->scope&&v->offset&&!v->internal&&!v->storage&&
               body_private(v)){
                if(known_integer(v->type)){
                    facts->value[i]=body_literal(v->type,defs[i].value,f->body->location);found=1;
                }else if(v->type.pointers&&!far_pointer(v->type)&&defs[i].expr){
                    Expr *copy=body_clone(defs[i].expr);
                    if(!same_type(unqualified_value(copy->type),unqualified_value(v->type))){
                        Expr *cast=new_expr(EX_CAST,f->body->location,v->type);
                        cast->left=copy;copy=cast;
                    }
                    facts->value[i]=copy;found=1;
                }
            }
        }
        if(!found)break;
        body_constant_definitions(f->body,NULL,facts);body_clear(facts);
    }
}
/* Facts never duplicate loads or nontrivial computations. Only constants and
 * copies (including offsets derived by an induction update) are substituted. */
static int body_fact_value(Expr *e)
{
    unsigned offset;
    if(e->kind==EX_INT)return 1;
    if(e->kind==EX_STRING)return 1;
    if(e->kind==EX_CAST&&far_pointer(e->type)&&e->left->kind==EX_STRING)return 1;
    if(e->kind==EX_OBJECT&&e->symbol->function)return 1;
    if(e->kind==EX_ADDRESS&&e->left->kind==EX_OBJECT&&e->left->symbol->function)return 1;
    if(e->kind==EX_ADDRESS){
        Symbol *s=near_object_address(e,&offset);
        return !far_pointer(e->type)&&((s&&!s->owner)||direct_memory_object(e->left,&offset));
    }
    if(e->kind==EX_OBJECT&&e->type.array&&!e->type.banked)return 1;
    if(e->kind==EX_CAST&&e->type.pointers&&!far_pointer(e->type)){
        if(e->left->kind==EX_ADDRESS)return body_fact_value(e->left);
        return near_object_address(e,&offset)!=NULL;
    }
    if(e->kind==EX_CAST&&!e->type.pointers&&numeric(e->type)&&e->type.base!=TY_FLOAT)return body_fact_value(e->left);
    if(e->kind==EX_BINARY&&e->op=='+'&&e->type.pointers&&!far_pointer(value_type(e->type))&&
       body_fact_value(e->left)&&e->right->kind==EX_INT)
        return 1;
    if(far_pointer(e->type)&&scalar_string_offset(e,&offset))return 1;
    uint32_t addend;
    if(function_address_relocation(e,&addend))return 1;
    return e->kind==EX_OBJECT&&body_private(e->symbol);
}
/* A discarded nonvolatile load still evaluates its address. With only
 * casts and literal offsets around a cursor update, keep just the update. */
static int body_discarded_load(Expr **at)
{
    Expr *load=*at,**address;
    for(;;){
        uint32_t amount;
        if(load->kind==EX_CAST&&!load->type.pointers&&
           (load->type.base==TY_VOID||(known_integer(load->type)&&known_integer(load->left->type))))
            load=load->left;
        else if(load->kind==EX_BINARY&&(load->op==TOK_SHL||load->op==TOK_SHR)&&
                known_integer(load->left->type)&&integer_constant(load->right,&amount))
            load=load->left;
        else break;
    }
    if(load->kind!=EX_DEREF||load->type.array||volatile_type(load->type))return 0;
    address=&load->left;
    for(;;){
        Expr *e=*address;
        if(e->kind==EX_CAST&&e->type.pointers&&e->left->type.pointers&&
           !far_pointer(e->type)&&!far_pointer(e->left->type))
            address=&e->left;
        else if(e->kind==EX_BINARY&&e->type.pointers&&!far_pointer(e->type)&&
                (e->op=='+'||e->op=='-')&&e->right->kind==EX_INT)
            address=&e->left;
        else break;
    }
    if(((*address)->kind==EX_ASSIGN||(*address)->kind==EX_PRE||(*address)->kind==EX_POST)&&
       (*address)->type.pointers){
        Expr *update=*address;
        *address=NULL;
        free_expression(*at);
        *at=update;
        return 1;
    }
    return 0;
}
static int body_exact_binary32_update(int op,Expr *left,Expr *right)
{
    float x,y;
    uint32_t bits;
    double a,b,result;
    if(!left||right->type.base!=TY_FLOAT||
       !binary32_literal(left,&x,1)||!binary32_literal(right,&y,1)||
       binary32_constant_operation(op,x,y,&bits))return 0;
    a=x;b=y;result=initializer_float(bits,left->type);
    if(op=='*')return result==a*b;
    if(op=='/')return result*b==a;
    if(op=='-')b=-b;
    /* Subtract the larger addend so a tiny addend cannot round away */
    if((a<0?-a:a)<(b<0?-b:b)){double swap=a;a=b;b=swap;}
    return result==a+b&&result-a==b;
}
static int body_literal_function_add(Expr *address,Expr *amount)
{
    uint32_t offset,bits;
    return function_address_relocation(address,&offset)&&!offset&&
           integer_constant(amount,&bits)&&bits<=65535;
}
static int body_literal_string_advance(Expr *value)
{
    unsigned offset=0;
    String *string=value?scalar_string_offset(value,&offset):NULL;
    return string&&offset<string->size;
}
static void body_expr(Expr **at,BodyFacts *facts,int discarded)
{
    Expr *e=*at,*known=NULL,*amount=NULL;Symbol *v=NULL;int operation='+';
    if(!e)return;
    if(cg.function->uses_wide&&body_nested_updates(e)){body_kill_expr(facts,e);return;}
    if((e->kind==EX_ASSIGN||e->kind==EX_PRE||e->kind==EX_POST)&&e->left->kind==EX_OBJECT&&
       (body_fact_home(e->left->symbol)||(!e->left->symbol->owner&&!object_volatile(e->left->type)&&
        facts->value[body_symbol(e->left->symbol)]))){
        v=e->left->symbol;
        Expr *old=facts->value[body_symbol(v)];
        if(e->kind==EX_ASSIGN&&e->op&&old&&wide_integer_literal(old)&&!body_effect(e->right)){
            body_replace(&e->right,facts,0);
            scalar_refold_expr(e->right);
        }
        if((e->kind==EX_PRE||e->kind==EX_POST)&&!v->type.pointers&&
           (v->type.base==TY_INT||v->type.base==TY_LONG)&&facts->value[body_symbol(v)]){
            known=body_clone(facts->value[body_symbol(v)]);operation=e->op==TOK_INC?'+':'-';
            amount=body_literal(type(TY_INT,0),1,e->location);
        }else if((e->kind==EX_PRE||e->kind==EX_POST)&&e->op==TOK_INC&&v->owner&&
                 far_pointer(v->type)&&width(pointed_type(value_type(v->type)))==1&&body_literal_string_advance(old)){
            known=body_clone(old);amount=body_literal(type(TY_INT,0),1,e->location);
        }else if(e->kind==EX_ASSIGN&&(e->op=='+'||e->op=='-')&&!v->type.pointers&&v->type.base==TY_INT&&
                 e->right->kind==EX_INT&&facts->value[body_symbol(v)]&&
                 same_type(common_type(v->type,e->right->type),promoted(v->type))){
            known=body_clone(facts->value[body_symbol(v)]);operation=e->op;amount=body_clone(e->right);
        }else if(e->kind==EX_ASSIGN&&e->op=='+'&&v->owner&&
                 old&&old->kind==EX_CAST&&body_literal_function_add(old,e->right)){
            known=body_clone(old);amount=body_clone(e->right);
        }else if(e->kind==EX_ASSIGN&&(basic_integer_op(e->op)||e->op=='*'||e->op=='/'||e->op=='%')&&
                 !v->type.is_bool&&old&&wide_integer_literal(old)&&wide_integer_literal(e->right)&&
                 same_type(common_type(v->type,e->right->type),promoted(v->type))){
            known=body_clone(old);operation=e->op;amount=body_clone(e->right);
        }else if(e->kind==EX_ASSIGN&&(e->op==TOK_SHL||e->op==TOK_SHR)&&
                 !v->type.pointers&&!v->type.is_bool&&(v->type.base==TY_CHAR||v->type.base==TY_INT||
                  v->type.base==TY_LONG||v->type.base==TY_LONGLONG)&&
                 wide_integer_literal(e->right)&&facts->value[body_symbol(v)]&&
                 wide_integer_literal(facts->value[body_symbol(v)])){
            known=body_clone(facts->value[body_symbol(v)]);operation=e->op;amount=body_clone(e->right);
        }else if(e->kind==EX_ASSIGN&&!v->type.pointers&&v->type.base==TY_FLOAT&&
                 (e->op=='+'||e->op=='-'||e->op=='*'||e->op=='/')&&
                 body_exact_binary32_update(e->op,facts->value[body_symbol(v)],e->right)){
            known=body_clone(facts->value[body_symbol(v)]);operation=e->op;amount=body_clone(e->right);
        }else if(e->kind==EX_ASSIGN&&(e->op=='+'||e->op=='-')&&v->type.pointers&&!far_pointer(v->type)&&
                 e->right->kind==EX_INT&&facts->value[body_symbol(v)]){
            known=body_clone(facts->value[body_symbol(v)]);operation=e->op;amount=body_clone(e->right);
        }
        if(e->kind==EX_ASSIGN&&!e->op&&!v->type.pointers&&v->type.base==TY_LONGLONG&&
           facts->value[body_symbol(v)]&&!body_mutating(e->right))
            body_replace(&e->right,facts,0);
    }
    body_kill_expr(facts,e);body_replace(at,facts,0);e=*at;
    if(known){
        if(v->type.pointers&&known->kind==EX_BINARY&&known->op=='+'&&known->right->kind==EX_INT){
            uint32_t k=known->right->value,a=amount->value;
            known->right->value=(operation=='+'?k+a:k-a)&0xFFFF;
            facts->value[body_symbol(v)]=known;
            free_expression(amount);
        }else{
            Expr *sum=new_expr(EX_BINARY,e->location,v->type.pointers?v->type:promoted(v->type));
            sum->op=operation;sum->left=known;sum->right=amount;
            scalar_refold_expr(sum);
            if(sum->kind==EX_INT&&v->type.base==TY_CHAR)sum=convert(sum,unqualified_value(v->type));
            if(sum->kind==EX_INT||(v->owner&&sum->kind==EX_BINARY&&v->type.base!=TY_FLOAT&&
                                 (operation=='+'||operation=='-'))){
                facts->value[body_symbol(v)]=sum;
                uint32_t addend;
                if(v->owner&&(sum->kind==EX_INT||function_address_relocation(sum,&addend)||
                              (far_pointer(v->type)&&scalar_string_offset(sum,&addend)))&&
                   (e->kind==EX_ASSIGN||e->kind==EX_PRE||(discarded&&e->kind==EX_POST))){
                    free_expression(e->right);e->kind=EX_ASSIGN;e->op=0;e->right=body_clone(sum);
                }
            }else free_expression(sum);
        }
    }else if(v&&e->kind==EX_ASSIGN&&!e->op){
        Expr *source=e->right,*value;
        int memset_result=0;
        if(v->type.pointers&&!far_pointer(v->type)){
            Expr *call=source;
            unsigned offset;
            if(call->kind==EX_CAST&&call->left->type.pointers&&
               !far_pointer(call->left->type))call=call->left;
            Expr *destination=memset_destination(call);
            if(destination&&body_repeatable_address(destination)&&
               (near_object_address(destination,&offset)||!body_mutating(call))){
                source=destination;memset_result=1;
            }
        }
        if((!memset_result&&!body_fact_value(source))||loop_mentions(source,v))return;
        value=body_clone(source);
        if(!same_type(unqualified_value(v->type),unqualified_value(value->type))){
            Expr *cast=new_expr(EX_CAST,e->location,v->type);cast->left=value;value=cast;scalar_refold_expr(value);
        }
        if(memset_result||body_fact_value(value))facts->value[body_symbol(v)]=value;else free_expression(value);
    }
}
static int body_value_returns(Statement *s)
{
    for (; s; s = s->next) {
        if ((s->kind == ST_RETURN && s->expression) || body_value_returns(s->body) ||
            body_value_returns(s->alternate) || body_value_returns(s->initial)) {
            return 1;
        }
    }
    return 0;
}
static Statement *body_single(Statement *s)
{
    while (s && s->kind == ST_BLOCK && !s->next) {
        s = s->body;
    }
    return s;
}
static int body_step_direction(Expr *e,Symbol *v)
{
    uint32_t n;
    if(!e||!e->left||e->left->kind!=EX_OBJECT||e->left->symbol!=v)return 0;
    if(e->kind==EX_POST||e->kind==EX_PRE)return e->op==TOK_INC?1:-1;
    if(e->kind==EX_ASSIGN&&(e->op=='+'||e->op=='-')&&integer_constant(e->right,&n)&&n==1&&
       same_type(common_type(v->type,e->right->type),promoted(v->type)))return e->op=='+'?1:-1;
    return 0;
}
static int body_unit_step(Expr *e,Symbol *v){return body_step_direction(e,v)==1;}
static int body_signed_affine(Expr *e,Symbol **base,int *offset)
{
    if(e->type.base!=TY_INT||e->type.pointers||e->type.is_unsigned)return 0;
    if(e->kind==EX_OBJECT){*base=e->symbol;*offset=0;return 1;}
    if(e->kind==EX_CAST&&same_type(unqualified_value(e->type),unqualified_value(e->left->type)))
        return body_signed_affine(e->left,base,offset);
    if(e->kind==EX_BINARY&&(e->op=='+'||e->op=='-')&&e->right->kind==EX_INT&&
       same_type(common_type(e->left->type,e->right->type),type(TY_INT,0))&&
       body_signed_affine(e->left,base,offset)){
        int delta=(int)(int16_t)e->right->value;
        *offset+=e->op=='+'?delta:-delta;
        /* A defined signed-word result can differ from its root by at most
         * 65535. Keep the mathematical offset: reducing it modulo 16 bits
         * could mistake a backwards/zero-trip range for a short forward one. */
        return *offset>=-65535&&*offset<=65535;
    }return 0;
}
/* A finite exit from a single guarded progress step is equivalent to retrying
 * the predicate, then running the guarded actions once. Counter and bound are
 * private signed words, with a proven true entry and a nonoverflowing exit. */
static int body_retry_loop(Statement *s,BodyFacts *facts)
{
    Expr *c=s->expression,*entry;Statement *guard,*a;Symbol *v;uint32_t limit,start;int steps=0;
    if(s->kind!=ST_WHILE||!c||c->kind!=EX_BINARY||(c->op!='<'&&c->op!=TOK_LE)||
       c->left->kind!=EX_OBJECT||!integer_constant(c->right,&limit))return 0;
    v=c->left->symbol;entry=facts->value[body_symbol(v)];
    if(!body_private(v)||v->type.pointers||v->type.base!=TY_INT||v->type.is_unsigned||
       !same_type(common_type(c->left->type,c->right->type),type(TY_INT,0))||!entry||!integer_constant(entry,&start))return 0;
    if(c->op=='<')limit=(limit-1)&65535;
    if((uint16_t)start!=(uint16_t)limit||(int16_t)limit==32767)return 0;
    guard=body_single(s->body);
    if(!guard||guard->next||guard->kind!=ST_IF||guard->alternate||body_mutating(guard->expression))return 0;
    if(scalar_writes_expr(guard->expression,v))return 0;
    a=body_single(guard->body);
    for(Statement *p=a;p;p=p->next){
        if(p->kind!=ST_EXPR)return 0;
        if(scalar_writes_expr(p->expression,v)){
            if(!body_unit_step(p->expression,v)||++steps!=1)return 0;
        }
    }
    if(steps!=1)return 0;
    {BodyFacts *inside=body_copy_facts(facts);Expr *test=body_clone(guard->expression),*neg;
     /* The counter retains the entry value on every retry */
     body_replace(&test,inside,0);body_clear(inside);free(inside);
     neg=new_expr(EX_UNARY,test->location,type(TY_INT,0));neg->op='!';neg->left=test;
     free_expression(s->expression);s->expression=NULL;s->kind=ST_BLOCK;
     Statement *retry=body_statement(ST_WHILE,s->location);retry->expression=neg;
     retry->body=body_statement(ST_EMPTY,s->location);retry->next=a;s->body=retry;
     guard->body=NULL; /* ownership of the actions moved to the new block */
    }return 1;
}
static int body_flat_cost(Statement *s)
{
    int n=0;
    for(;s;s=s->next){if(s->kind==ST_BLOCK){int k=body_flat_cost(s->body);if(k<0)return -1;n+=k;}
        else if(s->kind==ST_IF){
            int yes=body_flat_cost(s->body),no=body_flat_cost(s->alternate);
            if(yes<0||no<0)return -1;
            n+=1+yes+no;
        }
        else if(s->kind==ST_EXPR)++n;
        else if(s->kind!=ST_EMPTY)return -1;
        if(n>24)return -1;
    }
    return n;
}
static int body_discarded_loads(Statement *s)
{
    int changed=0;
    for(;s;s=s->next){
        if(s->kind==ST_EXPR&&s->expression)changed|=body_discarded_load(&s->expression);
        changed|=body_discarded_loads(s->initial);
        changed|=body_discarded_loads(s->body);
        changed|=body_discarded_loads(s->alternate);
    }
    return changed;
}
static int body_has_inline_region(Statement *s)
{
    for(;s;s=s->next)if(s->inline_callee||body_has_inline_region(s->body)||body_has_inline_region(s->alternate))return 1;
    return 0;
}
static Statement *body_install_loop_actions(Statement *s,Statement *actions)
{
    Statement **entry=&s->initial;
    while(*entry)entry=&(*entry)->next;
    *entry=actions;
    free_statements(s->body);
    free_expression(s->expression);
    free_expression(s->step);
    s->kind=ST_BLOCK;
    s->body=s->initial;
    s->initial=NULL;
    s->expression=NULL;
    s->step=NULL;
    return actions;
}
static Statement *body_expand_loop(Statement *s,unsigned trips)
{
    Statement *actions=NULL,**tail=&actions;
    for(unsigned i=0;i<trips;++i){
        *tail=body_clone_statements(s->body);
        while(*tail)tail=&(*tail)->next;
        if(s->step){
            *tail=body_statement(ST_EXPR,s->location);
            (*tail)->expression=body_clone(s->step);
            tail=&(*tail)->next;
        }
    }
    return body_install_loop_actions(s,actions);
}
static void body_simulate_actions(Statement *s,BodyFacts *facts)
{
    for(;s;s=s->next){
        if(s->kind==ST_FOR||s->kind==ST_WHILE||s->kind==ST_DO){
            body_kill_statements(facts,s->initial);
            body_kill_expr(facts,s->expression);
            body_kill_expr(facts,s->step);
            body_kill_statements(facts,s->body);
            continue;
        }
        if(s->kind==ST_IF){
            /* A conditional may kill a fact, but cannot publish a store on both paths */
            body_kill_expr(facts,s->expression);
            body_kill_statements(facts,s->body);
            body_kill_statements(facts,s->alternate);
            continue;
        }
        Expr *expression=body_clone(s->expression);
        body_expr(&expression,facts,1);
        free_expression(expression);
        body_simulate_actions(s->body,facts);
    }
}
/* Separate the update from an indexed assignment in an otherwise empty
 * loop. A private subscript's old value belongs to the access, and its
 * increment belongs to the next test. */
static void body_split_indexed_step(Statement *s)
{
    Statement *body=body_single(s->body);
    Expr *store=s->step,*address,**index,*update;
    Symbol *counter;
    if(s->kind!=ST_FOR||cg.function->jump_label_count||
       (body&&(body->kind!=ST_EMPTY||body->next))||body_has_inline_region(s->body)||
       !store||store->kind!=EX_ASSIGN||store->left->kind!=EX_DEREF)return;
    address=store->left->left;
    if(address->kind!=EX_BINARY||address->op!='+'||
       !value_type(address->left->type).pointers||body_effect(address->left))return;
    index=&address->right;
    while((*index)->kind==EX_CAST&&!(*index)->type.pointers)index=&(*index)->left;
    update=*index;
    if(update->kind!=EX_POST||update->left->kind!=EX_OBJECT||
       !known_integer(update->type)||!body_private(counter=update->left->symbol)||
       loop_mentions(address->left,counter)||loop_mentions(store->right,counter)||
       !loop_mentions(s->expression,counter))return;
    *index=body_clone(update->left);
    free_statements(s->body);
    s->body=body_statement(ST_EXPR,store->location);
    s->body->expression=store;
    s->step=update;
}
static int body_single_trip_region(Statement *s)
{
    for(;s;s=s->next)switch(s->kind){
    case ST_FOR:case ST_WHILE:case ST_DO:break;
    case ST_BLOCK:case ST_IF:
        if(!body_single_trip_region(s->body)||!body_single_trip_region(s->alternate))return 0;
        break;
    case ST_EXPR:case ST_EMPTY:break;
    default:return 0;
    }
    return 1;
}
static int body_known_test(Expr *expression,BodyFacts *facts)
{
    Expr *test=body_clone(expression);
    uint32_t value=0;
    int known;
    body_replace(&test,facts,0);
    if(test->kind==EX_INT&&test->type.pointers){known=1;value=test->value;}
    else known=(known_integer(test->type)||test->type.base==TY_LONG)&&integer_constant(test,&value);
    free_expression(test);
    return known?(value!=0):-1;
}
/* Drop unreachable exits on a trial copy before removing the loop that
 * owns them. Unresolved branches and nested loops keep their own effects. */
static int body_prune_single_trip(Statement *s,BodyFacts *facts)
{
    for(;s;s=s->next){
        if(s->kind==ST_IF&&!body_effect(s->expression)){
            int test=body_known_test(s->expression,facts);
            if(test>=0){
                Statement *chosen=test?s->body:s->alternate;
                free_statements(test?s->alternate:s->body);
                free_expression(s->expression);
                s->kind=ST_BLOCK;s->expression=NULL;s->body=chosen;s->alternate=NULL;
            }
        }
        if(s->kind==ST_BLOCK){
            if(!body_prune_single_trip(s->body,facts))return 0;
        }else{
            Statement single=*s;
            single.next=NULL;
            if(!body_single_trip_region(&single))return 0;
            body_simulate_actions(&single,facts);
        }
    }
    return 1;
}
static Statement *body_expand_single_trip(Statement *s,BodyFacts *facts)
{
    if(cg.function->jump_label_count||!s->expression||body_effect(s->expression)||
       body_single_trip_region(s->body)||
       (s->kind!=ST_DO&&body_known_test(s->expression,facts)!=1))return NULL;
    BodyFacts *trial=body_copy_facts(facts);
    Statement *actions=body_clone_statements(s->body);
    int proven=body_prune_single_trip(actions,trial);
    if(proven&&s->step){
        Statement **tail=&actions;
        while(*tail)tail=&(*tail)->next;
        *tail=body_statement(ST_EXPR,s->location);
        (*tail)->expression=body_clone(s->step);
        body_simulate_actions(*tail,trial);
    }
    proven=proven&&body_known_test(s->expression,trial)==0;
    body_clear(trial);free(trial);
    if(proven)return body_install_loop_actions(s,actions);
    free_statements(actions);
    return NULL;
}
static int body_asm_statements(Statement *s);
static int body_loop_preserves_global(Statement *s,Symbol *v);
/* With an explicit initialization and no other writer, a global counter
 * also has a known short trip count. Expansion retains its original stores. */
/* A do-while always writes at least once. If the only values exposed by
 * its body are the last counter and the final increment, emit those two. */
static int body_last_do_counter(Statement *s,BodyFacts *facts)
{
    Expr *test=s->expression;
    if(s->kind!=ST_DO||!test||test->kind!=EX_BINARY||test->op!='<'||
       test->left->kind!=EX_OBJECT||test->right->kind!=EX_INT||cg.function->jump_label_count)return 0;
    Symbol *index=test->left->symbol;
    Type t=index->type;
    if(t.base!=TY_INT||t.pointers||t.is_bool||!body_private(index)||
       !same_type(common_type(t,test->right->type),promoted(t)))return 0;
    Statement *store=body_single(s->body),*step=store?store->next:NULL;
    Expr *set=plain_assignment(store);
    uint32_t first,bound;
    if(!set||!step||step->next||step->kind!=ST_EXPR||!body_unit_step(step->expression,index)||
       set->right->kind!=EX_OBJECT||set->right->symbol!=index||set->left->symbol==index||
       !known_integer(set->left->type)||volatile_expression(set->left)||
       !facts->value[body_symbol(index)]||!integer_constant(facts->value[body_symbol(index)],&first)||
       !integer_constant(test->right,&bound))return 0;
    int start=t.is_unsigned?(uint16_t)first:(int16_t)first;
    int end=t.is_unsigned?(uint16_t)bound:(int16_t)bound;
    int last=start>=end?start:end-1;
    if(last==(t.is_unsigned?65535:32767))return 0;
    free_expression(set->right);set->right=body_literal(t,(uint32_t)last,set->location);
    Expr *increment=step->expression;
    free_expression(increment->right);increment->kind=EX_ASSIGN;increment->op=0;
    increment->right=body_literal(t,(uint32_t)(last+1),increment->location);
    free_expression(s->expression);s->expression=NULL;s->kind=ST_BLOCK;
    return 1;
}
static int body_global_trips(Statement *s)
{
    Statement *initial=body_single(s->initial);
    Expr *init,*test=s->expression;
    Symbol *v;
    uint32_t start;
    int cost,delta,low,high,current;
    if(s->kind!=ST_FOR||cg.function->jump_label_count||!initial||initial->next||initial->kind!=ST_EXPR||
       !test||test->kind!=EX_BINARY||!comparison(test->op)||body_effect(test))return -1;
    init=initial->expression;
    if(!init||init->kind!=EX_ASSIGN||init->op||init->left->kind!=EX_OBJECT||!integer_constant(init->right,&start))return -1;
    v=init->left->symbol;
    if(v->owner||!known_integer(v->type)||v->type.is_bool||object_volatile(v->type)||
       !loop_mentions(test,v)||loop_escapes_expr(test,v)||!(delta=body_step_direction(s->step,v)))return -1;
    cost=body_flat_cost(s->body);
    if((cost<0&&!body_single_trip_region(s->body))||!body_loop_preserves_global(s->body,v))return -1;
    high=(1u<<(8*width(v->type)-!v->type.is_unsigned))-1;
    low=v->type.is_unsigned?0:-high-1;
    current=(int32_t)initializer_cast(start,v->type);
    for(int trips=0;trips<=4;++trips){
        Expr *probe=body_clone(test);
        Expr value={.kind=EX_INT,.type=v->type,.location=test->location,.value=(uint32_t)current};
        uint32_t truth;
        scalar_replace_expr(&probe,v,&value);
        scalar_refold_expr(probe);
        int known=integer_constant(probe,&truth);
        free_expression(probe);
        if(!known)return -1;
        if(!truth)return trips;
        if(trips&&(cg.parser->no_loop_unroll||cost<0||cost*(trips+1)>24))return -1;
        current+=delta;
        if(current<low||current>high)return -1;
    }
    return -1;
}
/* Simulate a short while loop whose only writes update private literal
 * word counters. Keep the final stores without duplicating its body. */
static Statement *body_literal_while(Statement *s,BodyFacts *facts)
{
    Symbol *homes[2];unsigned count=0;
    if(s->kind!=ST_WHILE||s->step||cg.parser->no_loop_unroll||cg.function->jump_label_count||
       !s->expression||body_effect(s->expression))return NULL;
    for(Statement *item=body_single(s->body);item;item=item->next){
        Expr *e=item->expression;
        if(count==2||item->kind!=ST_EXPR||!e||!e->left||e->left->kind!=EX_OBJECT||
           !(e->kind==EX_PRE||e->kind==EX_POST||(e->kind==EX_ASSIGN&&e->right->kind==EX_INT)))return NULL;
        Symbol *v=e->left->symbol;Expr *initial=facts->value[body_symbol(v)];
        if(!body_private(v)||!word_integer(v->type)||v->type.is_bool||!initial||initial->kind!=EX_INT)return NULL;
        homes[count++]=v;
    }
    if(!count)return NULL;
    BodyFacts *trial=body_copy_facts(facts);
    Statement *stores=NULL;
    for(unsigned trip=0;trip<=16;++trip){
        int test=body_known_test(s->expression,trial);
        if(test<0)break;
        if(!test){
            for(unsigned i=count;i;--i){
                Symbol *v=homes[i-1];
                Expr *set=new_expr(EX_ASSIGN,s->location,v->type);
                set->left=body_object(v,s->location);set->right=body_clone(trial->value[body_symbol(v)]);
                Statement *step=body_statement(ST_EXPR,s->location);
                step->expression=set;step->next=stores;stores=step;
            }
            body_install_loop_actions(s,stores);break;
        }
        body_simulate_actions(s->body,trial);
        unsigned i;
        for(i=0;i<count;++i){
            Expr *value=trial->value[body_symbol(homes[i])];
            if(!value||value->kind!=EX_INT)break;
        }
        if(i<count)break;
    }
    body_clear(trial);free(trial);return stores;
}
/* An inlined helper can hide a fixed-offset loop from the cursor pass.
 * Keep other indexed loops on the existing costed paths. */
static int body_small_guarded_trip(Statement *loop);

/* A continue at the end of one guard arm only skips the remaining
 * statements of this iteration. Make that suffix the other arm. */
static void body_guard_loop_suffix(Statement *loop)
{
    for(Statement *guard=body_single(loop->body);guard;guard=guard->next){
        if(guard->kind!=ST_IF||guard->alternate||!guard->next)continue;
        Statement *skip=body_single(guard->body);
        if(!skip||skip->next||skip->kind!=ST_CONTINUE||body_has_inline_region(guard->body))continue;
        if(!body_small_guarded_trip(loop))return;
        free_statements(guard->body);
        guard->body=body_statement(ST_EMPTY,guard->location);
        guard->alternate=guard->next;
        guard->next=NULL;
        break;
    }
}
static int body_short_trips(Statement *s,BodyFacts *facts,int budget,int allow_indirect)
{
    BodyFacts *trial;
    Statement *guard=body_single(s->body);
    int cost,trips,result,body_unused;
    if(cg.function->jump_label_count||!s->expression||body_effect(s->expression)||
       (s->expression->kind==EX_INT&&s->expression->value))return -1;
    cost=body_flat_cost(s->body);
    if(cost<0&&!body_single_trip_region(s->body))return -1;
    if(s->kind!=ST_DO){
        result=body_known_test(s->expression,facts);
        if(result<=0)return result;
    }
    body_unused=guard&&!guard->next&&guard->kind==ST_IF&&!guard->alternate&&!body_effect(guard->expression);
    trial=body_copy_facts(facts);
    for(trips=1;;++trips){
        if(body_unused&&body_known_test(guard->expression,trial)!=0)body_unused=0;
        if(trips>(body_unused?8:4)||(trips>1&&(cost<0||cg.parser->no_loop_unroll||cost*trips>budget||body_asm_statements(s->body)||
           (!allow_indirect&&scalar_indirect(s->body,1)&&!body_has_inline_region(s->body))))){
            trips=-1;
            break;
        }
        if(!body_unused)body_simulate_actions(s->body,trial);
        if(s->step){
            Expr *step=body_clone(s->step);
            body_expr(&step,trial,1);
            free_expression(step);
        }
        result=body_known_test(s->expression,trial);
        if(result<=0){
            if(result<0)trips=-1;
            break;
        }
    }
    body_clear(trial);
    free(trial);
    return trips;
}
enum { FIXED_INDEX_TRIPS=4, FIXED_STORE_TRIPS=16, FIXED_INDEX_BUDGET=256,
       FIXED_INDEX_CONTROL_BYTES=14, FIXED_SELECTION_BYTES=26 };
typedef struct {
    Symbol *index;
    BodyFacts *invariants;
    Expr values[FIXED_STORE_TRIPS];
    unsigned trips,body_bytes,address_bytes,frame_accesses,indirect_accesses;
} FixedIndexLoop;

/* Constant subscripts through an opaque near pointer still require the
 * pointer load, but no longer need induction scaling on each iteration. */
static int body_fixed_pointer_index(Expr *e)
{
    unsigned levels=0;
    while(e->kind==EX_DEREF){
        Expr *address=e->left;
        uint32_t index;
        if(address->kind==EX_OBJECT&&!address->type.array&&
           address->type.pointers&&!far_pointer(address->type)){
            e=address;++levels;continue;
        }
        if(address->kind!=EX_BINARY||address->op!='+'||
           !value_type(address->left->type).pointers||far_pointer(value_type(address->left->type))||
           !integer_constant(address->right,&index))return 0;
        e=address->left;
        ++levels;
    }
    return levels&&e->kind==EX_OBJECT&&!e->type.array&&e->type.pointers;
}

/* Estimate the duplicated instruction bytes after folding the operands. An
 * indexed access only contributes savings when every copy resolves to the
 * same named home and a valid fixed offset. Frame-relative indexing has to
 * form a base address as well as scale the index. */
static int body_indexed_cost(Expr *e,FixedIndexLoop *loop)
{
    if(!e)return 1;
    if(loop->body_bytes>FIXED_INDEX_BUDGET||e->kind==EX_CALL||e->kind==EX_ADDRESS||
       e->kind==EX_BITFIELD||(!known_integer(e->type)&&
       (e->type.pointers||e->type.array||e->type.base!=TY_LONG)))return 0;
    if(e->kind==EX_DEREF||e->kind==EX_MEMBER){
        Symbol *home=NULL;
        int indirect=0;
        unsigned offset;
        if(loop_mentions(e,loop->index)){
            for(unsigned i=0;i<loop->trips;++i){
                Expr *copy=body_clone(e);
                Symbol *candidate;
                int displaced;
                scalar_replace_expr(&copy,loop->index,&loop->values[i]);
                body_replace(&copy,loop->invariants,1);
                candidate=fixed_memory_object(copy,&offset);
                displaced=!candidate&&body_fixed_pointer_index(copy);
                free_expression(copy);
                if(displaced){if(home)return 0;indirect=1;continue;}
                if(indirect||!candidate||(home&&home!=candidate))return 0;
                home=candidate;
            }
            if(indirect){loop->body_bytes+=9;loop->address_bytes+=8;++loop->indirect_accesses;return 1;}
            loop->address_bytes+=home->owner?12:5;
            if(home->owner)++loop->frame_accesses;
        }else home=fixed_memory_object(e,&offset);
        if(!home||home->type.banked)return 0;
        loop->body_bytes+=3;
        return 1;
    }
    if((e->kind==EX_PRE||e->kind==EX_POST)&&!e->type.pointers&&
       e->type.base==TY_INT&&e->left->kind==EX_OBJECT&&body_private(e->left->symbol)){
        /* A private word update can use one load, adjustment and store */
        loop->body_bytes+=6;
        return 1;
    }
    if(e->kind!=EX_CAST)loop->body_bytes+=(e->kind==EX_INT||e->kind==EX_OBJECT)?3:4;
    return body_indexed_cost(e->left,loop)&&body_indexed_cost(e->right,loop)&&
           body_indexed_cost(e->third,loop);
}
static Expr *body_indexed_call_test(Statement *s)
{
    if(!s||s->kind!=ST_IF||s->alternate||body_has_inline_region(s->body))return NULL;
    Statement *arm=body_single(s->body);
    Expr *test=s->expression,*call=arm?arm->expression:NULL;
    if(!arm||arm->next||arm->kind!=ST_EXPR||!call||call->kind!=EX_CALL||
       !call->symbol||call->arg_count||test->kind!=EX_BINARY||
       (test->op!=TOK_EQ&&test->op!=TOK_NE)||
       !word_integer(test->left->type)||!word_integer(test->right->type))return NULL;
    return test;
}
static int body_indexed_region(Statement *s,FixedIndexLoop *loop)
{
    for(;s;s=s->next){
        if(s->inline_callee||(s->kind!=ST_BLOCK&&s->kind!=ST_IF&&
           s->kind!=ST_EXPR&&s->kind!=ST_EMPTY))return 0;
        if(s->kind==ST_IF){
            /* A one-sided word equality guard can branch over a direct call */
            Expr *test=body_indexed_call_test(s);
            if(test){
                loop->body_bytes+=6;
                if(!body_indexed_cost(test->left,loop)||!body_indexed_cost(test->right,loop))return 0;
                continue;
            }
            loop->body_bytes+=6;
        }
        if(!body_indexed_cost(s->expression,loop)||!body_indexed_region(s->body,loop)||
           !body_indexed_region(s->alternate,loop))return 0;
    }
    return 1;
}
/* Fixed frame loads avoid the cursor update on every successful check */
static int body_fixed_call_scan(Statement *s,FixedIndexLoop *loop)
{
    uint32_t literal;
    s=body_single(s);
    Expr *test=body_indexed_call_test(s);
    return test&&!s->next&&loop->frame_accesses==1&&
        (integer_constant(test->left,&literal)||integer_constant(test->right,&literal))&&
        loop->trips*loop->body_bytes<=96;
}
static int body_indexed_values(Statement *s,FixedIndexLoop *loop,uint32_t start,int delta,Expr *final)
{
    Type t=loop->index->type;
    unsigned bits=width(t)*8;
    int64_t value=t.is_unsigned?(int64_t)initializer_cast(start,t):(int32_t)initializer_cast(start,t);
    int64_t limit=(INT64_C(1)<<(bits-!t.is_unsigned))-1;
    int64_t minimum=t.is_unsigned?0:-limit-1;
    final->kind=EX_INT;
    final->type=t;
    final->location=s->location;
    for(;;){
        Expr *test=body_clone(s->expression);
        uint32_t result;
        int known;
        final->value=initializer_cast((uint32_t)value,t);
        scalar_replace_expr(&test,loop->index,final);
        scalar_refold_expr(test);
        known=integer_constant(test,&result);
        free_expression(test);
        if(!known)return 0;
        if(!result)return loop->trips>=2;
        if(loop->trips==FIXED_STORE_TRIPS||value+delta<minimum||value+delta>limit)return 0;
        loop->values[loop->trips++]=*final;
        value+=delta;
    }
}
/* Keep loop-specific control flow unless the guarded continue belongs to
 * a small for loop whose private induction takes a fixed number of steps. */
static int body_small_guarded_trip(Statement *loop)
{
    if(loop->kind!=ST_FOR||!loop->expression||body_effect(loop->expression)||contains_break(loop->body))return 0;
    Statement *initial=body_single(loop->initial);
    if(!initial||initial->next||initial->kind!=ST_EXPR)return 0;
    Expr *init=initial->expression;
    uint32_t start;
    if(!init||init->kind!=EX_ASSIGN||init->op||init->left->kind!=EX_OBJECT||
       !integer_constant(init->right,&start))return 0;
    FixedIndexLoop plan={0};
    plan.index=init->left->symbol;
    if(!body_private(plan.index)||!word_integer(plan.index->type)||plan.index->type.is_bool||
       scalar_writes(loop->body,plan.index))return 0;
    int step=body_step_direction(loop->step,plan.index);
    Expr final={0};
    return step&&body_indexed_values(loop,&plan,start,step,&final)&&plan.trips<=FIXED_INDEX_TRIPS;
}
/* A batch of small fixed stores avoids a separate frame-address calculation
 * for every destination on each trip. Bound the emitted straight-line code. */
static int body_fixed_store_values(Expr *value,FixedIndexLoop *loop)
{
    for(unsigned i=0;i<loop->trips;++i){
        Expr *copy=body_clone(value);
        scalar_replace_expr(&copy,loop->index,&loop->values[i]);
        scalar_refold_expr(copy);
        int literal=wide_integer_literal(copy);
        free_expression(copy);
        if(!literal)return 0;
    }
    return 1;
}
static int body_fixed_store_batch(Statement *s,FixedIndexLoop *loop)
{
    unsigned bytes=0;
    int wide=0;
    int static_short=!loop->frame_accesses&&!loop->indirect_accesses&&loop->address_bytes&&loop->trips<=3;
    if(loop->indirect_accesses==1&&loop->trips<=FIXED_INDEX_TRIPS){
        Statement *one=body_single(s);
        Expr *store=one&&!one->next&&one->kind==ST_EXPR?one->expression:NULL;
        if(store&&store->kind==EX_ASSIGN&&!store->op&&store->left->kind==EX_DEREF&&
           loop_mentions(store->left,loop->index)&&store->right->kind==EX_BINARY&&
           (store->right->op=='/'||store->right->op=='%'||store->right->op=='*')){
            return body_fixed_store_values(store->right,loop);
        }
    }
    if(!loop->frame_accesses&&!static_short)return 0;
    s=body_single(s);
    if(static_short&&s&&s->kind==ST_IF&&!s->next&&!s->alternate&&!body_effect(s->expression)){
        BodyFacts values={0};
        for(unsigned i=0;i<loop->trips;++i){
            values.value[body_symbol(loop->index)]=&loop->values[i];
            if(body_known_test(s->expression,&values)<0)return 0;
        }
        s=body_single(s->body);
    }
    for(;s;s=s->next){
        Expr *store=s->expression,*value;
        unsigned size;
        if(s->kind!=ST_EXPR||!store||store->kind!=EX_ASSIGN||store->op||
           store->left->kind!=EX_DEREF)return 0;
        Type t=store->left->type;
        if(!known_integer(t)&&(t.pointers||t.array||t.base!=TY_LONG))return 0;
        value=store->right;
        while(value->kind==EX_CAST&&!value->type.pointers&&
              (known_integer(value->type)||value->type.base==TY_LONG))value=value->left;
        if(value->kind!=EX_INT&&(value->kind!=EX_OBJECT||value->symbol!=loop->index)&&
           !(static_short&&value->kind==EX_BINARY&&body_fixed_store_values(value,loop)))return 0;
        size=width(t);
        wide|=size==4;
        bytes+=size==4?12:size==1?10:6;
    }
    if(static_short)return bytes*(loop->trips-1)<=FIXED_INDEX_CONTROL_BYTES;
    return (wide||loop->frame_accesses>=2)&&bytes*loop->trips<=FIXED_INDEX_BUDGET;
}
/* Fixed offsets remove both the scan induction and the dynamic index capture */
static int body_fixed_selection_batch(Statement *s,FixedIndexLoop *loop)
{
    Expr *test,*best,*value,*update,*select;
    Statement *arm;
    s=body_single(s);
    if(s&&!s->next&&s->kind==ST_EXPR&&loop->trips==2&&loop->address_bytes){
        Expr *store=s->expression;
        if(store&&store->kind==EX_ASSIGN&&!store->op&&store->left->kind==EX_OBJECT&&
           word_integer(store->left->type)&&store->right->kind==EX_CHOOSE){
            Expr *choice=store->right,*condition=choice->left;
            return condition->kind==EX_BINARY&&comparison(condition->op)&&
                   condition->op!=TOK_EQ&&condition->op!=TOK_NE&&
                   (body_equal(choice->right,store->left)||body_equal(choice->third,store->left))&&
                   loop->body_bytes*loop->trips<=FIXED_INDEX_BUDGET;
        }
    }
    if(!s||s->next||s->kind!=ST_IF||s->alternate||!(test=s->expression)||
       test->kind!=EX_BINARY||!comparison(test->op)||test->op==TOK_EQ||test->op==TOK_NE)return 0;
    best=test->left;value=test->right;
    if(best->kind!=EX_OBJECT){best=test->right;value=test->left;}
    if(best->kind!=EX_OBJECT||!word_integer(best->type)||!body_private(best->symbol)||
       value->kind!=EX_DEREF||!word_integer(value->type)||!loop_mentions(value,loop->index)||
       loop->frame_accesses||loop->indirect_accesses)return 0;
    arm=body_single(s->body);
    if(!arm||!arm->next||arm->next->next||arm->kind!=ST_EXPR||arm->next->kind!=ST_EXPR)return 0;
    update=arm->expression;select=arm->next->expression;
    if(update&&update->kind==EX_ASSIGN&&!body_equal(update->left,best)){
        Expr *swap=update;update=select;select=swap;
    }
    return update&&update->kind==EX_ASSIGN&&!update->op&&body_equal(update->left,best)&&
       body_equal(update->right,value)&&select&&select->kind==EX_ASSIGN&&!select->op&&
       select->left->kind==EX_OBJECT&&word_integer(select->left->type)&&
       body_private(select->left->symbol)&&select->left->symbol!=best->symbol&&
       select->right->kind==EX_OBJECT&&select->right->symbol==loop->index&&
       FIXED_SELECTION_BYTES*(loop->trips-1)<=FIXED_INDEX_BUDGET;
}
/* Favor fixed-offset copies when several frame accesses would otherwise
 * rebuild addresses. Leave inexpensive counted and cursor loops to the
 * backend. The index is private, so only its final value can escape the loop. */
static Statement *body_expand_fixed_indices(Statement *s,BodyFacts *facts)
{
    FixedIndexLoop loop={0};
    Expr final={0},*init;
    Statement *initial,*actions=NULL,**tail=&actions;
    uint32_t start;
    int delta,profitable;
    Statement selection=*s;
    int pre=s->expression&&s->expression->kind==EX_PRE&&s->expression->op==TOK_DEC&&!s->step;
    if(cg.parser->no_loop_unroll||cg.parser->no_indexed_operands||cg.function->jump_label_count||
       s->kind!=ST_FOR||!s->expression||(!pre&&body_effect(s->expression))||!scalar_indirect(s->body,0))return NULL;
    initial=body_single(s->initial);
    if(!initial||initial->next||initial->kind!=ST_EXPR)return NULL;
    init=initial->expression;
    if(!init||init->kind!=EX_ASSIGN||init->op||init->left->kind!=EX_OBJECT)return NULL;
    loop.index=init->left->symbol;
    if(loop.index->type.is_bool||!body_fact_home(loop.index)||
       (!known_integer(loop.index->type)&&loop.index->type.base!=TY_LONG)||
       !facts->value[body_symbol(loop.index)]||
       !integer_constant(facts->value[body_symbol(loop.index)],&start)||scalar_writes(s->body,loop.index)||
       volatile_statements(s->body))return NULL;
    if(pre){
        if(!start||start>FIXED_INDEX_TRIPS+1||!body_equal(s->expression->left,init->left))return NULL;
        --start;delta=-1;selection.expression=s->expression->left;
    }else if(!(delta=body_step_direction(s->step,loop.index)))return NULL;
    if(!body_indexed_values(&selection,&loop,start,delta,&final))return NULL;
    loop.invariants=body_copy_facts(facts);
    body_kill_statements(loop.invariants,s->body);
    profitable=body_indexed_region(s->body,&loop);
    body_clear(loop.invariants);free(loop.invariants);
    unsigned control_bytes=FIXED_INDEX_CONTROL_BYTES+(width(loop.index->type)==4?18:0);
    if(!profitable)return NULL;
    if((loop.trips>FIXED_INDEX_TRIPS||
        (loop.frame_accesses<(width(loop.index->type)==4||loop.trips<=3?1u:2u)&&loop.indirect_accesses<2)||
        loop.trips*loop.body_bytes>FIXED_INDEX_BUDGET||
        loop.trips*loop.body_bytes>loop.body_bytes+loop.address_bytes+control_bytes)&&
       !body_fixed_store_batch(s->body,&loop)&&!body_fixed_selection_batch(s->body,&loop)&&
       !body_fixed_call_scan(s->body,&loop))return NULL;
    for(unsigned i=0;i<loop.trips;++i){
        *tail=body_clone_statements(s->body);
        scalar_replace(*tail,loop.index,&loop.values[i]);
        scalar_refold(*tail);
        while(*tail)tail=&(*tail)->next;
    }
    if(loop_observed_outside(cg.function->body,s,loop.index)){
        Expr *store=new_expr(EX_ASSIGN,s->location,loop.index->type);
        store->left=body_object(loop.index,s->location);
        store->right=body_clone(&final);
        *tail=body_statement(ST_EXPR,s->location);
        (*tail)->expression=store;
    }
    return body_install_loop_actions(s,actions);
}
/* Word-affine trip counts relative to a stable private start. Unsigned loops
 * need overflow guards and are left to the existing counted/unroll selector. */
static int body_relative_unroll(Statement *s)
{
    Statement *init;Expr *a,*c=s->expression;Symbol *v,*left=NULL,*right=NULL;int lo,hi,span,cost;
    if(cg.parser->no_loop_unroll||s->kind!=ST_FOR||!c||c->kind!=EX_BINARY||
       (c->op!='<'&&c->op!=TOK_LE)||c->left->kind!=EX_OBJECT)return 0;
    v=c->left->symbol;init=body_single(s->initial);
    if(!body_private(v)||v->type.base!=TY_INT||v->type.pointers||v->type.is_unsigned||
       common_type(c->left->type,c->right->type).is_unsigned||!body_unit_step(s->step,v)||
       !init||init->next||init->kind!=ST_EXPR)return 0;
    a=init->expression;
    if(a->kind!=EX_ASSIGN||a->op||a->left->kind!=EX_OBJECT||a->left->symbol!=v||
       !body_signed_affine(a->right,&left,&lo)||!body_signed_affine(c->right,&right,&hi)||left!=right||
       left==v||!body_private(left)||left->type.is_unsigned||!same_type(promoted(left->type),promoted(v->type))||
       scalar_writes(s->body,left)||scalar_writes(s->body,v))return 0;
    span=hi-lo+(c->op==TOK_LE);
    if(span<=0||span>4)return 0;
    cost=body_flat_cost(s->body);
    if(cost<1||cost*span>24||(span>1&&body_has_inline_region(s->body)))return 0;
    body_expand_loop(s,(unsigned)span);
    return 1;
}
/* A private byte bound is stable across arbitrary C calls when it does not
 * escape. If the body never reads/writes the index and has no exits, count
 * down instead, then restore the source loop's final index. No unsigned
 * full-word bound or wraparound loop is changed. */
static int body_action_loop(Statement *s,Symbol *index,Symbol *bound)
{
    for(;s;s=s->next){if(s->kind==ST_BLOCK){if(!body_action_loop(s->body,index,bound))return 0;}
        else if(s->kind==ST_EXPR){if(loop_mentions(s->expression,index)||(bound&&scalar_writes_expr(s->expression,bound)))return 0;}
        else if(s->kind!=ST_EMPTY)return 0;
    }return 1;
}
static int body_byte_countdown(Statement *s)
{
    Expr *c=s->expression,*init,*bound,*root;Statement *first,*loop,*after,*next;Symbol *v,*b=NULL;uint32_t n;
    if(s->kind!=ST_FOR||!c||c->kind!=EX_BINARY||c->op!='<'||c->left->kind!=EX_OBJECT)return 0;
    v=c->left->symbol;first=body_single(s->initial);
    if(!body_private(v)||v->type.base!=TY_INT||v->type.pointers||!first||first->next||first->kind!=ST_EXPR||!body_unit_step(s->step,v))return 0;
    init=first->expression;
    if(init->kind!=EX_ASSIGN||init->op||init->left->kind!=EX_OBJECT||init->left->symbol!=v||!integer_constant(init->right,&n)||n)return 0;
    root=c->right;while(root->kind==EX_CAST&&reg_width(root->type)==2)root=root->left;
    if(root->kind==EX_OBJECT&&root->type.base==TY_CHAR&&root->type.is_unsigned&&!root->type.pointers&&body_private(root->symbol))b=root->symbol;
    else return 0; /* constant bounds belong to the existing unroller */
    if(!body_action_loop(s->body,v,b))return 0;
    bound=body_clone(c->right);free_expression(init->right);init->right=convert(body_clone(bound),v->type);
    free_expression(s->expression);s->expression=new_expr(EX_BINARY,s->location,type(TY_INT,0));s->expression->op='>';
    s->expression->left=body_object(v,s->location);s->expression->right=body_literal(v->type,0,s->location);
    free_expression(s->step);s->step=new_expr(EX_POST,s->location,v->type);s->step->op=TOK_DEC;s->step->left=body_object(v,s->location);
    after=body_statement(ST_EXPR,s->location);after->expression=new_expr(EX_ASSIGN,s->location,v->type);
    after->expression->left=body_object(v,s->location);after->expression->right=convert(bound,v->type);
    loop=body_statement(ST_FOR,s->location);*loop=*s;loop->next=after;next=s->next;
    memset(s,0,sizeof *s);s->kind=ST_BLOCK;s->location=loop->location;s->body=loop;s->next=next;return 1;
}
/* A dead pointer update leaves only the load through the old address */
static void body_switch_post_load(Statement *s,BodyFacts *facts)
{
    Expr *load=s->expression,*update,*base,probe,zero,indexed;
    Symbol *v,*object;
    unsigned offset;
    int in,out;
    while(load->kind==EX_CAST&&!load->type.pointers&&known_integer(load->type))load=load->left;
    if(load->kind!=EX_DEREF||load->type.array||volatile_expression(load)||
       (update=load->left)->kind!=EX_POST||update->left->kind!=EX_OBJECT)return;
    v=update->left->symbol;
    if(!v->offset||!v->type.pointers||far_pointer(v->type)||!body_private(v)||
       cg.function->jump_label_count||statement_references(s->body,v)||
       body_asm_statements(cg.function->body))return;
    base=facts->value[body_symbol(v)];
    if(!base)return;
    probe=*load;
    probe.left=base;
    object=fixed_memory_object(&probe,&offset);
    if(!object){
        /* Represent array decay as a fixed subscript */
        zero=(Expr){.kind=EX_INT,.type=type(TY_INT,0),.location=load->location};
        indexed=(Expr){.kind=EX_BINARY,.type=v->type,.location=load->location,
                       .op='+',.left=base,.right=&zero};
        probe.left=&indexed;
        object=fixed_memory_object(&probe,&offset);
    }
    if(!object||object->type.banked)return;
    region_home_liveness(cg.function,s,v->offset,&in,&out);
    if(out)return;
    free_expression(update);
    load->left=body_clone(probe.left);
}
/* Give the normal fact pass a separate definition when the subscript writes
 * a private index that neither the array base nor the RHS can observe. */
static void body_split_index_store(Statement *s,BodyFacts *facts)
{
    Expr *store=s->expression,*address,*index;
    Symbol *home;
    Statement *write;
    uint32_t value;
    if(!store||store->kind!=EX_ASSIGN||store->left->kind!=EX_DEREF)return;
    address=store->left->left;
    if(address->kind!=EX_BINARY||address->op!='+'||!value_type(address->left->type).pointers)return;
    index=address->right;
    if((index->kind!=EX_ASSIGN&&index->kind!=EX_PRE&&index->kind!=EX_POST)||
       index->left->kind!=EX_OBJECT||!known_integer(index->type))return;
    home=index->left->symbol;
    if(!body_private(home)||loop_mentions(address->left,home)||loop_mentions(store->right,home))return;
    if(index->kind==EX_ASSIGN){
        if(index->op||index->right->kind!=EX_INT||!integer_constant(index->right,&value))return;
    }else{
        Expr *known=facts->value[body_symbol(home)];
        uint32_t updated;
        if(!known||!integer_constant(known,&value))return;
        updated=index->op==TOK_INC?value+1:value-1;
        if(index->kind==EX_PRE)value=updated;
        index->kind=EX_ASSIGN;index->op=0;
        index->right=body_literal(index->type,updated,index->location);
    }
    address->right=body_literal(index->type,value,index->location);
    write=body_statement(ST_EXPR,s->location);
    write->expression=store;write->next=s->next;
    s->expression=index;s->next=write;
}
static Expr *body_pointer_access(Expr *e)
{
    while(e->kind==EX_CAST)e=e->left;
    return e->kind==EX_DEREF&&(e->left->kind==EX_PRE||e->left->kind==EX_POST)&&
           e->left->left->kind==EX_OBJECT?e:NULL;
}
/* Separate an unobserved cursor update from its access so fixed offsets
 * propagate across straight-line transfers, including volatile transfers. */
static void body_split_fixed_pointer(Statement *s,BodyFacts *facts)
{
    Expr *store=s->expression,*access,*other,*update,*base;
    Symbol *cursor;
    unsigned offset;
    uint32_t old=0;
    int next,used,delta;
    if(!store||store->kind!=EX_ASSIGN)return;
    access=body_pointer_access(store->left);other=store->right;
    if(!access){access=body_pointer_access(store->right);other=store->left;}
    int subscript=0;
    if(!access&&store->left->kind==EX_DEREF){
        Expr *address=store->left->left;
        if(address->kind==EX_BINARY&&address->op=='+'&&value_type(address->left->type).pointers){
            access=body_pointer_access(address->right);subscript=access!=NULL;
        }
    }
    if(!access)return;
    update=access->left;cursor=update->left->symbol;
    int far=far_pointer(cursor->type);
    if(!cursor->offset||!cursor->type.pointers||!body_fact_home(cursor)||
       (subscript?expression_references(store,cursor)!=1:loop_mentions(other,cursor))||
       cg.function->jump_label_count||body_asm_statements(cg.function->body))return;
    if(far&&((other!=store->left&&!subscript)||width(pointed_type(cursor->type))!=1))return;
    base=facts->value[body_symbol(cursor)];
    if(!base)return;
    if(base->kind==EX_BINARY&&base->op=='+'&&integer_constant(base->right,&old))base=base->left;
    if(old>65535)return;
    delta=update->op==TOK_INC?1:-1;
    next=(int)old+delta;used=update->kind==EX_POST?(int)old:next;
    if(used<0||next<0||next>65535)return;
    Expr index={.kind=EX_INT,.type=type(TY_INT,0),.location=update->location,.value=(uint32_t)used};
    Expr address={.kind=EX_BINARY,.type=cursor->type,.location=update->location,.op='+',.left=base,.right=&index};
    Expr probe=*access;probe.left=&address;
    index.type.is_unsigned=1;
    if(far){
        String *literal=scalar_string_offset(&address,&offset);
        if(!literal||offset>=literal->size)return;
    }else if(!fixed_memory_object(&probe,&offset))return;
    index.value=(uint32_t)next;
    if(far?!scalar_string_offset(&address,&offset):!near_object_address(&address,&offset))return;
    Statement *write=body_statement(ST_EXPR,s->location);
    write->expression=new_expr(EX_ASSIGN,update->location,cursor->type);
    write->expression->left=body_object(cursor,update->location);
    write->expression->right=body_clone(&address);
    index.value=(uint32_t)used;
    access->left=body_clone(&address);free_expression(update);
    write->next=s->next;s->next=write;
}
/* A static callback may be changed by other calls. Only forward a direct
 * assignment into the next expression when it cannot run another effect first. */
static void body_adjacent_callback(Statement *s)
{
    Expr *assignment=s->expression,*call;
    Symbol *pointer;
    Statement *next=s->next;
    if(!assignment||assignment->kind!=EX_ASSIGN||assignment->op||
       assignment->left->kind!=EX_OBJECT||!next||
       (next->kind!=ST_IF&&next->kind!=ST_RETURN&&next->kind!=ST_EXPR))return;
    pointer=assignment->left->symbol;
    if(pointer->owner||!pointer->internal||!function_pointer(pointer->type)||
       object_volatile(pointer->type)||cg.function->jump_label_count)return;
    call=next->expression;
    while(call&&call->kind!=EX_CALL){
        if(call->kind==EX_CAST||call->kind==EX_UNARY)call=call->left;
        else if(call->kind==EX_BINARY&&!body_effect(call->left))call=call->right;
        else if(call->kind==EX_BINARY&&!body_effect(call->right))call=call->left;
        else if(call->kind==EX_ASSIGN&&!call->op&&!body_effect(call->left))call=call->right;
        else return;
    }
    if(!call||!call->left||call->left->kind!=EX_OBJECT||call->left->symbol!=pointer)return;
    for(unsigned i=0;i<call->arg_count;++i)if(body_effect(call->args[i]))return;
    body_direct_callback(call,assignment->right);
}
/* A signed word initialized nonnegative stays nonnegative when its sole
 * loop write shifts it right. This includes a shift used as a subscript. */
static void body_logical_loop_shift(Expr *e,Statement *loop,BodyFacts *entry)
{
    if(!e)return;
    if(e->kind==EX_ASSIGN&&e->op==TOK_SHR&&e->left->kind==EX_OBJECT&&
       word_integer(e->type)&&!e->type.is_unsigned){
        Symbol *v=e->left->symbol;
        Expr *initial=entry->value[body_symbol(v)];
        uint32_t start,count;
        if(initial&&body_private(v)&&integer_constant(initial,&start)&&start<=32767&&
           integer_constant(e->right,&count)&&count>0&&count<16&&
           scalar_writes(loop->body,v)==1&&!scalar_writes_expr(loop->step,v)&&
           !scalar_writes_expr(loop->expression,v)){
            Type word=type(TY_INT,0);
            Expr *shift;
            word.is_unsigned=1;
            shift=new_expr(EX_BINARY,e->location,word);
            shift->op=TOK_SHR;
            shift->left=convert(body_clone(e->left),word);
            shift->right=e->right;
            e->op=0;e->right=convert(shift,e->type);
            return;
        }
    }
    body_logical_loop_shift(e->left,loop,entry);
    body_logical_loop_shift(e->right,loop,entry);
    body_logical_loop_shift(e->third,loop,entry);
    for(unsigned i=0;i<e->arg_count;++i)body_logical_loop_shift(e->args[i],loop,entry);
}
static void body_logical_loop_shifts(Statement *s,Statement *loop,BodyFacts *entry)
{
    for(;s;s=s->next){
        body_logical_loop_shift(s->expression,loop,entry);
        body_logical_loop_shifts(s->body,loop,entry);
        body_logical_loop_shifts(s->alternate,loop,entry);
    }
}

/* Forward the old value of a known post-update into its enclosing use.
 * Resolve a pure conditional first and keep the selected write in sequence. */
static void body_split_post_value(Statement *s,BodyFacts *facts,int shared)
{
    Expr *e=s->expression,**value=NULL,*choice=NULL,*test,*update,*old;
    Symbol *home;
    Statement *use;
    int taken=0;
    if(!e||cg.parser->no_known_values||cg.function->uses_wide||cg.function->jump_label_count)return;
    if(s->kind==ST_IF&&e->kind==EX_BINARY&&comparison(e->op)){
        if(e->right->kind==EX_INT)value=&e->left;
        else if(e->left->kind==EX_INT)value=&e->right;
    }else if(s->kind==ST_EXPR&&e->kind==EX_ASSIGN&&!e->op&&e->left->kind==EX_OBJECT){
        value=&e->right;
    }
    if(!value||!word_integer((*value)->type))return;
    update=*value;
    if(update->kind==EX_CHOOSE){
        choice=update;
        if(!literal_integer_tree(choice->left))return;
        test=body_clone(choice->left);
        body_replace(&test,facts,0);
        taken=scalar_literal_truth(test);
        free_expression(test);
        if(taken<0)return;
        update=taken?choice->right:choice->third;
    }
    if(update->kind!=EX_POST||update->left->kind!=EX_OBJECT||
       !same_type(unqualified_value(update->type),unqualified_value((*value)->type)))return;
    home=update->left->symbol;
    old=facts->value[body_symbol(home)];
    if(!old||old->kind!=EX_INT||
       (!body_private(home)&&(!shared||home->owner||object_volatile(home->type))))return;
    *value=body_clone(old);
    if(choice){
        if(taken)choice->right=NULL;else choice->third=NULL;
        free_expression(choice);
    }
    use=allocate(sizeof *use);*use=*s;
    s->kind=ST_EXPR;s->expression=update;s->body=s->alternate=NULL;s->next=use;s->inline_callee=NULL;
}
/* The stored integer is the value of a plain assignment. Keep its write in
 * sequence and let ordinary condition folding handle the literal result. */
static void body_split_literal_condition(Statement *s)
{
    Expr **value=&s->expression,*store;
    Statement *test;
    unsigned negate=0;
    if(s->kind!=ST_IF||cg.function->jump_label_count)return;
    while(*value&&(*value)->kind==EX_UNARY&&(*value)->op=='!'){negate^=1;value=&(*value)->left;}
    store=*value;
    if(!store||store->kind!=EX_ASSIGN||store->op||store->left->kind!=EX_OBJECT||
       !store->right||!wide_integer_literal(store->right)||
       !same_type(unqualified_value(store->type),unqualified_value(store->right->type)))return;
    *value=NULL;free_expression(s->expression);
    s->expression=body_literal(type(TY_INT,0),scalar_literal_truth(store->right)^negate,store->location);
    test=allocate(sizeof *test);*test=*s;
    s->kind=ST_EXPR;s->expression=store;s->body=s->alternate=NULL;
    s->next=test;s->inline_callee=NULL;
}
static void body_split_update_value(Statement *s,BodyFacts *facts)
{
    Expr *e=s->expression,*update,**value=NULL;
    if(!e||cg.function->uses_wide)return;
    if(e->kind==EX_ASSIGN&&!e->op&&numeric(e->type)&&e->left->kind==EX_OBJECT)value=&e->right;
    if(e->kind==EX_CALL&&!e->left&&e->symbol){
        for(unsigned i=0;i<e->arg_count;++i){
            if(e->args[i]->kind==EX_INT)continue;
            if(value||e->args[i]->kind!=EX_ASSIGN)return;
            value=&e->args[i];
        }
    }
    if(!value||(update=*value)->kind!=EX_ASSIGN||update->left->kind!=EX_OBJECT||
       !body_fact_home(update->left->symbol)||body_effect(update->right))return;
    body_expr(value,facts,0);
    update=*value;
    if(update->kind!=EX_ASSIGN||update->op||!wide_integer_literal(update->right)||
       !same_type(unqualified_value(update->type),unqualified_value(update->right->type)))return;
    *value=body_clone(update->right);
    if(e->kind==EX_CALL)body_fold_literal_arguments(e,1);
    Statement *result=body_statement(ST_EXPR,s->location);
    result->expression=e;result->next=s->next;
    s->expression=update;s->next=result;
}
static void body_forward_fixed_load(Expr **at,Symbol *home,unsigned offset,Expr *value)
{
    Expr *e=*at;
    unsigned from;
    if(!e||e->kind==EX_ADDRESS)return;
    if((e->kind==EX_MEMBER||e->kind==EX_DEREF)&&fixed_memory_object(e,&from)==home){
        if(from==offset&&same_type(unqualified_value(e->type),unqualified_value(value->type))){
            *at=body_clone(value);free_expression(e);return;
        }
        unsigned written=width(value->type),read=width(e->type);
        if(wide_integer_literal(value)&&known_integer(e->type)&&!e->type.is_bool&&
           !volatile_expression(e)&&written<=4&&read&&read<written&&from>=offset&&from-offset<=written-read){
            /* Extract the covered little-endian bytes in the read's signedness */
            *at=body_literal(e->type,value->value>>(8*(from-offset)),e->location);
            free_expression(e);return;
        }
    }
    body_forward_fixed_load(&e->left,home,offset,value);
    body_forward_fixed_load(&e->right,home,offset,value);
    body_forward_fixed_load(&e->third,home,offset,value);
}
static void body_adjacent_fixed_value(Statement *s,BodyFacts *facts)
{
    Expr *store=s->expression;
    Statement *next=s->next;
    unsigned offset,string_offset;
    if(!next||!store||store->kind!=EX_ASSIGN||store->op||
       (store->left->kind!=EX_MEMBER&&store->left->kind!=EX_DEREF)||
       (!(store->right->kind==EX_INT&&numeric(store->right->type))&&
        !scalar_string_offset(store->right,&string_offset))||
       !same_type(unqualified_value(store->left->type),unqualified_value(store->right->type))||
       volatile_expression(store))return;
    Symbol *home=fixed_memory_object(store->left,&offset);
    unsigned width_stored=width(store->left->type);
    if(!home)return;
    BodyFacts empty={0};
    int crossed_store=0;
    for(unsigned budget=0;next&&budget<8;++budget,next=next->next){
        Expr **use,*assignment;
        Symbol *other=NULL;
        unsigned address=0,bytes=0;
        if(next->kind==ST_EMPTY)continue;
        while(next->kind==ST_BLOCK&&next->body)next=next->body;
        assignment=next->expression;
        if(next->kind==ST_EXPR&&assignment&&assignment->kind==EX_ASSIGN&&!assignment->op&&
           !body_effect(assignment->left)&&!volatile_expression(assignment->left)){
            use=&assignment->right;
            other=fixed_memory_object(assignment->left,&address);
            bytes=width(assignment->left->type);
        }else if(next->kind==ST_RETURN||next->kind==ST_IF)use=&next->expression;
        else break;
        if(!*use||body_effect(*use))break;
        if(!crossed_store)body_replace(use,facts,0);
        body_forward_fixed_load(use,home,offset,store->right);
        body_replace(use,&empty,0);
        if(!other||(other==home&&address<offset+width_stored&&offset<address+bytes))break;
        crossed_store=1;
    }
}
static void body_global_predicate(Statement *s);
static Statement *body_fold_counted_stores(Statement *s,BodyFacts *facts);
/* An unsigned unit step reaches zero by wraparound from any nonzero
 * value. A repeated, independent scalar assignment has one effect. */
static void body_fold_invariant_wrap(Statement *s)
{
    Expr *index=s->expression,*step=s->step,*assignment;
    Statement *body,*finish;
    if(s->kind!=ST_FOR||s->initial||cg.function->jump_label_count||
       !index||index->kind!=EX_OBJECT||!known_integer(index->type)||
       !index->type.is_unsigned||index->type.is_bool||
       !body_step_direction(step,index->symbol)||volatile_statement(s))return;
    body=body_single(s->body);
    if(!body||body->next||body->kind!=ST_EXPR||!(assignment=body->expression)||
       assignment->kind!=EX_ASSIGN||assignment->op||assignment->left->kind!=EX_OBJECT||
       !known_integer(assignment->left->type)||assignment->left->symbol==index->symbol||
       !literal_integer_tree(assignment->right)||loop_mentions(assignment->right,index->symbol)||
       loop_mentions(assignment->right,assignment->left->symbol))return;
    finish=body_statement(ST_EXPR,s->location);
    finish->expression=new_expr(EX_ASSIGN,s->location,index->type);
    finish->expression->left=body_clone(index);
    finish->expression->right=body_literal(index->type,0,s->location);
    body->next=finish;
    free_expression(step);s->step=NULL;s->kind=ST_IF;
}
static void body_flow(Statement *s,BodyFacts *facts);
/* The second comparison of a selected minimum or maximum has one known
 * result per arm. Its bound must remain unchanged by the selected store. */
static void body_selected_bound_guard(Statement *s)
{
    Statement *guard=s->next;
    Expr *set=s->expression;
    if(s->kind!=ST_EXPR||!set||set->kind!=EX_ASSIGN||set->op||
       !guard||guard->kind!=ST_IF||guard->alternate||cg.function->jump_label_count||
       set->right->kind!=EX_CHOOSE||!word_integer(set->left->type)||volatile_expression(set))return;
    Expr *pick=set->right,*test=pick->left,*again=guard->expression;
    if(test->kind!=EX_BINARY||!again||again->kind!=EX_BINARY||
       !((test->op=='<'&&again->op==TOK_GE)||(test->op=='>'&&again->op==TOK_LE))||
       !body_equal(pick->right,test->left)||!body_equal(pick->third,test->right)||
       !body_equal(again->left,set->left)||!body_equal(again->right,test->right)||
       !same_type(unqualified_value(set->left->type),unqualified_value(test->left->type))||
       !same_type(unqualified_value(set->left->type),unqualified_value(test->right->type))||
       body_effect(pick))return;
    unsigned offset;
    Symbol *home=direct_memory_object(set->left,&offset);
    Expr *bound=test->right;
    if(bound->kind==EX_BINARY&&(bound->op=='+'||bound->op=='-')&&bound->right->kind==EX_INT)
        bound=bound->left;
    if(!home||(bound->kind!=EX_INT&&(bound->kind!=EX_OBJECT||bound->symbol==home)))return;
    Statement *yes=body_statement(ST_EXPR,s->location),*no=body_statement(ST_EXPR,s->location);
    no->expression=body_clone(set);free_expression(no->expression->right);
    no->expression->right=pick->third;
    yes->expression=set;set->right=pick->right;
    no->next=guard->body;guard->body=NULL;
    s->expression=test;s->kind=ST_IF;s->body=yes;s->alternate=body_statement(ST_BLOCK,s->location);
    s->alternate->body=no;s->next=guard->next;
    free(pick);free_expression(guard->expression);free(guard);
}
/* A discarded assignment chain to scalar homes can expose both writes
 * to ordinary propagation. The inner private object has no observable reload. */
static void body_split_chained_store(Statement *s)
{
    Expr *outer=s->expression;
    if(!outer||outer->kind!=EX_ASSIGN||outer->op||outer->left->kind!=EX_OBJECT||
       outer->right->kind!=EX_ASSIGN||outer->right->op)return;
    Expr *inner=outer->right;
    if(inner->left->kind!=EX_OBJECT||!body_private(inner->left->symbol)||
       inner->left->symbol==outer->left->symbol)return;
    Statement *next=body_statement(ST_EXPR,s->location);
    next->expression=outer;next->next=s->next;
    outer->right=body_clone(inner->left);
    s->expression=inner;s->next=next;
}
static void body_split_commas(Statement *s)
{
    while(s->expression&&s->expression->kind==EX_COMMA){
        Expr *comma=s->expression;
        Statement *right=body_statement(ST_EXPR,comma->right->location);
        right->expression=comma->right;right->next=s->next;
        s->expression=comma->left;s->next=right;free(comma);
    }
}
/* The right operand of a repeated short-circuit guard has exactly one
 * incoming path. Look up its value before discarding the per-arm facts. */
static void body_forward_guard_arm(Statement *s,Statement *next,BodyFacts *yes,BodyFacts *no)
{
    Expr *test=s->expression,*other;
    if(!next||next->kind!=ST_IF||cg.function->jump_label_count||
       !test||test->kind!=EX_BINARY||!comparison(test->op)||
       test->left->kind!=EX_OBJECT||test->right->kind!=EX_INT)return;
    Symbol *index=test->left->symbol;
    other=next->expression;
    if(!known_integer(index->type)||!known_integer(test->right->type)||!body_private(index)||!other||other->kind!=EX_BINARY||
       (other->op!=TOK_LAND&&other->op!=TOK_LOR)||!body_equal(test,other->left)||
       other->right->kind!=EX_BINARY||!comparison(other->right->op)||
       other->right->left->kind!=EX_OBJECT||other->right->right->kind!=EX_INT||
       !known_integer(other->right->left->type)||!known_integer(other->right->right->type)||body_effect(other->right)||
       scalar_writes(s->body,index)||scalar_writes(s->alternate,index)||
       body_asm_statements(cg.function->body))return;
    int value=body_known_test(other->right,other->op==TOK_LAND?yes:no);
    if(value<0)return;
    free_expression(other->right);
    other->right=body_literal(type(TY_INT,0),value,other->location);
    scalar_refold_expr(other);
}
/* A direct return leaves the false edge as the only successor */
static void body_guard_fallthrough(Statement *s,BodyFacts *facts)
{
    Statement *arm=body_single(s->body);
    Expr *test=s->expression,*object=test;
    uint32_t value=0;
    if(cg.parser->no_known_values||cg.function->jump_label_count||s->alternate||
       !arm||arm->next||arm->kind!=ST_RETURN||body_asm_statements(cg.function->body))return;
    if(test->kind==EX_BINARY&&test->op==TOK_NE&&test->right->kind==EX_INT){
        object=test->left;value=test->right->value;
        if(!same_type(unqualified_value(object->type),unqualified_value(test->right->type)))return;
    }
    if(object->kind!=EX_OBJECT||!known_integer(object->type)||!body_private(object->symbol))return;
    unsigned index=body_symbol(object->symbol);
    free_expression(facts->value[index]);
    facts->value[index]=body_literal(object->type,value,object->location);
}
/* Direct cases that all break have one predecessor each. Each arm
 * starts with the dispatch facts; no arm may seed a sibling's facts. */
static void body_independent_switch_arms(Statement *s,BodyFacts *facts)
{
    if(cg.function->jump_label_count||body_effect(s->expression)||!s->body||
       s->body->kind!=ST_BLOCK||s->body->inline_callee)return;
    for(Statement *p=s->body->body;p;p=p->next){
        if(p->kind!=ST_CASE||!p->body||p->body->next||p->body->inline_callee)return;
        if(p->body->kind==ST_BREAK)continue;
        if(p->body->kind!=ST_EXPR||!p->next||p->next->kind!=ST_BREAK)return;
        p=p->next;
    }
    for(Statement *p=s->body->body;p;p=p->next){
        if(p->body->kind==ST_BREAK)continue;
        BodyFacts *arm=body_copy_facts(facts);
        body_expr(&p->body->expression,arm,1);
        body_clear(arm);free(arm);
        p=p->next;
    }
}
static void body_return_pointer_update(Statement *s)
{
    Statement *ret=s->next;
    if(s->kind!=ST_IF||s->alternate||!ret||ret->kind!=ST_RETURN||!ret->expression||
       ret->expression->kind!=EX_OBJECT||!far_pointer(ret->expression->type)||
       cg.function->jump_label_count)return;
    Statement *arm=body_single(s->body);
    Expr *set=arm?arm->expression:NULL;
    Symbol *pointer=ret->expression->symbol;
    if(!arm||arm->next||arm->kind!=ST_EXPR||!set||set->kind!=EX_ASSIGN||
       (set->op!='+'&&set->op!='-')||set->left->kind!=EX_OBJECT||
       set->left->symbol!=pointer||!loop_private(pointer)||object_volatile(pointer->type)||
       loop_escapes(cg.function->body,pointer))return;
    set->kind=EX_BINARY;arm->kind=ST_RETURN;
}
static void body_flow_until(Statement *s,Statement *end,BodyFacts *facts,Statement *following)
{
    for(;s&&s!=end;s=s->next){
        body_fold_invariant_wrap(s);
        if(body_byte_countdown(s)){}
        if(body_relative_unroll(s)){}
        if(body_retry_loop(s,facts)){}
        body_split_post_value(s,facts,0);
        body_split_literal_condition(s);
        body_selected_bound_guard(s);
        body_return_pointer_update(s);
        switch(s->kind){
        case ST_EXPR:
            if(s->next&&s->next->kind==ST_RETURN&&s->expression&&
               s->expression->kind==EX_ASSIGN&&!s->expression->op&&
               s->expression->type.base==TY_LONGLONG&&!s->expression->type.pointers&&
               s->expression->left->kind==EX_OBJECT&&!volatile_expression(s->expression->left)&&
               body_equal(s->expression->left,s->next->expression)){
                free_expression(s->next->expression);s->next->expression=s->expression;
                s->expression=NULL;s->kind=ST_EMPTY;break;
            }
            body_split_chained_store(s);
            body_split_update_value(s,facts);
            body_split_commas(s);
            body_split_fixed_pointer(s,facts);
            body_split_index_store(s,facts);
            body_expr(&s->expression,facts,1);
            Expr *call=s->expression;
            if(call&&call->kind==EX_CALL&&!call->left&&call->symbol){
                unsigned offset;
                if(!call->arg_count)body_fold_literal_arguments(call,1);
                else for(unsigned arg=0;arg<call->arg_count;++arg)
                    if(near_object_address(call->args[arg],&offset)||null_pointer_operand(call->args[arg])){
                        body_fold_literal_arguments(call,1);
                        break;
                    }
            }
            body_adjacent_fixed_value(s,facts);
            body_global_predicate(s);
            body_adjacent_callback(s);
            break;
        case ST_RETURN:body_expr(&s->expression,facts,0);break;
        case ST_BLOCK:body_flow_until(s->body,NULL,facts,s->next&&s->next!=end?s->next:following);break;
        case ST_IF:{BodyFacts *other;
            body_expr(&s->expression,facts,0);
            if(s->expression->kind==EX_INT){
                Statement *chosen=s->expression->value?s->body:s->alternate;
                free_expression(s->expression);s->expression=NULL;s->kind=ST_BLOCK;s->body=chosen;s->alternate=NULL;
                body_flow(s->body,facts);break;
            }
            other=body_copy_facts(facts);
            body_flow(s->body,facts);body_flow(s->alternate,other);
            body_forward_guard_arm(s,s->next&&s->next!=end?s->next:following,facts,other);
            for(unsigned i=0;i<1024;++i)if(!body_equal(facts->value[i],other->value[i])){
                free_expression(facts->value[i]);facts->value[i]=NULL;}
            body_clear(other);free(other);body_guard_fallthrough(s,facts);break;}
        case ST_FOR:case ST_WHILE:case ST_DO:{BodyFacts *inside;Statement *expanded;int trips;
            int nested=body_flat_cost(s->body)<0;
            if(body_last_do_counter(s,facts)){body_flow(s->body,facts);break;}
            if(!cg.parser->no_loop_unroll&&!cg.function->jump_label_count&&
               !body_asm_statements(s->body)&&!statement_has_case(s->body))body_guard_loop_suffix(s);
            body_split_indexed_step(s);
            body_flow(s->initial,facts);
            if(!cg.parser->no_known_values&&!cg.function->jump_label_count&&!find_symbol(cg.parser,"$basic_asm"))
                body_logical_loop_shifts(s->body,s,facts);
            expanded=body_literal_while(s,facts);
            if(expanded){body_flow(expanded,facts);break;}
            expanded=body_expand_fixed_indices(s,facts);
            if(expanded){body_flow(expanded,facts);break;}
            expanded=body_expand_single_trip(s,facts);
            if(expanded){body_flow(expanded,facts);break;}
            expanded=body_fold_counted_stores(s,facts);
            if(expanded){body_flow(expanded,facts);break;}
            trips=body_global_trips(s);
            if(trips<0)trips=body_short_trips(s,facts,24,0);
            if(trips>=0){body_flow(body_expand_loop(s,(unsigned)trips),facts);break;}
            inside=body_copy_facts(facts);
            body_kill_expr(inside,s->expression);body_kill_expr(inside,s->step);body_kill_statements(inside,s->body);
            if(!cg.function->uses_wide||!body_nested_updates(s->expression))body_replace(&s->expression,inside,0);
            body_flow(s->body,inside);body_expr(&s->step,inside,1);
            body_clear(inside);free(inside);
            if(nested&&body_flat_cost(s->body)>=0&&(trips=body_short_trips(s,facts,32,0))>=0){
                body_flow(body_expand_loop(s,(unsigned)trips),facts);break;
            }
            body_kill_expr(facts,s->expression);body_kill_expr(facts,s->step);body_kill_statements(facts,s->body);
            break;}
        case ST_SWITCH:body_independent_switch_arms(s,facts);body_switch_post_load(s,facts);body_clear(facts);break;
        case ST_CASE:case ST_BREAK:case ST_CONTINUE:body_clear(facts);break;
        default:break;
        }
    }
}
static void body_flow(Statement *s,BodyFacts *facts)
{
    body_flow_until(s,NULL,facts,NULL);
}
static unsigned body_reads(Expr *e,Symbol *v,int discarded)
{
    unsigned i,n=0;if(!e)return 0;
    if(e->kind==EX_OBJECT&&e->symbol==v)return 1;
    if(discarded&&(e->kind==EX_ASSIGN||e->kind==EX_PRE||e->kind==EX_POST)&&e->left->kind==EX_OBJECT&&e->left->symbol==v)
        return body_reads(e->right,v,0);
    n=body_reads(e->left,v,0)+body_reads(e->right,v,0)+body_reads(e->third,v,0);
    for (i = 0; i < e->arg_count; ++i) {
        n += body_reads(e->args[i], v, 0);
    }
    return n;
}
static unsigned body_statement_reads(Statement *s,Symbol *v)
{
    unsigned n = 0;

    for (; s; s = s->next) {
        n += body_reads(s->expression, v, s->kind == ST_EXPR) + body_reads(s->step, v, 1) +
             body_statement_reads(s->body, v) + body_statement_reads(s->alternate, v) +
             body_statement_reads(s->initial, v);
    }
    return n;
}
static void body_drop_private_update(Expr **at,Symbol *v)
{
    Expr *e=*at;
    if(!e)return;
    if((e->kind==EX_PRE||e->kind==EX_POST)&&e->left->kind==EX_OBJECT&&e->left->symbol==v){
        if(e->kind==EX_POST){*at=e->left;free(e);}
        else{
            e->kind=EX_BINARY;e->op=e->op==TOK_INC?'+':'-';
            e->right=body_literal(type(TY_INT,0),1,e->location);
        }
        return;
    }
    body_drop_private_update(&e->left,v);
    body_drop_private_update(&e->right,v);
    body_drop_private_update(&e->third,v);
    for(unsigned i=0;i<e->arg_count;++i)body_drop_private_update(&e->args[i],v);
}
static int literal_integer_tree(Expr *e);
static int body_pure_discard_call(Expr *e)
{
    if(e->left||e->string||!e->symbol->defined||
       e->symbol->interrupt||e->symbol->noinline)return 0;
    for(Function *f=cg.parser->functions;f;f=f->next)if(f->symbol==e->symbol){
        Statement *item[1];
        unsigned count=0;
        if(!reduction_statements(f->body,item,&count,1))return 0;
        if(!count||(item[0]->kind==ST_RETURN&&!item[0]->expression))return 1;
        Statement *only=body_single(f->body);
        return f->symbol->internal&&only&&only->kind==ST_RETURN&&!only->next&&
               only->expression&&literal_integer_tree(only->expression);
    }
    return 0;
}
static int body_discard_effect(Expr *e)
{
    if(!e)return 0;
    if((e->kind==EX_CALL&&!body_pure_discard_call(e))||e->kind==EX_ASSIGN||
       e->kind==EX_PRE||e->kind==EX_POST||volatile_expression(e)||
       (e->type.base==TY_DOUBLE&&wide_scalar(value_type(e->type))))return 1;
    if(body_discard_effect(e->left)||body_discard_effect(e->right)||body_discard_effect(e->third))return 1;
    for(unsigned i=0;i<e->arg_count;++i)if(body_discard_effect(e->args[i]))return 1;
    return 0;
}
static void body_drop_expr(Expr **at,Symbol *v)
{
    Expr *e=*at;if(!e)return;
    if((e->kind==EX_ASSIGN||e->kind==EX_PRE||e->kind==EX_POST)&&e->left->kind==EX_OBJECT&&e->left->symbol==v){
        if(cg.function->jump_label_count&&e->right&&
           !body_effect(e->right)&&!literal_integer_tree(e->right))return;
        if(scalar_leaf_parameter(cg.function,v))return;
        if(v->type.base==TY_LONGLONG&&!v->type.pointers&&
           (e->kind!=EX_ASSIGN||e->op||!e->right||!wide_integer_literal(e->right)))return;
        Expr *value=e->right;e->right=NULL;free_expression(e);*at=value;
        int effect=!v->type.pointers&&(v->type.base==TY_LONG||v->type.base==TY_LONGLONG)
            ?body_discard_effect(value):body_effect(value);
        if(value&&!effect){
            free_expression(value);*at=NULL;
        }
    }else if(v->type.pointers&&!far_pointer(v->type)&&body_reads(e,v,0)==1)
        body_drop_private_update(at,v);
}
static void body_drop_stores(Statement *s,Symbol *v)
{
    for(;s;s=s->next){if(s->kind==ST_EXPR){body_drop_expr(&s->expression,v);if(!s->expression)s->kind=ST_EMPTY;}
        body_drop_expr(&s->step,v);body_drop_stores(s->body,v);body_drop_stores(s->alternate,v);body_drop_stores(s->initial,v);}
}
static void body_dead_locals(Function *f)
{
    unsigned round,i,j;
    int structured=!f->jump_label_count&&!find_symbol(cg.parser,"$basic_asm");
    for(round=0;round<4;++round)for(i=0;i<cg.parser->symbol_count;++i){
        Symbol *v=&cg.parser->symbols[i];unsigned bytes,offset,writes;int parameter,pointer;
        int single=!f->uses_wide&&!v->type.pointers&&v->type.base==TY_FLOAT;
        int wide_integer=structured&&!v->type.pointers&&v->type.base==TY_LONGLONG;
        if(v->owner!=f->id||!v->offset||(!body_private(v)&&!body_private_callback(v)&&
           !((single||wide_integer)&&body_fact_home(v))))continue;
        parameter=scalar_leaf_parameter(f,v);
        pointer=v->type.pointers&&!far_pointer(v->type)&&body_private(v);
        if(parameter&&!pointer)continue;
        writes=structured?scalar_writes(f->body,v):0;
        if(writes>(pointer?0u:1u)){
            scalar_live_budget=4096;
            scalar_live_statements(f->body,v,0,1,1,1);
        }
        if(parameter)continue;
        if(body_statement_reads(f->body,v))continue;
        body_drop_stores(f->body,v);if(statement_references(f->body,v))continue;
        bytes=(width(v->type)+1)&~1u;offset=v->offset;v->offset=0;
        for(j=0;j<cg.parser->symbol_count;++j)if(cg.parser->symbols[j].owner==f->id&&cg.parser->symbols[j].offset>offset)cg.parser->symbols[j].offset-=bytes;
        f->slots-=bytes;
    }
}
/* Address value numbering is confined to straight-line, call-free regions.
 * Only private scalar inputs and actual array addresses form candidates.
 * Array data is always reloaded in source order, even when bases may alias. */
static int body_address_pure(Expr *e)
{
    if(!e)return 0;
    if(e->kind==EX_OBJECT)return e->type.array||body_private(e->symbol);
    if(e->kind==EX_INT)return e->type.base!=TY_FLOAT;
    if(e->kind==EX_DEREF&&e->type.array)return body_address_pure(e->left);
    if(e->kind==EX_CAST&&value_width(e->type)==value_width(e->left->type))return body_address_pure(e->left);
    return e->kind==EX_BINARY&&(e->op=='+'||e->op=='-'||e->op=='*')&&
        body_address_pure(e->left)&&body_address_pure(e->right);
}
/* Preserve linear named addresses inside loops for induction, numeric and
 * indexed-region selection. A pointer temporary would conceal their stride
 * or an enclosing loop's invariant base from those later planners. */
static int body_address_linear(Expr *e)
{
    uint32_t n;
    if(!e)return 0;
    if(e->kind==EX_OBJECT||e->kind==EX_INT)return body_address_pure(e);
    if((e->kind==EX_DEREF&&e->type.array)||
       (e->kind==EX_CAST&&value_width(e->type)==value_width(e->left->type)))
        return body_address_linear(e->left);
    if(e->kind!=EX_BINARY)return 0;
    if(e->op=='+'||e->op=='-')
        return body_address_linear(e->left)&&body_address_linear(e->right);
    return e->op=='*'&&((integer_constant(e->left,&n)&&body_address_linear(e->right))||
           (integer_constant(e->right,&n)&&body_address_linear(e->left)));
}
static int body_near_pointer_only(Expr *left)
{
    while(left&&left->kind==EX_CAST&&value_type(left->type).pointers&&
          !far_pointer(value_type(left->type)))left=left->left;
    return left&&left->kind==EX_OBJECT&&!left->type.array&&
           !pointed_type(value_type(left->type)).array&&
           !left->symbol->near_nowrap&&!left->symbol->dpage;
}
static int body_displaced_pattern(Expr *e,Expr *pattern)
{
    unsigned i;
    if(!e)return 0;
    if(e->kind==EX_BINARY&&(e->op=='+'||e->op=='-')&&e->right->kind==EX_INT&&
       e->right->value&&body_equal(e->left,pattern))return 1;
    if(body_displaced_pattern(e->left,pattern)||body_displaced_pattern(e->right,pattern)||
       body_displaced_pattern(e->third,pattern))return 1;
    for(i=0;i<e->arg_count;++i)if(body_displaced_pattern(e->args[i],pattern))return 1;
    return 0;
}
static void body_address_normalize(Expr *e,unsigned loops)
{
    unsigned i;if(!e)return;
    body_address_normalize(e->left,loops);body_address_normalize(e->right,loops);body_address_normalize(e->third,loops);
    for(i=0;i<e->arg_count;++i)body_address_normalize(e->args[i],loops);
    if(e->kind==EX_BINARY&&e->op=='+'&&value_type(e->left->type).pointers&&!far_pointer(value_type(e->left->type))){
        while(e->right->kind==EX_BINARY&&(e->right->op=='+'||e->right->op=='-')&&
              e->right->right->kind==EX_INT&&value_width(e->right->type)==2&&
              !e->right->type.pointers&&e->right->type.base!=TY_FLOAT&&
              e->right->left->kind==EX_BINARY&&(e->right->left->op=='+'||e->right->left->op=='-')&&
              e->right->left->right->kind==EX_INT&&
              same_type(unqualified_value(e->right->type),unqualified_value(e->right->left->type))&&
              e->right->type.is_unsigned&&body_address_pure(e)){
            Expr *outer=e->right,*inner=outer->left;
            uint32_t d1=inner->right->value&65535u,d2=outer->right->value&65535u;
            uint32_t s1=inner->op=='+'?d1:(0u-d1)&65535u;
            uint32_t s2=outer->op=='+'?d2:(0u-d2)&65535u;
            outer->left=inner->left;outer->op='+';outer->right->value=(s1+s2)&65535u;
            outer->right->known=known_constant(outer->right->value,outer->right->type);
            outer->known=known_binary('+',inner->left->known,outer->right->known,outer->type);
            inner->left=NULL;free_expression(inner);
        }
    }
    if(e->kind==EX_BINARY&&e->op=='+'&&value_type(e->left->type).pointers&&!far_pointer(value_type(e->left->type))&&
       e->right->kind==EX_BINARY&&(e->right->op=='+'||e->right->op=='-')&&
       (!loops||!body_address_linear(e)||body_near_pointer_only(e->left)||
        (e->right->op=='+'&&e->right->left->kind==EX_BINARY&&
         (e->right->left->op=='*'||e->right->left->op==TOK_SHL)))&&
       e->right->right->kind==EX_INT&&value_width(e->right->type)==2&&!e->right->type.pointers&&
       e->right->type.base!=TY_FLOAT&&body_address_pure(e)){
        Expr *index=e->right,*base=new_expr(EX_BINARY,e->location,e->type);
        uint32_t displacement=index->right->value&65535;
        /* Pull a constant out of a subscript only after proving that
         * subscript arithmetic cannot wrap. Absolute indexed operands
         * carry into the next bank, unlike a wrapped near-pointer sum. */
        int32_t limit=e->right->type.is_unsigned?65535:32767;
        if(!body_near_pointer_only(e->left)&&
           (!index->left->known.valid||index->left->known.min<0||
            (!e->right->type.is_unsigned&&displacement>32767)||
            (index->op=='+'?index->left->known.max>limit-(int32_t)displacement:
                            index->left->known.min<(int32_t)displacement))){
            free(base);return;
        }
        base->op='+';base->left=e->left;base->right=index->left;
        e->left=base;e->right=index->right;e->op=index->op;free(index);
    }
    if(loops&&value_type(e->type).pointers&&body_address_linear(e))return;
    if(e->kind==EX_BINARY&&e->op=='+'&&!far_pointer(value_type(e->type))&&
       e->left->kind==EX_DEREF&&e->left->type.array&&e->left->left->kind==EX_BINARY&&
       (e->left->left->op=='+'||e->left->left->op=='-')&&e->left->left->right->kind==EX_INT&&
       value_width(e->left->left->right->type)==2&&body_address_pure(e)){
        Expr *offset=e->left->left,*sum;unsigned outer=width(pointed_type(value_type(offset->left->type)));
        unsigned inner=width(pointed_type(value_type(e->type)));
        if(e->right->kind==EX_INT){
            Expr access={0};unsigned byte;
            access.kind=EX_DEREF;access.left=e;access.type=pointed_type(value_type(e->type));
            if(fixed_memory_object(&access,&byte))return;
        }
        if(!inner||!outer||outer%inner)return;
        sum=new_expr(EX_BINARY,e->location,e->type);sum->op='+';sum->left=e->left;sum->right=e->right;
        e->left=sum;e->right=body_literal(type(TY_INT,0),(offset->right->value*(outer/inner))&65535,e->location);e->op=offset->op;
        sum->left->left=offset->left;offset->left=NULL;free_expression(offset);
    }
}
static Statement *body_flatten(Statement *s)
{
    Statement *head=NULL,**tail=&head;
    while(s){Statement *next=s->next;s->next=NULL;
        if(s->kind==ST_EMPTY)free(s);
        else if(s->kind==ST_BLOCK&&!s->inline_callee){*tail=body_flatten(s->body);s->body=NULL;free(s);}
        else *tail=s;
        while (*tail) {
            tail = &(*tail)->next;
        }
        s = next;
    }return head;
}
static int body_hidden_control(Expr *e)
{
    unsigned i;if(!e)return 0;
    if(e->kind==EX_CALL||e->kind==EX_CHOOSE||(e->kind==EX_BINARY&&(e->op==TOK_LAND||e->op==TOK_LOR)))return 1;
    if(body_hidden_control(e->left)||body_hidden_control(e->right)||body_hidden_control(e->third))return 1;
    for (i = 0; i < e->arg_count; ++i) {
        if (body_hidden_control(e->args[i])) {
            return 1;
        }
    }
    return 0;
}
static unsigned body_occurs(Expr *e,Expr *pattern)
{
    unsigned i,n;if(!e)return 0;if(body_equal(e,pattern))return 1;
    n=body_occurs(e->left,pattern)+body_occurs(e->right,pattern)+body_occurs(e->third,pattern);
    for (i = 0; i < e->arg_count; ++i) {
        n += body_occurs(e->args[i], pattern);
    }
    return n;
}
static int body_changes_address(Expr *e,Expr *address)
{
    unsigned i;if(!e)return 0;
    if((e->kind==EX_ASSIGN||e->kind==EX_PRE||e->kind==EX_POST)&&e->left->kind==EX_OBJECT&&loop_mentions(address,e->left->symbol))return 1;
    if(body_changes_address(e->left,address)||body_changes_address(e->right,address)||body_changes_address(e->third,address))return 1;
    for (i = 0; i < e->arg_count; ++i) {
        if (body_changes_address(e->args[i], address)) {
            return 1;
        }
    }
    return 0;
}
static void body_candidates(Expr *e,Expr **list,unsigned *count)
{
    if(!e||*count>=64)return;
    body_candidates(e->left,list,count);body_candidates(e->right,list,count);body_candidates(e->third,list,count);
    if(*count<64&&e->kind==EX_BINARY&&value_type(e->type).pointers&&!far_pointer(value_type(e->type))&&
       e->right->kind!=EX_INT&&body_address_pure(e))list[(*count)++]=e;
}
static void body_address_replace(Expr **at,Expr *pattern,Symbol *v)
{
    Expr *e=*at;unsigned i;if(!e)return;
    if(body_equal(e,pattern)){Expr *n=body_object(v,e->location);free_expression(e);*at=n;return;}
    body_address_replace(&e->left,pattern,v);body_address_replace(&e->right,pattern,v);body_address_replace(&e->third,pattern,v);
    for(i=0;i<e->arg_count;++i)body_address_replace(&e->args[i],pattern,v);
}
static void body_address_normalize_statements(Statement *s,unsigned loops)
{
    for(;s;s=s->next){
        unsigned nested=loops+(s->kind==ST_FOR||s->kind==ST_WHILE||s->kind==ST_DO);
        body_address_normalize(s->expression,nested);body_address_normalize(s->step,nested);
        body_address_normalize_statements(s->initial,loops);
        body_address_normalize_statements(s->body,nested);
        body_address_normalize_statements(s->alternate,loops);
    }
}
static void body_address_cse_region(Function *f,Statement **head,unsigned *temps,unsigned loops)
{
    Statement **at=head;
    while(*at){Statement *s=*at;Expr *candidates[64];unsigned n=0,i;int selected=0;
        unsigned nested=loops+(s->kind==ST_FOR||s->kind==ST_WHILE||s->kind==ST_DO);
        if(s->kind==ST_BLOCK)s->body=body_flatten(s->body);
        body_address_cse_region(f,&s->initial,temps,loops);
        body_address_cse_region(f,&s->body,temps,nested);
        body_address_cse_region(f,&s->alternate,temps,loops);
        /* Keep adjacent extraction stores as indexed operands. Materializing
         * a shared pointer here would hide the later word-store candidate;
         * its range/bank checks still run at selection time. */
        if(store_pair_candidate(s)){at=&s->next->next;continue;}
        if(*temps>=4){at=&s->next;continue;}
        if(s->kind!=ST_EXPR||body_hidden_control(s->expression)){at=&s->next;continue;}
        IndexedOperand operand;
        int indexed_update=indexed_repeated_word_update(s->expression)&&
            indexed_operand(s->expression->left,&operand);
        body_candidates(s->expression,candidates,&n);
        for(i=0;i<n;++i){Expr *pattern=candidates[i];Statement *end=s,*p;unsigned uses=0,statements=0;
            int linear=loops&&body_address_linear(pattern),displaced=0;
            if(linear&&!(pattern->kind==EX_BINARY&&(pattern->op=='+'||pattern->op=='-')&&
               body_near_pointer_only(pattern->left)))continue;
            if(!loops&&!cg.parser->no_indexed_operands&&!cg.parser->no_store_fusion&&
               pattern->kind==EX_BINARY&&(pattern->op=='+'||pattern->op=='-')&&
               pattern->left->kind==EX_OBJECT&&pattern->left->type.array&&
               !pattern->left->type.banked&&!pattern->left->symbol->owner){
                int all_stores=1;
                for(p=s;p&&p!=end;p=p->next){
                    IndexedOperand dummy;
                    if(p->kind!=ST_EXPR||!p->expression||p->expression->kind!=EX_ASSIGN||p->expression->op||
                       !indexed_operand(p->expression->left,&dummy)||dummy.base!=pattern->left->symbol){
                        all_stores=0;break;
                    }
                }
                if(all_stores)continue;
            }
            for(p=s;p&&p->kind==ST_EXPR&&statements<64&&!body_hidden_control(p->expression);p=p->next,++statements){
                if(p!=s&&store_pair_candidate(p))break;
                if(body_changes_address(p->expression,pattern))break;
                uses+=body_occurs(p->expression,pattern);
                if(linear&&!displaced&&body_displaced_pattern(p->expression,pattern))displaced=1;
                end=p->next;
            }
            if(linear&&!displaced)continue;
            /* The native update already shares its own destination address */
            if(uses==2&&indexed_update&&body_occurs(s->expression->left,pattern)==1)continue;
            if(uses>=2&&cg.parser->symbol_count<1024&&f->slots+2<=768){
                char name[64];Symbol *v;Expr *definition=body_clone(pattern);Statement *store=body_statement(ST_EXPR,s->location);
                snprintf(name,sizeof name,"__addr_%u_%u",f->id,++*temps);
                v=new_symbol(cg.parser,name,definition->type,s->location);v->owner=f->id;v->scope=1;v->active=1;v->internal=1;v->offset=f->slots+1;f->slots+=2;
                for(p=s;p!=end;p=p->next)body_address_replace(&p->expression,definition,v);
                store->expression=new_expr(EX_ASSIGN,s->location,v->type);store->expression->left=body_object(v,s->location);store->expression->right=definition;
                store->next=s;*at=store;at=&store->next;selected=1;break;
            }
        }
        if(!selected)at=&s->next;
    }
}
static void body_address_cse(Function *f,Statement **head,unsigned *temps)
{
    /* Normalize the complete region before recognizing adjacent stores. Both
     * sides of a pair must use the same address representation. */
    known_prepare(f);
    body_address_normalize_statements(*head,0);
    body_address_cse_region(f,head,temps,0);
}
static unsigned body_cursor_step(Statement *s,Symbol **cursor)
{
    Expr *e=s->expression;
    uint32_t count=1;
    unsigned size;
    if(s->kind!=ST_EXPR||!e||!e->left||e->left->kind!=EX_OBJECT)return 0;
    *cursor=e->left->symbol;
    if(!body_private(*cursor)||!(*cursor)->type.pointers||far_pointer((*cursor)->type))return 0;
    if(e->kind==EX_ASSIGN&&e->op=='+'){
        if(!integer_constant(e->right,&count)||count>65535)return 0;
    }else if((e->kind!=EX_PRE&&e->kind!=EX_POST)||e->op!=TOK_INC)return 0;
    size=increment_step((*cursor)->type);
    return size&&count<=65535/size?(unsigned)count*size:0;
}
static int body_cursor_written(Statement *s,Statement *stop,Symbol *v)
{
    for(;s&&s!=stop;s=s->next)
        if(scalar_writes_expr(s->expression,v)||scalar_writes_expr(s->step,v)||
           body_cursor_written(s->initial,NULL,v)||body_cursor_written(s->body,NULL,v)||
           body_cursor_written(s->alternate,NULL,v))return 1;
    return 0;
}
static Expr *body_cursor_base(Statement *head,Statement *loop,Symbol *v)
{
    Expr *base=NULL;
    for(;head!=loop;head=head->next){
        Expr *e=head->expression;
        if(!body_cursor_written(head,head->next,v))continue;
        base=NULL;
        if(head->kind==ST_EXPR&&e&&e->kind==EX_ASSIGN&&!e->op&&e->left->kind==EX_OBJECT&&e->left->symbol==v){
            unsigned offset;
            Symbol *root=near_object_address(e->right,&offset);
            if(root&&root->type.array&&!root->owner&&!root->type.banked)base=e->right;
        }
    }
    return base;
}
static void body_cursor_replace(Expr **at,Symbol *cursor,Expr *address)
{
    Expr *e=*at;
    unsigned i;
    if(!e)return;
    if(e->kind==EX_OBJECT&&e->symbol==cursor){
        *at=body_clone(address);free_expression(e);return;
    }
    body_cursor_replace(&e->left,cursor,address);
    body_cursor_replace(&e->right,cursor,address);
    body_cursor_replace(&e->third,cursor,address);
    for(i=0;i<e->arg_count;++i)body_cursor_replace(&e->args[i],cursor,address);
}
static void body_cursor_substitute(Statement *s,Statement *stop,Symbol *cursor,Expr *address)
{
    for(;s&&s!=stop;s=s->next){
        body_cursor_replace(&s->expression,cursor,address);
        body_cursor_replace(&s->step,cursor,address);
        body_cursor_substitute(s->initial,NULL,cursor,address);
        body_cursor_substitute(s->body,NULL,cursor,address);
        body_cursor_substitute(s->alternate,NULL,cursor,address);
    }
}

static Expr *body_shared_cursor_address(Symbol *cursor,Expr *base,Symbol *index,
                                       unsigned displacement,Location at)
{
    Type bytes=pointer_to(type(TY_CHAR,0));
    Expr *address=new_expr(EX_CAST,at,cursor->type),*sum=new_expr(EX_BINARY,at,bytes);
    unsigned base_offset;
    Symbol *object=near_object_address(base,&base_offset);
    address->left=sum;
    sum->op='+';sum->left=new_expr(EX_CAST,at,bytes);
    sum->left->left=body_object(object,at);
    sum->right=body_object(index,at);
    if(base_offset+displacement){
        Expr *offset=new_expr(EX_BINARY,at,bytes);
        offset->op='+';offset->left=sum->left;
        offset->right=body_literal(index->type,(base_offset+displacement)&65535u,at);
        sum->left=offset;
    }
    return address;
}

static void body_branched_cursor_use(Expr **e,Symbol *cursor,Expr *base,Symbol *index,unsigned displacement)
{
    if(!index||!loop_mentions(*e,cursor))return;
    Expr *address=body_shared_cursor_address(cursor,base,index,displacement,(*e)->location);
    body_cursor_replace(e,cursor,address);
    free_expression(address);
}

/* Analyze simple conditional paths up to the shared loop step. A continue
 * bypasses that step, so it must also bypass every cursor advance */
static int body_branched_cursor(Statement *s,Statement *stop,Symbol *cursor,
                                Expr *base,Symbol *index,int displacement)
{
    for(;s&&s!=stop;s=s->next){
        Expr *e=s->expression;
        switch(s->kind){
        case ST_EMPTY:break;
        case ST_BLOCK:
            if(s->inline_callee)return -1;
            displacement=body_branched_cursor(s->body,NULL,cursor,base,index,displacement);
            break;
        case ST_IF:{
            if(scalar_writes_expr(e,cursor))return -1;
            body_branched_cursor_use(&s->expression,cursor,base,index,(unsigned)displacement);
            int yes=body_branched_cursor(s->body,NULL,cursor,base,index,displacement);
            int no=body_branched_cursor(s->alternate,NULL,cursor,base,index,displacement);
            if(yes==-1||no==-1||(yes>=0&&no>=0&&yes!=no))return -1;
            displacement=yes>=0?yes:no;
            break;
        }
        case ST_EXPR:{
            Symbol *v=NULL;
            unsigned step=body_cursor_step(s,&v);
            if(step&&v==cursor){
                if(index){free_expression(s->expression);s->expression=NULL;s->kind=ST_EMPTY;}
                if(step>65535u-(unsigned)displacement)return -1;
                displacement+=(int)step;
                break;
            }
            if(e&&e->kind==EX_ASSIGN&&!e->op&&e->left->kind==EX_DEREF&&
               e->left->left->kind==EX_POST&&e->left->left->op==TOK_INC&&
               lftr_object(e->left->left->left,cursor)){
                step=increment_step(cursor->type);
                if(loop_mentions(e->right,cursor)||!step||step>65535u-(unsigned)displacement)return -1;
                if(index){
                    free_expression(e->left->left);
                    e->left->left=body_shared_cursor_address(cursor,base,index,(unsigned)displacement,e->location);
                }
                displacement+=(int)step;
                break;
            }
            if(scalar_writes_expr(e,cursor))return -1;
            body_branched_cursor_use(&s->expression,cursor,base,index,(unsigned)displacement);
            break;
        }
        case ST_CONTINUE:return displacement==0?-2:-1;
        case ST_BREAK:return -2;
        case ST_RETURN:
            if(scalar_writes_expr(e,cursor))return -1;
            body_branched_cursor_use(&s->expression,cursor,base,index,(unsigned)displacement);
            return -2;
        default:return -1;
        }
        if(displacement<0)return displacement;
    }
    return displacement;
}

static int body_cursor_bound_stores(Statement *s,Statement *stop,Symbol *bound,
                                   Expr **stores,unsigned *count)
{
    for(;s&&s!=stop;s=s->next){
        Expr *set=plain_assignment(s);
        if(set&&set->left->symbol==bound){
            Type t=value_type(set->right->type);
            if(*count==8||!t.pointers||far_pointer(t))return 0;
            stores[(*count)++]=set;
        }
        if(!body_cursor_bound_stores(s->initial,NULL,bound,stores,count)||
           !body_cursor_bound_stores(s->body,NULL,bound,stores,count)||
           !body_cursor_bound_stores(s->alternate,NULL,bound,stores,count))return 0;
    }
    return 1;
}

static Expr *body_cursor_bound_offset(Expr *value,Expr *base,Type word)
{
    Location at=value->location;
    unsigned start,displacement=0,scale=0;
    Symbol *object=near_object_address(base,&start);
    Expr *index=NULL,*offset;
    if(object&&indexed_near_base(value,&index,&scale,&displacement)==object&&
       displacement==start){
        if(!index)offset=body_literal(word,0,at);
        else{
            offset=new_expr(EX_CAST,at,word);offset->left=body_clone(index);
            if(scale!=1){
                Expr *scaled=new_expr(EX_BINARY,at,word);
                scaled->op='*';scaled->left=offset;scaled->right=body_literal(word,scale,at);
                offset=scaled;
            }
        }
        free_expression(value);
    }else{
        offset=new_expr(EX_BINARY,at,word);offset->op='-';
        offset->left=new_expr(EX_CAST,at,word);offset->left->left=value;
        offset->right=new_expr(EX_CAST,at,word);offset->right->left=body_clone(base);
    }
    return offset;
}

/* Near-pointer equality is unchanged by subtracting the same base modulo
 * 65536. Convert the private end cursor when it is assigned, including on
 * any path that revises the end without advancing the current offset */
static int body_cursor_offset_test(Function *f,Statement *head,Statement *loop,
                                  Symbol *cursor,Expr *base,Symbol *index)
{
    Expr *test=loop->expression,**pos=&test->left,**limit=&test->right,*stores[8];
    Symbol *bound,*offset;
    unsigned count=0;
    char name[80];
    if(test->kind!=EX_BINARY||(test->op!=TOK_NE&&test->op!=TOK_EQ))return 0;
    if(!lftr_object(*pos,cursor)){pos=&test->right;limit=&test->left;}
    if(!lftr_object(*pos,cursor)||(*limit)->kind!=EX_OBJECT)return 0;
    bound=(*limit)->symbol;
    if(!bound->scope||bound==cursor||!body_private(bound)||!bound->type.pointers||
       far_pointer(bound->type)||cg.parser->symbol_count>=1024||f->slots+2>768||
       !body_cursor_bound_stores(head,loop,bound,stores,&count)||!count||
       !body_cursor_bound_stores(loop->body,NULL,bound,stores,&count)||
       statement_references(f->body,bound)!=count+1)return 0;
    snprintf(name,sizeof name,"%s_end",index->name);
    offset=new_symbol(cg.parser,name,index->type,loop->location);
    offset->owner=f->id;offset->scope=1;offset->active=1;offset->internal=1;
    offset->offset=f->slots+1;f->slots+=2;
    for(unsigned i=0;i<count;++i){
        Expr *set=stores[i];
        free_expression(set->left);
        set->left=body_object(offset,set->location);
        set->right=body_cursor_bound_offset(set->right,base,index->type);
        set->type=index->type;
    }
    free_expression(*pos);*pos=body_object(index,test->location);
    free_expression(*limit);*limit=body_object(offset,test->location);
    return 1;
}

/* Lockstep near cursors starting at fixed arrays share a byte induction
 * variable. Only the common trailing update changes the offset, so an early
 * continue keeps every cursor at its original element. Other cursors may
 * complete the same advance across branches before that common step. */
static void body_share_cursors(Function *f,Statement **head)
{
    Statement **link;
    unsigned serial=0;
    for(link=head;*link;link=&(*link)->next){
        Statement *loop=*link,*s,*first=NULL,*init;
        Symbol *cursors[8],*index;
        Expr *bases[8];
        unsigned count=0,stride=0,i,trailing;
        char name[64];
        Type word=type(TY_INT,0);
        word.is_unsigned=1;
        if(loop->kind!=ST_WHILE||!loop->body||loop->body->kind!=ST_BLOCK||
           loop->body->inline_callee||!loop->expression)continue;
        for(s=loop->body->body;s;s=s->next){
            Symbol *v=NULL;
            unsigned step=body_cursor_step(s,&v);
            if(!step||step!=stride||count==8){count=0;first=s;stride=step;}
            if(step)cursors[count++]=v;
        }
        if(count<2||cg.parser->symbol_count==1024||f->slots+2>768)continue;
        for(i=0;i<count;++i){
            unsigned j;
            for(j=0;j<i&&cursors[j]!=cursors[i];++j){}
            if(j<i||scalar_writes_expr(loop->expression,cursors[i])||
               body_cursor_written(loop->body->body,first,cursors[i])||
               loop_observed_outside(loop->next,NULL,cursors[i])||
               !(bases[i]=body_cursor_base(*head,loop,cursors[i])))break;
        }
        if(i!=count)continue;
        trailing=count;
        for(s=*head;s!=loop&&count<8;s=s->next){
            Expr *assignment=plain_assignment(s),*base;
            Symbol *cursor;
            if(!assignment||!(cursor=assignment->left->symbol)||!body_private(cursor)||
               !cursor->type.pointers||far_pointer(cursor->type))continue;
            for(i=0;i<count&&cursors[i]!=cursor;++i){}
            if(i!=count||loop_mentions(loop->expression,cursor)||
               body_cursor_written(first,NULL,cursor)||loop_observed_outside(loop->next,NULL,cursor)||
               !(base=body_cursor_base(*head,loop,cursor))||
               body_branched_cursor(loop->body->body,first,cursor,base,NULL,0)!=(int)stride)continue;
            cursors[count]=cursor;bases[count++]=base;
        }
        snprintf(name,sizeof name,"__stride_%u_%u",f->id,++serial);
        index=new_symbol(cg.parser,name,word,loop->location);
        index->owner=f->id;index->scope=1;index->active=1;index->internal=1;
        index->offset=f->slots+1;f->slots+=2;
        init=body_statement(ST_EXPR,loop->location);
        init->expression=new_expr(EX_ASSIGN,loop->location,word);
        init->expression->left=body_object(index,loop->location);
        init->expression->right=body_literal(word,0,loop->location);
        init->next=loop;*link=init;link=&init->next;
        for(i=0;i<count;++i){
            if(i>=trailing){
                body_branched_cursor(loop->body->body,first,cursors[i],bases[i],index,0);
                continue;
            }
            Expr *address=body_shared_cursor_address(cursors[i],bases[i],index,0,loop->location);
            if(!body_cursor_offset_test(f,*head,loop,cursors[i],bases[i],index))
                body_cursor_replace(&loop->expression,cursors[i],address);
            body_cursor_substitute(loop->body->body,first,cursors[i],address);
            free_expression(address);
        }
        while(first->next){
            Statement *next=first->next;first->next=next->next;
            free_expression(next->expression);free(next);
        }
        free_expression(first->expression);
        first->expression=new_expr(EX_ASSIGN,first->location,word);
        first->expression->op='+';
        first->expression->left=body_object(index,first->location);
        first->expression->right=body_literal(word,stride,first->location);
    }
}

static int body_far_address(Expr *e)
{
    if(!e||e->kind!=EX_BINARY||e->op!='+'||!far_pointer(value_type(e->type))||
       e->left->kind!=EX_OBJECT||!body_fact_home(e->left->symbol)||
       e->right->kind!=EX_OBJECT||!body_private(e->right->symbol)||
       !e->right->type.is_unsigned||!known_integer(e->right->type)||
       value_width(e->right->type)!=2)return 0;
    unsigned stride=width(pointed_type(value_type(e->left->type)));
    return stride>=2&&stride<=8&&!(stride&(stride-1));
}

static void body_far_candidates(Expr *e,Expr **list,unsigned *count)
{
    if(!e||*count==16)return;
    if(body_far_address(e)){
        for(unsigned i=0;i<*count;++i)if(body_equal(list[i],e))return;
        list[(*count)++]=e;
        return;
    }
    body_far_candidates(e->left,list,count);
    body_far_candidates(e->right,list,count);
    body_far_candidates(e->third,list,count);
    for(unsigned i=0;i<e->arg_count;++i)body_far_candidates(e->args[i],list,count);
}

static int body_far_region(Statement *s,Expr *pattern,int *uses)
{
    for(;s;s=s->next){
        int yes=0,no=0;
        if(s->inline_callee||body_hidden_control(s->expression)||
           body_changes_address(s->expression,pattern))return 0;
        *uses+=(int)body_occurs(s->expression,pattern);
        switch(s->kind){
        case ST_EMPTY:case ST_EXPR:break;
        case ST_BLOCK:
            if(!body_far_region(s->body,pattern,uses))return 0;
            break;
        case ST_IF:
            if(!body_far_region(s->body,pattern,&yes)||!body_far_region(s->alternate,pattern,&no))return 0;
            *uses+=yes>no?yes:no;
            break;
        case ST_RETURN:return 1;
        default:return 0;
        }
    }
    return 1;
}

static void body_far_arm_candidates(Statement *s,Expr **list,unsigned *count)
{
    for(;s&&*count<16;s=s->next){
        if(s->kind!=ST_EXPR&&s->kind!=ST_IF&&s->kind!=ST_BLOCK&&s->kind!=ST_RETURN)break;
        body_far_candidates(s->expression,list,count);
        body_far_arm_candidates(s->body,list,count);
        body_far_arm_candidates(s->alternate,list,count);
    }
}

static void body_far_replace(Statement *s,Statement *stop,Expr *pattern,Symbol *home)
{
    for(;s!=stop;s=s->next){
        body_address_replace(&s->expression,pattern,home);
        body_far_replace(s->body,NULL,pattern,home);
        body_far_replace(s->alternate,NULL,pattern,home);
    }
}

/* Keep a frequently used far record address in a compiler-owned pointer.
 * The address calculation may move earlier, while the field reads stay
 * on their original paths and retain the full bank carry */
static void body_reuse_far_addresses(Function *f,Statement **head,unsigned *serial)
{
    for(Statement **at=head;*at&&*serial<4;at=&(*at)->next){
        Statement *s=*at,*end;
        Expr *candidates[16];
        unsigned count=0;
        if(s->inline_callee)continue;
        if(s->kind==ST_BLOCK){
            body_reuse_far_addresses(f,&s->body,serial);
            continue;
        }
        if(s->kind!=ST_IF&&s->kind!=ST_EXPR&&s->kind!=ST_RETURN)continue;
        body_far_candidates(s->expression,candidates,&count);
        if(s->kind==ST_IF){
            body_far_arm_candidates(s->body,candidates,&count);
            body_far_arm_candidates(s->alternate,candidates,&count);
        }
        for(unsigned i=0;i<count;++i){
            int uses=0;
            Expr *pattern=candidates[i];
            for(end=s;end;end=end->next){
                Statement one=*end;
                int n=0;
                one.next=NULL;
                if(!body_far_region(&one,pattern,&n))break;
                uses+=n;
                if(end->kind==ST_RETURN){end=end->next;break;}
            }
            if(uses<2||cg.parser->symbol_count>=1024||f->slots+4>768)continue;
            char name[64];
            Expr *definition=body_clone(pattern);
            snprintf(name,sizeof name,"__far_entry_%u_%u",f->id,++*serial);
            Symbol *home=new_symbol(cg.parser,name,definition->type,s->location);
            home->owner=f->id;home->scope=1;home->active=1;home->internal=1;
            home->offset=f->slots+1;f->slots+=4;
            Statement *store=body_statement(ST_EXPR,s->location);
            store->expression=new_expr(EX_ASSIGN,s->location,home->type);
            store->expression->left=body_object(home,s->location);
            store->expression->right=definition;
            body_far_replace(s,end,definition,home);
            store->next=s;*at=store;
            break;
        }
    }
}

/* Drop an overwritten private home, keeping evaluation of the original
 * RHS. In particular, separate hardware reads remain in source order. */
static void body_overwritten_locals(Statement *s)
{
    for(;s;s=s->next){
        Statement *next=s->next;
        Expr *a=s->expression,*b=next?next->expression:NULL;
        body_overwritten_locals(s->initial);
        body_overwritten_locals(s->body);
        body_overwritten_locals(s->alternate);
        if(s->kind!=ST_EXPR||!next||next->kind!=ST_EXPR||!a||!b||
           a->kind!=EX_ASSIGN||b->kind!=EX_ASSIGN||a->op||b->op||
           a->left->kind!=EX_OBJECT||b->left->kind!=EX_OBJECT||
           a->left->symbol!=b->left->symbol||!body_private(a->left->symbol)||
           loop_mentions(b->right,a->left->symbol))continue;
        s->expression=a->right;a->right=NULL;free_expression(a);
    }
}
static Symbol *body_xor_source(Statement *s,Symbol *destination)
{
    Expr *e=s&&s->kind==ST_EXPR?s->expression:NULL,*rhs;
    if(!e||e->kind!=EX_ASSIGN||e->left->kind!=EX_OBJECT||e->left->symbol!=destination)return NULL;
    rhs=e->right;
    if(e->op!='^'){
        if(e->op)return NULL;
        while(rhs->kind==EX_CAST&&known_integer(rhs->type)&&!rhs->type.is_bool&&
              width(rhs->type)>=width(destination->type))rhs=rhs->left;
        if(rhs->kind!=EX_BINARY||rhs->op!='^')return NULL;
        if(rhs->left->kind==EX_OBJECT&&rhs->left->symbol==destination)rhs=rhs->right;
        else if(rhs->right->kind==EX_OBJECT&&rhs->right->symbol==destination)rhs=rhs->left;
        else return NULL;
    }
    return rhs->kind==EX_OBJECT?rhs->symbol:NULL;
}
static void body_exchange_uses(Expr *e,Symbol *a,Symbol *b)
{
    if(!e)return;
    if(e->kind==EX_OBJECT){
        if(e->symbol==a)e->symbol=b;
        else if(e->symbol==b)e->symbol=a;
    }
    body_exchange_uses(e->left,a,b);body_exchange_uses(e->right,a,b);body_exchange_uses(e->third,a,b);
    for(unsigned i=0;i<e->arg_count;++i)body_exchange_uses(e->args[i],a,b);
}
/* After a terminal straight-line swap, the two private homes can exchange
 * names. Neither home's identity is observable before the return. */
static void body_terminal_xor_swaps(Statement *s)
{
    for(;s;s=s->next){
        Expr *e=s->expression;
        Statement *second=s->next,*third=second?second->next:NULL,*tail;
        Symbol *a,*b;
        body_terminal_xor_swaps(s->initial);
        body_terminal_xor_swaps(s->body);
        body_terminal_xor_swaps(s->alternate);
        if(!third||s->kind!=ST_EXPR||!e||e->kind!=EX_ASSIGN||e->left->kind!=EX_OBJECT)continue;
        a=e->left->symbol;
        b=body_xor_source(s,a);
        if(!b||a==b||!known_integer(a->type)||a->type.is_bool||!same_type(a->type,b->type)||
           body_xor_source(second,b)!=a||body_xor_source(third,a)!=b||!body_private(a)||!body_private(b))continue;
        for(tail=third->next;tail&&(tail->kind==ST_EXPR||tail->kind==ST_EMPTY);tail=tail->next){}
        if(!tail||tail->kind!=ST_RETURN)continue;
        for(Statement *p=s;p!=third->next;p=p->next){
            free_expression(p->expression);p->expression=NULL;p->kind=ST_EMPTY;
        }
        for(Statement *p=third->next;p!=tail->next;p=p->next)body_exchange_uses(p->expression,a,b);
    }
}
static Symbol *body_literal_store(Statement *s,unsigned *offset,unsigned *bytes)
{
    Expr *store=s->expression;
    if(s->kind!=ST_EXPR||!store||store->kind!=EX_ASSIGN||store->op||
       !wide_integer_literal(store->right)||volatile_expression(store))return NULL;
    *bytes=width(store->left->type);
    return direct_memory_object(store->left,offset);
}
/* A fixed write can cover an earlier store if no intervening operation reads it */
static void body_covered_stores(Statement *s)
{
    for(;s;s=s->next){
        Statement *next=s->next;
        Expr *store,*copy;
        Symbol *destination,*source;
        unsigned at,from,to,bytes,span;
        body_covered_stores(s->initial);
        body_covered_stores(s->body);
        body_covered_stores(s->alternate);
        destination=body_literal_store(s,&at,&bytes);
        if(destination){
            unsigned budget=16;
            for(Statement *p=next;p&&budget--;p=p->next){
                if(p->kind==ST_EMPTY)continue;
                Expr *update=p->expression,*assign=s->expression;
                if(p->kind==ST_EXPR&&update&&(update->kind==EX_PRE||update->kind==EX_POST)&&
                   assign->left->kind==EX_OBJECT&&body_equal(assign->left,update->left)&&
                   known_integer(destination->type)&&!destination->type.is_bool){
                    uint64_t old=initializer_cast64(assign->right->value,destination->type),value;
                    if(integer_binary_constant(update->op==TOK_INC?'+':'-',promoted(destination->type),old,1,&value))break;
                    free_expression(assign->right);
                    assign->right=body_literal(destination->type,(uint32_t)value,update->location);
                    free_expression(update);p->expression=NULL;p->kind=ST_EMPTY;
                    continue;
                }
                source=body_literal_store(p,&to,&span);
                if(!source)break;
                if(source==destination&&at>=to&&at+bytes<=to+span){
                    free_expression(s->expression);s->expression=NULL;s->kind=ST_EMPTY;
                    break;
                }
                if(source==destination&&at<to+span&&to<at+bytes)break;
            }
        }
        while(next&&next->kind==ST_EMPTY)next=next->next;
        if(s->kind!=ST_EXPR||!next||next->kind!=ST_EXPR)continue;
        store=s->expression;copy=next->expression;
        if(store->kind!=EX_ASSIGN||store->op||copy->kind!=EX_ASSIGN||copy->op||
           !structure_object(copy->type)||body_effect(store->left)||body_effect(store->right)||
           volatile_expression(copy))continue;
        destination=direct_memory_object(store->left,&at);
        if(!destination||destination!=direct_memory_object(copy->left,&to))continue;
        source=direct_memory_object(copy->right,&from);
        bytes=width(store->left->type);span=width(copy->type);
        if(!source||at<to||at+bytes>to+span||
           (source==destination&&at<from+span&&from<at+bytes))continue;
        free_expression(store);s->expression=NULL;s->kind=ST_EMPTY;
    }
}
/* Defer a near address calculation until a switch arm that consumes it.
 * Only immutable parameters and static array addresses may be rematerialized,
 * and each consuming arm immediately leaves the switch. */
static int body_switch_address(Function *f,Expr *e)
{
    if(volatile_expression(e))return 0;
    if(e->kind==EX_OBJECT){
        Symbol *v=e->symbol;
        if(!v->owner&&v->type.array&&!v->type.banked)return 1;
        return v->owner==f->id&&!v->scope&&body_private(v)&&!scalar_writes(f->body,v);
    }
    if(e->kind==EX_INT)return reg_width(e->type)==2;
    if(e->kind==EX_CAST)
        return reg_width(e->type)==2&&body_switch_address(f,e->left);
    return e->kind==EX_BINARY&&(e->op=='+'||e->op=='-')&&reg_width(e->type)==2&&
        body_switch_address(f,e->left)&&body_switch_address(f,e->right);
}
static void body_defer_switch_addresses(Function *f,Statement *s)
{
    for(;s;s=s->next){
        Statement *sw=s->next,*arm;
        Expr *e=s->expression;
        Symbol *v;
        unsigned count=0,uses;
        if(s->kind!=ST_EXPR||!e||e->kind!=EX_ASSIGN||e->op||
           e->left->kind!=EX_OBJECT||!sw||sw->kind!=ST_SWITCH||sw->body->kind!=ST_BLOCK)continue;
        v=e->left->symbol;
        if(v->owner!=f->id||!v->scope||!v->type.pointers||far_pointer(v->type)||
           !body_private(v)||!body_switch_address(f,e->right)||loop_mentions(e->right,v))continue;
        for(arm=sw->body->body;arm;arm=arm->next){
            Statement *target=arm;
            while(target&&target->kind==ST_CASE)target=target->body;
            if(!target||target==arm||target->kind!=ST_EXPR||!target->expression||
               target->expression->kind!=EX_CALL||!arm->next||arm->next->kind!=ST_BREAK)continue;
            uses=expression_references(target->expression,v);
            if(uses==1)++count;
        }
        if(!count||count!=statement_references(sw->body,v)||
           statement_references(f->body,v)!=count+1||scalar_writes(sw->body,v))continue;
        body_cursor_substitute(sw->body,NULL,v,e->right);
        /* The regular dead-local pass removes the now unused definition */
    }
}
/* A selected string's byte can become the case result when the pointer
 * has no other observations between the assignment and the return. */
static void body_project_switch_strings(Statement *s)
{
    for(;s;s=s->next){
        Statement *result=s->next,*arms[64];
        Expr *values[64];
        unsigned char falls[64];
        Symbol *home=NULL;
        unsigned count=0;
        if(s->kind!=ST_SWITCH||!s->body||s->body->kind!=ST_BLOCK||
           !result||result->kind!=ST_RETURN||!result->expression||
           body_discard_effect(result->expression))continue;
        BodyFacts facts={0};
        Statement *arm=s->body->body;
        for(;arm;){
            Statement *action=arm,*after=arm->next;
            Expr *e,*value;
            if(after&&after->kind!=ST_BREAK&&after->kind!=ST_CASE)break;
            while(action->kind==ST_CASE)action=action->body;
            if(action==arm||action->next||action->kind!=ST_EXPR||!(e=action->expression)||
               e->kind!=EX_ASSIGN||e->op||e->left->kind!=EX_OBJECT||!far_pointer(e->left->type)||
               volatile_expression(e)||!body_fact_value(e->right)||count==64)break;
            Symbol *target=e->left->symbol;
            if(!loop_private(target)||(home&&home!=target)||
               expression_references(result->expression,target)!=1)break;
            home=target;
            facts.value[body_symbol(home)]=e->right;
            value=body_clone(result->expression);
            body_replace(&value,&facts,0);scalar_refold_expr(value);
            if(!wide_integer_literal(value)){free_expression(value);break;}
            falls[count]=after&&after->kind==ST_CASE;
            arms[count]=action;values[count++]=value;
            arm=after&&after->kind==ST_BREAK?after->next:after;
        }
        if(arm||count<4){
            for(unsigned i=0;i<count;++i)free_expression(values[i]);
            continue;
        }
        for(unsigned i=count;i;--i){
            unsigned j=i-1;
            if(falls[j]){free_expression(values[j]);values[j]=body_clone(values[j+1]);}
            free_expression(arms[j]->expression);
            arms[j]->expression=values[j];arms[j]->kind=ST_RETURN;
        }
    }
}
/* Keep a pure definition on the path that needs it. If the left side of an
 * OR succeeds and its arm returns, the right side and later uses are dead. */
static void body_sink_guard_value(Statement *s)
{
    for(;s;s=s->next){
        Statement *guard=s->next,*end;
        Expr *e=s->expression,*condition,*sequence;
        Symbol *v;
        if(s->kind!=ST_EXPR||!e||e->kind!=EX_ASSIGN||e->op||
           e->left->kind!=EX_OBJECT||!guard||guard->kind!=ST_IF||guard->alternate)continue;
        v=e->left->symbol;
        condition=guard->expression;
        if(!body_private(v)||!v->scope||!condition||condition->kind!=EX_BINARY||
           condition->op!=TOK_LOR||body_effect(e->right)||body_effect(condition->left)||
           loop_mentions(condition->left,v)||!loop_mentions(condition->right,v)||
           statement_references(guard->body,v))continue;
        end=body_single(guard->body);
        if(!end)continue;
        while(end->next)end=end->next;
        if(end->kind!=ST_RETURN)continue;
        sequence=new_expr(EX_COMMA,condition->right->location,condition->right->type);
        sequence->left=e;sequence->right=condition->right;
        condition->right=sequence;
        s->kind=ST_EMPTY;s->expression=NULL;
    }
}
/* An immediately tested value needs no home. Follow only the operands
 * that the next condition always evaluates first. */
static Statement *body_last_action(Statement *s)
{
    Statement *last=NULL;
    for(;s;s=s->next){
        Statement *action=s->kind==ST_BLOCK?body_last_action(s->body):s;
        if(action&&action->kind!=ST_EMPTY)last=action;
    }
    return last;
}
/* A terminal store to a private return home can return its value directly */
static int body_return_last_store(Statement *s,Symbol *home)
{
    if(!s)return 0;
    if(s->kind==ST_BLOCK)return body_return_last_store(body_last_action(s->body),home);
    if(s->kind==ST_IF){
        int yes=body_return_last_store(body_last_action(s->body),home);
        int no=body_return_last_store(body_last_action(s->alternate),home);
        return yes||no;
    }
    Expr *store=s->expression;
    if(s->kind!=ST_EXPR||!store||store->kind!=EX_ASSIGN||store->op||
       store->left->kind!=EX_OBJECT||store->left->symbol!=home)return 0;
    s->kind=ST_RETURN;
    s->expression=convert(store->right,unqualified_value(home->type));
    store->right=NULL;free_expression(store);
    return 1;
}
static int body_terminal_return_stores(Statement *body)
{
    if(body->kind!=ST_BLOCK)return 0;
    for(Statement *s=body->body;s;s=s->next){
        Statement *next=s->next;
        while(next&&next->kind==ST_EMPTY)next=next->next;
        if(next&&next->kind==ST_RETURN&&next->expression&&next->expression->kind==EX_OBJECT&&
           (s->kind==ST_IF||s->kind==ST_BLOCK)){
            Symbol *home=next->expression->symbol;
            if(body_private(home)&&home->scope&&body_return_last_store(s,home))return 1;
        }
    }
    return 0;
}
static int body_forward_branch_values(Statement *s)
{
    int changed=0;
    for(;s;s=s->next){
        Statement *guard=s->next;
        changed|=body_forward_branch_values(s->body);
        changed|=body_forward_branch_values(s->alternate);
        changed|=body_forward_branch_values(s->initial);
        if(!guard||guard->kind!=ST_IF)continue;
        for(;;){
            Statement *def=s->kind==ST_BLOCK?body_last_action(s->body):s;
            Expr *assign,*value,**test=&guard->expression;
            Symbol *home;
            uint32_t yes,no;
            if(!def||def->kind!=ST_EXPR||!(assign=def->expression)||assign->kind!=EX_ASSIGN||
               assign->op||assign->left->kind!=EX_OBJECT)break;
            value=assign->right;
            home=assign->left->symbol;
            Expr *condition=*test;
            if(condition->kind==EX_BINARY&&(condition->op==TOK_EQ||condition->op==TOK_NE)&&
               body_private(home)&&literal_integer_tree(value)&&!loop_mentions(value,home)&&
               same_type(unqualified_value(value->type),unqualified_value(assign->left->type))&&
               ((body_equal(condition->left,assign->left)&&body_equal(condition->right,value))||
                (body_equal(condition->right,assign->left)&&body_equal(condition->left,value)))){
                int equal=condition->op==TOK_EQ;
                Statement *chosen=equal?guard->body:guard->alternate;
                free_statements(equal?guard->alternate:guard->body);
                free_expression(condition);guard->expression=NULL;
                guard->kind=ST_BLOCK;guard->body=chosen;guard->alternate=NULL;
                changed=1;break;
            }
            while(((*test)->kind==EX_UNARY&&(*test)->op=='!')||
                  ((*test)->kind==EX_BINARY&&((*test)->op==TOK_LAND||(*test)->op==TOK_LOR)))
                test=&(*test)->left;
            if((*test)->kind==EX_BINARY&&comparison((*test)->op)&&integer_constant((*test)->right,&yes)){
                unsigned offset;
                int is_unsigned;
                Expr *byte=comparison_byte(value,&is_unsigned);
                if(!byte||width(byte->type)!=1||!direct_memory_object(byte,&offset)||volatile_expression(value)||
                   !same_type(unqualified_value(value->type),unqualified_value(assign->left->type)))break;
                test=&(*test)->left;
            }else if(!(value->kind==EX_BINARY&&comparison(value->op))&&
                    !(value->kind==EX_CHOOSE&&integer_constant(value->right,&yes)&&
                      integer_constant(value->third,&no)&&yes<=1&&no<=1&&yes!=no)&&
                    !(value->kind==EX_OBJECT&&body_private(value->symbol)&&same_type(value->type,assign->left->type)))break;
            if((*test)->kind!=EX_OBJECT||(*test)->symbol!=home||!body_private(home)||
               statement_references(cg.function->body,home)!=2)break;
            free_expression(*test);*test=value;assign->right=NULL;
            free_expression(assign);def->expression=NULL;def->kind=ST_EMPTY;
            changed=1;
        }
    }
    return changed;
}
static int body_has_continue(Statement *s)
{
    for(;s;s=s->next)if(s->kind==ST_CONTINUE||body_has_continue(s->body)||body_has_continue(s->alternate))return 1;
    return 0;
}
static int body_counted_step(Expr *step)
{
    Expr *rhs;uint32_t n;
    if(!step||!step->left||step->left->kind!=EX_OBJECT||step->type.base!=TY_INT||
       step->type.pointers||step->type.is_bool||width(step->type)!=2||volatile_expression(step))return 0;
    if(direct_increment(step))return step->op==TOK_INC;
    if(step->kind!=EX_ASSIGN)return 0;
    if(step->op=='+')return integer_constant(step->right,&n)&&n==1;
    rhs=step->right;
    if(step->op||rhs->kind!=EX_BINARY||rhs->op!='+'||reg_width(rhs->type)!=2)return 0;
    if(!body_equal(rhs->left,step->left)||!integer_constant(rhs->right,&n)||n!=1)return 0;
    free_expression(rhs);step->right=NULL;step->kind=EX_PRE;step->op=TOK_INC;
    return 1;
}
static int body_counted_test(Expr *test,Symbol *index)
{
    if(!test||test->kind!=EX_BINARY||body_effect(test))return 0;
    if(test->op=='>'&&test->right->kind==EX_OBJECT&&test->right->symbol==index){
        Expr *swap=test->left;test->left=test->right;test->right=swap;test->op='<';
    }
    return test->left->kind==EX_OBJECT&&test->left->symbol==index&&(test->op=='<'||test->op==TOK_NE);
}
static Statement **body_counted_tail(Statement *s)
{
    Statement **tail=&s->body;
    while(*tail&&(*tail)->kind==ST_BLOCK&&!(*tail)->next&&!(*tail)->inline_callee)tail=&(*tail)->body;
    while(*tail&&(*tail)->next)tail=&(*tail)->next;
    return *tail&&(*tail)->kind==ST_EXPR&&!(*tail)->inline_callee?tail:NULL;
}
static int32_t body_index_constant(uint32_t bits,Type t)
{
    return t.is_unsigned?(int32_t)(uint16_t)bits:(int16_t)bits;
}
static int body_index_interval(Expr *test,Symbol *index,int32_t *first,int32_t *limit)
{
    Expr *left,*right;
    uint32_t bits;
    int32_t bound;
    int op;
    Type t;
    if(!test||test->kind!=EX_BINARY)return 0;
    op=test->op;left=test->left;right=test->right;
    if(op==TOK_LAND)return body_index_interval(left,index,first,limit)&&
                          body_index_interval(right,index,first,limit);
    if(right->kind==EX_OBJECT&&right->symbol==index){
        Expr *swap=left;left=right;right=swap;
        if(op=='<'||op==TOK_LE)op=op=='<'?'>':TOK_GE;
        else if(op=='>'||op==TOK_GE)op=op=='>'?'<':TOK_LE;
    }
    t=common_type(left->type,right->type);
    if(left->kind!=EX_OBJECT||left->symbol!=index||!word_integer(t)||
       t.is_unsigned!=index->type.is_unsigned||!integer_constant(right,&bits))return 0;
    bound=body_index_constant(bits,t);
    if(op=='>'||op==TOK_GE||op==TOK_EQ){
        int32_t lo=bound+(op=='>');if(lo>*first)*first=lo;
    }
    if(op=='<'||op==TOK_LE||op==TOK_EQ){
        int32_t hi=bound+(op!='<');if(hi<*limit)*limit=hi;
    }
    return op=='>'||op==TOK_GE||op=='<'||op==TOK_LE||op==TOK_EQ;
}
/* A stable equality can select at most one iteration of a contiguous range */
static int body_counted_index_match(Statement *loop,Statement *guard,Symbol *index,int32_t first,int32_t end)
{
    Expr *test=guard->expression,*match,*counter,*distance,*range;
    Type word=type(TY_INT,0);
    word.is_unsigned=1;
    if(cg.parser->no_loop_unroll||!test||test->kind!=EX_BINARY||test->op!=TOK_EQ||
       body_has_continue(guard->body)||body_asm_statements(cg.function->body))return 0;
    counter=test->left;match=test->right;
    if(counter->kind!=EX_OBJECT||counter->symbol!=index){counter=test->right;match=test->left;}
    if(counter->kind!=EX_OBJECT||counter->symbol!=index||match->kind!=EX_OBJECT||
       match->symbol==index||!same_type(unqualified_value(match->type),unqualified_value(counter->type))||
       !body_private(match->symbol)||scalar_writes(guard->body,match->symbol))return 0;
    distance=convert(body_clone(match),word);
    if(first){
        Expr *subtract=new_expr(EX_BINARY,test->location,word);
        subtract->op='-';subtract->left=distance;
        subtract->right=body_literal(word,(uint32_t)first,test->location);
        distance=subtract;
    }
    range=new_expr(EX_BINARY,test->location,type(TY_INT,0));
    range->op='<';range->left=distance;range->right=body_literal(word,(uint32_t)(end-first),test->location);
    scalar_replace(guard->body,index,match);
    free_expression(test);guard->expression=range;
    if(loop_observed_outside(cg.function->body,loop,index)){
        Statement *exit=body_statement(ST_EXPR,loop->location);
        Expr *store=new_expr(EX_ASSIGN,loop->location,index->type);
        store->left=body_object(index,loop->location);
        store->right=body_literal(index->type,(uint32_t)end,loop->location);
        exit->expression=store;guard->next=exit;
    }
    return 1;
}
/* A constant guard on a private induction value can narrow the trip range.
 * Preserve the active iterations in order, including any volatile accesses. */
static void body_clip_counted_loop(Statement *s)
{
    Expr *start,*test=s->expression;
    Symbol *index=s->step->left->symbol;
    Statement *initial=body_single(s->initial),**arm=&s->body,*guard;
    uint32_t bits;
    int32_t first,limit,end;
    Type compare=index->type;
    if(cg.function->jump_label_count||!body_private(index)||!test||test->op!='<'||
       !initial||initial->next||initial->kind!=ST_EXPR||!(start=initial->expression)||
       start->kind!=EX_ASSIGN||start->op||start->left->kind!=EX_OBJECT||start->left->symbol!=index||
       !integer_constant(start->right,&bits))return;
    first=body_index_constant(bits,index->type);
    limit=index->type.is_unsigned?65536:32768;
    if(!body_index_interval(test,index,&first,&limit)||first>=limit)return;
    end=limit;
    while(*arm&&(*arm)->kind==ST_BLOCK&&!(*arm)->next&&!(*arm)->inline_callee)arm=&(*arm)->body;
    guard=*arm;
    if(!guard||guard->next||guard->kind!=ST_IF||guard->alternate||guard->inline_callee||
       scalar_writes(guard->body,index)||contains_break(guard->body))return;
    if(!body_index_interval(guard->expression,index,&first,&limit)){
        if(body_counted_index_match(s,guard,index,body_index_constant(bits,index->type),end)){
            *arm=NULL;
            free_statements(s->initial);
            s->initial=NULL;
            body_install_loop_actions(s,guard);
        }
        return;
    }
    if(first>=limit)first=limit=end;
    /* The header sees only the clipped interval and its one-past value */
    if(first>=0)compare.is_unsigned=1;
    free_expression(start->right);start->right=body_literal(index->type,(uint32_t)first,start->location);
    free_expression(test->right);test->right=body_literal(compare,(uint32_t)limit,test->location);
    *arm=guard->body;guard->body=NULL;free_statements(guard);
    if(limit!=end&&loop_observed_outside(cg.function->body,s,index)){
        Statement *exit=body_statement(ST_EXPR,s->location);
        exit->expression=body_clone(start);
        free_expression(exit->expression->right);
        exit->expression->right=body_literal(index->type,(uint32_t)end,s->location);
        exit->next=s->next;s->next=exit;
    }
}
static int body_effect_free_counted(Statement *s,Statement *loop,Symbol *index,int integer_only)
{
    for(;s;s=s->next){
        Expr *e=s->expression;
        if(s->kind==ST_BLOCK||s->kind==ST_IF){
            if((s->kind==ST_IF&&!literal_integer_tree(e))||
               !body_effect_free_counted(s->body,loop,index,integer_only)||
               !body_effect_free_counted(s->alternate,loop,index,integer_only))return 0;
        }
        else if(s->kind!=ST_EMPTY){
            if(s->kind!=ST_EXPR)return 0;
            if(!body_effect(e)&&(!integer_only||literal_integer_tree(e)))continue;
            /* Inlined return values can flow through several dead locals */
            if(e->kind!=EX_ASSIGN||e->op||e->left->kind!=EX_OBJECT||volatile_expression(e)||
               e->left->symbol==index||!loop_private(e->left->symbol)||body_effect(e->right)||
               (integer_only&&!literal_integer_tree(e->right))||
               loop_observed_outside(cg.function->body,loop,e->left->symbol))return 0;
        }
    }
    return 1;
}
static int body_binary32_integer(Expr *e,int32_t *value)
{
    Expr literal;
    double number;
    e=binary32_compare_operand(e,type(TY_FLOAT,0),&literal);
    if(e->kind!=EX_INT||e->type.base!=TY_FLOAT||e->type.pointers)return 0;
    number=initializer_float(e->value,e->type);
    if(!(number>=-16777216.0&&number<=16777216.0))return 0;
    *value=(int32_t)number;
    return number==*value;
}
/* Binary32 represents every integer in this interval exactly. When the
 * body has no effects, only the final value of the private counter matters. */
static void body_fold_binary32_counted(Statement *s)
{
    Statement *init;
    Expr *step=s->step,*test=s->expression,*start,*left,*right;
    Symbol *index;
    int32_t first,bound,delta,distance,stride,last;
    int op,ascending;
    if(cg.function->jump_label_count||!step||step->type.base!=TY_FLOAT||step->type.pointers||
       !step->left||step->left->kind!=EX_OBJECT||!test||test->kind!=EX_BINARY)return;
    index=step->left->symbol;
    if(object_volatile(index->type)||!loop_private(index))return;
    if(step->kind==EX_PRE||step->kind==EX_POST)delta=step->op==TOK_INC?1:-1;
    else if(step->kind==EX_ASSIGN&&(step->op=='+'||step->op=='-')&&
            body_binary32_integer(step->right,&delta)){
        if(step->op=='-')delta=-delta;
    }else return;
    op=test->op;left=test->left;right=test->right;
    if(op!='<'&&op!=TOK_LE&&op!='>'&&op!=TOK_GE)return;
    if(right->kind==EX_OBJECT&&right->symbol==index){
        Expr *swap=left;left=right;right=swap;op=reverse_order(op);
    }
    ascending=op=='<'||op==TOK_LE;
    if(left->kind!=EX_OBJECT||left->symbol!=index||
       !body_binary32_integer(right,&bound))return;
    init=body_single(s->initial);
    if(!init||init->next||init->kind!=ST_EXPR||!(start=init->expression)||
       start->kind!=EX_ASSIGN||start->op||start->left->kind!=EX_OBJECT||start->left->symbol!=index||
       !body_binary32_integer(start->right,&first)||find_symbol(cg.parser,"$basic_asm")||
       !body_effect_free_counted(s->body,s,index,0))return;
    distance=(ascending?bound-first:first-bound)+(op==TOK_LE||op==TOK_GE);
    if(distance>0){
        stride=ascending?delta:-delta;
        if(stride<=0)return;
        last=first+((distance+stride-1)/stride)*delta;
        if(last<-16777216||last>16777216)return;
        free_expression(start->right);
        start->right=body_literal(index->type,initializer_float_bits((float)last,start->location),start->location);
    }
    body_install_loop_actions(s,NULL);
}
/* Use the same form for equivalent counting loops. Keep each update on the
 * same side of a continue, a volatile access, or any other side effect. */
/* A zero-based loop that increments another word has one update per trip */
static void body_counted_increment(Statement *s)
{
    Statement *initial=body_single(s->initial),*body=body_single(s->body);
    Expr *test=s->expression,*step=s->step,*init,*increment,*bound;
    Symbol *index,*total;
    uint32_t start;
    if(cg.parser->no_loop_unroll||cg.function->jump_label_count||s->kind!=ST_FOR||
       !initial||initial->next||initial->kind!=ST_EXPR||!body||body->next||body->kind!=ST_EXPR||
       !(init=initial->expression)||init->kind!=EX_ASSIGN||init->op||init->left->kind!=EX_OBJECT||
       !integer_constant(init->right,&start)||start)return;
    index=init->left->symbol;
    if(!word_integer(index->type)||index->type.is_bool||!body_private(index)||!body_unit_step(step,index)||
       !body_counted_test(test,index)||test->op!='<'||(bound=test->right)->kind!=EX_OBJECT||
       !same_type(unqualified_value(bound->type),unqualified_value(index->type))||
       bound->symbol==index||body_effect(bound))return;
    increment=body->expression;
    if(!increment||(increment->kind!=EX_PRE&&increment->kind!=EX_POST)||increment->op!=TOK_INC||
       increment->left->kind!=EX_OBJECT||volatile_expression(increment))return;
    total=increment->left->symbol;
    if(total==index||total==bound->symbol||!word_integer(total->type)||total->type.is_bool)return;
    Statement *guard=body_statement(ST_IF,s->location);
    Expr *positive=new_expr(EX_BINARY,test->location,type(TY_INT,0));
    positive->op='>';positive->left=body_clone(bound);positive->right=body_literal(bound->type,0,bound->location);
    guard->expression=positive;
    guard->body=body_statement(ST_EXPR,increment->location);
    Expr *add=body_clone(increment);
    add->kind=EX_ASSIGN;add->op='+';add->right=body_clone(bound);
    guard->body->expression=add;
    if(loop_observed_outside(cg.function->body,s,index)){
        Statement *finish=body_statement(ST_EXPR,init->location);
        finish->expression=body_clone(init);
        free_expression(finish->expression->right);
        finish->expression->right=body_clone(bound);
        guard->body->next=finish;
    }
    body_install_loop_actions(s,guard);
}
static void body_counted_loops(Statement **head)
{
    for(;*head;head=&(*head)->next){
        Statement *s=*head,*guard=s->next,*loop,*initial=s;Statement **tail;
        Expr *init,*test;uint32_t zero;
        while(initial&&initial->kind==ST_BLOCK&&!initial->inline_callee&&(initial==s||!initial->next))
            initial=initial->body;
        /* From zero, an unsigned j < n enters exactly when n is nonzero */
        if(!cg.function->jump_label_count&&initial&&!initial->inline_callee&&initial->kind==ST_EXPR&&
           (initial==s||!initial->next)&&(init=initial->expression)&&
           init->kind==EX_ASSIGN&&!init->op&&init->left->kind==EX_OBJECT&&
           body_private(init->left->symbol)&&integer_constant(init->right,&zero)&&!zero&&
           guard&&guard->kind==ST_IF&&!guard->alternate&&!guard->inline_callee&&
           (loop=body_single(guard->body))&&loop->kind==ST_DO&&!loop->next&&
           !body_has_inline_region(guard->body)&&!body_has_continue(loop->body)&&
           body_counted_test(test=loop->expression,init->left->symbol)&&test->op=='<'&&
           test->right->kind==EX_OBJECT&&test->right->symbol!=init->left->symbol&&
           common_type(test->left->type,test->right->type).is_unsigned&&
           reg_width(common_type(test->left->type,test->right->type))==2&&
           body_equal(guard->expression,test->right)&&
           (tail=body_counted_tail(loop))&&body_counted_step((*tail)->expression)&&
           (*tail)->expression->left->symbol==init->left->symbol){
            Statement *last=*tail;
            *tail=NULL;loop->step=last->expression;free(last);
            loop->kind=ST_FOR;loop->initial=s;s->next=NULL;
            loop->next=guard->next;guard->next=NULL;
            /* Detach the loop from the guard's optional braces before freeing them */
            {Statement **inner=&guard->body;while(*inner!=loop)inner=&(*inner)->body;*inner=NULL;}
            free_statements(guard);*head=s=loop;
        }
        body_counted_loops(&s->initial);body_counted_loops(&s->body);body_counted_loops(&s->alternate);
        if(s->kind==ST_FOR)body_fold_binary32_counted(s);
        if(s->kind==ST_FOR)body_counted_increment(s);
        if(s->kind==ST_FOR&&body_counted_step(s->step)&&body_counted_test(s->expression,s->step->left->symbol))
            body_clip_counted_loop(s);
        if(s->kind==ST_WHILE&&(tail=body_counted_tail(s))&&!body_has_continue(s->body)&&
           body_counted_step((*tail)->expression)&&body_counted_test(s->expression,(*tail)->expression->left->symbol)){
            s->kind=ST_FOR;s->step=(*tail)->expression;(*tail)->expression=NULL;(*tail)->kind=ST_EMPTY;
        }
    }
}
/* Replace a loop-local pointer initialized from a fixed array and an unchanged
 * private index with its address expression. This exposes indexed operands to
 * the retained-loop selector while preserving any later pointer observations. */
static void body_loop_element_aliases(Function *f,Statement *s)
{
    for(;s;s=s->next){
        Statement *first,*definition;Expr *assignment,*address,*index_expr;Symbol *pointer,*index;unsigned a,b;
        body_loop_element_aliases(f,s->initial);
        body_loop_element_aliases(f,s->body);
        body_loop_element_aliases(f,s->alternate);
        if(s->kind!=ST_FOR||!s->body||s->body->kind!=ST_BLOCK||!s->expression||
           s->expression->kind!=EX_BINARY||s->expression->left->kind!=EX_OBJECT)continue;
        index=s->expression->left->symbol;first=s->body->body;
        while(first&&first->kind==ST_BLOCK&&!first->next)first=first->body;
        if(index->owner!=f->id||index->type.array||object_volatile(index->type)||
           scalar_writes(s->body,index)||!first)continue;
        definition=first;
        while(definition&&definition->kind==ST_BLOCK){
            definition=definition->body;
            if(definition&&definition->next){definition=NULL;break;}
        }
        if(!definition||definition->kind!=ST_EXPR)continue;
        assignment=definition->expression;
        if(!assignment||assignment->kind!=EX_ASSIGN||assignment->op||
           assignment->left->kind!=EX_OBJECT)continue;
        pointer=assignment->left->symbol;address=assignment->right;
        if(f->jump_label_count||!pointer->type.pointers||far_pointer(pointer->type)||!loop_private(pointer)||
           object_volatile(pointer->type)||body_cursor_written(first->next,NULL,pointer)||
           loop_observed_outside(f->body,s,pointer)||loop_mentions(s->expression,pointer)||
           loop_mentions(s->step,pointer)||loop_observed_outside(s->initial,NULL,pointer))continue;
        if(!same_type(pointer->type,assignment->right->type))continue;
        if(address->kind==EX_ADDRESS&&address->left->kind==EX_DEREF)address=address->left->left;
        if(address->kind!=EX_BINARY||address->op!='+'||address->left->kind!=EX_OBJECT||
           !address->left->type.array||address->left->symbol->owner||address->left->type.banked||
           body_effect(address))continue;
        index_expr=address->right;
        if(!retained_affine_for(index_expr,index,&a,&b)||a!=1||b!=0)continue;
        definition->expression=NULL;
        a=loop_escapes(f->body,index);
        definition->expression=assignment;
        if(a)continue;
        body_cursor_substitute(first->next,NULL,pointer,address);
        free_expression(definition->expression);definition->expression=NULL;definition->kind=ST_EMPTY;
    }
}
enum { BODY_FAR_VALUE = 0, BODY_FAR_PTR = 1, BODY_FAR_TRUTH = 2, BODY_FAR_DISCARD = 3 };
static int body_asm_expr(Expr *e)
{
    unsigned i;
    if(!e)return 0;
    if(e->kind==EX_CALL&&e->symbol&&!strcmp(e->symbol->name,"$basic_asm"))return 1;
    if(body_asm_expr(e->left)||body_asm_expr(e->right)||body_asm_expr(e->third))return 1;
    for(i=0;i<e->arg_count;++i)if(body_asm_expr(e->args[i]))return 1;
    return 0;
}
static int body_asm_statements(Statement *s)
{
    for(;s;s=s->next)if(body_asm_expr(s->expression)||body_asm_expr(s->step)||
        body_asm_statements(s->initial)||body_asm_statements(s->body)||body_asm_statements(s->alternate))return 1;
    return 0;
}
static int body_near_far_source(Expr *e,const unsigned char *live,int allow_null)
{
    Type t;
    if(!e)return 0;
    if(e->kind==EX_INT)return allow_null&&!e->value;
    t=value_type(e->type);
    if(e->kind==EX_OBJECT){
        if(far_pointer(t))return live&&live[body_symbol(e->symbol)]!=0;
        return t.pointers!=0;
    }
    if(e->kind==EX_ADDRESS)return !far_pointer(t);
    if(e->kind==EX_CAST){
        if(!t.pointers)return 0;
        if(!far_pointer(t))return 1;
        return body_near_far_source(e->left,live,allow_null);
    }
    if(e->kind==EX_BINARY&&(e->op=='+'||e->op=='-')&&t.pointers){
        if(value_type(e->left->type).pointers&&!value_type(e->right->type).pointers)
            return body_near_far_source(e->left,live,0);
        if(e->op=='+'&&value_type(e->right->type).pointers&&!value_type(e->left->type).pointers)
            return body_near_far_source(e->right,live,0);
        return 0;
    }
    if(e->kind==EX_CHOOSE)
        return body_near_far_source(e->right,live,allow_null)&&body_near_far_source(e->third,live,allow_null);
    if(e->kind==EX_ASSIGN&&(!e->op||e->op=='+'||e->op=='-')&&
       e->left->kind==EX_OBJECT&&live&&live[body_symbol(e->left->symbol)]){
        if(!e->op)return body_near_far_source(e->right,live,allow_null);
        return 1;
    }
    if((e->kind==EX_PRE||e->kind==EX_POST)&&e->left->kind==EX_OBJECT&&live&&live[body_symbol(e->left->symbol)])
        return 1;
    return 0;
}
static void body_far_expr_check(Expr *e,unsigned char *live,int ctx,int lvalue_addr,unsigned *uses,int *changed)
{
    unsigned i;
    if(!e)return;
    switch(e->kind){
    case EX_INT:case EX_STRING:case EX_VA_START:case EX_RESULT_ADDR:
        return;
    case EX_OBJECT:
        i=body_symbol(e->symbol);
        if(live[i]){
            if(lvalue_addr||ctx==BODY_FAR_VALUE){live[i]=0;*changed=1;}
            else ++uses[i];
        }
        return;
    case EX_ADDRESS:
        body_far_expr_check(e->left,live,(ctx==BODY_FAR_PTR||ctx==BODY_FAR_DISCARD)?ctx:BODY_FAR_VALUE,1,uses,changed);
        return;
    case EX_DEREF:
        if(!lvalue_addr&&!e->type.array&&!structure_object(e->type))
            body_far_expr_check(e->left,live,BODY_FAR_PTR,0,uses,changed);
        else
            body_far_expr_check(e->left,live,ctx==BODY_FAR_PTR&&!lvalue_addr&&!e->type.array?BODY_FAR_PTR:BODY_FAR_VALUE,0,uses,changed);
        return;
    case EX_MEMBER:
        if(e->op==TOK_ARROW){
            int child_ctx=(!lvalue_addr&&!e->type.array&&(!structure_object(e->type)||ctx==BODY_FAR_PTR))?BODY_FAR_PTR:BODY_FAR_VALUE;
            body_far_expr_check(e->left,live,child_ctx,0,uses,changed);
        }else{
            int child_ctx=(!lvalue_addr&&!e->type.array&&(!structure_object(e->type)||ctx==BODY_FAR_PTR))?BODY_FAR_PTR:BODY_FAR_VALUE;
            body_far_expr_check(e->left,live,child_ctx,lvalue_addr,uses,changed);
        }
        return;
    case EX_CAST:
        {
            Type to=value_type(e->type);
            if(!to.pointers&&!to.array&&to.base!=TY_FLOAT&&(to.is_bool||reg_width(to)<=2)){
                Expr *in=e->left;
                while(in->kind==EX_CAST&&!in->type.pointers&&!in->type.array&&in->type.base!=TY_FLOAT&&reg_width(in->type)==4)
                    in=in->left;
                body_far_expr_check(in,live,to.is_bool?BODY_FAR_TRUTH:BODY_FAR_PTR,0,uses,changed);
                return;
            }
            if(to.pointers&&!far_pointer(to)){
                body_far_expr_check(e->left,live,ctx==BODY_FAR_DISCARD?BODY_FAR_DISCARD:BODY_FAR_PTR,0,uses,changed);
                return;
            }
            if(to.pointers&&far_pointer(to)&&value_type(e->left->type).pointers&&far_pointer(value_type(e->left->type))){
                body_far_expr_check(e->left,live,ctx,0,uses,changed);
                return;
            }
            body_far_expr_check(e->left,live,BODY_FAR_VALUE,0,uses,changed);
            return;
        }
    case EX_UNARY:
        body_far_expr_check(e->left,live,e->op=='!'?BODY_FAR_TRUTH:BODY_FAR_VALUE,0,uses,changed);
        return;
    case EX_BINARY:
        if((e->op=='+'||e->op=='-')&&value_type(e->type).pointers){
            int ok=(ctx==BODY_FAR_PTR||ctx==BODY_FAR_DISCARD);
            if(value_type(e->left->type).pointers&&!value_type(e->right->type).pointers){
                body_far_expr_check(e->left,live,ok?ctx:BODY_FAR_VALUE,0,uses,changed);
                body_far_expr_check(e->right,live,BODY_FAR_VALUE,0,uses,changed);
            }else if(e->op=='+'&&value_type(e->right->type).pointers&&!value_type(e->left->type).pointers){
                body_far_expr_check(e->left,live,BODY_FAR_VALUE,0,uses,changed);
                body_far_expr_check(e->right,live,ok?ctx:BODY_FAR_VALUE,0,uses,changed);
            }else{
                body_far_expr_check(e->left,live,BODY_FAR_VALUE,0,uses,changed);
                body_far_expr_check(e->right,live,BODY_FAR_VALUE,0,uses,changed);
            }
            return;
        }
        if(e->op==TOK_EQ||e->op==TOK_NE){
            if(e->left->kind==EX_INT&&!e->left->value){body_far_expr_check(e->right,live,BODY_FAR_TRUTH,0,uses,changed);return;}
            if(e->right->kind==EX_INT&&!e->right->value){body_far_expr_check(e->left,live,BODY_FAR_TRUTH,0,uses,changed);return;}
            if(value_type(e->left->type).pointers&&value_type(e->right->type).pointers&&
               body_near_far_source(e->left,live,1)&&body_near_far_source(e->right,live,1)){
                body_far_expr_check(e->left,live,BODY_FAR_PTR,0,uses,changed);
                body_far_expr_check(e->right,live,BODY_FAR_PTR,0,uses,changed);
                return;
            }
        }
        if(e->op==TOK_LAND||e->op==TOK_LOR){
            body_far_expr_check(e->left,live,BODY_FAR_TRUTH,0,uses,changed);
            body_far_expr_check(e->right,live,BODY_FAR_TRUTH,0,uses,changed);
            return;
        }
        body_far_expr_check(e->left,live,BODY_FAR_VALUE,0,uses,changed);
        body_far_expr_check(e->right,live,BODY_FAR_VALUE,0,uses,changed);
        return;
    case EX_ASSIGN:
        if(e->left->kind==EX_OBJECT&&live[body_symbol(e->left->symbol)]){
            unsigned s=body_symbol(e->left->symbol);
            int valid_ctx=(ctx==BODY_FAR_DISCARD||ctx==BODY_FAR_PTR||(!e->op&&ctx==BODY_FAR_TRUTH));
            if(!valid_ctx||(e->op&&e->op!='+'&&e->op!='-')||
               (!e->op&&!body_near_far_source(e->right,live,1))){
                live[s]=0;*changed=1;
                body_far_expr_check(e->right,live,BODY_FAR_VALUE,0,uses,changed);
            }else if(!e->op){
                body_far_expr_check(e->right,live,BODY_FAR_PTR,0,uses,changed);
            }else{
                body_far_expr_check(e->right,live,BODY_FAR_VALUE,0,uses,changed);
            }
            return;
        }
        if((e->left->kind==EX_DEREF||e->left->kind==EX_MEMBER)&&!e->left->type.array&&!structure_object(e->left->type))
            body_far_expr_check(e->left,live,BODY_FAR_PTR,0,uses,changed);
        else
            body_far_expr_check(e->left,live,BODY_FAR_VALUE,0,uses,changed);
        body_far_expr_check(e->right,live,BODY_FAR_VALUE,0,uses,changed);
        return;
    case EX_PRE:case EX_POST:
        if(e->left->kind==EX_OBJECT&&live[body_symbol(e->left->symbol)]){
            unsigned s=body_symbol(e->left->symbol);
            if(ctx!=BODY_FAR_DISCARD&&ctx!=BODY_FAR_PTR){live[s]=0;*changed=1;}
            return;
        }
        if((e->left->kind==EX_DEREF||e->left->kind==EX_MEMBER)&&!e->left->type.array&&!structure_object(e->left->type))
            body_far_expr_check(e->left,live,BODY_FAR_PTR,0,uses,changed);
        else
            body_far_expr_check(e->left,live,BODY_FAR_VALUE,0,uses,changed);
        return;
    case EX_CHOOSE:
        body_far_expr_check(e->left,live,BODY_FAR_TRUTH,0,uses,changed);
        body_far_expr_check(e->right,live,ctx,0,uses,changed);
        body_far_expr_check(e->third,live,ctx,0,uses,changed);
        return;
    case EX_COMMA:
        body_far_expr_check(e->left,live,BODY_FAR_DISCARD,0,uses,changed);
        body_far_expr_check(e->right,live,ctx,0,uses,changed);
        return;
    default:
        body_far_expr_check(e->left,live,BODY_FAR_VALUE,0,uses,changed);
        body_far_expr_check(e->right,live,BODY_FAR_VALUE,0,uses,changed);
        body_far_expr_check(e->third,live,BODY_FAR_VALUE,0,uses,changed);
        for(i=0;i<e->arg_count;++i)body_far_expr_check(e->args[i],live,BODY_FAR_VALUE,0,uses,changed);
        return;
    }
}
static void body_far_stmt_check(Statement *s,unsigned char *live,unsigned *uses,int *changed)
{
    for(;s;s=s->next){
        int cond=(s->kind==ST_IF||s->kind==ST_WHILE||s->kind==ST_DO||s->kind==ST_FOR);
        body_far_expr_check(s->expression,live,s->kind==ST_EXPR?BODY_FAR_DISCARD:cond?BODY_FAR_TRUTH:BODY_FAR_VALUE,0,uses,changed);
        body_far_expr_check(s->step,live,BODY_FAR_DISCARD,0,uses,changed);
        body_far_stmt_check(s->initial,live,uses,changed);
        body_far_stmt_check(s->body,live,uses,changed);
        body_far_stmt_check(s->alternate,live,uses,changed);
    }
}
static Type body_near_pointer_type(Type t)
{
    t=value_type(t);
    t.far_pointers&=~pointer_bit(t.pointers);
    return t;
}
static void body_unwrap_near_expr(Expr **at,Type target)
{
    Expr *e=*at;
    if(!e)return;
    if(e->kind==EX_INT&&!e->value){e->type=target;return;}
    if(e->kind==EX_CAST){
        if(!far_pointer(value_type(e->type)))return;
        if(e->left->kind==EX_INT&&!e->left->value){
            Expr *z=e->left;e->left=NULL;free_expression(e);z->type=target;*at=z;return;
        }
        if(!far_pointer(value_type(e->left->type))&&value_type(e->left->type).pointers){
            if(!e->left->type.array&&same_type(unqualified_value(e->left->type),unqualified_value(target))&&
               !(e->left->kind==EX_OBJECT&&e->left->symbol->dpage&&!e->left->symbol->owner)){
                Expr *inner=e->left;e->left=NULL;free_expression(e);*at=inner;
            }else e->type=target;
            return;
        }
        if(far_pointer(value_type(e->left->type))){
            body_unwrap_near_expr(&e->left,target);
            if(!far_pointer(value_type(e->left->type))){
                Expr *inner=e->left;e->left=NULL;free_expression(e);*at=inner;
            }
            return;
        }
    }
    if(e->kind==EX_BINARY&&(e->op=='+'||e->op=='-')){
        if(value_type(e->left->type).pointers&&!value_type(e->right->type).pointers){
            Type pt=body_near_pointer_type(e->left->type);
            body_unwrap_near_expr(&e->left,pt);
            e->type=pt;
        }else if(e->op=='+'&&value_type(e->right->type).pointers&&!value_type(e->left->type).pointers){
            Type pt=body_near_pointer_type(e->right->type);
            body_unwrap_near_expr(&e->right,pt);
            e->type=pt;
        }
        return;
    }
    if(e->kind==EX_CHOOSE){
        body_unwrap_near_expr(&e->right,target);
        body_unwrap_near_expr(&e->third,target);
        e->type=target;
    }
}
static int body_near_truth_cast(Expr *e)
{
    if(!e)return 0;
    if(e->kind==EX_INT)return !e->value;
    if(e->kind==EX_OBJECT)return value_type(e->type).pointers&&!far_pointer(value_type(e->type));
    if(e->kind==EX_ADDRESS)return !far_pointer(value_type(e->type));
    if(e->kind==EX_CAST){
        Type t=value_type(e->type);
        if(!t.pointers)return 0;
        if(!far_pointer(t))return 1;
        return body_near_truth_cast(e->left);
    }
    if(e->kind==EX_CHOOSE)return body_near_truth_cast(e->right)&&body_near_truth_cast(e->third);
    return 0;
}
static void body_narrow_far_truth(Expr **at)
{
    Expr *e=*at;
    if(!e)return;
    if(far_pointer(value_type(e->type))&&body_near_truth_cast(e))
        body_unwrap_near_expr(at,body_near_pointer_type(e->type));
}
static void body_narrow_far_expr(Expr **at,const unsigned char *live,int lvalue_addr)
{
    Expr *e=*at;
    int was_left_far,was_left_banked,deref_addr;
    unsigned i;
    if(!e)return;
    if(e->kind==EX_OBJECT){
        if(live[body_symbol(e->symbol)])e->type=e->symbol->type;
        return;
    }
    was_left_far=e->left?far_pointer(value_type(e->left->type)):0;
    was_left_banked=e->left?e->left->type.banked:0;
    deref_addr=e->kind==EX_ADDRESS;
    body_narrow_far_expr(&e->left,live,deref_addr);
    body_narrow_far_expr(&e->right,live,0);
    body_narrow_far_expr(&e->third,live,0);
    for(i=0;i<e->arg_count;++i)body_narrow_far_expr(&e->args[i],live,0);
    if(e->kind==EX_DEREF){
        if(was_left_far&&!far_pointer(value_type(e->left->type)))e->type.banked=0;
        if(!lvalue_addr&&!e->type.array&&!structure_object(e->type)&&
           far_pointer(value_type(e->left->type))&&body_near_far_source(e->left,NULL,0)){
            body_unwrap_near_expr(&e->left,body_near_pointer_type(e->left->type));
            e->type.banked=0;
        }
    }else if(e->kind==EX_MEMBER){
        if(e->op==TOK_ARROW){
            if(was_left_far&&!far_pointer(value_type(e->left->type)))e->type.banked=0;
            if(!lvalue_addr&&!e->type.array&&!structure_object(e->type)&&
               far_pointer(value_type(e->left->type))&&body_near_far_source(e->left,NULL,0)){
                body_unwrap_near_expr(&e->left,body_near_pointer_type(e->left->type));
                e->type.banked=0;
            }
        }else if(was_left_banked&&!e->left->type.banked)e->type.banked=0;
    }else if(e->kind==EX_BINARY){
        if((e->op=='+'||e->op=='-')&&far_pointer(e->type)){
            if(value_type(e->left->type).pointers&&!far_pointer(value_type(e->left->type))&&!value_type(e->right->type).pointers)
                e->type=value_type(e->left->type);
            else if(e->op=='+'&&value_type(e->right->type).pointers&&!far_pointer(value_type(e->right->type))&&!value_type(e->left->type).pointers)
                e->type=value_type(e->right->type);
        }else if(e->op==TOK_EQ||e->op==TOK_NE){
            if(e->left->kind==EX_INT&&!e->left->value&&far_pointer(value_type(e->right->type))&&body_near_truth_cast(e->right))
                body_narrow_far_truth(&e->right);
            if(e->right->kind==EX_INT&&!e->right->value&&far_pointer(value_type(e->left->type))&&body_near_truth_cast(e->left))
                body_narrow_far_truth(&e->left);
            if(e->left->kind==EX_INT&&!e->left->value&&far_pointer(e->left->type)&&
               value_type(e->right->type).pointers&&!far_pointer(value_type(e->right->type)))
                e->left->type=value_type(e->right->type);
            if(e->right->kind==EX_INT&&!e->right->value&&far_pointer(e->right->type)&&
               value_type(e->left->type).pointers&&!far_pointer(value_type(e->left->type)))
                e->right->type=value_type(e->left->type);
            if(value_type(e->left->type).pointers&&!far_pointer(value_type(e->left->type))&&
               far_pointer(value_type(e->right->type))&&body_near_far_source(e->right,NULL,1))
                body_unwrap_near_expr(&e->right,body_near_pointer_type(e->left->type));
            if(value_type(e->right->type).pointers&&!far_pointer(value_type(e->right->type))&&
               far_pointer(value_type(e->left->type))&&body_near_far_source(e->left,NULL,1))
                body_unwrap_near_expr(&e->left,body_near_pointer_type(e->right->type));
        }else if(e->op==TOK_LAND||e->op==TOK_LOR){
            body_narrow_far_truth(&e->left);
            body_narrow_far_truth(&e->right);
        }
    }else if(e->kind==EX_UNARY&&e->op=='!'){
        body_narrow_far_truth(&e->left);
    }else if(e->kind==EX_ADDRESS){
        if(far_pointer(value_type(e->type))&&was_left_banked&&!e->left->type.banked)
            e->type.far_pointers&=~pointer_bit(e->type.pointers);
    }else if(e->kind==EX_CAST){
        if(e->type.is_bool)body_narrow_far_truth(&e->left);
        if(far_pointer(value_type(e->type))&&was_left_far&&value_type(e->left->type).pointers&&!far_pointer(value_type(e->left->type)))
            e->type.far_pointers&=~pointer_bit(e->type.pointers);
    }else if(e->kind==EX_CHOOSE){
        body_narrow_far_truth(&e->left);
        if(far_pointer(value_type(e->type))&&
           value_type(e->right->type).pointers&&!far_pointer(value_type(e->right->type))&&
           value_type(e->third->type).pointers&&!far_pointer(value_type(e->third->type)))
            e->type.far_pointers&=~pointer_bit(e->type.pointers);
    }else if((e->kind==EX_ASSIGN||e->kind==EX_PRE||e->kind==EX_POST)&&
             e->left->kind==EX_OBJECT&&live[body_symbol(e->left->symbol)]){
        e->type=e->left->symbol->type;
        if(e->kind==EX_ASSIGN&&!e->op)body_unwrap_near_expr(&e->right,e->left->symbol->type);
    }
}
static void body_narrow_far_statements(Statement *s,const unsigned char *live)
{
    for(;s;s=s->next){
        int cond=(s->kind==ST_IF||s->kind==ST_WHILE||s->kind==ST_DO||s->kind==ST_FOR);
        body_narrow_far_expr(&s->expression,live,0);
        if(cond)body_narrow_far_truth(&s->expression);
        body_narrow_far_expr(&s->step,live,0);
        body_narrow_far_statements(s->initial,live);
        body_narrow_far_statements(s->body,live);
        body_narrow_far_statements(s->alternate,live);
    }
}
static void body_narrow_far_locals(Function *f)
{
    unsigned char live[1024]={0};
    unsigned uses[1024]={0};
    unsigned i;
    int changed,any=0;
    if(body_asm_statements(f->body))return;
    for(i=0;i<cg.parser->symbol_count;++i){
        Symbol *v=&cg.parser->symbols[i];
        if(v->owner==f->id&&v->offset&&!scalar_leaf_parameter(f,v)&&!v->storage&&!v->type.array&&
           !v->type.element&&!object_volatile(v->type)&&far_pointer(value_type(v->type))&&loop_private(v)){
            live[i]=1;any=1;
        }
    }
    if(any){
        do{
            changed=0;
            memset(uses,0,sizeof uses);
            body_far_stmt_check(f->body,live,uses,&changed);
        }while(changed);
        for(i=0;i<cg.parser->symbol_count;++i)if(live[i]){
            Symbol *v=&cg.parser->symbols[i];
            v->type.far_pointers&=~pointer_bit(v->type.pointers);
            v->near_nowrap=1;
        }
    }
    body_narrow_far_statements(f->body,live);
}
/* Forward a single-use private offset into an adjacent two-register call
 * when doing so exposes a shared shift. Other arguments cannot change it. */
static void body_forward_shift_offset(Statement *s)
{
    for(;s;s=s->next){
        Statement *assignment=s,*next;
        Expr *def,*call,*right,*home;
        Expr trial;
        unsigned delta,mask;
        body_forward_shift_offset(s->initial);
        body_forward_shift_offset(s->body);
        body_forward_shift_offset(s->alternate);
        while(assignment&&assignment->kind==ST_BLOCK&&!assignment->inline_callee)
            assignment=assignment->body;
        if(!assignment||assignment->kind!=ST_EXPR||
           (assignment!=s&&assignment->next))continue;
        def=assignment->expression;
        if(!def||def->kind!=EX_ASSIGN||def->op||
           def->left->kind!=EX_OBJECT||!body_private(def->left->symbol)||
           !s->next)continue;
        next=s->next;
        if(next->kind!=ST_EXPR&&next->kind!=ST_RETURN)continue;
        call=next->expression;
        if(!call||call->kind!=EX_CALL||call->left||call->arg_count!=2||
           !call_register(call,0)||!call_register(call,1))continue;
        right=call->args[1];
        if(right->kind!=EX_BINARY||right->op!=TOK_SHR)continue;
        home=right->left;
        if(home->kind!=EX_OBJECT||
           home->symbol!=def->left->symbol||
           statement_references(cg.function->body,home->symbol)!=2)continue;
        trial=*right;trial.left=def->right;
        if(!word_shift_pair(call->args[0],&trial,&delta,&mask))continue;
        home=word_bits(def->right)->left;
        if(home->kind!=EX_OBJECT||!body_private(home->symbol))continue;
        free_expression(right->left);
        right->left=def->right;def->right=NULL;
        free_expression(def);
        assignment->kind=ST_EMPTY;assignment->expression=NULL;
    }
}

/* Place a single-use word shift at its definition. A constant shift of a
 * word can stay in A through the defining expression's join. Look only
 * through straight-line statements, so the use cannot precede its store. */
static int body_move_word_shift(Expr **at,Expr *definition)
{
    Expr *e=*at;
    uint32_t count;
    if(!e)return 0;
    if(e->kind==EX_BINARY&&e->op==TOK_SHL&&e->left->kind==EX_OBJECT&&
       e->left->symbol==definition->left->symbol&&word_integer(e->type)&&
       integer_constant(e->right,&count)&&count>0&&count<16){
        *at=e->left;
        e->left=convert(definition->right,e->type);
        definition->right=e;
        return 1;
    }
    if(e->kind==EX_BINARY&&(e->op=='|'||e->op=='^'))
        return body_move_word_shift(&e->left,definition)||body_move_word_shift(&e->right,definition);
    return 0;
}

static void body_place_word_shifts(Statement *s)
{
    for(;s;s=s->next){
        Expr *definition=s->expression;
        /* Switch lowering uses the original case and block structure */
        if(s->kind==ST_SWITCH)continue;
        if(s->body)s->body=body_flatten(s->body);
        if(s->alternate)s->alternate=body_flatten(s->alternate);
        body_place_word_shifts(s->body);
        body_place_word_shifts(s->alternate);
        if(s->kind!=ST_EXPR||!definition||definition->kind!=EX_ASSIGN||definition->op||
           definition->left->kind!=EX_OBJECT||!word_integer(definition->left->type)||
           !definition->left->type.is_unsigned||!body_private(definition->left->symbol)||
           word_bits(definition->right)->kind!=EX_CHOOSE||
           statement_references(cg.function->body,definition->left->symbol)!=2)continue;
        for(Statement *use=s->next;use;use=use->next){
            Expr **value=&use->expression;
            if(use->kind==ST_BLOCK&&!use->body)continue;
            if(use->kind!=ST_EXPR&&use->kind!=ST_RETURN)break;
            if(*value&&(*value)->kind==EX_ASSIGN&&!(*value)->op)value=&(*value)->right;
            if(body_move_word_shift(value,definition)||use->kind==ST_RETURN)break;
        }
    }
}

/* An automatic table can disappear once every use is a fixed element read.
 * Keep the initializer expressions so pointer relocations reach the emitter. */
static int body_table_reads(Expr **at,Symbol *table,Expr **values,unsigned stride,int read,int replace)
{
    Expr *e=*at;
    unsigned offset;
    if(!e)return 1;
    if(e->kind==EX_OBJECT&&e->symbol==table)return 0;
    if(read&&(e->kind==EX_MEMBER||e->kind==EX_DEREF)&&!volatile_expression(e)&&
       same_type(unqualified_value(e->type),unqualified_value(array_element(table->type)))&&
       fixed_memory_object(e,&offset)==table&&offset%stride==0&&offset/stride<table->type.array){
        if(replace){
            *at=body_clone(values[offset/stride]);
            free_expression(e);
        }
        return 1;
    }
    int read_left=e->kind==EX_DEREF||(e->kind==EX_MEMBER&&e->op==TOK_ARROW)||
        (read&&e->kind!=EX_ASSIGN&&e->kind!=EX_ADDRESS&&e->kind!=EX_PRE&&e->kind!=EX_POST);
    if(!body_table_reads(&e->left,table,values,stride,read_left,replace)||
       !body_table_reads(&e->right,table,values,stride,read,replace)||
       !body_table_reads(&e->third,table,values,stride,read,replace))return 0;
    for(unsigned i=0;i<e->arg_count;++i)
        if(!body_table_reads(&e->args[i],table,values,stride,read,replace))return 0;
    return 1;
}

static int body_table_uses(Statement *s,Symbol *table,Expr **values,unsigned stride,int replace)
{
    for(;s;s=s->next)
        if(!body_table_reads(&s->expression,table,values,stride,1,replace)||
           !body_table_reads(&s->step,table,values,stride,1,replace)||
           !body_table_uses(s->initial,table,values,stride,replace)||
           !body_table_uses(s->body,table,values,stride,replace)||
           !body_table_uses(s->alternate,table,values,stride,replace))return 0;
    return 1;
}

static int body_table_constant(Expr *e)
{
    unsigned offset;
    while(e->kind==EX_CAST&&e->type.pointers&&e->left->type.pointers&&
          far_pointer(e->type)==far_pointer(e->left->type))e=e->left;
    return !body_effect(e)&&(constant_address(e)||
        (value_type(e->type).pointers&&!far_pointer(value_type(e->type))&&near_object_address(e,&offset)));
}

static void body_remove_local(Function *f,Symbol *v)
{
    unsigned bytes=((width(v->type)+1)&~1u)+(structure_object(v->type)?2:0);
    for(unsigned i=0;i<cg.parser->symbol_count;++i){
        Symbol *other=&cg.parser->symbols[i];
        if(other->owner==f->id&&other->offset>v->offset)other->offset-=bytes;
    }
    v->offset=0;
    f->slots-=bytes;
}

static int vr_index(Expr *e);
static int body_unused_array_path(Expr *e,Symbol *array)
{
    if(e->kind==EX_OBJECT)return e->symbol==array;
    if(e->kind==EX_DEREF)return !far_pointer(value_type(e->left->type))&&body_unused_array_path(e->left,array);
    return e->kind==EX_BINARY&&e->op=='+'&&value_type(e->left->type).pointers&&
        vr_index(e->right)&&body_unused_array_path(e->left,array);
}

static int body_unused_fixed_stores(Statement *s,Symbol *home,int remove)
{
    for(;s;s=s->next){
        Expr *store=s->expression;
        unsigned offset;
        if(s->kind==ST_EXPR&&store&&store->kind==EX_ASSIGN&&!store->op&&
           !volatile_expression(store)&&body_table_constant(store->right)&&
           !expression_references(store->right,home)&&
           (fixed_memory_object(store->left,&offset)==home||
            (home->type.array&&body_unused_array_path(store->left,home)))){
            if(remove){free_expression(store);s->expression=NULL;s->kind=ST_EMPTY;}
        }else if(expression_references(store,home))return 0;
        if(expression_references(s->step,home)||!body_unused_fixed_stores(s->initial,home,remove)||
           !body_unused_fixed_stores(s->body,home,remove)||!body_unused_fixed_stores(s->alternate,home,remove))return 0;
    }
    return 1;
}

/* An aggregate with no escaping address can only observe bytes covered by
 * its direct reads. Aggregate copies observe the whole selected subobject. */
static int body_mark_fixed_reads(Expr *e,Symbol *home,unsigned char *read)
{
    unsigned offset=0,n;
    if(!e)return 1;
    /* A store through the actual array name consumes its subscript and
     * value, but does not read the destination element or publish the array. */
    if(e->kind==EX_ASSIGN&&!e->op&&e->left->kind==EX_DEREF){
        Expr *address=e->left->left;
        if(address->kind==EX_BINARY&&address->op=='+'&&address->left->kind==EX_OBJECT&&
           address->left->symbol==home&&home->type.array)
            return body_mark_fixed_reads(address->right,home,read)&&body_mark_fixed_reads(e->right,home,read);
    }
    if(e->kind==EX_ADDRESS)return !expression_references(e,home);
    if(!e->type.array&&direct_memory_object(e,&offset)==home){
        n=width(e->type);
        if(!n||offset>width(home->type)||n>width(home->type)-offset)return 0;
        memset(read+offset,1,n);
        return 1;
    }
    if(e->kind==EX_OBJECT)return e->symbol!=home;
    if(!body_mark_fixed_reads(e->left,home,read)||!body_mark_fixed_reads(e->right,home,read)||
       !body_mark_fixed_reads(e->third,home,read))return 0;
    for(unsigned i=0;i<e->arg_count;++i)
        if(!body_mark_fixed_reads(e->args[i],home,read))return 0;
    return 1;
}
/* A following unit-stride fill overwrites its covered initial bytes on
 * every path to the loop exit. Other stores may neither publish nor read
 * the array before the fill. The caller has already excluded escapes. */
static int body_overwritten_by_fill(Statement *s,Symbol *home,unsigned end)
{
    if(!home->type.array||width(array_element(home->type))!=1)return 0;
    for(;s&&(s->kind==ST_EMPTY||s->kind==ST_EXPR);s=s->next){
        if(expression_references(s->expression,home)){
            unsigned off,bytes;
            if(body_literal_store(s,&off,&bytes)!=home)return 0;
        }
    }
    if(!s||s->kind!=ST_FOR)return 0;
    Expr *test=s->expression;
    Statement *entry=body_single(s->initial),*body=s->body;
    uint32_t first,limit;
    if(!entry||entry->next||!test||test->kind!=EX_BINARY||test->op!='<'||
       test->left->kind!=EX_OBJECT||!integer_constant(test->right,&limit)||
       limit<end||limit>width(home->type)||limit>32767)return 0;
    Symbol *index=test->left->symbol;
    Expr *init=entry->expression;
    if(!body_private(index)||!word_integer(index->type)||entry->kind!=ST_EXPR||!init||
       init->kind!=EX_ASSIGN||init->op||init->left->kind!=EX_OBJECT||init->left->symbol!=index||
       !integer_constant(init->right,&first)||first||!body_unit_step(s->step,index)||
       scalar_writes(body,index)||contains_break(body)||body_has_continue(body)||
       statement_has_case(body)||statement_references(body,home)!=1)return 0;
    while(body&&body->kind==ST_BLOCK&&!body->next)body=body->body;
    for(;body;body=body->next){
        Expr *e=body->expression;
        if(body->kind!=ST_EXPR||!e||e->kind!=EX_ASSIGN||e->op||e->left->kind!=EX_DEREF||
           width(e->left->type)!=1)continue;
        Expr *addr=e->left->left;
        if(addr->kind==EX_BINARY&&addr->op=='+'&&addr->left->kind==EX_OBJECT&&
           addr->left->symbol==home&&addr->right->kind==EX_OBJECT&&addr->right->symbol==index)return 1;
    }
    return 0;
}
static int body_unread_fixed_stores(Statement *s,Symbol *home,unsigned char *read,int remove)
{
    for(;s;s=s->next){
        Expr *store=s->expression;
        unsigned offset,n;
        if(s->kind==ST_EXPR&&store&&store->kind==EX_ASSIGN&&!store->op&&
           !volatile_expression(store)&&body_table_constant(store->right)&&
           !expression_references(store->right,home)&&
           fixed_memory_object(store->left,&offset)==home&&offset<=width(home->type)&&
           (n=width(store->left->type))<=width(home->type)-offset){
            if(remove&&(!memchr(read+offset,1,n)||body_overwritten_by_fill(s->next,home,offset+n))){
                free_expression(store);s->expression=NULL;s->kind=ST_EMPTY;
            }
        }else if(!remove&&!body_mark_fixed_reads(store,home,read))return 0;
        if(!remove&&!body_mark_fixed_reads(s->step,home,read))return 0;
        if(!body_unread_fixed_stores(s->initial,home,read,remove)||
           !body_unread_fixed_stores(s->body,home,read,remove)||
           !body_unread_fixed_stores(s->alternate,home,read,remove))return 0;
    }
    return 1;
}
/* A single fixed byte initialization can reach into later loops when every
 * use of its automatic array is a direct access and no write overlaps it. */
static int body_private_byte_expression(Expr **at,Symbol *home,unsigned byte,Expr *init,int replace)
{
    Expr *e=*at;
    unsigned offset;
    if(!e||!expression_references(e,home))return 1;
    if(e->kind==EX_ASSIGN){
        if(expression_references(e->left,home)){
            if(e->op||fixed_memory_object(e->left,&offset)!=home||
               (e!=init&&offset<=byte&&byte-offset<width(e->left->type)))return 0;
        }
        return body_private_byte_expression(&e->right,home,byte,init,replace);
    }
    if(e->kind==EX_DEREF&&fixed_memory_object(e,&offset)==home){
        if(replace&&!volatile_expression(e)&&offset==byte&&same_type(e->type,init->left->type)){
            *at=body_clone(init->right);free_expression(e);
        }
        return 1;
    }
    if(e->kind==EX_OBJECT||e->kind==EX_ADDRESS||e->kind==EX_PRE||e->kind==EX_POST)return 0;
    if(!body_private_byte_expression(&e->left,home,byte,init,replace)||
       !body_private_byte_expression(&e->right,home,byte,init,replace)||
       !body_private_byte_expression(&e->third,home,byte,init,replace))return 0;
    for(unsigned i=0;i<e->arg_count;++i)
        if(!body_private_byte_expression(&e->args[i],home,byte,init,replace))return 0;
    return 1;
}
static int body_private_byte_statements(Statement *s,Symbol *home,unsigned byte,Expr *init,int replace)
{
    for(;s;s=s->next){
        Expr *discard=s->expression;
        if(s->kind==ST_EXPR&&discard&&!body_effect(discard)){
            while(discard->kind==EX_CAST)discard=discard->left;
            if(discard->kind==EX_OBJECT&&discard->symbol==home)continue;
        }
        if(!body_private_byte_expression(&s->expression,home,byte,init,replace)||
           !body_private_byte_expression(&s->step,home,byte,init,replace)||
           !body_private_byte_statements(s->initial,home,byte,init,replace)||
           !body_private_byte_statements(s->body,home,byte,init,replace)||
           !body_private_byte_statements(s->alternate,home,byte,init,replace))return 0;
    }
    return 1;
}
static void body_forward_private_bytes(Function *f,Symbol *home)
{
    if(!home->scope||home->storage||!home->type.array||width(array_element(home->type))!=1||
       f->body->kind!=ST_BLOCK)return;
    for(Statement *s=f->body->body;s;s=s->next){
        Expr *e=s->expression;
        unsigned byte;
        if(s->kind!=ST_EXPR||!s->next||!e||e->kind!=EX_ASSIGN||e->op||
           e->left->kind!=EX_DEREF||width(e->left->type)!=1||e->right->kind!=EX_INT||
           !same_type(e->left->type,e->right->type)||fixed_memory_object(e->left,&byte)!=home||
           byte>=width(home->type))continue;
        if(body_private_byte_statements(f->body,home,byte,e,0))
            body_private_byte_statements(s->next,home,byte,e,1);
    }
}
static void body_drop_unused_homes(Function *f)
{
    if(cg.parser->no_body_optimizations||cg.parser->no_strength_reduction||
       f->jump_label_count||body_asm_statements(f->body))return;
    for(unsigned i=0;i<cg.parser->symbol_count;++i){
        Symbol *v=&cg.parser->symbols[i];
        if(v->owner!=f->id||!v->offset)continue;
        if(v->type.array||structure_object(v->type)){
            if(v->type.array?object_volatile(array_element(v->type)):
               !v->scope||volatile_type(v->type)||find_symbol(cg.parser,"$basic_asm"))continue;
            body_forward_private_bytes(f,v);
            if(!body_unused_fixed_stores(f->body,v,0)){
                unsigned char read[512]={0};
                if(width(v->type)<=sizeof read&&body_unread_fixed_stores(f->body,v,read,0))
                    body_unread_fixed_stores(f->body,v,read,1);
                continue;
            }
            body_unused_fixed_stores(f->body,v,1);
        }else{
            if((v->type.pointers?!far_pointer(v->type):v->type.base!=TY_LONG&&v->type.base!=TY_LONGLONG)||
               object_volatile(v->type)||
               scalar_leaf_parameter(f,v)||!loop_private(v)||body_statement_reads(f->body,v))continue;
            body_drop_stores(f->body,v);
            if(statement_references(f->body,v))continue;
        }
        body_remove_local(f,v);
    }
}
static int body_zero_trip_for(Statement *s)
{
    Statement *entry=body_single(s->initial);
    Expr *init,*value,*test;
    if(!entry||entry->next||entry->kind!=ST_EXPR||!(init=entry->expression)||
       init->kind!=EX_ASSIGN||init->op||init->left->kind!=EX_OBJECT||
       !literal_integer_tree(init->left)||!literal_integer_tree(init->right)||
       !s->expression||!literal_integer_tree(s->expression)||statement_has_case(s->body)||
       !expression_references(s->expression,init->left->symbol))return 0;
    value=convert(body_clone(init->right),unqualified_value(init->left->type));
    scalar_refold_expr(value);
    if(!wide_integer_literal(value)){free_expression(value);return 0;}
    test=body_clone(s->expression);
    scalar_replace_expr(&test,init->left->symbol,value);
    scalar_refold_expr(test);
    int never=scalar_literal_truth(test)==0;
    free_expression(value);free_expression(test);
    if(never)body_install_loop_actions(s,NULL);
    return never;
}
static int body_direct_integer_stores(Statement *s,Symbol *index,int literals)
{
    for(;s;s=s->next){
        Expr *e=s->expression;
        if(s->kind==ST_EMPTY)continue;
        if(s->kind==ST_BLOCK){
            if(!body_direct_integer_stores(s->body,index,literals))return 0;
        }else if(s->kind!=ST_EXPR||!e||e->kind!=EX_ASSIGN||e->op||
                 e->left->kind!=EX_OBJECT||e->left->symbol==index||
                 !literal_integer_tree(e->left)||!literal_integer_tree(e->right)||
                 (literals&&!wide_integer_literal(e->right)))return 0;
    }
    return 1;
}
/* Both arms overwrite the same scalar on every trip. Only the choice on
 * the last iteration survives when all sources are the index or literals. */
static Statement *body_last_conditional_store(Statement *s,Symbol *index,uint32_t last)
{
    Statement *guard=body_single(s);
    if(!guard||guard->next||guard->kind!=ST_IF||!loop_private(index))return NULL;
    Statement *yes=body_single(guard->body),*no=body_single(guard->alternate);
    Expr *a=plain_assignment(yes),*b=plain_assignment(no),*test=guard->expression;
    if(!a||!b||yes->next||no->next||!body_equal(a->left,b->left)||
       a->left->symbol==index||!known_integer(a->left->type)||volatile_expression(a->left)||
       !wide_integer_literal(a->right)||!wide_integer_literal(b->right)||
       test->kind!=EX_BINARY||!comparison(test->op)||test->left->kind!=EX_OBJECT||
       test->left->symbol!=index||test->right->kind!=EX_INT||!known_integer(test->right->type))return NULL;
    Expr *probe=body_clone(test);
    Expr value={.kind=EX_INT,.type=index->type,.value=last};
    scalar_replace_expr(&probe,index,&value);
    scalar_refold_expr(probe);
    int taken=scalar_literal_truth(probe);
    free_expression(probe);
    if(taken<0)return NULL;
    Statement *result=body_statement(ST_EXPR,guard->location);
    result->expression=body_clone(taken?a:b);
    return result;
}
static int known_empty_loop_interval(Statement *s,Symbol *index,int32_t first,int32_t last);
static int body_drop_empty_loops(Statement *s)
{
    int changed=0;
    for(;s;s=s->next){
        Statement *entry;
        Expr *test=s->expression,*init;
        Symbol *index;
        Type t;
        uint32_t first,end;
        int64_t start,stop,limit,stride=1;
        changed|=body_drop_empty_loops(s->body);
        changed|=body_drop_empty_loops(s->alternate);
        if(s->kind!=ST_FOR)continue;
        if(body_zero_trip_for(s)){changed=1;continue;}
        index=bounded_wide_induction(s,&first,&end);
        if(index&&first<end&&body_direct_integer_stores(s->body,index,1)&&!statement_has_case(s->body)){
            /* Each iteration writes the same literals and leaves the counter alone */
            Statement *stores=s->body;
            init=body_single(s->initial)->expression;
            free_expression(init->right);
            init->right=body_literal(index->type,end,init->location);
            s->body=NULL;
            body_install_loop_actions(s,stores);
            changed=1;continue;
        }
        if(!test||test->kind!=EX_BINARY||(test->op!='<'&&test->op!=TOK_LE)||
           test->left->kind!=EX_OBJECT)continue;
        index=test->left->symbol;t=index->type;
        if(t.pointers||t.array||t.is_bool||object_volatile(t)||
           (t.base!=TY_INT&&t.base!=TY_LONG))continue;
        entry=body_single(s->initial);
        if(!entry||entry->next||entry->kind!=ST_EXPR||
           !(init=entry->expression)||init->kind!=EX_ASSIGN||init->op||
           !body_equal(init->left,test->left)||
           !same_type(common_type(t,test->right->type),promoted(t))||
           !integer_constant(init->right,&first)||!integer_constant(test->right,&end))continue;
        start=t.is_unsigned?(int64_t)initializer_cast(first,t):(int32_t)initializer_cast(first,t);
        stop=t.is_unsigned?(int64_t)initializer_cast(end,t):(int32_t)initializer_cast(end,t);
        stop+=test->op==TOK_LE;
        if(!body_unit_step(s->step,index)){
            Expr *step=s->step;
            uint32_t delta;
            if(!step||step->kind!=EX_ASSIGN||step->op!='+'||
               !body_equal(step->left,test->left)||!integer_constant(step->right,&delta)||
               !same_type(common_type(t,step->right->type),promoted(t)))continue;
            stride=t.is_unsigned?(int64_t)initializer_cast(delta,t):(int32_t)initializer_cast(delta,t);
            if(stride<=0)continue;
        }
        limit=(INT64_C(1)<<(8*width(t)-!t.is_unsigned))-1;
        if(stop>start)stop=start+(stop-start+stride-1)/stride*stride;
        else stop=start;
        if(stop>limit)continue;
        if(stop>start){
            Statement *last=body_last_conditional_store(s->body,index,(uint32_t)(stop-stride));
            if(last){
                free_expression(init->right);init->right=body_literal(t,(uint32_t)stop,init->location);
                body_install_loop_actions(s,last);
                changed=1;continue;
            }
        }
        if(!empty_loop_body(s->body)&&(cg.parser->no_known_values||stop==start||!body_private(index)||
           !known_empty_loop_interval(s->body,index,(int32_t)start,(int32_t)(stop-stride))))continue;
        if(loop_private(index)&&!loop_observed_outside(cg.function->body,s,index)){
            free_statements(s->initial);s->initial=NULL;
            body_install_loop_actions(s,NULL);s->kind=ST_EMPTY;
        }else{
            free_expression(init->right);
            init->right=body_literal(t,(uint32_t)stop,init->location);
            body_install_loop_actions(s,NULL);
        }
        changed=1;
    }
    return changed;
}

static Expr *body_long_double_definition(Statement *s)
{
    Expr *def=s?s->expression:NULL,*input;
    Symbol *v;
    if(!s||s->kind!=ST_EXPR||s->inline_callee||!def||def->kind!=EX_ASSIGN||def->op||
       def->left->kind!=EX_OBJECT||volatile_expression(def)||
       !(input=doubled_long_source(def->right))||input->kind!=EX_DEREF||
       input->type.base!=TY_LONG||input->type.pointers||input->type.banked||
       far_pointer(value_type(input->left->type))||!element_address_pure(input->left))return NULL;
    v=def->left->symbol;
    return v->offset&&v->type.base==TY_LONG&&!v->type.pointers&&loop_private(v)&&
        !scalar_leaf_parameter(cg.function,v)&&statement_references(cg.function->body,v)==2?input:NULL;
}
static int body_long_double_store(Statement *s,Expr *def,Expr *input)
{
    Expr *store=s?s->expression:NULL;
    return s&&s->kind==ST_EXPR&&!s->inline_callee&&store&&store->kind==EX_ASSIGN&&!store->op&&
        store->right->kind==EX_OBJECT&&store->right->symbol==def->left->symbol&&
        !volatile_expression(store)&&body_equal(store->left,input);
}
static int body_adjacent_long_elements(Expr *a,Expr *b)
{
    Symbol *i,*j;
    unsigned x,y;
    a=a->left;b=b->left;
    return a->kind==EX_BINARY&&a->op=='+'&&b->kind==EX_BINARY&&b->op=='+'&&
        a->left->kind==EX_OBJECT&&a->left->type.array&&body_equal(a->left,b->left)&&
        width(pointed_type(value_type(a->left->type)))==4&&
        strength_affine(a->right,&i,&x)&&strength_affine(b->right,&j,&y)&&i==j&&
        (x+1==y||y+1==x);
}
static void body_move_long_double(Function *f,Statement *def,Statement *store)
{
    Expr *e=def->expression;
    free_expression(store->expression->right);
    store->expression->right=e->right;e->right=NULL;
    body_remove_local(f,e->left->symbol);
    free_expression(e);def->expression=NULL;def->kind=ST_EMPTY;
}
/* The earlier store can move across the second load only when their actual
 * long elements are disjoint. Keep any address effects or aliasing in place. */
static void body_forward_long_doubles(Function *f,Statement *s)
{
    for(;s;s=s->next){
        Statement *next=s->next,*store;
        Expr *a,*b;
        if(s->kind==ST_SWITCH)continue;
        a=body_long_double_definition(s);
        if(s->body)s->body=body_flatten(s->body);
        if(s->alternate)s->alternate=body_flatten(s->alternate);
        body_forward_long_doubles(f,s->body);
        body_forward_long_doubles(f,s->alternate);
        if(!a)continue;
        if(body_long_double_store(next,s->expression,a)){
            body_move_long_double(f,s,next);
        }else if((b=body_long_double_definition(next))&&body_adjacent_long_elements(a,b)&&
                 (store=next->next)){
            if(body_long_double_store(store,s->expression,a)&&body_long_double_store(store->next,next->expression,b)){
                body_move_long_double(f,s,store);body_move_long_double(f,next,store->next);
            }else if(body_long_double_store(store,next->expression,b)&&body_long_double_store(store->next,s->expression,a)){
                body_move_long_double(f,s,store->next);body_move_long_double(f,next,store);
            }
        }
    }
}

static void body_fold_local_tables(Function *f)
{
    Statement *first=f->body->body;
    for(Statement *s=first;s;s=s->next){
        Expr *init=s->expression,*values[16];
        Symbol *table;
        Statement *end=s,*p;
        Type element;
        unsigned count,stride,i;
        if(s->kind!=ST_EXPR||!init||init->kind!=EX_ASSIGN||init->op||
           init->left->kind!=EX_MEMBER||init->left->op!='.'||init->left->value||
           init->left->left->kind!=EX_OBJECT)continue;
        table=init->left->left->symbol;
        count=table->type.array;
        if(table->owner!=f->id||!table->offset||!count||count>16)continue;
        element=array_element(table->type);
        if(!element.pointers||!object_constant(element)||object_volatile(element))continue;
        stride=width(element);
        for(i=0;i<count&&end;++i,end=end->next){
            Expr *assign=end->expression;
            unsigned at;
            if(end->kind!=ST_EXPR||!assign||assign->kind!=EX_ASSIGN||assign->op||
               fixed_memory_object(assign->left,&at)!=table||at!=i*stride||
               !body_table_constant(assign->right))break;
            values[i]=assign->right;
        }
        if(i!=count)continue;
        for(p=first;p!=s&&!statement_references(p->body,table)&&!statement_references(p->alternate,table)&&
            !statement_references(p->initial,table)&&!expression_references(p->expression,table)&&
            !expression_references(p->step,table);p=p->next){}
        if(p!=s||!body_table_uses(end,table,values,stride,0))continue;
        body_table_uses(end,table,values,stride,1);
        for(p=s;p!=end;p=p->next){
            free_expression(p->expression);
            p->expression=NULL;p->kind=ST_EMPTY;
        }
        body_remove_local(f,table);
    }
}

/* Evaluate a finite table initializer symbolically, then substitute only the
 * entries the continuation reads. The table itself must never escape.
 * shortcut: cap symbolic evaluation at 64 entries to bound compile time. */
static void body_fold_pointer_loops(Function *f,Statement *s)
{
    for(;s;s=s->next){
        Statement *init,*body;
        Expr *start,*test=s->expression,*store,*address,*values[64];
        Symbol *index,*subscript,*table;
        Type element;
        uint32_t count,zero;
        unsigned delta,stride,used=0;
        body_fold_pointer_loops(f,s->initial);
        body_fold_pointer_loops(f,s->body);
        body_fold_pointer_loops(f,s->alternate);
        if(s->kind!=ST_FOR||!test||test->kind!=EX_BINARY||test->op!='<'||
           test->left->kind!=EX_OBJECT||!word_integer(common_type(test->left->type,test->right->type))||
           !integer_constant(test->right,&count)||!count||count>sizeof values/sizeof *values)continue;
        index=test->left->symbol;
        if(!word_integer(index->type)||!body_private(index)||!body_unit_step(s->step,index))continue;
        init=body_single(s->initial);body=body_single(s->body);
        if(!init||init->kind!=ST_EXPR||init->next||!body||body->kind!=ST_EXPR||body->next)continue;
        start=init->expression;store=body->expression;
        if(!start||start->kind!=EX_ASSIGN||start->op||start->left->kind!=EX_OBJECT||start->left->symbol!=index||
           !integer_constant(start->right,&zero)||zero||!store||store->kind!=EX_ASSIGN||store->op||
           store->left->kind!=EX_DEREF||volatile_expression(store->left)||body_effect(store->right))continue;
        address=store->left->left;
        if(address->kind!=EX_BINARY||address->op!='+'||address->left->kind!=EX_OBJECT||
           !strength_affine(address->right,&subscript,&delta)||index!=subscript||delta)continue;
        table=address->left->symbol;
        if(table->owner!=f->id||!table->offset||table->type.array!=count||
           statement_references(f->body,table)!=1+statement_references(s->next,table))continue;
        element=array_element(table->type);
        if(!element.pointers||object_volatile(element)||!same_type(store->left->type,element))continue;
        stride=width(element);
        if(!body_table_uses(s->next,table,NULL,stride,0))continue;
        for(;used<count;++used){
            Expr *value=body_clone(store->right);
            Expr at={.kind=EX_INT,.type=index->type,.location=value->location,.value=used};
            scalar_replace_expr(&value,index,&at);
            scalar_refold_expr(value);
            if(!body_table_constant(value)){free_expression(value);break;}
            values[used]=value;
        }
        if(used==count){
            body_table_uses(s->next,table,values,stride,1);
            free_expression(start->right);start->right=body_literal(index->type,count,start->location);
            body_install_loop_actions(s,NULL);
            body_remove_local(f,table);
        }
        while(used)free_expression(values[--used]);
    }
}

/* Flat case labels can be removed before inlining. A nested case can be
 * entered from outside its statement, and a nested break can skip the suffix. */
static void body_fold_constant_switch(Statement *s)
{
    Expr *control=s->expression;
    Statement *head=s->body,*entry,*item,*next,*kept=NULL,**tail=&kept;
    int active=0;
    if(control->kind!=EX_INT)return;
    entry=switch_constant_case(s);
    if(head->kind==ST_BLOCK&&!head->next)head=head->body;
    for(item=head;item;item=item->next){
        Statement *arm=item,single;
        while(arm->kind==ST_CASE){
            if(arm==entry)active=1;
            arm=arm->body;
            if(arm->next)return;
        }
        single=*arm;single.next=NULL;
        if(statement_has_case(&single)||(active&&arm->kind!=ST_BREAK&&contains_break(&single)))return;
        if(active&&(arm->kind==ST_BREAK||arm->kind==ST_RETURN||arm->kind==ST_CONTINUE))active=0;
    }
    if(head!=s->body){s->body->body=NULL;free_statements(s->body);}
    active=0;
    for(item=head;item;item=next){
        next=item->next;item->next=NULL;
        while(item->kind==ST_CASE){
            Statement *arm=item->body;
            if(item==entry){active=1;entry=NULL;}
            free(item);item=arm;
        }
        if(active&&item->kind==ST_BREAK)active=0;
        if(active){
            *tail=item;tail=&item->next;
            if(item->kind==ST_RETURN||item->kind==ST_CONTINUE)active=0;
        }else free_statements(item);
    }
    free_expression(control);
    s->kind=ST_BLOCK;s->expression=NULL;s->cases=NULL;s->body=kept;
}
static void body_fold_constant_switches(Statement *s)
{
    for(;s;s=s->next){
        if(s->kind==ST_SWITCH)body_fold_constant_switch(s);
        body_fold_constant_switches(s->initial);
        body_fold_constant_switches(s->body);
        body_fold_constant_switches(s->alternate);
    }
}

static void body_entry_post_value(Expr **at,BodyFacts *facts)
{
    Expr *e=*at;
    if(!e)return;
    if(e->kind==EX_POST&&e->left->kind==EX_OBJECT){
        Symbol *v=e->left->symbol;
        Expr *old=facts->value[body_symbol(v)];
        if(body_fact_home(v)&&old&&old->kind==EX_INT&&statement_references(cg.function->body,v)==2){
            *at=body_clone(old);free_expression(e);return;
        }
    }
    body_entry_post_value(&e->left,facts);
    body_entry_post_value(&e->right,facts);
    body_entry_post_value(&e->third,facts);
}
static int body_entry_loop(Statement *s,BodyFacts *facts);
static int body_entry_prefix(Statement *s,BodyFacts *facts,int startup)
{
    for(;s;s=s->next){
        body_split_post_value(s,facts,1);
        Expr *e=s->expression;
        if(s->kind==ST_EMPTY)continue;
        if(s->kind==ST_BLOCK){if(!body_entry_prefix(s->body,facts,startup))return 0;continue;}
        if(s->kind==ST_EXPR&&e){
            if(e->kind==EX_CALL&&!e->left&&e->symbol&&e->arg_count)body_fold_literal_arguments(e,1);
            body_split_commas(s);e=s->expression;
            if(e->kind==EX_INT||(e->kind==EX_CAST&&!e->type.pointers&&
                                e->type.base==TY_VOID&&e->left->kind==EX_INT)){
                free_expression(e);s->expression=NULL;s->kind=ST_EMPTY;
                continue;
            }
        }
        if(startup&&(s->kind==ST_IF||s->kind==ST_RETURN)){
            body_entry_post_value(&s->expression,facts);e=s->expression;
        }
        if(startup&&s->kind==ST_WHILE&&e&&literal_integer_tree(e)){
            Expr *probe=body_clone(e);
            body_replace(&probe,facts,0);scalar_refold_expr(probe);
            int never=scalar_literal_truth(probe)==0;
            free_expression(probe);
            if(never){
                free_expression(e);free_statements(s->body);
                s->kind=ST_EMPTY;s->expression=NULL;s->body=NULL;
                continue;
            }
        }
        if(s->kind==ST_FOR||s->kind==ST_WHILE||s->kind==ST_DO){
            if(!startup||!body_entry_loop(s,facts))return 0;
            continue;
        }
        if((s->kind==ST_IF||s->kind==ST_RETURN)&&e&&!body_effect(e)){
            body_replace(&s->expression,facts,0);scalar_refold_expr(s->expression);
            if(s->kind==ST_RETURN)return 0;
            int taken=scalar_literal_truth(s->expression);
            if(taken<0)return 0;
            Statement *arm=taken?s->body:s->alternate;
            free_statements(taken?s->alternate:s->body);
            free_expression(s->expression);
            s->kind=ST_BLOCK;s->expression=NULL;s->body=arm;s->alternate=NULL;
            if(!body_entry_prefix(arm,facts,startup))return 0;
            continue;
        }
        if(s->kind!=ST_EXPR||!e||(e->kind!=EX_ASSIGN&&e->kind!=EX_PRE&&e->kind!=EX_POST)||
           e->left->kind!=EX_OBJECT||
           volatile_expression(e)||body_effect(e->right))return 0;
        if(e->kind!=EX_ASSIGN||e->op){body_expr(&s->expression,facts,1);continue;}
        body_replace(&e->right,facts,0);scalar_refold_expr(e->right);
        Symbol *target=e->left->symbol;
        body_forget(facts,target);
        if(e->right->kind==EX_INT&&same_type(unqualified_value(target->type),unqualified_value(e->right->type)))
            facts->value[body_symbol(target)]=body_clone(e->right);
    }
    return 1;
}
/* At any entry, a direct write establishes a shared fact until code can
 * write through another home, call out, or take a different path. Only
 * the startup entry also knows the initial contents of globals. */
static void body_entry_values(Function *f)
{
    int startup=!strcmp(f->symbol->name,"main");
    if(cg.parser->no_known_values||f->jump_label_count||
       body_asm_statements(f->body)||find_symbol(cg.parser,"$basic_asm"))return;
    BodyFacts *facts=allocate(sizeof *facts);
    if(startup)for(unsigned i=0;i<cg.parser->symbol_count;++i){
        Symbol *v=&cg.parser->symbols[i];
        uint64_t bits=0;
        if(v->owner||!v->defined||v->function||v->enumerator||v->runtime_ram||v->relocations||
           !numeric(v->type)||v->type.base==TY_DOUBLE||object_volatile(v->type))continue;
        if(v->initializer)for(unsigned b=0;b<width(v->type);++b)bits|=(uint64_t)v->initializer[b]<<(8*b);
        facts->value[i]=body_literal(v->type,(uint32_t)bits,f->body->location);
        facts->value[i]->value_high=(uint32_t)(bits>>32);
    }
    body_entry_prefix(f->body,facts,startup);
    body_clear(facts);free(facts);
}
static unsigned body_count_expr_symbol(Expr *e,Symbol *v)
{
    unsigned n=0,i;
    if(!e)return 0;
    if(e->kind==EX_OBJECT&&e->symbol==v)++n;
    n+=body_count_expr_symbol(e->left,v);
    n+=body_count_expr_symbol(e->right,v);
    n+=body_count_expr_symbol(e->third,v);
    for(i=0;i<e->arg_count;++i)n+=body_count_expr_symbol(e->args[i],v);
    return n;
}
static unsigned body_count_stmt_symbol(Statement *s,Symbol *v)
{
    unsigned n=0;
    for(;s;s=s->next){
        n+=body_count_expr_symbol(s->expression,v);
        n+=body_count_expr_symbol(s->step,v);
        n+=body_count_stmt_symbol(s->initial,v);
        n+=body_count_stmt_symbol(s->body,v);
        n+=body_count_stmt_symbol(s->alternate,v);
    }
    return n;
}
static int body_reads_only_privates_and_rodata(Expr *e)
{
    unsigned i;
    if(!e)return 1;
    if(e->kind==EX_INT||e->kind==EX_STRING)return 1;
    if(e->kind==EX_OBJECT)
        return e->symbol&&(body_private(e->symbol)||
               (object_constant(e->symbol->type)&&!object_volatile(e->symbol->type)));
    if(e->kind==EX_CALL||e->kind==EX_ASSIGN||e->kind==EX_PRE||e->kind==EX_POST)return 0;
    if(e->kind==EX_BINARY&&(e->op=='/'||e->op=='%')){
        uint32_t d=0;
        if(!integer_constant(e->right,&d)||!d)return 0;
    }
    if(e->kind==EX_DEREF||(e->kind==EX_MEMBER&&e->op==TOK_ARROW)){
        Expr *cur=e->left;
        while(cur&&(cur->kind==EX_CAST||cur->kind==EX_ADDRESS||
                    (cur->kind==EX_BINARY&&(cur->op=='+'||cur->op=='-')))){
            if(cur->kind==EX_BINARY){
                Expr *off=value_type(cur->right->type).pointers?cur->left:cur->right;
                if(!body_reads_only_privates_and_rodata(off))return 0;
                cur=off==cur->left?cur->right:cur->left;
            }else cur=cur->left;
        }
        if(!cur||cur->kind!=EX_OBJECT||!object_constant(cur->symbol->type)||
           object_volatile(cur->symbol->type))return 0;
        return 1;
    }
    if(e->kind==EX_MEMBER){
        if(e->op=='.')return body_reads_only_privates_and_rodata(e->left);
        return 0;
    }
    if(e->kind==EX_ADDRESS)
        return e->left&&e->left->kind==EX_OBJECT&&object_constant(e->left->symbol->type);
    if(!body_reads_only_privates_and_rodata(e->left)||
       !body_reads_only_privates_and_rodata(e->right)||
       !body_reads_only_privates_and_rodata(e->third))return 0;
    for(i=0;i<e->arg_count;++i)if(!body_reads_only_privates_and_rodata(e->args[i]))return 0;
    return 1;
}
static int body_writes_expr_locals(Expr *e,Expr *read_tree)
{
    unsigned i;
    if(!e)return 0;
    if((e->kind==EX_ASSIGN||e->kind==EX_PRE||e->kind==EX_POST)&&
       e->left&&e->left->kind==EX_OBJECT&&body_count_expr_symbol(read_tree,e->left->symbol))
        return 1;
    if(body_writes_expr_locals(e->left,read_tree)||
       body_writes_expr_locals(e->right,read_tree)||
       body_writes_expr_locals(e->third,read_tree))return 1;
    for(i=0;i<e->arg_count;++i)if(body_writes_expr_locals(e->args[i],read_tree))return 1;
    return 0;
}
static int body_substitute_single(Expr **at,Symbol *v,Expr *rhs,Type vtype)
{
    Expr *e=*at;unsigned i;
    if(!e)return 0;
    if(e->kind==EX_OBJECT&&e->symbol==v){
        Expr *rep=body_clone(rhs);
        if(!same_type(rep->type,vtype))rep=convert(rep,vtype);
        free_expression(e);*at=rep;return 1;
    }
    if((e->kind==EX_BINARY&&(e->op==TOK_LAND||e->op==TOK_LOR))||e->kind==EX_CHOOSE)
        return body_substitute_single(&e->left,v,rhs,vtype);
    if(body_substitute_single(&e->left,v,rhs,vtype)||
       body_substitute_single(&e->right,v,rhs,vtype)||
       body_substitute_single(&e->third,v,rhs,vtype))return 1;
    for(i=0;i<e->arg_count;++i)if(body_substitute_single(&e->args[i],v,rhs,vtype))return 1;
    return 0;
}
static void body_flatten_tree(Statement *s)
{
    for(;s;s=s->next){
        if(s->kind==ST_BLOCK)s->body=body_flatten(s->body);
        body_flatten_tree(s->initial);
        body_flatten_tree(s->body);
        body_flatten_tree(s->alternate);
    }
}
static void body_forward_single_locals(Function *f,Statement *s,unsigned loops)
{
    for(;s;s=s->next){
        if(s->kind==ST_BLOCK)body_forward_single_locals(f,s->body,loops);
        else{
            unsigned nested=loops+(s->kind==ST_FOR||s->kind==ST_WHILE||s->kind==ST_DO);
            body_forward_single_locals(f,s->initial,loops);
            body_forward_single_locals(f,s->body,nested);
            body_forward_single_locals(f,s->alternate,loops);
        }
        if(!loops||s->kind!=ST_EXPR||!s->expression||s->expression->kind!=EX_ASSIGN||
           s->expression->op||!s->expression->left||s->expression->left->kind!=EX_OBJECT)
            continue;
        Symbol *v=s->expression->left->symbol;
        Expr *rhs=s->expression->right;
        if(!v||v->owner!=f->id||!v->scope||!body_private(v)||object_volatile(v->type)||
           v->type.pointers||v->type.array||v->type.is_bool||!known_integer(v->type)||
           body_effect(rhs)||volatile_expression(rhs)||
           !body_reads_only_privates_and_rodata(rhs)||
           scalar_writes(f->body,v)!=1||body_count_stmt_symbol(f->body,v)!=2)
            continue;
        Statement *p=s->next;
        while(p){
            unsigned hits=(p->kind==ST_EXPR||p->kind==ST_RETURN)?body_count_expr_symbol(p->expression,v):
                          (p->kind==ST_EMPTY?0u:2u);
            if(!hits){
                if(p->kind==ST_EMPTY){p=p->next;continue;}
                if(p->kind!=ST_EXPR||volatile_expression(p->expression)||
                   body_writes_expr_locals(p->expression,rhs))
                    break;
                p=p->next;
                continue;
            }
            if(hits==1&&(p->kind==ST_EXPR||p->kind==ST_RETURN)&&
               !volatile_expression(p->expression)&&
               !body_writes_expr_locals(p->expression,rhs)&&
               body_substitute_single(&p->expression,v,rhs,v->type)){
                free_expression(s->expression);
                s->expression=NULL;
                s->kind=ST_EMPTY;
            }
            break;
        }
    }
}
static int body_widen_byte_expr_ok(Expr *e,Symbol *v,int is_call_arg)
{
    unsigned i;
    if(!e)return 1;
    if(is_call_arg&&e->kind==EX_OBJECT&&e->symbol==v)return 0;
    if((e->kind==EX_ASSIGN||e->kind==EX_PRE||e->kind==EX_POST)&&
       e->left&&e->left->kind==EX_OBJECT&&e->left->symbol==v){
        if(e->kind==EX_ASSIGN&&!e->op){
            Expr *rhs=e->right;
            if(!rhs||!rhs->known.valid||rhs->known.min<0||rhs->known.max>255)return 0;
            while(rhs->kind==EX_CAST&&!rhs->type.pointers&&rhs->type.base==TY_CHAR&&rhs->type.is_unsigned){
                rhs=rhs->left;
                if(!rhs||!rhs->known.valid||rhs->known.min<0||rhs->known.max>255)return 0;
            }
        }else if(e->kind==EX_PRE||e->kind==EX_POST){
            if(!e->left->known.valid||e->left->known.min<0||
               (e->op==TOK_INC?e->left->known.max>=255:(e->left->known.min<=0||e->left->known.max>255)))
                return 0;
        }else{
            if(!e->known.valid||e->known.min<0||e->known.max>255||
               !e->left->known.valid||!e->right->known.valid)return 0;
            if(e->op=='+'){
                if(e->left->known.max+e->right->known.max>255||
                   e->left->known.min+e->right->known.min<0)return 0;
            }else if(e->op=='-'){
                if(e->left->known.min-e->right->known.max<0||
                   e->left->known.max-e->right->known.min>255)return 0;
            }else if(e->op==TOK_SHR){
                if(e->left->known.min<0||e->left->known.max>255||
                   e->right->known.min<0||e->right->known.max>=16)return 0;
            }else if(e->op=='&'){
                if(e->left->known.min<0||e->left->known.max>255)return 0;
            }else if(e->op=='|'||e->op=='^'){
                if(e->left->known.min<0||e->left->known.max>255||
                   e->right->known.min<0||e->right->known.max>255)return 0;
            }else if(e->op==TOK_SHL){
                if(e->left->known.min<0||e->left->known.max>255||
                   e->right->known.min<0||e->right->known.max>=8||
                   (e->left->known.max<<e->right->known.max)>255)return 0;
            }else return 0;
        }
    }
    if(!body_widen_byte_expr_ok(e->left,v,0)||
       !body_widen_byte_expr_ok(e->right,v,0)||
       !body_widen_byte_expr_ok(e->third,v,0))return 0;
    for(i=0;i<e->arg_count;++i)if(!body_widen_byte_expr_ok(e->args[i],v,e->kind==EX_CALL))return 0;
    return 1;
}
static int body_widen_byte_stmt_ok(Statement *s,Symbol *v)
{
    for(;s;s=s->next){
        if(!body_widen_byte_expr_ok(s->expression,v,0)||
           !body_widen_byte_expr_ok(s->step,v,0)||
           !body_widen_byte_stmt_ok(s->initial,v)||
           !body_widen_byte_stmt_ok(s->body,v)||
           !body_widen_byte_stmt_ok(s->alternate,v))
            return 0;
    }
    return 1;
}
static void body_widen_byte_expr_apply(Expr *e,Symbol *v)
{
    unsigned i;
    if(!e)return;
    body_widen_byte_expr_apply(e->left,v);
    body_widen_byte_expr_apply(e->right,v);
    body_widen_byte_expr_apply(e->third,v);
    for(i=0;i<e->arg_count;++i)body_widen_byte_expr_apply(e->args[i],v);
    if(e->kind==EX_OBJECT&&e->symbol==v)e->type=v->type;
    else if((e->kind==EX_ASSIGN||e->kind==EX_PRE||e->kind==EX_POST)&&
            e->left&&e->left->kind==EX_OBJECT&&e->left->symbol==v){
        e->type=v->type;
        if(e->kind==EX_ASSIGN&&!e->op&&e->right&&e->right->kind==EX_CAST&&
           !e->right->type.pointers&&e->right->type.base==TY_CHAR&&e->right->type.is_unsigned)
            e->right->type=v->type;
    }
}
static void body_widen_byte_stmt_apply(Statement *s,Symbol *v)
{
    for(;s;s=s->next){
        body_widen_byte_expr_apply(s->expression,v);
        body_widen_byte_expr_apply(s->step,v);
        body_widen_byte_stmt_apply(s->initial,v);
        body_widen_byte_stmt_apply(s->body,v);
        body_widen_byte_stmt_apply(s->alternate,v);
    }
}
static int body_widen_byte_useful_expr(Expr *e,Symbol *v,int in_address)
{
    unsigned i;
    if(!e)return 0;
    if(in_address&&e->kind==EX_OBJECT&&e->symbol==v)return 1;
    if(e->kind==EX_DEREF)return body_widen_byte_useful_expr(e->left,v,1);
    if(e->kind==EX_MEMBER){
        if(e->op==TOK_ARROW)return body_widen_byte_useful_expr(e->left,v,1);
        return body_widen_byte_useful_expr(e->left,v,in_address);
    }
    if(body_widen_byte_useful_expr(e->left,v,in_address)||
       body_widen_byte_useful_expr(e->right,v,in_address)||
       body_widen_byte_useful_expr(e->third,v,in_address))return 1;
    for(i=0;i<e->arg_count;++i)if(body_widen_byte_useful_expr(e->args[i],v,0))return 1;
    return 0;
}
static int body_widen_byte_useful_stmt(Statement *s,Symbol *v)
{
    for(;s;s=s->next){
        if((s->kind==ST_IF||s->kind==ST_FOR||s->kind==ST_WHILE||s->kind==ST_DO)&&
           s->expression&&s->expression->kind==EX_OBJECT&&s->expression->symbol==v)
            return 1;
        if((s->kind==ST_FOR||s->kind==ST_WHILE||s->kind==ST_DO)&&
           (loop_mentions(s->expression,v)||loop_mentions(s->step,v)))
            return 1;
        if(body_widen_byte_useful_expr(s->expression,v,0)||
           body_widen_byte_useful_expr(s->step,v,0)||
           body_widen_byte_useful_stmt(s->initial,v)||
           body_widen_byte_useful_stmt(s->body,v)||
           body_widen_byte_useful_stmt(s->alternate,v))
            return 1;
    }
    return 0;
}
static void body_widen_unsigned_bytes(Function *f)
{
    unsigned i;int changed=0;
    known_prepare(f);
    for(i=0;i<cg.parser->symbol_count;++i){
        Symbol *v=&cg.parser->symbols[i];
        if(v->owner!=f->id||!v->scope||!body_private(v)||object_volatile(v->type)||
           v->type.pointers||v->type.array||v->type.base!=TY_CHAR||!v->type.is_unsigned||v->type.is_bool)
            continue;
        if(body_widen_byte_stmt_ok(f->body,v)&&body_widen_byte_useful_stmt(f->body,v)){
            v->type.base=TY_INT;
            v->type.is_unsigned=0; /* unsigned char promotes to signed int */
            v->type.is_plain_char=0;
            body_widen_byte_stmt_apply(f->body,v);
            changed=1;
        }
    }
    if(changed)scalar_refold(f->body);
}
/* A postupdate in a final call passes the old value. No later statement
 * can observe its private write on this path. */
/* A terminal recursive invocation can hit a literal exit even when an
 * earlier guard is unknown, if that guard returns the same value. */
static void body_recursive_literal_exit(Expr *call)
{
    Function *f=cg.function;
    if(call->left||call->symbol!=f->symbol||f->symbol->noinline||f->symbol->variadic||
       call->arg_count!=(unsigned)f->symbol->param_count||!known_integer(call->type)||
       width(call->type)>4)return;
    BodyFacts facts={0};
    int have=0;
    uint32_t common=0;
    for(unsigned i=0;i<call->arg_count;++i){
        Expr *arg=call->args[i];
        Symbol *formal=leaf_parameter(f,i);
        if(!formal||!literal_integer_tree(arg)||!known_integer(formal->type)||object_volatile(formal->type))goto done;
        if(wide_integer_literal(arg))
            facts.value[body_symbol(formal)]=convert(body_clone(arg),unqualified_value(formal->type));
    }
    for(Statement *s=body_single(f->body);s;s=s->next){
        if(s->kind==ST_EMPTY||(s->kind==ST_BLOCK&&!s->body&&!s->inline_callee))continue;
        if(s->kind!=ST_IF||s->alternate||!literal_integer_tree(s->expression))break;
        Statement *exit=body_single(s->body);
        uint32_t value;
        if(!exit||exit->kind!=ST_RETURN||exit->next||!exit->expression||
           !integer_constant(exit->expression,&value))break;
        int taken=body_known_test(s->expression,&facts);
        if(!taken)continue;
        value=initializer_cast(value,call->type);
        if(have&&value!=common)break;
        have=1;common=value;
        if(taken>0){
            Expr *result=body_literal(call->type,value,call->location);
            for(unsigned i=0;i<call->arg_count;++i)free_expression(call->args[i]);
            *call=*result;free(result);break;
        }
    }
done:
    body_clear(&facts);
}
static void body_final_call_arguments(Statement *s)
{
    if(!s)return;
    while(s->next)s=s->next;
    if(s->kind==ST_BLOCK){body_final_call_arguments(s->body);return;}
    if(s->kind==ST_IF){
        body_final_call_arguments(s->body);
        body_final_call_arguments(s->alternate);
        return;
    }
    Expr *call=s->expression;
    if((s->kind!=ST_RETURN&&s->kind!=ST_EXPR)||!call||call->kind!=EX_CALL)return;
    for(unsigned i=0;i<call->arg_count;++i){
        Expr *arg=call->args[i];
        if(arg->kind!=EX_POST||arg->left->kind!=EX_OBJECT||!known_integer(arg->type))continue;
        Symbol *v=arg->left->symbol;
        if(!body_private(v)||expression_references(call,v)!=1)continue;
        call->args[i]=arg->left;arg->left=NULL;free_expression(arg);
    }
    body_recursive_literal_exit(call);
}
/* Compare constant returns after conversion to the target result type.
 * A pure integral condition cannot distinguish two identical returns. */
static void body_simplify_branches(Statement *s,Type result)
{
    for(;s;s=s->next){
        body_simplify_branches(s->initial,result);
        body_simplify_branches(s->body,result);
        body_simplify_branches(s->alternate,result);
        Statement *yes=body_single(s->body),*no=body_single(s->alternate);
        uint32_t a,b;
        if(s->kind!=ST_IF||!yes||!no||body_has_inline_region(s->body)||
           body_has_inline_region(s->alternate)||!literal_integer_tree(s->expression)||
           body_effect(s->expression))continue;
        /* A goto whose target opens the opposite arm reaches the same
         * statement on both outcomes. Keep that label for external entries. */
        if(yes->kind==ST_LABEL&&no->kind==ST_GOTO&&!no->next&&no->jump_label==yes->jump_label){
            free_statements(s->alternate);s->alternate=NULL;
        }else if(no->kind==ST_LABEL&&yes->kind==ST_GOTO&&!yes->next&&yes->jump_label==no->jump_label){
            free_statements(s->body);s->body=s->alternate;s->alternate=NULL;
        }else if(!known_integer(result)||width(result)>4||yes->next||no->next||
           yes->kind!=ST_RETURN||no->kind!=ST_RETURN||!yes->expression||!no->expression||
           !integer_constant(yes->expression,&a)||
           !integer_constant(no->expression,&b)||initializer_cast(a,result)!=initializer_cast(b,result))continue;
        free_expression(s->expression);s->expression=NULL;
        free_statements(s->alternate);s->alternate=NULL;s->kind=ST_BLOCK;
    }
}
/* A direct call to the C termination routine ends the reachable statement
 * list. Keep declarations with a local definition or incompatible type. */
static int body_library_exit(Symbol *callee)
{
    return callee&&!callee->defined&&!callee->internal&&!callee->variadic&&!callee->interrupt&&
           callee->param_count==1&&!strcmp(callee->name,"exit")&&
           same_type(callee->type,type(TY_VOID,0))&&same_type(callee->params[0],type(TY_INT,0));
}

static int body_termination_call(const Expr *e)
{
    if(!e||e->kind!=EX_CALL||e->left||!e->symbol)return 0;
    Symbol *callee=e->symbol;
    if(e->arg_count==1)return body_library_exit(callee);
    return !e->arg_count&&!callee->defined&&!callee->internal&&!callee->variadic&&
           !callee->interrupt&&!callee->param_count&&!strcmp(callee->name,"abort")&&
           same_type(callee->type,type(TY_VOID,0));
}

static int body_trim_after_exit(Statement *s)
{
    for(;s;s=s->next){
        int child_stops=body_trim_after_exit(s->body);
        int alternate_stops=body_trim_after_exit(s->alternate);
        int stops=s->kind==ST_BLOCK?child_stops:s->kind==ST_IF&&child_stops&&alternate_stops;
        if(s->kind==ST_EXPR&&body_termination_call(s->expression))stops=1;
        if(stops){
            free_statements(s->next);
            s->next=NULL;
            return 1;
        }
    }
    return 0;
}

/* A private parameter can rule out the entire inner loop. Keep the
 * outer updates in that arm and test the invariant length just once. */
static void body_guard_empty_inner_loop(Function *f)
{
    if(cg.parser->no_known_values||f->jump_label_count||
       body_asm_statements(f->body)||statement_inline_markers(f->body))return;
    for(Statement *outer=body_single(f->body);outer;outer=outer->next){
        Expr *test=outer->expression,*step=outer->step;
        if(outer->kind!=ST_FOR||outer->initial||!test||test->kind!=EX_BINARY||test->op!='<'||
           test->left->kind!=EX_OBJECT||!word_integer(test->left->type)||
           test->left->symbol->owner||volatile_expression(test)||!step||
           step->kind!=EX_ASSIGN||step->op!='+'||!body_equal(step->left,test->left))continue;
        uint32_t amount;
        if(!integer_constant(step->right,&amount)||!amount||amount>4)continue;
        Statement *inner=body_single(outer->body);
        if(!inner||inner->next||inner->kind!=ST_FOR||!inner->expression)continue;
        Expr *bound=inner->expression;
        if(bound->kind!=EX_BINARY||bound->op!='<'||bound->left->kind!=EX_OBJECT||
           bound->right->kind!=EX_OBJECT||!word_integer(bound->left->type)||
           !word_integer(bound->right->type)||bound->left->type.is_unsigned||
           bound->right->type.is_unsigned)continue;
        Symbol *count=bound->left->symbol,*limit=bound->right->symbol;
        Statement *init=body_single(inner->initial);
        if(!body_private(count)||!count->scope||count->storage||!body_private(limit)||limit->scope||
           !init||init->next||init->kind!=ST_EXPR||!init->expression||init->expression->kind!=EX_ASSIGN||
           init->expression->op||!body_equal(init->expression->left,bound->left)||
           !integer_constant(init->expression->right,&amount)||amount||
           scalar_writes(outer,limit)||
           statement_references(inner,count)!=statement_references(f->body,count))continue;
        int cost=body_flat_cost(inner->body);
        if(cost<0||cost>20)continue;
        Statement header=*outer;
        header.next=header.body=NULL;
        Statement *empty=body_clone_statements(&header);
        empty->body=body_statement(ST_EMPTY,outer->location);
        Statement *full=allocate(sizeof *full);
        *full=*outer;
        full->next=NULL;
        Expr *positive=new_expr(EX_BINARY,bound->location,type(TY_INT,0));
        positive->op='>';
        positive->left=body_clone(bound->right);
        positive->right=body_literal(type(TY_INT,0),0,bound->location);
        outer->kind=ST_IF;
        outer->expression=positive;
        outer->step=NULL;
        outer->body=full;
        outer->alternate=empty;
        break;
    }
}

static void body_optimize(Function *f)
{
    BodyFacts *facts;unsigned temps=0;
    if(cg.parser->no_strength_reduction||cg.parser->no_body_optimizations||f->symbol->interrupt||statement_has_case(f->body))return;
    if(!f->jump_label_count&&!body_asm_statements(f->body))body_final_call_arguments(f->body);
    body_entry_values(f);
    body_discarded_loads(f->body);
    body_narrow_far_locals(f);
    body_pointer_store_sequences(f,f->body,&temps);
    body_guard_empty_inner_loop(f);
    body_counted_loops(&f->body);
    if(!cg.parser->no_indexed_operands)body_loop_element_aliases(f,f->body);
    if(!f->jump_label_count&&!body_asm_statements(f->body))body_terminal_xor_swaps(f->body);
    body_overwritten_locals(f->body);
    facts=allocate(sizeof *facts);
    if(!cg.parser->no_known_values&&!f->jump_label_count&&!body_asm_statements(f->body))
        body_propagate_constant_definitions(f,facts);
    body_flow(f->body,facts);body_clear(facts);free(facts);
    scalar_refold(f->body);
    if(!f->jump_label_count&&!body_asm_statements(f->body))body_trim_after_exit(f->body);
    if(!cg.parser->no_value_reuse&&!f->jump_label_count&&!body_asm_statements(f->body))
        body_fold_pointer_loops(f,f->body);
    if(f->body->kind==ST_BLOCK){
        f->body->body=body_flatten(f->body->body);
        if(!cg.parser->no_value_reuse&&!f->jump_label_count&&!body_asm_statements(f->body)){
            body_forward_shift_offset(f->body->body);
            body_fold_local_tables(f);
        }
        body_defer_switch_addresses(f,f->body->body);
        body_sink_guard_value(f->body->body);
        if(!cg.parser->no_indexed_operands&&!f->jump_label_count&&!body_asm_statements(f->body))
            body_share_cursors(f,&f->body->body);
    }
    if(!f->jump_label_count&&!body_asm_statements(f->body)){
        body_flatten_tree(f->body);
        body_forward_single_locals(f,f->body,0);
    }
    body_dead_locals(f);
    if(!cg.parser->no_known_values&&!f->jump_label_count&&!body_asm_statements(f->body)&&
       body_discarded_loads(f->body)){
        facts=allocate(sizeof *facts);
        body_flow(f->body,facts);body_clear(facts);free(facts);
        scalar_refold(f->body);
        body_dead_locals(f);
    }
    if(!cg.parser->no_known_values&&!f->jump_label_count&&!body_asm_statements(f->body))
        body_widen_unsigned_bytes(f);
    if(!f->jump_label_count&&!body_asm_statements(f->body)&&body_forward_branch_values(f->body))body_dead_locals(f);
    if(!cg.parser->no_loop_unroll&&!f->jump_label_count&&!body_asm_statements(f->body)&&
       body_drop_empty_loops(f->body))body_dead_locals(f);
    body_drop_unused_homes(f);
    if(f->body->kind==ST_BLOCK){
        /* Empty statements from dead stores interrupt straight-line address reuse */
        f->body->body=body_flatten(f->body->body);
        if(!f->jump_label_count&&!body_asm_statements(f->body))body_covered_stores(f->body->body);
        if(cg.parser->no_value_reuse)body_address_cse(f,&f->body->body,&temps);}
    if(!cg.parser->no_value_reuse&&!cg.parser->no_byte_shuffles&&!cg.parser->no_known_values&&
       !f->jump_label_count&&!body_asm_statements(f->body))body_place_word_shifts(f->body);
    if(!cg.parser->no_value_reuse&&!f->jump_label_count&&!body_asm_statements(f->body))
        body_forward_long_doubles(f,f->body);
    if(!cg.parser->no_value_reuse&&!f->jump_label_count&&!body_asm_statements(f->body)&&f->body->kind==ST_BLOCK){
        unsigned far_addresses=0;
        body_reuse_far_addresses(f,&f->body->body,&far_addresses);
    }
}
/* Adjacent private selections can share one unchanged pure predicate. Keep
 * both assignments on their original selected path; never speculate an arm. */
static Expr *body_selection_choice(Expr *e)
{
    while(e&&e->kind==EX_CAST&&!e->type.pointers&&reg_width(e->type)==2)e=e->left;
    return e&&e->kind==EX_CHOOSE?e:NULL;
}
static Expr *body_selection_arm(Expr *e,int yes)
{
    Expr *copy=body_clone(e),**at=&copy,*choice,*arm;
    while((*at)->kind==EX_CAST)at=&(*at)->left;
    choice=*at;arm=body_clone(yes?choice->right:choice->third);free_expression(choice);*at=arm;return copy;
}
static int body_selection(Statement *s)
{
    Expr *e=s?s->expression:NULL;
    return s&&s->kind==ST_EXPR&&e&&e->kind==EX_ASSIGN&&!e->op&&e->left->kind==EX_OBJECT&&
        body_private(e->left->symbol)&&!e->left->type.pointers&&reg_width(e->type)==2&&
        body_selection_choice(e->right)&&indexed_pure(e->right);
}
static void body_fuse_selections(Statement *s)
{
    for(;s;s=s->next){
        Expr *a,*b,*x,*y;Statement *next,*yes,*no,*tail;
        body_fuse_selections(s->initial);body_fuse_selections(s->body);body_fuse_selections(s->alternate);
        if(!body_selection(s)||!body_selection(s->next))continue;
        next=s->next;a=s->expression;b=next->expression;x=body_selection_choice(a->right);y=body_selection_choice(b->right);
        if(!body_equal(x->left,y->left)||loop_mentions(x->left,a->left->symbol)||
           a->left->symbol==b->left->symbol)continue;
        yes=body_statement(ST_EXPR,s->location);yes->expression=body_clone(a);
        free_expression(yes->expression->right);yes->expression->right=body_selection_arm(a->right,1);
        tail=body_statement(ST_EXPR,next->location);tail->expression=body_clone(b);
        free_expression(tail->expression->right);tail->expression->right=body_selection_arm(b->right,1);yes->next=tail;
        no=body_statement(ST_EXPR,s->location);no->expression=body_clone(a);
        free_expression(no->expression->right);no->expression->right=body_selection_arm(a->right,0);
        tail=body_statement(ST_EXPR,next->location);tail->expression=body_clone(b);
        free_expression(tail->expression->right);tail->expression->right=body_selection_arm(b->right,0);no->next=tail;
        s->kind=ST_IF;s->expression=body_clone(x->left);s->body=yes;s->alternate=no;s->next=next->next;
        free_expression(a);free_expression(b);free(next);
        code("; fused private selections\n");
    }
}
static void body_shared_selections(Function *f)
{
    if(!cg.parser->no_body_optimizations&&!cg.parser->no_strength_reduction&&
       !f->symbol->interrupt&&!statement_has_case(f->body))body_fuse_selections(f->body);
}

/* Split a short loop when a private word's constant choice feeds repeated
 * XORs. The zero arm loses those operations and the other uses immediates. */
static unsigned body_xor_uses(Expr *e,Symbol *mask)
{
    if(!e)return 0;
    if(e->kind==EX_BINARY&&e->op=='^'&&
       ((e->left->kind==EX_OBJECT&&e->left->symbol==mask)||
        (e->right->kind==EX_OBJECT&&e->right->symbol==mask)))return 1;
    return body_xor_uses(e->left,mask)+body_xor_uses(e->right,mask)+body_xor_uses(e->third,mask);
}
static int body_mask_loop_cost(Statement *s,Symbol *mask,unsigned *uses,unsigned *budget)
{
    for(;s;s=s->next){
        if(!*budget||s->inline_callee||(s->kind!=ST_BLOCK&&s->kind!=ST_EMPTY&&
           s->kind!=ST_EXPR&&s->kind!=ST_IF))return 0;
        --*budget;
        *uses+=body_xor_uses(s->expression,mask);
        if(!body_mask_loop_cost(s->body,mask,uses,budget)||
           !body_mask_loop_cost(s->alternate,mask,uses,budget))return 0;
    }
    return 1;
}
static void body_split_xor_loops(Statement *s)
{
    for(;s;s=s->next){
        Expr *def=s->expression,*choice,*yes_value,*no_value;
        Statement *loop=s->next,*copy;
        Symbol *mask;
        unsigned uses=0,budget=32;
        uint32_t yes,no;
        if(s->kind==ST_SWITCH)continue;
        body_split_xor_loops(s->body);body_split_xor_loops(s->alternate);
        if(s->kind!=ST_EXPR||!def||def->kind!=EX_ASSIGN||def->op||
           def->left->kind!=EX_OBJECT||!word_integer(def->left->type)||
           !(choice=body_selection_choice(def->right))||!integer_constant(choice->right,&yes)||
           !integer_constant(choice->third,&no)||(yes==0)==(no==0)||!loop||
           loop->kind!=ST_FOR||loop->initial||volatile_statement(loop->body))continue;
        mask=def->left->symbol;
        if(!body_private(mask)||scalar_writes(cg.function->body,mask)!=1||
           !body_mask_loop_cost(loop->body,mask,&uses,&budget)||uses<2||
           statement_references(cg.function->body,mask)!=uses+1)continue;
        s->next=loop->next;loop->next=NULL;
        copy=body_clone_statements(loop);
        s->kind=ST_IF;s->expression=body_clone(choice->left);s->body=loop;s->alternate=copy;
        yes_value=body_selection_arm(def->right,1);no_value=body_selection_arm(def->right,0);
        body_cursor_substitute(loop,NULL,mask,yes_value);
        body_cursor_substitute(copy,NULL,mask,no_value);
        free_expression(yes_value);free_expression(no_value);
        free_expression(def);
        scalar_refold(loop);scalar_refold(copy);
        code("; specialized loop for a constant XOR mask\n");
    }
}

/* Evaluate a single-use clamped value at its word combine. Its inputs are
 * private and unchanged across the intervening straight-line guards. */
static int body_stable_word(Expr *e,Statement *between)
{
    if(!word_integer(e->type)||volatile_expression(e))return 0;
    if(e->kind==EX_INT)return 1;
    if(e->kind==EX_OBJECT)return body_private(e->symbol)&&!scalar_writes(between,e->symbol);
    if(e->kind==EX_CAST)return body_stable_word(e->left,between);
    return e->kind==EX_BINARY&&basic_integer_op(e->op)&&
        body_stable_word(e->left,between)&&body_stable_word(e->right,between);
}
static void body_keep_clamps(Statement *s)
{
    for(;s;s=s->next){
        Expr *def=s->expression,*test,*update,*combine,*choice;
        Statement *guard,*use;
        Symbol *value;
        uint32_t limit,constant;
        if(s->kind==ST_SWITCH)continue;
        body_keep_clamps(s->body);body_keep_clamps(s->alternate);
        if(s->kind!=ST_EXPR||!def||def->kind!=EX_ASSIGN||def->op||
           def->left->kind!=EX_OBJECT||!word_integer(def->left->type)||
           !def->left->type.is_unsigned||!body_private(value=def->left->symbol)||
           statement_references(cg.function->body,value)!=4||
           !body_stable_word(def->right,s->next))continue;
        for(guard=s->next;guard&&guard->kind==ST_IF&&!guard->alternate;guard=guard->next){
            if(expression_references(guard->expression,value))break;
            if(!single_statement(guard->body)||single_statement(guard->body)->next||
               !plain_assignment(guard->body))break;
        }
        if(!guard||guard->kind!=ST_IF||guard->alternate||
           !(test=guard->expression)||test->kind!=EX_BINARY||
           (test->op!=TOK_GE&&test->op!=TOK_LE&&test->op!='<'&&test->op!='>')||
           !body_equal(test->left,def->left)||!integer_constant(test->right,&limit)||
           !(update=plain_assignment(guard->body))||single_statement(guard->body)->next||
           !body_equal(update->left,def->left)||!integer_constant(update->right,&constant))continue;
        use=guard->next;
        if(!use||(use->kind!=ST_EXPR&&use->kind!=ST_RETURN))continue;
        combine=use->expression;
        if(combine&&combine->kind==EX_ASSIGN&&!combine->op&&!body_effect(combine->left))
            combine=combine->right;
        if(combine&&combine->kind==EX_BINARY&&combine->op=='^'&&
           body_stable_word(combine->right,NULL))combine=combine->left;
        if(!combine||combine->kind!=EX_BINARY||combine->op!='|'||
           !body_equal(combine->right,def->left)||combine->left->kind!=EX_OBJECT||
           !body_private(combine->left->symbol)||volatile_expression(use->expression)||
           !word_integer(combine->type))continue;
        choice=new_expr(EX_CHOOSE,guard->location,def->left->type);
        choice->left=body_clone(test);
        choice->right=body_clone(update->right);
        choice->third=convert(body_clone(def->right),def->left->type);
        body_cursor_replace(&choice->left,value,choice->third);
        free_expression(combine->right);combine->right=choice;
        free_expression(def);s->expression=NULL;s->kind=ST_EMPTY;
        free_expression(guard->expression);guard->expression=NULL;
        free_statements(guard->body);guard->body=NULL;guard->kind=ST_EMPTY;
        code("; forward bounded word into combine\n");
    }
}
static void body_reuse_addresses(Function *f)
{
    unsigned temps=0;
    if(cg.parser->no_value_reuse||cg.parser->no_strength_reduction||cg.parser->no_body_optimizations||
       f->symbol->interrupt||statement_has_case(f->body))return;
    /* Named-object value selection must see the array base before address CSE
     * hides it behind a pointer temporary. Remaining addresses still share. */
    if(f->body->kind==ST_BLOCK)body_address_cse(f,&f->body->body,&temps);
}

/* Whole-function byte bounds require every write to an unescaped private
 * scalar to be a proven byte. Ascending iteration proves copy/cast chains;
 * parameters, updates and escaped/volatile objects remain unknown. */
static void body_byte_writes_expr(Expr *e,unsigned char *seen,unsigned char *bad)
{
    unsigned i;if(!e)return;
    if((e->kind==EX_ASSIGN||e->kind==EX_PRE||e->kind==EX_POST)&&e->left->kind==EX_OBJECT){
        unsigned n=body_symbol(e->left->symbol);seen[n]=1;
        if(e->kind!=EX_ASSIGN||e->op||!unsigned_byte_value(e->right))bad[n]=1;
    }
    body_byte_writes_expr(e->left,seen,bad);body_byte_writes_expr(e->right,seen,bad);body_byte_writes_expr(e->third,seen,bad);
    for(i=0;i<e->arg_count;++i)body_byte_writes_expr(e->args[i],seen,bad);
}
static void body_byte_writes(Statement *s,unsigned char *seen,unsigned char *bad)
{
    for(;s;s=s->next){body_byte_writes_expr(s->expression,seen,bad);body_byte_writes_expr(s->step,seen,bad);
        body_byte_writes(s->initial,seen,bad);body_byte_writes(s->body,seen,bad);body_byte_writes(s->alternate,seen,bad);}
}
static void body_byte_ranges(Function *f)
{
    unsigned round,i;memset(byte_symbols,0,sizeof byte_symbols);
    if(cg.parser->no_body_optimizations)return;
    for(round=0;round<1024;++round){unsigned char seen[1024]={0},bad[1024]={0};int changed=0;
        body_byte_writes(f->body,seen,bad);
        for(i=0;i<cg.parser->symbol_count;++i){Symbol *v=&cg.parser->symbols[i];
            if(!byte_symbols[i]&&v->owner==f->id&&!scalar_leaf_parameter(f,v)&&body_private(v)&&seen[i]&&!bad[i])byte_symbols[i]=1,changed=1;
        }
        if(!changed)break;
    }
}

/* Store comparison-only signed loop keys in unsigned order. Copies between
 * keys keep the representation, so a loop-carried key is biased only when
 * it is loaded from its original source. */
typedef struct { unsigned char live[1024],loop_use[1024];int changed,assembly; } OrderHomes;
static int order_home(OrderHomes *homes,Expr *e)
{
    return e&&e->kind==EX_OBJECT&&homes->live[body_symbol(e->symbol)];
}
static int signed_word_order(Expr *e)
{
    Type t;
    if(e->kind!=EX_BINARY||(e->op!='<'&&e->op!='>'&&e->op!=TOK_LE&&e->op!=TOK_GE))return 0;
    t=common_type(e->left->type,e->right->type);
    return t.base==TY_INT&&!t.is_unsigned&&!t.pointers;
}
static Expr *order_bits(Expr *e,int biased)
{
    Type t=type(TY_INT,0);
    Expr *result;
    t.is_unsigned=1;e=convert(e,t);
    if(biased)return e;
    if(e->kind==EX_INT){e->value^=0x8000;return e;}
    result=new_expr(EX_BINARY,e->location,t);result->op='^';result->left=e;
    result->right=new_expr(EX_INT,e->location,t);result->right->value=0x8000;
    return result;
}
static void order_expr(OrderHomes *homes,Expr *e,int loop,int rewrite)
{
    unsigned i;
    if(!e)return;
    if(order_home(homes,e)){
        homes->live[body_symbol(e->symbol)]=0;homes->changed=1;return;
    }
    if(e->kind==EX_CALL&&e->symbol&&!strcmp(e->symbol->name,"$basic_asm"))homes->assembly=1;
    if(signed_word_order(e)){
        int left=order_home(homes,e->left),right=order_home(homes,e->right);
        if(!left)order_expr(homes,e->left,loop,rewrite);
        if(!right)order_expr(homes,e->right,loop,rewrite);
        if(loop&&left)homes->loop_use[body_symbol(e->left->symbol)]=1;
        if(loop&&right)homes->loop_use[body_symbol(e->right->symbol)]=1;
        if(rewrite&&(left||right)){e->left=order_bits(e->left,left);e->right=order_bits(e->right,right);}
        return;
    }
    order_expr(homes,e->left,loop,rewrite);order_expr(homes,e->right,loop,rewrite);
    order_expr(homes,e->third,loop,rewrite);
    for(i=0;i<e->arg_count;++i)order_expr(homes,e->args[i],loop,rewrite);
}
static void order_statements(OrderHomes *homes,Statement *s,int loop,int rewrite)
{
    for(;s;s=s->next){
        Expr *e=s->expression;
        int inside=loop||s->kind==ST_FOR||s->kind==ST_WHILE||s->kind==ST_DO;
        if(s->kind==ST_EXPR&&e&&e->kind==EX_ASSIGN&&!e->op&&order_home(homes,e->left)){
            int copy=order_home(homes,e->right);
            if(!copy)order_expr(homes,e->right,inside,rewrite);
            if(rewrite&&!copy)e->right=convert(order_bits(e->right,0),e->left->type);
        }else order_expr(homes,e,inside,rewrite);
        order_expr(homes,s->step,inside,rewrite);
        order_statements(homes,s->initial,loop,rewrite);
        order_statements(homes,s->body,inside,rewrite);
        order_statements(homes,s->alternate,inside,rewrite);
    }
}
static void body_order_homes(Function *f)
{
    OrderHomes homes={0};unsigned i;
    if(cg.parser->no_body_optimizations||cg.parser->no_strength_reduction||f->symbol->interrupt)return;
    for(i=0;i<cg.parser->symbol_count;++i){
        Symbol *v=&cg.parser->symbols[i];
        if(v->owner==f->id&&v->type.base==TY_INT&&!v->type.is_unsigned&&!v->type.is_bool&&
           !v->type.pointers&&body_private(v)&&!scalar_leaf_parameter(f,v))homes.live[i]=1;
    }
    do{
        homes.changed=0;memset(homes.loop_use,0,sizeof homes.loop_use);
        order_statements(&homes,f->body,0,0);
        if(homes.assembly)return;
        for(i=0;i<cg.parser->symbol_count;++i)if(homes.live[i]&&!homes.loop_use[i]){
            homes.live[i]=0;homes.changed=1;
        }
    }while(homes.changed);
    order_statements(&homes,f->body,0,1);
}
