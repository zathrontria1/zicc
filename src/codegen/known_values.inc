/* Typed, flow-sensitive word facts. Only unescaped automatic scalars have
 * homes in this environment. Bit facts describe normalized register values,
 * never the unused byte beside a byte object in memory. */
typedef struct {
    KnownValue values[1024],element_values[32];
    Expr *elements[32];
    unsigned element_count;
    VrEffects expression_effects;
    unsigned char private[1024], near_ptr[1024], nonnull[1024];
    int probing;
} KnownFlow;
static int known_integer(Type t)
{
    return !t.pointers&&!t.array&&(t.base==TY_INT||t.base==TY_CHAR);
}
static KnownValue known_type(Type t)
{
    KnownValue v={0};
    if (!known_integer(t)) {
        return v;
    }
    v.valid = 1;
    if(t.is_bool){v.zero=65534;v.min=0;v.max=1;}
    else if(t.base==TY_CHAR){v.min=t.is_unsigned?0:-128;v.max=t.is_unsigned?255:127;if(t.is_unsigned)v.zero=65280;}
    else{v.min=t.is_unsigned?0:-32768;v.max=t.is_unsigned?65535:32767;}
    return v;
}
static KnownValue known_bits(KnownValue v,Type t)
{
    KnownValue domain=known_type(t);int32_t lo,hi;unsigned bit;
    if(!v.valid||!domain.valid)return domain;
    v.zero&=65535;v.one&=65535;
    if(t.is_unsigned||t.is_bool){lo=(int32_t)v.one;hi=(int32_t)(65535^v.zero);}
    else if(v.zero&32768){lo=(int32_t)v.one;hi=(int32_t)(32767&~v.zero);}
    else if(v.one&32768){lo=(int32_t)(int16_t)v.one;hi=(int32_t)(int16_t)(65535^v.zero);}
    else{lo=(int32_t)(int16_t)(v.one|32768);hi=(int32_t)(32767&~v.zero);}
    if (v.min < lo) v.min = lo;
    if (v.max > hi) v.max = hi;
    if (v.min < domain.min) v.min = domain.min;
    if (v.max > domain.max) v.max = domain.max;
    /* Invalid/intersecting unreachable facts are not used as proofs */
    if(v.min>v.max||(v.zero&v.one))return domain;
    if(v.min>=0){
        for(bit=32768;bit&&(int32_t)bit>v.max;bit>>=1)v.zero|=bit;
    }
    if(v.min==v.max){v.one=(unsigned)v.min&65535;v.zero=v.one^65535;}
    return v;
}
static KnownValue known_constant(uint32_t n,Type t)
{
    KnownValue v=known_type(t);if(!v.valid)return v;n=initializer_cast(n,t)&65535;
    v.one=n;v.zero=n^65535;v.min=v.max=t.is_unsigned||t.is_bool?(int32_t)n:(int32_t)(int16_t)n;return v;
}
static KnownValue known_cast(KnownValue v,Type t)
{
    KnownValue result=known_type(t);if(!v.valid||!result.valid)return result;
    if(t.is_bool){if(v.min>0||v.max<0)return known_constant(1,t);if(!v.min&&!v.max)return known_constant(0,t);return result;}
    result.zero=v.zero;result.one=v.one;
    if(t.base==TY_CHAR){
        result.zero&=255;result.one&=255;
        if(t.is_unsigned||v.zero&128)result.zero|=65280;
        else if(v.one&128)result.one|=65280;
    }
    if(v.min>=result.min&&v.max<=result.max){result.min=v.min;result.max=v.max;}
    return known_bits(result,t);
}
static KnownValue known_join(KnownValue a,KnownValue b,Type t)
{
    KnownValue v=known_type(t);if(!a.valid||!b.valid)return v;
    v.zero=a.zero&b.zero;v.one=a.one&b.one;v.min=a.min<b.min?a.min:b.min;v.max=a.max>b.max?a.max:b.max;
    return known_bits(v,t);
}
static KnownValue known_binary(int op,KnownValue a,KnownValue b,Type t)
{
    KnownValue v=known_type(t);int64_t lo,hi;
    if(!v.valid||!a.valid||!b.valid)return v;
    a=known_cast(a,t);b=known_cast(b,t);
    if(op=='&'){v.zero=a.zero|b.zero;v.one=a.one&b.one;}
    else if(op=='|'){v.zero=a.zero&b.zero;v.one=a.one|b.one;}
    else if(op=='^'){v.zero=(a.zero&b.zero)|(a.one&b.one);v.one=(a.zero&b.one)|(a.one&b.zero);}
    else if(op=='+'||op=='-'){
        lo=op=='+'?(int64_t)a.min+b.min:(int64_t)a.min-b.max;
        hi=op=='+'?(int64_t)a.max+b.max:(int64_t)a.max-b.min;
        if(lo>=v.min&&hi<=v.max){v.min=(int32_t)lo;v.max=(int32_t)hi;}
    }else if(op=='*'){
        int64_t p0=(int64_t)a.min*b.min,p1=(int64_t)a.min*b.max,p2=(int64_t)a.max*b.min,p3=(int64_t)a.max*b.max;
        lo=hi=p0;
        if (p1 < lo) lo = p1;
        if (p1 > hi) hi = p1;
        if (p2 < lo) lo = p2;
        if (p2 > hi) hi = p2;
        if (p3 < lo) lo = p3;
        if (p3 > hi) hi = p3;
        if(lo>=v.min&&hi<=v.max){v.min=(int32_t)lo;v.max=(int32_t)hi;}
    }else if(op=='/'&&b.min==b.max&&b.min>0){
        v.min=a.min/b.min;v.max=a.max/b.min;
    }else if(op=='%'&&((t.is_unsigned&&b.max>0)||(a.min>=0&&b.min>0))){
        /* On defined executions the result is below the nonzero divisor */
        int32_t limit=b.max-1;
        v.min=0;v.max=a.max<limit?a.max:limit;
    }else if((op==TOK_SHL||op==TOK_SHR)&&b.min==b.max&&b.min>=0&&b.max<16){
        unsigned n=(unsigned)b.min;
        if(op==TOK_SHL){v.zero=((a.zero<<n)|((1u<<n)-1))&65535;v.one=(a.one<<n)&65535;}
        else{
            v.zero=a.zero>>n;v.one=a.one>>n;
            if(t.is_unsigned||a.min>=0)v.zero|=(65535u<<(16-n))&65535;
            else if(a.max<0)v.one|=(65535u<<(16-n))&65535;
        }
    }else if(op==TOK_SHR&&a.min>=0&&a.max>=0){
        v.min=0;v.max=a.max;
    }
    return known_bits(v,t);
}
static KnownValue known_comparison(int op,KnownValue a,KnownValue b,Type common,Type result)
{
    KnownValue v=known_type(result);
    v.zero=65534;v.min=0;v.max=1;
    if(!a.valid||!b.valid||!known_integer(common))return v;
    a=known_cast(a,common);b=known_cast(b,common);
    if(op==TOK_EQ||op==TOK_NE){
        if(a.max<b.min||b.max<a.min)return known_constant(op==TOK_NE,result);
        if(a.min==a.max&&a.min==b.min&&b.min==b.max)return known_constant(op==TOK_EQ,result);
    }else{
        int inclusive=op==TOK_GE||op==TOK_LE;
        if(op=='>'||op==TOK_GE){KnownValue swap=a;a=b;b=swap;}
        if(a.max<b.min||(inclusive&&a.max==b.min))return known_constant(1,result);
        if(a.min>b.max||(!inclusive&&a.min==b.max))return known_constant(0,result);
    }
    return v;
}
/* Named elements have identities only while their private subscripts and
 * array versions are unchanged. No facts are attached to arbitrary pointers. */
static int known_element(KnownFlow *flow,Expr *e,int create)
{
    Expr *index;unsigned i;
    if(vr_invalid(e,&flow->expression_effects)||!vr_load(e)||!e->left||e->left->kind!=EX_BINARY)return -1;
    index=e->left->right;while(index->kind==EX_CAST&&width(index->type)==2)index=index->left;
    if(index->kind!=EX_OBJECT||!body_private(index->symbol))return -1;
    for(i=0;i<flow->element_count;++i)if(body_equal(flow->elements[i],e))return (int)i;
    if(!create||i==32)return -1;
    flow->elements[i]=e;flow->element_values[i]=known_type(e->type);++flow->element_count;return (int)i;
}
static void known_kill_expr(KnownFlow *flow,Expr *e)
{
    unsigned i;if(!e)return;
    if(e->kind==EX_CALL||e->kind==EX_ASSIGN||e->kind==EX_PRE||e->kind==EX_POST||volatile_expression(e)){
        VrEffects effects={0};vr_effect_expr(&effects,e);i=0;
        while(i<flow->element_count){if(vr_invalid(flow->elements[i],&effects)){
            --flow->element_count;flow->elements[i]=flow->elements[flow->element_count];flow->element_values[i]=flow->element_values[flow->element_count];
        }else ++i;}
    }
    if((e->kind==EX_ASSIGN||e->kind==EX_PRE||e->kind==EX_POST)&&e->left->kind==EX_OBJECT){
        memset(&flow->values[body_symbol(e->left->symbol)],0,sizeof(KnownValue));
        flow->nonnull[body_symbol(e->left->symbol)]=0;
    }
    known_kill_expr(flow,e->left);known_kill_expr(flow,e->right);known_kill_expr(flow,e->third);
    for(i=0;i<e->arg_count;++i)known_kill_expr(flow,e->args[i]);
}
static void known_kill_statements(KnownFlow *flow,Statement *s)
{
    for(;s;s=s->next){known_kill_expr(flow,s->expression);known_kill_expr(flow,s->step);
        known_kill_statements(flow,s->initial);known_kill_statements(flow,s->body);known_kill_statements(flow,s->alternate);}
}
/* Subtracting an array or object start address in valid C yields a
 * non-negative byte offset bounded by the object's size (up to ptrdiff_t max). */
static int known_object_span(Expr *p,int32_t *hi)
{
    for(;;){
        while(p->kind==EX_CAST&&value_type(p->type).pointers)p=p->left;
        if(p->kind==EX_BINARY&&p->op=='+'&&p->right->kind==EX_INT&&!p->right->value){p=p->left;continue;}
        if(p->kind==EX_ADDRESS){
            Expr *in=p->left;
            if(in->kind==EX_DEREF){p=in->left;continue;}
            if(in->kind==EX_OBJECT){unsigned w=width(in->symbol->type);*hi=w&&w<32767u?(int32_t)w:32767;return 1;}
            if(in->kind==EX_MEMBER&&in->type.array){unsigned w=width(in->type);*hi=w&&w<32767u?(int32_t)w:32767;return 1;}
            return 0;
        }
        if(p->kind==EX_OBJECT&&p->symbol->type.array){unsigned w=width(p->symbol->type);*hi=w&&w<32767u?(int32_t)w:32767;return 1;}
        if(p->kind==EX_MEMBER&&p->type.array){unsigned w=width(p->type);*hi=w&&w<32767u?(int32_t)w:32767;return 1;}
        return 0;
    }
}
static int known_expr_modifies(Expr *e,Symbol *target)
{
    unsigned i;
    if(!e)return 0;
    if((e->kind==EX_ASSIGN||e->kind==EX_PRE||e->kind==EX_POST)&&
       e->left->kind==EX_OBJECT&&e->left->symbol==target)return 1;
    if(known_expr_modifies(e->left,target)||known_expr_modifies(e->right,target)||known_expr_modifies(e->third,target))return 1;
    for(i=0;i<e->arg_count;++i)if(known_expr_modifies(e->args[i],target))return 1;
    return 0;
}
static void known_expr_deref(KnownFlow *flow,Expr *root,Expr *e)
{
    unsigned i;
    if(!e||e->kind==EX_ADDRESS)return;
    if((e->kind==EX_DEREF||(e->kind==EX_MEMBER&&e->op==TOK_ARROW))&&
       e->left->kind==EX_OBJECT&&flow->near_ptr[body_symbol(e->left->symbol)]&&
       (!root||!known_expr_modifies(root,e->left->symbol)))
        flow->nonnull[body_symbol(e->left->symbol)]=1;
    known_expr_deref(flow,root,e->left);
    if(e->kind==EX_CHOOSE)return;
    if(e->kind==EX_BINARY&&(e->op==TOK_LAND||e->op==TOK_LOR))return;
    known_expr_deref(flow,root,e->right);known_expr_deref(flow,root,e->third);
    for(i=0;i<e->arg_count;++i)known_expr_deref(flow,root,e->args[i]);
}
static Expr *known_unwrap_ptr_truth(Expr *e)
{
    while(e&&e->kind==EX_CAST&&(e->type.is_bool||
          (e->left->type.pointers&&reg_width(e->type)>=reg_width(e->left->type))))
        e=e->left;
    return e;
}
static int immutable_element_bounds(const Expr *e,int use_expr_known,int has_idx_bounds,int32_t idx_min,int32_t idx_max,KnownValue *out)
{
    Symbol *base=NULL;
    Expr *idx_expr=NULL;
    unsigned member_offset=0,w,stride,count,lo_i,hi_i,i;
    Type elem_type={0};
    KnownValue acc={0};
    if(!e||volatile_expression((Expr *)e)||!known_integer(e->type)||e->type.is_bool)return 0;
    w=width(e->type);
    if(!w||w>2)return 0;
    if(e->kind==EX_OBJECT){
        Symbol *s=e->symbol;
        if(!s||s->owner||!s->defined||!s->initializer||s->relocations||s->type.array||
           !object_constant(s->type)||object_volatile(s->type)||width(s->type)!=w)return 0;
        uint32_t raw=s->initializer[0];
        if(w==2)raw|=(uint32_t)s->initializer[1]<<8;
        *out=known_constant(raw,e->type);
        return out->valid;
    }else if(e->kind==EX_DEREF){
        Expr *addr=e->left;
        if(addr&&addr->kind==EX_BINARY&&addr->op=='+'){
            if(addr->left->kind==EX_OBJECT){base=addr->left->symbol;idx_expr=addr->right;}
            else if(addr->right->kind==EX_OBJECT){base=addr->right->symbol;idx_expr=addr->left;}
        }else if(addr&&addr->kind==EX_OBJECT&&addr->symbol->type.array){
            base=addr->symbol;idx_min=0;idx_max=0;has_idx_bounds=1;
        }
        if(!base||!base->type.array||base->type.array==~0u||(base->type.element&&base->type.element->array))return 0;
        elem_type=pointed_type(value_type(base->type));
        if(width(elem_type)!=w)return 0;
    }else if(e->kind==EX_MEMBER){
        const Expr *cur=e;
        Expr *addr=NULL;
        while(cur&&cur->kind==EX_MEMBER&&cur->op=='.'){
            member_offset+=cur->value;
            cur=cur->left;
        }
        if(!cur)return 0;
        if(cur->kind==EX_OBJECT&&!cur->symbol->type.array){
            base=cur->symbol;
            if(base->owner||!base->defined||!base->initializer||base->relocations||
               !object_constant(base->type)||object_volatile(base->type)||
               member_offset+w>width(base->type))return 0;
            uint32_t raw=base->initializer[member_offset];
            if(w==2)raw|=(uint32_t)base->initializer[member_offset+1]<<8;
            *out=known_constant(raw,e->type);
            return out->valid;
        }
        if(cur->kind==EX_MEMBER&&cur->op==TOK_ARROW){
            member_offset+=cur->value;
            addr=cur->left;
        }else if(cur->kind==EX_DEREF){
            addr=cur->left;
        }else return 0;
        if(addr&&addr->kind==EX_BINARY&&addr->op=='+'){
            if(addr->left->kind==EX_OBJECT){base=addr->left->symbol;idx_expr=addr->right;}
            else if(addr->right->kind==EX_OBJECT){base=addr->right->symbol;idx_expr=addr->left;}
        }else if(addr&&addr->kind==EX_OBJECT&&addr->symbol->type.array){
            base=addr->symbol;idx_min=0;idx_max=0;has_idx_bounds=1;
        }
        if(!base||!base->type.array||base->type.array==~0u||(base->type.element&&base->type.element->array))return 0;
        elem_type=pointed_type(value_type(base->type));
    }else return 0;
    if(base->owner||!base->defined||!base->initializer||base->relocations||
       !object_constant(base->type)||object_volatile(base->type))return 0;
    stride=width(elem_type);count=base->type.array;
    if(!stride||!count||member_offset+w>stride||count>width(base->type)/stride)return 0;
    if(!has_idx_bounds&&use_expr_known&&idx_expr&&idx_expr->known.valid){
        has_idx_bounds=1;idx_min=idx_expr->known.min;idx_max=idx_expr->known.max;
    }
    lo_i=0;hi_i=count-1;
    if(has_idx_bounds&&idx_min>=0&&idx_max>=idx_min&&(unsigned)idx_max<count){
        lo_i=(unsigned)idx_min;hi_i=(unsigned)idx_max;
    }
    if(hi_i-lo_i>=1024u)return 0;
    for(i=lo_i;i<=hi_i;++i){
        unsigned off=i*stride+member_offset;
        uint32_t raw=base->initializer[off];
        if(w==2)raw|=(uint32_t)base->initializer[off+1]<<8;
        KnownValue item=known_constant(raw,e->type);
        acc=i==lo_i?item:known_join(acc,item,e->type);
    }
    *out=known_bits(acc,e->type);
    return out->valid;
}
static void known_refine(KnownFlow *flow,Expr *test,int truth);
static KnownValue known_expression(KnownFlow *flow,Expr *e,int lvalue)
{
    KnownValue v={0},a={0},b={0},c={0};unsigned i,offset=0;Type t;
    if (!e) {
        return v;
    }
    e->known_no_conversion = 0;
    e->known_nonnull = 0;
    /* Subexpressions never publish stores into the environment: all writes
     * were killed first, so unspecified operand/argument order adds no facts. */
    a=known_expression(flow,e->left,e->kind==EX_ADDRESS||e->kind==EX_ASSIGN||e->kind==EX_PRE||e->kind==EX_POST);
    if(e->kind==EX_CHOOSE){
        KnownFlow *yes=allocate(sizeof *yes),*no=allocate(sizeof *no);*yes=*flow;*no=*flow;
        known_kill_expr(yes,e->left);known_kill_expr(no,e->left);
        known_refine(yes,e->left,1);known_refine(no,e->left,0);
        known_kill_expr(yes,e->right);known_kill_expr(no,e->third);
        b=known_expression(yes,e->right,0);c=known_expression(no,e->third,0);free(yes);free(no);
    }else if(e->kind==EX_BINARY&&(e->op==TOK_LAND||e->op==TOK_LOR)){
        KnownFlow *sub=allocate(sizeof *sub);*sub=*flow;
        known_kill_expr(sub,e->left);
        known_expr_deref(sub,e->left,e->left);known_refine(sub,e->left,e->op==TOK_LAND);
        known_kill_expr(sub,e->right);
        b=known_expression(sub,e->right,0);free(sub);
    }else{b=known_expression(flow,e->right,0);c=known_expression(flow,e->third,0);}
    for(i=0;i<e->arg_count;++i)known_expression(flow,e->args[i],0);
    v=known_type(e->type);
    if(e->kind==EX_INT)v=known_constant(e->value,e->type);
    else if(e->kind==EX_OBJECT&&!lvalue&&flow->private[body_symbol(e->symbol)]&&flow->values[body_symbol(e->symbol)].valid)v=flow->values[body_symbol(e->symbol)];
    else if(!lvalue&&vr_load(e)){int n=known_element(flow,e,1);if(n>=0)v=flow->element_values[n];}
    else if(e->kind==EX_CAST)v=known_cast(a,e->type);
    else if(e->kind==EX_ASSIGN){
        if(e->op&&!a.valid){
            if(e->left->kind==EX_OBJECT&&flow->private[body_symbol(e->left->symbol)]&&
               flow->values[body_symbol(e->left->symbol)].valid)
                a=flow->values[body_symbol(e->left->symbol)];
            else a=known_type(e->left->type);
            if(e->left->kind==EX_OBJECT)e->left->known=a;
        }
        t=e->op==TOK_SHL||e->op==TOK_SHR?promoted(e->left->type):e->op?common_type(e->left->type,e->right->type):e->type;
        v=e->op?known_binary(e->op,a,b,t):b;
        if(e->op){Expr result={0};result.type=binary_operands(e->left,e->right,e->op);result.known=v;e->known_no_conversion=known_conversion(&result,e->type);}
        v=known_cast(v,e->type);
    }else if(e->kind==EX_CHOOSE){
        Expr *test=e->left;
        uint32_t limit;
        /* A pure word expression repeated in the selected arm has the
         * same bits as the value that passed the unsigned bound. */
        if(word_integer(e->type)&&test->kind==EX_BINARY&&
           (test->op=='<'||test->op==TOK_LE)&&word_integer(test->left->type)&&
           word_integer(common_type(test->left->type,test->right->type))&&
           common_type(test->left->type,test->right->type).is_unsigned&&
           integer_constant(test->right,&limit)&&limit<=32767&&
           body_equal(word_bits(test->left),word_bits(e->right))&&!body_effect(e->right)){
            KnownValue bounded=known_type(e->type);
            bounded.min=0;bounded.max=(int32_t)limit-(test->op=='<');
            if(bounded.max>=0)b=known_bits(bounded,e->type);
        }
        v=known_join(known_cast(b,e->type),known_cast(c,e->type),e->type);
    }
    else if(e->kind==EX_UNARY&&e->op=='-')
        v=known_binary('-',known_constant(0,e->type),a,e->type);
    else if(e->kind==EX_UNARY&&e->op=='~'&&a.valid){v.zero=a.one;v.one=a.zero;v=known_bits(v,e->type);}
    else if(e->kind==EX_BINARY){
        if(comparison(e->op)&&!find_symbol(cg.parser,"$basic_asm")){
            v=known_comparison(e->op,a,b,common_type(e->left->type,e->right->type),e->type);
        }else if(comparison(e->op)||e->op==TOK_LAND||e->op==TOK_LOR){
            v.zero=65534;v.min=0;v.max=1;
        }
        else{
            int32_t hi=0;
            t=e->type;v=known_binary(e->op,a,b,t);
            if(e->op=='-'&&value_type(e->left->type).pointers&&value_type(e->right->type).pointers&&
               !far_pointer(common_type(e->left->type,e->right->type))&&known_object_span(e->right,&hi)){
                v.min=0;v.max=hi;v=known_bits(v,t);
            }
            if(!flow->probing&&v.valid&&reg_width(t)==2&&!volatile_expression(e)){
                if(e->op=='-'&&e->left->kind==EX_INT&&b.valid&&
                   (e->left->value&65535)==e->left->value&&
                   ((e->left->value+1)&e->left->value)==0&&
                   ((b.zero|e->left->value)&65535)==65535){
                    Expr *constant=e->left;e->left=e->right;e->right=constant;e->op='^';
                }else if(e->op=='&'&&e->right->kind==EX_INT&&a.valid&&
                         ((a.zero|e->right->value)&65535)==65535){
                    free_expression(e->right);e->right=NULL;e->kind=EX_CAST;e->op=0;
                }
            }
        }
    }
    if(e->kind==EX_OBJECT&&!lvalue){
        if(e->type.array||(flow->near_ptr[body_symbol(e->symbol)]&&flow->nonnull[body_symbol(e->symbol)]))
            e->known_nonnull=1;
    }else if(e->kind==EX_ADDRESS){
        if(near_object_address(e,&offset)||(e->left->kind==EX_OBJECT&&!e->left->symbol->function)||
           ((e->left->kind==EX_DEREF||(e->left->kind==EX_MEMBER&&e->left->op==TOK_ARROW))&&e->left->left->known_nonnull))
            e->known_nonnull=1;
    }else if(e->kind==EX_CAST){
        if(value_type(e->type).pointers&&value_type(e->left->type).pointers&&
           (!far_pointer(value_type(e->left->type))||far_pointer(value_type(e->type)))&&
           e->left->known_nonnull)
            e->known_nonnull=1;
    }else if(e->kind==EX_CHOOSE){
        if(e->right->known_nonnull&&e->third->known_nonnull)e->known_nonnull=1;
    }else if(e->kind==EX_BINARY&&(e->op=='+'||e->op=='-')&&value_type(e->type).pointers){
        Expr *ptr=value_type(e->left->type).pointers?e->left:e->right;
        if(ptr->known_nonnull)e->known_nonnull=1;
    }else if(e->kind==EX_ASSIGN&&!e->op&&value_type(e->type).pointers&&e->right->known_nonnull){
        e->known_nonnull=1;
    }
    if(!lvalue&&v.valid&&(e->kind==EX_OBJECT||e->kind==EX_DEREF||e->kind==EX_MEMBER)){
        KnownValue imm={0};
        if(immutable_element_bounds(e,1,0,0,0,&imm)){
            if (v.min < imm.min) v.min = imm.min;
            if (v.max > imm.max) v.max = imm.max;
            v.zero|=imm.zero;v.one|=imm.one;v=known_bits(v,e->type);
        }
    }
    if(!lvalue&&v.valid&&e->range.valid){
        if (v.min < e->range.min) v.min = e->range.min;
        if (v.max > e->range.max) v.max = e->range.max;
        v.zero|=e->range.zero;v.one|=e->range.one;v=known_bits(v,e->type);
    }
    if (lvalue) {
        memset(&v, 0, sizeof v);
    }
    e->known = v;
    return v;
}
static void known_full_expression(KnownFlow *flow,Expr *e)
{
    memset(&flow->expression_effects,0,sizeof flow->expression_effects);
    vr_effect_expr(&flow->expression_effects,e);known_expression(flow,e,0);
    known_expr_deref(flow,e,e);
}
static void known_refine(KnownFlow *flow,Expr *test,int truth)
{
    Expr *object,*constant,*ptr;KnownValue *v;int op;int32_t n;Type t;
    if(!test)return;
    ptr=known_unwrap_ptr_truth(test);
    if(ptr!=test&&(ptr->type.pointers||(ptr->kind==EX_UNARY&&ptr->op=='!'))){known_refine(flow,ptr,truth);return;}
    if(test->kind==EX_UNARY&&test->op=='!'){known_refine(flow,test->left,!truth);return;}
    if(test->kind==EX_BINARY&&test->op==TOK_LAND){
        if(truth){known_refine(flow,test->left,1);known_kill_expr(flow,test->right);known_refine(flow,test->right,1);}
        return;
    }
    if(test->kind==EX_BINARY&&test->op==TOK_LOR){
        if(!truth){known_refine(flow,test->left,0);known_kill_expr(flow,test->right);known_refine(flow,test->right,0);}
        return;
    }
    if(test->kind==EX_OBJECT){
        if(flow->near_ptr[body_symbol(test->symbol)]){
            if(truth)flow->nonnull[body_symbol(test->symbol)]=1;
        }else if(flow->private[body_symbol(test->symbol)]&&known_integer(test->type)&&!test->type.pointers){
            v=&flow->values[body_symbol(test->symbol)];
            if(!v->valid)*v=known_type(test->type);
            if(!truth){v->min=v->max=0;*v=known_bits(*v,test->type);}
            else if(v->min==0&&v->max>=1){v->min=1;*v=known_bits(*v,test->type);}
            else if(v->max==0&&v->min<=-1){v->max=-1;*v=known_bits(*v,test->type);}
        }
        return;
    }
    if(test->kind!=EX_BINARY||!comparison(test->op))return;
    if(test->op==TOK_EQ||test->op==TOK_NE){
        Expr *zero=NULL,*lhs=known_unwrap_ptr_truth(test->left),*rhs=known_unwrap_ptr_truth(test->right);
        if(test->right->kind==EX_INT&&!test->right->value){ptr=lhs;zero=test->right;}
        else if(test->left->kind==EX_INT&&!test->left->value){ptr=rhs;zero=test->left;}
        if(zero&&ptr&&ptr->kind==EX_OBJECT&&flow->near_ptr[body_symbol(ptr->symbol)]){
            if((test->op==TOK_NE&&truth)||(test->op==TOK_EQ&&!truth))flow->nonnull[body_symbol(ptr->symbol)]=1;
            return;
        }
    }
    if(truth&&test->op=='<'&&value_type(test->left->type).pointers&&value_type(test->right->type).pointers&&
       test->right->kind==EX_OBJECT&&flow->near_ptr[body_symbol(test->right->symbol)]&&
       !known_expr_modifies(test->left,test->right->symbol))
        flow->nonnull[body_symbol(test->right->symbol)]=1;
    if(truth&&test->op=='>'&&value_type(test->left->type).pointers&&value_type(test->right->type).pointers&&
       test->left->kind==EX_OBJECT&&flow->near_ptr[body_symbol(test->left->symbol)]&&
       !known_expr_modifies(test->right,test->left->symbol))
        flow->nonnull[body_symbol(test->left->symbol)]=1;
    object=test->left;constant=test->right;op=test->op;
    if(object->kind==EX_INT&&constant->kind!=EX_INT){
        Expr *swap=object;object=constant;constant=swap;
        op=op=='<'?'>':op==TOK_LE?TOK_GE:op=='>'?'<':op==TOK_GE?TOK_LE:op;
    }
    t=common_type(object->type,constant->type);
    if(!known_integer(t)||reg_width(t)!=2)return;
    while(object->kind==EX_CAST&&known_integer(object->type)&&known_integer(object->left->type)&&
          reg_width(object->type)<=2&&reg_width(object->left->type)<=2){
        KnownValue dst=known_type(object->type),src=known_type(object->left->type);
        if(object->left->kind==EX_OBJECT&&flow->private[body_symbol(object->left->symbol)]&&
           flow->values[body_symbol(object->left->symbol)].valid)
            src=flow->values[body_symbol(object->left->symbol)];
        if(!dst.valid||!src.valid||src.min<dst.min||src.max>dst.max)return;
        object=object->left;
    }
    if(object->kind==EX_OBJECT&&flow->private[body_symbol(object->symbol)]){
        v=&flow->values[body_symbol(object->symbol)];
        if(!v->valid)*v=known_type(object->type);
    }
    else{int element=known_element(flow,object,0);if(element<0)return;v=&flow->element_values[element];}
    if(!v->valid||(t.is_unsigned&&v->min<0)||(!t.is_unsigned&&v->max>32767))return;
    if(!truth)op=op=='<'?TOK_GE:op==TOK_LE?'>':op=='>'?TOK_LE:op==TOK_GE?'<':op==TOK_EQ?TOK_NE:TOK_EQ;
    if(constant->kind==EX_INT){
        n=t.is_unsigned?(int32_t)(constant->value&65535):(int32_t)(int16_t)constant->value;
        if(op=='<'&&v->max>=n)v->max=n-1;
        else if(op==TOK_LE&&v->max>n)v->max=n;
        else if(op=='>'&&v->min<=n)v->min=n+1;
        else if(op==TOK_GE&&v->min<n)v->min=n;
        else if(op==TOK_EQ)v->min=v->max=n;
        else if(op==TOK_NE&&!n){
            if(v->min==0&&v->max>=1)v->min=1;
            else if(v->max==0&&v->min<=-1)v->max=-1;
        }
    }else if(constant->known.valid&&
             (t.is_unsigned?(constant->known.min>=0&&constant->known.max<=65535):
                            (constant->known.min>=-32768&&constant->known.max<=32767))){
        if((op=='<'||op==TOK_LE)&&(t.is_unsigned||v->min>=0)){
            int32_t hi=constant->known.max-(op=='<');
            if(hi>=v->min&&v->max>hi)v->max=hi;
        }else if((op=='>'||op==TOK_GE)&&(t.is_unsigned?v->max<=65535:v->max<=32767)){
            int32_t lo=constant->known.min+(op=='>');
            if(lo<=v->max&&v->min<lo)v->min=lo;
        }
    }else return;
    *v=known_bits(*v,object->type);
    known_kill_expr(flow,test);
}
static void known_merge(KnownFlow *to,KnownFlow *other)
{
    unsigned i,j;
    for(i=0;i<cg.parser->symbol_count;++i){
        if(to->private[i])to->values[i]=known_join(to->values[i],other->values[i],cg.parser->symbols[i].type);
        if(to->near_ptr[i])to->nonnull[i]&=(unsigned char)(other->nonnull[i]!=0);
    }
    for(i=0;i<to->element_count;++i){
        for(j=0;j<other->element_count&&!body_equal(to->elements[i],other->elements[j]);++j){}
        to->element_values[i]=j<other->element_count?known_join(to->element_values[i],other->element_values[j],to->elements[i]->type):known_type(to->elements[i]->type);
    }
}
static int known_flow(KnownFlow *flow,Statement *s);
static int known_loop_body(Statement *s)
{
    for(;s;s=s->next){
        if(s->kind!=ST_EXPR&&s->kind!=ST_EMPTY&&s->kind!=ST_BLOCK&&s->kind!=ST_IF)return 0;
        if(!known_loop_body(s->body)||!known_loop_body(s->alternate))return 0;
    }
    return 1;
}
static void known_kill_loop(KnownFlow *flow,Statement *s)
{
    known_kill_statements(flow,s->body);
    known_kill_expr(flow,s->expression);
    known_kill_expr(flow,s->step);
}
static int known_expr_safe_reapply(Expr *e,Statement *body,const KnownFlow *flow)
{
    if(!e)return 1;
    if(e->kind==EX_INT)return 1;
    if(e->kind==EX_OBJECT)return flow->private[body_symbol(e->symbol)]&&!scalar_writes(body,e->symbol);
    if(e->kind==EX_CAST||e->kind==EX_UNARY)return !body_effect(e)&&known_expr_safe_reapply(e->left,body,flow);
    if(e->kind==EX_BINARY)
        return !body_effect(e)&&known_expr_safe_reapply(e->left,body,flow)&&known_expr_safe_reapply(e->right,body,flow);
    return 0;
}
/* The index has the same bound even when a switch or an early exit prevents
 * interpreting one full iteration. The last increment must fit the type. */
static void known_seed_index(KnownFlow *inside,const KnownFlow *entry,Statement *s)
{
    Expr *test=s->expression;
    Symbol *index;
    KnownValue initial,limit,range;
    unsigned n;
    int32_t last;
    if(s->kind!=ST_FOR||!test||test->kind!=EX_BINARY||(test->op!='<'&&test->op!=TOK_LE)||
       test->left->kind!=EX_OBJECT||
       !word_integer(test->left->type)||test->left->type.is_unsigned||
       !word_integer(test->right->type)||test->right->type.is_unsigned)return;
    index=test->left->symbol;n=body_symbol(index);
    if(!entry->private[n]||!(initial=entry->values[n]).valid||initial.min<0||
       !body_unit_step(s->step,index)||scalar_writes(s->body,index))return;
    if(test->right->kind==EX_INT){
        limit=known_constant(test->right->value,test->right->type);
    }else if(known_expr_safe_reapply(test->right,s->body,entry)&&!loop_mentions(test->right,index)){
        KnownFlow *tmp=allocate(sizeof *tmp);
        *tmp=*entry;
        limit=known_expression(tmp,test->right,0);
        free(tmp);
    }else return;
    if(!limit.valid||limit.min<0)return;
    last=limit.max+(test->op==TOK_LE);
    if(last>32767)return;
    /* Bits common to the endpoints need not hold for intermediate indices */
    range=known_type(index->type);
    range.min=initial.min;
    range.max=initial.max>last?initial.max:last;
    inside->values[n]=known_bits(range,index->type);
}
/* Interpret one iteration with the loop writes unconstrained. A private
 * word bounded at entry and on this unrestricted back edge has an
 * inductive bound. Bodies with early exits retain the normal analysis. */
static int known_flow_one(KnownFlow *flow,Statement *s);
static void known_seed_loop(KnownFlow *inside,const KnownFlow *entry,Statement *s)
{
    KnownFlow *probe,*base;
    unsigned i,round;
    if(entry->probing||cg.function->jump_label_count)return;
    if(!find_symbol(cg.parser,"$basic_asm"))known_seed_index(inside,entry,s);
    if(!known_loop_body(s->body))return;
    for(i=0;i<cg.parser->symbol_count;++i)
        if(entry->private[i]&&entry->values[i].valid&&!inside->values[i].valid)break;
    if(i==cg.parser->symbol_count)return;
    probe=allocate(sizeof *probe);*probe=*inside;probe->probing=1;
    if(s->kind!=ST_DO){
        known_full_expression(probe,s->expression);
        known_refine(probe,s->expression,1);
    }
    known_flow(probe,s->body);
    known_kill_expr(probe,s->step);
    known_kill_expr(probe,s->expression);
    for(;i<cg.parser->symbol_count;++i)
        if(entry->private[i]&&entry->values[i].valid&&!inside->values[i].valid&&probe->values[i].valid)
            inside->values[i]=known_join(entry->values[i],probe->values[i],cg.parser->symbols[i].type);
    /* If any private variable remained wider than entry (e.g. shrinking
     * signed-widened byte shifts), check inductive invariance from entry. */
    for(i=0;i<cg.parser->symbol_count;++i)
        if(entry->private[i]&&entry->values[i].valid&&
           (!inside->values[i].valid||entry->values[i].min>inside->values[i].min||
            entry->values[i].max<inside->values[i].max))break;
    if(i==cg.parser->symbol_count){free(probe);return;}
    base=allocate(sizeof *base);*base=*entry;base->element_count=0;
    for(i=0;i<cg.parser->symbol_count;++i)
        if(base->private[i]&&inside->values[i].valid&&
           (!base->values[i].valid||inside->values[i].min>base->values[i].min||inside->values[i].max<base->values[i].max))
            base->values[i]=inside->values[i];
    for(round=0;round<2;++round){
        int stable=1;
        *probe=*base;probe->probing=1;
        if(s->kind!=ST_DO){
            known_full_expression(probe,s->expression);
            known_refine(probe,s->expression,1);
        }
        known_flow(probe,s->body);
        if(s->step){
            Statement step={0};
            step.kind=ST_EXPR;step.expression=s->step;
            known_flow_one(probe,&step);
        }
        for(i=0;i<cg.parser->symbol_count;++i){
            KnownValue joined,top;
            if(!base->private[i]||!base->values[i].valid)continue;
            top=inside->values[i].valid?inside->values[i]:known_type(cg.parser->symbols[i].type);
            joined=probe->values[i].valid?
                known_join(base->values[i],probe->values[i],cg.parser->symbols[i].type):top;
            if(!joined.valid||joined.min!=base->values[i].min||joined.max!=base->values[i].max||
               joined.zero!=base->values[i].zero||joined.one!=base->values[i].one){
                base->values[i]=top;
                stable=0;
            }
        }
        if(stable){
            for(i=0;i<cg.parser->symbol_count;++i)
                if(base->private[i]&&base->values[i].valid&&
                   (!inside->values[i].valid||base->values[i].min>inside->values[i].min||
                    base->values[i].max<inside->values[i].max))
                    inside->values[i]=base->values[i];
            break;
        }
    }
    free(base);
    free(probe);
}
static int known_flow(KnownFlow *flow,Statement *s);
static void known_reset_facts(KnownFlow *flow)
{
    memset(flow->values,0,sizeof flow->values);
    memset(flow->nonnull,0,sizeof flow->nonnull);
    flow->element_count=0;
}
static int known_structured_switch(Statement *s)
{
    for(;s;s=s->next){
        if(s->kind==ST_CASE){
            Statement *leaf=s->body;
            while(leaf&&leaf->kind==ST_CASE)leaf=leaf->body;
            if(leaf&&leaf->kind==ST_BLOCK&&!leaf->inline_callee){
                if(!known_structured_switch(leaf->body))return 0;
            }else if(statement_has_case(leaf))return 0;
        }else if(s->kind==ST_BLOCK&&!s->inline_callee){
            if(!known_structured_switch(s->body))return 0;
        }else if(s->kind!=ST_SWITCH&&(statement_has_case(s->body)||statement_has_case(s->alternate)||statement_has_case(s->initial)))return 0;
    }
    return 1;
}
static int known_flow_one(KnownFlow *flow,Statement *s);
static void known_flow_switch(KnownFlow *sw,Statement *s)
{
    int alive=1;
    if(s&&s->kind==ST_BLOCK&&!s->inline_callee)s=s->body;
    for(;s;s=s->next){
        if(s->kind==ST_CASE){
            known_reset_facts(sw);
            alive=known_flow_one(sw,s->body);
        }else if(s->kind==ST_BLOCK&&!s->inline_callee){
            if(alive)known_flow_switch(sw,s->body);
            else if(known_structured_switch(s->body))known_flow_switch(sw,s->body);
        }else if(alive){
            alive=known_flow_one(sw,s);
        }
    }
}
static int known_flow_one(KnownFlow *flow,Statement *s)
{
    if(!s)return 1;
    if(s->kind==ST_CASE){
        known_reset_facts(flow);
        return known_flow(flow,s->body);
    }
    if(s->kind==ST_BLOCK)return known_flow(flow,s->body);
    if(s->kind==ST_IF){
        KnownFlow *other;int yes,no;known_kill_expr(flow,s->expression);known_full_expression(flow,s->expression);
        other=allocate(sizeof *other);*other=*flow;known_refine(flow,s->expression,1);known_refine(other,s->expression,0);
        yes=known_flow(flow,s->body);no=known_flow(other,s->alternate);
        if(!yes&&no)*flow=*other;else if(yes&&no)known_merge(flow,other);
        free(other);return yes||no;
    }
    if(s->kind==ST_FOR||s->kind==ST_WHILE||s->kind==ST_DO){
        KnownFlow *inside;
        known_flow(flow,s->initial);
        inside=allocate(sizeof *inside);*inside=*flow;
        known_kill_loop(inside,s);
        known_seed_loop(inside,flow,s);
        known_kill_loop(flow,s);
        if(s->kind!=ST_DO){known_full_expression(inside,s->expression);known_refine(inside,s->expression,1);}
        known_flow(inside,s->body);
        /* Continue can bypass definitions at the bottom of a body */
        known_kill_statements(inside,s->body);
        if(s->kind==ST_FOR&&s->expression&&known_expr_safe_reapply(s->expression,s->body,inside)){
            known_refine(inside,s->expression,1);
        }
        if(s->kind==ST_FOR&&s->step&&
           ((s->step->kind==EX_PRE||s->step->kind==EX_POST)||
            (s->step->kind==EX_ASSIGN&&(s->step->op=='+'||s->step->op=='-')))&&
           s->step->left&&s->step->left->kind==EX_OBJECT&&
           inside->private[body_symbol(s->step->left->symbol)]){
            Expr *step=s->step;unsigned n=body_symbol(step->left->symbol);
            KnownValue pre=inside->values[n].valid?inside->values[n]:known_type(step->left->type);
            known_kill_expr(inside,step);known_kill_expr(inside,s->expression);
            known_full_expression(inside,step);
            step->left->known=pre;
        }else{
            known_kill_expr(inside,s->step);known_kill_expr(inside,s->expression);
            known_full_expression(inside,s->step);
        }
        if(s->kind==ST_DO)known_full_expression(inside,s->expression);
        free(inside);return 1;
    }
    if(s->kind==ST_BREAK||s->kind==ST_CONTINUE)return 0;
    if(s->kind==ST_EXPR&&s->expression&&(s->expression->kind==EX_PRE||s->expression->kind==EX_POST)&&
       s->expression->left&&s->expression->left->kind==EX_OBJECT&&
       flow->private[body_symbol(s->expression->left->symbol)]){
        Expr *e=s->expression;unsigned n=body_symbol(e->left->symbol);
        KnownValue pre=flow->values[n].valid?flow->values[n]:known_type(e->left->type);
        KnownValue post;
        known_kill_expr(flow,e);known_full_expression(flow,e);
        e->left->known=pre;
        post=known_cast(known_binary(e->op==TOK_INC?'+':'-',pre,known_constant(1,e->type),promoted(e->type)),e->type);
        e->known=e->kind==EX_POST?pre:post;
        flow->values[n]=post;
        return 1;
    }
    if(s->kind==ST_EXPR&&s->expression&&s->expression->kind==EX_ASSIGN&&s->expression->op&&
       s->expression->left&&s->expression->left->kind==EX_OBJECT&&
       flow->private[body_symbol(s->expression->left->symbol)]&&
       !scalar_writes_expr(s->expression->right,s->expression->left->symbol)){
        Expr *e=s->expression;unsigned n=body_symbol(e->left->symbol);
        KnownValue pre=flow->values[n].valid?flow->values[n]:known_type(e->left->type);
        known_kill_expr(flow,e);
        flow->values[n]=pre;
        known_full_expression(flow,e);
        e->left->known=pre;
        flow->values[n]=e->known;
        return 1;
    }
    known_kill_expr(flow,s->expression);known_full_expression(flow,s->expression);
    /* The selector runs once, but any arm can change the outgoing facts */
    if(s->kind==ST_SWITCH){
        if(!flow->probing&&known_structured_switch(s->body)){
            KnownFlow *sw=allocate(sizeof *sw);
            *sw=*flow;
            known_flow_switch(sw,s->body);
            free(sw);
        }
        known_kill_statements(flow,s->body);
    }
    if(s->kind==ST_RETURN)return 0;
    if(s->kind==ST_EXPR&&s->expression&&s->expression->kind==EX_ASSIGN&&s->expression->left->kind==EX_OBJECT){
        Expr *e=s->expression;unsigned n=body_symbol(e->left->symbol);
        if(flow->private[n])flow->values[n]=e->known;
        if(!e->op&&flow->near_ptr[n])flow->nonnull[n]=(unsigned char)(e->right->known_nonnull!=0);
    }
    return 1;
}
static int known_flow(KnownFlow *flow,Statement *s)
{
    for(;s;s=s->next)if(!known_flow_one(flow,s))return 0;
    return 1;
}
static int known_empty_loop_body(KnownFlow *flow,Statement *s)
{
    for(;s;s=s->next){
        if(s->kind==ST_EMPTY)continue;
        if(s->kind==ST_BLOCK){
            if(!known_empty_loop_body(flow,s->body))return 0;
        }else if(s->kind==ST_IF&&literal_integer_tree(s->expression)){
            Expr *test=body_clone(s->expression);
            KnownValue result=known_expression(flow,test,0);
            free_expression(test);
            if(!result.valid||result.min!=result.max||
               !known_empty_loop_body(flow,result.min?s->body:s->alternate))return 0;
        }else return 0;
    }
    return 1;
}
static int known_empty_loop_interval(Statement *s,Symbol *index,int32_t first,int32_t last)
{
    KnownFlow *flow=allocate(sizeof *flow);
    unsigned slot=body_symbol(index);
    KnownValue range=known_type(index->type);
    range.min=first;range.max=last;
    flow->private[slot]=1;
    flow->values[slot]=known_bits(range,index->type);
    int empty=known_empty_loop_body(flow,s);
    free(flow);
    return empty;
}
#include "range_values.inc"
static void known_prepare(Function *f)
{
    KnownFlow *flow;unsigned i;
    if(cg.parser->no_known_values||cg.parser->no_body_optimizations||cg.parser->no_strength_reduction||
       f->symbol->interrupt||statement_has_case(f->body))return;
    range_prepare(f);
    flow=allocate(sizeof *flow);
    for(i=0;i<cg.parser->symbol_count;++i){
        Symbol *s=&cg.parser->symbols[i];
        int priv=s->owner==f->id&&body_private(s);
        flow->private[i]=(unsigned char)(priv&&known_integer(s->type));
        flow->near_ptr[i]=(unsigned char)(priv&&s->type.pointers&&!far_pointer(value_type(s->type)));
    }
    if(f->ipa_internal){
        for(i=0;i<(unsigned)f->symbol->param_count&&i<16;++i){
            Symbol *formal;
            if(!f->ipa_known_valid[i])continue;
            formal=leaf_parameter(f,i);
            if(!formal||object_volatile(formal->type)||scalar_writes(f->body,formal)||
               !flow->private[body_symbol(formal)])continue;
            flow->values[body_symbol(formal)]=known_bits(known_cast(f->ipa_known[i],formal->type),formal->type);
        }
    }
    known_flow(flow,f->body);free(flow);
}
