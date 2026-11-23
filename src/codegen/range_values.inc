/* Bounded abstract execution, never program unrolling. Facts on an expression
 * are joined over every visit. Unbounded loops forget their writes before the
 * body, and unknown effects forget memory. No runtime-observed bounds are used. */
enum { RV_CELLS=128,RV_TRIPS=64,RV_BUDGET=200000 };
typedef struct {unsigned root;int64_t lo,hi;} RvTerm;
typedef struct {int valid;int32_t lo,hi;unsigned id;int select;RvTerm terms[2];} RvValue;
typedef struct {int alive;RvValue vars[1024],cells[RV_CELLS];} RvFlow;
typedef struct RvLoop RvLoop;
struct RvLoop {RvFlow *breaking,*continuing;RvLoop *outer;};
typedef struct {Expr *expr;KnownValue value;} RvNote;
typedef struct {Function *function;unsigned serial,budget;int failed;unsigned char private[1024];
    Symbol *bases[RV_CELLS];unsigned indices[RV_CELLS],cells;RvNote *notes;unsigned count,capacity;} RvContext;
static RvValue rv_type(Type t)
{
    KnownValue k=known_type(t);RvValue v={0};v.valid=k.valid;v.lo=k.min;v.hi=k.max;return v;
}
static RvValue rv_point(Type t,uint32_t n)
{
    KnownValue k=known_constant(n,t);RvValue v=rv_type(t);v.lo=k.min;v.hi=k.max;return v;
}
static void rv_identity(RvContext *c,RvValue *v)
{
    if (!v->valid) {
        return;
    }
    if (!v->id) {
        v->id = ++c->serial;
    }
    if(!v->select&&!v->terms[0].root){v->terms[0].root=v->id;v->terms[0].lo=v->terms[0].hi=0;}
}
static RvValue rv_cast(RvValue v,Type t)
{
    RvValue domain=rv_type(t);
    if(!domain.valid||!v.valid)return domain;
    if(t.is_bool){if(v.lo>0||v.hi<0)return rv_point(t,1);if(!v.lo&&!v.hi)return rv_point(t,0);return domain;}
    if(v.lo>=domain.lo&&v.hi<=domain.hi)return v;
    if(v.lo==v.hi)return rv_point(t,(uint32_t)v.lo);
    return domain;
}
static int rv_same(RvValue a,RvValue b)
{
    return a.valid&&b.valid&&((a.id&&a.id==b.id)||(a.lo==a.hi&&b.lo==b.hi&&a.lo==b.lo));
}
static RvValue rv_join(RvContext *c,RvValue a,RvValue b,Type t)
{
    RvValue v=rv_type(t);int same;
    a=rv_cast(a,t);b=rv_cast(b,t);same=rv_same(a,b);
    if(!a.valid||!b.valid)return v;
    v.lo=a.lo<b.lo?a.lo:b.lo;v.hi=a.hi>b.hi?a.hi:b.hi;
    if(same&&a.select==b.select&&!memcmp(a.terms,b.terms,sizeof a.terms)){v=a;v.lo=a.lo<b.lo?a.lo:b.lo;v.hi=a.hi>b.hi?a.hi:b.hi;}
    else if(v.lo!=v.hi)rv_identity(c,&v);
    return v;
}
static void rv_merge(RvContext *c,RvFlow *to,const RvFlow *from)
{
    unsigned i;if(!from->alive)return;if(!to->alive){*to=*from;return;}
    for(i=0;i<cg.parser->symbol_count;++i)if(c->private[i])to->vars[i]=rv_join(c,to->vars[i],from->vars[i],cg.parser->symbols[i].type);
    for(i=0;i<c->cells;++i){Type t=pointed_type(value_type(c->bases[i]->type));
        to->cells[i]=rv_join(c,to->cells[i],from->cells[i],t);}
}
static void rv_forget(RvContext *c,RvFlow *f,VrEffects *effects)
{
    unsigned i;for(i=0;i<cg.parser->symbol_count;++i)if(effects->symbols[i])memset(&f->vars[i],0,sizeof f->vars[i]);
    for(i=0;i<c->cells;++i)if(effects->unknown||effects->bases[body_symbol(c->bases[i])])memset(&f->cells[i],0,sizeof f->cells[i]);
}
static void rv_note(RvContext *c,Expr *e,RvValue v)
{
    unsigned i;KnownValue k=known_type(e->type);
    if(!k.valid||!v.valid)return;
    k.min=v.lo;k.max=v.hi;k=known_bits(k,e->type);
    for(i=0;i<c->count&&c->notes[i].expr!=e;++i){}
    if(i<c->count){c->notes[i].value=known_join(c->notes[i].value,k,e->type);return;}
    if(c->count==c->capacity){unsigned n=c->capacity?c->capacity*2:128;RvNote *p=realloc(c->notes,n*sizeof *p);
        if(!p){fputs("out of memory\n",stderr);exit(EXIT_FAILURE);}c->notes=p;c->capacity=n;}
    c->notes[c->count].expr=e;c->notes[c->count++].value=k;
}
static RvValue rv_expr(RvContext *c,RvFlow *f,Expr *e,int lvalue);
static int rv_cell(RvContext *c,RvFlow *f,Expr *e,int create)
{
    Expr *address;Symbol *base;RvValue index;unsigned i;
    if(!e||e->kind!=EX_DEREF||width(e->type)!=2||!known_integer(e->type)||volatile_expression(e))return -1;
    address=e->left;
    if(!address||address->kind!=EX_BINARY||address->op!='+'||address->left->kind!=EX_OBJECT)return -1;
    base=address->left->symbol;
    if(!base->type.array||base->owner||vr_immutable(base)||!same_type(unqualified_value(e->type),unqualified_value(pointed_type(value_type(base->type))))||!vr_index(address->right))return -1;
    index=rv_expr(c,f,address->right,0);
    if(!index.valid||index.lo!=index.hi||index.lo<0||(unsigned)index.lo>=width(base->type)/2)return -1;
    for(i=0;i<c->cells;++i)if(c->bases[i]==base&&c->indices[i]==(unsigned)index.lo)return (int)i;
    if(!create||i==RV_CELLS)return -1;
    c->bases[i]=base;c->indices[i]=(unsigned)index.lo;++c->cells;return (int)i;
}
static RvValue rv_read(RvContext *c,RvFlow *f,Expr *e)
{
    RvValue v=rv_type(e->type);unsigned n;int cell;
    if(e->kind==EX_OBJECT&&c->private[body_symbol(e->symbol)]){
        n=body_symbol(e->symbol);if(!f->vars[n].valid){f->vars[n]=v;rv_identity(c,&f->vars[n]);}return f->vars[n];
    }
    cell=rv_cell(c,f,e,1);
    if(cell>=0){if(!f->cells[cell].valid){f->cells[cell]=v;rv_identity(c,&f->cells[cell]);}return f->cells[cell];}
    if(e->kind==EX_OBJECT&&!volatile_expression(e)&&vr_immutable(e->symbol)&&e->symbol->initializer&&known_integer(e->type)&&width(e->type)<=2){
        uint32_t value=e->symbol->initializer[0];if(width(e->type)==2)value|=(uint32_t)e->symbol->initializer[1]<<8;return rv_point(e->type,value);
    }
    /* Immutable initialized scalar/array bytes are source facts, not samples */
    {
        RvValue index={0};
        KnownValue imm={0};
        if(e->kind==EX_DEREF&&e->left&&e->left->kind==EX_BINARY&&e->left->op=='+'&&e->left->left->kind==EX_OBJECT&&vr_index(e->left->right)){
            Symbol *base=e->left->left->symbol;unsigned w=width(e->type),offset;
            index=rv_expr(c,f,e->left->right,0);
            if(base->type.array&&!volatile_expression(e)&&!object_volatile(base->type)&&vr_immutable(base)&&base->initializer&&known_integer(e->type)&&w<=2&&w==width(pointed_type(value_type(base->type)))&&index.valid&&index.lo==index.hi&&index.lo>=0){
                offset=(unsigned)index.lo*w;
                if(offset+w<=width(base->type)){uint32_t value=base->initializer[offset];if(w==2)value|=(uint32_t)base->initializer[offset+1]<<8;return rv_point(e->type,value);}
            }
        }
        if(immutable_element_bounds(e,0,index.valid,index.lo,index.hi,&imm)){
            if (v.lo < imm.min) v.lo = imm.min;
            if (v.hi > imm.max) v.hi = imm.max;
        }
    }
    rv_identity(c,&v);return v;
}
static void rv_store(RvContext *c,RvFlow *f,Expr *target,RvValue v)
{
    int cell;Symbol *base;unsigned i;v=rv_cast(v,target->type);
    if(target->kind==EX_OBJECT){if(c->private[body_symbol(target->symbol)])f->vars[body_symbol(target->symbol)]=v;return;}
    cell=rv_cell(c,f,target,1);
    if(cell>=0){rv_identity(c,&v);v.select=0;memset(v.terms,0,sizeof v.terms);v.terms[0].root=v.id;f->cells[cell]=v;return;}
    base=target->kind==EX_DEREF?vr_base(target->left):NULL;
    for(i=0;i<c->cells;++i)if(!base||base==c->bases[i])memset(&f->cells[i],0,sizeof f->cells[i]);
}
static RvValue rv_binary(RvContext *c,int op,RvValue a,RvValue b,Type t)
{
    RvValue v=rv_type(t);int64_t lo,hi;unsigned i,j;
    a=rv_cast(a,t);b=rv_cast(b,t);if(!a.valid||!b.valid||!v.valid)return v;
    if(op=='+'||op=='-'){
        lo=op=='+'?(int64_t)a.lo+b.lo:(int64_t)a.lo-b.hi;hi=op=='+'?(int64_t)a.hi+b.hi:(int64_t)a.hi-b.lo;
        /* min(A)-max(B) <= A_i-B_j. Matching affine roots cancel exactly */
        if(op=='-'&&(a.select==1||!a.select)&&(b.select==2||!b.select)){
            for(i=0;i<(a.select?2u:1u);++i)for(j=0;j<(b.select?2u:1u);++j)
                if(a.terms[i].root&&a.terms[i].root==b.terms[j].root&&hi>a.terms[i].hi-b.terms[j].lo)hi=a.terms[i].hi-b.terms[j].lo;
        }
        if(lo>=v.lo&&hi<=v.hi&&lo<=hi){v.lo=(int32_t)lo;v.hi=(int32_t)hi;
            if(!a.select&&a.terms[0].root){v.terms[0]=a.terms[0];v.terms[0].lo+=op=='+'?b.lo:-(int64_t)b.hi;v.terms[0].hi+=op=='+'?b.hi:-(int64_t)b.lo;}
            else if(op=='+'&&!b.select&&b.terms[0].root){v.terms[0]=b.terms[0];v.terms[0].lo+=a.lo;v.terms[0].hi+=a.hi;}
        }
    }else if(op=='*'){
        int64_t p0=(int64_t)a.lo*b.lo,p1=(int64_t)a.lo*b.hi,p2=(int64_t)a.hi*b.lo,p3=(int64_t)a.hi*b.hi;
        lo=hi=p0;
        if (p1 < lo) lo = p1;
        if (p1 > hi) hi = p1;
        if (p2 < lo) lo = p2;
        if (p2 > hi) hi = p2;
        if (p3 < lo) lo = p3;
        if (p3 > hi) hi = p3;
        if(lo>=v.lo&&hi<=v.hi){v.lo=(int32_t)lo;v.hi=(int32_t)hi;}
    }else if(op=='/'&&b.lo==b.hi&&b.lo>0){
        lo=a.lo/b.lo;hi=a.hi/b.lo;
        if(lo>=v.lo&&hi<=v.hi){v.lo=(int32_t)lo;v.hi=(int32_t)hi;}
    }else if(op==TOK_SHR&&b.lo==b.hi&&b.lo>=0&&b.hi<16){int32_t divisor=1<<b.lo;
        v.lo=a.lo>=0?a.lo/divisor:-((-a.lo+divisor-1)/divisor);v.hi=a.hi>=0?a.hi/divisor:-((-a.hi+divisor-1)/divisor);
    }else if(op=='&'||op=='|'||op=='^'||op==TOK_SHL){KnownValue x=known_type(t),y=known_type(t),z;
        x.min=a.lo;x.max=a.hi;y.min=b.lo;y.max=b.hi;z=known_binary(op,known_bits(x,t),known_bits(y,t),t);v.lo=z.min;v.hi=z.max;
    }
    v.id=++c->serial;return v;
}
static void rv_refine(RvContext *c,RvFlow *f,Expr *test,int truth);
static RvValue rv_full(RvContext *c,RvFlow *f,Expr *e)
{
    VrEffects effects={0};RvValue none={0};if(!e)return none;
    /* The root store is sequenced after its RHS. Other effects invalidate
     * facts before any operand is evaluated, respecting unspecified order. */
    if(!volatile_expression(e)&&(e->kind==EX_ASSIGN||e->kind==EX_PRE||e->kind==EX_POST)&&
       (e->left->kind==EX_OBJECT||(e->left->kind==EX_DEREF&&vr_index(e->left->left->right))))vr_effect_expr(&effects,e->right);
    else vr_effect_expr(&effects,e);
    rv_forget(c,f,&effects);return rv_expr(c,f,e,0);
}
static RvValue rv_expr(RvContext *c,RvFlow *f,Expr *e,int lvalue)
{
    RvValue v={0},a={0},b={0};Type t;unsigned i;
    if(!e||!f->alive||c->failed)return v;
    if(!c->budget--){c->failed=1;return v;}
    v=rv_type(e->type);
    if(e->kind==EX_INT)v=rv_point(e->type,e->value);
    else if(e->kind==EX_OBJECT||e->kind==EX_DEREF||e->kind==EX_MEMBER){
        if(lvalue){if(e->kind==EX_DEREF||e->kind==EX_MEMBER)rv_expr(c,f,e->left,0);return v;}
        if(e->kind==EX_DEREF||e->kind==EX_MEMBER)rv_expr(c,f,e->left,0);
        v=rv_read(c,f,e);
    }else if(e->kind==EX_CAST){a=rv_expr(c,f,e->left,0);v=rv_cast(a,e->type);}
    else if(e->kind==EX_ASSIGN){
        rv_expr(c,f,e->left,1);a=e->op?rv_read(c,f,e->left):v;b=rv_expr(c,f,e->right,0);
        t=e->op?binary_operands(e->left,e->right,e->op):e->type;v=e->op?rv_binary(c,e->op,a,b,t):b;v=rv_cast(v,e->type);rv_store(c,f,e->left,v);
    }else if(e->kind==EX_PRE||e->kind==EX_POST){
        a=rv_read(c,f,e->left);b=rv_point(type(TY_INT,0),1);v=rv_cast(rv_binary(c,e->op==TOK_INC?'+':'-',a,b,promoted(e->type)),e->type);rv_store(c,f,e->left,v);if(e->kind==EX_POST)v=a;
    }else if(e->kind==EX_CHOOSE){
        RvFlow *yes=allocate(sizeof *yes),*no=allocate(sizeof *no);RvValue x,y,ta={0},tb={0};int minimum=0,select=0;
        a=rv_expr(c,f,e->left,0);*yes=*f;*no=*f;rv_refine(c,yes,e->left,1);rv_refine(c,no,e->left,0);
        if(a.valid&&a.lo==0&&a.hi==0)yes->alive=0;else if(a.valid&&(a.lo>0||a.hi<0))no->alive=0;
        x=rv_expr(c,yes,e->right,0);y=rv_expr(c,no,e->third,0);
        if(yes->alive&&no->alive)v=rv_join(c,x,y,e->type);else v=yes->alive?x:y;
        if(e->left->kind==EX_BINARY&&(e->left->op=='<'||e->left->op=='>'||e->left->op==TOK_LE||e->left->op==TOK_GE)&&
           vr_pure(e->left->left)&&vr_pure(e->left->right)&&vr_pure(e->right)&&vr_pure(e->third)){
            ta=rv_expr(c,f,e->left->left,0);tb=rv_expr(c,f,e->left->right,0);
            if(rv_same(x,ta)&&rv_same(y,tb)){select=1;minimum=e->left->op=='<'||e->left->op==TOK_LE;}
            else if(rv_same(x,tb)&&rv_same(y,ta)){select=1;minimum=e->left->op=='>'||e->left->op==TOK_GE;}
            t=common_type(e->left->left->type,e->left->right->type);
            if(select&&ta.valid&&tb.valid&&ta.lo>=rv_type(t).lo&&ta.hi<=rv_type(t).hi&&tb.lo>=rv_type(t).lo&&tb.hi<=rv_type(t).hi){
                v=rv_type(e->type);v.lo=minimum?(ta.lo<tb.lo?ta.lo:tb.lo):(ta.lo>tb.lo?ta.lo:tb.lo);v.hi=minimum?(ta.hi<tb.hi?ta.hi:tb.hi):(ta.hi>tb.hi?ta.hi:tb.hi);
                if(!ta.select&&!tb.select&&ta.terms[0].root&&tb.terms[0].root){v.select=minimum?1:2;v.terms[0]=ta.terms[0];v.terms[1]=tb.terms[0];}
                v.id=++c->serial;
            }
        }
        v=rv_cast(v,e->type);
        if(yes->alive){*f=*yes;rv_merge(c,f,no);}else *f=*no;free(yes);free(no);
    }else if(e->kind==EX_BINARY&&(e->op==TOK_LAND||e->op==TOK_LOR)){
        RvFlow *other=allocate(sizeof *other);a=rv_expr(c,f,e->left,0);*other=*f;
        rv_expr(c,other,e->right,0);rv_merge(c,f,other);free(other);v.lo=0;v.hi=1;
    }else if(e->kind==EX_BINARY){
        a=rv_expr(c,f,e->left,0);b=rv_expr(c,f,e->right,0);
        if(comparison(e->op)||e->op==TOK_LAND||e->op==TOK_LOR){
            v=rv_type(e->type);v.lo=0;v.hi=1;
        }else v=rv_binary(c,e->op,a,b,e->type);
    }else if(e->kind==EX_UNARY){
        a=rv_expr(c,f,e->left,e->op=='&');
        if(e->op=='+')v=rv_cast(a,e->type);
        else if(e->op=='-')v=rv_binary(c,'-',rv_point(e->type,0),a,e->type);
        else if(e->op=='~'&&a.valid){v=rv_binary(c,'^',a,rv_point(e->type,65535),e->type);}
        else if(e->op=='!'){v.lo=0;v.hi=1;}
    }else{
        rv_expr(c,f,e->left,0);rv_expr(c,f,e->right,0);rv_expr(c,f,e->third,0);
        for(i=0;i<e->arg_count;++i)rv_expr(c,f,e->args[i],0);
        if(e->kind==EX_CALL){VrEffects effects={0};effects.unknown=1;rv_forget(c,f,&effects);}
    }
    if (!lvalue) {
        rv_note(c, e, v);
    }
    return v;
}
static RvValue *rv_lvalue(RvContext *c,RvFlow *f,Expr *e)
{
    int cell;if(e->kind==EX_OBJECT&&c->private[body_symbol(e->symbol)])return &f->vars[body_symbol(e->symbol)];
    cell=rv_cell(c,f,e,1);return cell>=0?&f->cells[cell]:NULL;
}
static void rv_refine(RvContext *c,RvFlow *f,Expr *test,int truth)
{
    RvValue a,b,*slot;Type t;int op;
    if(!test||!f->alive)return;
    if(test->kind==EX_UNARY&&test->op=='!'){rv_refine(c,f,test->left,!truth);return;}
    if(test->kind!=EX_BINARY||!comparison(test->op)||!vr_pure(test->left)||!vr_pure(test->right))return;
    a=rv_expr(c,f,test->left,0);b=rv_expr(c,f,test->right,0);t=common_type(test->left->type,test->right->type);
    if(!a.valid||!b.valid||a.lo<rv_type(t).lo||a.hi>rv_type(t).hi||b.lo<rv_type(t).lo||b.hi>rv_type(t).hi)return;
    op=test->op;if(!truth)op=op=='<'?TOK_GE:op==TOK_LE?'>':op=='>'?TOK_LE:op==TOK_GE?'<':op==TOK_EQ?TOK_NE:TOK_EQ;
    slot=rv_lvalue(c,f,test->left);if(!slot)return;
    if(op=='<'&&a.hi>=b.hi)a.hi=b.hi-1;else if(op==TOK_LE&&a.hi>b.hi)a.hi=b.hi;
    else if(op=='>'&&a.lo<=b.lo)a.lo=b.lo+1;else if(op==TOK_GE&&a.lo<b.lo)a.lo=b.lo;
    else if(op==TOK_EQ){if(a.lo<b.lo)a.lo=b.lo;if(a.hi>b.hi)a.hi=b.hi;}
    if(a.lo>a.hi){f->alive=0;return;}*slot=a;
}
static void rv_statements(RvContext *c,RvFlow *f,Statement *s,RvLoop *loop);
static int rv_counted(RvContext *c,RvFlow *f,Statement *s,int *trips)
{
    Expr *test=s->expression,*step=s->step;Symbol *index;RvValue a,b;int64_t end,n;VrEffects effects={0};
    if(s->kind!=ST_FOR||!test||test->kind!=EX_BINARY||(test->op!='<'&&test->op!=TOK_LE)||test->left->kind!=EX_OBJECT||
       !step||(step->kind!=EX_PRE&&step->kind!=EX_POST)||step->op!=TOK_INC||step->left->kind!=EX_OBJECT)return 0;
    index=test->left->symbol;if(!c->private[body_symbol(index)]||step->left->symbol!=index||scalar_writes(s->body,index)||!vr_pure(test->right))return 0;
    vr_effect_statements(&effects,s->body);if(vr_invalid(test->right,&effects))return 0;
    a=rv_expr(c,f,test->left,0);b=rv_expr(c,f,test->right,0);if(!a.valid||!b.valid||a.lo!=a.hi||b.lo!=b.hi||a.lo<0)return 0;
    end=(int64_t)b.lo+(test->op==TOK_LE);n=end-a.lo;
    if (n < 0) {
        n = 0;
    }
    if (n > RV_TRIPS || end > rv_type(index->type).hi || b.lo < 0) {
        return 0;
    }
    *trips=(int)n;return 1;
}
static void rv_loop(RvContext *c,RvFlow *f,Statement *s,RvLoop *outer)
{
    int trips=0,i;RvLoop loop;VrEffects effects={0};RvFlow *entry=allocate(sizeof *entry);
    rv_statements(c,f,s->initial,outer);*entry=*f;
    loop.outer=outer;loop.breaking=allocate(sizeof *loop.breaking);loop.continuing=allocate(sizeof *loop.continuing);
    if(rv_counted(c,f,s,&trips)){
        for(i=0;i<trips&&f->alive&&!c->failed;++i){
            rv_full(c,f,s->expression);loop.continuing->alive=0;rv_statements(c,f,s->body,&loop);rv_merge(c,f,loop.continuing);rv_full(c,f,s->step);
        }
        if (f->alive) {
            rv_full(c, f, s->expression);
        }
        rv_merge(c, f, loop.breaking);
    }else{
        vr_effect_statements(&effects,s->body);vr_effect_expr(&effects,s->step);vr_effect_expr(&effects,s->expression);rv_forget(c,f,&effects);
        if(s->kind!=ST_DO){rv_full(c,f,s->expression);rv_refine(c,f,s->expression,1);}
        rv_statements(c,f,s->body,&loop);rv_merge(c,f,loop.continuing);rv_full(c,f,s->step);
        if(s->kind==ST_DO)rv_full(c,f,s->expression);
        *f=*entry;rv_forget(c,f,&effects);
    }
    free(entry);free(loop.breaking);free(loop.continuing);
}
static void rv_statements(RvContext *c,RvFlow *f,Statement *s,RvLoop *loop)
{
    for(;s&&f->alive&&!c->failed;s=s->next){
        if(s->kind==ST_BLOCK){rv_statements(c,f,s->body,loop);continue;}
        if(s->kind==ST_FOR||s->kind==ST_WHILE||s->kind==ST_DO){rv_loop(c,f,s,loop);continue;}
        if(s->kind==ST_IF){RvFlow *other;RvValue test;
            test=rv_full(c,f,s->expression);other=allocate(sizeof *other);*other=*f;
            rv_refine(c,f,s->expression,1);rv_refine(c,other,s->expression,0);
            if(test.valid&&!test.lo&&!test.hi)f->alive=0;else if(test.valid&&(test.lo>0||test.hi<0))other->alive=0;
            rv_statements(c,f,s->body,loop);rv_statements(c,other,s->alternate,loop);rv_merge(c,f,other);free(other);continue;
        }
        if(s->kind==ST_BREAK||s->kind==ST_CONTINUE){if(loop)rv_merge(c,s->kind==ST_BREAK?loop->breaking:loop->continuing,f);f->alive=0;continue;}
        rv_full(c,f,s->expression);if(s->kind==ST_RETURN)f->alive=0;
        if(s->kind==ST_SWITCH||s->kind==ST_CASE)c->failed=1;
    }
}
static void rv_clear_expr(Expr *e)
{
    unsigned i;if(!e)return;memset(&e->range,0,sizeof e->range);
    rv_clear_expr(e->left);rv_clear_expr(e->right);rv_clear_expr(e->third);for(i=0;i<e->arg_count;++i)rv_clear_expr(e->args[i]);
}
static void rv_clear(Statement *s)
{
    for(;s;s=s->next){rv_clear_expr(s->expression);rv_clear_expr(s->step);rv_clear(s->initial);rv_clear(s->body);rv_clear(s->alternate);}
}
static void range_prepare(Function *f)
{
    RvContext *c=allocate(sizeof *c);RvFlow *flow=allocate(sizeof *flow);unsigned i;
    c->function=f;c->budget=RV_BUDGET;flow->alive=1;rv_clear(f->body);
    for(i=0;i<cg.parser->symbol_count;++i)c->private[i]=(unsigned char)(cg.parser->symbols[i].owner==f->id&&body_private(&cg.parser->symbols[i])&&known_integer(cg.parser->symbols[i].type));
    rv_statements(c,flow,f->body,NULL);
    if(!c->failed)for(i=0;i<c->count;++i)c->notes[i].expr->range=c->notes[i].value;
    free(c->notes);free(flow);free(c);
}
