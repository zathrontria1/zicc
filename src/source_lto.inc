/* Source LTO parses each C file with its own macros and names, then joins
 * the typed programs before generating assembly. Each file keeps its own
 * storage, literals, and local symbols. */
static void lto_parse(Parser *p,const char *path,const char *include_directory,FILE *dependencies)
{
    const char *name=strrchr(path,'/'),*back=strrchr(path,'\\'),*end;size_t n=0;
    p->path=intern_path(p,path);p->line=p->column=1;
    if (!name || (back && back > name)) {
        name = back;
    }
    name = name ? name + 1 : path;
    end=strrchr(name,'.');if(!end||end==name)end=name+strlen(name);
    while(name<end&&n+1<sizeof p->unit){
        char ch=*name++;
        p->unit[n++]=(char)(((ch>='a'&&ch<='z')||(ch>='A'&&ch<='Z')||(ch>='0'&&ch<='9'))?ch:'_');
    }
    p->function_tail=&p->functions;p->string_tail=&p->strings;
    p->source=preprocess_with_embeds(path,include_directory,&p->embeds,binary64_enabled,dependencies);lex(p);translation_unit(p);
    /* Manual builds can assemble files with the same basename. Their
     * private WRAM segments still need distinct linker identities. */
    uint32_t hash=UINT32_C(2166136261);
    for(const unsigned char *ch=(const unsigned char *)path;*ch;++ch)
        hash=(hash^*ch)*UINT32_C(16777619);
    for(unsigned i=0;i<p->symbol_count;++i){
        Symbol *s=&p->symbols[i];
        if(s->wram&&s->internal){
            char original[sizeof s->asm_name];
            strcpy(original,s->asm_name);
            snprintf(s->asm_name,sizeof s->asm_name,"w%08lX_%.112s",(unsigned long)hash,original);
        }
    }
}
static void lto_free(Parser *p)
{
    unsigned i;
    while(p->functions){Function *next=p->functions->next;free_statements(p->functions->body);free(p->functions);p->functions=next;}
    free(p->source);
    while(p->strings){String *next=p->strings->next;free(p->strings->bytes);free(p->strings);p->strings=next;}
    for(i=0;i<p->path_count;++i)free(p->paths[i]);
    for(i=0;i<p->tag_count;++i){Member *member=p->tags[i].members;while(member){Member *next=member->next;free(member);member=next;}}
    for(i=0;i<p->symbol_count;++i){
        Relocation *r=p->symbols[i].relocations;
        while(r){Relocation *next=r->next;free(r);r=next;}
        free(p->symbols[i].initializer);
    }
    while(p->embeds){EmbeddedRange *next=p->embeds->next;free(p->embeds->resource);free(p->embeds);p->embeds=next;}
    free(p);
}
typedef struct {
    char name[64];Symbol *winner,*symbol;int provided,hint,force,never,noclone,used,called,address_taken;
    Symbol *declarations[32];unsigned declaration_count;
} LtoExternal;
typedef struct {
    Parser *program,**units;unsigned count,external_count;
    unsigned parent[2049],function_base[32];
    Symbol *map[32][1024];LtoExternal external[1024];
    Structure *left[128],*right[128];unsigned pairs;
    Location at;
} LtoMerge;
static unsigned lto_root(LtoMerge *m,unsigned id)
{
    while(m->parent[id]!=id){m->parent[id]=m->parent[m->parent[id]];id=m->parent[id];}return id;
}
static unsigned lto_structure_id(LtoMerge *m,Structure *s)
{
    unsigned u,i;for(u=0;u<m->count;++u)for(i=0;i<m->units[u]->tag_count;++i)
        if(s==&m->units[u]->tags[i])return u*64+i+1;
    error_at(m->at,"source LTO encountered an unowned aggregate type");
}
static int lto_compatible(LtoMerge *m,Type a,Type b)
{
    Member *x,*y;unsigned i,ra,rb;
    if(a.base!=b.base||a.is_bool!=b.is_bool||a.is_short!=b.is_short||a.is_plain_char!=b.is_plain_char||a.pointers!=b.pointers||a.constant!=b.constant||
       a.is_volatile!=b.is_volatile||a.is_unsigned!=b.is_unsigned||a.pointer_constants!=b.pointer_constants||
       a.pointer_volatiles!=b.pointer_volatiles||a.far_pointers!=b.far_pointers)return 0;
    if(a.array!=b.array&&(!a.array||!b.array||(a.array!=~0u&&b.array!=~0u)))return 0;
    if((a.element!=NULL)!=(b.element!=NULL))return 0;
    if(a.element&&!lto_compatible(m,*a.element,*b.element))return 0;
    if(a.signature!=b.signature){
        int n;
        if(!a.signature||!b.signature||a.signature->variadic!=b.signature->variadic||
           !lto_compatible(m,a.signature->result,b.signature->result))return 0;
        if(a.signature->count<0||b.signature->count<0){
            FunctionType *prototype=a.signature->count<0?b.signature:a.signature;
            for(n=0;n<prototype->count;++n){
                Type parameter=unqualified_value(prototype->parameters[n]);
                if(!lto_compatible(m,parameter,promoted(parameter)))return 0;
            }
        }else{
            if(a.signature->count!=b.signature->count)return 0;
            for(n=0;n<a.signature->count;++n)
                if(!lto_compatible(m,unqualified_value(a.signature->parameters[n]),
                                    unqualified_value(b.signature->parameters[n])))return 0;
        }
    }
    if(a.base!=TY_STRUCT)return 1;
    if(!a.structure||!b.structure)return a.structure==b.structure;
    if(a.structure==b.structure)return 1;
    if(a.structure->is_union!=b.structure->is_union||strcmp(a.structure->name,b.structure->name))return 0;
    for(i=0;i<m->pairs;++i)if(m->left[i]==a.structure&&m->right[i]==b.structure)return 1;
    if(m->pairs==128)error_at(m->at,"source LTO aggregate comparison depth exceeds 128");
    m->left[m->pairs]=a.structure;m->right[m->pairs++]=b.structure;
    if(a.structure->complete&&b.structure->complete){
        if(a.structure->size!=b.structure->size)return 0;
        for(x=a.structure->members;x;x=x->next){
            if(a.structure->is_union){for(y=b.structure->members;y&&strcmp(x->name,y->name);y=y->next){}}
            else{y=b.structure->members;for(Member *p=a.structure->members;p!=x&&y;p=p->next)y=y->next;}
            if(!y||strcmp(x->name,y->name)||x->offset!=y->offset||
               x->bit_width!=y->bit_width||x->bit_shift!=y->bit_shift||!lto_compatible(m,x->type,y->type))return 0;
        }
        {unsigned na=0,nb=0;for(x=a.structure->members;x;x=x->next)++na;for(y=b.structure->members;y;y=y->next)++nb;if(na!=nb)return 0;}
    }
    ra=lto_root(m,lto_structure_id(m,a.structure));rb=lto_root(m,lto_structure_id(m,b.structure));
    if (ra != rb) {
        m->parent[rb] = ra;
    }
    return 1;
}
static int lto_inline_only(Symbol *s)
{
    return s->function&&s->defined&&s->inline_hint&&!s->inline_external&&!s->internal;
}
static void lto_check_declaration(LtoMerge *m,Symbol *a,Symbol *b)
{
    int i;Symbol *prototype;
    m->pairs=0;
    if(a->function!=b->function||!lto_compatible(m,a->type,b->type)){
        report_error(m->at,"source LTO conflicting type for '%s'",b->name);
        if(a->function!=b->function)return;
    }
    if(!a->function){
        if(a->dpage!=b->dpage||a->loram!=b->loram||a->type.banked!=b->type.banked||a->runtime_ram!=b->runtime_ram||a->wram!=b->wram)
            report_error(m->at,"source LTO conflicting placement for '%s'",b->name);
        return;
    }
    if(a->param_count>=0&&b->param_count>=0){
        if(a->param_count!=b->param_count||a->variadic!=b->variadic)report_error(m->at,"source LTO conflicting prototype for '%s'",b->name);
        else for(i=0;i<a->param_count;++i){m->pairs=0;
            if(!lto_compatible(m,unqualified_value(a->params[i]),unqualified_value(b->params[i])))
                report_error(m->at,"source LTO conflicting parameter type for '%s'",b->name);
        }
    }
    if(a->old_style!=b->old_style){
        prototype=a->old_style?b:a;
        if(prototype->variadic)report_error(m->at,"source LTO variadic/non-prototype conflict for '%s'",b->name);
        for(i=0;i<prototype->param_count;++i){m->pairs=0;
            if(!lto_compatible(m,unqualified_value(prototype->params[i]),promoted(prototype->params[i])))
                report_error(m->at,"source LTO default-promotion conflict for '%s'",b->name);
        }
    }
    if(a->interrupt&&b->interrupt&&a->interrupt!=b->interrupt)report_error(m->at,"source LTO conflicting interrupt kind for '%s'",b->name);
}
static LtoExternal *lto_external(LtoMerge *m,const char *name)
{
    unsigned i;for(i=0;i<m->external_count;++i)if(!strcmp(m->external[i].name,name))return &m->external[i];return NULL;
}
static Type lto_type(LtoMerge *m,Type t,unsigned unit)
{
    if(t.structure)t.tag=lto_root(m,lto_structure_id(m,t.structure));
    else if(t.tag)t.tag+=unit*64;
    if(t.enum_tag)t.enum_tag+=unit*64;
    if(t.element)t.element=type_copy(lto_type(m,*t.element,unit));
    if(t.signature){
        FunctionType *old=t.signature;
        int i;
        Type result=lto_type(m,old->result,unit);
        t.signature=function_signature(result,old->count,old->variadic,old->parameters).signature;
        for(i=0;i<old->count;++i)t.signature->parameters[i]=lto_type(m,old->parameters[i],unit);
    }
    return t;
}
static Symbol *lto_copy_symbol(LtoMerge *m,Symbol *old,unsigned unit)
{
    unsigned i;Symbol *s;
    if(m->program->symbol_count==1024)error_at(m->at,"source LTO combined symbol budget exceeds 1024");
    s=&m->program->symbols[m->program->symbol_count++];*s=*old;s->type=lto_type(m,s->type,unit);
    if(s->internal&&!s->owner)snprintf(s->asm_name,sizeof s->asm_name,"__lto_%u_%.100s",unit,old->asm_name);
    for(i=0;i<(unsigned)(s->param_count<0?0:s->param_count);++i)s->params[i]=lto_type(m,s->params[i],unit);
    if(s->owner)s->owner+=m->function_base[unit];
    s->initializer=old->initializer;old->initializer=NULL;
    s->relocations=old->relocations;old->relocations=NULL;return s;
}
static unsigned lto_symbol_unit(LtoMerge *m,Symbol *s)
{
    unsigned u,i;for(u=0;u<m->count;++u)for(i=0;i<m->units[u]->symbol_count;++i)if(s==&m->units[u]->symbols[i])return u;
    error_at(m->at,"source LTO encountered an unowned symbol");
}
static void lto_expression(LtoMerge *m,Expr *e,unsigned unit)
{
    unsigned i;if(!e)return;e->type=lto_type(m,e->type,unit);
    if(e->symbol)e->symbol=m->map[unit][e->symbol-m->units[unit]->symbols];
    lto_expression(m,e->left,unit);lto_expression(m,e->right,unit);lto_expression(m,e->third,unit);
    for(i=0;i<e->arg_count;++i)lto_expression(m,e->args[i],unit);
}
static void lto_statements(LtoMerge *m,Statement *s,unsigned unit)
{
    for(;s;s=s->next){lto_expression(m,s->expression,unit);lto_expression(m,s->step,unit);
        lto_statements(m,s->initial,unit);lto_statements(m,s->body,unit);lto_statements(m,s->alternate,unit);}
}
static Parser *lto_merge(Parser *options,Parser **units,unsigned count)
{
    LtoMerge *m=allocate(sizeof *m);Parser *p=allocate(sizeof *p);unsigned u,i,j,handlers=0;
    Function **tail=&p->functions;String **strings=&p->strings;EmbeddedRange **embeds=&p->embeds;
    *p=*options;p->source=NULL;p->path=units[0]->path;m->program=p;m->units=units;m->count=count;m->at=(Location){p->path,1,1};
    strcpy(p->unit,count==1?units[0]->unit:"lto_program");
    for(i=0;i<2049;++i)m->parent[i]=i;
    for(u=0;u<count;++u){
        for(j=0;j<u;++j)if(!strcmp(units[j]->unit,units[u]->unit))error_at((Location){units[u]->path,1,1},"source LTO requires distinct sanitized unit names");
        m->function_base[u]=p->function_count;p->function_count+=units[u]->function_count;
        for(i=0;i<units[u]->symbol_count;++i){Symbol *s=&units[u]->symbols[i];LtoExternal *entry;int provided;
            if (s->owner || s->internal || s->enumerator) {
                continue;
            }
            m->at = (Location){units[u]->path, 1, 1};
            entry=lto_external(m,s->name);provided=s->defined&&!lto_inline_only(s);
            if(!entry){if(m->external_count==1024)error_at(m->at,"source LTO external symbol budget exceeds 1024");
                entry=&m->external[m->external_count++];strcpy(entry->name,s->name);entry->winner=s;entry->provided=provided;
            }else{
                for(j=0;j<entry->declaration_count;++j)lto_check_declaration(m,entry->declarations[j],s);
                if(provided&&entry->provided)error_at(m->at,"source LTO duplicate definition of '%s'",s->name);
                if(provided){entry->winner=s;entry->provided=1;}
                else if(!entry->provided&&!lto_inline_only(s)&&s->param_count>entry->winner->param_count)entry->winner=s;
            }
            entry->declarations[entry->declaration_count++]=s;
            entry->hint|=s->inline_hint;entry->force|=s->always_inline;entry->never|=s->noinline;entry->noclone|=s->noclone;
            entry->used|=s->used;entry->called|=s->called;entry->address_taken|=s->address_taken;
            if(entry->force&&entry->never)error_at(m->at,"source LTO always_inline conflicts with noinline for '%s'",s->name);
        }
    }
    if(p->function_count>1024)error_at(m->at,"source LTO function budget exceeds 1024");
    for(u=0;u<count;++u)for(i=0;i<units[u]->tag_count;++i)
        for(Member *member=units[u]->tags[i].members;member;member=member->next)member->type=lto_type(m,member->type,u);
    for(i=0;i<m->external_count;++i){LtoExternal *e=&m->external[i];Symbol *s;
        u=lto_symbol_unit(m,e->winner);s=lto_copy_symbol(m,e->winner,u);e->symbol=s;
        s->defined=e->provided;s->inline_external=1;s->inline_hint|=e->hint;s->always_inline=e->force;s->noinline=e->never;s->noclone=e->noclone;s->used=e->used;s->called=e->called;
        s->address_taken|=e->address_taken;
        if(s->interrupt&&(s->called||s->address_taken))error_at(m->at,"source LTO interrupt handler '%s' cannot be called",s->name);
    }
    for(u=0;u<count;++u)for(i=0;i<units[u]->symbol_count;++i){Symbol *s=&units[u]->symbols[i];LtoExternal *e=NULL;
        if(!s->owner&&!s->internal&&!s->enumerator)e=lto_external(m,s->name);
        if(e&&!lto_inline_only(s))m->map[u][i]=e->symbol;
        else{Symbol *copy=lto_copy_symbol(m,s,u);m->map[u][i]=copy;
            if(e){copy->always_inline=e->force;copy->noinline=e->never;copy->noclone=e->noclone;}}
    }
    for(i=0;i<p->symbol_count;++i){
        Relocation *r;
        for(r=p->symbols[i].relocations;r;r=r->next)if(r->symbol){
            unsigned owner=lto_symbol_unit(m,r->symbol);
            r->symbol=m->map[owner][r->symbol-m->units[owner]->symbols];
        }
    }
    for(u=0;u<count;++u){Function *f=units[u]->functions;String *s=units[u]->strings;
        while(f){Function *next=f->next;f->symbol=m->map[u][f->symbol-units[u]->symbols];f->id+=m->function_base[u];f->next=NULL;
            if(f->symbol->interrupt){unsigned bit=1u<<f->symbol->interrupt;if(handlers&bit)error_at(m->at,"source LTO duplicate interrupt handler");handlers|=bit;}
            lto_statements(m,f->body,u);*tail=f;tail=&f->next;f=next;}
        units[u]->functions=NULL;
        while(s){String *next=s->next;s->id=++p->string_count;s->next=NULL;*strings=s;strings=&s->next;s=next;}units[u]->strings=NULL;
        *embeds=units[u]->embeds;while(*embeds)embeds=&(*embeds)->next;units[u]->embeds=NULL;
    }
    p->function_tail=tail;p->string_tail=strings;free(m);return p;
}
