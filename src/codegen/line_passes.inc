/* Post-emission passes over one finished function's assembly lines. They run
 * after the frame passes and before relaxation, so branches are still
 * "bxx :+ / jmp .loword(cg_N) / :" sequences. A backward liveness analysis of
 * A, X, Y and the N/Z/C/V flags over the function's control flow decides
 * where an instruction's register or flag results are unobserved. Anything
 * the analysis does not model (unknown instructions, indirect transfers)
 * reads everything, so it only blocks rewrites. */
enum { LP_AL=1,LP_AH=2,LP_A=LP_AL|LP_AH,LP_X=4,LP_Y=8,LP_N=16,LP_Z=32,LP_C=64,LP_V=128,LP_FLAGS=LP_N|LP_Z|LP_C|LP_V,LP_ALL=255 };
typedef struct {
    const char *text; size_t length; const char *op;
    int label, m8, x8, target, first_incoming, next_incoming, ends, call, indirect,wrap_step;
    unsigned use, def, live, out;
    char *replace; int deleted; char *before;
} LpLine;
typedef struct { char *text; LpLine *lines; unsigned count; int indirect, calls, helpers; } LpUnit;
static int lp_is(const LpLine *l,const char *name){return l->op&&op_is(l->op,name);}
static int lp_line_is(const LpLine *l,const char *text){size_t n=strlen(text);return l->op&&l->length==n+4&&!strncmp(l->op,text,n);}
/* Operand text after the mnemonic, and its length */
static const char *lp_operand(const LpLine *l,size_t *n)
{
    if(!l->op||l->length<8||l->op[3]!=' '){*n=0;return "";}
    *n=l->length-8;return l->op+4;
}
static int lp_operand_is(const LpLine *l,const char *text,size_t n){size_t m;const char *o=lp_operand(l,&m);return m==n&&!strncmp(o,text,n);}
static unsigned lp_index_use(const LpLine *l)
{
    size_t n;const char *o=lp_operand(l,&n);unsigned use=0;
    if(n>=2&&o[n-2]==','&&o[n-1]=='x')use|=LP_X;
    if(n>=2&&o[n-2]==','&&o[n-1]=='y')use|=LP_Y;
    if(n>=3&&o[0]=='('&&memchr(o,',',n)&&o[n-1]==')'&&o[n-2]=='x')use|=LP_X;
    return use;
}
static void lp_effects(LpLine *l)
{
    static const char *const branches[]={"bcc","bcs","beq","bne","bmi","bpl","bvc","bvs"};
    static const unsigned reads[]={LP_C,LP_C,LP_Z,LP_Z,LP_N,LP_N,LP_V,LP_V};
    const char *op=l->op;unsigned a=l->m8?LP_AL:LP_A,x=l->x8?0:LP_X,y=l->x8?0:LP_Y,idx=lp_index_use(l);size_t n;unsigned i;
    const char *operand=lp_operand(l,&n);int accumulator=!n||(n==1&&operand[0]=='a');
    l->use=LP_ALL;l->def=0;l->target=-1;
    for(i=0;i<8;++i)if(op_is(op,branches[i])){l->use=reads[i];return;}
    if(op_is(op,"bra")||op_is(op,"brl")){l->use=0;l->ends=1;return;}
    if(op_is(op,"jmp")||op_is(op,"jml")){
        l->ends=1;
        if(n&&(operand[0]=='('||operand[0]=='[')){l->indirect=1;l->use=LP_ALL;return;}
        l->use=0;return; /* resolved as a label below, or a tail call */
    }
    /* A word result leaves X caller-clobbered */
    if(op_is(op,"rts")||op_is(op,"rtl")){l->ends=1;l->use=LP_Y|(cg.lp_value_result?(LP_A|(cg.lp_word_result?0:LP_X)):0);return;}
    if(op_is(op,"rti")||op_is(op,"brk")||op_is(op,"cop")||op_is(op,"stp")||op_is(op,"wai")){l->ends=op_is(op,"rti")||op_is(op,"stp");return;}
    /* Callees read A, X, Y (preserved) and no flags; their results stay
     * unmodelled, so nothing counts as defined. */
    if(op_is(op,"jsr")||op_is(op,"jsl")){l->call=1;l->use=LP_A|LP_X|LP_Y;return;}
    if(op_is(op,"lda")){l->use=idx;l->def=a|LP_N|LP_Z;return;}
    if(op_is(op,"ldx")){l->use=idx;l->def=x|LP_N|LP_Z;return;}
    if(op_is(op,"ldy")){l->use=idx;l->def=y|LP_N|LP_Z;return;}
    if(op_is(op,"sta")){l->use=a|idx;return;}
    if(op_is(op,"stx")){l->use=LP_X|idx;return;}
    if(op_is(op,"sty")){l->use=LP_Y|idx;return;}
    if(op_is(op,"stz")){l->use=idx;return;}
    if(op_is(op,"adc")||op_is(op,"sbc")){l->use=a|LP_C|idx;l->def=a|LP_FLAGS;return;}
    if(op_is(op,"and")||op_is(op,"ora")||op_is(op,"eor")){l->use=a|idx;l->def=a|LP_N|LP_Z;return;}
    if(op_is(op,"cmp")){l->use=a|idx;l->def=LP_N|LP_Z|LP_C;return;}
    if(op_is(op,"cpx")){l->use=LP_X|idx;l->def=LP_N|LP_Z|LP_C;return;}
    if(op_is(op,"cpy")){l->use=LP_Y|idx;l->def=LP_N|LP_Z|LP_C;return;}
    if(op_is(op,"bit")){l->use=a|idx;l->def=LP_Z;return;}
    if(op_is(op,"inc")||op_is(op,"dec")){l->use=accumulator?a:idx;l->def=(accumulator?a:0)|LP_N|LP_Z;return;}
    if(op_is(op,"asl")||op_is(op,"lsr")){l->use=accumulator?a:idx;l->def=(accumulator?a:0)|LP_N|LP_Z|LP_C;return;}
    if(op_is(op,"rol")||op_is(op,"ror")){l->use=(accumulator?a:idx)|LP_C;l->def=(accumulator?a:0)|LP_N|LP_Z|LP_C;return;}
    if(op_is(op,"inx")||op_is(op,"dex")){l->use=LP_X;l->def=x|LP_N|LP_Z;return;}
    if(op_is(op,"iny")||op_is(op,"dey")){l->use=LP_Y;l->def=y|LP_N|LP_Z;return;}
    if(op_is(op,"tax")){l->use=l->x8?LP_AL:LP_A;l->def=x|LP_N|LP_Z;return;}
    if(op_is(op,"tay")){l->use=l->x8?LP_AL:LP_A;l->def=y|LP_N|LP_Z;return;}
    if(op_is(op,"txa")){l->use=LP_X;l->def=a|LP_N|LP_Z;return;}
    if(op_is(op,"tya")){l->use=LP_Y;l->def=a|LP_N|LP_Z;return;}
    if(op_is(op,"txy")){l->use=LP_X;l->def=y|LP_N|LP_Z;return;}
    if(op_is(op,"tyx")){l->use=LP_Y;l->def=x|LP_N|LP_Z;return;}
    if(op_is(op,"tsc")||op_is(op,"tdc")){l->use=0;l->def=LP_A|LP_N|LP_Z;return;}
    if(op_is(op,"tsx")){l->use=0;l->def=x|LP_N|LP_Z;return;}
    if(op_is(op,"tcs")||op_is(op,"tcd")){l->use=LP_A;l->def=op[2]=='d'?LP_N|LP_Z:0;return;}
    if(op_is(op,"txs")){l->use=LP_X;return;}
    if(op_is(op,"xba")){l->use=LP_A;l->def=LP_N|LP_Z;return;}
    if(op_is(op,"clc")||op_is(op,"sec")){l->use=0;l->def=LP_C;return;}
    if(op_is(op,"clv")){l->use=0;l->def=LP_V;return;}
    if(op_is(op,"nop")){l->use=0;return;}
    if(op_is(op,"pha")){l->use=a;return;}
    if(op_is(op,"phx")){l->use=LP_X;return;}
    if(op_is(op,"phy")){l->use=LP_Y;return;}
    if(op_is(op,"pea")||op_is(op,"pei")||op_is(op,"phb")||op_is(op,"phd")||op_is(op,"phk")||op_is(op,"per")){l->use=0;return;}
    if(op_is(op,"pla")){l->use=0;l->def=a|LP_N|LP_Z;return;}
    if(op_is(op,"plx")){l->use=0;l->def=x|LP_N|LP_Z;return;}
    if(op_is(op,"ply")){l->use=0;l->def=y|LP_N|LP_Z;return;}
    if(op_is(op,"plb")||op_is(op,"pld")){l->use=0;l->def=LP_N|LP_Z;return;}
    if(op_is(op,"php")){l->use=LP_FLAGS;return;}
    if((op_is(op,"rep")||op_is(op,"sep"))&&n==4&&!strncmp(operand,"#$20",4)){l->use=0;return;}
    /* REP/SEP, PLP, block moves and anything else: reads everything */
}
static int lp_branch(const LpLine *l)
{
    static const char *const names[]={"bcc","bcs","beq","bne","bmi","bpl","bvc","bvs","bra","brl"};
    unsigned i;for(i=0;i<10;++i)if(lp_is(l,names[i]))return 1;
    return 0;
}
static Symbol *lp_callee(const LpLine *call)
{
    size_t length;
    const char *name=lp_operand(call,&length);
    unsigned i;
    if(length>9&&!strncmp(name,".loword(",8)&&name[length-1]==')'){
        name+=8;length-=9;
    }
    if(length<2||name[0]!='_'||name[1]=='_')return NULL;
    for(i=0;i<cg.parser->symbol_count;++i){
        Symbol *s=&cg.parser->symbols[i];
        if(s->function&&strlen(s->asm_name)==length-1&&!memcmp(name+1,s->asm_name,length-1))
            return s;
    }
    return NULL;
}
static unsigned lp_call_use(const LpLine *call)
{
    Symbol *callee=lp_callee(call);
    if(!callee||callee->variadic||callee->param_count<0)return LP_A|LP_X|LP_Y;
    if(callee->old_style){
        /* A visible K&R definition still has fixed incoming register homes */
        Function *body=inl.by_symbol[callee-cg.parser->symbols];
        if(!body||body->aggregate_abi||body->uses_varargs||callee->interrupt||
           body_asm_statements(body->body))return LP_A|LP_X|LP_Y;
    }
    return LP_Y|
           (callee->param_count>=1&&register_parameter(0,callee->params[0])?LP_X:0)|
           (callee->param_count>=2&&register_parameter(1,callee->params[1])?LP_A:0);
}
static void lp_parse(LpUnit *u,const char *source,size_t length)
{
    const char *p;int m8=0,x8=0,wrap_step=0;unsigned i,label_count=0;
    AssemblyLabels labels;
    memset(u,0,sizeof *u);
    u->text=malloc(length+1);u->lines=malloc((length/2+2)*sizeof *u->lines);
    if(!u->text||!u->lines){fputs("out of memory emitting assembly\n",stderr);exit(EXIT_FAILURE);}
    memcpy(u->text,source,length);u->text[length]=0;
    for(p=u->text;*p;){
        const char *eol=strchr(p,'\n');LpLine *l=&u->lines[u->count++];
        if(!eol)eol=p+strlen(p);
        memset(l,0,sizeof *l);l->text=p;l->length=(size_t)(eol-p);l->target=-1;
        l->first_incoming=l->next_incoming=-1;
        l->label=assembly_decode(p,l->length,&m8,&x8,&l->op);
        l->m8=m8;l->x8=x8;
        if(!strncmp(p,"; near pointer wrap\n",20))wrap_step=1;
        if(!l->op&&!l->label&&l->length&&*p=='.'&&(!strncmp(p,".word",5)||!strncmp(p,".addr",5)||!strncmp(p,".byte",5)||!strncmp(p,".faraddr",8)))u->indirect=1;
        if(l->op){l->wrap_step=wrap_step;wrap_step=0;}
        if(l->label)++label_count;
        p=*eol?eol+1:eol;
    }
    assembly_labels_init(&labels,label_count);
    for(i=0;i<u->count;++i){
        const LpLine *l=&u->lines[i];
        if(l->label)assembly_label_add(&labels,l->text,l->length,i);
    }
    for(i=0;i<u->count;++i){
        LpLine *l=&u->lines[i];
        if(!l->op)continue;
        lp_effects(l);
        if(l->indirect)u->indirect=1;
        if(l->call)++u->calls;
        if(lp_branch(l)||op_is(l->op,"jmp")||op_is(l->op,"jml")){
            size_t n;const char *name=lp_operand(l,&n);
            if(!l->indirect&&n){
                if(n>9&&!strncmp(name,".loword(",8)&&name[n-1]==')'){name+=8;n-=9;}
                l->target=assembly_label_target(&labels,i,name,n);
                if(l->target<0&&(op_is(l->op,"jmp")||op_is(l->op,"jml"))){
                    /* A transfer out of the function: a tail call */
                    l->call=1;++u->calls;
                    l->use=lp_call_use(l);
                    if(!strncmp(name,"__",2))u->helpers=1;
                }else if(l->target<0)l->use=LP_ALL;
            }
        }
        if(op_is(l->op,"jsr")||op_is(l->op,"jsl")){
            size_t n;const char *name=lp_operand(l,&n);
            l->use=lp_call_use(l);
            static const char stack_args[]="; unprototyped stack arguments: ";
            if(i&&u->lines[i-1].length>sizeof stack_args-1&&
               !strncmp(u->lines[i-1].text,stack_args,sizeof stack_args-1)){
                Symbol *callee=lp_callee(l);
                size_t name_length=u->lines[i-1].length-(sizeof stack_args-1);
                if(callee&&callee->param_count<0&&strlen(callee->asm_name)==name_length&&
                   !memcmp(u->lines[i-1].text+sizeof stack_args-1,callee->asm_name,name_length))l->use=LP_Y;
            }
            if(n>8&&!strncmp(name,".loword(",8)){name+=8;}
            if(!strncmp(name,"__",2)||name[0]=='('||name[0]=='[')u->helpers=1;
        }
    }
    assembly_labels_free(&labels);
    for(i=u->count;i-->0;){
        LpLine *l=&u->lines[i];
        if(l->target>=0){
            LpLine *target=&u->lines[l->target];
            l->next_incoming=target->first_incoming;
            target->first_incoming=(int)i;
        }
    }
}
static void lp_free_edits(LpUnit *u)
{
    unsigned i;
    for(i=0;i<u->count;++i){free(u->lines[i].replace);free(u->lines[i].before);}
}
/* Backward liveness: live = registers and flags read before being written
 * from the start of the line; out = the same after it. */
static void lp_liveness(LpUnit *u)
{
    int changed=1;unsigned i;
    for(i=0;i<u->count;++i)u->lines[i].live=u->lines[i].out=0;
    while(changed){
        changed=0;
        for(i=u->count;i-->0;){
            LpLine *l=&u->lines[i];unsigned out=0,live;
            if(!l->op){out=i+1<u->count?u->lines[i+1].live:LP_ALL;live=out;}
            else{
                if(!l->ends)out|=i+1<u->count?u->lines[i+1].live:LP_ALL;
                if(l->target>=0)out|=u->lines[l->target].live;
                live=l->use|(out&~l->def);
            }
            if(live!=l->live||out!=l->out){l->live=live;l->out=out;changed=1;}
        }
    }
}
/* Next or previous instruction past comments only; -1 at a label, directive or edge */
static int lp_next(const LpUnit *u,unsigned k,int direction)
{
    unsigned i=k;
    for(;;){
        if(direction<0){if(!i)return -1;--i;}else if(++i>=u->count)return -1;
        if(!u->lines[i].length)return -1;
        if(u->lines[i].text[0]==';')continue;
        return u->lines[i].op?(int)i:-1;
    }
}
static void lp_set(LpLine *l,const char *format,...)
{
    va_list args;int n;char *text;
    va_start(args,format);n=vsnprintf(NULL,0,format,args);va_end(args);
    text=malloc((size_t)n+1);if(!text){fputs("out of memory emitting assembly\n",stderr);exit(EXIT_FAILURE);}
    va_start(args,format);vsnprintf(text,(size_t)n+1,format,args);va_end(args);
    free(l->replace);l->replace=text;l->deleted=0;
}
static void lp_insert(LpLine *l,const char *text)
{
    size_t old=l->before?strlen(l->before):0,n=strlen(text);char *b=realloc(l->before,old+n+1);
    if(!b){fputs("out of memory emitting assembly\n",stderr);exit(EXIT_FAILURE);}
    memcpy(b+old,text,n+1);l->before=b;
}
/* Write the edited lines back over the function's text */
static void lp_emit(LpUnit *u,size_t at)
{
    unsigned i;
    cg.length=at;cg.assembly[at]=0;
    for(i=0;i<u->count;++i){
        LpLine *l=&u->lines[i];
        if(l->before)code("%s",l->before);
        if(l->deleted)continue;
        if(l->replace){code("%s\n",l->replace);continue;}
        if(i+1<u->count||l->length)code("%.*s\n",(int)l->length,l->text);
    }
}
/* Workspace words (scratch offset 2n) the text references: two bytes for
 * direct/near-indirect accesses and three bytes for far-indirect `[dp]`. */
static unsigned lp_text_words(const char *p,const char *end)
{
    unsigned taken=0;const char *q;
    for(q=p;q<end;++q){
        if(end-q>=11&&(!strncmp(q,"__arith_lhs",11)||!strncmp(q,"__arith_rhs",11))){
            unsigned byte=q[8]=='r'?4:0;
            unsigned bytes=(q>p&&q[-1]=='[')?3u:2u;
            q+=11;
            if(q<end&&*q=='+')byte+=(unsigned)strtoul(q+1,(char**)&q,10);
            dp_mark_width(&taken,byte,bytes);--q;
        }else if(*q=='$'&&q>p&&(q[-1]==':'||q[-1]=='['||q[-1]=='(')&&end-q>=3&&
                 isxdigit((unsigned char)q[1])&&isxdigit((unsigned char)q[2])&&(end-q==3||!isxdigit((unsigned char)q[3])))
            dp_mark_width(&taken,(unsigned)strtoul(q+1,NULL,16)-0xE0u,(q>p&&q[-1]=='[')?3u:2u);
    }
    return taken;
}
/* A workspace word operand "z:__arith_lhs+N" / "z:__arith_rhs+N" as its byte
 * offset, or -1. */
static int lp_workspace_offset(const char *o,size_t n)
{
    unsigned byte;char *stop;
    if(n<11||strncmp(o,"__arith_",8)||(strncmp(o+8,"lhs",3)&&strncmp(o+8,"rhs",3)))return -1;
    byte=o[8]=='r'?4:0;
    if(n==11)return (int)byte;
    if(o[11]!='+')return -1;
    byte+=(unsigned)strtoul(o+12,&stop,10);
    if(stop!=o+n||byte>30)return -1;
    return (int)byte;
}
static int lp_workspace_word(const char *o,size_t n)
{
    return n>2&&!strncmp(o,"z:",2)?lp_workspace_offset(o+2,n-2):-1;
}
static int lp_workspace_pointer(const char *o,size_t n)
{
    return n>2&&o[0]=='('&&o[n-1]==')'?lp_workspace_offset(o+1,n-2):-1;
}
static int lp_accumulator_memory(const LpLine *l)
{
    return lp_is(l,"lda")||lp_is(l,"sta")||lp_is(l,"adc")||lp_is(l,"sbc")||
           lp_is(l,"and")||lp_is(l,"ora")||lp_is(l,"eor")||lp_is(l,"cmp");
}
/* Bytes a direct operand access covers: the register width, or four when unknown */
static int lp_width(const LpLine *l)
{
    static const char *const a_ops[]={"lda","sta","adc","sbc","cmp","and","ora","eor","bit","inc","dec","asl","lsr","rol","ror","stz","tsb","trb"};
    static const char *const x_ops[]={"ldx","stx","cpx","ldy","sty","cpy"};
    unsigned i;
    for(i=0;i<sizeof a_ops/sizeof *a_ops;++i)if(lp_is(l,a_ops[i]))return l->m8?1:2;
    for(i=0;i<sizeof x_ops/sizeof *x_ops;++i)if(lp_is(l,x_ops[i]))return l->x8?1:2;
    if(lp_is(l,"pei"))return 2;
    return 4;
}
static int lp_overlaps_n(const LpLine *l,int at,int word,int bytes){return at<=word+bytes-1&&at+lp_width(l)-1>=word;}
static int lp_overlaps(const LpLine *l,int at,int word){return lp_overlaps_n(l,at,word,2);}
static int lp_store_op(const LpLine *l)
{
    return lp_is(l,"sta")||lp_is(l,"stx")||lp_is(l,"sty")||lp_is(l,"stz")||lp_is(l,"inc")||lp_is(l,"dec")||
           lp_is(l,"asl")||lp_is(l,"lsr")||lp_is(l,"rol")||lp_is(l,"ror")||lp_is(l,"tsb")||lp_is(l,"trb");
}
/* The innermost loop around line k: a label h <= k that a branch b >= k jumps
 * back to, entered only by falling into h. Returns h and sets *back to the
 * last such branch, or -1. */
static int lp_loop(const LpUnit *u,unsigned k,unsigned *back)
{
    int h;
    for(h=(int)k;h>=0;--h){
        unsigned j,last=0;int found=0;
        if(!u->lines[h].label)continue;
        for(j=k;j<u->count;++j)if(u->lines[j].op&&u->lines[j].target==h){found=1;last=j;}
        if(!found)continue;
        *back=last;return h;
    }
    return -1;
}
/* Entries of the loop region [h, b]: falling into h's label group from above,
 * or unconditional jumps from outside to a label of that group. Each entry
 * gets a preheader copy: sites[] holds the lines to insert before. Any other
 * transfer from outside into the region rejects it. */
static int lp_entries(const LpUnit *u,unsigned h,unsigned b,unsigned *sites,unsigned *count)
{
    unsigned j,group=h,end=h;int prev;
    if(u->indirect)return 0;
    while(group>0&&!u->lines[group-1].op)--group;
    while(end+1<u->count&&!u->lines[end+1].op)++end;
    *count=0;
    for(j=0;j<u->count;++j){
        const LpLine *l=&u->lines[j];
        if(!l->op||l->target<0||(j>=h&&j<=b))continue;
        if((unsigned)l->target<group||(unsigned)l->target>b)continue;
        if((unsigned)l->target>end||!l->ends||lp_is(l,"jml")||*count==8)return 0;
        sites[(*count)++]=j;
    }
    for(prev=(int)group-1;prev>=0&&!u->lines[prev].op;--prev);
    if(prev>=0&&!u->lines[prev].ends){if(*count==8)return 0;sites[(*count)++]=group;}
    return *count>0;
}
static int lp_region_writes(const LpUnit *u,unsigned h,unsigned b,const char *operand,size_t n,int word)
{
    unsigned j;
    for(j=h;j<=b;++j){
        const LpLine *l=&u->lines[j];size_t m;const char *o;
        if(!l->op)continue;
        if(l->call||lp_is(l,"mvn")||lp_is(l,"mvp")||(l->use==LP_ALL&&!lp_is(l,"rep")&&!lp_is(l,"sep")))return 1;
        o=lp_operand(l,&m);
        if(word>=0){
            int w=lp_workspace_word(o,m);
            if(w<0&&lp_text_words(o,o+m)&(3u<<(word/2)))return 1; /* other spelling of the workspace */
            if(w>=0&&lp_overlaps(l,w,word)&&lp_store_op(l))return 1;
        }else if(m==n&&!strncmp(o,operand,n)&&lp_store_op(l))return 1;
    }
    return 0;
}
/* Precomputed loop-exit bounds. Index elimination tests "X - base == k" as
 * TXA/SEC/SBC base/CMP #k; with base invariant in the loop the test is
 * CPX of base+k, computed once ahead of the loop (and of enclosing loops in
 * which base is also invariant) into a free workspace word. The loop's A, C,
 * N and V results of the old test must be dead, its Z is the same. */
static int lp_stop_bounds(LpUnit *u,Function *f,size_t at)
{
    unsigned i,changed=0,used=lp_text_words(u->text,u->text+strlen(u->text));
    (void)f;(void)at;
    lp_liveness(u);
    for(i=0;i+2<u->count;++i){
        LpLine *t=&u->lines[i];int s1,s2,s3,last,h,word=-1,prev;unsigned k=0,back,free_word,b,sites[8],sites_count,e;size_t n;const char *o;char text[160],pre[256];
        if(!lp_line_is(t,"txa")||t->m8||t->x8)continue;
        if((s1=lp_next(u,i,1))<0||!lp_line_is(&u->lines[s1],"sec"))continue;
        if((s2=lp_next(u,(unsigned)s1,1))<0||!lp_is(&u->lines[s2],"sbc"))continue;
        last=s2;s3=lp_next(u,(unsigned)s2,1);
        if(s3>=0&&lp_is(&u->lines[s3],"cmp")&&!strncmp(u->lines[s3].op,"cmp #$",6)&&u->lines[s3].length==14){
            k=(unsigned)strtoul(u->lines[s3].op+6,NULL,16);last=s3;
        }
        if(u->lines[last].out&(LP_A|LP_N|LP_C|LP_V))continue;
        o=lp_operand(&u->lines[s2],&n);
        if(!k&&n>2&&(!strncmp(o,"z:",2)||!strncmp(o,"a:",2))&&!memchr(o,',',n)){
            /* X - base == 0 needs no precomputed bound at all */
            lp_set(t,"    cpx %.*s",(int)n,o);u->lines[s1].deleted=u->lines[s2].deleted=1;++changed;break;
        }
        /* The test must open its loop: only labels and comments before it */
        if((h=lp_loop(u,i,&back))<0||!lp_entries(u,(unsigned)h,back,sites,&sites_count))continue;
        for(prev=h+1;prev<(int)i&&!u->lines[prev].op;++prev);
        if(prev!=(int)i)continue;
        if(n>1&&o[0]=='#'){
            /* An immediate base needs no workspace */
            if(k)lp_set(t,"    cpx #.loword(%.*s+$%04X)",(int)(n-1),o+1,k);else lp_set(t,"    cpx %.*s",(int)n,o);
            u->lines[s1].deleted=u->lines[s2].deleted=1;if(last==s3)u->lines[s3].deleted=1;
            ++changed;continue;
        }
        if((word=lp_workspace_word(o,n))<0||(word&1))continue;
        if(lp_region_writes(u,(unsigned)h,back,o,n,word))continue;
        for(free_word=0;free_word<16&&(used>>free_word&1);++free_word);
        if(free_word==16)continue;
        /* Hoist past enclosing loops that keep base and give A and flags no meaning */
        b=back;
        for(;;){
            int up,h2;unsigned back2,sites2[8],count2;
            for(up=h-1;up>=0&&!u->lines[up].op;--up);
            if(up<0)break;
            h2=lp_loop(u,(unsigned)up,&back2);
            if(h2<0||back2<b||!lp_entries(u,(unsigned)h2,back2,sites2,&count2)||lp_region_writes(u,(unsigned)h2,back2,o,n,word))break;
            {int first=(int)h2;while(first<(int)u->count&&!u->lines[first].op)++first;
             if(first>=(int)u->count||u->lines[first].live&(LP_A|LP_FLAGS))break;}
            h=h2;b=back2;memcpy(sites,sites2,sizeof sites);sites_count=count2;
        }
        used|=1u<<free_word;
        snprintf(pre,sizeof pre,"; loop bound %.*s%+d precomputed\n    lda %.*s\n",(int)n,o,(int)(int16_t)k,(int)n,o);
        if(k==1||k==2||k==0xFFFF||k==0xFFFE){
            unsigned j,c=k<3?k:0x10000u-k;
            for(j=0;j<c;++j)strcat(pre,k<3?"    inc a\n":"    dec a\n");
        }else if(k){snprintf(text,sizeof text,"    clc\n    adc #$%04X\n",k);strcat(pre,text);}
        snprintf(text,sizeof text,"    sta z:__arith_lhs+%u\n",free_word*2);strcat(pre,text);
        for(e=0;e<sites_count;++e)lp_insert(&u->lines[sites[e]],pre);
        lp_set(t,"    cpx z:__arith_lhs+%u",free_word*2);
        u->lines[s1].deleted=u->lines[s2].deleted=1;if(last==s3)u->lines[s3].deleted=1;
        /* At the innermost head CPX now sets N/Z/C and A/V were dead, so the
         * preheader's clobbers are unobserved; enclosing heads were checked. */
        ++changed;
        break; /* one rewrite per analysis; the caller iterates */
    }
    return (int)changed;
}
/* Private storage: the arithmetic workspace, Y-frame slots and N,s slots.
 * No volatile object or escaping address lives there. */
static int lp_private(const char *o,size_t n)
{
    if(lp_workspace_word(o,n)>=0)return 1;
    if(cg.lp_volatile)return 0;
    if(n==9&&!strncmp(o,"a:$",3)&&o[7]==','&&o[8]=='y')return 1;
    if(n>=3&&n<=5&&o[n-2]==','&&o[n-1]=='s'){size_t i;for(i=0;i+2<n;++i)if(!isdigit((unsigned char)o[i]))return 0;return 1;}
    return 0;
}
static int lp_stack_op(const LpLine *l)
{
    static const char *const ops[]={"pha","phx","phy","php","phb","phd","phk","pea","pei","per","pla","plx","ply","plp","plb","pld","tcs","txs","rts","rtl","rti"};
    unsigned i;for(i=0;i<sizeof ops/sizeof *ops;++i)if(lp_is(l,ops[i]))return 1;
    return l->call;
}
/* Could line l change memory operand o (private, spelled once)? */
static const char *lp_near_name(const char *operand,size_t *length);
static size_t lp_named_base(const char **operand,size_t length)
{
    size_t i;
    const char *p=lp_near_name(*operand,&length);
    if(length>3&&(p[0]=='z'||p[0]=='f')&&p[1]==':'&&p[2]=='_'){p+=2;length-=2;}
    if(length<2||p[0]!='_')return 0;
    *operand=p;
    for(i=1;i<length&&(isalnum((unsigned char)p[i])||p[i]=='_');++i){}
    return i;
}
static int lp_field_displacement(const char *suffix,const char *end)
{
    if(suffix==end)return 0;
    if(end-suffix>=2&&end-suffix<=6&&suffix[0]=='+'&&isdigit((unsigned char)suffix[1])){
        char *next;
        long offset=strtol(suffix+1,&next,10);
        return next==end&&offset<=65535?(int)offset:-1;
    }
    if(end-suffix!=6||strncmp(suffix,"+$",2)||strspn(suffix+2,"0123456789abcdefABCDEF")!=4)return -1;
    return (int)strtol(suffix+2,NULL,16);
}
static int lp_named_word_alias(const char *a,size_t na,const char *b,size_t nb)
{
    if(na<3||nb<3||strncmp(a,"a:",2)||strncmp(b,"a:",2))return 0;
    a=lp_near_name(a,&na);b=lp_near_name(b,&nb);
    const char *end_a=a+na,*end_b=b+nb;
    size_t name=lp_named_base(&a,na),other=lp_named_base(&b,nb);
    if(!name||name!=other||memcmp(a,b,name))return 0;
    int first=lp_field_displacement(a+name,end_a);
    return first>=0&&lp_field_displacement(b+other,end_b)==first;
}
static int lp_frame_slot_escaped(const Function *f,int offset,int bytes)
{
    unsigned i;
    if(!cg.lp_frame_address)return 0;
    if(!f||f->uses_varargs||f->aggregate_abi)return 1;
    for(i=0;i<cg.parser->symbol_count;++i){
        const Symbol *v=&cg.parser->symbols[i];
        if(v->owner!=f->id||!v->offset)continue;
        if(!v->address_taken&&!v->type.array&&!structure_object(v->type)&&
           !loop_escapes(f->body,(Symbol *)v))continue;
        int start=(int)frame_offset(v->offset),end=start+(int)width(v->type);
        if(offset<end&&offset+bytes>start)return 1;
    }
    return 0;
}
static int lp_may_write(const LpLine *l,const char *o,size_t n,int bytes)
{
    size_t m;const char *p=lp_operand(l,&m);int word=lp_workspace_word(o,n);
    if(l->call||lp_is(l,"mvn")||lp_is(l,"mvp")||(l->use==LP_ALL&&!lp_is(l,"rep")&&!lp_is(l,"sep")))return 1;
    if(!lp_store_op(l))return 0;
    if(word>=0){
        int w=lp_workspace_word(p,m);
        if(w<0)return (lp_text_words(p,p+m)&(3u<<(word/2)))!=0;
        return lp_overlaps_n(l,w,word,bytes);
    }
    /* Frame and stack slots: the same spelling, a neighbour, or any indexed or indirect store */
    if(m&&(p[0]=='('||p[0]=='['||(m>=2&&p[m-2]==','&&p[m-1]=='x')))return 1;
    if(m==n&&!strncmp(p,o,n))return 1;
    if(n==9&&m==9&&!strncmp(p,"a:$",3)&&p[7]==','&&p[8]=='y'){
        long a=strtol(o+3,NULL,16),b=strtol(p+3,NULL,16);return lp_overlaps_n(l,(int)b,(int)a,bytes);
    }
    if(o[n-1]=='s'&&m&&p[m-1]=='s'){long a=strtol(o,NULL,10),b=strtol(p,NULL,10);return lp_overlaps_n(l,(int)b,(int)a,bytes);}
    /* Literal field displacements on the same absolute object need only
     * invalidate the bytes they overlap. Other same-name spellings may alias. */
    const char *read_end=o+n,*write_end=p+m;
    int absolute=n>11&&m>11&&!strncmp(o,"a:.loword(_",11)&&!strncmp(p,"a:.loword(_",11);
    n=lp_named_base(&o,n);m=lp_named_base(&p,m);
    if(!n||n!=m||memcmp(o,p,n))return 0;
    if(absolute&&read_end[-1]==')'&&write_end[-1]==')'){
        int first=lp_field_displacement(o+n,read_end-1),second=lp_field_displacement(p+m,write_end-1);
        if(first>=0&&second>=0&&first+bytes<=65536&&second+lp_width(l)<=65536)
            return lp_overlaps_n(l,second,first,bytes);
    }
    return 1;
}
static long lp_immediate(const LpLine *l);
static unsigned char *lp_local_targets(LpUnit *u,int *known_targets)
{
    unsigned i;
    unsigned char *targets=allocate(u->count);
    *known_targets=!u->indirect;
    for(i=0;i<u->count;++i){
        if(u->lines[i].target>=0){
            unsigned char *count=&targets[u->lines[i].target];
            if(*count<2)++*count;
        }
        else if(lp_branch(&u->lines[i]))*known_targets=0;
    }
    return targets;
}
static int lp_fallthrough_label(const LpLine *l)
{
    return l->label&&(!strncmp(l->text,"cg_",3)||!strncmp(l->text,"__inlined_",10));
}
/* Skip comments and untargeted fallthrough labels in direction (+1 or -1) */
static int lp_next_fallthrough(const LpUnit *u,unsigned k,int direction,
                               const unsigned char *targets,int known_targets)
{
    unsigned i=k;
    for(;;){
        if(direction<0){if(!i)return -1;--i;}else if(++i>=u->count)return -1;
        if(!u->lines[i].length)return -1;
        if(u->lines[i].text[0]==';'||!strncmp(u->lines[i].text,".export __inlined_",18))continue;
        if(known_targets&&!targets[i]&&lp_fallthrough_label(&u->lines[i]))continue;
        return u->lines[i].op?(int)i:-1;
    }
}
static int pr_named(const char *p,size_t n);
static int lp_flags_from_a(const LpUnit *u,int at)
{
    const LpLine *l;
    if(at<0)return 0;
    l=&u->lines[at];
    return !l->deleted&&!l->replace&&!l->m8&&(l->def&(LP_A|LP_N|LP_Z))==(LP_A|LP_N|LP_Z);
}
/* Two adjacent writes of the same register to a private home (or a
 * direct nonvolatile object) produce one value and do not set flags. */
static int lp_duplicate_stores(LpUnit *u,Function *f,size_t at)
{
    int changed=0;(void)at;
    if(cg.lp_volatile||cg.parser->no_value_reuse||body_asm_statements(f->body))return 0;
    for(unsigned i=0;i<u->count;++i){
        LpLine *first=&u->lines[i];size_t n;const char *home=lp_operand(first,&n);
        if((!lp_is(first,"sta")&&!lp_is(first,"stx")&&!lp_is(first,"sty")&&!lp_is(first,"stz"))||
           (!lp_private(home,n)&&(memchr(home,',',n)||!pr_named(home,n))))continue;
        int next=lp_next(u,i,1);
        if(next>=0&&lp_is(&u->lines[next],first->op)&&lp_operand_is(&u->lines[next],home,n)){
            first->deleted=1;++changed;
        }
    }
    return changed;
}
/* A store immediately after a value-select join inherits N/Z from A
 * if both the fallthrough and every incoming jump carry such a value. */
static int lp_store_flags_from_a(const LpUnit *u,unsigned store)
{
    int prev=lp_next(u,store,-1);
    if(prev>=0)return lp_flags_from_a(u,prev);
    if(u->indirect||!store)return 0;
    unsigned j=store;
    while(j){
        const LpLine *mark=&u->lines[--j];
        if(mark->op)return lp_flags_from_a(u,(int)j);
        if(mark->text[0]==';')continue;
        if(!lp_fallthrough_label(mark)&&!(mark->label&&mark->length==1&&mark->text[0]==':'))return 0;
        for(int from=mark->first_incoming;from>=0;from=u->lines[from].next_incoming){
            if(!u->lines[from].ends||u->lines[from].call||
               !lp_flags_from_a(u,lp_next(u,(unsigned)from,-1)))return 0;
        }
    }
    return 0;
}
/* The emitter uses both spellings for a named near operand */
static const char *lp_near_name(const char *operand,size_t *length)
{
    if(*length>12&&!strncmp(operand,"a:.loword(_",11)&&operand[*length-1]==')'){
        *length-=11;
        return operand+10;
    }
    if(*length>3&&!strncmp(operand,"a:_",3)){
        *length-=2;
        return operand+2;
    }
    return operand;
}
static int lp_reloads(LpUnit *u,Function *f,size_t at)
{
    unsigned i;int changed=0,known_targets;
    unsigned char *targets=lp_local_targets(u,&known_targets);
    (void)f;(void)at;
    lp_liveness(u);
    for(i=0;i<u->count;++i){
        LpLine *s=&u->lines[i],*l;int j,prev;size_t n,m;const char *o,*p;
        if((lp_line_is(s,"phx")||lp_line_is(s,"pha"))&&!s->m8&&!s->x8&&(j=lp_next(u,i,1))>=0&&
           lp_line_is(&u->lines[j],"lda 1,s")&&!u->lines[j].m8&&!u->lines[j].replace&&!u->lines[j].deleted){
            /* The value just pushed is still in X or A */
            if(lp_line_is(s,"phx")){lp_set(&u->lines[j],"    txa");++changed;}
            else if(!(u->lines[j].out&(LP_N|LP_Z))){u->lines[j].deleted=1;++changed;}
            else if(!(u->lines[j].out&LP_X)){lp_set(&u->lines[j],"    tax");++changed;}
            else if(!(u->lines[j].out&LP_Y)){lp_set(&u->lines[j],"    tay");++changed;}
            continue;
        }
        if(!s->op||s->m8||s->x8||!(lp_is(s,"sta")||lp_is(s,"stx")||lp_is(s,"sty")))continue;
        o=lp_operand(s,&n);
        if(lp_is(s,"sta")&&!cg.lp_volatile&&!cg.parser->no_value_reuse&&
           (lp_private(o,n)||(!memchr(o,',',n)&&pr_named(o,n)))&&
           (j=lp_next_fallthrough(u,i,1,targets,known_targets))>=0){
            l=&u->lines[j];
            if(!l->x8&&!l->m8&&!l->replace&&!l->deleted&&lp_operand_is(l,o,n)&&
               (lp_is(l,"ldx")||lp_is(l,"ldy"))){
                lp_set(l,lp_is(l,"ldx")?"    tax":"    tay");++changed;continue;
            }
        }
        if(!cg.lp_volatile&&!cg.parser->no_value_reuse&&(lp_is(s,"stx")||lp_is(s,"sty"))&&
           pr_named(o,n)&&(j=lp_next_fallthrough(u,i,1,targets,known_targets))>=0){
            l=&u->lines[j];p=lp_operand(l,&m);
            if(lp_is(l,"lda")&&!l->m8&&!l->replace&&!l->deleted&&lp_named_word_alias(o,n,p,m)){
                lp_set(l,lp_is(s,"stx")?"    txa":"    tya");++changed;continue;
            }
        }
        if(!lp_private(o,n)){
            size_t name_length=n;
            const char *name;
            if(cg.parser->no_value_reuse||!lp_is(s,"sta")||memchr(o,',',n)||
               (j=lp_next_fallthrough(u,i,1,targets,known_targets))<0)continue;
            l=&u->lines[j];
            if(!lp_is(l,"lda")||l->m8)continue;
            name=lp_near_name(o,&name_length);
            p=lp_operand(l,&m);
            p=lp_near_name(p,&m);
            if(name_length==m&&!memcmp(name,p,m)&&pr_named(o,n)&&
               (!(l->out&(LP_N|LP_Z))||lp_store_flags_from_a(u,i))){
                l->deleted=1;
                ++changed;
            }
            continue;
        }
        /* Redundant A8 zero-test reload of a byte value already zero-extended in A */
        if(lp_is(s,"sta")&&(prev=lp_next(u,i,-1))>=0&&!u->lines[prev].m8){
            long pv=lp_immediate(&u->lines[prev]);
            if(pv>=0&&pv<=255&&(lp_is(&u->lines[prev],"and")||lp_is(&u->lines[prev],"lda"))){
                int sep=lp_next_fallthrough(u,i,1,targets,known_targets);
                if(sep>=0&&lp_line_is(&u->lines[sep],"sep #$20")&&(unsigned)sep+1<u->count&&
                   !strncmp(u->lines[sep+1].text,".a8",3)&&u->lines[sep+1].length==3){
                    int load2=lp_next(u,(unsigned)sep+1,1);
                    int rep=load2>=0?lp_next(u,(unsigned)load2,1):-1;
                    if(load2>=0&&rep>=0&&lp_is(&u->lines[load2],"lda")&&lp_operand_is(&u->lines[load2],o,n)&&
                       lp_line_is(&u->lines[rep],"rep #$20")&&(unsigned)rep+1<u->count&&
                       !strncmp(u->lines[rep+1].text,".a16",4)&&u->lines[rep+1].length==4&&
                       !(u->lines[rep].out&(LP_A|LP_N))){
                        u->lines[sep].deleted=u->lines[sep+1].deleted=u->lines[load2].deleted=1;
                        u->lines[rep].deleted=u->lines[rep+1].deleted=1;
                        ++changed;continue;
                    }
                }
            }
        }
        j=lp_next_fallthrough(u,i,1,targets,known_targets);
        if(j<0)continue;
        l=&u->lines[j];p=lp_operand(l,&m);
        if(l->m8||l->x8||m!=n||strncmp(p,o,n)||l->replace||l->deleted)continue;
        if(lp_is(l,"lda")&&lp_is(s,"sta")){
            if((l->out&(LP_N|LP_Z))&&!lp_store_flags_from_a(u,i))continue;
            l->deleted=1;++changed;
        }
        else if(lp_is(l,"lda")){lp_set(l,lp_is(s,"stx")?"    txa":"    tya");++changed;}
        else if(lp_is(l,"ldx")){
            if(lp_is(s,"stx")){if(l->out&(LP_N|LP_Z))continue;l->deleted=1;}
            else lp_set(l,lp_is(s,"sta")?"    tax":"    tyx");
            ++changed;
        }else if(lp_is(l,"ldy")){
            if(lp_is(s,"sty")){if(l->out&(LP_N|LP_Z))continue;l->deleted=1;}
            else lp_set(l,lp_is(s,"sta")?"    tay":"    txy");
            ++changed;
        }
    }
    free(targets);
    return changed;
}
/* Numeric immediate "#$XXXX" or unsigned decimal "#N" of a line, or -1 */
static long lp_immediate(const LpLine *l)
{
    size_t m;const char *p=lp_operand(l,&m);char *stop;unsigned long v;
    if(m>=2&&p[0]=='#'&&isdigit((unsigned char)p[1])){
        v=strtoul(p+1,&stop,10);
        return stop==p+m&&v<=0xFFFFul?(long)v:-1;
    }
    if(m<3||p[0]!='#'||p[1]!='$')return -1;
    v=strtoul(p+2,&stop,16);
    return stop==p+m?(long)v:-1;
}
static int lp_has_immediate(const LpLine *l)
{
    static const char *const ops[]={"lda","ldx","ldy","adc","sbc","cmp","cpx","cpy","and","ora","eor"};
    unsigned i;for(i=0;i<sizeof ops/sizeof *ops;++i)if(lp_is(l,ops[i]))return 1;
    return 0;
}
/* A label every branch to which comes from lines [from, to) */
static int lp_inner_label(const LpUnit *u,unsigned k,unsigned from,unsigned to)
{
    unsigned j;
    if(u->indirect)return 0;
    if(u->lines[k].length>=2&&u->lines[k].text[0]=='_'&&!lp_fallthrough_label(&u->lines[k]))return 0; /* the function's own entry */
    for(j=0;j<u->count;++j)if(u->lines[j].op&&u->lines[j].target==(int)k&&(j<from||j>=to))return 0;
    return 1;
}
/* Constant store forwarding: after "lda #v / sta M" (or "stz M"), later
 * reads of M along straight-line code (labels only entered from it) use #v
 * while nothing may write M. A byte store also serves a 16-bit read whose
 * high byte an AND #$00FF discards. */
static int lp_forward_constants(LpUnit *u,Function *f,size_t at)
{
    unsigned i;int changed=0,named_ok=!cg.parser->no_value_reuse&&!cg.lp_volatile&&!u->indirect&&!body_asm_statements(f->body);(void)at;
    for(i=0;i<u->count;++i){
        LpLine *s=&u->lines[i];size_t n,vn=0;const char *o,*value=NULL;unsigned j;int y_frame,stack,dead=0,byte,named;long bv=-1;char text[16];
        int index_store=lp_is(s,"stx");
        if(!s->op||!(lp_is(s,"sta")||lp_is(s,"stz")||index_store)||s->deleted)continue;
        o=lp_operand(s,&n);byte=index_store?s->x8:s->m8;
        if(index_store&&byte)continue;
        named=!lp_private(o,n);
        if(named&&(!named_ok||memchr(o,',',n)||!pr_named(o,n)))continue;
        if(lp_is(s,"stz")){value=byte?"$00":"$0000";vn=byte?3:5;bv=0;}
        else if(!byte){
            int k,from_x=index_store,step=0;
            /* Recover a literal and any intervening word increments */
            for(k=(int)i-1;k>=0;--k){
                LpLine *l=&u->lines[k];
                if(!l->op){
                    if(l->text[0]==';'||!strncmp(l->text,".export __inlined_",18)||
                       (!u->indirect&&l->first_incoming<0&&lp_fallthrough_label(l)))continue;
                    break;
                }
                if(l->ends)break;
                if(lp_is(l,from_x?"ldx":"lda")){
                    size_t m;const char *p=lp_operand(l,&m);
                    if(!(from_x?l->x8:l->m8)&&m>1&&p[0]=='#'){
                        bv=lp_immediate(l);
                        if(bv>=0)bv=(bv+step)&65535;
                        if(!step){value=p+1;vn=m-1;}
                        else if(bv>=0){
                            vn=(size_t)snprintf(text,sizeof text,"$%04X",(unsigned)(lp_immediate(l)+step)&65535u);
                            value=text;
                        }
                    }
                    break;
                }
                if(!from_x&&!l->m8&&(lp_line_is(l,"inc a")||lp_line_is(l,"dec a"))){
                    step+=lp_is(l,"inc")?1:-1;continue;
                }
                if(!from_x&&!l->m8&&!l->x8&&lp_line_is(l,"txa")){from_x=1;continue;}
                if((l->def&(from_x?LP_X:LP_A))||l->use==LP_ALL||l->m8||l->x8||l->call)break;
            }
            if(!value)continue;
        }else{
            int k;
            /* The low byte of A: back over stores, comments and accumulator width changes */
            for(k=(int)i-1;k>=0;--k){
                LpLine *l=&u->lines[k];
                if(!l->op){if(l->label)break;continue;}
                if(lp_is(l,"lda")){bv=lp_immediate(l);break;}
                if((lp_is(l,"rep")||lp_is(l,"sep"))&&lp_line_is(l,lp_is(l,"rep")?"rep #$20":"sep #$20"))continue;
                if(lp_is(l,"sta")||lp_is(l,"stx")||lp_is(l,"sty")||lp_is(l,"stz")||lp_is(l,"ldx")||lp_is(l,"ldy"))continue;
                break;
            }
            if(bv<0)continue;
            bv&=0xFF;snprintf(text,sizeof text,"$%02lX",bv);value=text;vn=3;
        }
        y_frame=o[n-1]=='y';stack=o[n-1]=='s';
        unsigned pushed=0;
        for(j=i+1;j<u->count;++j){
            LpLine *l=&u->lines[j];size_t m;const char *p;int a_op,x_op;
            char adjusted[12];
            const char *home=o;
            size_t home_length=n;
            if(l->label){if(pushed||!lp_inner_label(u,j,i,j))break;dead=0;continue;}
            if(!l->op||dead)continue;
            if(stack&&lp_stack_op(l)){
                if(lp_is(l,"pea"))pushed+=2;
                else if(lp_is(l,"pha"))pushed+=l->m8?1u:2u;
                else if(lp_is(l,"phx")||lp_is(l,"phy"))pushed+=l->x8?1u:2u;
                else break;
                continue;
            }
            if(pushed){
                unsigned offset=(unsigned)atoi(o)+pushed;
                if(offset>255||l->ends||lp_branch(l))break;
                home_length=(size_t)snprintf(adjusted,sizeof adjusted,"%u,s",offset);
                home=adjusted;
            }
            if(named&&lp_store_op(l)){
                size_t width;const char *dest=lp_operand(l,&width);
                /* A direct slot in the reserved hardware stack cannot
                 * overlap an ordinary named object in this ABI. */
                if(width>=3&&dest[width-2]==','&&dest[width-1]=='s'&&
                   strspn(dest,"0123456789")==width-2)continue;
                if(memchr(dest,',',width)||!pr_named(dest,width))break;
            }
            if(lp_may_write(l,home,home_length,byte?1:2)||(y_frame&&(l->def&LP_Y)))break;
            /* After an unconditional transfer only internal labels continue the path */
            if(l->ends){dead=1;continue;}
            if(lp_is(l,"rep")||lp_is(l,"sep")){if(lp_line_is(l,"rep #$20")||lp_line_is(l,"sep #$20"))continue;break;}
            p=lp_operand(l,&m);
            if((!lp_operand_is(l,home,home_length)&&(!named||!lp_named_word_alias(home,home_length,p,m)))||
               !lp_has_immediate(l)||l->replace||l->deleted)continue;
            a_op=lp_is(l,"lda")||lp_is(l,"adc")||lp_is(l,"sbc")||lp_is(l,"cmp")||lp_is(l,"and")||lp_is(l,"ora")||lp_is(l,"eor");
            x_op=!a_op;
            if(!byte&&((a_op&&!l->m8)||(x_op&&!l->x8))){lp_set(l,"    %.3s #%.*s",l->op,(int)vn,value);++changed;}
            else if(byte&&((a_op&&l->m8)||(x_op&&l->x8))){lp_set(l,"    %.3s #%.*s",l->op,(int)vn,value);++changed;}
            else if(!byte&&a_op&&l->m8&&bv>=0){
                lp_set(l,"    %.3s #$%02lX",l->op,bv&255);++changed;
            }
            else if(byte&&lp_is(l,"lda")&&!l->m8){
                int k=lp_next(u,j,1);
                if(k>=0&&lp_line_is(&u->lines[k],"and #$00FF")){lp_set(l,"    lda #$00%02lX",bv);++changed;}
            }
        }
    }
    return changed;
}
/* A nonvolatile object assigned a literal and immediately stepped needs
 * just the final store. The old accumulator value must be dead afterward. */
static int lp_step_literal_store(LpUnit *u,Function *f,size_t at)
{
    (void)at;
    if(cg.parser->no_value_reuse||cg.lp_volatile||u->indirect||body_asm_statements(f->body))return 0;
    lp_liveness(u);
    for(unsigned i=0;i<u->count;++i){
        LpLine *clear=&u->lines[i];
        if(lp_is(clear,"stz")){
            size_t n;
            const char *home=lp_operand(clear,&n);
            if(memchr(home,',',n)||!pr_named(home,n))continue;
            const char *object=home;
            size_t length=lp_named_base(&object,n);
            for(int k=lp_next(u,i,1);k>=0;k=lp_next(u,(unsigned)k,1)){
                LpLine *l=&u->lines[k];
                if(l->m8!=clear->m8)break;
                if(lp_is(l,"inc")||lp_is(l,"dec")){
                    if(lp_operand_is(l,home,n)&&!(l->out&(l->m8?LP_AL:LP_A))){
                        unsigned value=lp_is(l,"inc")?1u:l->m8?255u:65535u;
                        lp_set(l,"    lda #$%0*X\n    sta %.*s",l->m8?2:4,value,(int)n,home);
                        clear->deleted=1;return 1;
                    }
                    break;
                }
                if(!lp_is(l,"lda")&&!lp_is(l,"sta"))break;
                size_t m;
                const char *p=lp_operand(l,&m);
                if(lp_immediate(l)>=0||lp_workspace_word(p,m)>=0)continue;
                if(memchr(p,',',m)||!pr_named(p,m))break;
                size_t other=lp_named_base(&p,m);
                if(!length||!other||(other==length&&!memcmp(p,object,length)))break;
            }
            continue;
        }
        LpLine *load=&u->lines[i];int store,step;size_t n;const char *home;
        long value;
        if(!lp_is(load,"lda")||(value=lp_immediate(load))<0||
           (store=lp_next(u,i,1))<0||!lp_is(&u->lines[store],"sta")||
           (step=lp_next(u,(unsigned)store,1))<0)continue;
        LpLine *update=&u->lines[step];
        home=lp_operand(&u->lines[store],&n);
        if((!lp_is(update,"inc")&&!lp_is(update,"dec"))||load->m8!=update->m8||
           (update->out&(load->m8?LP_AL:LP_A))||memchr(home,',',n)||
           !pr_named(home,n)||!lp_operand_is(update,home,n))continue;
        value=(value+(lp_is(update,"inc")?1:-1))&(load->m8?255:65535);
        lp_set(load,load->m8?"    lda #$%02lX":"    lda #$%04lX",value);
        update->deleted=1;return 1;
    }
    return 0;
}
/* Cache a word store in an otherwise unused index while A is reused.
 * Keep the original store until normal dead-store analysis proves it dead. */
static int lp_cache_stored_word(LpUnit *u,Function *f,size_t at)
{
    (void)at;
    if(cg.lp_volatile||u->indirect||body_asm_statements(f->body))return 0;
    lp_liveness(u);
    for(unsigned i=0;i<u->count;++i){
        LpLine *store=&u->lines[i];size_t n;const char *home=lp_operand(store,&n);
        int named=!lp_private(home,n);
        if(!lp_is(store,"sta")||store->m8||store->x8||
           (named&&(cg.parser->no_value_reuse||memchr(home,',',n)||!pr_named(home,n)))||
           ((store->out&(LP_N|LP_Z))&&!lp_flags_from_a(u,lp_next(u,i,-1))))continue;
        unsigned spare=LP_X|LP_Y;int clobbered=0;
        for(int k=(int)i;spare&&(k=lp_next(u,(unsigned)k,1))>=0;){
            LpLine *l=&u->lines[k];
            if(l->m8||l->x8||l->call||l->ends||lp_branch(l)||l->use==LP_ALL||
               lp_may_write(l,home,n,2)||lp_stack_op(l)||
               (home[n-1]=='y'&&(l->def&LP_Y)))break;
            if(named&&lp_store_op(l)){
                size_t length;
                const char *dest=lp_operand(l,&length);
                if(memchr(dest,',',length)||!pr_named(dest,length))break;
            }
            if(lp_is(l,"lda")&&lp_operand_is(l,home,n)){
                spare&=~l->out;
                if(clobbered&&spare){
                    lp_set(store,"    sta %.*s\n    %s",(int)n,home,spare&LP_X?"tax":"tay");
                    lp_set(l,spare&LP_X?"    txa":"    tya");return 1;
                }
                break;
            }
            spare&=~(l->use|l->def);
            if(l->def&LP_A)clobbered=1;
        }
    }
    return 0;
}
/* Defer the low word of a signed zero comparison until its high word
 * has proved zero. A/X and unsigned carry must be dead on every exit. */
static int lp_signed_home_positive(LpUnit *u,Function *f,size_t at)
{
    (void)f;(void)at;
    if(cg.lp_volatile||u->indirect)return 0;
    lp_liveness(u);
    for(unsigned i=0;i<u->count;++i){
        LpLine *high=&u->lines[i];
        int seq[6],j=(int)i;
        size_t width;
        const char *low;
        if(high->m8||high->x8||!lp_is(high,"lda"))continue;
        unsigned n=0;
        for(;n<6&&(j=lp_next(u,(unsigned)j,1))>=0;++n)seq[n]=j;
        if(n!=6)continue;
        LpLine *transfer=&u->lines[seq[0]],*load=&u->lines[seq[1]],*neg=&u->lines[seq[3]],*pos=&u->lines[seq[4]];
        if(!lp_line_is(transfer,"tax")||!lp_is(load,"lda")||
           !lp_line_is(&u->lines[seq[2]],"cpx #0")||!lp_is(neg,"bmi")||!lp_is(pos,"bne")||
           !lp_line_is(&u->lines[seq[5]],"cmp #0")||neg->target<0||pos->target<0)continue;
        low=lp_operand(load,&width);
        if(!lp_private(low,width)||((u->lines[neg->target].live|u->lines[pos->target].live)&(LP_A|LP_X|LP_C))||
           (u->lines[seq[5]].out&(LP_X|LP_C)))continue;
        lp_set(&u->lines[seq[5]],"    lda %.*s",(int)width,low);
        transfer->deleted=load->deleted=u->lines[seq[2]].deleted=1;
        return 1;
    }
    return 0;
}
/* A signed long comparison consumes the high flags first. Exchange
 * X:A before subtracting the high word so X can retain the low result. */
static int lp_signed_difference_flags(LpUnit *u,Function *f,size_t at)
{
    (void)f;(void)at;
    lp_liveness(u);
    for(unsigned i=0;i<u->count;++i){
        LpLine *push=&u->lines[i];
        if(push->m8||push->x8||!lp_line_is(push,"pha"))continue;
        int seq[8],next=(int)i;
        unsigned count=0;
        for(;count<8&&(next=lp_next(u,(unsigned)next,1))>=0;++count)seq[count]=next;
        if(count!=8||!lp_line_is(&u->lines[seq[0]],"txa")||!lp_is(&u->lines[seq[1]],"sbc")||
           !lp_line_is(&u->lines[seq[2]],"tax")||!lp_line_is(&u->lines[seq[3]],"pla")||
           !lp_line_is(&u->lines[seq[4]],"cpx #0")||!lp_is(&u->lines[seq[5]],"bmi")||
           !lp_is(&u->lines[seq[6]],"bne")||!lp_line_is(&u->lines[seq[7]],"cmp #0"))continue;
        LpLine *high=&u->lines[seq[1]],*negative=&u->lines[seq[5]],*positive=&u->lines[seq[6]];
        if(negative->target<0||positive->target<0||
           ((u->lines[negative->target].live|u->lines[positive->target].live)&(LP_A|LP_X|LP_C))||
           (u->lines[seq[7]].out&(LP_A|LP_X)))continue;
        size_t n;
        const char *operand=lp_operand(high,&n);
        int stack=lp_private(operand,n)&&operand[n-1]=='s';
        if(stack){
            if(atoi(operand)<3)continue;
            lp_set(&u->lines[seq[2]],"    sbc %u,s",(unsigned)atoi(operand)-2);
        }else{
            if(!pr_named(operand,n)||memchr(operand,',',n))continue;
            lp_set(&u->lines[seq[2]],"    sbc %.*s",(int)n,operand);
        }
        lp_set(push,"    phx");lp_set(&u->lines[seq[0]],"    tax");
        lp_set(high,"    pla");
        u->lines[seq[3]].deleted=u->lines[seq[4]].deleted=1;
        lp_set(&u->lines[seq[7]],"    cpx #0");return 1;
    }
    return 0;
}
/* Stage a register pair into the private arithmetic workspace without
 * borrowing X. The low source must survive the earlier high-word store. */
static int lp_stage_pair_words(LpUnit *u,Function *f,size_t at)
{
    (void)f;(void)at;
    lp_liveness(u);
    for(unsigned i=0;i<u->count;++i){
        LpLine *save=&u->lines[i];
        if(save->m8||save->x8||!lp_line_is(save,"tax"))continue;
        int load=lp_next(u,i,1),low=load<0?-1:lp_next(u,(unsigned)load,1);
        int high=low<0?-1:lp_next(u,(unsigned)low,1);
        if(high<0||!lp_is(&u->lines[load],"lda")||(u->lines[load].use&LP_X)||
           !lp_is(&u->lines[low],"sta")||!lp_is(&u->lines[high],"stx")||
           (u->lines[high].out&LP_X))continue;
        size_t n,m,k;
        const char *a=lp_operand(&u->lines[low],&n),*b=lp_operand(&u->lines[high],&m);
        const char *source=lp_operand(&u->lines[load],&k);
        if(lp_workspace_word(a,n)<0||lp_workspace_word(b,m)<0||
           !lp_private(source,k)||lp_may_write(&u->lines[high],a,n,2)||
           lp_may_write(&u->lines[high],source,k,2))continue;
        lp_set(save,"    sta %.*s",(int)m,b);u->lines[high].deleted=1;return 1;
    }
    return 0;
}
/* Compare an already-computed signed word against a literal on the left.
 * Bias both words to unsigned order, replacing the reverse subtraction and
 * its overflow correction. No arithmetic flags survive the sign branch. */
static int lp_reverse_signed_literal(LpUnit *u,Function *f,size_t at)
{
    (void)f;(void)at;
    lp_liveness(u);
    for(unsigned i=0;i<u->count;++i){
        LpLine *save=&u->lines[i];
        size_t n;
        const char *home=lp_operand(save,&n);
        if(save->m8||!lp_is(save,"sta")||lp_workspace_word(home,n)<0)continue;
        int load=lp_next(u,i,1),carry=load<0?-1:lp_next(u,(unsigned)load,1);
        int sub=carry<0?-1:lp_next(u,(unsigned)carry,1);
        if(sub<0||!lp_is(&u->lines[load],"lda")||!lp_line_is(&u->lines[carry],"sec")||
           !lp_is(&u->lines[sub],"sbc")||!lp_operand_is(&u->lines[sub],home,n))continue;
        long literal=lp_immediate(&u->lines[load]);
        if(literal<0||literal>65535||literal==32767)continue;
        int check=lp_next(u,(unsigned)sub,1),invert=check<0?-1:lp_next(u,(unsigned)check,1);
        if(invert<0||!lp_line_is(&u->lines[check],"bvc :+")||
           !lp_line_is(&u->lines[invert],"eor #$8000")||(unsigned)invert+2>=u->count)continue;
        LpLine *label=&u->lines[invert+1],*branch=&u->lines[invert+2];
        if(label->length!=1||label->text[0]!=':'||label->first_incoming!=check||
           u->lines[check].next_incoming>=0||(branch->out&(LP_A|LP_FLAGS)))continue;
        int greater=lp_is(branch,"bmi");
        if(!greater&&!lp_is(branch,"bpl"))continue;
        const char *target=lp_operand(branch,&n);
        lp_set(&u->lines[load],"    eor #$8000");
        lp_set(&u->lines[carry],"    cmp #$%04lX",(literal^32768)+1);
        u->lines[sub].deleted=u->lines[check].deleted=u->lines[invert].deleted=1;
        /* Keep the anonymous label so later relative-label references do not change */
        lp_set(branch,"    %s %.*s",greater?"bcs":"bcc",(int)n,target);
        return 1;
    }
    return 0;
}
/* Two private destinations can take the low half of X:A before TXA
 * exposes the high half. Keep the order of any overlapping writes. */
static int lp_pair_store_order(LpUnit *u,Function *f,size_t at)
{
    (void)at;
    if(cg.lp_volatile||cg.lp_frame_address||body_asm_statements(f->body))return 0;
    for(unsigned i=0;i<u->count;++i){
        LpLine *low=&u->lines[i];
        size_t n,m,h;
        const char *home=lp_operand(low,&n);
        if(!lp_is(low,"sta")||low->m8||low->x8||!lp_private(home,n)||
           (home[n-1]!='s'&&home[n-1]!='y'))continue;
        int seq[5],next=(int)i;
        unsigned count=0;
        for(;count<5&&(next=lp_next(u,(unsigned)next,1))>=0;++count)seq[count]=next;
        if(count!=5||!lp_line_is(&u->lines[seq[0]],"txa")||!lp_is(&u->lines[seq[1]],"sta")||
           !lp_is(&u->lines[seq[2]],"lda")||!lp_operand_is(&u->lines[seq[2]],home,n)||
           !lp_is(&u->lines[seq[3]],"sta")||!lp_line_is(&u->lines[seq[4]],"txa"))continue;
        LpLine *high=&u->lines[seq[1]],*also=&u->lines[seq[3]];
        const char *second=lp_operand(also,&m),*upper=lp_operand(high,&h);
        if(!lp_private(second,m)||!lp_private(upper,h)||second[m-1]!=home[n-1]||
           upper[h-1]!=home[n-1]||lp_may_write(high,home,n,2)||lp_may_write(high,second,m,2))continue;
        lp_set(&u->lines[seq[0]],"    sta %.*s\n    txa",(int)m,second);
        u->lines[seq[2]].deleted=also->deleted=u->lines[seq[4]].deleted=1;return 1;
    }
    return 0;
}
/* X:A already holds a double-word result. Propagate the low word's
 * carry into X without moving either half through the stack. */
static int lp_fold_index_carry(LpUnit *u,unsigned i)
{
    LpLine *save=&u->lines[i];
    if(save->m8||save->x8||!lp_line_is(save,"pha"))return 0;
    int transfer=lp_next(u,i,1);
    int high=transfer<0?-1:lp_next(u,(unsigned)transfer,1);
    int index=high<0?-1:lp_next(u,(unsigned)high,1);
    int restore=index<0?-1:lp_next(u,(unsigned)index,1);
    if(restore<0||!lp_line_is(&u->lines[transfer],"txa")||
       !lp_line_is(&u->lines[index],"tax")||!lp_line_is(&u->lines[restore],"pla")||
       (u->lines[restore].out&(LP_C|LP_V)))return 0;
    int add=lp_is(&u->lines[high],"adc");
    if((!add&&!lp_is(&u->lines[high],"sbc"))||lp_immediate(&u->lines[high])!=0)return 0;
    unsigned label=++cg.label;
    lp_set(save,"    %s cg_%s_%u",add?"bcc":"bcs",cg.parser->unit,label);
    lp_set(&u->lines[transfer],"    %s",add?"inx":"dex");
    lp_set(&u->lines[high],"cg_%s_%u = *%s",cg.parser->unit,label,
           (u->lines[restore].out&(LP_N|LP_Z))?"\n    ora #$0000":"");
    u->lines[index].deleted=u->lines[restore].deleted=1;
    return restore;
}
static int lp_index_carry(LpUnit *u,Function *f,size_t at)
{
    int changed=0;
    (void)f;(void)at;
    lp_liveness(u);
    for(unsigned i=0;i<u->count;++i){
        int end=lp_fold_index_carry(u,i);
        if(end){++changed;i=(unsigned)end;}
    }
    return changed;
}
/* Track a private word backwards across outgoing argument pushes. Only
 * direct nonoverlapping frame stores and loads may intervene. */
static int lp_fixed_stack_argument(LpUnit *u,Function *f,size_t at)
{
    (void)f;(void)at;
    if(cg.lp_volatile||u->indirect)return 0;
    lp_liveness(u);
    for(unsigned i=0;i<u->count;++i){
        LpLine *load=&u->lines[i];
        size_t n;
        const char *op=lp_operand(load,&n);
        if(!lp_is(load,"lda")||load->m8||!lp_private(op,n)||op[n-1]!='s')continue;
        int push=lp_next(u,i,1);
        if(push<0||!lp_line_is(&u->lines[push],"pha")||u->lines[push].m8)continue;
        int slot=atoi(op),crossed=0;
        for(int j=(int)i;(j=lp_next(u,(unsigned)j,-1))>=0;){
            LpLine *l=&u->lines[j];
            if(lp_is(l,"pea")||lp_line_is(l,"pha")){
                slot-=lp_is(l,"pea")||!l->m8?2:1;
                if(slot<1)break;
                crossed=1;continue;
            }
            if(lp_is(l,"lda"))continue;
            if(!lp_is(l,"sta"))break;
            op=lp_operand(l,&n);
            if(!lp_private(op,n)||op[n-1]!='s')break;
            int stored=atoi(op);
            if(stored>=slot+2||stored+(l->m8?1:2)<=slot)continue;
            if(stored==slot&&!l->m8&&crossed){
                int def=lp_next(u,(unsigned)j,-1);
                long literal;
                if(def>=0&&!u->lines[def].m8&&lp_is(&u->lines[def],"lda")&&
                   (literal=lp_immediate(&u->lines[def]))>=0&&literal<=65535){
                    if(!(u->lines[push].out&(LP_A|LP_N|LP_Z))){
                        lp_set(load,"    pea $%04lX",literal);u->lines[push].deleted=1;
                    }else lp_set(load,"    lda #$%04lX",literal);
                    return 1;
                }
            }
            break;
        }
    }
    return 0;
}
/* Workspace words read nowhere except by "lda M / inc a... / sta M" updates
 * of themselves: those updates and every other store go. */
static int lp_dead_workspace(LpUnit *u,Function *f,size_t at)
{
    unsigned word,i;int changed=0;(void)f;(void)at;
    if(u->helpers||u->indirect)return 0;
    lp_liveness(u);
    for(word=0;word<32;word+=2){
        int ok=1,stores=0;
        for(i=0;i<u->count&&ok;++i){
            LpLine *l=&u->lines[i];size_t m;const char *p;int w;
            if(!l->op||l->deleted)continue;
            p=lp_operand(l,&m);w=lp_workspace_word(p,m);
            if(w<0){if(lp_text_words(p,p+m)&(1u<<(word/2)))ok=0;continue;}
            if(!lp_overlaps(l,w,(int)word))continue;
            if((lp_is(l,"sta")||lp_is(l,"stx")||lp_is(l,"sty")||lp_is(l,"stz"))&&w==(int)word){++stores;continue;}
            if(lp_is(l,"lda")&&w==(int)word&&!l->m8){
                /* A self-update chain ending in "sta M" with dead results */
                int k=(int)i;unsigned written=LP_A|LP_N|LP_Z;
                while((k=lp_next(u,(unsigned)k,1))>=0){
                    LpLine *c=&u->lines[k];
                    if(lp_line_is(c,"inc a")||lp_line_is(c,"dec a")||lp_line_is(c,"inc")||lp_line_is(c,"dec"))continue;
                    if(lp_line_is(c,"clc")||lp_line_is(c,"sec")){written|=LP_C;continue;}
                    if((lp_is(c,"adc")||lp_is(c,"sbc"))&&!strncmp(c->op+4,"#",1)){written|=LP_FLAGS;continue;}
                    break;
                }
                if(k>=0&&lp_is(&u->lines[k],"sta")&&!u->lines[k].m8&&lp_operand_is(&u->lines[k],p,m)&&!(u->lines[k].out&written))continue;
            }
            ok=0;
        }
        if(!ok||!stores)continue;
        for(i=0;i<u->count;++i){
            LpLine *l=&u->lines[i];size_t m;const char *p;
            if(!l->op||l->deleted)continue;
            p=lp_operand(l,&m);
            if(lp_workspace_word(p,m)!=(int)word)continue;
            if(lp_is(l,"lda")){
                int k=(int)i;l->deleted=1;
                while((k=lp_next(u,(unsigned)k,1))>=0){u->lines[k].deleted=1;if(lp_is(&u->lines[k],"sta"))break;}
            }else l->deleted=1;
            ++changed;
        }
        if(changed)break;
    }
    return changed;
}
/* Instructions without side effects whose results are all dead */
static unsigned lp_byte_live_out(const LpUnit *u,unsigned i)
{
    int rep=lp_next(u,i,1);
    return rep>=0&&lp_line_is(&u->lines[rep],"rep #$20")?u->lines[rep].out:u->lines[i].out;
}
static int lp_dead_code(LpUnit *u,Function *f,size_t at)
{
    unsigned i;int changed=0;(void)f;(void)at;
    lp_liveness(u);
    for(i=0;i<u->count;++i){
        LpLine *l=&u->lines[i];size_t m;const char *p;int pure=0;
        if(!l->op||l->deleted||l->replace)continue;
        p=lp_operand(l,&m);
        if(l->m8&&m>1&&p[0]=='#'&&(lp_is(l,"cmp")||lp_is(l,"lda"))){
            unsigned live=lp_byte_live_out(u,i);
            if(!(live&l->def)){l->deleted=1;++changed;continue;}
        }
        if((lp_is(l,"lda")||lp_is(l,"and")||lp_is(l,"ora")||lp_is(l,"eor")||lp_is(l,"adc")||lp_is(l,"sbc")||lp_is(l,"cmp"))&&!l->m8)
            pure=m>1&&(p[0]=='#'||lp_private(p,m));
        else if((lp_is(l,"ldx")||lp_is(l,"ldy")||lp_is(l,"cpx")||lp_is(l,"cpy"))&&!l->x8)pure=m>1&&(p[0]=='#'||lp_private(p,m));
        else if(lp_line_is(l,"tax")||lp_line_is(l,"tay")||lp_line_is(l,"txy")||lp_line_is(l,"tyx")||lp_line_is(l,"inx")||
                lp_line_is(l,"dex")||lp_line_is(l,"iny")||lp_line_is(l,"dey"))pure=!l->x8;
        else if(lp_line_is(l,"txa")||lp_line_is(l,"tya")||lp_line_is(l,"inc a")||lp_line_is(l,"dec a")||lp_line_is(l,"inc")||
                lp_line_is(l,"dec")||lp_line_is(l,"asl a")||lp_line_is(l,"lsr a")||lp_line_is(l,"asl")||lp_line_is(l,"lsr"))pure=!l->m8;
        else if(lp_line_is(l,"clc")||lp_line_is(l,"sec"))pure=1;
        if(pure&&l->def&&!(l->def&l->out)){l->deleted=1;++changed;}
    }
    return changed;
}
/* Cleanup can leave an adjacent save/restore after removing the instructions
 * between them. A pull also sets N/Z, so remove the pair only when those
 * results are dead. */
static int lp_operand_has_s(const char *o,size_t n);
static int lp_dead_push_pairs(LpUnit *u,Function *f,size_t at)
{
    static const char *const push[]={"pha","phx","phy"},*const pull[]={"pla","plx","ply"};
    static const unsigned reg[]={LP_A,LP_X,LP_Y};
    unsigned i,j;
    int changed=0;
    (void)f;(void)at;
    lp_liveness(u);
    for(i=0;i<u->count;++i){
        int k,clobbered=0;unsigned spare=LP_X|LP_Y;
        if(u->lines[i].deleted||u->lines[i].m8||u->lines[i].x8)continue;
        for(j=0;j<3&&!lp_is(&u->lines[i],push[j]);++j){}
        if(j==3)continue;
        for(k=lp_next(u,i,1);k>=0;k=lp_next(u,(unsigned)k,1)){
            LpLine *cur=&u->lines[k];
            size_t n;
            const char *o;
            if(cur->deleted||cur->m8||cur->x8)break;
            if(lp_is(cur,pull[j])){
                if(!(cur->out&(LP_N|LP_Z|(clobbered?reg[j]:0)))){
                    u->lines[i].deleted=cur->deleted=1;
                    changed=1;
                }else if(j==0&&clobbered){
                    /* Rematerialize a saved word literal once intervening
                     * code has overwritten A. LDA reproduces the flags of PLA. */
                    int prev=(int)i;
                    while((prev=lp_next(u,(unsigned)prev,-1))>=0){
                        LpLine *source=&u->lines[prev];long value;
                        if(lp_is(source,"lda")&&!source->m8&&(value=lp_immediate(source))>=0){
                            u->lines[i].deleted=1;
                            lp_set(cur,"    lda #$%04lX",value);
                            changed=1;break;
                        }
                        if(!lp_is(source,"sta")&&!lp_is(source,"stx")&&!lp_is(source,"sty"))break;
                    }
                    spare&=~cur->out;
                    if(!u->lines[i].deleted&&spare&&!(u->lines[i].out&(LP_N|LP_Z))){
                        /* Keep a wide add/subtract in X:A when only carry
                         * can change its high word. No temporary is needed. */
                        if(lp_fold_index_carry(u,i)){changed=1;break;}
                        /* A dead index may hold the saved word until this pull */
                        lp_set(&u->lines[i],spare&LP_X?"    tax":"    tay");
                        lp_set(cur,spare&LP_X?"    txa":"    tya");changed=1;
                    }
                }
                break;
            }
            o=lp_operand(cur,&n);
            if(cur->ends||lp_branch(cur)||cur->call||lp_stack_op(cur)||cur->use==LP_ALL||
               lp_is(cur,"sep")||lp_is(cur,"rep")||lp_is(cur,"tsx")||lp_is(cur,"tsc")||
               lp_operand_has_s(o,n))break;
            spare&=~(cur->use|cur->def);
            if((cur->def&reg[j])||(j==0&&lp_is(cur,"xba")))clobbered=1;
        }
    }
    return changed;
}
static int lp_next_mode(const LpUnit *u,unsigned k)
{
    unsigned i=k;
    for(;;){
        if(++i>=u->count)return -1;
        if(!u->lines[i].length)return -1;
        if(u->lines[i].text[0]==';'||u->lines[i].deleted)continue;
        if(!u->lines[i].op&&((u->lines[i].length==3&&!strncmp(u->lines[i].text,".a8",3))||
           (u->lines[i].length==4&&!strncmp(u->lines[i].text,".a16",4))))continue;
        return u->lines[i].op?(int)i:-1;
    }
}
/* X used only as an a:$D,x index from line k on until it dies there:
 * returns the last such line and counts the uses, or -1. */
static int lp_index_run(const LpUnit *u,int k,int *uses,int any_op)
{
    int j;*uses=0;
    for(j=k;j>=0;j=lp_next_mode(u,(unsigned)j)){
        const LpLine *c=&u->lines[j];size_t m;const char *p=lp_operand(c,&m);
        if(c->replace||c->deleted)return -1;
        if(lp_line_is(c,"sep #$20")||lp_line_is(c,"rep #$20")){
            if(!(c->out&LP_X))return *uses?j:-1;
            continue;
        }
        if(c->use&LP_X){
            if(c->use==LP_ALL||c->call||c->def&LP_X||!(m==9&&!strncmp(p,"a:$",3)&&p[7]==','&&p[8]=='x'))return -1;
            if(!any_op&&!(lp_is(c,"lda")||lp_is(c,"sta")||lp_is(c,"adc")||lp_is(c,"sbc")||lp_is(c,"cmp")||
                          lp_is(c,"and")||lp_is(c,"ora")||lp_is(c,"eor")))return -1;
            ++*uses;
        }
        if(!(c->out&LP_X))return *uses?j:-1;
        if(c->ends||lp_branch(c))return -1;
    }
    return -1;
}
/* "inx/dex ... op a:$D,x" while X dies: fold the steps into the displacements */
static int lp_fold_steps(LpUnit *u,Function *f,size_t at)
{
    unsigned i;int changed=0;(void)f;(void)at;
    lp_liveness(u);
    for(i=0;i<u->count;++i){
        int k=(int)i,last=-1,delta=0,end,uses,j;
        if(!(lp_line_is(&u->lines[i],"inx")||lp_line_is(&u->lines[i],"dex"))||u->lines[i].wrap_step||u->lines[i].x8||u->lines[i].deleted||u->lines[i].replace)continue;
        for(;k>=0&&(lp_line_is(&u->lines[k],"inx")||lp_line_is(&u->lines[k],"dex"))&&!u->lines[k].wrap_step&&!u->lines[k].deleted;k=lp_next(u,(unsigned)k,1)){
            delta+=lp_line_is(&u->lines[k],"inx")?1:-1;last=k;
        }
        if(k<0||u->lines[last].out&(LP_N|LP_Z)||(end=lp_index_run(u,k,&uses,1))<0)continue;
        {   /* Indexed addresses carry into the next bank: a folded displacement
             * must stay within 0..$FFFF, where X itself would have wrapped. */
            int ok=1;
            for(j=k;j>=0;j=lp_next_mode(u,(unsigned)j)){
                size_t m;const char *p=lp_operand(&u->lines[j],&m);long d;
                if(u->lines[j].use&LP_X){d=(long)strtoul(p+3,NULL,16)+delta;if(d<0||d>0xFFFF)ok=0;}
                if(j==end)break;
            }
            if(!ok)continue;
        }
        for(j=k;j>=0;j=lp_next_mode(u,(unsigned)j)){
            LpLine *c=&u->lines[j];size_t m;const char *p=lp_operand(c,&m);
            if(c->use&LP_X){
                unsigned d=((unsigned)strtoul(p+3,NULL,16)+(unsigned)delta)&0xFFFFu;
                lp_set(c,"    %.3s a:$%04X,x",c->op,d);
            }
            if(j==end)break;
        }
        for(j=(int)i;j<=last;++j)if(u->lines[j].op)u->lines[j].deleted=1;
        ++changed;i=(unsigned)end;
    }
    return changed;
}
static int lp_cond_branch_target(const LpUnit *u,int k,int *after)
{
    const LpLine *b;
    if(k<0||(unsigned)k>=u->count)return -1;
    b=&u->lines[k];
    if(!lp_branch(b)||b->ends||b->deleted||b->replace||b->label||b->target<0)return -1;
    if(b->target==k+2&&(unsigned)(k+2)<u->count&&
       u->lines[k+2].length==1&&u->lines[k+2].text[0]==':'&&!u->lines[k+2].deleted&&
       lp_is(&u->lines[k+1],"jmp")&&!u->lines[k+1].deleted&&!u->lines[k+1].replace&&
       !u->lines[k+1].label&&u->lines[k+1].target>=0){
        if(after)*after=k+2;
        return u->lines[k+1].target;
    }
    if(u->lines[b->target].length==1&&u->lines[b->target].text[0]==':')return -1;
    if(after)*after=k;
    return b->target;
}
static int lp_far_stack_guard(LpUnit *u,int start,int ops[4],int *after,int *carry)
{
    static const char *const op[]={"lda","cmp","lda","sbc"};
    int k=start;
    for(unsigned i=0;i<4;++i){
        if(k<0)return -1;
        LpLine *l=&u->lines[k];
        size_t n;
        const char *operand=lp_operand(l,&n);
        if(l->m8||!lp_is(l,op[i])||!lp_private(operand,n)||operand[n-1]!='s'||atoi(operand)<1)return -1;
        ops[i]=k;
        k=lp_next(u,(unsigned)k,1);
    }
    if(lp_cond_branch_target(u,k,after)<0)return -1;
    if(lp_is(&u->lines[k],"bcs"))*carry=(*after==k);
    else if(lp_is(&u->lines[k],"bcc"))*carry=(*after!=k);
    else return -1;
    if(*after!=k&&(u->lines[*after].first_incoming!=k||u->lines[k].next_incoming>=0))return -1;
    return k;
}

/* A byte test using a temporary stack-relative direct page restores
 * both S and D before its branch. */
static int lp_far_stack_byte_test(LpUnit *u,int k)
{
    static const char *const prologue[]={"phd","tsc","tcd","sep #$20"};
    for(unsigned i=0;i<sizeof prologue/sizeof *prologue;++i){
        if(k<0||!lp_line_is(&u->lines[k],prologue[i]))return -1;
        k=lp_next_mode(u,(unsigned)k);
    }
    if(k<0||!lp_is(&u->lines[k],"lda")||!u->lines[k].m8)return -1;
    size_t n;
    const char *p=lp_operand(&u->lines[k],&n);
    if(n!=5||p[0]!='['||p[1]!='$'||p[4]!=']'||
       !isxdigit((unsigned char)p[2])||!isxdigit((unsigned char)p[3]))return -1;
    k=lp_next_mode(u,(unsigned)k);
    if(k<0||!lp_line_is(&u->lines[k],"pld"))return -1;
    k=lp_next_mode(u,(unsigned)k);
    if(k<0||!lp_is(&u->lines[k],"cmp")||!u->lines[k].m8||lp_immediate(&u->lines[k])<0)return -1;
    k=lp_next_mode(u,(unsigned)k);
    if(k<0||!lp_line_is(&u->lines[k],"rep #$20"))return -1;
    return lp_next_mode(u,(unsigned)k);
}

/* The passed stack-pointer guard remains true across a register counter
 * test or a byte test that leaves its operand slots unchanged. */
static int lp_skip_repeated_far_loop_guard(LpUnit *u,Function *f,size_t at)
{
    (void)at;
    if(u->indirect||body_asm_statements(f->body))return 0;
    int known,changed=0;
    unsigned char *targets=lp_local_targets(u,&known);
    lp_liveness(u);
    for(unsigned i=0;i<u->count&&!changed;++i){
        int ops[4],repeat[4],after,want,again_after,again_want;
        if(lp_far_stack_guard(u,(int)i,ops,&after,&want)<0)continue;
        int step=lp_next_fallthrough(u,(unsigned)after,1,targets,known);
        if(step<0||u->lines[step].x8)continue;
        int enter,enter_after;
        int counter=lp_is(&u->lines[step],"dey")||lp_is(&u->lines[step],"dex");
        if(counter){
            int check=lp_next(u,(unsigned)step,1);
            if(check<0||!lp_is(&u->lines[check],lp_is(&u->lines[step],"dey")?"cpy":"cpx")||
               lp_immediate(&u->lines[check])<0)continue;
            enter=lp_next(u,(unsigned)check,1);
        }else enter=lp_far_stack_byte_test(u,step);
        int target=lp_cond_branch_target(u,enter,&enter_after);
        if(target<0||(counter&&target>=(int)i))continue;
        int head=lp_next_fallthrough(u,(unsigned)target,1,targets,known);
        if(lp_far_stack_guard(u,head,repeat,&again_after,&again_want)<0||want!=again_want||
           (unsigned)(again_after+1)>=u->count||(u->lines[again_after+1].live&(LP_A|LP_FLAGS)))continue;
        int same=1;
        for(unsigned j=0;j<4;++j){
            size_t n;
            const char *p=lp_operand(&u->lines[ops[j]],&n);
            if(!lp_operand_is(&u->lines[repeat[j]],p,n))same=0;
        }
        if(!same)continue;
        char label[48];
        unsigned id=++cg.label;
        snprintf(label,sizeof label,"cg_lp_%u:\n",id);
        lp_insert(&u->lines[again_after+1],label);
        if(enter_after==enter)lp_set(&u->lines[enter],"    %.3s cg_lp_%u",u->lines[enter].op,id);
        else lp_set(&u->lines[enter+1],"    jmp .loword(cg_lp_%u)",id);
        changed=1;
    }
    free(targets);
    return changed;
}

/* An index initialized before a signed-length guard is needed only
 * on the positive path, provided neither exit observes the old Y. */
static int lp_delay_guarded_y_init(LpUnit *u,Function *f,size_t at)
{
    (void)at;
    if(u->indirect||body_asm_statements(f->body))return 0;
    lp_liveness(u);
    for(unsigned i=0;i<u->count;++i){
        LpLine *init=&u->lines[i];
        if(!lp_is(init,"ldy")||init->x8||lp_immediate(init)<0)continue;
        int load=lp_next(u,i,1),zero=load<0?-1:lp_next(u,(unsigned)load,1);
        int after_zero,after_negative;
        int zero_exit=lp_cond_branch_target(u,zero,&after_zero);
        if(zero_exit<0||!lp_is(&u->lines[load],"lda")||(u->lines[load].use&LP_Y)||
           !lp_is(&u->lines[zero],after_zero==zero?"beq":"bne")||
           (after_zero!=zero&&(u->lines[after_zero].first_incoming!=zero||
                              u->lines[zero].next_incoming>=0))||
           (u->lines[zero_exit].live&LP_Y))continue;
        int negative=lp_next(u,(unsigned)after_zero,1);
        int negative_exit=lp_cond_branch_target(u,negative,&after_negative);
        if(negative_exit<0||(unsigned)(after_negative+1)>=u->count||
           !lp_is(&u->lines[negative],after_negative==negative?"bmi":"bpl")||
           (after_negative!=negative&&(u->lines[after_negative].first_incoming!=negative||
                                      u->lines[negative].next_incoming>=0))||
           (u->lines[negative_exit].live&LP_Y)||(u->lines[after_negative+1].live&(LP_N|LP_Z)))continue;
        char literal[32];
        snprintf(literal,sizeof literal,"    ldy #$%04X\n",(unsigned)lp_immediate(init));
        lp_insert(&u->lines[after_negative+1],literal);
        init->deleted=1;
        return 1;
    }
    return 0;
}
/* Y register forms: TYA/INC A/TAY -> INY, TYA/TAX -> TYX, TXA/TAY -> TXY,
 * and TYX feeding only a:$D,x operands -> a:$D,y. */
static int lp_y_forms(LpUnit *u,Function *f,size_t at)
{
    unsigned i;int changed=0;(void)f;(void)at;
    lp_liveness(u);
    for(i=0;i<u->count;++i){
        LpLine *l=&u->lines[i];int k,steps=0,dir=0;
        if(!l->op||l->m8||l->x8||l->deleted||l->replace)continue;
        if(lp_line_is(l,"tya")||lp_line_is(l,"txa")){
            int from_y=lp_line_is(l,"tya");
            int carry=lp_next(u,i,1);
            if(carry>=0&&lp_is(&u->lines[carry],"cmp")&&!u->lines[carry].deleted&&!u->lines[carry].replace){
                size_t n;
                const char *operand=lp_operand(&u->lines[carry],&n);
                if(n&&(operand[0]=='#'||(n>2&&(operand[0]=='a'||operand[0]=='z')&&
                   operand[1]==':'&&!memchr(operand,',',n)))){
                    if(!(u->lines[carry].out&LP_A)){
                        l->deleted=1;lp_set(&u->lines[carry],"    cp%c %.*s",from_y?'y':'x',(int)n,operand);
                        ++changed;continue;
                    }else{
                        int br=lp_next(u,(unsigned)carry,1),after_br=-1,target;
                        target=lp_cond_branch_target(u,br,&after_br);
                        if(target>=0&&!(u->lines[target].live&(u->lines[target].m8?LP_AL:LP_A))){
                            unsigned t=(unsigned)after_br+1;
                            while(t<u->count&&!u->lines[t].op&&u->lines[t].length&&
                                  (u->lines[t].text[0]==';'||u->lines[t].deleted||
                                   (u->lines[t].label&&u->lines[t].first_incoming<0)))++t;
                            if(t<u->count&&u->lines[t].op&&!u->lines[t].deleted&&!u->lines[t].replace&&
                               !u->lines[t].m8&&!u->lines[t].x8&&
                               lp_line_is(&u->lines[t],from_y?"tax":"tay")&&
                               !(u->lines[t].out&(LP_A|LP_N|LP_Z))){
                                l->deleted=1;
                                lp_set(&u->lines[carry],"    cp%c %.*s",from_y?'y':'x',(int)n,operand);
                                lp_set(&u->lines[t],from_y?"    tyx":"    txy");
                                ++changed;continue;
                            }
                        }
                    }
                }
            }
            if(carry>=0&&(lp_line_is(&u->lines[carry],"clc")||lp_line_is(&u->lines[carry],"sec"))){
                int arith=lp_next(u,(unsigned)carry,1);
                int transfer=arith>=0?lp_next(u,(unsigned)arith,1):-1;
                int add=lp_line_is(&u->lines[carry],"clc");
                long count=arith>=0?lp_immediate(&u->lines[arith]):-1;
                if(transfer>=0&&count>0&&count<=3&&lp_is(&u->lines[arith],add?"adc":"sbc")&&
                   lp_line_is(&u->lines[transfer],from_y?"tay":"tax")&&
                   !(u->lines[transfer].out&(LP_A|LP_C|LP_V))&&
                   !u->lines[carry].deleted&&!u->lines[carry].replace&&
                   !u->lines[arith].deleted&&!u->lines[arith].replace&&
                   !u->lines[transfer].deleted&&!u->lines[transfer].replace){
                    const char *step=from_y?(add?"iny":"dey"):(add?"inx":"dex");
                    char text[32]="";
                    long j;
                    for(j=0;j<count;++j){if(j)strcat(text,"\n");strcat(text,"    ");strcat(text,step);}
                    l->deleted=u->lines[carry].deleted=u->lines[arith].deleted=1;
                    lp_set(&u->lines[transfer],"%s",text);++changed;continue;
                }
            }
            for(k=lp_next(u,i,1);k>=0&&(lp_line_is(&u->lines[k],"inc a")||lp_line_is(&u->lines[k],"dec a"));k=lp_next(u,(unsigned)k,1)){
                int d=lp_line_is(&u->lines[k],"inc a")?1:-1;if(dir&&d!=dir)break;dir=d;++steps;
            }
            if(k<0||u->lines[k].out&LP_A||u->lines[k].replace||u->lines[k].deleted)continue;
            if(from_y&&lp_line_is(&u->lines[k],"tay")&&steps&&steps<=3){
                int j;for(j=(int)i;j<=k;++j)if(u->lines[j].op)u->lines[j].deleted=1;
                {char text[48]="";int s;for(s=0;s<steps;++s)strcat(text,s?"\n    iny":"    iny");
                 if(dir<0){char *q;for(q=text;(q=strstr(q,"iny"))!=NULL;q+=3)q[0]='d',q[1]='e';}
                 lp_set(&u->lines[k],"%s",text);}
                ++changed;continue;
            }
            if(!steps&&lp_line_is(&u->lines[k],from_y?"tax":"tay")){
                l->deleted=1;lp_set(&u->lines[k],from_y?"    tyx":"    txy");++changed;continue;
            }
            continue;
        }
        if(!changed&&(lp_line_is(l,"tyx")||lp_line_is(l,"txy"))){
            /* Keep the transfer establishing equality intact for this round.
             * Reparse before the indexed-address rewrites reconsider it. */
            for(k=lp_next_mode(u,i);k>=0;k=lp_next_mode(u,(unsigned)k)){
                LpLine *same=&u->lines[k];
                if(same->x8||same->deleted||same->replace)break;
                if(lp_line_is(same,"tyx")||lp_line_is(same,"txy")){
                    if(!(same->out&(LP_N|LP_Z))){same->deleted=1;return 1;}
                    continue;
                }
                if(lp_line_is(same,"sep #$20")||lp_line_is(same,"rep #$20"))continue;
                if(same->call||same->ends||lp_branch(same)||(same->def&(LP_X|LP_Y))||
                   same->use==LP_ALL)break;
            }
        }
        if(lp_line_is(l,"tyx")&&!(l->out&(LP_N|LP_Z))){
            int j,uses,end,start=lp_next_mode(u,i),ok=1;
            if(start<0||(end=lp_index_run(u,start,&uses,0))<0)continue;
            for(j=start;j>=0;j=lp_next_mode(u,(unsigned)j)){
                if(u->lines[j].op&&(u->lines[j].def&LP_Y))ok=0;
                if(j==end)break;
            }
            if(!ok)continue;
            for(j=start;j>=0;j=lp_next_mode(u,(unsigned)j)){
                LpLine *c=&u->lines[j];size_t m;const char *p=lp_operand(c,&m);
                if(c->op&&(c->use&LP_X))lp_set(c,"    %.3s %.7s,y",c->op,p);
                if(j==end)break;
            }
            l->deleted=1;++changed;i=(unsigned)end;
        }
    }
    return changed;
}
/* Loop depth of every line from backward branches */
static void lp_depths(const LpUnit *u,unsigned *depth)
{
    unsigned i,j;
    for(i=0;i<u->count;++i)depth[i]=0;
    for(j=0;j<u->count;++j)if(u->lines[j].op&&u->lines[j].target>=0&&(unsigned)u->lines[j].target<j)
        for(i=(unsigned)u->lines[j].target;i<=j;++i)++depth[i];
}
/* Bytes pushed since entry before each line (-1 unreached), along every path;
 * 0 when a push depth is unknown or differs between paths into a label. */
static int lp_stack_depths_from(const LpUnit *u,unsigned first,int initial,int *sd)
{
    unsigned *work=malloc((u->count+1)*sizeof *work),top=0,i;int ok=1;
    if(!work){fputs("out of memory emitting assembly\n",stderr);exit(EXIT_FAILURE);}
    for(i=0;i<u->count;++i)sd[i]=-1;
    sd[first]=initial;work[top++]=first;
    while(ok&&top){
        unsigned k=work[--top];int d=sd[k];
        for(;k<u->count;++k){
            const LpLine *l=&u->lines[k];int delta=0;
            if(sd[k]>=0&&sd[k]!=d){ok=0;break;}
            if(sd[k]<0)sd[k]=d;
            if(!l->op)continue;
            if(lp_is(l,"pha"))delta=l->m8?1:2;else if(lp_is(l,"pla"))delta=l->m8?-1:-2;
            else if(lp_is(l,"phx")||lp_is(l,"phy"))delta=l->x8?1:2;else if(lp_is(l,"plx")||lp_is(l,"ply"))delta=l->x8?-1:-2;
            else if(lp_is(l,"php")||lp_is(l,"phb")||lp_is(l,"phk"))delta=1;else if(lp_is(l,"plp")||lp_is(l,"plb"))delta=-1;
            else if(lp_is(l,"phd")||lp_is(l,"pea")||lp_is(l,"pei")||lp_is(l,"per"))delta=2;else if(lp_is(l,"pld"))delta=-2;
            else if(lp_is(l,"tcs")){
                int b=lp_next(u,k,-1),c=b>=0?lp_next(u,(unsigned)b,-1):-1,t=c>=0?lp_next(u,(unsigned)c,-1):-1;
                if(t<0||!lp_line_is(&u->lines[t],"tsc")){ok=0;break;}
                if(lp_line_is(&u->lines[c],"clc")&&!strncmp(u->lines[b].op,"adc #$",6))
                    delta=-(int)strtoul(u->lines[b].op+6,NULL,16);
                else if(lp_line_is(&u->lines[c],"sec")&&!strncmp(u->lines[b].op,"sbc #$",6))
                    delta=(int)strtoul(u->lines[b].op+6,NULL,16);
                else{ok=0;break;}
            }else if(lp_is(l,"txs")||lp_is(l,"rti")||lp_is(l,"mvn")||lp_is(l,"mvp")){ok=0;break;}
            d+=delta;
            if(d<0){ok=0;break;}
            if((lp_is(l,"rts")||lp_is(l,"rtl")||(l->call&&l->ends))&&d){ok=0;break;}
            if(l->target>=0){
                if(sd[l->target]<0){sd[l->target]=d;work[top++]=(unsigned)l->target;}
                else if(sd[l->target]!=d){ok=0;break;}
            }else if(l->use==LP_ALL&&lp_branch(l)){ok=0;break;}
            if(l->ends)break;
            if(k+1<u->count&&sd[k+1]>=0){if(sd[k+1]!=d)ok=0;break;}
        }
    }
    free(work);
    return ok;
}
static int lp_stack_depths(const LpUnit *u,unsigned first,int *sd)
{
    return lp_stack_depths_from(u,first,0,sd);
}
/* Y as a loop register: in a function that leaves Y alone, the most used
 * in-loop workspace word moves to Y, saved at entry and restored at exits.
 * Y survives every call, so the word may live across them. */
static int lp_y_promote(LpUnit *u,Function *f,size_t at)
{
    unsigned i,word,best=0,best_score=0,*depth,first=0;int entry=-1,*sd;
    (void)at;
    if(u->helpers||u->indirect||f->symbol->interrupt)return 0;
    for(i=0;i<u->count;++i){
        LpLine *l=&u->lines[i];
        if(!l->op)continue;
        if(entry<0)entry=(int)i;
        if(l->x8)return 0;
        if(lp_index_use(l)&LP_Y||l->use&LP_Y&&!l->ends&&!l->call&&l->use!=LP_ALL)return 0;
        if(l->def&LP_Y||lp_is(l,"phy")||lp_is(l,"ply")||lp_is(l,"tsx")||lp_is(l,"txs")||lp_is(l,"mvn")||lp_is(l,"mvp"))return 0;
        if(lp_is(l,"jml")||lp_is(l,"rti"))return 0;
        if(l->use==LP_ALL&&!lp_is(l,"rep")&&!lp_is(l,"sep"))return 0;
        if((lp_is(l,"rep")||lp_is(l,"sep"))&&strtoul(l->op+6,NULL,16)&0x10)return 0;
        if(lp_is(l,"tsc")){
            /* Allow frame allocation "tsc / sec / sbc #n / tcs" and cleanup "tsc / clc / adc #n / tcs" */
            int a=lp_next(u,i,1),b=a>=0?lp_next(u,(unsigned)a,1):-1,c=b>=0?lp_next(u,(unsigned)b,1):-1;
            if(c<0||!lp_line_is(&u->lines[c],"tcs"))return 0;
            if(!((lp_line_is(&u->lines[a],"clc")&&!strncmp(u->lines[b].op,"adc #",5))||
                 (lp_line_is(&u->lines[a],"sec")&&!strncmp(u->lines[b].op,"sbc #",5))))return 0;
        }else if(lp_is(l,"tcs")){
            int b=lp_next(u,i,-1);
            if(b<0||(strncmp(u->lines[b].op,"adc #",5)&&strncmp(u->lines[b].op,"sbc #",5)))return 0;
        }
        if(l->target>=0){unsigned t=(unsigned)l->target;while(t<u->count&&!u->lines[t].op)++t;if(entry>=0&&t<=(unsigned)entry)return 0;}
        {size_t m;const char *p=lp_operand(l,&m);if(m>=2&&p[m-2]==','&&p[m-1]=='s'&&strtoul(p,NULL,10)+2>255)return 0;}
    }
    if(entry<0)return 0;
    first=(unsigned)entry;
    depth=malloc(u->count*sizeof *depth);if(!depth){fputs("out of memory emitting assembly\n",stderr);exit(EXIT_FAILURE);}
    lp_depths(u,depth);lp_liveness(u);
    for(word=0;word<32;word+=2){
        unsigned score=0,loop_uses=0;int ok=1;
        for(i=0;i<u->count&&ok;++i){
            LpLine *l=&u->lines[i];size_t m;const char *p;int w,gain;
            if(!l->op)continue;
            p=lp_operand(l,&m);w=lp_workspace_word(p,m);
            if(w<0&&(w=lp_workspace_pointer(p,m))>=0){
                if(w==(int)word){
                    if(!lp_accumulator_memory(l))ok=0;
                    if(depth[i]){++loop_uses;score+=5u<<(3*(depth[i]>3?3:depth[i]));}
                }else if(w+1==(int)word||w==(int)word+1)ok=0;
                continue;
            }
            if(w<0){if(lp_text_words(p,p+m)&(1u<<(word/2)))ok=0;continue;}
            if(!lp_overlaps(l,w,(int)word))continue;
            if(w!=(int)word){ok=0;break;}
            if((lp_is(l,"lda")||lp_is(l,"sta")||lp_is(l,"stz"))&&!l->m8)gain=2;
            else if(lp_is(l,"ldx")||lp_is(l,"stx"))gain=2;
            else if((lp_is(l,"inc")||lp_is(l,"dec"))&&!l->m8)gain=5;
            else{ok=0;break;}
            if((lp_is(l,"sta")||lp_is(l,"stx")||lp_is(l,"stz"))&&l->out&(LP_N|LP_Z)){ok=0;break;}
            if(depth[i]){++loop_uses;score+=(unsigned)gain<<(3*(depth[i]>3?3:depth[i]));}
        }
        if(ok&&loop_uses>=2&&score>best_score){best_score=score;best=word;}
    }
    free(depth);
    if(!best_score)return 0;
    sd=malloc(u->count*sizeof *sd);if(!sd){fputs("out of memory emitting assembly\n",stderr);exit(EXIT_FAILURE);}
    if(!lp_stack_depths(u,first,sd)){free(sd);return 0;}
    for(i=0;i<u->count;++i){
        size_t m;const char *p=lp_operand(&u->lines[i],&m);
        if(u->lines[i].op&&m>=2&&p[m-2]==','&&p[m-1]=='s'&&(sd[i]<0||(strtoul(p,NULL,10)>(unsigned long)sd[i]&&strtoul(p,NULL,10)+2>255))){free(sd);return 0;}
    }
    for(i=0;i<u->count;++i){
        LpLine *l=&u->lines[i];size_t m;const char *p;
        if(!l->op)continue;
        p=lp_operand(l,&m);
        if(lp_workspace_word(p,m)==(int)best){
            if(lp_is(l,"lda"))lp_set(l,"    tya");else if(lp_is(l,"ldx"))lp_set(l,"    tyx");
            else if(lp_is(l,"sta"))lp_set(l,"    tay");else if(lp_is(l,"stx"))lp_set(l,"    txy");
            else if(lp_is(l,"stz"))lp_set(l,"    ldy #$0000");else if(lp_is(l,"inc"))lp_set(l,"    iny");else lp_set(l,"    dey");
        }else if(lp_workspace_pointer(p,m)==(int)best){
            lp_set(l,"    %.3s a:$0000,y",l->op);
        }else if(m>=2&&p[m-2]==','&&p[m-1]=='s'){
            /* The saved Y sits below the entry stack, above this function's pushes */
            if(strtoul(p,NULL,10)>(unsigned long)sd[i])lp_set(l,"    %.3s %lu,s",l->op,strtoul(p,NULL,10)+2);
        }
        if(l->ends&&(lp_is(l,"rts")||lp_is(l,"rtl")||(l->call&&l->target<0)))lp_insert(l,"    ply\n");
    }
    {char text[96];snprintf(text,sizeof text,"; Y holds workspace word %u\n    phy\n",best);lp_insert(&u->lines[first],text);}
    free(sd);return 1;
}
static int lp_y_promote_split(LpUnit *u,Function *f,size_t at)
{
    unsigned i,word,best=0,best_score=0,*depth,first=0,y_first=u->count,y_last=0;
    int entry=-1,*sd,has_phy=0;
    (void)at;
    if(u->helpers||u->indirect||f->symbol->interrupt)return 0;
    for(i=0;i<u->count;++i){
        LpLine *l=&u->lines[i];
        if(!l->op)continue;
        if(entry<0)entry=(int)i;
        if(l->x8)return 0;
        if(lp_is(l,"phy")||lp_is(l,"ply")){has_phy=1;continue;}
        if(lp_is(l,"tsx")||lp_is(l,"txs")||lp_is(l,"mvn")||lp_is(l,"mvp")||
           lp_is(l,"jml")||lp_is(l,"rti")||lp_is(l,"tsc")||lp_is(l,"tcs"))return 0;
        if(l->use==LP_ALL&&!lp_is(l,"rep")&&!lp_is(l,"sep"))return 0;
        if((lp_is(l,"rep")||lp_is(l,"sep"))&&strtoul(l->op+6,NULL,16)&0x10)return 0;
        if(l->target>=0){unsigned t=(unsigned)l->target;while(t<u->count&&!u->lines[t].op)++t;if(entry>=0&&t<=(unsigned)entry)return 0;}
        {size_t m;const char *p=lp_operand(l,&m);if(m>=2&&p[m-2]==','&&p[m-1]=='s'&&strtoul(p,NULL,10)+2>255)return 0;}
    }
    if(entry<0)return 0;
    first=(unsigned)entry;
    depth=malloc(u->count*sizeof *depth);if(!depth){fputs("out of memory emitting assembly\n",stderr);exit(EXIT_FAILURE);}
    lp_depths(u,depth);lp_liveness(u);
    for(i=0;i<u->count;++i){
        LpLine *l=&u->lines[i];
        if(!l->op)continue;
        if((lp_index_use(l)&LP_Y)||(l->use&LP_Y&&!l->ends&&!l->call&&l->use!=LP_ALL)||
           (l->def&LP_Y)||(l->live&LP_Y)){
            if(i<y_first)y_first=i;
            y_last=i;
        }
    }
    if(y_first>y_last||y_last+1>=u->count){free(depth);return 0;}
    for(i=0;i<u->count;++i){
        LpLine *l=&u->lines[i];
        if(!l->op||l->target<0)continue;
        if(i<y_first||i>y_last){
            if((unsigned)l->target>y_first&&(unsigned)l->target<=y_last){free(depth);return 0;}
        }else{
            if(l->ends&&(lp_is(l,"rts")||lp_is(l,"rtl"))){free(depth);return 0;}
            if((unsigned)l->target<y_first||(unsigned)l->target>y_last+1){free(depth);return 0;}
        }
    }
    for(word=0;word<32;word+=2){
        unsigned score=0,loop_uses=0;int ok=1;
        for(i=0;i<u->count&&ok;++i){
            LpLine *l=&u->lines[i];size_t m;const char *p;int w,gain;
            if(!l->op)continue;
            p=lp_operand(l,&m);w=lp_workspace_word(p,m);
            if(i>=y_first&&i<=y_last){
                if(w>=0&&lp_overlaps(l,w,(int)word)){ok=0;break;}
                if(w<0&&(lp_workspace_pointer(p,m)==(int)word||(lp_text_words(p,p+m)&(1u<<(word/2))))){ok=0;break;}
                continue;
            }
            if(w<0&&(w=lp_workspace_pointer(p,m))>=0){
                if(w==(int)word){
                    if(!lp_accumulator_memory(l))ok=0;
                    if(depth[i]){++loop_uses;score+=5u<<(3*(depth[i]>3?3:depth[i]));}
                }else if(w+1==(int)word||w==(int)word+1)ok=0;
                continue;
            }
            if(w<0){if(lp_text_words(p,p+m)&(1u<<(word/2)))ok=0;continue;}
            if(!lp_overlaps(l,w,(int)word))continue;
            if(w!=(int)word){ok=0;break;}
            if((lp_is(l,"lda")||lp_is(l,"sta")||lp_is(l,"stz"))&&!l->m8)gain=2;
            else if(lp_is(l,"ldx")||lp_is(l,"stx"))gain=2;
            else if((lp_is(l,"inc")||lp_is(l,"dec"))&&!l->m8)gain=5;
            else{ok=0;break;}
            if((lp_is(l,"sta")||lp_is(l,"stx")||lp_is(l,"stz"))&&l->out&(LP_N|LP_Z)){ok=0;break;}
            if(depth[i]){++loop_uses;score+=(unsigned)gain<<(3*(depth[i]>3?3:depth[i]));}
        }
        if(ok&&loop_uses>=2&&score>best_score){best_score=score;best=word;}
    }
    free(depth);
    if(!best_score)return 0;
    sd=malloc(u->count*sizeof *sd);if(!sd){fputs("out of memory emitting assembly\n",stderr);exit(EXIT_FAILURE);}
    if(!lp_stack_depths(u,first,sd)){free(sd);return 0;}
    if(!has_phy){
        for(i=0;i<u->count;++i){
            size_t m;const char *p=lp_operand(&u->lines[i],&m);
            if(u->lines[i].op&&m>=2&&p[m-2]==','&&p[m-1]=='s'&&(sd[i]<0||(strtoul(p,NULL,10)>(unsigned long)sd[i]&&strtoul(p,NULL,10)+2>255))){free(sd);return 0;}
        }
    }
    for(i=0;i<u->count;++i){
        LpLine *l=&u->lines[i];size_t m;const char *p;
        if(!l->op)continue;
        p=lp_operand(l,&m);
        if(i<y_first||i>y_last){
            if(lp_workspace_word(p,m)==(int)best){
                if(lp_is(l,"lda"))lp_set(l,"    tya");else if(lp_is(l,"ldx"))lp_set(l,"    tyx");
                else if(lp_is(l,"sta"))lp_set(l,"    tay");else if(lp_is(l,"stx"))lp_set(l,"    txy");
                else if(lp_is(l,"stz"))lp_set(l,"    ldy #$0000");else if(lp_is(l,"inc"))lp_set(l,"    iny");else lp_set(l,"    dey");
            }else if(lp_workspace_pointer(p,m)==(int)best){
                lp_set(l,"    %.3s a:$0000,y",l->op);
            }else if(!has_phy&&m>=2&&p[m-2]==','&&p[m-1]=='s'){
                if(strtoul(p,NULL,10)>(unsigned long)sd[i])lp_set(l,"    %.3s %lu,s",l->op,strtoul(p,NULL,10)+2);
            }
        }else if(!has_phy&&m>=2&&p[m-2]==','&&p[m-1]=='s'){
            if(strtoul(p,NULL,10)>(unsigned long)sd[i])lp_set(l,"    %.3s %lu,s",l->op,strtoul(p,NULL,10)+2);
        }
        if(!has_phy&&l->ends&&(lp_is(l,"rts")||lp_is(l,"rtl")||(l->call&&l->target<0)))lp_insert(l,"    ply\n");
    }
    {
        char sty[64],ldy[64];
        if(best){
            snprintf(sty,sizeof sty,"    sty z:__arith_lhs+%u\n",best);
            snprintf(ldy,sizeof ldy,"    ldy z:__arith_lhs+%u\n",best);
        }else{
            snprintf(sty,sizeof sty,"    sty z:__arith_lhs\n");
            snprintf(ldy,sizeof ldy,"    ldy z:__arith_lhs\n");
        }
        lp_insert(&u->lines[y_first],sty);
        lp_insert(&u->lines[y_last+1],ldy);
    }
    if(!has_phy){char text[96];snprintf(text,sizeof text,"; Y holds workspace word %u (split)\n    phy\n",best);lp_insert(&u->lines[first],text);}
    free(sd);return 1;
}
/* Known accumulator constants: "lda #v" folds a following and/ora/eor #m,
 * and "lda #v / cmp #w" decides the branches that read only its flags. */
/* A compiler-local label every entry of which (branch or fallthrough) is a
 * chain line, or is preceded by a line control cannot fall out of. */
static int lp_chain_label(const LpUnit *u,unsigned t,const char *chain)
{
    const LpLine *l=&u->lines[t];unsigned j;int p;
    if(!(l->length==1&&l->text[0]==':')&&strncmp(l->text,"cg_",3))return 0;
    for(j=0;j<u->count;++j)if(u->lines[j].op&&!u->lines[j].deleted&&u->lines[j].target==(int)t&&!chain[j])return 0;
    for(p=(int)t-1;p>=0&&(u->lines[p].deleted||!u->lines[p].length||u->lines[p].text[0]==';');--p){}
    if(p<0)return 0;
    if(chain[p]||(u->lines[p].op&&u->lines[p].ends&&!u->lines[p].call))return 1;
    return 0;
}
/* Folds the branches that follow line k, whose flag results are known;
 * a negative c or v is unknown. Follows taken branches and fallthroughs into
 * labels entered only from the chain. Returns how many branches changed. */
static int lp_fold_branches(LpUnit *u,int k,int z,int c,int n,int v)
{
    int i=k,changed=0,steps=0;char *chain;
    if(u->indirect)return 0;
    chain=calloc(u->count,1);
    if(!chain){fputs("out of memory emitting assembly\n",stderr);exit(EXIT_FAILURE);}
    chain[k]=1;
    while(++steps<64){
        unsigned t=(unsigned)i+1;LpLine *br;int taken;
        while(t<u->count&&u->lines[t].length&&(u->lines[t].text[0]==';'||u->lines[t].deleted))++t;
        if(t>=u->count||!u->lines[t].length)break;
        br=&u->lines[t];
        if(br->label){if(!lp_chain_label(u,t,chain))break;chain[t]=1;i=(int)t;continue;}
        if(!br->op||!lp_branch(br)||br->replace||lp_is(br,"brl")||lp_is(br,"jml"))break;
        if(lp_is(br,"bra"))taken=1;
        else if(lp_is(br,"beq"))taken=z;else if(lp_is(br,"bne"))taken=!z;
        else if(c>=0&&lp_is(br,"bcs"))taken=c;else if(c>=0&&lp_is(br,"bcc"))taken=!c;
        else if(lp_is(br,"bmi"))taken=n;else if(lp_is(br,"bpl"))taken=!n;
        else if(v>=0&&lp_is(br,"bvs"))taken=v;else if(v>=0&&lp_is(br,"bvc"))taken=!v;
        else break;
        chain[t]=1;
        if(!taken){br->deleted=1;++changed;i=(int)t;continue;}
        if(!lp_is(br,"bra")){size_t m;const char *p=lp_operand(br,&m);lp_set(br,"    bra %.*s",(int)m,p);++changed;}
        /* Continue at a forward target only if nothing else enters it */
        if(br->target<=(int)t||!lp_chain_label(u,(unsigned)br->target,chain))break;
        chain[br->target]=1;i=br->target;
    }
    free(chain);
    return changed;
}
static int lp_fallthrough_marker(const LpLine *l,unsigned j,const unsigned char *targets,int known_targets)
{
    if(l->op)return 0;
    if(!l->length||l->text[0]==';')return 1;
    if(!strncmp(l->text,".export __inlined_",18))return 1;
    return known_targets&&!targets[j]&&lp_fallthrough_label(l);
}
/* Consecutive folded conversions can raise the same sticky flag.
 * A guard that only observes the rounding mode leaves that flag set. */
static int lp_repeated_inexact_raise(LpUnit *u,Function *f,size_t at)
{
    static const char raise[]="tsb a:.loword(__fp_exceptions)";
    (void)at;
    if(u->indirect||body_asm_statements(f->body))return 0;
    int known;
    unsigned char *targets=lp_local_targets(u,&known);
    lp_liveness(u);
    for(unsigned i=0;i<u->count;++i){
        LpLine *first=&u->lines[i];
        if(first->m8||!lp_line_is(first,raise))continue;
        int literal=lp_next_fallthrough(u,i,-1,targets,known);
        if(literal<0||!lp_line_is(&u->lines[literal],"lda #$0010"))continue;
        int step=(int)i;
        for(unsigned n=0;n<5;++n){
            step=lp_next_fallthrough(u,(unsigned)step,1,targets,known);
            if(step<0)break;
            LpLine *next=&u->lines[step];
            if(next->m8)break;
            if(lp_line_is(next,"lda #$0010")){
                int dup=lp_next_fallthrough(u,(unsigned)step,1,targets,known);
                if(dup>=0&&lp_line_is(&u->lines[dup],raise)&&
                   !(u->lines[dup].out&(LP_A|LP_N|LP_Z))){
                    next->deleted=u->lines[dup].deleted=1;
                    free(targets);
                    return 1;
                }
                break;
            }
            if(lp_line_is(next,"lda a:.loword(__fp_round_mode)")||lp_line_is(next,"lsr a")||
               ((lp_is(next,"bit")||lp_is(next,"cmp"))&&lp_immediate(next)>=0))continue;
            int after;
            if(lp_cond_branch_target(u,step,&after)<0)break;
            if(after!=step&&(u->lines[after].first_incoming!=step||next->next_incoming>=0))break;
            step=after;
        }
    }
    free(targets);
    return 0;
}
/* Carry the value just written to a named object along a loop backedge.
 * A separate entry keeps the original load on every other predecessor. */
static int lp_forward_named_latch_load(LpUnit *u,Function *f,size_t at)
{
    (void)at;
    if(u->indirect||cg.parser->no_value_reuse||body_asm_statements(f->body))return 0;
    int known;
    unsigned char *targets=lp_local_targets(u,&known);
    lp_liveness(u);
    for(unsigned i=1;i<u->count;++i){
        LpLine *edge=&u->lines[i];
        if((!lp_is(edge,"bra")&&!lp_is(edge,"jmp"))||edge->target<0||
           (unsigned)edge->target>=i)continue;
        int store=lp_next_fallthrough(u,i,-1,targets,known);
        int load=lp_next_fallthrough(u,(unsigned)edge->target,1,targets,known);
        if(store<0||load<0||load>=store||(unsigned)(load+1)>=u->count)continue;
        LpLine *write=&u->lines[store],*read=&u->lines[load];
        if(!lp_is(write,"sta")||!lp_is(read,"lda")||write->m8!=read->m8||
           (read->out&(LP_N|LP_Z)))continue;
        size_t n;
        const char *home=lp_operand(write,&n);
        if(memchr(home,',',n)||!pr_named(home,n)||!lp_operand_is(read,home,n))continue;
        unsigned id=++cg.label;
        char label[48];
        snprintf(label,sizeof label,"cg_lp_%u:\n",id);
        lp_insert(&u->lines[load+1],label);
        lp_set(edge,"    jmp .loword(cg_lp_%u)",id);
        free(targets);
        return 1;
    }
    free(targets);
    return 0;
}
/* Keep a named loop word in X while the loop test consumes A */
static int lp_named_counter_in_x(LpUnit *u,Function *f,size_t at)
{
    (void)at;
    if(u->indirect||cg.parser->no_value_reuse||body_asm_statements(f->body))return 0;
    int known,changed=0;
    unsigned char *targets=lp_local_targets(u,&known);
    lp_liveness(u);
    for(unsigned i=1;i<u->count&&!changed;++i){
        LpLine *edge=&u->lines[i];
        int head=edge->target;
        if((!lp_is(edge,"bra")&&!lp_is(edge,"jmp"))||head<0||(unsigned)head>=i||
           u->lines[head].first_incoming!=(int)i||edge->next_incoming>=0)continue;
        int store=lp_next_fallthrough(u,i,-1,targets,known);
        if(store<0||!lp_is(&u->lines[store],"sta")||u->lines[store].m8)continue;
        size_t n;
        const char *home=lp_operand(&u->lines[store],&n);
        if(n<3||strncmp(home,"a:",2)||memchr(home,',',n)||!pr_named(home,n))continue;
        int first=lp_next(u,(unsigned)store,-1),read=first;
        while(read>=0&&(lp_line_is(&u->lines[read],"inc a")||lp_line_is(&u->lines[read],"dec a")))
            read=lp_next(u,(unsigned)read,-1);
        if(read<0||read==first||!lp_is(&u->lines[read],"lda")||
           !lp_operand_is(&u->lines[read],home,n))continue;
        int init=lp_next_fallthrough(u,(unsigned)head,-1,targets,known);
        int test=lp_next_fallthrough(u,(unsigned)head,1,targets,known);
        if(init<0||test<0||test>=read||!lp_is(&u->lines[init],"lda")||
           !lp_operand_is(&u->lines[init],home,n)||(u->lines[init].out&LP_X))continue;
        unsigned sites[8],entries;
        if(!lp_entries(u,(unsigned)head,i,sites,&entries)||entries!=1)continue;
        int valid=1,uses_a=0;
        for(unsigned j=(unsigned)init;j<=i&&valid;++j){
            LpLine *l=&u->lines[j];
            if(!l->op)continue;
            if(l->m8||l->x8||l->call||(l->use|l->def)&LP_X||
               (j<(unsigned)store&&lp_may_write(l,home,n,2)))valid=0;
            if(j>=(unsigned)test&&j<(unsigned)read&&(l->use&LP_A))uses_a=1;
        }
        if(!valid||!uses_a)continue;
        lp_set(&u->lines[init],"    ldx %.*s",(int)n,home);
        lp_insert(&u->lines[test],"    txa\n");
        u->lines[read].deleted=1;
        for(int j=first;j!=read;j=lp_next(u,(unsigned)j,-1))
            lp_set(&u->lines[j],"    %s",lp_line_is(&u->lines[j],"inc a")?"inx":"dex");
        lp_set(&u->lines[store],"    stx %.*s",(int)n,home);
        changed=1;
    }
    free(targets);
    return changed;
}

/* Remove a direct stack or object store covered by another before any memory read,
 * control transfer, stack movement or potential entry into the sequence. */
static int lp_overwritten_stores(LpUnit *u,Function *f,size_t at)
{
    int known,changed=0;
    (void)at;
    if(u->indirect||cg.lp_frame_address||cg.lp_volatile||cg.parser->no_private_regions||
       body_asm_statements(f->body))return 0;
    unsigned char *targets=lp_local_targets(u,&known);
    for(unsigned i=0;i<u->count;++i){
        LpLine *store=&u->lines[i];size_t n;
        const char *p=lp_operand(store,&n);
        int stack=n>=3&&p[n-1]=='s'&&lp_private(p,n);
        int named=!stack&&!memchr(p,',',n)&&pr_named(p,n);
        if((!lp_is(store,"sta")&&!lp_is(store,"stz"))||(!stack&&!named))continue;
        for(unsigned j=i+1;j<u->count;++j){
            LpLine *l=&u->lines[j];size_t m;
            const char *q=lp_operand(l,&m);
            if(lp_fallthrough_marker(l,j,targets,known))continue;
            if((lp_is(l,"sta")||lp_is(l,"stz"))&&
               ((stack&&m>=3&&q[m-1]=='s'&&lp_private(q,m))||
                (named&&!memchr(q,',',m)&&pr_named(q,m)))){
                if(lp_operand_is(l,p,n)&&lp_width(l)>=lp_width(store)){
                    store->deleted=1;++changed;break;
                }
                continue;
            }
            if(lp_line_is(l,"inc a")||lp_line_is(l,"dec a")||
               ((lp_is(l,"lda")||lp_is(l,"ldx")||lp_is(l,"ldy"))&&m&&q[0]=='#'))continue;
            break;
        }
    }
    free(targets);return changed;
}
/* Push an outgoing register pair directly instead of spilling the low
 * word and fetching it again below the high-word argument. */
static int lp_push_register_pair(LpUnit *u,Function *f,size_t at)
{
    int known,changed=0;
    unsigned char *targets=lp_local_targets(u,&known);
    (void)f;(void)at;
    lp_liveness(u);
    for(unsigned i=0;i<u->count;++i){
        LpLine *save=&u->lines[i];
        size_t n;
        const char *slot=lp_operand(save,&n);
        if(!lp_is(save,"sta")||save->m8||save->x8||!lp_private(slot,n)||slot[n-1]!='s')continue;
        unsigned seq[4],count=0,j=i+1;
        for(;count<4;++count){
            while(j<u->count&&lp_fallthrough_marker(&u->lines[j],j,targets,known))++j;
            if(j==u->count||!u->lines[j].op)break;
            seq[count]=j++;
        }
        if(count!=4||!lp_line_is(&u->lines[seq[0]],"txa")||!lp_line_is(&u->lines[seq[1]],"pha")||
           !lp_is(&u->lines[seq[2]],"lda")||!lp_line_is(&u->lines[seq[3]],"pha")||
           (u->lines[seq[3]].out&(LP_N|LP_Z)))continue;
        const char *reload=lp_operand(&u->lines[seq[2]],&n);
        if(!lp_private(reload,n)||reload[n-1]!='s'||atoi(reload)!=atoi(slot)+2)continue;
        u->lines[seq[0]].deleted=u->lines[seq[2]].deleted=1;
        lp_set(&u->lines[seq[1]],"    phx");++changed;i=seq[3];
    }
    free(targets);return changed;
}
/* Pulling and immediately pushing the same register leaves the stack
 * untouched. A known scalar return supplies A and a long return also
 * supplies X, even if their result is subsequently live. */
static int lp_cancel_pull_push(LpUnit *u,Function *f,size_t at)
{
    int known,changed=0;
    unsigned char *targets=lp_local_targets(u,&known);
    (void)f;(void)at;
    lp_liveness(u);
    for(unsigned i=0;i<u->count;++i){
        LpLine *pull=&u->lines[i];
        unsigned reg=lp_is(pull,"pla")?LP_A:lp_is(pull,"plx")?LP_X:lp_is(pull,"ply")?LP_Y:0;
        if(!reg||pull->m8||pull->x8)continue;
        unsigned j=i+1;
        while(j<u->count&&lp_fallthrough_marker(&u->lines[j],j,targets,known))++j;
        if(j==u->count||!lp_line_is(&u->lines[j],reg==LP_A?"pha":reg==LP_X?"phx":"phy")||
           (u->lines[j].out&(LP_N|LP_Z)))continue;
        if(u->lines[j].out&reg){
            int k=(int)j;
            while((k=lp_next(u,(unsigned)k,1))>=0){
                LpLine *l=&u->lines[k];
                if(l->use&reg)break;
                if(l->call){
                    Symbol *callee=lp_callee(l);
                    if(callee&&!callee->interrupt&&!structure_object(callee->type)&&
                       (callee->type.pointers||callee->type.base!=TY_VOID)&&
                       (reg==LP_A||(reg==LP_X&&reg_width(callee->type)==4)))goto dead;
                    break;
                }
                if(l->target>=0||l->ends||lp_branch(l))break;
            }
            continue;
        }
dead:
        pull->deleted=u->lines[j].deleted=1;++changed;i=j;
    }
    free(targets);return changed;
}
/* Only edges from the already validated interval may enter a label */
static int lp_internal_path_marker(const LpUnit *u,unsigned j,unsigned start)
{
    const LpLine *l=&u->lines[j];
    if(!l->length||l->text[0]==';'||!strncmp(l->text,".export __inlined_",18))return 1;
    if(!l->label||(!lp_fallthrough_label(l)&&(l->length!=1||l->text[0]!=':')))return 0;
    int incoming=l->first_incoming;
    while(incoming>(int)start&&(unsigned)incoming<j)incoming=u->lines[incoming].next_incoming;
    return incoming<0;
}
/* At a join every incoming path must retain the same byte read from
 * the far cursor, or the whole word loaded from or stored in a private home. A finite search rejects cycles and unknown control flow. */
static int lp_prior_home_value(const LpUnit *u,int pos,unsigned load,const char *home,size_t n,int word,int flags,int *budget)
{
    for(;pos>=0&&*budget>0;--pos){
        const LpLine *l=&u->lines[pos];
        --*budget;
        if((unsigned)pos==load)return 0;
        if(l->op){
            if(lp_is(l,"lda")||(word&&lp_is(l,"sta"))){
                if(l->m8!=!word||!lp_operand_is(l,home,n))return 0;
                if(!flags||lp_is(l,"lda"))return 1;
                int prev=lp_next(u,(unsigned)pos,-1);
                return prev>=0&&!u->lines[prev].m8&&
                    full_accumulator_flags(u->lines[prev].text,u->lines[prev].length);
            }
            size_t operand_length;const char *operand=lp_operand(l,&operand_length);
            if(lp_line_is(l,"rep #$20")||lp_line_is(l,"sep #$20")||
               (!flags&&(lp_is(l,"cmp")||lp_is(l,"cpx")||lp_is(l,"cpy"))&&operand_length>1&&operand[0]=='#')||
               (l->target>=0&&(lp_branch(l)||lp_is(l,"jmp"))))continue;
            return 0;
        }
        if(l->label){
            if(!lp_fallthrough_label(l)&&(l->length!=1||l->text[0]!=':'))return 0;
            for(int j=l->first_incoming;j>=0;j=u->lines[j].next_incoming)
                if(!lp_prior_home_value(u,j,load,home,n,word,flags,budget))return 0;
            if(pos&&u->lines[pos-1].ends)return l->first_incoming>=0;
        }else if(l->length&&l->text[0]!=';'&&strncmp(l->text,".export __inlined_",18)&&
                 !(l->length==3&&!strncmp(l->text,".a8",3))&&
                 !(l->length==4&&!strncmp(l->text,".a16",4)))return 0;
    }
    return 0;
}
/* A unit increment sets Z exactly when the unsigned addition would
 * carry. Use it directly when the branch is the last consumer of C. */
static int lp_increment_wrap_test(LpUnit *u,Function *f,size_t at)
{
    int changed=0;(void)at;
    if(body_asm_statements(f->body))return 0;
    lp_liveness(u);
    for(unsigned i=0;i<u->count;++i){
        if(!lp_line_is(&u->lines[i],"clc"))continue;
        int add=lp_next(u,i,1),branch=add<0?-1:lp_next(u,(unsigned)add,1);
        if(branch<0||!lp_is(&u->lines[add],"adc")||lp_immediate(&u->lines[add])!=1)continue;
        LpLine *edge=&u->lines[branch];size_t n;const char *target=lp_operand(edge,&n);
        if((!lp_is(edge,"bcc")&&!lp_is(edge,"bcs"))||edge->target<0||
           (edge->out&(LP_C|LP_V)))continue;
        u->lines[i].deleted=1;lp_set(&u->lines[add],"    inc a");
        lp_set(edge,"    %s %.*s",lp_is(edge,"bcc")?"bne":"beq",(int)n,target);++changed;
    }
    return changed;
}
/* Testing a far byte and then consuming it on one path only needs the
 * first read. Width changes and branches preserve both A and its flags. */
static int lp_reuse_far_byte(LpUnit *u,Function *f,size_t at)
{
    (void)f;(void)at;
    if(cg.lp_volatile||u->indirect||body_asm_statements(f->body))return 0;
    lp_liveness(u);
    for(unsigned i=0;i<u->count;++i){
        LpLine *first=&u->lines[i];
        size_t n;
        const char *op=lp_operand(first,&n);
        if(!first->m8&&lp_is(first,"lda")&&lp_private(op,n)){
            int budget=96;
            if(lp_prior_home_value(u,(int)i-1,i,op,n,1,first->out&(LP_N|LP_Z),&budget)){
                first->deleted=1;return 1;
            }
        }
        if(!first->m8||!lp_is(first,"lda")||n<13||strncmp(op,"[__arith_",9)||op[n-1]!=']')continue;
        int budget=96;
        if(!(first->out&(LP_N|LP_Z))&&lp_prior_home_value(u,(int)i-1,i,op,n,0,0,&budget)){
            first->deleted=1;return 1;
        }
        for(unsigned j=i+1;j<u->count;++j){
            LpLine *l=&u->lines[j];
            if(!l->op){
                if(lp_internal_path_marker(u,j,i)||(l->length==3&&!strncmp(l->text,".a8",3))||
                   (l->length==4&&!strncmp(l->text,".a16",4)))continue;
                break;
            }
            if(lp_line_is(l,"sep #$20")||lp_line_is(l,"rep #$20")||
               (!l->call&&l->target>=0&&(lp_branch(l)||lp_is(l,"jmp"))))continue;
            if(l->m8&&lp_is(l,"lda")&&lp_operand_is(l,op,n)){l->deleted=1;return 1;}
            break;
        }
    }
    return 0;
}
/* Unsigned A < its sign bit is the nonnegative half of the encoding.
 * A preceding load already supplied N at the comparison width. */
static int lp_sign_bit_order(LpUnit *u,Function *f,size_t at)
{
    int changed=0;
    (void)f;(void)at;
    lp_liveness(u);
    for(unsigned i=0;i<u->count;++i){
        LpLine *cmp=&u->lines[i];
        if(!lp_is(cmp,"cmp")||lp_immediate(cmp)!=(cmp->m8?128:32768))continue;
        int previous=(int)i-1;
        while(previous>=0&&!u->lines[previous].op&&
              (u->lines[previous].text[0]==';'||(u->lines[previous].length==3&&!strncmp(u->lines[previous].text,".a8",3))||
               (u->lines[previous].length==4&&!strncmp(u->lines[previous].text,".a16",4))))--previous;
        if(previous<0||u->lines[previous].m8!=cmp->m8||!lp_is(&u->lines[previous],"lda"))continue;
        unsigned j=i+1;
        while(j<u->count&&(u->lines[j].text[0]==';'||lp_line_is(&u->lines[j],"rep #$20")||
              (u->lines[j].length==4&&!strncmp(u->lines[j].text,".a16",4))))++j;
        if(j==u->count)continue;
        LpLine *br=&u->lines[j];
        if((!lp_is(br,"bcc")&&!lp_is(br,"bcs"))||(br->out&(LP_C|LP_N|LP_Z)))continue;
        size_t n;
        const char *target=lp_operand(br,&n);
        lp_set(br,"    %s %.*s",lp_is(br,"bcc")?"bpl":"bmi",(int)n,target);
        cmp->deleted=1;++changed;
    }
    return changed;
}
/* A zero-only mask test can preserve its source word for the next
 * test along the same path. Branches do not modify the frame or A. */
static int lp_keep_mask_source(LpUnit *u,Function *f,size_t at)
{
    (void)f;(void)at;
    if(u->indirect||cg.lp_volatile)return 0;
    lp_liveness(u);
    for(unsigned i=u->count;i-->0;){
        LpLine *load=&u->lines[i];
        size_t n;
        const char *home=lp_operand(load,&n);
        if(!lp_is(load,"lda")||load->m8||!lp_private(home,n))continue;
        int next=lp_next(u,i,1);
        if(next<0)continue;
        LpLine *mask=&u->lines[next];
        long bits=lp_immediate(mask);
        if(!lp_is(mask,"and")||bits<0)continue;
        int zero_only=!(mask->out&(LP_N|LP_A));
        for(unsigned j=(unsigned)next+1;j<u->count;++j){
            LpLine *l=&u->lines[j];
            if(!l->op){
                if(lp_internal_path_marker(u,j,(unsigned)next))continue;
                break;
            }
            if(!l->call&&l->target>=0&&(lp_branch(l)||lp_is(l,"jmp")))continue;
            if(!zero_only&&lp_is(l,"cmp")&&lp_immediate(l)>=0)continue;
            if(lp_is(l,"lda")&&!l->m8&&lp_operand_is(l,home,n)){
                if(zero_only&&!(l->out&(LP_N|LP_Z))){
                    lp_set(mask,"    bit #$%04lX",bits);l->deleted=1;return 1;
                }
                int repeat=lp_next(u,j,1);
                if(repeat>=0&&lp_is(&u->lines[repeat],"and")&&lp_immediate(&u->lines[repeat])==bits&&
                   !(u->lines[repeat].out&(LP_N|LP_Z))){
                    l->deleted=u->lines[repeat].deleted=1;return 1;
                }
            }
            break;
        }
    }
    return 0;
}
/* INC/DEC A supplies the same word and N/Z without fetching a
 * carry setup and immediate operand. Preserve observable C and V. */
static int lp_small_accumulator_steps(LpUnit *u,Function *f,size_t at)
{
    int changed=0;
    (void)f;(void)at;
    lp_liveness(u);
    for(unsigned i=0;i<u->count;++i){
        int sub=lp_line_is(&u->lines[i],"sec");
        if(!sub&&!lp_line_is(&u->lines[i],"clc"))continue;
        int step=lp_next(u,i,1);
        if(step<0||!lp_is(&u->lines[step],sub?"sbc":"adc")||u->lines[step].m8||
           (u->lines[step].out&(LP_C|LP_V)))continue;
        long n=lp_immediate(&u->lines[step]);
        int initial=-1;
        if(n<0&&!sub){
            initial=lp_next(u,i,-1);
            if(initial<0||!lp_is(&u->lines[initial],"lda")||u->lines[initial].m8)continue;
            n=lp_immediate(&u->lines[initial]);
        }
        if(n<0||n>65535)continue;
        unsigned delta=(unsigned)(sub?-n:n)&65535u;
        if(delta!=1&&delta!=2&&delta!=65535&&delta!=65534)continue;
        const char *op=delta<=2?"    inc a":"    dec a";
        if(initial>=0){
            /* Addition commutes. Read the original memory operand once
             * into A, then apply the literal steps without a carry setup. */
            size_t length;
            const char *operand=lp_operand(&u->lines[step],&length);
            lp_set(&u->lines[initial],"    lda %.*s",(int)length,operand);
        }
        lp_set(&u->lines[step],"%s",op);
        if(delta==2||delta==65534)lp_set(&u->lines[i],"%s",op);
        else u->lines[i].deleted=1;
        changed=1;
    }
    return changed;
}
/* Commit a high result while it is still in A, before pulling the low word.
 * Both destination words are compiler scratch, and X must die at the store. */
static int lp_store_pulled_pair(LpUnit *u,Function *f,size_t at)
{
    int changed=0;(void)f;(void)at;
    lp_liveness(u);
    for(unsigned i=0;i<u->count;++i){
        LpLine *transfer=&u->lines[i];
        if(!lp_line_is(transfer,"tax")||transfer->m8||transfer->x8)continue;
        int pull=lp_next(u,i,1),low=pull<0?-1:lp_next(u,(unsigned)pull,1);
        int high=low<0?-1:lp_next(u,(unsigned)low,1);
        if(high<0||!lp_line_is(&u->lines[pull],"pla")||!lp_is(&u->lines[low],"sta")||
           !lp_is(&u->lines[high],"stx")||(u->lines[high].out&LP_X))continue;
        size_t n,m;const char *a=lp_operand(&u->lines[low],&n),*b=lp_operand(&u->lines[high],&m);
        int first=lp_workspace_word(a,n),second=lp_workspace_word(b,m);
        if(first<0||second<0||lp_overlaps(&u->lines[high],second,first))continue;
        lp_set(transfer,"    sta %.*s",(int)m,b);u->lines[high].deleted=1;++changed;
    }
    return changed;
}
/* A discarded wide assignment sometimes protects its low word only
 * while X is stored through S. Rebase that store after dropping the save. */
static int lp_dead_stack_word_save(LpUnit *u,Function *f,size_t at)
{
    int changed=0;
    (void)f;(void)at;
    lp_liveness(u);
    for(unsigned i=0;i<u->count;++i){
        LpLine *push=&u->lines[i];
        if(!lp_line_is(push,"pha")||push->m8||push->x8)continue;
        int high=lp_next(u,i,1),store=high<0?-1:lp_next(u,(unsigned)high,1);
        int pull=store<0?-1:lp_next(u,(unsigned)store,1);
        if(pull<0||!lp_line_is(&u->lines[high],"txa")||!lp_is(&u->lines[store],"sta")||
           !lp_line_is(&u->lines[pull],"pla")||(u->lines[pull].out&(LP_A|LP_N|LP_Z)))continue;
        size_t n;
        const char *operand=lp_operand(&u->lines[store],&n);
        char *end;
        long displacement=strtol(operand,&end,10);
        if(n<3||end!=operand+n-2||end[0]!=','||end[1]!='s'||displacement<3||displacement>255)continue;
        lp_set(&u->lines[store],"    sta %ld,s",displacement-2);
        push->deleted=u->lines[pull].deleted=1;
        changed=1;
    }
    return changed;
}
/* Test the old index after an update by comparing the new index with
 * the value it has when the old one is zero. N and Z describe old A. */
static int lp_post_index_test(LpUnit *u,Function *f,size_t at)
{
    (void)f;(void)at;
    lp_liveness(u);
    for(unsigned i=0;i<u->count;++i){
        LpLine *move=&u->lines[i];
        int x=lp_line_is(move,"txa");
        if((!x&&!lp_line_is(move,"tya"))||move->m8||move->x8)continue;
        int change=lp_next(u,i,1),save=change<0?-1:lp_next(u,(unsigned)change,1);
        int restore=save<0?-1:lp_next(u,(unsigned)save,1);
        int test=restore<0?-1:lp_next(u,(unsigned)restore,1);
        if(test<0||!(lp_is(&u->lines[test],"beq")||lp_is(&u->lines[test],"bne"))||
           (u->lines[test].out&(LP_A|LP_C))||!lp_line_is(&u->lines[save],x?"tax":"tay"))continue;
        int inc=lp_line_is(&u->lines[change],"inc a");
        if((!inc&&!lp_line_is(&u->lines[change],"dec a"))||
           !lp_line_is(&u->lines[restore],inc?"dec a":"inc a"))continue;
        lp_set(move,"    %s",inc?(x?"inx":"iny"):(x?"dex":"dey"));
        lp_set(&u->lines[change],"    %s #$%04X",x?"cpx":"cpy",inc?1:65535);
        u->lines[save].deleted=u->lines[restore].deleted=1;
        return 1;
    }
    return 0;
}
static int lp_literal_stack_slot(const LpLine *l)
{
    size_t n;
    const char *p=lp_operand(l,&n);
    char *end;
    long offset=strtol(p,&end,10);
    return n>=3&&n<=5&&end==p+n-2&&p[n-2]==','&&p[n-1]=='s'&&
           offset>0&&offset<=255?(int)offset:-1;
}

/* Combine literal byte fields before copying their words to the outgoing
 * argument area. Each push rebases the next load by two bytes. */
static int lp_literal_stack_argument_bytes(LpUnit *u,Function *f,size_t at)
{
    (void)at;
    if(u->indirect||cg.lp_volatile||cg.parser->no_value_reuse||body_asm_statements(f->body))return 0;
    int changed=0;
    for(unsigned i=0;i<u->count;++i){
        if(!lp_line_is(&u->lines[i],"sep #$20"))continue;
        unsigned char known[256]={0},bytes[256];
        int prev=lp_next(u,i,-1),k=lp_next_mode(u,i);
        long literal=prev>=0&&lp_is(&u->lines[prev],"lda")?lp_immediate(&u->lines[prev]):-1;
        unsigned stores=0;
        while(k>=0&&(unsigned)k<=i+96&&!lp_line_is(&u->lines[k],"rep #$20")){
            LpLine *line=&u->lines[k];
            if(!line->m8)break;
            if(lp_is(line,"lda")&&lp_immediate(line)>=0)literal=lp_immediate(line);
            else if(lp_is(line,"sta")&&literal>=0){
                int offset=lp_literal_stack_slot(line);
                if(offset<0)break;
                bytes[offset]=(unsigned char)literal;
                known[offset]=1;
                ++stores;
            }else break;
            k=lp_next_mode(u,(unsigned)k);
        }
        if(k<0||stores<2||!lp_line_is(&u->lines[k],"rep #$20"))continue;
        int pushed=0;
        for(k=lp_next_mode(u,(unsigned)k);k>=0;k=lp_next_mode(u,(unsigned)k)){
            LpLine *load=&u->lines[k];
            if(!lp_is(load,"lda")||load->m8)break;
            int offset=lp_literal_stack_slot(load)-pushed;
            int push=lp_next_mode(u,(unsigned)k);
            if(offset<1||offset>=255||!known[offset]||!known[offset+1]||
               push<0||!lp_line_is(&u->lines[push],"pha")||u->lines[push].m8)break;
            unsigned value=(unsigned)bytes[offset]|((unsigned)bytes[offset+1]<<8);
            lp_set(load,"    lda #$%04X",value);
            pushed+=2;
            k=push;
            changed=1;
        }
    }
    return changed;
}
/* A retained index can consume a literal directly once A is dead */
static int lp_literal_to_index(LpUnit *u,Function *f,size_t at)
{
    int changed=0;
    (void)f;(void)at;
    lp_liveness(u);
    for(unsigned i=0;i<u->count;++i){
        LpLine *load=&u->lines[i];
        if(!lp_is(load,"lda")||load->m8||load->x8)continue;
        size_t n;const char *operand=lp_operand(load,&n);
        if(n<2||operand[0]!='#')continue;
        int next=lp_next(u,i,1);
        if(next<0||(u->lines[next].out&LP_A))continue;
        int x=lp_line_is(&u->lines[next],"tax");
        if(!x&&!lp_line_is(&u->lines[next],"tay"))continue;
        lp_set(load,"    %s %.*s",x?"ldx":"ldy",(int)n,operand);
        u->lines[next].deleted=1;
        changed=1;
    }
    return changed;
}
static int lp_push_immediate_word(LpUnit *u,Function *f,size_t at)
{
    int changed=0;(void)f;(void)at;
    lp_liveness(u);
    for(unsigned i=0;i<u->count;++i){
        LpLine *load=&u->lines[i];size_t n;const char *operand=lp_operand(load,&n);
        if(load->m8||!lp_is(load,"lda")||n<2||operand[0]!='#')continue;
        int push=lp_next(u,i,1);
        if(push<0||!lp_line_is(&u->lines[push],"pha"))continue;
        if(u->lines[push].out&(LP_A|LP_N|LP_Z)){
            int next=lp_next(u,(unsigned)push,1);
            if(next<0)continue;
            LpLine *call=&u->lines[next];
            Symbol *callee=call->call&&!call->ends?lp_callee(call):NULL;
            Function *body=callee?inl.by_symbol[callee-cg.parser->symbols]:NULL;
            /* A known scalar result replaces A after a stack-only
             * argument. The call still gets exactly the same bytes. */
            if(!body||callee->interrupt||callee->variadic||structure_object(callee->type)||
               reg_width(callee->type)!=2||(call->use&LP_A)||(call->out&(LP_N|LP_Z))||
               body_asm_statements(body->body)||!inl_definitely_returns(body->body))continue;
        }
        lp_set(load,"    pea %.*s",(int)n-1,operand+1);
        u->lines[push].deleted=1;++changed;
    }
    return changed;
}
/* Delay an index literal past an independent store when its only purpose
 * is to load A for the next value. */
static int lp_delay_index_literal(LpUnit *u,Function *f,size_t at)
{
    (void)f;(void)at;
    lp_liveness(u);
    for(unsigned i=0;i<u->count;++i){
        LpLine *load=&u->lines[i];
        int x=lp_is(load,"ldx");
        if((!x&&!lp_is(load,"ldy"))||load->m8||load->x8)continue;
        long value=lp_immediate(load);
        if(value<0||value>65535)continue;
        unsigned reg=x?LP_X:LP_Y;
        int store=lp_next(u,i,1);
        if(store<0||!lp_is(&u->lines[store],"sta")||(u->lines[store].use&reg))continue;
        int move=lp_next(u,(unsigned)store,1);
        if(move<0||!lp_line_is(&u->lines[move],x?"txa":"tya")||(u->lines[move].out&reg))continue;
        lp_set(&u->lines[move],"    lda #$%04lX",value);
        load->deleted=1;return 1;
    }
    return 0;
}
/* A zero index on a named absolute load or store selects the same address
 * without index calculation. Keep the register setup if later code uses it. */
/* A published pointer to a byte inside the current stack frame can still
 * be read directly through its frame index. Preserve the publication. */
static int lp_published_frame_read(LpUnit *u,Function *f,size_t at)
{
    (void)at;
    if(u->indirect||cg.lp_volatile||!f->slots||body_asm_statements(f->body))return 0;
    int known,changed=0;
    unsigned char *targets=lp_local_targets(u,&known);
    lp_liveness(u);
    for(unsigned i=0;i<u->count&&!changed;++i){
        LpLine *load=&u->lines[i];
        if(!lp_line_is(load,"lda a:$0000,x")||load->m8||load->x8||(load->out&LP_X))continue;
        int transfer=lp_next_fallthrough(u,i,-1,targets,known);
        int store=transfer<0?-1:lp_next_fallthrough(u,(unsigned)transfer,-1,targets,known);
        if(store<0||!lp_line_is(&u->lines[transfer],"tax")||!lp_is(&u->lines[store],"sta"))continue;
        int pos=lp_next_fallthrough(u,(unsigned)store,-1,targets,known),offset=0;
        while(pos>=0&&lp_line_is(&u->lines[pos],"inc a")){
            ++offset;pos=lp_next_fallthrough(u,(unsigned)pos,-1,targets,known);
        }
        if(pos<0||!offset||(unsigned)offset>f->slots||!lp_line_is(&u->lines[pos],"tya"))continue;
        do{
            pos=lp_next_fallthrough(u,(unsigned)pos,-1,targets,known);
        }while(pos>=0&&!(u->lines[pos].def&LP_Y)&&!u->lines[pos].call&&!u->lines[pos].ends);
        if(pos<0||!lp_line_is(&u->lines[pos],"tay"))continue;
        pos=lp_next(u,(unsigned)pos,-1);
        if(pos<0||!lp_line_is(&u->lines[pos],"tsc"))continue;
        u->lines[transfer].deleted=1;
        lp_set(load,"    lda a:$%04X,y",offset);changed=1;
    }
    free(targets);return changed;
}
/* Testing a word index for zero needs only a transfer when A and the
 * carry produced by the comparison are dead. N and Z match exactly. */
static int lp_test_index(LpUnit *u,Function *f,size_t at)
{
    (void)f;(void)at;
    lp_liveness(u);
    int changed=0;
    for(unsigned i=0;i<u->count;++i){
        LpLine *l=&u->lines[i];
        if((!lp_is(l,"cpx")&&!lp_is(l,"cpy"))||l->m8||l->x8||lp_immediate(l)!=0||
           (l->out&(LP_A|LP_C)))continue;
        lp_set(l,"    %s",lp_is(l,"cpx")?"txa":"tya");
        ++changed;
    }
    return changed;
}
static int lp_zero_index_address(LpUnit *u,Function *f,size_t at)
{
    (void)f;(void)at;
    lp_liveness(u);
    for(unsigned i=0;i<u->count;++i){
        LpLine *zero=&u->lines[i];
        int x=lp_is(zero,"ldx");
        if((!x&&!lp_is(zero,"ldy"))||zero->x8||lp_immediate(zero)!=0)continue;
        int next=lp_next(u,i,1);
        if(next<0)continue;
        LpLine *access=&u->lines[next];
        if(!lp_is(access,"lda")&&!lp_is(access,"sta"))continue;
        size_t n;
        const char *p=lp_operand(access,&n);
        if(n<5||p[0]!='a'||p[1]!=':'||p[n-2]!=','||p[n-1]!=(x?'x':'y')||
           !pr_named(p,n-2))continue;
        lp_set(access,"    %.3s %.*s",access->op,(int)n-2,p);
        unsigned needed=x?LP_X:LP_Y;
        if(lp_is(access,"sta"))needed|=LP_N|LP_Z;
        if(!(access->out&needed))zero->deleted=1;
        return 1;
    }
    return 0;
}

/* Taking a named near address through A and X need not hide the
 * identity of the subsequent zero-displacement load. */
static int lp_direct_relocated_read(LpUnit *u,Function *f,size_t at)
{
    (void)at;
    if(u->indirect||cg.lp_volatile||cg.parser->no_indexed_operands||
       cg.parser->no_value_reuse||body_asm_statements(f->body))return 0;
    lp_liveness(u);
    for(unsigned i=0;i<u->count;++i){
        LpLine *load=&u->lines[i];
        if(load->m8||load->x8||!lp_is(load,"lda"))continue;
        size_t n;
        const char *operand=lp_operand(load,&n);
        if(n<12||n>120||strncmp(operand,"#.loword(_",10)||operand[n-1]!=')')continue;
        char direct[128];
        snprintf(direct,sizeof direct,"a:%.*s",(int)n-1,operand+1);
        if(!pr_named(direct,n+1))continue;
        for(unsigned j=i+1;j<u->count&&j-i<28;++j){
            LpLine *line=&u->lines[j];
            if(lp_internal_path_marker(u,j,i))continue;
            if(!line->op||line->m8||line->x8)break;
            if(lp_line_is(line,"tax")){
                int read=lp_next(u,j,1);
                if(read<0||!lp_line_is(&u->lines[read],"lda a:$0000,x")||
                   u->lines[read].m8||u->lines[read].x8)break;
                lp_set(&u->lines[read],"    lda %s",direct);
                if(!(u->lines[read].out&LP_X))line->deleted=1;
                return 1;
            }
            if(!lp_is(line,"sta")&&!lp_is(line,"stx")&&!lp_is(line,"sty")&&!lp_is(line,"stz"))break;
        }
    }
    return 0;
}
/* Move an adjusted index directly to X or Y when the intermediate
 * accumulator copy does not escape the transfer. */
static int lp_index_transfer_steps(LpUnit *u,Function *f,size_t at)
{
    (void)f;(void)at;
    lp_liveness(u);
    for(unsigned i=0;i<u->count;++i){
        LpLine *start=&u->lines[i];
        int from_x=lp_line_is(start,"txa");
        if((!from_x&&!lp_line_is(start,"tya"))||start->m8||start->x8)continue;
        int first=lp_next(u,i,1),copy=-1;
        if(first>=0&&lp_line_is(&u->lines[first],from_x?"tay":"tax")){
            copy=first;
            first=lp_next(u,(unsigned)copy,1);
        }
        int end=first;
        while(end>=0&&(lp_line_is(&u->lines[end],"inc a")||lp_line_is(&u->lines[end],"dec a")))
            end=lp_next(u,(unsigned)end,1);
        if(end<0||end==first)continue;
        int to_x=lp_line_is(&u->lines[end],"tax");
        if(!to_x&&!lp_line_is(&u->lines[end],"tay"))continue;
        int keep_a=(u->lines[end].out&LP_A)!=0;
        if((keep_a||copy>=0)&&from_x!=to_x)continue;
        if(copy>=0)lp_set(&u->lines[copy],"    %s",from_x?"txy":"tyx");
        if(from_x==to_x)start->deleted=1;
        else lp_set(start,"    %s",to_x?"tyx":"txy");
        for(int k=first;k!=end;k=lp_next(u,(unsigned)k,1)){
            int inc=lp_line_is(&u->lines[k],"inc a");
            lp_set(&u->lines[k],"    %s",to_x?(inc?"inx":"dex"):(inc?"iny":"dey"));
        }
        if(keep_a)lp_set(&u->lines[end],"    %s",to_x?"txa":"tya");
        else u->lines[end].deleted=1;
        return 1;
    }
    return 0;
}
/* (A + c) * 2^k + d has one combined word displacement. Its final
 * carry and overflow differ from the two-add sequence and must be dead. */
static int lp_scaled_displacement(LpUnit *u,Function *f,size_t at)
{
    (void)f;(void)at;
    lp_liveness(u);
    for(unsigned i=0;i<u->count;++i){
        if(!lp_line_is(&u->lines[i],"clc"))continue;
        int first=lp_next(u,i,1);
        if(first<0||!lp_is(&u->lines[first],"adc")||u->lines[first].m8)continue;
        long add=lp_immediate(&u->lines[first]);
        if(add<0||add>65535)continue;
        int k=lp_next(u,(unsigned)first,1);
        unsigned shifts=0;
        while(k>=0&&lp_line_is(&u->lines[k],"asl a")&&!u->lines[k].m8&&shifts<15){
            ++shifts;k=lp_next(u,(unsigned)k,1);
        }
        if(!shifts||k<0||!lp_line_is(&u->lines[k],"clc"))continue;
        int last=lp_next(u,(unsigned)k,1);
        if(last<0||!lp_is(&u->lines[last],"adc")||u->lines[last].m8||
           (u->lines[last].out&(LP_C|LP_V)))continue;
        long tail=lp_immediate(&u->lines[last]);
        if(tail<0||tail>65535)continue;
        lp_set(&u->lines[last],"    adc #$%04X",(((unsigned)add<<shifts)+(unsigned)tail)&65535u);
        u->lines[i].deleted=u->lines[first].deleted=1;
        return 1;
    }
    return 0;
}
/* The zero flag already represents both scalar truth values across an
 * inlined, effect-free arm. Keep marker paths and the original branch. */
static int lp_materialized_zero_flag(LpUnit *u,Function *f,size_t at)
{
    int known,changed=0;
    unsigned char *targets=lp_local_targets(u,&known);
    (void)f;(void)at;
    if(!known){free(targets);return 0;}
    lp_liveness(u);
    for(unsigned i=0;i<u->count;++i){
        LpLine *br=&u->lines[i];
        if(!(lp_is(br,"beq")||lp_is(br,"bne"))||br->target!=(int)i+2||
           !lp_is(&u->lines[i+1],"jmp")||u->lines[i+1].target<=br->target||
           targets[br->target]!=1||targets[u->lines[i+1].target]!=1)continue;
        unsigned branch=(unsigned)u->lines[i+1].target,first=i+3,second=branch+1;
        while(first<branch&&lp_fallthrough_marker(&u->lines[first],first,targets,known))++first;
        if(first>=branch||!lp_is(&u->lines[first],"lda")||u->lines[first].m8)continue;
        long high=lp_immediate(&u->lines[first]);
        if(high<0||high>65535)continue;
        int skip=lp_next(u,first,1);
        if(skip<0||(unsigned)skip+1!=branch||!lp_is(&u->lines[skip],"jmp")||u->lines[skip].target<=(int)branch)continue;
        unsigned join=(unsigned)u->lines[skip].target;
        while(second<join&&lp_fallthrough_marker(&u->lines[second],second,targets,known))++second;
        if(second>=join||!lp_is(&u->lines[second],"lda")||u->lines[second].m8)continue;
        long low=lp_immediate(&u->lines[second]);
        if(low<0||low>65535||!!low==!!high)continue;
        unsigned end=second+1;
        while(end<join&&lp_fallthrough_marker(&u->lines[end],end,targets,known))++end;
        int test=lp_next(u,join,1);
        int compare=-1;
        if(test>=0&&lp_is(&u->lines[test],"cmp")&&!u->lines[test].m8){
            long literal=lp_immediate(&u->lines[test]);
            if(literal<0||targets[join]!=1||(low==literal)==(high==literal))continue;
            /* The consuming equality branch observes Z from the compare.
             * Treat an unequal arm as nonzero for the same flag proof. */
            compare=test;test=lp_next(u,(unsigned)test,1);
            if(test>=0&&end==join&&(u->lines[test].out&LP_A)&&
               !(u->lines[test].out&(LP_N|LP_Z|LP_C))&&
               (lp_is(&u->lines[test],"beq")||lp_is(&u->lines[test],"bne"))){
                if((high==0)!=(high==literal)){
                    size_t n;const char *target=lp_operand(&u->lines[test],&n);
                    lp_set(&u->lines[test],"    %s %.*s",lp_is(&u->lines[test],"beq")?"bne":"beq",(int)n,target);
                }
                u->lines[compare].deleted=1;changed=1;continue;
            }
            high=high!=literal;
        }
        if(end!=join||test<0||(compare>=0&&(u->lines[test].out&LP_C))||
           !(lp_is(&u->lines[test],"beq")||lp_is(&u->lines[test],"bne"))||
           (u->lines[test].out&(LP_A|LP_N)))continue;
        if(!!high!=lp_is(br,"bne")){
            LpLine *consumer=&u->lines[test];
            size_t n;
            const char *target=lp_operand(consumer,&n);
            if(targets[join]!=1||(consumer->out&LP_Z))continue;
            lp_set(consumer,"    %s %.*s",lp_is(consumer,"beq")?"bne":"beq",(int)n,target);
        }
        if(compare>=0)u->lines[compare].deleted=1;
        u->lines[first].deleted=u->lines[second].deleted=1;
        changed=1;
    }
    free(targets);return changed;
}
/* An A8 load preserves the hidden accumulator high byte */
static int lp_zero_high_across_byte_load(LpUnit *u,Function *f,size_t at)
{
    int zero_high=0,low=-1,changed=0;
    (void)f;(void)at;
    lp_liveness(u);
    for(unsigned i=0;i<u->count;++i){
        LpLine *l=&u->lines[i];
        if(!l->op){
            if(l->length&&(l->text[0]==';'||!strncmp(l->text,".a8\n",4)||!strncmp(l->text,".a16\n",5)))continue;
            zero_high=0;low=-1;continue;
        }
        if(lp_is(l,"lda")){
            long value=lp_immediate(l);
            if(l->m8&&value>=0&&low==(int)(value&255)&&!(lp_byte_live_out(u,i)&(LP_N|LP_Z))){
                l->deleted=1;++changed;continue;
            }
            low=value<0?-1:(int)(value&255);
        }else if(!(lp_line_is(l,"sep #$20")||lp_line_is(l,"rep #$20")||lp_is(l,"sta")))
            low=-1;
        if(!l->m8&&(lp_is(l,"lda")||lp_is(l,"and"))){
            long value=lp_immediate(l);
            if(value==255&&lp_is(l,"and")&&zero_high&&!(l->out&(LP_N|LP_Z))){
                l->deleted=1;changed=1;
            }
            zero_high=value>=0&&value<=255;
        }else if(!(lp_line_is(l,"sep #$20")||lp_line_is(l,"rep #$20")||lp_is(l,"sta")||
                   (l->m8&&lp_is(l,"lda"))))zero_high=0;
    }
    return changed;
}
/* Fold a word shift sequence selected after source-level folding, such
 * as a byte exchange followed by shifts. XBA sets byte-sized N and Z. */
static int lp_literal_shifts(LpUnit *u,Function *f,size_t at)
{
    int changed=0;
    (void)f;(void)at;
    lp_liveness(u);
    for(unsigned i=0;i<u->count;++i){
        LpLine *load=&u->lines[i];
        long initial=lp_immediate(load);
        if(!lp_is(load,"lda")||load->m8||initial<0||initial>65535)continue;
        unsigned value=(unsigned)initial,final=value;
        int last=-1,k=(int)i,carry=0;
        while((k=lp_next(u,(unsigned)k,1))>=0){
            LpLine *l=&u->lines[k];
            int swap=lp_line_is(l,"xba");
            if(swap)value=((value>>8)|(value<<8))&65535;
            else if(lp_line_is(l,"asl a")){value=(value<<1)&65535;carry=1;}
            else if(lp_line_is(l,"lsr a")){value>>=1;carry=1;}
            else break;
            if((!carry||!(l->out&LP_C))&&(!swap||!(l->out&(LP_N|LP_Z)))){last=k;final=value;}
        }
        if(last<0)continue;
        lp_set(load,"    lda #$%04X",final);
        for(k=(int)i;k!=last;){k=lp_next(u,(unsigned)k,1);u->lines[k].deleted=1;}
        ++changed;i=(unsigned)last;
    }
    return changed;
}

/* A literal low limb decides whether the known high limb is stepped.
 * Fold both modular words after checking that the arithmetic flags die. */
static int lp_literal_limb_carry(LpUnit *u,Function *f,size_t at)
{
    (void)at;
    if(u->indirect||f->symbol->interrupt||body_asm_statements(f->body))return 0;
    lp_liveness(u);
    for(unsigned i=0;i<u->count;++i){
        int second=lp_next(u,i,1);
        if(second<0)continue;
        LpLine *low=&u->lines[i],*high=&u->lines[second];
        if(lp_is(low,"ldx")){LpLine *swap=low;low=high;high=swap;}
        if(low->m8||high->x8||!lp_is(low,"lda")||!lp_is(high,"ldx"))continue;
        long a=lp_immediate(low),x=lp_immediate(high);
        if(a<0||a>65535||x<0||x>65535)continue;
        int carry=lp_next(u,(unsigned)second,1);
        int op=carry<0?-1:lp_next(u,(unsigned)carry,1);
        int branch=op<0?-1:lp_next(u,(unsigned)op,1);
        int step=branch<0?-1:lp_next(u,(unsigned)branch,1);
        if(step<0)continue;
        int subtract=lp_line_is(&u->lines[carry],"sec");
        if((!subtract&&!lp_line_is(&u->lines[carry],"clc"))||u->lines[op].m8||
           !lp_is(&u->lines[op],subtract?"sbc":"adc")||
           !lp_is(&u->lines[branch],subtract?"bcs":"bcc")||
           !lp_line_is(&u->lines[step],subtract?"dex":"inx")||u->lines[step].x8)continue;
        long operand=lp_immediate(&u->lines[op]);
        int join=u->lines[branch].target;
        if(operand<0||operand>65535||join<=step||
           u->lines[join].first_incoming!=branch||u->lines[branch].next_incoming>=0||
           u->lines[join].live&LP_FLAGS)continue;
        int j=step+1;
        while(j<join&&u->lines[j].length&&u->lines[j].text[0]==';')++j;
        if(j!=join)continue;
        long value=subtract?a-operand:a+operand;
        if(value<0)--x;
        if(value>65535)++x;
        lp_set(low,"    lda #$%04X",(unsigned)value&65535u);
        lp_set(high,"    ldx #$%04X",(unsigned)x&65535u);
        u->lines[carry].deleted=u->lines[op].deleted=u->lines[branch].deleted=u->lines[step].deleted=1;
        return 1;
    }
    return 0;
}

static int lp_const_branches(LpUnit *u,Function *f,size_t at)
{
    unsigned i;int changed=0;(void)f;(void)at;
    int known_targets;
    int marker_literals=!body_asm_statements(f->body)&&!find_symbol(cg.parser,"$basic_asm");
    unsigned char *targets=lp_local_targets(u,&known_targets);
    lp_liveness(u);
    for(i=0;i<u->count;++i){
        LpLine *l=&u->lines[i];int k,j,s;long v,w;
        if(lp_is(l,"lda")&&!l->replace&&!l->deleted&&(v=lp_immediate(l))>=0){
            int last=(int)i;
            while((k=lp_next_fallthrough(u,(unsigned)last,1,targets,known_targets))>=0&&
                  !u->lines[k].deleted&&!u->lines[k].replace&&
                  (lp_is(&u->lines[k],"sta")||lp_is(&u->lines[k],"stx")||
                   lp_is(&u->lines[k],"sty")||lp_is(&u->lines[k],"stz")))last=k;
            if(last!=(int)i&&k>=0&&lp_branch(&u->lines[k])){
                unsigned sign=l->m8?128u:32768u,value=(unsigned)v&(2*sign-1);
                changed+=lp_fold_branches(u,last,value==0,-1,(value&sign)!=0,-1);
            }
        }
        if(l->m8&&lp_is(l,"lda")&&!l->replace&&!l->deleted&&(v=lp_immediate(l))>=0&&
           (k=lp_next(u,i,1))>=0&&lp_line_is(&u->lines[k],"rep #$20")&&
           (unsigned)k+1<u->count&&u->lines[k+1].length==4&&!strncmp(u->lines[k+1].text,".a16",4)){
            /* Restoring A16 leaves the byte load's N/Z unchanged */
            int branch=lp_next(u,(unsigned)k+1,1);
            if(branch>=0&&lp_branch(&u->lines[branch]))
                changed+=lp_fold_branches(u,k+1,(v&255)==0,-1,(v&128)!=0,-1);
        }
        if(l->m8&&lp_is(l,"lda")&&!l->replace&&!l->deleted&&(v=lp_immediate(l))>=0&&
           (k=lp_next(u,i,1))>=0&&lp_is(&u->lines[k],"cmp")&&u->lines[k].m8&&
           !u->lines[k].replace&&!u->lines[k].deleted&&(w=lp_immediate(&u->lines[k]))>=0){
            int end=k,rep=lp_next(u,(unsigned)k,1);
            if(rep>=0&&lp_line_is(&u->lines[rep],"rep #$20")&&
               (unsigned)rep+1<u->count&&u->lines[rep+1].length==4&&
               !strncmp(u->lines[rep+1].text,".a16",4))end=rep+1;
            unsigned left=(unsigned)v&255u,right=(unsigned)w&255u;
            changed+=lp_fold_branches(u,end,left==right,left>=right,((left-right)&128u)!=0,-1);
            continue;
        }
        if(!l->m8&&!l->x8&&!l->replace&&!l->deleted&&
           (lp_is(l,"lda")||lp_is(l,"ldx")||lp_is(l,"ldy"))){
            size_t n;const char *p=lp_operand(l,&n);
            size_t prefix=n>10&&!strncmp(p,"#.loword(",9)?9:
                          n>12&&!strncmp(p,"#.bankbyte(",11)?11:0;
            int relocated=0;
            if(prefix&&p[n-1]==')'){
                size_t h=prefix;
                while(h<n-1&&(isalnum((unsigned char)p[h])||p[h]=='_'||p[h]=='+'||
                      p[h]=='-'||p[h]=='$'))++h;
                relocated=h==n-1;
            }
            long index=lp_immediate(l);
            if(lp_is(l,"lda")&&!marker_literals)index=-1;
            int earlier=changed;
            if(relocated||index>=0){
                unsigned reg=lp_is(l,"lda")?LP_A:lp_is(l,"ldx")?LP_X:LP_Y;
                const char *compare=reg==LP_A?"cmp":reg==LP_X?"cpx":"cpy";
                for(k=(int)i;(k=lp_next_fallthrough(u,(unsigned)k,1,targets,known_targets))>=0;){
                    LpLine *test=&u->lines[k];
                    if(test->deleted||test->replace||test->m8||test->x8||test->call||
                       test->ends||lp_branch(test)||test->def&reg)break;
                    if(!lp_is(test,compare))continue;
                    if(relocated&&lp_operand_is(test,p,n)){
                        changed+=lp_fold_branches(u,k,1,1,0,-1);break;
                    }
                    long right=lp_immediate(test);
                    if(index>=0&&right>=0){
                        unsigned left=(unsigned)index&65535u,value=(unsigned)right&65535u;
                        changed+=lp_fold_branches(u,k,left==value,left>=value,((left-value)&32768u)!=0,-1);
                        break;
                    }
                }
            }
            if(changed!=earlier)continue;
        }
        if(!lp_is(l,"lda")||l->m8||l->replace||l->deleted||(v=lp_immediate(l))<0)continue;
        if((k=lp_next(u,i,1))<0)continue;
        if(u->lines[k].replace||u->lines[k].deleted)continue;
        if(!u->lines[k].m8&&(lp_line_is(&u->lines[k],"inc a")||lp_line_is(&u->lines[k],"dec a"))){
            /* Both forms set word N/Z and preserve incoming C/V */
            unsigned value=((unsigned)v+(lp_is(&u->lines[k],"inc")?1u:65535u))&65535;
            lp_set(l,"    lda #$%04X",value);u->lines[k].deleted=1;++changed;continue;
        }
        {int test=k;unsigned value=(unsigned)v;
         /* Stores and index-register setup leave the known A unchanged.
          * An immediate CMP supplies new N/Z/C before the branch. */
         while(test>=0&&!u->lines[test].replace&&!u->lines[test].deleted){
             if(!u->lines[test].m8&&lp_line_is(&u->lines[test],"inc a"))value=(value+1)&65535u;
             else if(!u->lines[test].m8&&lp_line_is(&u->lines[test],"dec a"))value=(value-1)&65535u;
             else if(!(lp_is(&u->lines[test],"ldx")||lp_is(&u->lines[test],"ldy")||
               lp_is(&u->lines[test],"stx")||lp_is(&u->lines[test],"sty")||
               lp_is(&u->lines[test],"sta")||lp_is(&u->lines[test],"stz")||
                lp_line_is(&u->lines[test],"tax")||lp_line_is(&u->lines[test],"tay")))break;
             do{++test;}while((unsigned)test<u->count&&
                   lp_fallthrough_marker(&u->lines[test],(unsigned)test,targets,known_targets));
             if((unsigned)test==u->count)test=-1;
         }
         if(test>=0&&test!=k&&!u->lines[test].replace&&!u->lines[test].deleted&&
            !u->lines[test].m8&&(w=lp_immediate(&u->lines[test]))>=0&&
            (lp_is(&u->lines[test],"and")||lp_is(&u->lines[test],"ora")||lp_is(&u->lines[test],"eor"))){
             LpLine *bitwise=&u->lines[test];
             unsigned result=lp_is(bitwise,"and")?value&(unsigned)w:
                             lp_is(bitwise,"ora")?value|(unsigned)w:value^(unsigned)w;
             lp_set(bitwise,"    lda #$%04X",result&65535u);++changed;continue;
         }
         if(test>=0&&test!=k&&!u->lines[test].replace&&!u->lines[test].deleted&&
            lp_is(&u->lines[test],"cmp")&&!u->lines[test].m8&&(w=lp_immediate(&u->lines[test]))>=0){
             unsigned diff=(value-(unsigned)w)&65535u;
             changed+=lp_fold_branches(u,test,diff==0,value>=(unsigned)w,(diff>>15)&1,-1);continue;
         }}
        if((lp_is(&u->lines[k],"and")||lp_is(&u->lines[k],"ora")||lp_is(&u->lines[k],"eor"))&&!u->lines[k].m8&&
           (w=lp_immediate(&u->lines[k]))>=0){
            long r=lp_is(&u->lines[k],"and")?v&w:lp_is(&u->lines[k],"ora")?v|w:v^w;
            lp_set(l,"    lda #$%04lX",r&0xFFFF);u->lines[k].deleted=1;++changed;continue;
        }
        if(lp_is(&u->lines[k],"cmp")&&!u->lines[k].m8&&(w=lp_immediate(&u->lines[k]))>=0){
            unsigned diff=(unsigned)(v-w)&0xFFFFu;
            changed+=lp_fold_branches(u,k,diff==0,v>=w,(diff>>15)&1,-1);
            continue;
        }
        if(lp_branch(&u->lines[k])){changed+=lp_fold_branches(u,(int)i,v==0,-1,(int)(v>>15)&1,-1);continue;}
        /* A shifted constant: the carry out must be dead */
        if(lp_line_is(&u->lines[k],"asl a")&&!u->lines[k].m8&&!(u->lines[k].out&LP_C)){
            lp_set(l,"    lda #$%04lX",(v<<1)&0xFFFF);u->lines[k].deleted=1;++changed;continue;
        }
        /* Copies and stores of the constant leave A, C and V alone */
        for(j=k;j>=0&&!u->lines[j].replace&&!u->lines[j].deleted&&
            (lp_line_is(&u->lines[j],"tay")||lp_line_is(&u->lines[j],"tax")||(lp_is(&u->lines[j],"sta")&&!u->lines[j].m8));)
            j=lp_next(u,(unsigned)j,1);
        if(j<0||(!lp_line_is(&u->lines[j],"sec")&&!lp_line_is(&u->lines[j],"clc"))||u->lines[j].replace||u->lines[j].deleted)continue;
        if((s=lp_next(u,(unsigned)j,1))<0||u->lines[s].replace||u->lines[s].deleted||u->lines[s].m8)continue;
        {
            LpLine *o=&u->lines[s];int sub=lp_line_is(&u->lines[j],"sec");
            if(!(sub?lp_is(o,"sbc"):lp_is(o,"adc")))continue;
            if((w=lp_immediate(o))>=0){
                long r=(sub?v-w:v+w)&0xFFFF;
                int c=sub?v>=w:v+w>0xFFFF,ov=(int)(((sub?(v^w):~(v^w))&(v^r)&0x8000)!=0),folded;
                folded=lp_fold_branches(u,s,r==0,c,(int)(r>>15)&1,ov);
                if(folded){changed+=folded;continue;}
                if(j==k&&!(o->out&(LP_C|LP_V))){
                    lp_set(l,"    lda #$%04lX",r);u->lines[j].deleted=1;o->deleted=1;++changed;
                }
            }else if(!v&&!sub&&j==k&&!(o->out&(LP_C|LP_V))){
                /* 0 + M is M; LDA sets N and Z alike */
                size_t m;const char *p=lp_operand(o,&m);
                lp_set(l,"    lda %.*s",(int)m,p);u->lines[j].deleted=1;o->deleted=1;++changed;
            }
        }
    }
    for(i=0;i<u->count;++i){LpLine *l=&u->lines[i];unsigned t;
        if(l->deleted||l->replace||!l->op||l->call||(!lp_branch(l)&&!lp_is(l,"jmp"))||
           l->target<0||(unsigned)l->target<=i)continue;
        for(t=i+1;t<u->count;++t){LpLine *m=&u->lines[t];
            if(t==(unsigned)l->target){l->deleted=1;++changed;break;}
            if(!m->deleted&&m->length&&!m->label&&m->text[0]!=';')break;
        }
    }
    free(targets);
    return changed;
}
/* Instructions no path from the entry reaches */
static int lp_unreachable(LpUnit *u,Function *f,size_t at)
{
    unsigned i,*work,top=0,first=u->count;char *seen;int changed=0;(void)f;(void)at;
    if(u->indirect)return 0;
    for(i=0;i<u->count&&first==u->count;++i)if(u->lines[i].op)first=i;
    if(first==u->count)return 0;
    seen=calloc(u->count,1);work=malloc((u->count+1)*sizeof *work);
    if(!seen||!work){fputs("out of memory emitting assembly\n",stderr);exit(EXIT_FAILURE);}
    work[top++]=0;seen[0]=1;
    /* Named labels other than compiler-local ones may be entered from outside */
    for(i=0;i<u->count;++i){
        const LpLine *l=&u->lines[i];
        if(l->label&&!(l->length==1)&&strncmp(l->text,"cg_",3)&&strncmp(l->text,"return_",7)&&!seen[i]){seen[i]=1;work[top++]=i;}
    }
    while(top){
        unsigned k=work[--top];
        for(;k<u->count;++k){
            const LpLine *l=&u->lines[k];
            seen[k]=1;
            if(!l->op)continue;
            if(l->target>=0&&!seen[l->target]){seen[l->target]=1;work[top++]=(unsigned)l->target;}
            if(l->ends)break;
            if(k+1<u->count&&seen[k+1])break;
        }
    }
    for(i=0;i<u->count;++i)if(u->lines[i].op&&!seen[i]&&!u->lines[i].deleted){u->lines[i].deleted=1;++changed;}
    free(seen);free(work);
    return changed;
}
/* A == index + c before each line: -2 unreached, -1 unknown, else c */
static void lp_accumulator_offsets(const LpUnit *u,long *state,unsigned index)
{
    unsigned i;int changed=1;
    const char *read=index==LP_X?"txa":"tya",*write=index==LP_X?"tax":"tay";
    const char *up=index==LP_X?"inx":"iny",*down=index==LP_X?"dex":"dey";
    for(i=0;i<u->count;++i)state[i]=-2;
    if(u->count)state[0]=-1;
    while(changed){
        changed=0;
        for(i=0;i<u->count;++i){
            const LpLine *l=&u->lines[i];long in=state[i],out=in;
            if(in==-2)continue;
            if(l->op){
                long k;int prev=lp_next(u,i,-1);
                if(l->call||l->use==LP_ALL)out=-1;
                else if(lp_line_is(l,read)||lp_line_is(l,write))out=l->m8||l->x8?-1:0;
                else if(in>=0&&lp_is(l,"sbc")&&!l->m8&&(k=lp_immediate(l))>=0&&prev>=0&&lp_line_is(&u->lines[prev],"sec"))out=(in-k)&0xFFFF;
                else if(in>=0&&lp_is(l,"adc")&&!l->m8&&(k=lp_immediate(l))>=0&&prev>=0&&lp_line_is(&u->lines[prev],"clc"))out=(in+k)&0xFFFF;
                else if(in>=0&&(lp_line_is(l,"inc a")||lp_line_is(l,"inc"))&&!l->m8)out=(in+1)&0xFFFF;
                else if(in>=0&&(lp_line_is(l,"dec a")||lp_line_is(l,"dec"))&&!l->m8)out=(in-1)&0xFFFF;
                else if(in>=0&&lp_line_is(l,up)&&!l->x8)out=(in-1)&0xFFFF;
                else if(in>=0&&lp_line_is(l,down)&&!l->x8)out=(in+1)&0xFFFF;
                else if(l->def&(LP_A|index)||((l->m8||l->x8)&&l->def))out=-1;
                else if((lp_is(l,"lda")||lp_is(l,"adc")||lp_is(l,"sbc")||lp_is(l,"and")||lp_is(l,"ora")||lp_is(l,"eor")||
                         lp_is(l,"pla")||lp_is(l,"txa")||lp_is(l,"tya")||lp_is(l,"xba"))&&l->m8)out=-1;
            }
            /* Meet into successors */
            {unsigned s[2];int c=0,j;
             if(!l->op||!l->ends){if(i+1<u->count)s[c++]=i+1;}
             if(l->op&&l->target>=0)s[c++]=(unsigned)l->target;
             for(j=0;j<c;++j){long old=state[s[j]],nw=old==-2?out:old==out?old:-1;if(nw!=old){state[s[j]]=nw;changed=1;}}}
        }
    }
}
/* Read "lda n,s" plus its constant adjustment (SEC/SBC #k, CLC/ADC #k,
 * INC A, DEC A): sets *k and *end (last adjustment line). 0 if not. */
static int lp_adjusted_read(const LpUnit *u,unsigned i,long *k,int *end,int *cost)
{
    int j=(int)i,n;*k=0;*end=(int)i;*cost=0;
    while((n=lp_next(u,(unsigned)j,1))>=0){
        const LpLine *a=&u->lines[n];int m;long v;
        if(a->m8||a->replace||a->deleted)break;
        if(lp_line_is(a,"inc a")||lp_line_is(a,"inc")){++*k;*cost+=2;j=*end=n;continue;}
        if(lp_line_is(a,"dec a")||lp_line_is(a,"dec")){--*k;*cost+=2;j=*end=n;continue;}
        if((lp_line_is(a,"sec")||lp_line_is(a,"clc"))&&(m=lp_next(u,(unsigned)n,1))>=0&&
           lp_is(&u->lines[m],lp_line_is(a,"sec")?"sbc":"adc")&&!u->lines[m].m8&&(v=lp_immediate(&u->lines[m]))>=0){
            *k+=lp_line_is(a,"sec")?-v:v;*cost+=5;j=*end=m;continue;
        }
        break;
    }
    *k&=0xFFFF;return 1;
}
/* Reuse the frame address already in A on every path to this calculation */
static int lp_redundant_y_offset(LpUnit *u,Function *f,size_t at)
{
    int changed=0;
    (void)at;
    if(u->indirect||cg.parser->no_value_reuse||body_asm_statements(f->body))return 0;
    long *offsets=allocate(u->count*sizeof *offsets);
    lp_accumulator_offsets(u,offsets,LP_Y);
    lp_liveness(u);
    for(unsigned i=0;i<u->count;++i){
        LpLine *base=&u->lines[i];
        long offset;int last,cost;
        if(offsets[i]<0||base->m8||base->x8||!lp_line_is(base,"tya"))continue;
        lp_adjusted_read(u,i,&offset,&last,&cost);
        if(cost&&offset==offsets[i]&&!(u->lines[last].out&LP_FLAGS)){
            for(unsigned j=i;j<=(unsigned)last;++j)
                if(u->lines[j].op)u->lines[j].deleted=1;
            changed=1;
            break;
        }
    }
    free(offsets);
    return changed;
}
/* A direct call whose callee takes no stack arguments (at most two named
 * word parameters, not variadic), so it reads nothing of the caller's stack. */
static int lp_register_call(const LpLine *l)
{
    size_t n;const char *name=lp_operand(l,&n);unsigned i;
    if(n>9&&!strncmp(name,".loword(",8)&&name[n-1]==')'){name+=8;n-=9;}
    if(n<2||name[0]!='_')return 0;
    ++name;--n;
    for(i=0;i<cg.parser->symbol_count;++i){
        const Symbol *s=&cg.parser->symbols[i];unsigned k;
        if(!s->function||s->owner||strlen(s->asm_name)!=n||strncmp(s->asm_name,name,n))continue;
        if(s->variadic||s->param_count<0||s->param_count>2)return 0;
        for(k=0;k<(unsigned)s->param_count;++k)if(reg_width(s->params[k])!=2)return 0;
        return 1;
    }
    return 0;
}
/* A pushed copy of X whose reads all add a constant: push A = X + c instead
 * and fold c into each read. A compare's subtraction (n - 2 for n < 2)
 * then serves the later n - 1 and n - 2. */
static int lp_push_offsets(LpUnit *u,Function *f,size_t at)
{
    unsigned i,first=u->count;long *ax;int *sd,changed=0;char *region;
    (void)f;(void)at;
    if(u->indirect)return 0;
    for(i=0;i<u->count&&first==u->count;++i)if(u->lines[i].op)first=i;
    if(first==u->count)return 0;
    ax=malloc(u->count*sizeof *ax);sd=malloc(u->count*sizeof *sd);region=malloc(u->count);
    if(!ax||!sd||!region){fputs("out of memory emitting assembly\n",stderr);exit(EXIT_FAILURE);}
    lp_liveness(u);lp_accumulator_offsets(u,ax,LP_X);
    if(!lp_stack_depths(u,first,sd)){free(ax);free(sd);free(region);return 0;}
    for(i=0;i<u->count&&!changed;++i){
        LpLine *p=&u->lines[i];unsigned j;int top,ok=1,gain=0,slot_depth;long c=ax[i];
        if(!lp_line_is(p,"phx")||p->m8||p->x8||c<=0||sd[i]<0)continue;
        slot_depth=sd[i]+2;
        /* The region where the slot is on the stack: forward from the push
         * until it is popped. */
        memset(region,0,u->count);
        {unsigned *work=malloc((u->count+1)*sizeof *work);top=0;
         if(!work){fputs("out of memory emitting assembly\n",stderr);exit(EXIT_FAILURE);}
         if(i+1<u->count){work[top++]=i+1;}
         while(top&&ok){
             unsigned k=work[--top];
             for(;k<u->count;++k){
                 const LpLine *l=&u->lines[k];
                 if(region[k])break;
                 region[k]=1;
                 if(!l->op)continue;
                 if(sd[k]<slot_depth){ok=0;break;}
                 if(l->ends&&!l->call&&l->target<0){ok=0;break;} /* return with the slot pushed */
                 if(l->target>=0&&!region[l->target])work[top++]=(unsigned)l->target;
                 if(l->ends)break;
                 if(k+1<u->count&&sd[k+1]>=0&&sd[k+1]<slot_depth){
                     /* This line pops the slot: a dead 16-bit pull, or the TSC/TCS cleanup */
                     if(!((lp_line_is(l,"plx")&&!(l->out&LP_X))||(lp_line_is(l,"pla")&&!(l->out&LP_A))||
                          (lp_line_is(l,"ply")&&!(l->out&LP_Y))||lp_is(l,"tcs"))||l->m8||l->x8){ok=0;}
                     break;
                 }
             }
         }
         free(work);}
        if(!ok)continue;
        /* Labels in the region are entered only from it */
        for(j=0;j<u->count&&ok;++j){
            const LpLine *l=&u->lines[j];
            if(l->op&&l->target>=0&&region[l->target]&&!region[j]&&j!=i)ok=0;
        }
        for(j=0;j<u->count&&ok;++j)if(region[j]&&u->lines[j].label&&j&&!region[j-1]&&j-1!=i){
            int prev=(int)j-1;while(prev>=0&&!u->lines[prev].op)--prev;
            if(prev>=0&&prev!=(int)i&&!region[prev]&&!u->lines[prev].ends)ok=0;
        }
        /* Every access to the slot is an adjusted 16-bit read */
        for(j=0;j<u->count&&ok;++j){
            const LpLine *l=&u->lines[j];size_t m;const char *o=lp_operand(l,&m);long slot,n,k,nk;int end,cost,newcost;
            if(!region[j]||!l->op)continue;
            if(l->call&&!lp_register_call(l)){ok=0;break;}
            if(!(m>=3&&o[m-2]==','&&o[m-1]=='s'))continue;
            slot=(long)sd[j]-slot_depth+1;n=strtol(o,NULL,10);
            if(n+lp_width(l)-1<slot||n>slot+1)continue;
            if(!lp_is(l,"lda")||l->m8||n!=slot){ok=0;break;}
            lp_adjusted_read(u,j,&k,&end,&cost);
            nk=(k-c)&0xFFFF;
            newcost=nk==0?0:(nk<=2||nk>=0xFFFE)?2*(nk<=2?(int)nk:(int)(0x10000-nk)):5;
            if(newcost>cost||(u->lines[end].out&(LP_C|LP_V)&&cost!=newcost)){ok=0;break;}
            gain+=cost-newcost;
        }
        if(!ok||gain<=0)continue;
        lp_set(p,"    pha");
        for(j=0;j<u->count;++j){
            LpLine *l=&u->lines[j];size_t m;const char *o=lp_operand(l,&m);long slot,n,k,nk;int end,cost,e;char text[64];
            if(!region[j]||!l->op||!(m>=3&&o[m-2]==','&&o[m-1]=='s'))continue;
            slot=(long)sd[j]-slot_depth+1;n=strtol(o,NULL,10);
            if(n!=slot||!lp_is(l,"lda"))continue;
            lp_adjusted_read(u,j,&k,&end,&cost);
            nk=(k-c)&0xFFFF;
            for(e=(int)j+1;e<=end;++e)if(u->lines[e].op)u->lines[e].deleted=1;
            text[0]=0;
            if(nk&&(nk<=2||nk>=0xFFFE)){int s,count=nk<=2?(int)nk:(int)(0x10000-nk);
                for(s=0;s<count;++s)strcat(text,nk<=2?"\n    inc a":"\n    dec a");}
            else if(nk)snprintf(text,sizeof text,"\n    clc\n    adc #$%04lX",nk);
            lp_set(l,"%.*s%s",(int)l->length,l->text,text);
        }
        ++changed;
    }
    free(ax);free(sd);free(region);
    return changed;
}
/* "txa / adjust by k" where A already holds X + c: adjust A by k - c instead */
static int lp_ax_reuse(LpUnit *u,Function *f,size_t at)
{
    unsigned i;long *ax;int changed=0;(void)f;(void)at;
    ax=malloc((u->count+1)*sizeof *ax);
    if(!ax){fputs("out of memory emitting assembly\n",stderr);exit(EXIT_FAILURE);}
    lp_liveness(u);lp_accumulator_offsets(u,ax,LP_X);
    for(i=0;i<u->count;++i){
        LpLine *l=&u->lines[i];long k,nk,c=ax[i];int end,cost,newcost,e;char text[64];
        /* A full-width round trip leaves the destination and N/Z unchanged
         * from the first transfer. Reanalyse before removing dead transfers. */
        const char *reverse=lp_line_is(l,"tax")?"txa":lp_line_is(l,"txa")?"tax":
                            lp_line_is(l,"tay")?"tya":lp_line_is(l,"tya")?"tay":NULL;
        if(reverse&&!l->m8&&!l->x8){
            e=lp_next(u,i,-1);
            while(e>=0&&(lp_is(&u->lines[e],"sta")||lp_is(&u->lines[e],"stx")||
                          lp_is(&u->lines[e],"sty")||lp_is(&u->lines[e],"stz")))
                e=lp_next(u,(unsigned)e,-1);
            if(e>=0&&!u->lines[e].m8&&!u->lines[e].x8&&lp_line_is(&u->lines[e],reverse)){
                if(changed)break;
                l->deleted=1;
                changed=1;
                break;
            }
        }
        if(!lp_line_is(l,"txa")||l->m8||l->x8||c<0||l->replace||l->deleted)continue;
        lp_adjusted_read(u,i,&k,&end,&cost);
        nk=(k-c)&0xFFFF;
        newcost=nk==0?0:(nk<=2||nk>=0xFFFE)?2*(nk<=2?(int)nk:(int)(0x10000-nk)):5;
        if(newcost>=cost+2)continue;
        /* N/Z must come out the same (no instruction left to set them), and C/V
         * may differ only where dead. */
        if((!newcost&&u->lines[end].out&(LP_N|LP_Z))||(u->lines[end].out&(LP_C|LP_V)&&cost!=newcost))continue;
        for(e=(int)i+1;e<=end;++e)if(u->lines[e].op)u->lines[e].deleted=1;
        text[0]=0;
        if(nk&&(nk<=2||nk>=0xFFFE)){int s,count=nk<=2?(int)nk:(int)(0x10000-nk);
            for(s=0;s<count;++s)strcat(text,s?(nk<=2?"\n    inc a":"\n    dec a"):(nk<=2?"    inc a":"    dec a"));}
        else if(nk)snprintf(text,sizeof text,"    clc\n    adc #$%04lX",nk);
        if(text[0])lp_set(l,"%s",text);else l->deleted=1;
        ++changed;
    }
    free(ax);
    return changed;
}
/* Run a line pass to a fixed point over the function's text; 1 if it changed anything */
typedef struct { LpUnit parsed; LpLine *work; unsigned capacity; } LpRunner;

static void lp_invalidate(LpRunner *runner)
{
    free(runner->parsed.text);free(runner->parsed.lines);
    runner->parsed.text=NULL;runner->parsed.lines=NULL;
}

/* Commit the low word directly when the high half reads only C objects
 * and disjoint compiler scratch. It uses the carry from the low operation. */
static int lp_store_low_before_high(LpUnit *u,Function *f,size_t at)
{
    (void)at;
    if(u->indirect||cg.lp_volatile||cg.parser->no_value_reuse||body_asm_statements(f->body))return 0;
    lp_liveness(u);
    for(unsigned i=0;i<u->count;++i){
        LpLine *push=&u->lines[i];
        if(!lp_line_is(push,"pha")||push->m8||push->x8)continue;
        int load=lp_next(u,i,1),operate=load<0?-1:lp_next(u,(unsigned)load,1);
        int high=operate<0?-1:lp_next(u,(unsigned)operate,1),pull=high<0?-1:lp_next(u,(unsigned)high,1);
        int low=pull<0?-1:lp_next(u,(unsigned)pull,1);
        if(low<0||!lp_is(&u->lines[load],"lda")||
           (!lp_is(&u->lines[operate],"adc")&&!lp_is(&u->lines[operate],"sbc"))||
           !lp_is(&u->lines[high],"sta")||!lp_line_is(&u->lines[pull],"pla")||
           !lp_is(&u->lines[low],"sta")||(u->lines[low].out&(LP_A|LP_N|LP_Z)))continue;
        size_t load_n,operate_n,high_n,low_n;
        const char *address=lp_operand(&u->lines[load],&load_n);
        const char *rhs=lp_operand(&u->lines[operate],&operate_n);
        const char *high_dst=lp_operand(&u->lines[high],&high_n);
        const char *low_dst=lp_operand(&u->lines[low],&low_n);
        int lo=lp_workspace_word(low_dst,low_n),hi=lp_workspace_word(high_dst,high_n);
        int other=lp_workspace_word(rhs,operate_n),source=lp_workspace_word(address,load_n);
        if(lo<0||hi<0||other<0||lp_overlaps(&u->lines[high],hi,lo)||
           lp_overlaps(&u->lines[operate],other,lo))continue;
        if(source>=0){
            if(lp_overlaps(&u->lines[load],source,lo))continue;
        }else{
            char *end;
            if(load_n!=9||strncmp(address,"a:$",3)||
               (memcmp(address+7,",x",2)&&memcmp(address+7,",y",2)))continue;
            strtoul(address+3,&end,16);
            if(end!=address+7)continue;
        }
        lp_set(push,"    sta %.*s",(int)low_n,low_dst);
        u->lines[pull].deleted=u->lines[low].deleted=1;
        return 1;
    }
    return 0;
}

static int lp_run(LpRunner *runner,Function *f,size_t at,int (*pass)(LpUnit*,Function*,size_t))
{
    unsigned rounds;int any=0;
    for(rounds=0;rounds<64;++rounds){
        LpUnit u;int changed;
        if(!runner->parsed.text)lp_parse(&runner->parsed,cg.assembly+at,cg.length-at);
        u=runner->parsed;
        if(runner->capacity<u.count){
            free(runner->work);
            runner->work=allocate(u.count*sizeof *runner->work);
            runner->capacity=u.count;
        }
        /* Rejected passes can change analysis fields as well as stage edits */
        u.lines=runner->work;
        if(u.count)memcpy(u.lines,runner->parsed.lines,u.count*sizeof *u.lines);
        changed=pass(&u,f,at);
        if(changed)lp_emit(&u,at);
        lp_free_edits(&u);
        if(!changed)break;
        lp_invalidate(runner);
        any=1;
    }
    return any;
}
/* A plain store changes neither A nor N/Z, even for volatile destinations.
 * Keep every store and reuse matching immediate loads within the same run. */
static int lp_reuse_store_immediates(LpUnit *u,Function *f,size_t at)
{
    long value=-1;
    int m8=0,changed=0;
    unsigned i;
    (void)f;(void)at;
    for(i=0;i<u->count;++i){
        LpLine *l=&u->lines[i];
        if(!l->op){
            if(l->length&&l->text[0]!=';')value=-1;
            continue;
        }
        if(lp_is(l,"sta")||lp_is(l,"stx")||lp_is(l,"sty")||lp_is(l,"stz"))continue;
        if(lp_is(l,"lda")){
            long immediate=lp_immediate(l);
            if(immediate>=0&&immediate==value&&l->m8==m8){
                l->deleted=1;
                changed=1;
            }
            value=immediate;
            m8=l->m8;
        }else value=-1;
    }
    return changed;
}
/* Compare a byte before restoring A16 when the widened value and N flag are
 * dead. CMP preserves Z/C for an unsigned byte and an in-range constant. */
static int lp_byte_compare(LpUnit *u,Function *f,size_t at)
{
    unsigned i;int changed=0;(void)f;(void)at;lp_liveness(u);
    for(i=0;i<u->count;++i){
        LpLine *load=&u->lines[i],*restore,*mask,*compare,*branch;int j,k,m,n;long value;
        if(!lp_is(load,"lda")||!load->m8||load->deleted||load->replace)continue;
        j=lp_next(u,i,1);if(j<0||!lp_line_is(&u->lines[j],"rep #$20"))continue;
        k=j+1;
        while((unsigned)k<u->count&&!u->lines[k].op&&
              (!u->lines[k].length||u->lines[k].text[0]==';'||
               (u->lines[k].length==4&&!strncmp(u->lines[k].text,".a16",4))))++k;
        if((unsigned)k>=u->count)continue;
        m=lp_next(u,(unsigned)k,1);n=m>=0?lp_next(u,(unsigned)m,1):-1;
        if(n<0)continue;restore=&u->lines[j];mask=&u->lines[k];compare=&u->lines[m];branch=&u->lines[n];
        if(!lp_is(mask,"and")||lp_immediate(mask)!=255||!lp_is(compare,"cmp")||
           (value=lp_immediate(compare))<0||value>255||!lp_branch(branch)||
           (compare->out&(LP_A|LP_N))||restore->deleted||mask->deleted||compare->deleted)continue;
        restore->deleted=1;compare->deleted=1;
        lp_set(mask,".a8\n    cmp #$%02lX\n    rep #$20\n.a16",value);
        ++changed;
    }return changed;
}
/* Reuse an accumulator already related to two private stack words while
 * materializing a straight-line series of word sums into fixed globals. */
static int lp_stack_sum_series(LpUnit *u,Function *f,size_t at)
{
    unsigned i;int changed=0;(void)f;(void)at;lp_liveness(u);
    for(i=0;i<u->count;++i){
        LpLine *first=&u->lines[i],*second;size_t n1,n2;const char *slot1,*slot2;
        char *end1,*end2;long offset1,offset2;
        int clear,addition,save,pos;long delta,current;
        if(!lp_is(first,"sta")||first->m8||first->deleted||first->replace)continue;
        slot1=lp_operand(first,&n1);
        if(n1<3||slot1[n1-2]!=','||slot1[n1-1]!='s'||!isdigit((unsigned char)slot1[0]))continue;
        clear=lp_next(u,i,1);addition=clear>=0?lp_next(u,(unsigned)clear,1):-1;
        save=addition>=0?lp_next(u,(unsigned)addition,1):-1;
        if(save<0||!lp_line_is(&u->lines[clear],"clc")||!lp_is(&u->lines[addition],"adc")||
           (delta=lp_immediate(&u->lines[addition]))<0||!lp_is(&u->lines[save],"sta"))continue;
        second=&u->lines[save];slot2=lp_operand(second,&n2);
        if(second->m8||n2<3||slot2[n2-2]!=','||slot2[n2-1]!='s'||
           !isdigit((unsigned char)slot2[0]))continue;
        offset1=strtol(slot1,&end1,10);offset2=strtol(slot2,&end2,10);
        if(end1!=slot1+n1-2||end2!=slot2+n2-2||offset1<1||offset2<1||
           offset1>254||offset2>254||labs(offset1-offset2)<2)continue;
        current=delta;pos=lp_next(u,(unsigned)save,1);
        while(pos>=0){
            LpLine *load=&u->lines[pos],*sum,*store;int c,a,t;long literal,desired,adjust;
            size_t m;const char *operand,*destination;
            if(!lp_is(load,"lda")||load->m8||(literal=lp_immediate(load))<0||load->deleted||load->replace)break;
            c=lp_next(u,(unsigned)pos,1);a=c>=0?lp_next(u,(unsigned)c,1):-1;
            t=a>=0?lp_next(u,(unsigned)a,1):-1;if(t<0)break;
            sum=&u->lines[a];store=&u->lines[t];
            if(!lp_line_is(&u->lines[c],"clc")||!lp_is(sum,"adc")||!lp_is(store,"sta")||
               sum->m8||store->m8||(sum->out&(LP_C|LP_V))||sum->deleted||sum->replace||store->deleted)break;
            operand=lp_operand(sum,&m);
            if(m==n1&&!strncmp(operand,slot1,n1))desired=literal;
            else if(m==n2&&!strncmp(operand,slot2,n2))desired=literal+delta;
            else break;
            destination=lp_operand(store,&m);
            if(m<12||strncmp(destination,"a:.loword(_",11))break;
            adjust=(desired-current)&65535;
            lp_set(load,"    clc\n    adc #$%04lX",adjust);u->lines[c].deleted=1;sum->deleted=1;
            current=desired;++changed;pos=lp_next(u,(unsigned)t,1);
        }
        if(changed)break;
    }return changed;
}
/* Reuse word values in A/X within a basic block. Private operands retain their
 * identity only while writes, stack movement and calls cannot invalidate it. */
static int lp_x_store_may_write_slot(const LpLine *l,const Function *f,const char *x,size_t xn,int y_is_frame)
{
    size_t m;const char *p=lp_operand(l,&m);
    if(!lp_may_write(l,x,xn,2))return 0;
    if(l->call||lp_is(l,"mvn")||lp_is(l,"mvp")||l->use==LP_ALL||!lp_store_op(l))return 1;
    if(m<2||p[m-2]!=','||p[m-1]!='x')return 1;
    if(y_is_frame&&xn==9&&!strncmp(x,"a:$",3)&&x[7]==','&&x[8]=='y')
        return lp_frame_slot_escaped(f,(int)strtol(x+3,NULL,16),2);
    if(xn>=3&&x[xn-2]==','&&x[xn-1]=='s'&&!cg.lp_frame_address&&f&&!f->uses_varargs&&!f->aggregate_abi)
        return 0;
    return 1;
}
static int lp_register_values(LpUnit *u,Function *f,size_t at)
{
    char a[128]="",x[128]="",a8[128]="";unsigned i;int changed=0,known_targets;
    unsigned char *targets=lp_local_targets(u,&known_targets);
    int y_is_frame=f&&f->frame>0&&!body_asm_statements(f->body);
    (void)at;
    if(y_is_frame){
        int seen_tay=0;
        for(i=0;i<u->count;++i){
            const LpLine *l=&u->lines[i];
            if(!l->op||!(l->def&LP_Y)||lp_line_is(l,"ply"))continue;
            if(!seen_tay&&lp_line_is(l,"tay")){
                int prev=lp_next(u,i,-1);
                if(prev>=0&&(lp_line_is(&u->lines[prev],"tsc")||lp_line_is(&u->lines[prev],"tcs"))){
                    seen_tay=1;continue;
                }
            }
            y_is_frame=0;break;
        }
    }
    for(i=0;i<u->count;++i)
        if(lp_line_is(&u->lines[i],"sep #$20")||lp_line_is(&u->lines[i],"rep #$20"))
            u->lines[i].use=0;
    lp_liveness(u);
    for(i=0;i<u->count;++i){
        LpLine *l=&u->lines[i];size_t n;const char *o=lp_operand(l,&n);int load_a=lp_is(l,"lda"),load_x=lp_is(l,"ldx");
        if(!l->op){
            /* An untargeted internal label is just the fallthrough edge of
             * a predicate. Other labels may have an independent predecessor. */
            int fallthrough=known_targets&&!targets[i]&&lp_fallthrough_label(l);
            if((l->length==3&&!strncmp(l->text,".a8",3))||
               (l->length==4&&!strncmp(l->text,".a16",4))){a[0]=0;a8[0]=0;}
            else if(!fallthrough&&l->length&&l->text[0]!=';'&&strncmp(l->text,".export",7))a[0]=x[0]=a8[0]=0;
            continue;
        }
        if(l->call||l->x8||l->use==LP_ALL){a[0]=x[0]=a8[0]=0;continue;}
        if(l->m8||lp_line_is(l,"sep #$20")||lp_line_is(l,"rep #$20"))a[0]=0;
        if(!l->m8||lp_line_is(l,"sep #$20")||lp_line_is(l,"rep #$20"))a8[0]=0;
        /* Y can become a promoted value/cursor. A frame operand's spelling
         * alone does not identify the same storage after its base changes. */
        if(l->def&LP_Y){
            if(a[0]&&a[strlen(a)-1]=='y')a[0]=0;
            if(x[0]&&x[strlen(x)-1]=='y')x[0]=0;
            if(a8[0]&&a8[strlen(a8)-1]=='y')a8[0]=0;
        }
        if(a[0]&&(lp_may_write(l,a,strlen(a),2)||(a[strlen(a)-1]=='s'&&lp_stack_op(l))))a[0]=0;
        if(x[0]&&(lp_x_store_may_write_slot(l,f,x,strlen(x),y_is_frame)||(x[strlen(x)-1]=='s'&&lp_stack_op(l))))x[0]=0;
        if(a8[0]&&(lp_may_write(l,a8,strlen(a8),1)||(a8[strlen(a8)-1]=='s'&&lp_stack_op(l))))a8[0]=0;
        if(load_a&&l->m8&&n<sizeof a8&&n&&(o[0]=='#'||lp_private(o,n))){
            if(strlen(a8)==n&&!strncmp(a8,o,n)&&!(l->out&(LP_N|LP_Z))){l->deleted=1;++changed;continue;}
            memcpy(a8,o,n);a8[n]=0;continue;
        }
        if(((load_a&&!l->m8)||load_x)&&n<sizeof a&&n&&(o[0]=='#'||lp_private(o,n))){
            char *key=load_a?a:x;
            if(strlen(key)==n&&!strncmp(key,o,n)&&!(l->out&(LP_N|LP_Z))){l->deleted=1;++changed;continue;}
            {
                const char *other=load_a?x:a;
                if(strlen(other)==n&&!strncmp(other,o,n)){
                    lp_set(l,load_a?"    txa":"    tax");
                    free(targets);
                    return 1;
                }
            }
            memcpy(key,o,n);key[n]=0;continue;
        }
        if(lp_is(l,"sta")&&!l->m8&&n<sizeof a&&n&&lp_private(o,n)){memcpy(a,o,n);a[n]=0;continue;}
        if(lp_is(l,"sta")&&l->m8&&n<sizeof a8&&n&&lp_private(o,n)){memcpy(a8,o,n);a8[n]=0;continue;}
        if(lp_is(l,"stx")&&!l->x8&&n<sizeof x&&n&&lp_private(o,n)){memcpy(x,o,n);x[n]=0;continue;}
        if(lp_is(l,"tax")){memcpy(x,a,sizeof x);continue;}
        if(lp_is(l,"txa")){if(!l->m8)memcpy(a,x,sizeof a);continue;}
        if(l->def&(LP_A|LP_AL)){a[0]=0;a8[0]=0;}if(l->def&LP_X)x[0]=0;
        if(l->ends)a[0]=x[0]=a8[0]=0;
    }
    free(targets);return changed;
}
/* Discover the first scale when the load also supplies an entry test. The
 * fallthrough arm must have no other predecessor and keeps A unchanged.
 * The second scale is still removed only as a straight-line sequence. */
static int lp_scale_after_test(LpUnit *u,unsigned start,const unsigned char *targets)
{
    unsigned i;
    int test=-1;
    for(i=start+1;i<u->count;++i){
        LpLine *l=&u->lines[i];
        if(l->length&&l->text[0]==';')continue;
        if(!targets[i]&&lp_fallthrough_label(l))continue;
        if(test<0&&l->target>=0&&!l->ends&&lp_branch(l)){test=(int)i;continue;}
        /* Before relaxation, the inverted test can skip a long jump */
        if(test>=0&&l->ends&&l->target>=0){
            unsigned skip=(unsigned)u->lines[test].target;
            if(skip==i+1&&targets[skip]==1&&u->lines[skip].length==1&&u->lines[skip].text[0]==':'){
                i=skip;continue;
            }
        }
        return test>=0&&lp_line_is(l,"asl a")?(int)i:-1;
    }
    return -1;
}
/* Keep a scaled array index in X while its source and X are unchanged.
 * Re-emitting TXA can recover the old A/N/Z result, but not ASL's carry. */
static int lp_reuse_scaled_index(LpUnit *u,Function *f,size_t at)
{
    const char *input=NULL;
    size_t input_length=0;
    unsigned i,scale=0,dependencies=0;
    int known_targets;
    unsigned char *targets;
    (void)f;(void)at;
    if(cg.parser->no_value_reuse||u->indirect)return 0;
    targets=lp_local_targets(u,&known_targets);
    lp_liveness(u);
    for(i=0;i<u->count;++i){
        LpLine *l=&u->lines[i];
        size_t length;
        const char *operand=lp_operand(l,&length);
        int from_y=lp_line_is(l,"tya");
        if(!l->op){
            if(!lp_fallthrough_marker(l,i,targets,known_targets))input=NULL;
            continue;
        }
        int stored=lp_is(l,"sta");
        if(!l->m8&&!l->x8&&(from_y||((lp_is(l,"lda")||stored)&&lp_private(operand,length)))){
            int end=lp_next(u,i,1),straight=end>=0&&lp_line_is(&u->lines[end],"asl a");
            unsigned shifts=0;
            if(!straight&&known_targets&&!stored)end=lp_scale_after_test(u,i,targets);
            while(end>=0&&!u->lines[end].m8&&lp_line_is(&u->lines[end],"asl a")){
                ++shifts;end=lp_next(u,(unsigned)end,1);
            }
            if(shifts&&end>=0&&!u->lines[end].x8&&lp_line_is(&u->lines[end],"tax")){
                if(!stored&&straight&&input&&input_length==length&&scale==shifts&&!memcmp(input,operand,length)&&
                   !(u->lines[end].out&LP_C)){
                    unsigned j;
                    if(u->lines[end].out&(LP_A|LP_N|LP_Z))lp_set(l,"    txa");
                    else l->deleted=1;
                    for(j=i+1;j<=(unsigned)end;++j)if(u->lines[j].op)u->lines[j].deleted=1;
                    free(targets);
                    return 1;
                }
                input=operand;input_length=length;scale=shifts;
                dependencies=from_y?LP_Y:lp_index_use(l);
                i=(unsigned)end;
                continue;
            }
        }
        if(l->m8||l->x8||l->call||l->use==LP_ALL||l->ends||lp_branch(l)||
           (l->def&(LP_X|dependencies)))input=NULL;
        else if(input&&input_length&&((lp_may_write(l,input,input_length,2)&&
                !(input[input_length-1]=='s'&&!cg.lp_frame_address&&
                  length>13&&operand[length-2]==','&&operand[length-1]=='x'&&
                  !strncmp(operand,"a:.loword(_",11)&&pr_named(operand,length-2)))||
                (input[input_length-1]=='s'&&lp_stack_op(l))||
                lp_is(l,"tcd")||lp_is(l,"pld")||lp_is(l,"plb")))input=NULL;
    }
    free(targets);
    return 0;
}
/* Retain a word-array displacement in X when a loop already owns the
 * unscaled counter in Y. Updating both registers avoids scaling at each use. */
static int lp_loop_entry_jump(const LpUnit *u,unsigned entry,unsigned head)
{
    unsigned i;
    if(entry>=head||!u->lines[entry].ends||u->lines[entry].target!=(int)head)return 0;
    for(i=entry+1;i<head;++i){
        const LpLine *l=&u->lines[i];
        if(l->length&&!l->label&&l->text[0]!=';')return 0;
    }
    return 1;
}
static int lp_retain_word_index(LpUnit *u,Function *f,size_t at)
{
    unsigned latch;
    const unsigned clobbers=LP_A|LP_X|LP_N|LP_Z|LP_C;
    (void)f;(void)at;
    if(u->indirect||cg.parser->no_register_cursors||cg.parser->no_index_elimination)return 0;
    lp_liveness(u);
    for(latch=0;latch<u->count;++latch){
        LpLine *edge=&u->lines[latch],*head;
        int start=edge->target,entry=-1,step=-1,source=-1,shift=-1,save=-1,valid=1;
        size_t slot_length=0;
        const char *slot=NULL;
        unsigned i;
        if(start<0||(unsigned)start>=latch||edge->call||(edge->out&LP_X))continue;
        head=&u->lines[start];
        if(!lp_fallthrough_label(head)||head->m8||head->x8||
           (head->live&clobbers))continue;
        for(i=0;i<u->count;++i){
            LpLine *l=&u->lines[i];
            if(i<(unsigned)start||i>latch){
                if(l->target>=start&&(unsigned)l->target<=latch){
                    if(entry>=0||!lp_loop_entry_jump(u,i,(unsigned)start)){valid=0;break;}
                    entry=(int)i;
                }
                continue;
            }
            if(!l->op){
                if(l->label&&l->length!=1&&!lp_fallthrough_label(l)){valid=0;break;}
                continue;
            }
            if(l->m8||l->x8||l->call||l->use==LP_ALL){valid=0;break;}
            if(!slot&&(l->def&LP_Y)){
                if(step>=0||(l->out&LP_X)||
                   (!lp_line_is(l,"iny")&&!lp_line_is(l,"dey"))){valid=0;break;}
                step=(int)i;
            }
            if((l->def&LP_X)&&i!=(unsigned)save){valid=0;break;}
            if(source<0&&(lp_line_is(l,"tya")||lp_is(l,"lda"))){
                int a=lp_next(u,i,1),x=a<0?-1:lp_next(u,(unsigned)a,1);
                size_t length;
                const char *operand=lp_operand(l,&length);
                if(x>=0&&(unsigned)x<latch&&lp_line_is(&u->lines[a],"asl a")&&
                   lp_line_is(&u->lines[x],"tax")&&
                   (lp_line_is(l,"tya")||lp_workspace_word(operand,length)>=0)&&
                   !(u->lines[x].out&(LP_A|LP_N|LP_Z|LP_C))){
                    source=(int)i;shift=a;save=x;
                    if(length){slot=operand;slot_length=length;}
                }
            }
        }
        if(valid&&slot){
            if(step>=0)continue;
            for(i=(unsigned)start;i<latch;++i){
                LpLine *l=&u->lines[i];
                if(!l->op)continue;
                if((source>(int)i&&lp_branch(l))||
                   (l->target>=0&&l->target<=start)||
                   lp_is(l,"tcd")||lp_is(l,"pld")){valid=0;break;}
                if(!lp_may_write(l,slot,slot_length,2))continue;
                if(step>=0||i<=(unsigned)save||(l->out&LP_X)||
                   (!lp_is(l,"inc")&&!lp_is(l,"dec"))||
                   !lp_operand_is(l,slot,slot_length)){valid=0;break;}
                step=(int)i;
            }
            if(step>=0)for(i=(unsigned)start;i<(unsigned)step;++i)
                if(u->lines[i].target>step){valid=0;break;}
        }
        if(!valid||save<0||step<0)continue;
        /* Fall through the seed when the original entry skipped only labels */
        if(entry>=0)u->lines[entry].deleted=1;
        if(slot){
            char seed[96];
            snprintf(seed,sizeof seed,"    lda %.*s\n    asl a\n    tax\n",(int)slot_length,slot);
            lp_insert(head,seed);
        }else lp_insert(head,"    tya\n    asl a\n    tax\n");
        lp_insert(&u->lines[step],lp_is(&u->lines[step],"iny")||lp_is(&u->lines[step],"inc")?
                  "    inx\n    inx\n":"    dex\n    dex\n");
        u->lines[source].deleted=u->lines[shift].deleted=u->lines[save].deleted=1;
        return 1;
    }
    return 0;
}
/* Reassociate consecutive immediate adds/subs only when their intermediate carry
 * and final carry/overflow have no users. N/Z reflect the same modulo sum. */
static int lp_nz_matches_a16(const LpUnit *u,unsigned before)
{
    int prev=lp_next(u,before,-1);
    const LpLine *p;
    if(prev<0)return 0;
    p=&u->lines[prev];
    return !p->m8&&!p->call&&!lp_line_is(p,"xba")&&(p->def&(LP_A|LP_N|LP_Z))==(LP_A|LP_N|LP_Z);
}
static int lp_add_constants(LpUnit *u,Function *f,size_t at)
{
    unsigned i;(void)f;(void)at;lp_liveness(u);
    for(i=0;i<u->count;++i){int a,b,c,sub1,sub2;long x,y;LpLine *l=&u->lines[i];
        if(l->deleted||l->replace)continue;
        if(!l->m8&&!(l->out&(LP_N|LP_Z))&&
           (((lp_is(l,"ora")||lp_is(l,"eor"))&&lp_immediate(l)==0)||(lp_is(l,"and")&&lp_immediate(l)==65535))){
            l->deleted=1;return 1;
        }
        if(!l->m8&&(((lp_is(l,"ora")||lp_is(l,"eor"))&&lp_immediate(l)==0)||(lp_is(l,"and")&&lp_immediate(l)==65535))&&
           lp_nz_matches_a16(u,i)){
            l->deleted=1;return 1;
        }
        sub1=lp_line_is(l,"sec");
        if((!sub1&&!lp_line_is(l,"clc"))||(a=lp_next(u,i,1))<0||
           !lp_is(&u->lines[a],sub1?"sbc":"adc")||u->lines[a].m8||(x=lp_immediate(&u->lines[a]))<0)continue;
        if((b=lp_next(u,(unsigned)a,1))>=0&&(c=lp_next(u,(unsigned)b,1))>=0){
            sub2=lp_line_is(&u->lines[b],"sec");
            if((sub2||lp_line_is(&u->lines[b],"clc"))&&lp_is(&u->lines[c],sub2?"sbc":"adc")&&
               !u->lines[c].m8&&(y=lp_immediate(&u->lines[c]))>=0&&!(u->lines[c].out&(LP_C|LP_V))){
                unsigned delta=((sub1?(unsigned)(-x): (unsigned)x)+(sub2?(unsigned)(-y):(unsigned)y))&65535u;
                if(!delta){
                    l->deleted=u->lines[b].deleted=u->lines[c].deleted=1;
                    if(!(u->lines[c].out&(LP_N|LP_Z))||lp_nz_matches_a16(u,i))u->lines[a].deleted=1;
                    else lp_set(&u->lines[a],"    ora #$0000");
                    return 1;
                }
                if(delta>=65534u||(sub1&&sub2&&delta>=32768u)){
                    lp_set(l,"    sec");lp_set(&u->lines[a],"    sbc #$%04X",(65536u-delta)&65535u);
                }else{
                    lp_set(l,"    clc");lp_set(&u->lines[a],"    adc #$%04X",delta);
                }
                u->lines[b].deleted=u->lines[c].deleted=1;return 1;
            }
        }
        if(!x&&!(u->lines[a].out&(LP_C|LP_V))){
            if(!(u->lines[a].out&(LP_N|LP_Z))||lp_nz_matches_a16(u,i)){
                l->deleted=u->lines[a].deleted=1;return 1;
            }
            l->deleted=1;lp_set(&u->lines[a],"    ora #$0000");return 1;
        }
    }return 0;
}
/* With carry-in clear, (a + b) modulo 65536 is below b exactly
 * when ADC sets carry. The repeated operand is compiler scratch. */
static int lp_add_overflow_branch(LpUnit *u,Function *f,size_t at)
{
    unsigned i;
    (void)f;(void)at;
    lp_liveness(u);
    for(i=0;i<u->count;++i){
        LpLine *add=&u->lines[i],*compare,*branch;
        int clear,test,edge;
        size_t n;
        const char *operand=lp_operand(add,&n);
        if(!lp_is(add,"adc")||add->m8||lp_workspace_word(operand,n)<0||
           (clear=lp_next(u,i,-1))<0||!lp_line_is(&u->lines[clear],"clc")||
           (test=lp_next(u,i,1))<0)continue;
        compare=&u->lines[test];
        if(!lp_is(compare,"cmp")||compare->m8||!lp_operand_is(compare,operand,n)||
           (compare->out&(LP_N|LP_Z))||(edge=lp_next(u,(unsigned)test,1))<0)continue;
        branch=&u->lines[edge];
        if(branch->target<0||(branch->out&LP_C)||(!lp_is(branch,"bcc")&&!lp_is(branch,"bcs")))continue;
        lp_set(branch,"    %s%.*s",lp_is(branch,"bcc")?"bcs":"bcc",(int)branch->length-7,branch->op+3);
        compare->deleted=1;
        return 1;
    }
    return 0;
}
static Symbol *lp_callee(const LpLine *call);
typedef struct { unsigned char seen,frame,count,stack[64]; } PrState;
static PrState *pr_states(LpUnit *u);
#include "private_values.inc"
#include "private_regions.inc"
#include "accumulator_cfg.inc"
/* Propagate a later low-bit demand through modular immediate arithmetic.
 * Control flow, memory observations and live arithmetic flags are barriers. */
typedef struct { char name[64]; unsigned zero,ones; } LpKnownSlot;
static void lp_known_invalidate(LpKnownSlot *slots,unsigned *nslots,const LpLine *l)
{
    unsigned k=0;
    while(k<*nslots){
        size_t len=strlen(slots[k].name);
        if(lp_may_write(l,slots[k].name,len,2)||
           (slots[k].name[len-1]=='y'&&(l->def&LP_Y))||
           (slots[k].name[len-1]=='s'&&lp_stack_op(l)))
            slots[k]=slots[--*nslots];
        else ++k;
    }
}
static void lp_known_record(LpKnownSlot *slots,unsigned *nslots,const LpLine *l,unsigned zero,unsigned ones)
{
    size_t n;const char *o=lp_operand(l,&n);
    lp_known_invalidate(slots,nslots,l);
    if(n>=sizeof slots[0].name||!lp_private(o,n)||*nslots>=16)return;
    LpKnownSlot *slot=&slots[(*nslots)++];
    memcpy(slot->name,o,n);slot->name[n]=0;slot->zero=zero;slot->ones=ones;
}
/* Eliminate redundant bit masks via backward demand and forward known-zero tracking */
static int lp_bits_dead_after(LpUnit *u,unsigned start,unsigned bits,int low_ok,
                               const unsigned char *targets,int known_targets)
{
    int k=(int)start;
    while((unsigned)++k<u->count){LpLine *p=&u->lines[k];long n;
        if(p->deleted)continue;
        if(p->replace)break;
        if(!p->op){
            if(!p->length)break;
            if(p->text[0]==';'||(p->length==3&&!strncmp(p->text,".a8",3))||
               (p->length==4&&!strncmp(p->text,".a16",4))||
               (known_targets&&!targets[k]&&lp_fallthrough_label(p)))continue;
            break;
        }
        if(!p->x8&&!(p->def&LP_A)&&!(p->use&LP_A)&&
           (lp_is(p,"ldx")||lp_is(p,"ldy")||lp_line_is(p,"plx")||lp_line_is(p,"ply")))continue;
        if(p->m8){
            if(!(bits&0x00FFu)&&(lp_is(p,"sta")||lp_is(p,"cmp")||lp_is(p,"bit")||
               lp_is(p,"and")||lp_is(p,"ora")||lp_is(p,"eor")||lp_is(p,"adc")||lp_is(p,"sbc")||
               lp_line_is(p,"inc a")||lp_line_is(p,"dec a")||lp_line_is(p,"asl a")||
               lp_line_is(p,"lsr a")||lp_line_is(p,"rol a")||lp_line_is(p,"ror a"))){
                if(!(p->out&LP_A))return 1;
                continue;
            }
            break;
        }
        if(lp_line_is(p,"sep #$20")||lp_line_is(p,"rep #$20")||
           lp_line_is(p,"clc")||lp_line_is(p,"sec"))continue;
        if(lp_is(p,"and")&&(n=lp_immediate(p))>=0){
            bits&=(unsigned)n;
            if(!bits)return 1;
            if(p->out&(LP_N|LP_Z))break;
        }else if(lp_is(p,"ora")&&(n=lp_immediate(p))>=0&&!(p->out&(LP_N|LP_Z))){
            bits&=~(unsigned)n;
            if(!bits)return 1;
        }else if(lp_is(p,"eor")&&lp_immediate(p)>=0&&!(p->out&(LP_N|LP_Z))){
        }else if(lp_line_is(p,"xba")&&!(p->out&(LP_N|LP_Z))){
            bits=((bits>>8)|(bits<<8))&0xFFFFu;low_ok=0;
        }else if(lp_line_is(p,"asl a")&&!(p->out&(LP_C|LP_N|LP_Z))){
            bits=(bits<<1)&0xFFFFu;low_ok=0;
            if(!bits)return 1;
        }else if(lp_line_is(p,"lsr a")&&!(p->out&(LP_C|LP_N|LP_Z))){
            bits=(bits>>1)&0xFFFFu;low_ok=0;
            if(!bits)return 1;
        }else if(low_ok&&(lp_is(p,"adc")||lp_is(p,"sbc"))&&lp_immediate(p)>=0&&!(p->out&LP_FLAGS)){
        }else break;
    }
    return 0;
}
/* If A is copied to an index, both consumers must discard every bit the
 * original mask cleared. Reject any other observation of the saved index. */
static int lp_masked_index_copy(LpUnit *u,unsigned transfer,unsigned bits,int low_ok,
                                const unsigned char *targets,int known_targets)
{
    LpLine *copy=&u->lines[transfer];int x=lp_line_is(copy,"tax");
    unsigned reg=x?LP_X:LP_Y;
    if((!x&&!lp_line_is(copy,"tay"))||copy->m8||copy->x8||
       (copy->out&(LP_N|LP_Z))||!lp_bits_dead_after(u,transfer,bits,low_ok,targets,known_targets))return 0;
    for(int k=(int)transfer;(k=lp_next(u,(unsigned)k,1))>=0;){
        LpLine *l=&u->lines[k];
        if(l->m8||l->x8||l->ends||l->call||lp_branch(l)||l->replace||l->deleted)return 0;
        if(lp_line_is(l,x?"txa":"tya"))return !(l->out&(reg|LP_Z|LP_N))&&
            lp_bits_dead_after(u,(unsigned)k,bits,low_ok,targets,known_targets);
        if((l->use|l->def)&reg)return 0;
    }
    return 0;
}
/* Only the negative half of a masked value needs high sign bits */
static int lp_sign_extension_branch(LpUnit *u,Function *f,size_t at)
{
    (void)at;
    if(body_asm_statements(f->body))return 0;
    lp_liveness(u);
    for(unsigned i=0;i<u->count;++i){
        LpLine *mask=&u->lines[i];
        if(!lp_is(mask,"and")||mask->m8)continue;
        long bits=lp_immediate(mask);
        if(bits<3||bits>=32768||(bits&(bits+1)))continue;
        int bias=lp_next(u,i,1);
        int carry=bias<0?-1:lp_next(u,(unsigned)bias,1);
        int sub=carry<0?-1:lp_next(u,(unsigned)carry,1);
        long sign=(bits+1)/2;
        if(sub<0||!lp_is(&u->lines[bias],"eor")||lp_immediate(&u->lines[bias])!=sign||
           !lp_line_is(&u->lines[carry],"sec")||!lp_is(&u->lines[sub],"sbc")||
           lp_immediate(&u->lines[sub])!=sign||u->lines[sub].out&LP_FLAGS)continue;
        unsigned label=++cg.label;
        lp_set(&u->lines[bias],"    cmp #$%04lX\n    bcc cg_%s_%u",sign,cg.parser->unit,label);
        u->lines[carry].deleted=1;
        lp_set(&u->lines[sub],"    ora #$%04lX\ncg_%s_%u = *",
               65535-bits,cg.parser->unit,label);
        return 1;
    }
    return 0;
}

static int lp_demanded_masks(LpUnit *u,Function *f,size_t at)
{
    unsigned i,zero_a=0,ones_a=0,nslots=0;int changed=0,known=0,known_targets;
    int private_stack=!cg.lp_frame_address&&!u->indirect&&!body_asm_statements(f->body);
    LpKnownSlot slots[16];
    unsigned char *targets=lp_local_targets(u,&known_targets);
    (void)at;lp_liveness(u);
    for(i=0;i<u->count;++i){LpLine *l=&u->lines[i];long mask;int k;
        if(l->deleted||l->replace)continue;
        /* A byte load already sets Z from exactly the bits in a later
         * word mask. REP changes M without disturbing that result. */
        if(i>=3&&!l->m8&&lp_is(l,"and")&&lp_immediate(l)==255&&
           !(l->out&(LP_AH|LP_N))&&u->lines[i-1].length==4&&
           !strncmp(u->lines[i-1].text,".a16",4)&&lp_line_is(&u->lines[i-2],"rep #$20")){
            int load=lp_next(u,i-2,-1);
            if(load>=0&&u->lines[load].m8&&lp_is(&u->lines[load],"lda")){
                l->deleted=1;++changed;continue;
            }
        }
        if(lp_is(l,"ora")&&lp_immediate(l)==0&&!(l->out&(LP_N|LP_Z))){l->deleted=1;++changed;continue;}
        if(lp_is(l,"eor")&&!l->m8&&(mask=lp_immediate(l))>0&&(mask&0x00FF)==0){
            int k1=lp_next(u,i,1),k2=k1<0?-1:lp_next(u,(unsigned)k1,1);
            if(k2>=0&&!u->lines[k1].label&&!u->lines[k2].label&&
               !u->lines[k1].replace&&!u->lines[k2].replace&&
               lp_line_is(&u->lines[k1],"sec")&&lp_is(&u->lines[k2],"sbc")&&
               !u->lines[k2].m8&&lp_immediate(&u->lines[k2])==mask&&
               !(u->lines[k2].out&LP_FLAGS)){
                unsigned low=(unsigned)mask&(0u-(unsigned)mask);
                unsigned bits=(~(low-1u))&0xFFFFu;
                if(lp_bits_dead_after(u,(unsigned)k2,bits,1,targets,known_targets)){
                    l->deleted=u->lines[k1].deleted=u->lines[k2].deleted=1;++changed;continue;
                }
            }
        }
        if(!lp_is(l,"and")||l->m8||(mask=lp_immediate(l))<0||l->out&(LP_N|LP_Z))continue;
        k=lp_next(u,i,1);
        if(k>=0&&!u->lines[k].m8&&!u->lines[k].deleted&&!u->lines[k].replace&&
           lp_is(&u->lines[k],"and")&&lp_immediate(&u->lines[k])>=0){
            long m2=lp_immediate(&u->lines[k]);
            lp_set(&u->lines[k],"    and #$%04lX",(unsigned)(mask&m2)&0xFFFFu);
            l->deleted=1;++changed;continue;
        }
        {   unsigned bits=(~(unsigned)mask)&0xFFFFu;int low_ok=!(mask&(mask+1));
            if(lp_bits_dead_after(u,i,bits,low_ok,targets,known_targets)||
               (k>=0&&lp_masked_index_copy(u,(unsigned)k,bits,low_ok,targets,known_targets))){
                l->deleted=1;++changed;
            }
        }
    }
    if(changed){free(targets);return changed;}
    /* Forward pass: drop AND #imm that only clears already-zero bits */
    for(i=0;i<u->count;++i){
        LpLine *l=&u->lines[i];size_t n;const char *o=lp_operand(l,&n);long imm;
        if(l->deleted||l->replace)continue;
        if(!l->op){
            int fallthrough=known_targets&&!targets[i]&&
                (lp_fallthrough_label(l)||(l->label&&l->length==1&&l->text[0]==':'));
            if((l->length==3&&!strncmp(l->text,".a8",3))||(l->length==4&&!strncmp(l->text,".a16",4)))known=0;
            else if(!fallthrough&&l->length&&l->text[0]!=';'&&strncmp(l->text,".export",7)){known=0;nslots=0;}
            continue;
        }
        if(known_targets&&i+2<u->count&&lp_branch(l)&&l->target==(int)(i+2)&&
           !u->lines[i+1].deleted&&u->lines[i+1].ends&&!u->lines[i+1].label&&
           targets[i+2]==1&&u->lines[i+2].label){
            i+=2;continue;
        }
        if(l->call&&!l->x8&&private_stack&&lp_callee(l)){
            unsigned k=0;
            /* A call returns to the same S and cannot name a private slot */
            while(k<nslots){
                if(slots[k].name[strlen(slots[k].name)-1]=='s')++k;
                else slots[k]=slots[--nslots];
            }
            known=0;continue;
        }
        if(l->call||l->x8||(l->use==LP_ALL&&!lp_line_is(l,"sep #$20")&&!lp_line_is(l,"rep #$20"))){
            known=0;nslots=0;continue;
        }
        if(lp_line_is(l,"sep #$20")||lp_line_is(l,"rep #$20")){known=0;continue;}
        if(l->m8){
            lp_known_invalidate(slots,&nslots,l);
            known=0;if(l->ends)nslots=0;
            continue;
        }
        if(known&&lp_is(l,"and")&&(imm=lp_immediate(l))>=0){
            unsigned mask=(unsigned)imm&0xFFFFu;
            if(!(mask&~(zero_a|ones_a))){
                lp_set(l,"    lda #$%04X",mask&ones_a);
                free(targets);return changed+1;
            }
            if(!((~zero_a&0xFFFFu)&~mask)&&!(l->out&(LP_N|LP_Z))){l->deleted=1;++changed;continue;}
        }
        if(lp_is(l,"lda")){
            lp_known_invalidate(slots,&nslots,l);
            if((imm=lp_immediate(l))>=0){known=1;zero_a=(~(unsigned)imm)&0xFFFFu;ones_a=(unsigned)imm&0xFFFFu;}
            else{
                unsigned k;known=0;ones_a=0;
                if(n<sizeof slots[0].name&&lp_private(o,n))
                    for(k=0;k<nslots;++k)
                        if(strlen(slots[k].name)==n&&!strncmp(slots[k].name,o,n)){
                            known=1;zero_a=slots[k].zero;ones_a=slots[k].ones;break;
                        }
            }
        }else if(lp_is(l,"and")&&(imm=lp_immediate(l))>=0){
            if(!known){zero_a=0;ones_a=0;}
            known=1;zero_a|=(~(unsigned)imm)&0xFFFFu;ones_a&=(unsigned)imm&0xFFFFu;
        }else if(lp_is(l,"ora")&&(imm=lp_immediate(l))>=0){
            if(!known){known=1;zero_a=0;ones_a=0;}
            zero_a&=(~(unsigned)imm)&0xFFFFu;ones_a|=(unsigned)imm&0xFFFFu;
        }else if(lp_is(l,"eor")&&(imm=lp_immediate(l))>=0){
            if(known){
                unsigned nz=(zero_a&~(unsigned)imm)|(ones_a&(unsigned)imm);
                unsigned no=(ones_a&~(unsigned)imm)|(zero_a&(unsigned)imm);
                zero_a=nz;ones_a=no;
            }
        }else if(lp_line_is(l,"xba")){
            if(known){zero_a=((zero_a>>8)|(zero_a<<8))&0xFFFFu;ones_a=((ones_a>>8)|(ones_a<<8))&0xFFFFu;}
        }else if(lp_line_is(l,"asl a")){
            if(known){zero_a=((zero_a<<1)|1u)&0xFFFFu;ones_a=(ones_a<<1)&0xFFFFu;}
        }else if(lp_line_is(l,"lsr a")){
            if(known){zero_a=((zero_a>>1)|0x8000u)&0xFFFFu;ones_a=(ones_a>>1)&0xFFFFu;}
        }else if(lp_is(l,"sta")){
            if(known)lp_known_record(slots,&nslots,l,zero_a,ones_a);
            else lp_known_invalidate(slots,&nslots,l);
        }else if(lp_is(l,"stz")){
            lp_known_record(slots,&nslots,l,0xFFFFu,0);
        }else{
            lp_known_invalidate(slots,&nslots,l);
            if(l->def&LP_A)known=0;
        }
        if(l->ends){known=0;nslots=0;}
    }
    free(targets);
    return changed;
}
static int lp_m_invariant_op(const LpLine *l)
{
    return l->op&&!l->deleted&&!l->replace&&!l->x8&&
           (lp_is(l,"ldx")||lp_is(l,"ldy")||lp_is(l,"stx")||lp_is(l,"sty")||
            lp_is(l,"cpx")||lp_is(l,"cpy")||lp_is(l,"inx")||lp_is(l,"dex")||
            lp_is(l,"iny")||lp_is(l,"dey")||lp_is(l,"phx")||lp_is(l,"phy")||
            lp_is(l,"plx")||lp_is(l,"ply")||lp_is(l,"txy")||lp_is(l,"tyx")||
            lp_is(l,"clc")||lp_is(l,"sec")||lp_is(l,"clv")||lp_is(l,"nop")||
            lp_is(l,"pea"));
}
static int lp_m_invariant(const LpLine *l)
{
    return !l->m8&&lp_m_invariant_op(l);
}
static int lp_operand_has_s(const char *o,size_t n)
{
    size_t k;
    for(k=0;k+1<n;++k)if(o[k]==','&&o[k+1]=='s')return 1;
    return 0;
}
static int lp_is_mmio_operand(const char *o,size_t n)
{
    size_t k;
    const char *p=o;
    char *end;
    unsigned long addr;
    if(!n||o[0]=='#'||o[0]=='('||o[0]=='['||lp_operand_has_s(o,n))return 1;
    for(k=0;k<n;++k)if(o[k]=='_')return 0;
    if((p[0]=='a'||p[0]=='f'||p[0]=='z')&&p[1]==':'&&p[2]=='$')p+=3;
    else if(p[0]=='$')p+=1;
    else return 1;
    addr=strtoul(p,&end,16);
    if(end==p)return 1;
    addr&=0xFFFFul;
    return addr>=0x2000ul&&addr<0x6000ul;
}
/* Track the hardware M flag over internal branches. Assembler width
 * annotations describe operand encoding and stay in the output. */
static int lp_known_accumulator_mode(LpUnit *u,Function *f,size_t at)
{
    unsigned char *out;
    int again=1,changed=0;
    (void)at;
    if(!u->count||u->indirect||f->symbol->interrupt||body_asm_statements(f->body))return 0;
    out=allocate(u->count*sizeof *out);
    while(again){
        again=0;
        for(unsigned i=0;i<u->count;++i){
            LpLine *l=&u->lines[i];
            /* Ordinary compiler entry follows the A16 calling convention */
            unsigned in=i?(u->lines[i-1].ends?0:out[i-1]):1;
            for(int edge=l->first_incoming;edge>=0;edge=u->lines[edge].next_incoming)in|=out[edge];
            if(!in)continue;
            unsigned mode=in;
            if(lp_line_is(l,"rep #$20"))mode=1;
            else if(lp_line_is(l,"sep #$20"))mode=2;
            else if(l->call||(l->op&&(l->use==LP_ALL||lp_is(l,"plp")||lp_is(l,"xce")||
                    lp_is(l,"rep")||lp_is(l,"sep"))))mode=3;
            if(out[i]!=mode){out[i]=(unsigned char)mode;again=1;}
        }
    }
    for(unsigned i=1;i<u->count;++i){
        LpLine *l=&u->lines[i];
        if(!u->lines[i-1].ends&&((out[i-1]==1&&lp_line_is(l,"rep #$20"))||
                                 (out[i-1]==2&&lp_line_is(l,"sep #$20")))){
            l->deleted=1;++changed;
        }
    }
    free(out);return changed;
}
static int lp_frame_byte_private(Function *f,unsigned byte);

static int lp_byte_test_branch(const LpUnit *u,unsigned restore,int taken_when_equal,
                               int *after,int *edge)
{
    if(!lp_line_is(&u->lines[restore],"rep #$20")||restore+1>=u->count||
       u->lines[restore+1].length!=4||strncmp(u->lines[restore+1].text,".a16",4))return -1;
    int compare=lp_next(u,restore,-1);
    if(compare<0||!u->lines[compare].m8||!lp_is(&u->lines[compare],"cmp")||
       lp_immediate(&u->lines[compare])<0)return -1;
    int branch=lp_next_mode(u,restore);
    int target=lp_cond_branch_target(u,branch,after);
    if(target<0||!lp_is(&u->lines[branch],(taken_when_equal==(*after==branch))?"beq":"bne"))return -1;
    *edge=*after==branch?branch:branch+1;
    return target;
}

/* Find the first instruction after a join with just one branch and
 * its contiguous fallthrough. The first op must follow the target label. */
static int lp_byte_test_join(const LpUnit *u,int from,int target,int edge)
{
    for(int i=from;(unsigned)i<u->count;++i){
        const LpLine *line=&u->lines[i];
        if(line->op)return i>target?i:-1;
        if(!line->length||line->text[0]==';')continue;
        if(!lp_fallthrough_label(line)||
           line->first_incoming!=(i==target?edge:-1)||
           (i==target&&u->lines[edge].next_incoming>=0))break;
    }
    return -1;
}

/* Keep byte mode on both outcomes of the test until the cursor advance
 * needs word mode. The pretest and latch join only at those two points. */
static int lp_byte_loop_test_exits(LpUnit *u,Function *f,size_t at)
{
    (void)at;
    if(u->indirect||cg.parser->no_byte_shuffles||body_asm_statements(f->body))return 0;
    for(unsigned first=0;first<u->count;++first){
        int entry_after,entry_edge;
        int exit=lp_byte_test_branch(u,first,0,&entry_after,&entry_edge);
        if(exit<0||exit<=entry_after||(unsigned)(exit-entry_after)>96)continue;
        for(int latch=entry_after+1;latch<exit;++latch){
            int latch_after,latch_edge;
            int head=lp_byte_test_branch(u,(unsigned)latch,1,&latch_after,&latch_edge);
            if(head<=entry_after||head>=latch||latch_after>=exit)continue;
            int step=lp_byte_test_join(u,entry_after+1,head,latch_edge);
            int narrow=lp_byte_test_join(u,latch_after+1,exit,entry_edge);
            if(step<0||step>=latch||narrow<0||!lp_line_is(&u->lines[narrow],"sep #$20")||
               (unsigned)narrow+1>=u->count||u->lines[narrow+1].length!=3||
               strncmp(u->lines[narrow+1].text,".a8",3))continue;
            lp_insert(&u->lines[step],"    rep #$20\n.a16\n");
            u->lines[first].deleted=u->lines[first+1].deleted=1;
            u->lines[latch].deleted=u->lines[latch+1].deleted=u->lines[narrow].deleted=1;
            return 1;
        }
    }
    return 0;
}

static int lp_frame_indexed_offset(const LpLine *line,int index)
{
    size_t n;
    const char *p=lp_operand(line,&n);
    if(n!=9||strncmp(p,"a:$",3)||p[7]!=','||p[8]!=index)return -1;
    char *end;
    long offset=strtol(p+3,&end,16);
    return end==p+7&&offset>=0&&offset<=65535?(int)offset:-1;
}

static int lp_previous_frame_index_transfer(const LpUnit *u,int before)
{
    for(int i=before;(i=lp_next(u,(unsigned)i,-1))>=0;){
        const LpLine *line=&u->lines[i];
        if(lp_line_is(line,"tax")&&!line->m8&&!line->x8)return i;
        if((line->def&(LP_X|LP_Y))||line->use==LP_ALL||line->call||
           line->ends||lp_branch(line))break;
    }
    return -1;
}

static int lp_remove_equal_frame_compare(LpUnit *u,int compare)
{
    int branch=lp_next(u,(unsigned)compare,1),after=-1;
    if(branch<0||lp_cond_branch_target(u,branch,&after)<0||
       !lp_is(&u->lines[branch],after==branch?"bne":"beq"))return 0;
    unsigned live=after==branch?u->lines[branch].out:u->lines[after].live;
    if(live&(LP_C|LP_N|LP_Z))return 0;
    u->lines[compare].deleted=u->lines[branch].deleted=1;
    if(after!=branch)u->lines[branch+1].deleted=1;
    return 1;
}

/* Only direct, disjoint frame stores can intervene in this snapshot */
static int lp_previous_frame_word_store(const LpUnit *u,int before,int slot)
{
    for(int i=before;i-->0;){
        const LpLine *line=&u->lines[i];
        if(!line->op){
            if(!line->length||line->text[0]==';'||!strncmp(line->text,".export __inlined_",18)||
               (lp_fallthrough_label(line)&&line->first_incoming<0))continue;
            break;
        }
        if(line->x8||line->use==LP_ALL||(line->def&LP_Y)||lp_stack_op(line)||
           line->ends||lp_branch(line))break;
        if(!lp_store_op(line)||lp_operand_is(line,"a",1))continue;
        int other=lp_frame_indexed_offset(line,'y');
        if(other<0)break;
        if(lp_overlaps(line,other,slot))
            return other==slot&&!line->m8&&lp_is(line,"sta")?i:-1;
    }
    return -1;
}

/* A frame pointer stored back after an increment is still a known
 * offset from Y. The comparison can use the two offsets directly. */
static int lp_compare_saved_frame_offset(LpUnit *u,Function *f,size_t at)
{
    (void)at;
    if(u->indirect||cg.lp_volatile||cg.parser->no_private_regions||
       cg.parser->no_value_reuse||body_asm_statements(f->body))return 0;
    long *offsets=NULL;
    PrState *frames=NULL;
    int changed=0;
    for(unsigned i=0;i<u->count;++i){
        LpLine *compare=&u->lines[i];
        if(compare->m8||compare->x8||!lp_is(compare,"cmp"))continue;
        int slot=lp_frame_indexed_offset(compare,'y');
        if(slot<=0||(unsigned)(slot+1)>f->slots)continue;
        int store=lp_previous_frame_word_store(u,(int)i,slot);
        if(store<0)continue;
        int load=store,delta=0;
        while((load=lp_next(u,(unsigned)load,-1))>=0){
            LpLine *step=&u->lines[load];
            if(step->m8||(!lp_line_is(step,"inc a")&&!lp_line_is(step,"dec a")))break;
            delta+=lp_is(step,"inc")?1:-1;
        }
        if(load<0||!delta||u->lines[load].m8||!lp_is(&u->lines[load],"lda")||
           lp_frame_indexed_offset(&u->lines[load],'y')!=slot)continue;
        int initial=lp_previous_frame_word_store(u,load,slot);
        if(initial<0)continue;
        if(!offsets){
            offsets=allocate(u->count*sizeof *offsets);
            lp_accumulator_offsets(u,offsets,LP_Y);
            frames=pr_states(u);
            lp_liveness(u);
        }
        if(offsets[initial]<0||offsets[i]<0||((offsets[initial]+delta)&65535)!=offsets[i]||
           !frames[initial].frame||!frames[i].frame)continue;
        if(lp_remove_equal_frame_compare(u,(int)i)){changed=1;break;}
    }
    free(offsets);
    free(frames);
    return changed;
}

/* X can refer to a different stack slot than the word just saved in Y.
 * Clearing that slot leaves the accumulator and its saved copy equal. */
static int lp_compare_past_frame_clear(LpUnit *u,Function *f,size_t at)
{
    (void)at;
    if(u->indirect||cg.lp_volatile||cg.parser->no_private_regions||
       cg.parser->no_value_reuse||body_asm_statements(f->body))return 0;
    long *offsets=NULL;
    PrState *frames=NULL;
    int changed=0;
    for(unsigned i=0;i<u->count;++i){
        LpLine *clear=&u->lines[i];
        if(clear->m8||clear->x8||!lp_is(clear,"stz")||lp_frame_indexed_offset(clear,'x')!=0)continue;
        int store=lp_next(u,i,-1),compare=lp_next(u,i,1);
        if(store<0||compare<0||!lp_is(&u->lines[store],"sta")||
           !lp_is(&u->lines[compare],"cmp")||u->lines[store].m8||u->lines[compare].m8)continue;
        int slot=lp_frame_indexed_offset(&u->lines[store],'y');
        if(slot<=0||(unsigned)(slot+1)>f->slots||lp_frame_indexed_offset(&u->lines[compare],'y')!=slot)continue;
        int transfer=lp_previous_frame_index_transfer(u,store);
        if(transfer<0)continue;
        if(!offsets){
            offsets=allocate(u->count*sizeof *offsets);
            lp_accumulator_offsets(u,offsets,LP_Y);
            frames=pr_states(u);
            lp_liveness(u);
        }
        long cleared=offsets[transfer];
        if(cleared<=0||(unsigned long)(cleared+1)>f->slots||labs(cleared-slot)<2||
           !frames[transfer].frame||!frames[i].frame)continue;
        if(lp_remove_equal_frame_compare(u,compare)){changed=1;break;}
    }
    free(offsets);
    free(frames);
    return changed;
}

/* The same stack word can be addressed through either the retained
 * frame register or an index derived from it without intervening writes. */
static int lp_forward_frame_clear(LpUnit *u,Function *f,size_t at)
{
    (void)at;
    if(u->indirect||cg.lp_volatile||cg.parser->no_private_regions||
       cg.parser->no_value_reuse||body_asm_statements(f->body))return 0;
    long *offsets=NULL;
    PrState *frames=NULL;
    int changed=0;
    for(unsigned i=0;i<u->count;++i){
        LpLine *clear=&u->lines[i];
        if(clear->m8||clear->x8||!lp_is(clear,"stz")||lp_frame_indexed_offset(clear,'x')!=0)continue;
        unsigned next=i+1;
        while(next<u->count&&lp_internal_path_marker(u,next,i))++next;
        if(next>=u->count)continue;
        LpLine *load=&u->lines[next];
        if(load->m8||load->x8||!lp_is(load,"lda"))continue;
        int slot=lp_frame_indexed_offset(load,'y');
        int transfer=lp_previous_frame_index_transfer(u,(int)i);
        if(slot<=0||(unsigned)(slot+1)>f->slots||transfer<0)continue;
        if(!offsets){
            offsets=allocate(u->count*sizeof *offsets);
            lp_accumulator_offsets(u,offsets,LP_Y);
            frames=pr_states(u);
        }
        if(offsets[transfer]!=slot||!frames[transfer].frame||!frames[next].frame)continue;
        lp_set(load,"    lda #$0000");
        changed=1;
        break;
    }
    free(offsets);
    free(frames);
    return changed;
}

/* A byte already loaded from a private local can provide bit 7 in C
 * before its masked store. This avoids a second word load and XBA/ASL. */
static int lp_carry_from_shift_byte(LpUnit *u,Function *f,size_t at)
{
    int changed=0;
    (void)at;
    if(!u->count||u->indirect||cg.lp_volatile||cg.lp_frame_address||cg.parser->no_private_regions||
       cg.parser->no_value_reuse||body_asm_statements(f->body))return 0;
    PrState *frames=NULL;
    for(unsigned i=0;i+1<u->count;++i){
        LpLine *rep=&u->lines[i];
        if(!lp_line_is(rep,"rep #$20")||u->lines[i+1].length!=4||strncmp(u->lines[i+1].text,".a16",4))continue;
        int store=lp_next(u,i,-1),reload=lp_next(u,i+1,1);
        if(store<0||reload<0||!lp_is(&u->lines[store],"sta")||!u->lines[store].m8||
           !lp_is(&u->lines[reload],"lda")||u->lines[reload].m8)continue;
        int mask=lp_next(u,(unsigned)store,-1);
        if(mask>=0&&lp_is(&u->lines[mask],"ldx"))mask=lp_next(u,(unsigned)mask,-1);
        if(mask<0||!lp_is(&u->lines[mask],"and")||!u->lines[mask].m8||lp_immediate(&u->lines[mask])<0)continue;
        int read=lp_next(u,(unsigned)mask,-1);
        if(read<0||!lp_is(&u->lines[read],"lda")||!u->lines[read].m8)continue;
        size_t length;
        const char *home=lp_operand(&u->lines[read],&length);
        if(length!=9||strncmp(home,"a:$",3)||memcmp(home+7,",y",2)||
           !lp_operand_is(&u->lines[reload],home,length))continue;
        int swap=lp_next(u,(unsigned)reload,1),shift=swap<0?-1:lp_next(u,(unsigned)swap,1);
        int next=shift<0?-1:lp_next(u,(unsigned)shift,1);
        if(next<0||!lp_line_is(&u->lines[swap],"xba")||!lp_line_is(&u->lines[shift],"asl a")||
           !lp_is(&u->lines[next],"lda")||u->lines[next].m8)continue;
        unsigned home_byte=(unsigned)strtoul(home+3,NULL,16);
        if(!home_byte||home_byte+1>f->slots||!lp_frame_byte_private(f,home_byte)||
           !lp_frame_byte_private(f,home_byte+1))continue;
        int offset;
        if(!frames)frames=pr_states(u);
        if(!frames[read].frame||!frames[reload].frame||
           pr_memory(&u->lines[store],&frames[store],f,&offset)!=PR_OTHER)continue;
        lp_insert(&u->lines[mask],"    cmp #$80\n");
        u->lines[reload].deleted=u->lines[swap].deleted=u->lines[shift].deleted=1;
        changed=1;
        break;
    }
    free(frames);
    return changed;
}
/* Adjacent byte regions need one width transition pair, bridging any
 * M-invariant X/Y/flag/immediate-push instructions between them. */
static int lp_byte_region_modes(LpUnit *u,Function *f,size_t at)
{
    unsigned i,j;int changed=0,known_targets=0;
    unsigned char *targets=lp_local_targets(u,&known_targets);
    (void)at;
    if(!f->symbol->interrupt&&!cg.lp_volatile){
        lp_liveness(u);
        for(i=0;i+1<u->count;++i){
            int k,load=-1;size_t n;const char *o;
            if(u->lines[i].deleted||u->lines[i].replace||u->lines[i].before||u->lines[i].label||
               u->lines[i+1].deleted||u->lines[i+1].replace||u->lines[i+1].before||u->lines[i+1].label||
               u->lines[i].m8||!lp_line_is(&u->lines[i],"sep #$20")||
               u->lines[i+1].length!=3||strncmp(u->lines[i+1].text,".a8",3))continue;
            if((u->lines[i].live&(LP_N|LP_Z))||(u->lines[i+1].out&LP_AH))continue;
            for(k=(int)i-1;k>=0;--k){
                const LpLine *l=&u->lines[k];
                if(l->deleted)continue;
                if(!l->op){if(!l->label&&l->length&&l->text[0]==';')continue;break;}
                if(l->replace||l->before||l->label)break;
                if(lp_is(l,"lda")&&!l->m8){load=k;break;}
                if((lp_is(l,"and")||lp_is(l,"ora")||lp_is(l,"eor"))&&!l->m8&&lp_immediate(l)>=0)continue;
                if(!lp_m_invariant(l))break;
            }
            if(load<0)continue;
            o=lp_operand(&u->lines[load],&n);
            long imm=lp_immediate(&u->lines[load]);
            if(imm<0&&!lp_operand_has_s(o,n)&&lp_is_mmio_operand(o,n))continue;
            /* Only the low byte survives this region. Shorten its logical
             * immediates alongside the load; they do not read the flags. */
            if(imm>=0)lp_set(&u->lines[load],"    lda #$%02lX",imm&255);
            for(k=load+1;k<(int)i;++k){
                LpLine *l=&u->lines[k];
                if(!l->deleted&&(lp_is(l,"and")||lp_is(l,"ora")||lp_is(l,"eor")))
                    lp_set(l,"    %.3s #$%02lX",l->op,lp_immediate(l)&255);
            }
            lp_insert(&u->lines[load],"    sep #$20\n.a8\n");
            u->lines[i].deleted=u->lines[i+1].deleted=1;
            changed=1;
        }
        if(changed){free(targets);return 1;}
    }
    for(i=0;i+1<u->count;++i)if(!u->lines[i].deleted&&lp_line_is(&u->lines[i],"rep #$20")&&
       u->lines[i+1].length==4&&!strncmp(u->lines[i+1].text,".a16",4)){
        for(j=i+2;j<u->count;++j){
            const LpLine *l=&u->lines[j];
            if(l->deleted)continue;
            if(lp_fallthrough_marker(l,j,targets,known_targets))continue;
            if(lp_m_invariant(l))continue;
            break;
        }
        if(j+1<u->count&&!u->lines[j].deleted&&lp_line_is(&u->lines[j],"sep #$20")&&
           u->lines[j+1].length==3&&!strncmp(u->lines[j+1].text,".a8",3)){
            u->lines[i].deleted=u->lines[i+1].deleted=u->lines[j].deleted=u->lines[j+1].deleted=1;
            changed=1;i=j+1;
        }
    }
    for(i=0;i+1<u->count;++i)if(!u->lines[i].deleted&&lp_line_is(&u->lines[i],"sep #$20")&&
       u->lines[i+1].length==3&&!strncmp(u->lines[i+1].text,".a8",3)){
        int entry_a16=0;
        for(j=i;j-- >0;){
            const LpLine *p=&u->lines[j];
            if(p->deleted)continue;
            if(p->length==4&&!strncmp(p->text,".a16",4)){entry_a16=1;break;}
            if(p->length==3&&!strncmp(p->text,".a8",3))break;
            if(!p->op){if(p->length&&p->text[0]==';')continue;break;}
            if(lp_is(p,"sep")||lp_is(p,"rep")||lp_line_is(p,"plp")||lp_line_is(p,"rti"))break;
        }
        if(!entry_a16)continue;
        for(j=i+2;j<u->count;++j){
            const LpLine *l=&u->lines[j];
            if(l->deleted)continue;
            if(lp_fallthrough_marker(l,j,targets,known_targets))continue;
            if(lp_m_invariant_op(l))continue;
            break;
        }
        if(j+1<u->count&&!u->lines[j].deleted&&lp_line_is(&u->lines[j],"rep #$20")&&
           u->lines[j+1].length==4&&!strncmp(u->lines[j+1].text,".a16",4)){
            u->lines[i].deleted=u->lines[i+1].deleted=u->lines[j].deleted=u->lines[j+1].deleted=1;
            changed=1;i=j+1;
        }
    }
    /* If a width region lost its last instruction, intervening assembler
     * width annotations do not observe M. The final REP establishes A16
     * even when the incoming hardware width is unknown. */
    for(i=0;i<u->count;++i)if(lp_line_is(&u->lines[i],"sep #$20")&&!u->lines[i].deleted){
        for(j=i+1;j<u->count;++j){
            LpLine *l=&u->lines[j];
            if(l->deleted||!l->length||l->text[0]==';'||
               (l->length==3&&!strncmp(l->text,".a8",3))||
               (l->length==4&&!strncmp(l->text,".a16",4)))continue;
            if(lp_line_is(l,"rep #$20")&&j+1<u->count&&u->lines[j+1].length==4&&
               !strncmp(u->lines[j+1].text,".a16",4)){
                for(unsigned k=i;k<j;++k)
                    if(k==i||u->lines[k].text[0]=='.')u->lines[k].deleted=1;
                changed=1;
            }
            break;
        }
    }
    free(targets);
    return changed;
}
/* Remove PHX/PLX pairs when nothing in between modifies X, shifts S or uses ,s */
static int lp_dead_x_save(LpUnit *u,Function *f,size_t at)
{
    unsigned i;int changed=0;(void)f;(void)at;
    lp_liveness(u);
    for(i=0;i<u->count;++i){
        LpLine *push=&u->lines[i];int k;
        if(!lp_line_is(push,"phx")||push->x8||push->deleted||push->replace)continue;
        k=(int)i;
        while((k=lp_next(u,(unsigned)k,1))>=0){
            LpLine *l=&u->lines[k];size_t n;const char *o;int sp_rel=0;unsigned c;
            if(l->deleted||l->replace)break;
            if(lp_line_is(l,"plx")&&!l->x8){
                if(!(l->out&(LP_N|LP_Z))){push->deleted=l->deleted=1;++changed;}
                break;
            }
            if(l->x8||l->call||l->ends||lp_branch(l)||lp_stack_op(l)||(l->def&LP_X)||
               (l->use==LP_ALL&&!lp_line_is(l,"sep #$20")&&!lp_line_is(l,"rep #$20")))break;
            o=lp_operand(l,&n);
            for(c=0;c+1<n;++c)if(o[c]==','&&o[c+1]=='s'){sp_rel=1;break;}
            if(sp_rel)break;
        }
    }
    return changed;
}
/* Narrow 16-bit RMWs ending in "sep #$20 / .a8 / sta <same>" when A and N/Z die */
static int lp_byte_rmw(LpUnit *u,Function *f,size_t at)
{
    unsigned i;int changed=0;(void)f;(void)at;
    if(cg.lp_volatile)return 0;
    lp_liveness(u);
    for(i=0;i<u->count;++i){
        LpLine *load=&u->lines[i];size_t n;const char *op;
        int k,sep=-1,store=-1,steps=0,ok=1;
        if(!lp_is(load,"lda")||load->m8||load->deleted||load->replace)continue;
        op=lp_operand(load,&n);
        if(!n||op[0]=='#')continue;
        k=(int)i;
        while((k=lp_next(u,(unsigned)k,1))>=0){
            LpLine *l=&u->lines[k];
            if(l->deleted||l->replace){ok=0;break;}
            if(lp_line_is(l,"sep #$20")){sep=k;break;}
            if(l->m8||l->call||l->ends||lp_branch(l)){ok=0;break;}
            if((lp_is(l,"and")||lp_is(l,"ora")||lp_is(l,"eor"))&&lp_immediate(l)>=0&&!(l->out&(LP_N|LP_Z))){
                ++steps;continue;
            }
            if((lp_line_is(l,"inc a")||lp_line_is(l,"dec a"))&&!(l->out&(LP_N|LP_Z))){
                ++steps;continue;
            }
            ok=0;break;
        }
        if(!ok||sep<0||!steps||(unsigned)sep+1>=u->count||
           u->lines[sep+1].length!=3||strncmp(u->lines[sep+1].text,".a8",3))continue;
        store=lp_next(u,(unsigned)sep+1,1);
        if(store<0||!lp_is(&u->lines[store],"sta")||!lp_operand_is(&u->lines[store],op,n)||
           u->lines[store].deleted||u->lines[store].replace||
           (u->lines[store].out&(LP_A|LP_N|LP_Z)))continue;
        lp_set(load,"    sep #$20\n.a8\n    lda %.*s",(int)n,op);
        for(k=lp_next(u,i,1);k>=0&&k<sep;k=lp_next(u,(unsigned)k,1)){
            LpLine *l=&u->lines[k];long imm=lp_immediate(l);
            if(imm>=0){
                unsigned b=(unsigned)imm&0xFFu;
                if((lp_is(l,"and")&&b==0xFFu)||((lp_is(l,"ora")||lp_is(l,"eor"))&&b==0u))
                    l->deleted=1;
                else lp_set(l,"    %.3s #$%02X",l->op,b);
            }
        }
        u->lines[sep].deleted=u->lines[sep+1].deleted=1;
        ++changed;i=(unsigned)store;
    }
    return changed;
}
/* Advance a private masked cursor before loading its old indexed element.
 * Keeping the old cursor in X leaves the loaded value in A for its consumer. */
static int lp_advance_before_indexed_load(LpUnit *u,Function *f,size_t at)
{
    unsigned i;
    (void)f;(void)at;
    if(u->indirect||cg.lp_volatile)return 0;
    for(i=0;i<u->count;++i){
        LpLine *x=&u->lines[i],*q[8];
        int j=(int)i,word;
        unsigned k;
        size_t n,m;
        const char *cell,*cursor,*array;
        if(x->m8||x->x8||(!lp_is(x,"tax")&&!lp_is(x,"ldx")))continue;
        for(k=0;k<8;++k){
            j=lp_next(u,(unsigned)j,1);
            if(j<0||u->lines[j].m8||u->lines[j].x8)break;
            q[k]=&u->lines[j];
        }
        if(k<8||!lp_is(q[0],"lda")||!lp_is(q[1],"sta")||!lp_line_is(q[2],"txa")||
           !lp_line_is(q[3],"clc")||!lp_is(q[4],"adc")||lp_immediate(q[4])<0||
           !lp_is(q[5],"and")||lp_immediate(q[5])<0||!lp_is(q[6],"sta")||
           !lp_is(q[7],"lda"))continue;
        array=lp_operand(q[0],&n);
        if(n<15||strncmp(array,"a:.loword(_",11)||array[n-2]!=','||array[n-1]!='x')continue;
        cell=lp_operand(q[1],&n);cursor=lp_operand(q[6],&m);
        word=lp_workspace_word(cell,n);
        if(word<0||(word&1)||lp_workspace_word(cursor,m)<0||(lp_workspace_word(cursor,m)&1)||
           lp_workspace_word(cursor,m)==word||!lp_operand_is(q[7],cell,n))continue;
        if(lp_is(x,"ldx")&&!lp_operand_is(x,cursor,m))continue;
        lp_set(q[7],"    %.*s\n    %.*s",(int)q[0]->length-4,q[0]->op,
               (int)q[1]->length-4,q[1]->op);
        q[0]->deleted=q[1]->deleted=1;
        if(lp_is(x,"tax"))q[2]->deleted=1;
        return 1;
    }
    return 0;
}

/* A discarded word update can use native RMW on compiler scratch or a
 * nonvolatile named WRAM object. INC/DEC preserve the same N/Z and C/V. */
static int lp_memory_word_steps(LpUnit *u,Function *f,size_t at)
{
    unsigned i;(void)f;(void)at;lp_liveness(u);
    for(i=0;i<u->count;++i){LpLine *l=&u->lines[i];int step,store,w;size_t n,m;const char *p,*destination;
        if(!lp_is(l,"lda")||l->m8)continue;
        p=lp_operand(l,&n);w=lp_workspace_word(p,n);
        if(w<0&&((n<4||strncmp(p,"a:_",3))&&
                 (n<13||strncmp(p,"a:.loword(_",11)||p[n-1]!=')')))continue;
        if(w<0&&(memchr(p,',',n)||!pr_named(p,n)))continue;
        step=lp_next(u,i,1);if(step<0)continue;
        if(!lp_line_is(&u->lines[step],"inc a")&&!lp_line_is(&u->lines[step],"dec a"))continue;
        store=lp_next(u,(unsigned)step,1);
        if(store<0||!lp_is(&u->lines[store],"sta")||u->lines[store].m8||u->lines[store].out&LP_A)continue;
        destination=lp_operand(&u->lines[store],&m);
        if(!lp_operand_is(&u->lines[store],p,n)&&
           !(w<0&&n==m+9&&m>=4&&!strncmp(p,"a:.loword(_",11)&&
             !strncmp(destination,"a:_",3)&&!strncmp(p+10,destination+2,m-2)))continue;
        lp_set(l,"    %.3s %.*s",u->lines[step].op,(int)n,p);u->lines[step].deleted=u->lines[store].deleted=1;return 1;
    }return 0;
}

/* INC and DEC set the same N/Z as a same-width reload of the result.
 * Only named nonvolatile objects are eligible, including indexed arrays. */
static int lp_rmw_reload(LpUnit *u,Function *f,size_t at)
{
    unsigned i;
    (void)f;(void)at;
    if(cg.lp_volatile||u->indirect)return 0;
    lp_liveness(u);
    for(i=0;i<u->count;++i){
        LpLine *update=&u->lines[i],*load;
        const char *operand;
        size_t length;
        int next;
        if(!lp_is(update,"inc")&&!lp_is(update,"dec"))continue;
        next=lp_next(u,i,1);
        if(next<0)continue;
        load=&u->lines[next];
        if(!lp_is(load,"lda")||load->m8!=update->m8||(load->out&LP_A))continue;
        operand=lp_operand(update,&length);
        if(!pr_named(operand,length)||!lp_operand_is(load,operand,length))continue;
        load->deleted=1;
        return 1;
    }
    for(i=0;i<u->count;++i){
        LpLine *load=&u->lines[i],*shift,*store;
        const char *operand,*comma;
        size_t length;
        int s,t;
        if(!lp_is(load,"lda")||load->deleted||load->replace)continue;
        operand=lp_operand(load,&length);
        if(length<3||(strncmp(operand,"z:",2)&&strncmp(operand,"a:",2))||
           memchr(operand,'(',length)||memchr(operand,'[',length))continue;
        comma=memchr(operand,',',length);
        if(comma&&!(comma+2==operand+length&&comma[1]=='x'))continue;
        s=lp_next(u,i,1);
        t=s<0?-1:lp_next(u,(unsigned)s,1);
        if(t<0)continue;
        shift=&u->lines[s];store=&u->lines[t];
        if(shift->deleted||shift->replace||store->deleted||store->replace||
           shift->m8!=load->m8||store->m8!=load->m8||
           (!lp_line_is(shift,"lsr a")&&!lp_line_is(shift,"asl a")&&
            !lp_line_is(shift,"ror a")&&!lp_line_is(shift,"rol a"))||
           !lp_is(store,"sta")||!lp_operand_is(store,operand,length)||
           (store->out&LP_A))continue;
        lp_set(load,"    %.3s %.*s",shift->op,(int)length,operand);
        shift->deleted=store->deleted=1;
        return 1;
    }
    return 0;
}

/* Swap a constant's bytes instead of swapping A around a word operation.
 * The final XBA reports byte N/Z, so those flags must be dead. */
static int lp_swapped_word_mask(LpUnit *u,Function *f,size_t at)
{
    unsigned i;
    (void)f;(void)at;
    lp_liveness(u);
    for(i=0;i<u->count;++i){
        LpLine *first=&u->lines[i],*operation,*last;
        int op,end;
        long mask;
        if(!lp_line_is(first,"xba")||first->m8||(op=lp_next(u,i,1))<0)continue;
        operation=&u->lines[op];
        if(operation->m8||(!lp_is(operation,"and")&&!lp_is(operation,"ora")&&!lp_is(operation,"eor"))||
           (mask=lp_immediate(operation))<0||mask>65535||(end=lp_next(u,(unsigned)op,1))<0)continue;
        last=&u->lines[end];
        if(last->m8||!lp_line_is(last,"xba")||(last->out&(LP_N|LP_Z)))continue;
        lp_set(operation,"    %.3s #$%04lX",operation->op,((mask&255)<<8)|(mask>>8));
        first->deleted=last->deleted=1;
        return 1;
    }
    return 0;
}
/* A full-width transfer solely to feed an unindexed store can use the
 * source register's store opcode. Keep live A and transfer flags intact. */
static int lp_store_index_value(LpUnit *u,Function *f,size_t at)
{
    unsigned i;
    (void)f;(void)at;
    lp_liveness(u);
    for(i=0;i<u->count;++i){
        LpLine *transfer=&u->lines[i],*store;
        int next;
        size_t n;
        const char *operand;
        if(transfer->m8||transfer->x8||
           (!lp_line_is(transfer,"txa")&&!lp_line_is(transfer,"tya"))||
           (next=lp_next(u,i,1))<0)continue;
        store=&u->lines[next];
        if(store->m8||!lp_is(store,"sta")||(store->out&(LP_A|LP_N|LP_Z)))continue;
        operand=lp_operand(store,&n);
        if(n<3||(strncmp(operand,"a:",2)&&strncmp(operand,"z:",2))||memchr(operand,',',n))continue;
        lp_set(store,"    %s %.*s",lp_line_is(transfer,"txa")?"stx":"sty",(int)n,operand);
        transfer->deleted=1;
        return 1;
    }
    return 0;
}
/* The direct-page word is already a near address. If the loaded X is
 * otherwise dead, an unindexed indirect load gives the same value and flags. */
static int lp_near_indirect(LpUnit *u,Function *f,size_t at)
{
    unsigned i;
    int changed=0;
    (void)f;(void)at;
    if(cg.parser->no_direct_dpage)return 0;
    lp_liveness(u);
    for(i=0;i<u->count;++i){
        LpLine *l=&u->lines[i],*read;
        const char *p;
        size_t n;
        int j;
        if(!lp_is(l,"ldx")||l->x8||(j=lp_next(u,i,1))<0)continue;
        read=&u->lines[j];p=lp_operand(l,&n);
        if((read->out&LP_X)||lp_workspace_word(p,n)<0||n<3||strncmp(p,"z:",2))continue;
        if(!lp_operand_is(read,"a:$0000,x",9)||!lp_accumulator_memory(read))continue;
        /* Unlike LDA, a store does not replace the flags set by LDX */
        if(lp_is(read,"sta")&&(read->out&(LP_N|LP_Z)))continue;
        l->deleted=1;lp_set(read,"    %.3s (%.*s)",read->op,(int)n-2,p+2);++changed;
    }
    return changed;
}
/* With the two-word parameter frame still in place, a reload of its first
 * slot into X can feed a self-call without rewriting that same slot. */
static int lp_first_parameter_in_x(LpUnit *u,unsigned call)
{
    for(int j=(int)call;(j=lp_next(u,(unsigned)j,-1))>=0;){
        LpLine *l=&u->lines[j];
        if(l->m8||l->x8||l->use==LP_ALL||lp_stack_op(l)||lp_store_op(l)||l->ends||l->target>=0)return 0;
        if(l->def&LP_X){
            int source=lp_next(u,(unsigned)j,-1);
            return lp_line_is(l,"tax")&&source>=0&&!u->lines[source].m8&&lp_line_is(&u->lines[source],"lda 1,s");
        }
    }
    return 0;
}
/* A void wrapper can restore a short push-only frame before transferring
 * to a register-argument callee. Pull through Y so X and A still hold args. */
static int lp_tail_return_compatible(Type caller,Type callee)
{
    if(caller.base==TY_VOID&&!caller.pointers)return !structure_object(callee);
    return !structure_object(caller)&&!structure_object(callee)&&
        (callee.base!=TY_VOID||callee.pointers)&&reg_width(caller)==reg_width(callee)&&
        reg_width(caller)<=4&&width(caller)==width(callee)&&caller.is_bool==callee.is_bool&&
        (width(caller)!=1||caller.is_bool||caller.is_unsigned==callee.is_unsigned);
}
static int lp_tail_wrapper(LpUnit *u,Function *f,size_t at)
{
    unsigned first=0,i;
    int long_return=cg.parser->long_return;
    const char *call_op=long_return?"jsl":"jsr",*jump_op=long_return?"jml":"jmp";
    int changed=0,*depths,saved_y,known_depths;
    (void)at;
    if(u->indirect||f->symbol->interrupt||frame_address_visible(f->body)||
       f->aggregate_abi||structure_object(f->symbol->type)||reg_width(f->symbol->type)>4)return 0;
    while(first<u->count&&!u->lines[first].op)++first;
    if(first==u->count||u->lines[first].x8)return 0;
    saved_y=lp_line_is(&u->lines[first],"phy");
    depths=allocate(u->count*sizeof *depths);
    known_depths=lp_stack_depths(u,first,depths);
    if(saved_y&&known_depths)for(i=first+1;i<u->count;++i)
        if(depths[i]==0&&u->lines[i].op&&!lp_line_is(&u->lines[i],"rtl")&&!lp_line_is(&u->lines[i],"rts")){
            saved_y=0;break;
        }
    for(i=first;i<u->count;++i){
        LpLine *call=&u->lines[i];
        const char *name;
        size_t length;
        unsigned j,pulls=0;
        int k,last_y=0;
        Symbol *callee=NULL;
        if(!lp_is(call,call_op)||call->m8||call->x8)continue;
        name=lp_operand(call,&length);
        if(!long_return&&(length<=9||strncmp(name,".loword(",8)||name[length-1]!=')'))continue;
        callee=lp_callee(call);
        if(!callee||callee->variadic||callee->param_count<0||
           !lp_tail_return_compatible(f->symbol->type,callee->type))continue;
        for(j=0;j<(unsigned)callee->param_count&&register_parameter(j,callee->params[j]);++j){}
        if(j!=(unsigned)callee->param_count)continue;
        k=(int)i+1;
        for(j=0;j<8;++j){
            while(k<(int)u->count&&!u->lines[k].op)++k;
            if(k==(int)u->count||!u->lines[k].ends||u->lines[k].target<0)break;
            k=u->lines[k].target;
        }
        /* A Y-based frame's existing release preserves X but uses A.
         * Move that exact release ahead of a call taking zero or one words. */
        if(callee->param_count<=1&&k<(int)u->count){
            int saved_result=lp_line_is(&u->lines[k],"tax");
            int start=saved_result?lp_next(u,(unsigned)k,1):k;
            int clc=start>=0?lp_next(u,(unsigned)start,1):-1;
            int add=clc>=0?lp_next(u,(unsigned)clc,1):-1;
            int tcs=add>=0?lp_next(u,(unsigned)add,1):-1;
            int ret=tcs>=0?lp_next(u,(unsigned)tcs,1):-1;
            int restore_y;
            if(saved_result&&ret>=0&&lp_line_is(&u->lines[ret],"txa"))ret=lp_next(u,(unsigned)ret,1);
            else if(saved_result)ret=-1;
            restore_y=ret>=0&&lp_line_is(&u->lines[ret],"ply");
            if(restore_y)ret=lp_next(u,(unsigned)ret,1);
            if(ret>=0&&!u->lines[start].m8&&
               (lp_line_is(&u->lines[start],"tsc")||
                (restore_y&&lp_line_is(&u->lines[start],"tya")))&&lp_line_is(&u->lines[clc],"clc")&&
               lp_is(&u->lines[add],"adc")&&lp_immediate(&u->lines[add])>0&&
               lp_line_is(&u->lines[tcs],"tcs")&&
               (lp_line_is(&u->lines[ret],"rts")||(long_return&&lp_line_is(&u->lines[ret],"rtl")))){
                lp_set(call,"    %.3s\n    clc\n%.*s\n    tcs\n%s    %s %.*s",
                       u->lines[start].op,(int)u->lines[add].length,u->lines[add].text,
                       restore_y?"    ply\n":"",jump_op,(int)length,name);
                ++changed;
                continue;
            }
        }
        if(!known_depths||depths[i]<0||depths[i]>8)continue;
        for(;k<(int)u->count;++k){
            LpLine *l=&u->lines[k];
            if(!l->op)continue;
            if(l->x8||last_y)break;
            if(lp_line_is(l,"plx")||(lp_line_is(l,"pla")&&!l->m8)){++pulls;continue;}
            if(lp_line_is(l,"ply")){++pulls;last_y=1;continue;}
            break;
        }
        if(callee==f->symbol&&callee->param_count==2&&!last_y&&pulls==2&&depths[i]==4&&
           k<(int)u->count&&(lp_line_is(&u->lines[k],"rts")||lp_line_is(&u->lines[k],"rtl"))&&
           lp_line_is(&u->lines[first],"pha")){
            int second=lp_next(u,first,1);
            int body=second>=0?lp_next(u,(unsigned)second,1):-1;
            if(body>=0&&lp_line_is(&u->lines[second],"phx")){
                lp_liveness(u);
                if(!(u->lines[body].live&(LP_N|LP_Z))){
                    /* The recursive edge reuses the existing argument frame.
                     * Preserve A when the entry body consumes its register value. */
                    char entry[128];
                    unsigned target=++cg.label;
                    snprintf(entry,sizeof entry,"cg_%s_%u = *\n",cg.parser->unit,target);
                    lp_insert(&u->lines[body],entry);
                    int same_x=lp_first_parameter_in_x(u,i);
                    lp_set(call,"    sta 3,s\n%s%s    jmp cg_%s_%u",same_x?"":"    txa\n    sta 1,s\n",
                           !same_x&&(u->lines[body].live&LP_A)?"    lda 3,s\n":"",cg.parser->unit,target);
                    ++changed;continue;
                }
            }
        }
        if((last_y&&saved_y)||!depths[i]||(!last_y&&callee->param_count<=1)){
            while(k<(int)u->count&&!u->lines[k].op)++k;
            if(k<(int)u->count&&(lp_line_is(&u->lines[k],"rts")||(long_return&&lp_line_is(&u->lines[k],"rtl")))&&
               2*pulls==(unsigned)depths[i]){
                char restore[40]="";
                for(j=0;j<pulls;++j)strcat(restore,last_y?"    ply\n":"    pla\n");
                lp_set(call,"%s    %s %.*s",restore,jump_op,(int)length,name);
                ++changed;
            }
        }
    }
    free(depths);return changed;
}
/* Keep an incoming X parameter in X when its frame home is read-only
 * and the body never uses X for anything else. Preserve it around ordinary
 * calls. Keep a second parameter in scratch if all uses precede calls,
 * otherwise give it one stack-relative word. */
static int lp_register_parameter_frame(LpUnit *u,Function *f,size_t at)
{
    Symbol *s=f->symbol;
    unsigned entry=0,i,frame;
    int save_a,save_x,base,ready,*depths,ok=0,dp_a,reads_a=0,call_seen=0,stack_only;
    (void)at;
    if(s->param_count<1||s->param_count>2||s->variadic||u->indirect||u->helpers||
       statement_inline_markers(f->body)||!register_parameter(0,s->params[0])||
       (s->param_count==2&&!register_parameter(1,s->params[1])))return 0;
    while(entry<u->count&&!u->lines[entry].op)++entry;
    if(entry==u->count||u->lines[entry].x8)return 0;
    stack_only=s->param_count==1&&lp_line_is(&u->lines[entry],"phx");
    if(!stack_only&&!lp_line_is(&u->lines[entry],"phy"))return 0;
    save_a=s->param_count==2?lp_next(u,entry,1):-1;
    if(s->param_count==2&&(save_a<0||!lp_line_is(&u->lines[save_a],"pha")||u->lines[save_a].m8))return 0;
    save_x=stack_only?(int)entry:lp_next(u,save_a>=0?(unsigned)save_a:entry,1);
    if(save_x<0||!lp_line_is(&u->lines[save_x],"phx"))return 0;
    base=stack_only?save_x:lp_next(u,(unsigned)save_x,1);
    if(base<0||(!stack_only&&!lp_line_is(&u->lines[base],"tsc")))return 0;
    ready=stack_only?base:lp_next(u,(unsigned)base,1);
    if(ready<0||(!stack_only&&!lp_line_is(&u->lines[ready],"tay")))return 0;
    frame=stack_only?2:save_a>=0?6:4;
    depths=allocate(u->count*sizeof *depths);
    if(!lp_stack_depths(u,entry,depths))goto done;
    for(i=(unsigned)ready+1;i<u->count;++i)
        if(lp_line_is(&u->lines[i],"sep #$20")||lp_line_is(&u->lines[i],"rep #$20"))u->lines[i].use=0;
    lp_liveness(u);
    if(!stack_only&&(u->lines[ready].out&(LP_A|LP_N|LP_Z)))goto done;
    dp_a=save_a>=0&&!cg.parser->no_dp_homes&&
        !(lp_text_words(u->text,u->text+strlen(u->text))&1);
    for(i=(unsigned)ready+1;dp_a&&i<u->count;++i){
        LpLine *l=&u->lines[i];
        if(!l->op||depths[i]<0)continue;
        if(l->target>=0&&(unsigned)l->target<=i)dp_a=0;
        if(l->call)call_seen=1;
        if(lp_line_is(l,"lda a:$0003,y")&&
           (lp_next(u,(unsigned)ready,1)!=(int)i||l->out&(LP_N|LP_Z))){
            ++reads_a;
            if(call_seen)dp_a=0;
        }
    }
    for(i=(unsigned)ready+1;i<u->count;++i){
        LpLine *l=&u->lines[i];
        const char *operand;
        size_t length;
        int next;
        if(!l->op||depths[i]<0)continue;
        if(l->target>=0&&l->target<=ready)goto done;
        if(lp_line_is(l,"rts")||lp_line_is(l,"rtl")||(l->ends&&(l->call||l->target<0))){
            if(depths[i]!=0)goto done;
            continue;
        }
        if(stack_only&&(lp_line_is(l,"pla")||lp_line_is(l,"plx"))){
            Symbol *callee;
            next=lp_next(u,i,1);
            if(next<0||depths[i]!=2||l->m8)goto done;
            callee=lp_callee(&u->lines[next]);
            if(lp_line_is(l,"pla")&&(!u->lines[next].ends||!callee||
               callee->param_count<0||callee->param_count>1))goto done;
            if(lp_line_is(l,"plx")&&!lp_line_is(&u->lines[next],"rts")&&
               !lp_line_is(&u->lines[next],"rtl"))goto done;
            l->deleted=1;
            continue;
        }
        if(lp_line_is(l,"ply")||lp_line_is(l,"plx")){
            next=lp_next(u,i,1);
            if(l->x8||depths[i]<=0||depths[i]>(int)frame||next<0||
               (depths[i]>2&&!lp_line_is(&u->lines[next],"plx")&&!lp_line_is(&u->lines[next],"ply"))||
               (depths[i]==2&&(!lp_line_is(l,"ply")||
                !(lp_line_is(&u->lines[next],"rts")||lp_line_is(&u->lines[next],"rtl")||
                  (u->lines[next].ends&&(u->lines[next].call||u->lines[next].target<0))))))goto done;
            if(save_a<0||dp_a||depths[i]==(int)frame)l->deleted=1;
            continue;
        }
        if(depths[i]!=(int)frame||l->x8)goto done;
        if(l->call){
            if(l->out&(LP_X|LP_N|LP_Z))goto done;
            lp_set(l,"    phx\n%.*s\n    plx",(int)l->length,l->text);
            continue;
        }
        if(lp_stack_op(l))goto done;
        if(lp_line_is(l,"ldx a:$0001,y")){
            if(l->out&(LP_N|LP_Z))goto done;
            l->deleted=1;
            continue;
        }
        if(lp_line_is(l,stack_only?"lda 1,s":"lda a:$0001,y")&&!l->m8){
            next=lp_next(u,i,1);
            if(next>=0&&lp_line_is(&u->lines[next],"tax")&&!u->lines[next].x8){
                /* X still holds this argument. Keep TXA only for A or N/Z */
                if(u->lines[next].out&(LP_A|LP_N|LP_Z))lp_set(l,"    txa");
                else l->deleted=1;
                u->lines[next].deleted=1;
                i=(unsigned)next;
            }else lp_set(l,"    txa");
            continue;
        }
        if(save_a>=0&&lp_line_is(l,"lda a:$0003,y")&&!l->m8){
            if(lp_next(u,(unsigned)ready,1)==(int)i&&!(l->out&(LP_N|LP_Z)))l->deleted=1;
            else lp_set(l,dp_a?"    lda z:__arith_lhs":"    lda 1,s");
            continue;
        }
        operand=lp_operand(l,&length);
        if(l->def&LP_X){
            int previous=lp_next(u,i,-1);
            if(lp_line_is(l,"tax")&&!l->m8&&previous>=0&&
               lp_line_is(&u->lines[previous],"txa")){
                l->deleted=1;
                continue;
            }
            /* A final argument may replace the incoming X immediately
             * before a validated cleanup and terminal transfer. */
            next=lp_next(u,i,1);
            while(next>=0&&(lp_line_is(&u->lines[next],"ply")||lp_line_is(&u->lines[next],"plx")||
                           (stack_only&&lp_line_is(&u->lines[next],"pla"))))
                next=lp_next(u,(unsigned)next,1);
            if(next<0||!u->lines[next].ends||(!u->lines[next].call&&u->lines[next].target>=0))goto done;
        }
        if((l->def&LP_Y)||(l->use&LP_Y)||lp_line_is(l,"tsc")||
           (length>=2&&operand[length-2]==','&&operand[length-1]=='s')||
           (l->use==LP_ALL&&!lp_line_is(l,"sep #$20")&&!lp_line_is(l,"rep #$20")))goto done;
    }
    if(save_a<0||dp_a)u->lines[entry].deleted=1;
    if(dp_a){
        if(reads_a){lp_set(&u->lines[save_a],"    sta z:__arith_lhs");cg.arithmetic=1;}
        else u->lines[save_a].deleted=1;
    }
    u->lines[save_x].deleted=u->lines[base].deleted=u->lines[ready].deleted=1;
    ok=1;
done:
    free(depths);return ok;
}
static int lp_store_zero_operand(const LpLine *store,const char **operand,size_t *length,int m8)
{
    if(!lp_is(store,"sta")||store->m8!=m8||store->deleted||store->replace)return 0;
    *operand=lp_operand(store,length);
    return *length>=3&&(!strncmp(*operand,"a:",2)||!strncmp(*operand,"z:",2))&&
           !(*length>=2&&(*operand)[*length-2]==','&&(*operand)[*length-1]!='x');
}
static int lp_store_zero(LpUnit *u,Function *f,size_t at)
{
    unsigned i;
    int changed=0;
    (void)f;(void)at;
    lp_liveness(u);
    for(i=0;i<u->count;++i){
        LpLine *load=&u->lines[i];
        int k,last=-1,m8=load->m8;
        const char *operand;
        size_t length;
        unsigned live_mask=m8?(LP_A|LP_AL|LP_N|LP_Z):(LP_A|LP_N|LP_Z);
        if(!lp_is(load,"lda")||load->deleted||load->replace||lp_immediate(load)!=0)continue;
        k=lp_next(u,i,1);
        if(!m8&&k>=0&&lp_line_is(&u->lines[k],"sep #$20")&&(unsigned)k+1<u->count&&
           !u->lines[k+1].deleted&&u->lines[k+1].length==3&&!strncmp(u->lines[k+1].text,".a8",3)){
            m8=1;k=lp_next(u,(unsigned)(k+1),1);
            live_mask=LP_A|LP_AL|LP_N|LP_Z;
        }
        if(k<0)continue;
        for(;k>=0&&(unsigned)k<u->count;k=lp_next(u,(unsigned)k,1)){
            if(!lp_store_zero_operand(&u->lines[k],&operand,&length,m8))break;
            last=k;
            if(!(u->lines[k].out&live_mask))break;
        }
        if(last<0||(u->lines[last].out&live_mask))continue;
        for(k=(int)i+1;k<=last;++k){
            LpLine *store=&u->lines[k];
            if(lp_store_zero_operand(store,&operand,&length,m8))
                lp_set(store,"    stz %.*s",(int)length,operand);
        }
        load->deleted=1;
        ++changed;
    }
    return changed;
}
/* Relocate a call-free stack-relative frame to unused DP words. No
 * transfer is folded, so volatile stack accesses retain their width and
 * order. A tail call may clobber the relocated locals after the last use. */
static int lp_closed_frame(LpUnit *u,Function *f,size_t at)
{
    unsigned entry=0,i,slot,words,used;
    int sec,sub,ready;
    long size;
    (void)at;
    if(cg.parser->no_dp_homes||u->indirect||f->symbol->param_count!=0||
       f->symbol->type.base!=TY_VOID||f->symbol->type.pointers)return 0;
    while(entry<u->count&&!u->lines[entry].op)++entry;
    if(entry==u->count||!lp_line_is(&u->lines[entry],"tsc"))return 0;
    sec=lp_next(u,entry,1);
    sub=sec>=0?lp_next(u,(unsigned)sec,1):-1;
    ready=sub>=0?lp_next(u,(unsigned)sub,1):-1;
    if(ready<0||!lp_line_is(&u->lines[sec],"sec")||!lp_is(&u->lines[sub],"sbc")||
       (size=lp_immediate(&u->lines[sub]))<1||size>24||!lp_line_is(&u->lines[ready],"tcs"))return 0;
    words=((unsigned)size+1)/2;
    used=lp_text_words(u->text,u->text+strlen(u->text));
    for(slot=0;slot+words<=16;++slot)
        if(!(used&(((1u<<words)-1u)<<slot)))break;
    if(slot+words>16)return 0;
    for(i=(unsigned)ready+1;i<u->count;++i)
        if(lp_line_is(&u->lines[i],"sep #$20")||lp_line_is(&u->lines[i],"rep #$20"))u->lines[i].use=0;
    lp_liveness(u);
    if(u->lines[ready].out&(LP_A|LP_FLAGS))return 0;
    for(i=(unsigned)ready+1;i<u->count;++i){
        LpLine *l=&u->lines[i];
        const char *p;
        size_t n;
        if(!l->op)continue;
        if(l->x8||(l->call&&!l->ends)||((lp_branch(l)||l->target>=0)&&l->target<=ready))return 0;
        if(lp_line_is(l,"tsc")){
            int clc=lp_next(u,i,1);
            int add=clc>=0?lp_next(u,(unsigned)clc,1):-1;
            int reset=add>=0?lp_next(u,(unsigned)add,1):-1;
            int ret=reset>=0?lp_next(u,(unsigned)reset,1):-1;
            int saved_result=ret>=0&&lp_line_is(&u->lines[ret],"txa");
            int previous=lp_next(u,i,-1);
            if(saved_result)ret=lp_next(u,(unsigned)ret,1);
            if(ret<0||l->m8||!lp_line_is(&u->lines[clc],"clc")||
               !lp_is(&u->lines[add],"adc")||lp_immediate(&u->lines[add])!=size||
               !lp_line_is(&u->lines[reset],"tcs")||
               !(lp_line_is(&u->lines[ret],"rts")||lp_line_is(&u->lines[ret],"rtl")||
                 (u->lines[ret].ends&&u->lines[ret].call)))return 0;
            if(saved_result){
                int after=lp_next(u,(unsigned)reset,1);
                if(previous<0||!lp_line_is(&u->lines[previous],"tax")||
                   (u->lines[ret].ends&&u->lines[ret].call))return 0;
                u->lines[previous].deleted=u->lines[after].deleted=1;
            }
            l->deleted=u->lines[clc].deleted=u->lines[add].deleted=u->lines[reset].deleted=1;
            i=(unsigned)ret;
            continue;
        }
        if(lp_stack_op(l)||lp_is(l,"tsx"))return 0;
        p=lp_operand(l,&n);
        if(n>=2&&p[n-2]==','&&p[n-1]=='s'){
            char *end;
            long offset=strtol(p,&end,10);
            if(end!=p+n-2||offset<1||offset+lp_width(l)-1>size||
               (!lp_is(l,"lda")&&!lp_is(l,"sta")&&!lp_is(l,"adc")&&!lp_is(l,"sbc")&&
                !lp_is(l,"and")&&!lp_is(l,"ora")&&!lp_is(l,"eor")&&!lp_is(l,"cmp")))return 0;
            lp_set(l,"    %.3s z:__arith_lhs+%u",l->op,2*slot+(unsigned)offset-1);
        }else if(l->use==LP_ALL&&!lp_line_is(l,"sep #$20")&&!lp_line_is(l,"rep #$20"))return 0;
    }
    u->lines[entry].deleted=u->lines[sec].deleted=u->lines[sub].deleted=u->lines[ready].deleted=1;
    cg.arithmetic=1;
    return 1;
}
#include "frame_regions.inc"
/* Keep a saved X in its register through a stack-free dispatch. A tail
 * callee with one register argument needs the adjusted X, but not the PLA
 * that used to release the wrapper's stack word. */
static int lp_tail_index_dispatch(LpUnit *u,Function *f,size_t at)
{
    unsigned first=0,i;
    int *depth,ok=0,tails=0,stack,word;
    const char *saved;
    size_t saved_length=3;
    (void)at;
    if(u->indirect||cg.parser->no_stack_frames||frame_address_visible(f->body)||
       f->symbol->type.base!=TY_VOID||f->symbol->type.pointers)return 0;
    while(first<u->count&&!u->lines[first].op)++first;
    if(first==u->count||u->lines[first].x8)return 0;
    stack=lp_line_is(&u->lines[first],"phx");
    saved=stack?"1,s":lp_operand(&u->lines[first],&saved_length);
    if(stack)word=-1;
    else if(!lp_is(&u->lines[first],"stx")||
            (word=lp_workspace_word(saved,saved_length))<0||(word&1))return 0;
    depth=allocate(u->count*sizeof *depth);
    if(!lp_stack_depths(u,first,depth))goto done;
    for(i=first+1;i<u->count;++i){
        LpLine *l=&u->lines[i];
        size_t n;
        const char *operand=lp_operand(l,&n);
        int next;
        if(!l->op)continue;
        if(l->m8||l->x8||depth[i]<0||(l->target>=0&&(unsigned)l->target<=first))goto done;
        next=lp_next(u,i,1);
        if(stack&&lp_line_is(l,"plx")&&depth[i]==2&&next>=0&&
           (lp_is(&u->lines[next],"rts")||lp_is(&u->lines[next],"rtl"))){
            l->deleted=1;
            i=(unsigned)next;
        }else if(lp_is(l,"lda")&&n>1&&operand[0]=='#'&&depth[i]==2*stack){
            int add=next>=0?lp_next(u,(unsigned)next,1):-1;
            int tax=add>=0?lp_next(u,(unsigned)add,1):-1;
            int after=tax>=0?lp_next(u,(unsigned)tax,1):-1;
            int jump=stack&&after>=0?lp_next(u,(unsigned)after,1):after;
            Symbol *callee=jump>=0?lp_callee(&u->lines[jump]):NULL;
            if(!callee||callee->interrupt||callee->variadic||callee->param_count!=1||
               !register_parameter(0,callee->params[0])||!u->lines[jump].ends||
               !u->lines[jump].call||!lp_line_is(&u->lines[next],"clc")||
               !lp_is(&u->lines[add],"adc")||!lp_operand_is(&u->lines[add],saved,saved_length)||
               !lp_line_is(&u->lines[tax],"tax")||(stack&&!lp_line_is(&u->lines[after],"pla")))continue;
            lp_set(l,"    txa");
            lp_set(&u->lines[add],"    adc %.*s",(int)n,operand);
            if(stack)u->lines[after].deleted=1;
            i=(unsigned)jump;
            ++tails;
        }else if(!stack&&(lp_is(l,"rts")||lp_is(l,"rtl"))){
            continue;
        }else if(depth[i]!=2*stack||lp_stack_op(l)||lp_is(l,"tsx")||lp_is(l,"tsc")||
                 (l->def&LP_X)||l->use==LP_ALL||(lp_branch(l)&&l->target<0)||
                 (!stack&&(lp_text_words(operand,operand+n)&(1u<<(word/2))))||
                 (n>=2&&operand[n-2]==','&&operand[n-1]=='s')||
                 (n>=5&&!memcmp(operand+n-5,",s),y",5)))goto done;
    }
    if(tails){u->lines[first].deleted=1;ok=1;}
done:
    free(depth);
    return ok;
}
typedef struct { char mem[4][64],imm[4][64];signed char eq[4];unsigned count,valid; } LpFactSet;
static void lp_fact_kill(LpFactSet *f,const LpLine *l)
{
    unsigned i=0;
    if(!l->op||l->deleted)return;
    if(l->call||l->use==LP_ALL){f->count=0;return;}
    while(i<f->count){
        size_t n=strlen(f->mem[i]);
        if(lp_may_write(l,f->mem[i],n,2)||(n>=2&&f->mem[i][n-2]==','&&f->mem[i][n-1]=='s'&&lp_stack_op(l))){
            f->count--;
            if(i<f->count){memcpy(f->mem[i],f->mem[f->count],64);memcpy(f->imm[i],f->imm[f->count],64);f->eq[i]=f->eq[f->count];}
        }else ++i;
    }
}
static void lp_fact_set(LpFactSet *f,const char *mem,const char *imm,int eq)
{
    unsigned i;
    for(i=0;i<f->count;++i){
        if(!strcmp(f->mem[i],mem)&&!strcmp(f->imm[i],imm)){f->eq[i]=(signed char)eq;return;}
    }
    if(f->count<4){
        snprintf(f->mem[f->count],64,"%s",mem);
        snprintf(f->imm[f->count],64,"%s",imm);
        f->eq[f->count]=(signed char)eq;
        ++f->count;
    }
}
static void lp_fact_meet(LpFactSet *dst,const LpFactSet *src)
{
    unsigned i=0,j;
    if(!src->valid)return;
    if(!dst->valid){*dst=*src;return;}
    while(i<dst->count){
        for(j=0;j<src->count;++j){
            if(!strcmp(dst->mem[i],src->mem[j])&&!strcmp(dst->imm[i],src->imm[j])&&dst->eq[i]==src->eq[j])break;
        }
        if(j==src->count){
            dst->count--;
            if(i<dst->count){memcpy(dst->mem[i],dst->mem[dst->count],64);memcpy(dst->imm[i],dst->imm[dst->count],64);dst->eq[i]=dst->eq[dst->count];}
        }else ++i;
    }
}
static int lp_first_code(const LpUnit *u,unsigned k)
{
    while(k<u->count){
        if(u->lines[k].deleted||u->lines[k].label||!u->lines[k].op){++k;continue;}
        return (int)k;
    }
    return (int)u->count;
}
static int lp_next_in_block(const LpUnit *u,unsigned k)
{
    while(++k<u->count){
        if(u->lines[k].deleted)continue;
        if(u->lines[k].label||!u->lines[k].length)return -1;
        if(u->lines[k].text[0]==';')continue;
        return u->lines[k].op?(int)k:-1;
    }
    return -1;
}
static int lp_label_name_at(const LpUnit *u,unsigned k,char *out,size_t out_sz)
{
    while(k<u->count){
        const LpLine *l=&u->lines[k];
        if(l->deleted){++k;continue;}
        if(l->label){
            size_t len=l->length;
            if(len>=4&&!strncmp(l->text+len-4," = *",4))len-=4;
            else if(len>=1&&l->text[len-1]==':')--len;
            if(len>3&&!strncmp(l->text,"cg_",3)&&len<out_sz){
                memcpy(out,l->text,len);out[len]=0;return 1;
            }
            ++k;continue;
        }
        if(!l->op){++k;continue;}
        break;
    }
    return 0;
}
static int lp_match_test_at(const LpUnit *u,unsigned start,char *mem,char *imm,int *eq_line,int *ne_line,int *end_line)
{
    int k0=lp_first_code(u,start),k1,kb,kj;
    const LpLine *l0,*lc,*lb,*lj;
    size_t n;const char *o;
    if(k0>=(int)u->count)return 0;
    l0=&u->lines[k0];
    if(!lp_is(l0,"lda")||l0->m8||l0->deleted||l0->replace||lp_index_use(l0))return 0;
    o=lp_operand(l0,&n);
    if(!n||n>=64||o[0]=='#'||o[0]=='('||o[0]=='['||!strncmp(o,"f:$",3))return 0;
    if(cg.lp_volatile&&!lp_private(o,n))return 0;
    memcpy(mem,o,n);mem[n]=0;
    k1=lp_next_in_block(u,(unsigned)k0);
    if(k1<0)return 0;
    lc=&u->lines[k1];
    if(lp_is(lc,"cmp")){
        if(lc->m8||lc->deleted||lc->replace)return 0;
        o=lp_operand(lc,&n);
        if(!n||n>=64||o[0]!='#')return 0;
        memcpy(imm,o,n);imm[n]=0;
        kb=lp_next_in_block(u,(unsigned)k1);
        if(kb<0)return 0;
    }else{
        strcpy(imm,"#0");kb=k1;
    }
    lb=&u->lines[kb];
    if((!lp_is(lb,"beq")&&!lp_is(lb,"bne"))||lb->deleted||lb->replace||lb->target<0)return 0;
    if(u->lines[lb->target].length==1&&u->lines[lb->target].text[0]==':'){
        int colon=lb->target;
        kj=lp_next_in_block(u,(unsigned)kb);
        if(kj<0||kj>=colon)return 0;
        lj=&u->lines[kj];
        if(!lp_is(lj,"jmp")||lj->deleted||lj->replace||lj->target<0)return 0;
        if(lp_next_in_block(u,(unsigned)kj)>=0)return 0;
        if(lp_is(lb,"bne")){*eq_line=lj->target;*ne_line=colon+1;}
        else{*eq_line=colon+1;*ne_line=lj->target;}
        *end_line=colon;
        return 1;
    }
    if(lp_is(lb,"beq")){*eq_line=lb->target;*ne_line=kb+1;}
    else{*ne_line=lb->target;*eq_line=kb+1;}
    *end_line=kb;
    return 1;
}
static int lp_jump_threading(LpUnit *u,Function *f,size_t at)
{
    LpFactSet *in,*out,*branch_out;
    unsigned i;int changed=0,iter,step_changed=0;
    (void)f;(void)at;
    if(!u->count)return 0;
    in=allocate(u->count*sizeof *in);
    out=allocate(u->count*sizeof *out);
    branch_out=allocate(u->count*sizeof *branch_out);
    {
        lp_liveness(u);
        memset(in,0,u->count*sizeof *in);
        memset(out,0,u->count*sizeof *out);
        memset(branch_out,0,u->count*sizeof *branch_out);
        in[0].valid=1;
        for(iter=0;iter<16;++iter){
            int diff=0;
            for(i=0;i<u->count;++i){
                LpLine *l=&u->lines[i];
                LpFactSet cur={0};
                if(i==0){cur.valid=1;}
                else if(l->label){
                    int p;
                    if(!u->lines[i-1].ends&&out[i-1].valid)lp_fact_meet(&cur,&out[i-1]);
                    for(p=l->first_incoming;p>=0;p=u->lines[p].next_incoming){
                        if(u->lines[p].deleted)continue;
                        if(lp_branch(&u->lines[p])){
                            if(branch_out[p].valid)lp_fact_meet(&cur,&branch_out[p]);
                        }else if(out[p].valid)lp_fact_meet(&cur,&out[p]);
                    }
                }else if(!u->lines[i-1].ends&&out[i-1].valid){
                    cur=out[i-1];
                }
                if(!cur.valid)continue;
                if(memcmp(&in[i],&cur,sizeof cur)!=0){in[i]=cur;diff=1;}
                {
                    LpFactSet nxt=cur,bout=cur;
                    char mem[64],imm[64];int eq_l,ne_l,end_l;
                    if(lp_match_test_at(u,i,mem,imm,&eq_l,&ne_l,&end_l)){
                        /* Check conditional branch lines generated inside [i..end_l] below; propagate per-line cleanly */
                    }
                    lp_fact_kill(&nxt,l);
                    lp_fact_kill(&bout,l);
                    /* Look back at cmp/lda right before a conditional branch b */
                    if(!l->deleted&&(lp_is(l,"beq")||lp_is(l,"bne"))){
                        int k1=(int)i-1,k0;
                        while(k1>=0&&(u->lines[k1].deleted||!u->lines[k1].op))--k1;
                        if(k1>=0&&lp_is(&u->lines[k1],"cmp")&&!u->lines[k1].m8){
                            const char *co;size_t cn;
                            co=lp_operand(&u->lines[k1],&cn);
                            k0=k1-1;while(k0>=0&&(u->lines[k0].deleted||!u->lines[k0].op))--k0;
                            if(k0>=0&&lp_is(&u->lines[k0],"lda")&&!u->lines[k0].m8&&!lp_index_use(&u->lines[k0])&&cn&&cn<64&&co[0]=='#'){
                                size_t mn;const char *mo=lp_operand(&u->lines[k0],&mn);
                                if(mn&&mn<64&&mo[0]!='#'&&mo[0]!='('&&mo[0]!='['&&strncmp(mo,"f:$",3)&&(!cg.lp_volatile||lp_private(mo,mn))){
                                    char mb[64],ib[64];
                                    memcpy(mb,mo,mn);mb[mn]=0;memcpy(ib,co,cn);ib[cn]=0;
                                    lp_fact_set(&bout,mb,ib,lp_is(l,"beq")?1:0);
                                    lp_fact_set(&nxt,mb,ib,lp_is(l,"beq")?0:1);
                                }
                            }
                        }else if(k1>=0&&lp_is(&u->lines[k1],"lda")&&!u->lines[k1].m8&&!lp_index_use(&u->lines[k1])){
                            size_t mn;const char *mo=lp_operand(&u->lines[k1],&mn);
                            if(mn&&mn<64&&mo[0]!='#'&&strncmp(mo,"f:$",3)&&(!cg.lp_volatile||lp_private(mo,mn))){
                                char mb[64];memcpy(mb,mo,mn);mb[mn]=0;
                                lp_fact_set(&bout,mb,"#0",lp_is(l,"beq")?1:0);
                                lp_fact_set(&nxt,mb,"#0",lp_is(l,"beq")?0:1);
                            }
                        }
                    }
                    (void)eq_l;(void)ne_l;(void)end_l;(void)mem;(void)imm;
                    if(memcmp(&out[i],&nxt,sizeof nxt)!=0){out[i]=nxt;diff=1;}
                    if(memcmp(&branch_out[i],&bout,sizeof bout)!=0){branch_out[i]=bout;diff=1;}
                }
            }
            if(!diff)break;
        }
        /* Thread edges targeting redundant conditional tests */
        for(i=0;i<u->count;++i){
            LpLine *l=&u->lines[i];
            const LpFactSet *ef;
            char t_mem[64],t_imm[64],dest_lbl[64],old_lbl[64];
            int eq_l,ne_l,end_l,dest_l,dest_op;unsigned j;
            if(l->deleted||!l->op||l->target<0)continue;
            if(!lp_is(l,"jmp")&&!lp_is(l,"beq")&&!lp_is(l,"bne")&&!lp_is(l,"bra"))continue;
            if(u->lines[l->target].length==1&&u->lines[l->target].text[0]==':')continue;
            ef=lp_branch(l)?&branch_out[i]:&in[i];
            if(!ef->valid)continue;
            if(!lp_match_test_at(u,(unsigned)l->target,t_mem,t_imm,&eq_l,&ne_l,&end_l))continue;
            for(j=0;j<ef->count;++j){
                if(!strcmp(ef->mem[j],t_mem)&&!strcmp(ef->imm[j],t_imm))break;
            }
            if(j==ef->count)continue;
            dest_l=ef->eq[j]?eq_l:ne_l;
            dest_op=lp_first_code(u,(unsigned)dest_l);
            if(dest_op>=(int)u->count)continue;
            if(u->lines[dest_op].live&(LP_A|LP_N|LP_Z|LP_C))continue;
            if(!lp_label_name_at(u,(unsigned)dest_l,dest_lbl,sizeof dest_lbl))continue;
            if(lp_label_name_at(u,(unsigned)l->target,old_lbl,sizeof old_lbl)&&!strcmp(old_lbl,dest_lbl))continue;
            if(lp_is(l,"jmp"))lp_set(l,"    jmp .loword(%s)",dest_lbl);
            else lp_set(l,"    %.*s %s",3,l->op,dest_lbl);
            ++step_changed;++changed;break;
        }
        if(!step_changed){
            for(i=0;i<u->count;++i){
                char t_mem[64],t_imm[64],dest_lbl[64];
                int eq_l,ne_l,end_l,dest_l,dest_op;unsigned j,k;
                if(!in[i].valid||u->lines[i].label||u->lines[i].deleted||!u->lines[i].op)continue;
                if(!lp_match_test_at(u,i,t_mem,t_imm,&eq_l,&ne_l,&end_l))continue;
                if(lp_first_code(u,i)!=(int)i)continue;
                for(j=0;j<in[i].count;++j){
                    if(!strcmp(in[i].mem[j],t_mem)&&!strcmp(in[i].imm[j],t_imm))break;
                }
                if(j==in[i].count)continue;
                dest_l=in[i].eq[j]?eq_l:ne_l;
                dest_op=lp_first_code(u,(unsigned)dest_l);
                if(dest_op>=(int)u->count)continue;
                if(u->lines[dest_op].live&(LP_A|LP_N|LP_Z|LP_C))continue;
                if(dest_l==end_l+1){
                    for(k=i;k<=(unsigned)end_l;++k)if(u->lines[k].op)u->lines[k].deleted=1;
                    ++step_changed;++changed;break;
                }
                if(lp_label_name_at(u,(unsigned)dest_l,dest_lbl,sizeof dest_lbl)){
                    lp_set(&u->lines[i],"    jmp .loword(%s)",dest_lbl);
                    for(k=i+1;k<=(unsigned)end_l;++k)if(u->lines[k].op)u->lines[k].deleted=1;
                    ++step_changed;++changed;break;
                }
            }
        }
        (void)step_changed;
    }
    free(in);free(out);free(branch_out);
    return changed;
}
static int lp_next_carry(const LpUnit *u,unsigned k)
{
    unsigned i=k;
    while(++i<u->count){
        const LpLine *l=&u->lines[i];
        if(l->deleted||l->text[0]==';')continue;
        if(l->label){
            int p,used=0;
            for(p=l->first_incoming;p>=0;p=u->lines[p].next_incoming)
                if(!u->lines[p].deleted){used=1;break;}
            if(!used)continue;
            return -1;
        }
        return l->op?(int)i:-1;
    }
    return -1;
}
static int lp_reuse_address_carry(LpUnit *u,Function *f,size_t at)
{
    unsigned i;int changed=0;(void)f;(void)at;
    lp_liveness(u);
    for(i=0;i<u->count;++i){
        LpLine *l0=&u->lines[i];
        int k,mask1=-1,clc1,adc1,p,cnt=0;
        const char *o;size_t mn,an;char slot[64],imm[64];
        if(l0->deleted||l0->replace||l0->m8||!lp_is(l0,"lda")||lp_index_use(l0))continue;
        o=lp_operand(l0,&mn);
        if(!mn||mn>=64||o[0]=='#'||!strncmp(o,"f:$",3))continue;
        if(cg.lp_volatile&&!(mn>=3&&mn<=5&&o[mn-2]==','&&o[mn-1]=='s'&&isdigit((unsigned char)o[0])))continue;
        memcpy(slot,o,mn);slot[mn]=0;
        k=lp_next(u,i,1);if(k<0)continue;
        if(lp_is(&u->lines[k],"and")&&lp_immediate(&u->lines[k])==255&&!u->lines[k].m8&&!u->lines[k].deleted){
            mask1=k;k=lp_next(u,(unsigned)k,1);if(k<0)continue;
        }
        if(!lp_line_is(&u->lines[k],"clc")||u->lines[k].deleted)continue;
        clc1=k;adc1=lp_next(u,(unsigned)clc1,1);if(adc1<0)continue;
        if(!lp_is(&u->lines[adc1],"adc")||u->lines[adc1].m8||u->lines[adc1].deleted||u->lines[adc1].replace)continue;
        o=lp_operand(&u->lines[adc1],&an);
        if(!an||an>=64||o[0]!='#')continue;
        memcpy(imm,o,an);imm[an]=0;
        p=lp_next_carry(u,(unsigned)adc1);
        while(p>=0&&cnt<8){
            LpLine *cur=&u->lines[p];
            if(cur->deleted){p=lp_next_carry(u,(unsigned)p);continue;}
            if(lp_is(cur,"lda")&&lp_operand_is(cur,slot,mn)&&!cur->m8&&!cur->replace){
                int q=lp_next(u,(unsigned)p,1),end_q;
                if(mask1>=0){
                    if(q<0||!lp_is(&u->lines[q],"and")||lp_immediate(&u->lines[q])!=255||u->lines[q].m8)break;
                    q=lp_next(u,(unsigned)q,1);
                }
                if(q<0||!lp_line_is(&u->lines[q],"clc")||u->lines[q].deleted)break;
                end_q=lp_next(u,(unsigned)q,1);
                if(end_q<0||!lp_is(&u->lines[end_q],"adc")||u->lines[end_q].m8||u->lines[end_q].deleted||u->lines[end_q].replace)break;
                if(lp_operand_is(&u->lines[end_q],imm,an)&&!(u->lines[end_q].out&(LP_A|LP_N|LP_Z|LP_V))){
                    int d;for(d=p;d<=end_q;++d)if(u->lines[d].op)u->lines[d].deleted=1;
                    ++changed;break;
                }
                break;
            }
            if((cur->def&LP_C)||cur->call||cur->use==LP_ALL||lp_branch(cur)||
               lp_may_write(cur,slot,mn,2)||(mn>=2&&slot[mn-2]==','&&slot[mn-1]=='s'&&lp_stack_op(cur)))break;
            if(!lp_is(cur,"sta")&&!lp_is(cur,"stx")&&!lp_is(cur,"sty")&&!lp_is(cur,"stz")&&
               !lp_is(cur,"ldx")&&!lp_is(cur,"ldy"))break;
            ++cnt;p=lp_next_carry(u,(unsigned)p);
        }
    }
    return changed;
}
/* Propagate known clear carry only through a closed forward region. A
 * marked ADC was emitted from an unsigned sum whose range fits a word. */
static int lp_reuse_clear_carry(LpUnit *u,Function *f,size_t at)
{
    (void)f;(void)at;
    if(u->indirect||cg.parser->no_known_values||cg.parser->no_strength_reduction)return 0;
    for(unsigned i=1;i<u->count;++i){
        LpLine *adc=&u->lines[i];
        int clear;
        if(!lp_is(adc,"adc")||adc->m8||u->lines[i-1].length!=18||
           strncmp(u->lines[i-1].text,"; ADC cannot carry",18))continue;
        clear=lp_next(u,i,-1);
        if(clear<0||!lp_line_is(&u->lines[clear],"clc"))continue;
        for(unsigned j=i+1;j<u->count;++j){
            LpLine *l=&u->lines[j];
            if(l->label&&(!lp_fallthrough_label(l)&&l->length!=1))break;
            if(l->label&&!lp_inner_label(u,j,i+1,j))break;
            if(!l->op)continue;
            if(lp_line_is(l,"clc")){
                l->deleted=1;return 1;
            }
            if(l->call||l->indirect||l->use==LP_ALL||(l->def&LP_C)||
               ((lp_branch(l)||l->ends)&&l->target<=(int)j))break;
        }
    }
    return 0;
}
static int lp_slot_written_byte_clean(const LpUnit *u,const char *slot,unsigned off,unsigned read_at)
{
    unsigned i;int stores=0,safe_before=0;
    char adj_lo[16],adj_hi[16];
    snprintf(adj_lo,sizeof adj_lo,"a:$%04X,y",(off-1)&0xFFFFu);
    snprintf(adj_hi,sizeof adj_hi,"a:$%04X,y",(off+1)&0xFFFFu);
    for(i=0;i<u->count;++i){
        const LpLine *l=&u->lines[i];
        size_t n;const char *o;
        if(l->deleted)continue;
        if(l->replace)return 0;
        if(!l->op)continue;
        o=lp_operand(l,&n);
        if(n==9&&(!strncmp(o,adj_lo,9)||!strncmp(o,adj_hi,9)))return 0;
        if(lp_store_op(l)&&n==9&&!strncmp(o,slot,9)){
            int prev;long imm_v;
            if(l->m8)return 0;
            if(lp_is(l,"stz")){++stores;if(i<read_at)safe_before=1;continue;}
            if(!lp_is(l,"sta"))return 0;
            prev=lp_next(u,i,-1);
            if(prev>=0&&lp_is(&u->lines[prev],"lda")&&!u->lines[prev].m8&&(imm_v=lp_immediate(&u->lines[prev]))>=0&&imm_v<=255){
                ++stores;if(i<read_at)safe_before=1;continue;
            }
            /* Check all predecessors of the label right before l for lda #imm (<=255) */
            {
                unsigned lbl=i;
                while(lbl>0&&!u->lines[lbl-1].op) --lbl;
                if(lbl>0&&u->lines[lbl].label){
                    unsigned p,ok_all=1,seen=0;
                    for(p=0;p<u->count;++p){
                        int k;long pv;
                        if(u->lines[p].deleted||!u->lines[p].op)continue;
                        if(p+1==lbl&&!u->lines[p].ends){k=(int)p;}
                        else if(u->lines[p].target==(int)lbl&&(op_is(u->lines[p].op,"bra")||op_is(u->lines[p].op,"jmp"))){
                            k=lp_next(u,p,-1);
                        }else continue;
                        if(k<0||!lp_is(&u->lines[k],"lda")||u->lines[k].m8||(pv=lp_immediate(&u->lines[k]))<0||pv>255){ok_all=0;break;}
                        seen=1;
                    }
                    if(ok_all&&seen){++stores;if(i<read_at)safe_before=1;continue;}
                }
            }
            return 0;
        }
    }
    /* Ensure no control flow falls from entry without at least one prior write visible before loop/read */
    (void)safe_before;
    return stores>0;
}
static int lp_next_skip_modes(const LpUnit *u,unsigned k,int *mode_line)
{
    unsigned i=k;
    if(mode_line)*mode_line=-1;
    while(++i<u->count){
        const LpLine *l=&u->lines[i];
        if(l->deleted)continue;
        if(!l->length)return -1;
        if(l->text[0]==';')continue;
        if(!l->op&&((l->length==3&&!strncmp(l->text,".a8",3))||
                    (l->length==4&&!strncmp(l->text,".a16",4)))){
            if(mode_line&&*mode_line<0)*mode_line=(int)i;
            continue;
        }
        return l->op?(int)i:-1;
    }
    return -1;
}
static int lp_bool_slot_test(LpUnit *u,Function *f,size_t at)
{
    unsigned i;int changed=0;(void)f;(void)at;
    if(cg.lp_volatile||cg.lp_frame_address||u->indirect)return 0;
    lp_liveness(u);
    for(i=0;i+3<u->count;++i){
        LpLine *s0=&u->lines[i];
        int d0=-1,k1,k2,d1=-1,k3;unsigned off;size_t n;const char *o;char *end;char slot[16];
        if(s0->deleted||s0->replace||!lp_line_is(s0,"sep #$20"))continue;
        k1=lp_next_skip_modes(u,i,&d0);if(k1<0)continue;
        k2=lp_next_skip_modes(u,(unsigned)k1,NULL);if(k2<0)continue;
        k3=lp_next_skip_modes(u,(unsigned)k2,&d1);if(k3<0)continue;
        if(!lp_is(&u->lines[k1],"lda")||!lp_line_is(&u->lines[k2],"rep #$20")||
           (!lp_is(&u->lines[k3],"beq")&&!lp_is(&u->lines[k3],"bne")))continue;
        if(u->lines[k1].deleted||u->lines[k1].replace||u->lines[k2].deleted||u->lines[k2].replace)continue;
        if(u->lines[k2].out&(LP_A|LP_N|LP_V|LP_C))continue;
        o=lp_operand(&u->lines[k1],&n);
        if(n!=9||strncmp(o,"a:$",3)||o[7]!=','||o[8]!='y')continue;
        off=(unsigned)strtoul(o+3,&end,16);
        if(end!=o+7)continue;
        memcpy(slot,o,9);slot[9]=0;
        if(!lp_slot_written_byte_clean(u,slot,off,(unsigned)k1))continue;
        s0->deleted=1;u->lines[k2].deleted=1;
        if(d0>=0)u->lines[d0].deleted=1;
        if(d1>=0)u->lines[d1].deleted=1;
        u->lines[k1].m8=0;u->lines[k1].def=LP_A|LP_N|LP_Z;
        ++changed;
    }
    return changed;
}
typedef struct { char slot[64];unsigned shifts;signed char valid; } LpScaleState;
static int lp_scale_invalidated(const LpLine *l,const char *slot,size_t length)
{
    return lp_may_write(l,slot,length,2)||
        (slot[length-1]=='s'&&lp_stack_op(l))||
        (slot[length-1]=='y'&&(l->def&LP_Y))||
        lp_is(l,"tcd")||lp_is(l,"pld")||lp_is(l,"plb");
}
static int lp_match_scale_seq(const LpUnit *u,unsigned i,char *slot_out,unsigned *shifts_out,int *tx_out)
{
    const LpLine *l0=&u->lines[i];const char *o;size_t mn;int k;unsigned shifts=0;
    if(l0->deleted||l0->replace||l0->m8||!lp_is(l0,"lda")||lp_index_use(l0))return 0;
    o=lp_operand(l0,&mn);
    if(!mn||mn>=64||!lp_private(o,mn))return 0;
    memcpy(slot_out,o,mn);slot_out[mn]=0;
    k=lp_next(u,i,1);
    while(k>=0&&shifts<7&&!u->lines[k].deleted&&!u->lines[k].replace&&!u->lines[k].m8&&lp_line_is(&u->lines[k],"asl a")){
        ++shifts;k=lp_next(u,(unsigned)k,1);
    }
    if(!shifts||k<0||u->lines[k].deleted||u->lines[k].replace||u->lines[k].x8||!lp_is(&u->lines[k],"tax"))return 0;
    *shifts_out=shifts;*tx_out=k;return 1;
}
static int lp_cfg_scaled_index(LpUnit *u,Function *f,size_t at)
{
    LpScaleState *in,*out;
    int *plx_src;
    unsigned i;int changed=0,iter;
    (void)f;(void)at;
    if(!u->count||u->indirect||cg.parser->no_value_reuse)return 0;
    lp_liveness(u);
    in=allocate(u->count*sizeof *in);
    out=allocate(u->count*sizeof *out);
    plx_src=allocate(u->count*sizeof *plx_src);
    for(i=0;i<u->count;++i){in[i].valid=-1;out[i].valid=-1;plx_src[i]=-1;}
    /* Pair balanced straight-line phx ... plx regions free of non-phx/plx stack ops */
    for(i=0;i<u->count;++i){
        if(!u->lines[i].deleted&&lp_is(&u->lines[i],"phx")){
            int depth=1;unsigned m=i+1;
            while(m<u->count&&depth>0){
                const LpLine *cur=&u->lines[m];
                if(!cur->deleted){
                    if(cur->label||lp_branch(cur)||cur->ends||cur->call||cur->use==LP_ALL)break;
                    if(cur->op){
                        if(lp_is(cur,"phx"))++depth;
                        else if(lp_is(cur,"plx")){if(--depth==0){plx_src[m]=(int)i;break;}}
                        else if(lp_stack_op(cur)||lp_is(cur,"tsx")||lp_is(cur,"tsc"))break;
                    }
                }
                ++m;
            }
        }
    }
    in[0].valid=0;
    for(iter=0;iter<16;++iter){
        int diff=0;
        for(i=0;i<u->count;++i){
            LpScaleState cur={0};cur.valid=-1;
            if(i==0){cur.valid=0;}
            else if(u->lines[i].label){
                int p;
                if(!u->lines[i-1].ends&&out[i-1].valid>=0){cur=out[i-1];}
                for(p=u->lines[i].first_incoming;p>=0&&cur.valid!=0;p=u->lines[p].next_incoming){
                    if(u->lines[p].deleted)continue;
                    if(out[p].valid<0)continue;
                    if(cur.valid<0)cur=out[p];
                    else if(out[p].valid==0||cur.shifts!=out[p].shifts||strcmp(cur.slot,out[p].slot))cur.valid=0;
                }
            }else if(!u->lines[i-1].ends){cur=out[i-1];}
            else{cur.valid=0;}
            if(cur.valid<0)continue;
            if(memcmp(&in[i],&cur,sizeof cur)!=0){in[i]=cur;diff=1;}
            {
                LpScaleState nxt=cur;
                const LpLine *l=&u->lines[i];
                if(plx_src[i]>=0){
                    unsigned phx_i=(unsigned)plx_src[i];
                    if(in[phx_i].valid==1){
                        unsigned m;int ok=1;size_t mn=strlen(in[phx_i].slot);
                        for(m=phx_i+1;m<i;++m){
                            if(!u->lines[m].deleted&&lp_scale_invalidated(&u->lines[m],in[phx_i].slot,mn)){ok=0;break;}
                        }
                        if(ok)nxt=in[phx_i];else nxt.valid=0;
                    }else nxt.valid=0;
                }else if(!l->deleted&&l->op){
                    if((l->def&LP_X)||l->call||l->use==LP_ALL){
                        /* Allow tax ending a scaled sequence to establish new state when reached */
                        nxt.valid=0;
                    }else if(nxt.valid==1&&lp_scale_invalidated(l,nxt.slot,strlen(nxt.slot)))nxt.valid=0;
                }
                /* If l is `tax`, check if preceded immediately by `lda <slot>; asl^sh; tax`: */
                if(!l->deleted&&lp_is(l,"tax")&&!l->x8){
                    int k=lp_next(u,i,-1);unsigned sh2=0;
                    while(k>=0&&lp_line_is(&u->lines[k],"asl a")&&!u->lines[k].m8&&sh2<7){++sh2;k=lp_next(u,(unsigned)k,-1);}
                    if(sh2&&k>=0){
                        int tx;
                        if(lp_match_scale_seq(u,(unsigned)k,nxt.slot,&nxt.shifts,&tx)&&tx==(int)i)
                            nxt.valid=1;
                    }
                }
                if(memcmp(&out[i],&nxt,sizeof nxt)!=0){out[i]=nxt;diff=1;}
            }
        }
        if(!diff)break;
    }
    for(i=0;i<u->count;++i){
        char slot[64];unsigned sh=0;int tx=-1;
        if(in[i].valid!=1)continue;
        if(!lp_match_scale_seq(u,i,slot,&sh,&tx))continue;
        if(in[i].shifts!=sh||strcmp(in[i].slot,slot))continue;
        if(u->lines[tx].out&LP_FLAGS)continue;
        if(!(u->lines[tx].out&LP_A)){
            int k;for(k=(int)i;k<=tx;++k)if(u->lines[k].op)u->lines[k].deleted=1;
            ++changed;
        }else if(sh>=1){
            int k;for(k=(int)i;k<tx;++k)if(u->lines[k].op)u->lines[k].deleted=1;
            lp_set(&u->lines[tx],"    txa");
            ++changed;
        }
    }
    free(in);free(out);free(plx_src);
    return changed;
}
/* For a discarded postdecrement tested against zero, subtracting one
 * leaves carry set exactly when the previous unsigned bit pattern was
 * nonzero. Store the new word and branch on that same carry. */
static int lp_postdecrement_truth(LpUnit *u,Function *f,size_t at)
{
    (void)at;
    if(cg.lp_volatile||u->indirect||body_asm_statements(f->body))return 0;
    lp_liveness(u);
    for(unsigned i=0;i<u->count;++i){
        LpLine *load=&u->lines[i];
        if(!lp_is(load,"lda")||load->m8)continue;
        size_t n;const char *home=lp_operand(load,&n);
        int step=lp_next(u,i,1),test=step<0?-1:lp_next(u,(unsigned)step,1);
        int edge=test<0?-1:lp_next(u,(unsigned)test,1);
        if(edge<0||!lp_is(&u->lines[step],"dec")||!lp_operand_is(&u->lines[step],home,n)||
           !lp_is(&u->lines[test],"cmp")||lp_immediate(&u->lines[test])!=0||
           n<2||home[0]=='#'||lp_is_mmio_operand(home,n))continue;
        LpLine *branch=&u->lines[edge];
        if((!lp_is(branch,"beq")&&!lp_is(branch,"bne"))||branch->target<0||
           (branch->out&(LP_A|LP_FLAGS)))continue;
        size_t length;const char *dest=lp_operand(branch,&length);
        lp_set(&u->lines[step],"    sec\n    sbc #$0001");
        lp_set(&u->lines[test],"    sta %.*s",(int)n,home);
        lp_set(branch,"    %s %.*s",lp_is(branch,"bne")?"bcs":"bcc",(int)length,dest);
        return 1;
    }
    return 0;
}
static void lp_cleanup(LpRunner *runner,Function *f,size_t at,int relocated)
{
    static int (*const passes[])(LpUnit*,Function*,size_t)={lp_region_private_copies,lp_region_dead_stores,lp_forward_constants,lp_dead_workspace,lp_dead_code,lp_dead_push_pairs,lp_fold_steps,lp_y_forms,lp_const_branches,lp_unreachable,lp_push_offsets,lp_ax_reuse,lp_register_values,lp_add_overflow_branch,lp_byte_compare,lp_stack_sum_series};
    unsigned round,k;
    for(round=0;round<8;++round){
        int any=lp_run(runner,f,at,lp_demanded_masks)|lp_run(runner,f,at,lp_byte_region_modes);
        any|=lp_run(runner,f,at,lp_bool_slot_test);
        any|=lp_run(runner,f,at,lp_reuse_address_carry);
        any|=lp_run(runner,f,at,lp_dead_x_save);
        any|=lp_run(runner,f,at,lp_byte_rmw);
        any|=lp_run(runner,f,at,lp_memory_word_steps);
        any|=lp_run(runner,f,at,lp_swapped_word_mask);
        any|=lp_run(runner,f,at,lp_store_index_value);
        any|=lp_run(runner,f,at,lp_near_indirect);
        /* Keep operands in their original order until the stack frame is chosen */
        if(relocated){
            any|=lp_run(runner,f,at,lp_commute_saved_word);
            any|=lp_run(runner,f,at,lp_forward_named_word);
            any|=lp_run(runner,f,at,lp_test_saved_byte);
            any|=lp_run(runner,f,at,lp_relocated_word_steps);
            any|=lp_run(runner,f,at,lp_sink_word_step);
            any|=lp_run(runner,f,at,lp_boolean_join);
        }
        any|=lp_run(runner,f,at,lp_reloads);
        any|=lp_run(runner,f,at,lp_add_constants);
        any|=lp_run(runner,f,at,lp_private_copies);
        any|=lp_run(runner,f,at,relocated?lp_relocated_dead_stores:lp_private_dead_stores);
        for(k=0;k<sizeof passes/sizeof *passes;++k)any|=lp_run(runner,f,at,passes[k]);
        any|=lp_run(runner,f,at,lp_cfg_accumulator);
        any|=lp_run(runner,f,at,lp_cfg_index);
        any|=lp_run(runner,f,at,lp_reuse_scaled_index);
        any|=lp_run(runner,f,at,lp_cfg_scaled_index);
        any|=lp_run(runner,f,at,lp_advance_before_indexed_load);
        any|=lp_run(runner,f,at,lp_jump_threading);
        if(!any)break;
    }
}
/* A fixed access whose entire operand is mirrored in bank $80 */
static unsigned lp_mmio_mirror(const LpLine *l)
{
    size_t n;
    const char *p=lp_operand(l,&n);
    char *end;
    unsigned long address,last;
    if(n!=9||strncmp(p,"f:$",3))return 0;
    if(!lp_is(l,"sta")&&!lp_is(l,"lda")&&!lp_is(l,"adc")&&!lp_is(l,"sbc")&&
       !lp_is(l,"and")&&!lp_is(l,"ora")&&!lp_is(l,"eor")&&!lp_is(l,"cmp"))return 0;
    address=strtoul(p+3,&end,16);
    if(end!=p+n||(address>>16)!=0)return 0;
    last=address+!l->m8;
    if((address>=0x2100&&last<=0x21ff)||(address>=0x4016&&last<=0x4017)||
       (address>=0x4200&&last<=0x437f))return (unsigned)address;
    return 0;
}

static int lp_mmio_return_fallthrough(const LpUnit *u,unsigned i)
{
    const LpLine *l=&u->lines[i];
    return lp_is(l,"jmp")&&l->target==(int)(i+1)&&
           !strncmp(u->lines[i+1].text,"return_",7);
}

typedef struct {int bytes,cycles;} LpMmioSavings;

static unsigned lp_mmio_page(const LpLine *l,unsigned address)
{
    if(!l->m8&&(address&0xff)==0xff)return 0;
    return address&0xff00;
}

/* Score and emit the same lowering, including loads made dead by STZ.
 * A zero page argument means the original D is left in place. */
static LpMmioSavings lp_mmio_lower(LpUnit *u,LpLine *ret,unsigned page,int bank,int emit)
{
    LpMmioSavings savings={-(page?6:0)-(bank?5:0),-(page?19:0)-(bank?13:0)};
    LpLine *zero=NULL;
    int zero_only_stores=0;
    unsigned i;
    for(i=0;i<u->count;++i){
        LpLine *l=&u->lines[i];
        unsigned address;
        int direct,shorten,stz;
        if(!l->op)continue;
        if(lp_mmio_return_fallthrough(u,i)){
            if(emit)l->deleted=1;
            continue;
        }
        address=lp_mmio_mirror(l);
        direct=address&&page&&lp_mmio_page(l,address)==page;
        shorten=direct||(address&&bank);
        stz=shorten&&lp_is(l,"sta")&&zero&&l->m8==zero->m8;
        if(shorten){
            savings.bytes+=1+direct;
            savings.cycles+=1+direct;
            if(emit){
                const char *op=stz?"stz":l->op;
                /* Four digits distinguish MMIO offsets from the ABI's
                 * two-digit direct-page workspace operands. */
                if(direct)lp_set(l,"    %.3s z:$%04X",op,address-page);
                else lp_set(l,"    %.3s a:$%04X",op,address);
            }
        }
        if(stz){
            zero_only_stores=1;
            continue;
        }
        if(zero&&zero_only_stores&&
           ((lp_is(l,"lda")&&(zero->m8||!l->m8))||(l==ret&&!cg.lp_value_result))){
            savings.bytes+=zero->m8?2:3;
            savings.cycles+=zero->m8?2:3;
            if(emit)zero->deleted=1;
        }
        /* REP can precede a void return without consuming the zero */
        if(lp_line_is(l,"rep #$20"))continue;
        zero=lp_is(l,"lda")&&lp_immediate(l)==0?l:NULL;
        zero_only_stores=0;
    }
    return savings;
}

/* Scope D and/or DBR to a straight-line leaf with only fixed mirrored
 * operands. No branch or PHP can observe the flags changed by PLD/PLB. */
static int lp_mmio_addressing(LpUnit *u,Function *f,size_t at)
{
    LpLine *first=NULL,*ret=NULL;
    unsigned pages[256]={0},i,count=0,best_page=0;
    int can_dp=1,bank,best_bank=0;
    LpMmioSavings best={0,0};
    (void)at;
    if(u->calls||u->indirect||statement_inline_markers(f->body))return 0;
    for(i=0;i<u->count;++i){
        LpLine *l=&u->lines[i];
        unsigned address;
        size_t n;
        if(!l->op){
            if(first&&l->label&&strncmp(l->text,"return_",7))return 0;
            continue;
        }
        if(ret)return 0;
        if(!first)first=l;
        if(lp_is(l,"rts")||lp_is(l,"rtl"))ret=l;
        else if((address=lp_mmio_mirror(l))!=0){
            ++count;
            ++pages[lp_mmio_page(l,address)>>8];
        }else if(lp_mmio_return_fallthrough(u,i))continue;
        else if(lp_line_is(l,"sep #$20")||lp_line_is(l,"rep #$20"))continue;
        else if(lp_has_immediate(l)&&lp_immediate(l)>=0)continue;
        else{
            /* Reject stack use and memory operands that depend on the
             * original D or DBR. TDC/TCD also preclude changing D. */
            lp_operand(l,&n);
            if(n||l->use==LP_ALL||l->ends||lp_stack_op(l)||lp_is(l,"tsc")||lp_is(l,"tsx"))return 0;
            if(lp_is(l,"tdc")||lp_is(l,"tcd"))can_dp=0;
        }
    }
    if(!count||!ret)return 0;
    for(i=0;i<256;++i){
        if(i&&(!can_dp||!pages[i]))continue;
        for(bank=i==0;bank<=1;++bank){
            LpMmioSavings trial=lp_mmio_lower(u,ret,i<<8,bank,0);
            if(trial.bytes>0&&(trial.cycles>best.cycles||
               (trial.cycles==best.cycles&&trial.bytes>best.bytes&&trial.cycles>0))){
                best=trial;
                best_page=i<<8;
                best_bank=bank;
            }
        }
    }
    if(!best.cycles)return 0;
    /* The entry ABI supplies DBR=$7E, so one PEA provides both PLBs */
    if(best_bank)lp_insert(first,"    pea $7E80\n    plb\n");
    if(best_page){
        char setup[40];
        snprintf(setup,sizeof setup,"    phd\n    pea $%04X\n    pld\n",best_page);
        lp_insert(first,setup);
        lp_insert(ret,"    pld\n");
    }
    if(best_bank)lp_insert(ret,"    plb\n");
    lp_mmio_lower(u,ret,best_page,best_bank,1);
    return 1;
}

/* In a sentinel scan the cursor's only update is by a fixed word stride.
 * Carry it across the backedge in X. Keep the private memory home current
 * at each iteration and reproduce the loaded word's condition flags. */
static int lp_word_scan_cursor(LpUnit *u,Function *f,size_t at)
{
    (void)at;
    if(u->indirect||cg.lp_volatile||cg.parser->no_register_cursors||body_asm_statements(f->body))return 0;
    lp_liveness(u);
    for(unsigned i=0;i<u->count;++i){
        LpLine *load=&u->lines[i];size_t n;const char *home=lp_operand(load,&n);
        if(!lp_is(load,"ldx")||load->m8||load->x8||lp_workspace_word(home,n)<0)continue;
        int seq[5],k=(int)i;unsigned count=0,back;
        for(;count<5&&(k=lp_next(u,(unsigned)k,1))>=0;++count)seq[count]=k;
        if(count!=5||!lp_line_is(&u->lines[seq[0]],"txa")||
           !lp_line_is(&u->lines[seq[1]],"inc a")||!lp_line_is(&u->lines[seq[2]],"inc a")||
           !lp_is(&u->lines[seq[3]],"sta")||!lp_operand_is(&u->lines[seq[3]],home,n)||
           !lp_line_is(&u->lines[seq[4]],"lda a:$0000,x")||(u->lines[seq[4]].out&(LP_X|LP_C)))continue;
        int head=lp_loop(u,i,&back);
        if(head<0||!u->lines[back].ends||back<=(unsigned)seq[4])continue;
        int valid=1;
        for(unsigned j=0;j<u->count&&valid;++j){
            LpLine *l=&u->lines[j];
            if(j>=(unsigned)head&&j<i&&l->op)valid=0;
            if(j>(unsigned)seq[4]&&j<=back&&l->op&&((!lp_branch(l)&&!lp_is(l,"jmp"))||l->target<0))valid=0;
            if(l->target>=head&&l->target<=(int)back&&
               (j<(unsigned)head||j>back||(l->target<=(int)seq[4]&&
                (l->target!=head||j!=back))))valid=0;
        }
        if(!valid)continue;
        char setup[80];snprintf(setup,sizeof setup,"    ldx %.*s\n",(int)n,home);
        lp_insert(&u->lines[head],setup);
        lp_set(load,"    lda a:$0000,x");lp_set(&u->lines[seq[0]],"    inx");
        lp_set(&u->lines[seq[1]],"    inx");lp_set(&u->lines[seq[2]],"    stx %.*s",(int)n,home);
        lp_set(&u->lines[seq[3]],"    cmp #0");u->lines[seq[4]].deleted=1;
        return 1;
    }
    return 0;
}
/* A private promoted pointer can stay in an index register across a
 * single-entry loop when its only uses are marked post-update transfers.
 * Keep both homes coherent at the exit and save the incoming Y on the stack. */
typedef struct {
    unsigned load,access,step1,step2,store,slot;
} LpCursorTransfer;

static int lp_cursor_transfer(LpUnit *u,unsigned i,LpCursorTransfer *t)
{
    const char *home;
    size_t n;
    int a,b,c,d;
    int word;
    if(!i||!lp_is(&u->lines[i],"ldx")||
       strncmp(u->lines[i-1].text,post_cursor_marker,sizeof post_cursor_marker-1))return 0;
    home=lp_operand(&u->lines[i],&n);
    word=lp_workspace_word(home,n);
    if(word<0||word>30||(word&1))return 0;
    a=lp_next(u,i,1);b=a<0?-1:lp_next(u,(unsigned)a,1);
    c=b<0?-1:lp_next(u,(unsigned)b,1);d=c<0?-1:lp_next(u,(unsigned)c,1);
    if(d<0||!lp_operand_is(&u->lines[a],"a:$0000,x",9)||
       !(lp_is(&u->lines[a],"lda")||lp_is(&u->lines[a],"sta")||
         lp_is(&u->lines[a],"adc")||lp_is(&u->lines[a],"sbc")||
         lp_is(&u->lines[a],"and")||lp_is(&u->lines[a],"ora")||lp_is(&u->lines[a],"eor"))||
       !((lp_is(&u->lines[b],"inx")&&lp_is(&u->lines[c],"inx"))||
         (lp_is(&u->lines[b],"dex")&&lp_is(&u->lines[c],"dex")))||
       !lp_is(&u->lines[d],"stx")||!lp_operand_is(&u->lines[d],home,n))return 0;
    for(unsigned j=i;j<=(unsigned)d;++j)
        if(u->lines[j].m8||u->lines[j].x8)return 0;
    *t=(LpCursorTransfer){i,(unsigned)a,(unsigned)b,(unsigned)c,(unsigned)d,(unsigned)word/2};
    return 1;
}

/* Account for the extra PHY only for slots outside the loop's own
 * pushes. A reference spanning both regions cannot be moved safely. */
static int lp_cursor_stack(const LpLine *l,int *depth,int *adjust)
{
    size_t n;
    const char *o=lp_operand(l,&n);
    if(n>=2&&o[n-2]==','&&o[n-1]=='s'){
        char *end;
        long offset=strtol(o,&end,10);
        if(end!=o+n-2||offset<1||offset>255)return 0;
        if(offset>*depth){
            if(offset>253)return 0;
            *adjust=(int)offset+2;
        }else if(offset+lp_width(l)-1>*depth)return 0;
    }
    if(lp_line_is(l,"pha"))*depth+=l->m8?1:2;
    else if(lp_line_is(l,"pla"))*depth-=l->m8?1:2;
    else if(lp_stack_op(l))return 0;
    return *depth>=0;
}

static int lp_keep_post_cursors(LpUnit *u,Function *f,size_t at)
{
    unsigned latch;
    (void)f;(void)at;
    if(u->indirect||cg.lp_volatile||cg.parser->no_register_cursors||cg.parser->no_dp_homes)return 0;
    for(latch=0;latch<u->count;++latch)
        if(lp_line_is(&u->lines[latch],"sep #$20")||lp_line_is(&u->lines[latch],"rep #$20"))
            u->lines[latch].use=0;
    lp_liveness(u);
    for(latch=0;latch<u->count;++latch){
        LpLine *edge=&u->lines[latch];
        LpCursorTransfer transfers[16];
        unsigned start,exit,i,count=0,slots[2],slot_count=0;
        int valid=1,depth=0,depths[256],stack_adjust[256]={0};
        char setup[160],restore[120];
        if(edge->target<0||(unsigned)edge->target>=latch||edge->call)continue;
        start=(unsigned)edge->target;
        if(!lp_fallthrough_label(&u->lines[start])||u->lines[start].m8||u->lines[start].x8||
           (u->lines[start].live&(LP_X|LP_N|LP_Z)))continue;
        exit=latch+1;
        while(exit<u->count&&!u->lines[exit].op)++exit;
        if(exit-start>=256||exit==u->count||u->lines[exit].m8||u->lines[exit].x8||
           (u->lines[exit].live&(LP_X|LP_N|LP_Z)))continue;
        /* External jumps must bypass both the body and the register restore */
        for(i=0;i<u->count;++i){
            LpLine *l=&u->lines[i];
            if((i<start||i>latch)&&l->target>=(int)start&&l->target<=(int)exit)valid=0;
        }
        for(i=start;valid&&i<=latch;++i){
            LpLine *l=&u->lines[i];
            LpCursorTransfer t;
            unsigned j;
            depths[i-start]=depth;
            if(!l->op)continue;
            if(lp_cursor_transfer(u,i,&t)&&t.store<=latch&&count<16){
                for(j=0;j<slot_count&&slots[j]!=t.slot;++j){}
                if(j==slot_count){
                    if(slot_count==2){valid=0;break;}
                    slots[slot_count++]=t.slot;
                }
                transfers[count++]=t;
                for(j=i+1;j<=t.store;++j)depths[j-start]=depth;
                i=t.store;continue;
            }
            if(l->call||l->x8||l->use==LP_ALL||
               ((l->use|l->def)&(LP_X|LP_Y))||
               (l->target>=0&&(l->target<(int)start||l->target>(int)exit))||
               (l->ends&&l->target<0)||lp_is(l,"tcd")||lp_is(l,"pld")||
               lp_is(l,"plb")||lp_is(l,"mvn")||lp_is(l,"mvp")||lp_is(l,"tsc"))valid=0;
            if(!lp_cursor_stack(l,&depth,&stack_adjust[i-start]))valid=0;
        }
        if(!valid||depth||slot_count!=2)continue;
        for(i=latch+1;i<=exit;++i)depths[i-start]=0;
        for(i=start;valid&&i<=latch;++i){
            int target=u->lines[i].target;
            if(target>=0&&depths[target-(int)start]!=depths[i-start])valid=0;
        }
        for(i=start;valid&&i<=latch;++i){
            size_t n;
            const char *o=lp_operand(&u->lines[i],&n);
            unsigned j;
            for(j=0;j<count;++j)if(i==transfers[j].load){i=transfers[j].store;break;}
            if(j<count)continue;
            {
                int word=lp_workspace_word(o,n);
                if(word>=0){
                    if(lp_overlaps_n(&u->lines[i],word,2*(int)slots[0],2)||
                       lp_overlaps_n(&u->lines[i],word,2*(int)slots[1],2))valid=0;
                }else if(lp_text_words(o,o+n)&((1u<<slots[0])|(1u<<slots[1])))valid=0;
            }
        }
        if(!valid)continue;
        snprintf(setup,sizeof setup,"; retain private word cursors in X and Y\n"
                 "    phy\n    ldx z:__arith_lhs+%u\n    ldy z:__arith_lhs+%u\n",
                 slots[0]*2,slots[1]*2);
        snprintf(restore,sizeof restore,"    stx z:__arith_lhs+%u\n    sty z:__arith_lhs+%u\n    ply\n",
                 slots[0]*2,slots[1]*2);
        lp_insert(&u->lines[start],setup);
        lp_insert(&u->lines[exit],restore);
        for(i=start;i<=latch;++i)
            if(stack_adjust[i-start])lp_set(&u->lines[i],"    %.3s %d,s",u->lines[i].op,stack_adjust[i-start]);
        for(i=0;i<count;++i){
            LpCursorTransfer *t=&transfers[i];
            u->lines[t->load].deleted=1;
            u->lines[t->store].deleted=1;
            if(t->slot==slots[1]){
                const char *step=lp_is(&u->lines[t->step1],"inx")?"iny":"dey";
                lp_set(&u->lines[t->access],"    %.3s a:$0000,y",u->lines[t->access].op);
                lp_set(&u->lines[t->step1],"    %s",step);
                lp_set(&u->lines[t->step2],"    %s",step);
            }
        }
        return 1;
    }
    return 0;
}

enum { DIVIDER_WAIT_SLOTS=5 };
/* Match the compiler's hardware start, width restore and complete wait.
 * The first full-word result read may be either quotient or remainder. */
static int lp_divider_wait(const LpUnit *u,unsigned trigger,int *first)
{
    int rep,read;
    if(!lp_line_is(&u->lines[trigger],"sta f:$004206")||!u->lines[trigger].m8)return -1;
    rep=lp_next(u,trigger,1);
    if(rep<0||!lp_line_is(&u->lines[rep],"rep #$20")||
       (unsigned)(rep+2+DIVIDER_WAIT_SLOTS)>=u->count||
       strncmp(u->lines[rep+1].text,".a16\n",5))return -1;
    *first=rep+2;
    for(read=*first;read<*first+DIVIDER_WAIT_SLOTS;++read){
        const LpLine *wait=&u->lines[read];
        if(!lp_line_is(wait,"nop")&&!lp_line_is(wait,"inx")&&!lp_line_is(wait,"dex")&&
           !lp_line_is(wait,"iny")&&!lp_line_is(wait,"dey"))return -1;
    }
    if(u->lines[read].m8||
       (!lp_line_is(&u->lines[read],"lda f:$004214")&&!lp_line_is(&u->lines[read],"lda f:$004216")))return -1;
    return read;
}

/* Index steps take the same two cycles as NOP and do not change A or
 * carry. Move them across divider setup only inside a straight-line
 * region that never observes the index or the steps' N/Z results. */
static int lp_divider_index_wait(LpUnit *u,Function *f,size_t at)
{
    unsigned trigger;
    (void)f;(void)at;
    if(cg.lp_volatile||u->indirect||cg.parser->no_strength_reduction)return 0;
    for(trigger=0;trigger<u->count;++trigger){
        unsigned blocked=0,moved=0;
        int i,dividend=0,first,next=lp_divider_wait(u,trigger,&first);
        if(next<0||!lp_line_is(&u->lines[next],"lda f:$004216"))continue;
        for(i=first;i<next&&lp_line_is(&u->lines[i],"nop");++i){}
        if(i!=next)continue;
        for(i=(int)trigger-1;i>=0&&(int)trigger-i<=24;--i){
            LpLine *l=&u->lines[i];
            unsigned index;
            if(!l->op){
                if(l->text[0]==';'||!strncmp(l->text,".a8\n",4)||!strncmp(l->text,".a16\n",5))continue;
                break;
            }
            if(lp_line_is(l,"sep #$20")||lp_line_is(l,"rep #$20"))continue;
            if(l->x8||l->call||l->target>=0||l->ends||l->use==LP_ALL||l->use&(LP_N|LP_Z))break;
            if(lp_line_is(l,"sta f:$004204")&&!l->m8&&!dividend)dividend=1;
            else if(lp_mmio_mirror(l))break;
            index=lp_is(l,"inx")||lp_is(l,"dex")?LP_X:
                  lp_is(l,"iny")||lp_is(l,"dey")?LP_Y:0;
            if(dividend&&index&&!(blocked&index)&&!l->m8){
                lp_set(&u->lines[next-1-(int)moved],"    %.3s",l->op);
                l->deleted=1;
                if(++moved==DIVIDER_WAIT_SLOTS)break;
                continue;
            }
            blocked|=l->use|l->def;
        }
        if(moved)return 1;
    }
    return 0;
}

/* Forward an interleaved pair of saved word results. Copy the first
 * result to its final private home while it is still in A, then keep
 * the second result in A instead of reloading both temporary homes. */
static int lp_forward_interleaved_words(LpUnit *u,Function *f,size_t at)
{
    unsigned i;
    (void)f;(void)at;
    if(cg.lp_volatile||cg.parser->no_value_reuse)return 0;
    for(i=0;i<u->count;++i){
        LpLine *sequence[6];
        static const char *const ops[]={"sta","lda","sta","lda","sta","lda"};
        const char *operand[6];
        size_t length[6];
        unsigned j;
        int k=(int)i,first,second,destination,input;
        for(j=0;j<6&&k>=0;++j){
            LpLine *l=&u->lines[k];
            if(l->m8||!lp_is(l,ops[j]))break;
            sequence[j]=l;
            operand[j]=lp_operand(l,&length[j]);
            if(j<5)k=lp_next(u,(unsigned)k,1);
        }
        if(j!=6)continue;
        first=lp_workspace_word(operand[0],length[0]);
        second=lp_workspace_word(operand[2],length[2]);
        destination=lp_workspace_word(operand[4],length[4]);
        input=lp_workspace_word(operand[1],length[1]);
        if(first<0||second<0||destination<0||abs(first-second)<2||
           abs(first-destination)<2||abs(second-destination)<2||
           !lp_operand_is(sequence[3],operand[0],length[0])||
           !lp_operand_is(sequence[5],operand[2],length[2]))continue;
        if(input>=0){
            if(abs(input-destination)<2)continue;
        }else if(lp_immediate(sequence[1])<0){
            int producer=lp_next(u,i,-1);
            /* Only a latched divider quotient can be delayed here. The
             * preceding remainder read comes from the same operation. */
            if(producer<0||!lp_line_is(&u->lines[producer],"lda f:$004216")||
               !lp_line_is(sequence[1],"lda f:$004214"))continue;
        }
        lp_set(sequence[0],"    sta %.*s\n    sta %.*s",
               (int)length[0],operand[0],(int)length[4],operand[4]);
        sequence[3]->deleted=sequence[4]->deleted=sequence[5]->deleted=1;
        return 1;
    }
    return 0;
}

/* Both divider results are ready. Save the quotient before reading the
 * remainder when the next use reloads the remainder or the quotient
 * goes directly through a private cursor. The result homes are disjoint. */
static int lp_divider_remainder_last(LpUnit *u,Function *f,size_t at)
{
    unsigned trigger;
    (void)f;(void)at;
    if(cg.lp_volatile||u->indirect||cg.parser->no_value_reuse)return 0;
    lp_liveness(u);
    for(trigger=0;trigger<u->count;++trigger){
        int first,ready=lp_divider_wait(u,trigger,&first),q,store,tail,step;
        unsigned i,rem_words=0,quot_words=0;
        size_t n;
        const char *o;
        if(ready<0||!lp_line_is(&u->lines[ready],"lda f:$004216"))continue;
        i=(unsigned)ready;
        q=lp_next(u,i,1);
        while(q>=0&&lp_is(&u->lines[q],"sta")&&!u->lines[q].m8){
            int home;
            o=lp_operand(&u->lines[q],&n);home=lp_workspace_word(o,n);
            if(home<0||(home&1))break;
            rem_words|=1u<<(home/2);
            q=lp_next(u,(unsigned)q,1);
        }
        if(!rem_words||q<0||!lp_line_is(&u->lines[q],"lda f:$004214")||u->lines[q].m8)continue;
        store=lp_next(u,(unsigned)q,1);
        while(store>=0&&lp_is(&u->lines[store],"sta")&&!u->lines[store].m8){
            int home;
            o=lp_operand(&u->lines[store],&n);home=lp_workspace_word(o,n);
            if(home<0||(home&1))break;
            quot_words|=1u<<(home/2);
            store=lp_next(u,(unsigned)store,1);
        }
        if(store<1||(rem_words & quot_words)||u->lines[store].m8||u->lines[store].x8)continue;
        if(lp_is(&u->lines[store],"lda")){
            int home;
            o=lp_operand(&u->lines[store],&n);home=lp_workspace_word(o,n);
            if(home<0||(home&1)||!(rem_words&(1u<<(home/2))))continue;
            /* The reload already selects the remainder and its flags.
             * Read it from the divider here, after saving the quotient. */
            lp_set(&u->lines[store],"%.*s",
                   (int)(u->lines[q].text-u->lines[i].text-1),u->lines[i].text);
        }else{
            if(strncmp(u->lines[store-1].text,post_cursor_marker,sizeof post_cursor_marker-1)||
               !lp_line_is(&u->lines[store],"sta a:$0000,y"))continue;
            step=lp_next(u,(unsigned)store,1);
            tail=step<0?-1:lp_next(u,(unsigned)step,1);
            if(tail<0||!((lp_line_is(&u->lines[step],"iny")&&lp_line_is(&u->lines[tail],"iny"))||
                         (lp_line_is(&u->lines[step],"dey")&&lp_line_is(&u->lines[tail],"dey")))||
               (u->lines[tail].out&(LP_A|LP_N|LP_Z)))continue;
            lp_set(&u->lines[tail],"    %.3s\n%.*s",u->lines[tail].op,
                   (int)(u->lines[q].text-u->lines[i].text-1),u->lines[i].text);
        }
        for(;i<(unsigned)q;++i)u->lines[i].deleted=1;
        return 1;
    }
    return 0;
}

/* Seed a word load once when a loop latch already carries the same
 * private home in A. Reject alternate backedges to the load. */
static int lp_keep_loop_word_in_a(LpUnit *u,Function *f,size_t at)
{
    unsigned latch;
    (void)f;(void)at;
    if(u->indirect||cg.lp_volatile||cg.parser->no_value_reuse)return 0;
    lp_liveness(u);
    for(latch=0;latch<u->count;++latch){
        int head=u->lines[latch].target,load,producer;
        size_t n;
        const char *home;
        unsigned j;
        if(head<0||(unsigned)head>=latch||!lp_fallthrough_label(&u->lines[head]))continue;
        for(load=head+1;(unsigned)load<latch&&!u->lines[load].op;++load)
            if(u->lines[load].label||u->lines[load].text[0]!=';')break;
        if((unsigned)load>=latch||!lp_is(&u->lines[load],"lda")||u->lines[load].m8)continue;
        home=lp_operand(&u->lines[load],&n);
        for(j=0;j<u->count;++j)
            if(j!=latch&&u->lines[j].target>=head&&u->lines[j].target<=load)break;
        if(j!=u->count)continue;
        int update=lp_next(u,latch,-1);
        if(update>load&&!u->lines[update].m8&&lp_is(&u->lines[update],"sta")&&
           lp_private(home,n)&&lp_operand_is(&u->lines[update],home,n)&&
           lp_flags_from_a(u,lp_next(u,(unsigned)update,-1))){
            /* A and N/Z already hold the stored word on this backedge */
            char text[80];
            snprintf(text,sizeof text,"    lda %.*s\n",(int)n,home);
            lp_insert(&u->lines[head],text);
            u->lines[load].deleted=1;
            return 1;
        }
        if(update>load&&!u->lines[update].m8&&!(u->lines[load].out&LP_A)&&
           (lp_is(&u->lines[update],"inc")||lp_is(&u->lines[update],"dec"))&&pr_named(home,n)){
            size_t m;
            const char *updated=lp_operand(&u->lines[update],&m);
            if(lp_named_word_alias(home,n,updated,m)){
                /* Execute the load on entry. INC/DEC supply the same N/Z
                 * on the unique backedge and the loaded word is dead. */
                char *text=allocate(n+16);
                snprintf(text,n+16,"    lda %.*s\n",(int)n,home);
                lp_insert(&u->lines[head],text);free(text);
                u->lines[load].deleted=1;return 1;
            }
        }
        if((u->lines[load].out&(LP_N|LP_Z))||lp_workspace_word(home,n)<0)continue;
        /* Only cross consecutive labels with no incoming jumps. The
         * ordinary fallthrough enters these after the final A definition. */
        for(producer=(int)latch-1;producer>load;--producer){
            LpLine *l=&u->lines[producer];
            if(l->label){
                if(!lp_inner_label(u,(unsigned)producer,(unsigned)producer,(unsigned)producer))break;
                continue;
            }
            if(!l->op){if(l->text[0]!=';')break;continue;}
            if(!l->m8&&lp_is(l,"sta")&&lp_operand_is(l,home,n))break;
            if(l->m8||l->call||l->ends||(l->target>=0&&(unsigned)l->target<=latch)||
               (l->def&LP_A)||l->use==LP_ALL||lp_may_write(l,home,n,2))break;
            if(!lp_branch(l)&&!lp_is(l,"cmp")&&!lp_is(l,"cpx")&&!lp_is(l,"cpy")&&
               !lp_is(l,"dec")&&!lp_is(l,"inc")&&!lp_is(l,"inx")&&!lp_is(l,"dex")&&
               !lp_is(l,"iny")&&!lp_is(l,"dey")&&!lp_is(l,"nop"))break;
        }
        if(producer<=load||!lp_is(&u->lines[producer],"sta")||u->lines[producer].m8||
           !lp_operand_is(&u->lines[producer],home,n))continue;
        {
            char text[80];
            snprintf(text,sizeof text,"; carry private word in A across loop\n    lda %.*s\n",(int)n,home);
            lp_insert(&u->lines[head],text);
            u->lines[load].deleted=1;
        }
        return 1;
    }
    return 0;
}
/* A cleared byte takes the zero exit when its nonvolatile loop test is
 * reached immediately. Keep the clear, and preserve status on both edges. */
static int lp_cleared_byte_loop(LpUnit *u,Function *f,size_t at)
{
    (void)f;(void)at;
    if(cg.lp_volatile||u->indirect)return 0;
    int known,changed=0;
    unsigned char *targets=lp_local_targets(u,&known);
    lp_liveness(u);
    for(unsigned i=0;i<u->count&&!changed;++i){
        LpLine *clear=&u->lines[i];
        size_t n,m;
        const char *slot=lp_operand(clear,&n);
        if(!lp_is(clear,"stz")||!clear->m8||!pr_named(slot,n))continue;
        int restore=lp_next(u,i,1);
        if(restore<0||!lp_line_is(&u->lines[restore],"rep #$20")||
           (unsigned)restore+1>=u->count||u->lines[restore+1].length!=4||strncmp(u->lines[restore+1].text,".a16",4))continue;
        int latch=lp_next_fallthrough(u,(unsigned)restore+1,1,targets,known);
        if(latch<0||!lp_is(&u->lines[latch],"jmp"))continue;
        int head=u->lines[latch].target;
        if(head<0||(unsigned)head>=i)continue;
        int mode=lp_next(u,(unsigned)head,1);
        int load=mode<0?-1:lp_next_mode(u,(unsigned)mode);
        int wide=load<0?-1:lp_next(u,(unsigned)load,1);
        int branch=wide<0?-1:lp_next_mode(u,(unsigned)wide);
        if(branch<0||!lp_line_is(&u->lines[mode],"sep #$20")||!lp_is(&u->lines[load],"lda")||
           !u->lines[load].m8||!lp_operand_is(&u->lines[load],slot,n)||
           !lp_line_is(&u->lines[wide],"rep #$20")||!lp_line_is(&u->lines[branch],"bne :+"))continue;
        int after=-1,target=lp_cond_branch_target(u,branch,&after);
        if(target<0||after!=branch+2||(u->lines[target].live&(LP_AL|LP_N|LP_Z)))continue;
        const char *dest=lp_operand(&u->lines[branch+1],&m);
        lp_set(&u->lines[latch],"    jmp %.*s",(int)m,dest);changed=1;
    }
    free(targets);return changed;
}
static int lp_reduction_home_ok(const char *home,size_t hn)
{
    if(lp_workspace_word(home,hn)>=0)return 1;
    return lp_private(home,hn)&&!cg.lp_frame_address&&!lp_is_mmio_operand(home,hn);
}
static int lp_reduction_step(const LpUnit *u,unsigned i,const char **home_out,size_t *hn_out,
                             const char **src_out,size_t *sn_out,int *op_idx_out,int *store_idx_out,
                             const char *fixed_home,size_t fixed_hn,const char *fixed_op)
{
    const LpLine *load=&u->lines[i],*op,*store;
    int next,op_idx,st_idx;
    size_t hn,sn;
    const char *home,*src;
    if(load->deleted||load->replace||load->m8||load->x8||!lp_is(load,"lda"))return 0;
    src=lp_operand(load,&sn);
    if(!sn)return 0;
    next=lp_next(u,i,1);
    if(next<0)return 0;
    if(lp_line_is(&u->lines[next],"clc")){
        op_idx=lp_next(u,(unsigned)next,1);
        if(op_idx<0)return 0;
        op=&u->lines[op_idx];
        if(!lp_is(op,"adc"))return 0;
    }else{
        op_idx=next;
        op=&u->lines[op_idx];
        if(!lp_is(op,"and")&&!lp_is(op,"ora")&&!lp_is(op,"eor"))return 0;
    }
    if(op->deleted||op->replace||op->m8||op->x8)return 0;
    if(fixed_op&&!lp_is(op,fixed_op))return 0;
    home=lp_operand(op,&hn);
    if(!lp_reduction_home_ok(home,hn))return 0;
    if(fixed_home&&(hn!=fixed_hn||strncmp(home,fixed_home,hn)))return 0;
    st_idx=lp_next(u,(unsigned)op_idx,1);
    if(st_idx<0)return 0;
    store=&u->lines[st_idx];
    if(store->deleted||store->replace||store->m8||store->x8||
       !lp_is(store,"sta")||!lp_operand_is(store,home,hn))return 0;
    if(lp_operand_is(load,home,hn)||lp_may_write(store,src,sn,2))return 0;
    *home_out=home;*hn_out=hn;*src_out=src;*sn_out=sn;
    *op_idx_out=op_idx;*store_idx_out=st_idx;
    return 1;
}
/* Fuse straight-line sequences of two or more commutative DP/private word
 * reductions ("lda <src>; [clc]; <op> home; sta home") so A keeps the
 * running accumulator across the entire chain. */
static int lp_chain_reduction_in_a(LpUnit *u,Function *f,size_t at)
{
    unsigned i;
    (void)f;(void)at;
    if(u->indirect||cg.lp_volatile||cg.parser->no_value_reuse)return 0;
    lp_liveness(u);
    for(i=0;i<u->count;++i){
        const char *home=NULL,*srcs[32],*op_name;
        size_t hn=0,sns[32];
        int loads[32],ops[32],stores[32],count=0,next;
        char op_buf[4];
        if(!lp_reduction_step(u,i,&home,&hn,&srcs[0],&sns[0],&ops[0],&stores[0],NULL,0,NULL))continue;
        loads[0]=(int)i;
        snprintf(op_buf,sizeof op_buf,"%.3s",u->lines[ops[0]].op);
        op_name=op_buf;
        count=1;
        while(count<32&&(next=lp_next(u,(unsigned)stores[count-1],1))>=0){
            const char *h2=NULL;size_t hn2=0;
            if(!lp_reduction_step(u,(unsigned)next,&h2,&hn2,&srcs[count],&sns[count],
                                  &ops[count],&stores[count],home,hn,op_name))break;
            loads[count]=next;
            ++count;
        }
        if(count<2||(u->lines[stores[count-1]].out&LP_V))continue;
        lp_set(&u->lines[loads[0]],"    lda %.*s",(int)hn,home);
        for(int k=0;k<count;++k){
            if(k>0)u->lines[loads[k]].deleted=1;
            lp_set(&u->lines[ops[k]],"    %s %.*s",op_name,(int)sns[k],srcs[k]);
            if(k+1<count)u->lines[stores[k]].deleted=1;
        }
        return 1;
    }
    return 0;
}
/* Hoist the load and sink the store of a commutative DP/private word reduction
 * out of a single-block loop when the loop body and backedge preserve A. */
static int lp_keep_reduction_in_a(LpUnit *u,Function *f,size_t at)
{
    unsigned latch;
    int known_targets;
    unsigned char *targets;
    (void)f;(void)at;
    if(u->indirect||cg.lp_volatile||cg.parser->no_value_reuse)return 0;
    targets=lp_local_targets(u,&known_targets);
    lp_liveness(u);
    for(latch=0;latch<u->count;++latch){
        int head=u->lines[latch].target;
        unsigned j;
        int first_op=-1,red_load=-1,red_store=-1,is_chain=0;
        const char *home=NULL,*src=NULL;
        size_t hn=0,sn=0;
        int op_idx=-1;
        if(head<0||(unsigned)head>=latch||!known_targets||latch+1>=u->count)continue;
        if(!lp_branch(&u->lines[latch])||u->lines[latch].ends||(u->lines[latch].use&LP_A))continue;
        if(!lp_fallthrough_label(&u->lines[head]))continue;
        for(j=0;j<u->count;++j)
            if(j!=latch&&u->lines[j].target>=head&&u->lines[j].target<=(int)latch)break;
        if(j!=u->count)continue;
        for(j=(unsigned)head+1;j<latch;++j){
            const LpLine *l=&u->lines[j];
            if(l->deleted||l->replace)break;
            if(!l->op){if(l->label||l->text[0]!=';')break;continue;}
            if(l->m8||l->x8||l->ends||lp_branch(l)||l->call||lp_stack_op(l)||l->use==LP_ALL)break;
            if(first_op<0)first_op=(int)j;
        }
        if(j!=latch||first_op<0||(u->lines[first_op].use&(LP_A|LP_N|LP_Z|LP_C)))continue;
        for(j=(unsigned)first_op;j<latch;++j){
            const LpLine *l=&u->lines[j];
            if(!l->op||l->deleted)continue;
            if(red_load<0&&lp_reduction_step(u,j,&home,&hn,&src,&sn,&op_idx,&red_store,NULL,0,NULL)){
                red_load=(int)j;j=(unsigned)red_store;continue;
            }
            if(red_load<0&&lp_is(l,"lda")&&lp_reduction_home_ok(lp_operand(l,&hn),hn)){
                int cur=(int)j,last_st=-1,ok=1,steps=0;
                home=lp_operand(l,&hn);
                while(ok){
                    int nxt=lp_next(u,(unsigned)cur,1);
                    if(nxt<0||(unsigned)nxt>=latch){ok=0;break;}
                    if(lp_is(&u->lines[nxt],"sta")&&lp_operand_is(&u->lines[nxt],home,hn)){
                        last_st=nxt;break;
                    }
                    if(lp_line_is(&u->lines[nxt],"clc")){
                        int nxt2=lp_next(u,(unsigned)nxt,1);
                        if(nxt2<0||(unsigned)nxt2>=latch||!lp_is(&u->lines[nxt2],"adc")){ok=0;break;}
                        nxt=nxt2;
                    }else if(!lp_is(&u->lines[nxt],"and")&&!lp_is(&u->lines[nxt],"ora")&&!lp_is(&u->lines[nxt],"eor")){
                        ok=0;break;
                    }
                    if(lp_operand_is(&u->lines[nxt],home,hn)||
                       lp_may_write(&u->lines[nxt],home,hn,2)){ok=0;break;}
                    cur=nxt;++steps;
                }
                if(ok&&steps>0&&last_st>=0){
                    int alias=0;
                    for(int c=j+1;c<last_st;++c){
                        size_t cn;const char *co=lp_operand(&u->lines[c],&cn);
                        if(u->lines[c].op&&cn&&lp_may_write(&u->lines[last_st],co,cn,2)){alias=1;break;}
                    }
                    if(!alias){red_load=(int)j;red_store=last_st;is_chain=1;j=(unsigned)last_st;continue;}
                }
                home=NULL;hn=0;
            }
            if((l->use&LP_A)||(l->def&LP_A))break;
            if((l->use&LP_C)&&j+1<latch)break;
        }
        if(j!=latch||red_load<0||red_store<0||(u->lines[red_store].out&LP_V))continue;
        for(j=(unsigned)first_op;j<=latch;++j){
            const LpLine *l=&u->lines[j];
            size_t ln;const char *lo;
            if(!l->op||l->deleted||((int)j>=red_load&&(int)j<=red_store))continue;
            lo=lp_operand(l,&ln);
            if(lp_may_write(l,home,hn,2)||lp_operand_is(l,home,hn)||
               (ln&&lp_may_write(&u->lines[red_store],lo,ln,2)))break;
        }
        if(j<=latch)continue;
        {
            char enter_text[160],exit_text[160];
            snprintf(enter_text,sizeof enter_text,"    lda %.*s\n",(int)hn,home);
            snprintf(exit_text,sizeof exit_text,"    sta %.*s\n",(int)hn,home);
            lp_insert(&u->lines[head],enter_text);
            lp_insert(&u->lines[latch+1],exit_text);
            u->lines[red_load].deleted=1;
            u->lines[red_store].deleted=1;
            if(!is_chain)lp_set(&u->lines[op_idx],"    %.3s %.*s",u->lines[op_idx].op,(int)sn,src);
        }
        free(targets);
        return 1;
    }
    free(targets);
    return 0;
}

typedef struct {
    uint32_t read,write,live,out,update;
} LpWorkspaceLive;

static uint32_t lp_workspace_access(const LpLine *l,int *exact)
{
    size_t n;
    const char *o=lp_operand(l,&n);
    int offset=lp_workspace_word(o,n);
    uint32_t mask=0;
    *exact=0;
    if(offset<0&&n>3&&o[1]==':'&&o[2]=='$'&&(o[0]=='z'||o[0]=='a'||o[0]=='f')){
        char *end;
        unsigned long address=strtoul(o+3,&end,16);
        unsigned long bank=address>>16,low=address&65535;
        int start=(int)low-DP_SCRATCH_BASE,width=lp_width(l);
        if(start<32&&start+width>0&&(bank==0x7E||(bank&0x7F)<0x40)){
            if(end==o+n){
                *exact=1;
                if(start<0)return (1u<<(start+width))-1u;
                offset=start;
            }else if(lp_index_use(l))return UINT32_MAX;
        }
    }
    if(offset>=0){
        *exact=1;
        return ((1u<<lp_width(l))-1u)<<offset;
    }
    {
        int w=n>4&&o[0]=='('&&!strncmp(o+n-3,"),y",3)?lp_workspace_offset(o+1,n-4):-1;
        unsigned words=lp_text_words(o,o+n);
        if(w>=0&&!(w&1))return 3u<<w;
        if(words&&lp_index_use(l))return UINT32_MAX;
        for(unsigned i=0;i<16;++i)if(words&(1u<<i))mask|=3u<<(2*i);
    }
    return mask;
}

/* The arithmetic workspace is caller-clobbered. Unknown calls and
 * instructions may read every byte. During DSE a flag-dead update only
 * needs its input if a successor observes the written value. */
static void lp_workspace_liveness(LpUnit *u,LpWorkspaceLive *memory,int dead_updates)
{
    unsigned i;
    int changed;
    for(i=0;i<u->count;++i){
        LpLine *l=&u->lines[i];
        int exact;
        uint32_t access;
        if(!l->op||lp_line_is(l,"sep #$20")||lp_line_is(l,"rep #$20"))continue;
        if(l->call&&lp_callee(l))continue;
        if(l->call||l->use==LP_ALL){memory[i].read=UINT32_MAX;continue;}
        access=lp_workspace_access(l,&exact);
        if(exact&&(lp_is(l,"sta")||lp_is(l,"stx")||lp_is(l,"sty")||lp_is(l,"stz")))
            memory[i].write=access;
        else if(dead_updates&&exact&&(lp_is(l,"inc")||lp_is(l,"dec"))&&!(l->out&l->def))
            memory[i].write=memory[i].update=access;
        else memory[i].read=access;
    }
    do{
        changed=0;
        for(i=u->count;i-->0;){
            LpLine *l=&u->lines[i];
            uint32_t out=0,live;
            if(!l->ends)out=i+1<u->count?memory[i+1].live:UINT32_MAX;
            if(l->target>=0)out|=memory[l->target].live;
            live=memory[i].read|(out&~memory[i].write);
            if(out&memory[i].update)live|=memory[i].update;
            if(live!=memory[i].live||out!=memory[i].out)changed=1;
            memory[i].live=live;memory[i].out=out;
        }
    }while(changed);
}

/* A short conditional update can keep the saved word in A. Reorder
 * the commutative add once the branch and the intervening memory
 * update are proved to preserve A and exclude alternate entries. */
static int lp_forward_conditional_word(LpUnit *u,Function *f,size_t at)
{
    unsigned i;
    (void)f;(void)at;
    if(u->indirect||cg.lp_volatile||cg.parser->no_value_reuse)return 0;
    for(i=0;i<u->count;++i){
        LpLine *save=&u->lines[i];
        int branch,exit,start,jump,load,clear,add;
        size_t n,m;
        const char *home=lp_operand(save,&n),*other;
        if(!lp_is(save,"sta")||save->m8||lp_workspace_word(home,n)<0)continue;
        branch=lp_next(u,i,1);
        if(branch<0||!lp_branch(&u->lines[branch])||u->lines[branch].ends||
           u->lines[branch].target<=branch)continue;
        exit=u->lines[branch].target;
        start=branch+1;
        jump=lp_next(u,(unsigned)branch,1);
        if(jump>=0&&u->lines[jump].ends&&!u->lines[jump].call&&
           u->lines[jump].target>exit&&jump+1==exit){
            start=exit;
            exit=u->lines[jump].target;
        }
        for(;start<exit&&!u->lines[start].op;++start){
            const LpLine *l=&u->lines[start];
            if(l->label){
                if(!lp_inner_label(u,(unsigned)start,(unsigned)branch,(unsigned)branch+1))break;
            }else if(l->text[0]!=';')break;
        }
        if(start>=exit||u->lines[start].m8)continue;
        if(lp_is(&u->lines[start],"lda"))load=start;
        else{
            LpLine *update=&u->lines[start];
            if(lp_is(update,"dec")||lp_is(update,"inc")){
                int exact;
                uint32_t changed=lp_workspace_access(update,&exact);
                uint32_t saved=3u<<lp_workspace_word(home,n);
                if((update->def&LP_A)||(changed&saved))continue;
            }else if(!lp_is(update,"inx")&&!lp_is(update,"dex")&&
                     !lp_is(update,"iny")&&!lp_is(update,"dey"))continue;
            load=lp_next(u,(unsigned)start,1);
        }
        clear=load<0?-1:lp_next(u,(unsigned)load,1);
        add=clear<0?-1:lp_next(u,(unsigned)clear,1);
        if(add<0||add>=exit||u->lines[load].m8||u->lines[add].m8||
           !lp_is(&u->lines[load],"lda")||!lp_line_is(&u->lines[clear],"clc")||
           !lp_is(&u->lines[add],"adc")||!lp_operand_is(&u->lines[add],home,n))continue;
        other=lp_operand(&u->lines[load],&m);
        if(!lp_private(other,m)&&lp_immediate(&u->lines[load])<0)continue;
        lp_insert(save,"; conditional word save\n");
        u->lines[load].deleted=1;
        lp_set(&u->lines[add],"    adc %.*s",(int)m,other);
        return 1;
    }
    return 0;
}

static int lp_fixed_workspace(const LpUnit *u)
{
    for(unsigned i=0;i<u->count;++i){
        const LpLine *l=&u->lines[i];
        if(lp_is(l,"tcd")||lp_is(l,"pld")||lp_is(l,"plb")||lp_is(l,"xce"))return 0;
    }
    return 1;
}

/* A register argument already spilled in the opposite operand order can feed
 * a commutative add directly. Later DSE removes the unused A spill. */
static int lp_commute_spilled_add(LpUnit *u,Function *f,size_t at)
{
    (void)f;(void)at;
    if(u->indirect||cg.lp_volatile||cg.parser->no_value_reuse||!lp_fixed_workspace(u))return 0;
    for(unsigned i=0;i<u->count;++i){
        int save=lp_next(u,i,1);
        int copy=save<0?-1:lp_next(u,(unsigned)save,1);
        int clear=copy<0?-1:lp_next(u,(unsigned)copy,1);
        int add=clear<0?-1:lp_next(u,(unsigned)clear,1);
        size_t n,m;
        const char *x=lp_operand(&u->lines[i],&n),*a;
        int xslot,aslot;
        if(add<0||!lp_is(&u->lines[i],"stx")||u->lines[i].x8||
           (xslot=lp_workspace_word(x,n))<0||!lp_is(&u->lines[save],"sta")||
           u->lines[save].m8||u->lines[add].m8||
           !lp_line_is(&u->lines[copy],"txa")||!lp_line_is(&u->lines[clear],"clc")||
           !lp_is(&u->lines[add],"adc"))continue;
        a=lp_operand(&u->lines[save],&m);
        aslot=lp_workspace_word(a,m);
        if(aslot<0||abs(xslot-aslot)<2||!lp_operand_is(&u->lines[add],a,m))continue;
        lp_set(&u->lines[add],"    adc %.*s",(int)n,x);
        u->lines[copy].deleted=1;
        return 1;
    }
    return 0;
}

/* Fuse the saved trip counter with the retained X displacement. The typed
 * emitter proves that the loop cannot need more than one period of 2*i. */
static int lp_scaled_word_latch(LpUnit *u,Function *f,size_t at)
{
    unsigned i,used,slot;
    int known;
    unsigned char *targets;
    (void)f;(void)at;
    if(u->indirect||cg.lp_volatile||cg.parser->no_index_elimination||!lp_fixed_workspace(u))return 0;
    used=lp_text_words(u->text,u->text+strlen(u->text));
    for(slot=0;slot<16&&(used&(1u<<slot));++slot){}
    if(slot==16)return 0;
    targets=lp_local_targets(u,&known);
    lp_liveness(u);
    if(known)for(i=1;i+3<u->count;++i){
        LpLine *dec=&u->lines[i];
        int beq,jump,head,x,shift,seed,save,sub,sec,bound,push,pull,restore,step,first;
        size_t n,m;
        const char *index;
        if(!lp_line_is(dec,"dec z:$0000")||dec->m8||dec->x8||(dec->out&(LP_C|LP_N))||
           strncmp(u->lines[i-1].text,"; word-array loop distance fits 32768\n",
                   sizeof "; word-array loop distance fits 32768\n"-1))continue;
        beq=lp_next(u,i,1);
        jump=beq<0?-1:lp_next(u,(unsigned)beq,1);
        if(jump<0||!lp_line_is(&u->lines[beq],"beq :+")||!lp_is(&u->lines[jump],"jmp")||
           u->lines[beq].target!=jump+1)continue;
        head=u->lines[jump].target;
        if(head<0||head>=(int)i||(u->lines[head].live&LP_V))continue;
        step=lp_next_fallthrough(u,i,-1,targets,known);
        first=step<0?-1:lp_next_fallthrough(u,(unsigned)step,-1,targets,known);
        if(first<0||!lp_line_is(&u->lines[step],"inx")||!lp_line_is(&u->lines[first],"inx"))continue;
        x=lp_next_fallthrough(u,(unsigned)head,-1,targets,known);
        shift=x<0?-1:lp_next(u,(unsigned)x,-1);
        seed=shift<0?-1:lp_next(u,(unsigned)shift,-1);
        save=seed<0?-1:lp_next_fallthrough(u,(unsigned)seed,-1,targets,known);
        sub=save<0?-1:lp_next(u,(unsigned)save,-1);
        sec=sub<0?-1:lp_next(u,(unsigned)sub,-1);
        bound=sec<0?-1:lp_next(u,(unsigned)sec,-1);
        push=bound<0?-1:lp_next(u,(unsigned)bound,-1);
        if(push<0||!lp_line_is(&u->lines[push],"pei ($00)")||!lp_is(&u->lines[bound],"lda")||
           !lp_line_is(&u->lines[sec],"sec")||!lp_is(&u->lines[sub],"sbc")||
           !lp_line_is(&u->lines[save],"sta z:$0000")||!lp_is(&u->lines[seed],"lda")||
           !lp_line_is(&u->lines[shift],"asl a")||!lp_line_is(&u->lines[x],"tax"))continue;
        index=lp_operand(&u->lines[seed],&n);
        const char *limit=lp_operand(&u->lines[bound],&m);
        if(lp_workspace_word(index,n)<0||!lp_operand_is(&u->lines[sub],index,n)||
           lp_workspace_word(limit,m)<0)continue;
        /* The branch around the backedge is the only way into the restore */
        if(targets[jump+1]!=1)continue;
        pull=lp_next_fallthrough(u,(unsigned)jump+1,1,targets,known);
        restore=pull<0?-1:lp_next(u,(unsigned)pull,1);
        if(restore<0||!lp_line_is(&u->lines[pull],"pla")||
           !lp_line_is(&u->lines[restore],"sta z:$0000")||
           (u->lines[restore].out&(LP_A|LP_FLAGS)))continue;
        if(targets[head]!=1)continue;
        for(unsigned j=0;j<u->count;++j){
            int dest=u->lines[j].target;
            if((j<=(unsigned)push||j>=(unsigned)pull)&&dest>push&&dest<pull)goto next;
        }
        for(int k=push+1;k<pull;++k){
            const LpLine *l=&u->lines[k];
            size_t length;
            int exact;
            const char *operand=lp_operand(l,&length);
            if(!l->op)continue;
            if(l->m8||l->x8||l->use==LP_ALL||lp_stack_op(l)||lp_is(l,"tsx")||lp_is(l,"tsc")||
               (k>x&&k<first&&(l->def&LP_X))||
               (length>=2&&operand[length-2]==','&&operand[length-1]=='s')||
               (length>=5&&!memcmp(operand+length-5,",s),y",5))||
               (lp_workspace_access(l,&exact)&(3u<<(slot*2)))||
               (l->target>=0&&(l->target<head||l->target>jump+1))||
               (l->ends&&l->target<0))goto next;
        }
        u->lines[push].deleted=u->lines[sub].deleted=u->lines[pull].deleted=u->lines[restore].deleted=1;
        lp_set(&u->lines[sec],"    asl a");
        lp_set(&u->lines[save],"    sta z:__arith_lhs+%u",slot*2);
        u->lines[i-1].deleted=1;
        lp_insert(dec,"; scaled word-array end offset\n");
        lp_set(dec,"    cpx z:__arith_lhs+%u",slot*2);
        free(targets);
        return 1;
next:;
    }
    free(targets);
    return 0;
}

/* Track a saved word index through a straight-line sequence. A nearby
 * constant displacement needs only the remaining wrapping index steps. */
static int lp_saved_index_steps(LpUnit *u,Function *f,size_t at)
{
    (void)f;(void)at;
    if(u->indirect||cg.lp_volatile||cg.parser->no_private_regions)return 0;
    lp_liveness(u);
    for(unsigned i=0;i<u->count;++i){
        LpLine *save=&u->lines[i];
        size_t n;
        const char *home=lp_operand(save,&n);
        if(!lp_is(save,"stx")||save->x8||lp_workspace_word(home,n)<0)continue;
        int delta=0;
        for(int j=lp_next(u,i,1);j>=0;j=lp_next(u,(unsigned)j,1)){
            LpLine *l=&u->lines[j];
            if(l->m8||l->x8||l->target>=0||l->ends||l->call||lp_may_write(l,home,n,2))break;
            if(lp_line_is(l,"inx"))++delta;
            else if(lp_line_is(l,"dex"))--delta;
            else if(l->def&LP_X)break;
            else if(lp_is(l,"lda")&&lp_operand_is(l,home,n)){
                int carry=lp_next(u,(unsigned)j,1);
                int add=carry<0?-1:lp_next(u,(unsigned)carry,1);
                int move=add<0?-1:lp_next(u,(unsigned)add,1);
                if(move<0||!lp_line_is(&u->lines[carry],"clc")||!lp_is(&u->lines[add],"adc")||
                   !lp_line_is(&u->lines[move],"tax")||(u->lines[move].out&(LP_A|LP_C|LP_V)))break;
                long displacement=lp_immediate(&u->lines[add]);
                if(displacement<0)break;
                int steps=(int)(int16_t)(displacement-delta);
                if(steps<-2||steps>2||(!steps&&(u->lines[move].out&(LP_N|LP_Z))))break;
                l->deleted=u->lines[carry].deleted=u->lines[add].deleted=1;
                if(!steps)u->lines[move].deleted=1;
                else{
                    const char *step=steps<0?"dex":"inx";
                    if(steps==-2||steps==2)lp_set(&u->lines[move],"    %s\n    %s",step,step);
                    else lp_set(&u->lines[move],"    %s",step);
                }
                return 1;
            }
        }
    }
    return 0;
}
/* Fold a small word displacement into a scaled index after adding its
 * original base. The pointer and index still wrap at the same word width. */
static int lp_scaled_base_steps(LpUnit *u,Function *f,size_t at)
{
    (void)f;(void)at;
    if(u->indirect||cg.lp_volatile||cg.parser->no_private_regions)return 0;
    lp_liveness(u);
    for(unsigned i=0;i<u->count;++i){
        LpLine *base=&u->lines[i];
        size_t n,m;
        const char *p=lp_operand(base,&n);
        if(!lp_is(base,"lda")||base->m8||base->x8||lp_workspace_word(p,n)<0)continue;
        int first=lp_next(u,i,1),k=first,count=0;
        while(k>=0&&lp_line_is(&u->lines[k],"inc a")&&count<3){
            ++count;k=lp_next(u,(unsigned)k,1);
        }
        if(!count||k<0||!lp_is(&u->lines[k],"sta"))continue;
        int save=k;
        const char *q=lp_operand(&u->lines[save],&m);
        int slot=lp_workspace_word(q,m);
        k=lp_next(u,(unsigned)k,1);
        if(slot<0||k<0||(!lp_line_is(&u->lines[k],"tya")&&!lp_line_is(&u->lines[k],"txa")))continue;
        k=lp_next(u,(unsigned)k,1);
        while(k>=0&&lp_line_is(&u->lines[k],"asl a"))k=lp_next(u,(unsigned)k,1);
        if(k<0||!lp_line_is(&u->lines[k],"clc"))continue;
        int add=lp_next(u,(unsigned)k,1);
        if(add<0||!lp_is(&u->lines[add],"adc")||!lp_operand_is(&u->lines[add],q,m)||
           (u->lines[add].out&(LP_C|LP_V)))continue;
        LpWorkspaceLive *state=allocate(u->count*sizeof *state);
        lp_workspace_liveness(u,state,0);
        int dead=!(state[add].out&(3u<<slot));free(state);
        if(!dead)continue;
        for(k=(int)i;k<=save;++k)if(u->lines[k].op)u->lines[k].deleted=1;
        lp_set(&u->lines[add],"    adc %.*s%.*s",(int)n,p,10*count,
               "\n    inc a\n    inc a\n    inc a");
        return 1;
    }
    return 0;
}
/* Restore a once-stepped pointer index when its only saved use is a
 * direct-page indirect load. Reversing INX/DEX preserves word wrap. */
static int lp_restore_indirect_index(LpUnit *u,Function *f,size_t at)
{
    (void)f;(void)at;
    if(u->indirect||cg.lp_volatile||cg.parser->no_private_regions)return 0;
    lp_liveness(u);
    for(unsigned i=0;i<u->count;++i){
        LpLine *save=&u->lines[i];
        size_t n;
        const char *home=lp_operand(save,&n);
        int slot=lp_workspace_word(home,n);
        if(slot<0||save->x8||!lp_is(save,"stx"))continue;
        int step=lp_next(u,i,1);
        if(step<0||(!lp_line_is(&u->lines[step],"inx")&&!lp_line_is(&u->lines[step],"dex")))continue;
        for(int k=lp_next(u,(unsigned)step,1);k>=0;k=lp_next(u,(unsigned)k,1)){
            LpLine *l=&u->lines[k];
            size_t m;
            const char *address=lp_operand(l,&m);
            if(l->x8||l->m8||l->call||l->ends||lp_branch(l)||(l->def&LP_X)||l->use==LP_ALL)break;
            if(lp_is(l,"lda")&&m==n&&address[0]=='('&&address[m-1]==')'&&
               !memcmp(address+1,home+2,n-2)&&!(l->out&LP_X)){
                LpWorkspaceLive *state=allocate(u->count*sizeof *state);
                lp_workspace_liveness(u,state,0);
                int dead=!(state[k].out&(3u<<slot));free(state);
                if(!dead)break;
                save->deleted=1;
                lp_set(l,"    %s\n    lda a:$0000,x",lp_is(&u->lines[step],"inx")?"dex":"inx");
                return 1;
            }
            int exact;
            if(lp_workspace_access(l,&exact)&(3u<<slot))break;
        }
    }
    return 0;
}
/* Compare the two ends of a short index interval directly in X when
 * normalizing the index in A would spill an unrelated pointer. */
static int lp_preserved_range_pointer(LpUnit *u,Function *f,size_t at)
{
    (void)at;
    if(u->indirect||cg.lp_volatile||cg.parser->no_private_regions||cg.parser->no_value_reuse||
       body_asm_statements(f->body)||!lp_fixed_workspace(u))return 0;
    int known,changed=0;
    unsigned char *targets=lp_local_targets(u,&known);
    lp_liveness(u);
    for(unsigned i=0;i<u->count;++i){
        LpLine *store=&u->lines[i];
        size_t length;
        const char *home=lp_operand(store,&length);
        int word=lp_workspace_word(home,length);
        if(word<0||!lp_is(store,"sta")||store->m8||store->x8)continue;
        int move=lp_next(u,i,1),carry=move<0?-1:lp_next(u,(unsigned)move,1);
        int subtract=carry<0?-1:lp_next(u,(unsigned)carry,1);
        int compare=subtract<0?-1:lp_next(u,(unsigned)subtract,1);
        int branch=compare<0?-1:lp_next(u,(unsigned)compare,1),after=-1;
        int outside=lp_cond_branch_target(u,branch,&after);
        if(outside<0||after!=branch+2||!lp_line_is(&u->lines[branch],"bcc :+")||
           !lp_line_is(&u->lines[move],"txa")||!lp_line_is(&u->lines[carry],"sec")||
           !lp_is(&u->lines[subtract],"sbc")||!lp_is(&u->lines[compare],"cmp")||
           (u->lines[branch].out&LP_FLAGS)||(u->lines[outside].live&LP_A))continue;
        long base=lp_immediate(&u->lines[subtract]),span=lp_immediate(&u->lines[compare]);
        if(base<=0||span<=0||base>65535-span)continue;
        int reload=lp_next_fallthrough(u,(unsigned)after,1,targets,known);
        if(reload<0||!lp_is(&u->lines[reload],"ldx")||
           !lp_operand_is(&u->lines[reload],home,length)||(u->lines[reload].out&LP_A))continue;
        size_t n;
        const char *jump=lp_operand(&u->lines[branch+1],&n);
        lp_set(&u->lines[subtract],"    cpx #$%04lX\n    bcs :+\n    jmp %.*s\n:",base,(int)n,jump);
        lp_set(&u->lines[compare],"    cpx #$%04lX",base+span);
        lp_set(&u->lines[reload],"    tax");
        u->lines[move].deleted=u->lines[carry].deleted=1;
        changed=1;
        break;
    }
    free(targets);
    return changed;
}
/* A register-indexed word can be the ALU operand itself. Moving its read
 * across the private left-word load preserves the index and reads both once. */
static int lp_indexed_alu_rhs(LpUnit *u,Function *f,size_t at)
{
    (void)at;
    if(u->indirect||cg.lp_volatile||cg.parser->no_private_regions||body_asm_statements(f->body))return 0;
    for(unsigned i=0;i<u->count;++i){
        LpLine *load=&u->lines[i];
        size_t n,m,k;
        const char *operand=lp_operand(load,&n);
        if(!lp_is(load,"lda")||load->m8||load->x8||n!=9||strncmp(operand,"a:$",3)||
           operand[7]!=','||(operand[8]!='x'&&operand[8]!='y'))continue;
        int save=lp_next(u,i,1),lhs=save<0?-1:lp_next(u,(unsigned)save,1);
        int carry=lhs<0?-1:lp_next(u,(unsigned)lhs,1),op=carry<0?-1:lp_next(u,(unsigned)carry,1);
        if(op<0||!lp_is(&u->lines[save],"sta")||!lp_is(&u->lines[lhs],"lda")||
           !lp_line_is(&u->lines[carry],"sec")||!lp_is(&u->lines[op],"sbc"))continue;
        const char *scratch=lp_operand(&u->lines[save],&m),*left=lp_operand(&u->lines[lhs],&k);
        int word=lp_workspace_word(scratch,m);
        if(word<0||!lp_private(left,k)||lp_may_write(&u->lines[save],left,k,2)||
           !lp_operand_is(&u->lines[op],scratch,m))continue;
        LpWorkspaceLive *state=allocate(u->count*sizeof *state);
        lp_workspace_liveness(u,state,0);
        int dead=!(state[op].out&(3u<<word));
        free(state);
        if(dead){
            load->deleted=u->lines[save].deleted=1;
            lp_set(&u->lines[op],"    sbc %.*s",(int)n,operand);return 1;
        }
    }
    return 0;
}
static int lp_drop_dead_workspace_stores(LpUnit *u,Function *f,size_t at)
{
    LpWorkspaceLive *memory=NULL;
    unsigned i;
    int changed=0;
    (void)f;(void)at;
    if(u->indirect||cg.lp_volatile||cg.parser->no_value_reuse||!lp_fixed_workspace(u))return 0;
    for(i=0;i<u->count;++i){
        LpLine *l=&u->lines[i];
        size_t n;
        const char *o=lp_operand(l,&n);
        if((!lp_is(l,"sta")&&!lp_is(l,"stx")&&!lp_is(l,"sty")&&!lp_is(l,"stz")&&
            !lp_is(l,"inc")&&!lp_is(l,"dec"))||lp_workspace_word(o,n)<0)continue;
        if(!memory){
            lp_liveness(u);
            memory=allocate(u->count*sizeof *memory);
            lp_workspace_liveness(u,memory,1);
        }
        if(memory[i].write&&!(memory[i].out&memory[i].write)&&!(l->out&l->def)){
            l->deleted=1;
            changed=1;
        }
    }
    free(memory);return changed;
}

/* Once X carries the stack cursor along its complete backedge, the
 * workspace copy is unused by code outside that cursor. */
static int lp_dead_retained_varargs_cursor(LpUnit *u,Function *f,size_t at)
{
    (void)at;
    if(!f->uses_varargs||u->calls||u->indirect||cg.lp_volatile||
       cg.parser->no_private_regions||cg.parser->no_value_reuse||body_asm_statements(f->body))return 0;
    PrState *frames=NULL;
    int changed=0;
    for(unsigned i=0;i<u->count;++i){
        LpLine *save=&u->lines[i];
        size_t n;
        const char *home=lp_operand(save,&n);
        int slot=lp_workspace_word(home,n);
        if(slot<0||save->m8||save->x8||!lp_is(save,"sta"))continue;
        int add=lp_next(u,i,-1),clear=add<0?-1:lp_next(u,(unsigned)add,-1);
        int frame=clear<0?-1:lp_next(u,(unsigned)clear,-1),index=lp_next(u,i,1);
        if(frame<0||index<0||!lp_is(&u->lines[add],"adc")||
           !lp_line_is(&u->lines[clear],"clc")||!lp_line_is(&u->lines[frame],"tya")||
           !lp_line_is(&u->lines[index],"tax"))continue;
        long offset=lp_immediate(&u->lines[add]);
        if(offset<=(long)f->frame+2||offset>255)continue;
        int read=index+1,back=-1;
        for(; (unsigned)read<u->count&&!u->lines[read].op;++read){
            const LpLine *marker=&u->lines[read];
            if(!marker->length||marker->text[0]==';')continue;
            if(!lp_fallthrough_label(marker))break;
            if(marker->first_incoming>=0){
                if(back>=0||u->lines[marker->first_incoming].next_incoming>=0)break;
                back=marker->first_incoming;
            }
        }
        if((unsigned)read>=u->count||back<=read||!lp_line_is(&u->lines[read],"lda a:$0000,x")||
           (!lp_is(&u->lines[back],"jmp")&&!lp_is(&u->lines[back],"bra")))continue;
        int first=lp_next(u,(unsigned)read,1),second=first<0?-1:lp_next(u,(unsigned)first,1);
        int write=second<0?-1:lp_next(u,(unsigned)second,1);
        if(write<0||write>=back||!lp_line_is(&u->lines[first],"inx")||
           !lp_line_is(&u->lines[second],"inx")||!lp_is(&u->lines[write],"stx")||
           !lp_operand_is(&u->lines[write],home,n))continue;
        int j=write+1;
        for(;j<back;++j){
            const LpLine *line=&u->lines[j];
            if(line->m8||line->x8||line->use==LP_ALL||(line->def&LP_X))break;
            if(line->label&&!lp_inner_label(u,(unsigned)j,(unsigned)read,(unsigned)back))break;
        }
        if(j!=back)continue;
        if(!frames)frames=pr_states(u);
        if(!frames[frame].frame||!frames[read].frame)continue;
        uint32_t bits=3u<<slot;
        unsigned k=0;
        for(;k<u->count;++k){
            const LpLine *line=&u->lines[k];
            if(!line->op||k==i||(int)k==read||(int)k==write)continue;
            if(line->use==LP_ALL)break;
            int exact,within=lp_frame_indexed_offset(line,'y');
            if(within>0&&within<256&&frames[k].frame)continue;
            if(lp_workspace_access(line,&exact)&bits)break;
        }
        if(k!=u->count)continue;
        save->deleted=u->lines[write].deleted=1;
        changed=1;
        break;
    }
    free(frames);
    return changed;
}

/* A far pointer already on the hardware stack can be read using D=S.
 * Preserve D and rebase the pointer past PHD. PLD changes N/Z and a byte
 * load retains the accumulator high byte, so both must be dead. */
static int lp_far_stack_read(LpUnit *u,Function *f,size_t at)
{
    (void)at;
    if(u->indirect||cg.lp_volatile||body_asm_statements(f->body))return 0;
    lp_liveness(u);
    for(unsigned i=0;i<u->count;++i){
        LpLine *high=&u->lines[i];
        if(high->m8||!lp_is(high,"lda"))continue;
        size_t n;
        const char *operand=lp_operand(high,&n);
        char *end;
        long offset=strtol(operand,&end,10);
        if(n<3||end!=operand+n-2||strncmp(end,",s",2)||offset<3||offset>255)continue;
        int sh=lp_next(u,i,1),low=sh<0?-1:lp_next(u,(unsigned)sh,1);
        int sl=low<0?-1:lp_next(u,(unsigned)low,1),mode=sl<0?-1:lp_next(u,(unsigned)sl,1);
        if(mode<0||!lp_line_is(&u->lines[sh],"sta z:__arith_lhs+2")||
           !lp_is(&u->lines[low],"lda")||!lp_line_is(&u->lines[sl],"sta z:__arith_lhs")||
           !lp_line_is(&u->lines[mode],"sep #$20"))continue;
        operand=lp_operand(&u->lines[low],&n);
        if(strtol(operand,&end,10)!=offset-2||n<3||end!=operand+n-2||strncmp(end,",s",2))continue;
        int read=lp_next_mode(u,(unsigned)mode);
        if(read<0||!u->lines[read].m8||!lp_line_is(&u->lines[read],"lda [__arith_lhs]")||
           (u->lines[read].out&(LP_AH|LP_N|LP_Z)))continue;
        LpWorkspaceLive *memory=allocate(u->count*sizeof *memory);
        lp_workspace_liveness(u,memory,0);
        int live=(memory[read].out&15)!=0;
        free(memory);
        if(live)continue;
        lp_set(high,"    phd");lp_set(&u->lines[sh],"    tsc");lp_set(&u->lines[low],"    tcd");
        u->lines[sl].deleted=1;
        lp_set(&u->lines[read],"    lda [$%02lX]\n    pld",offset);
        return 1;
    }
    return 0;
}
/* An OR reduction can start with its last-produced operand still in A.
 * Keep its store for any other readers, then let workspace DSE remove it. */
static int lp_forward_or_chain(LpUnit *u,Function *f,size_t at)
{
    (void)f;(void)at;
    if(u->indirect||cg.lp_volatile||cg.parser->no_value_reuse||!lp_fixed_workspace(u))return 0;
    for(unsigned i=0;i<u->count;++i){
        LpLine *save=&u->lines[i];
        size_t n,m;
        const char *home=lp_operand(save,&n),*first;
        int load,combine;
        if(!lp_is(save,"sta")||save->m8||lp_workspace_word(home,n)<0)continue;
        load=lp_next(u,i,1);
        if(load<0||!lp_is(&u->lines[load],"lda")||u->lines[load].m8)continue;
        first=lp_operand(&u->lines[load],&m);
        if(lp_workspace_word(first,m)<0)continue;
        for(combine=lp_next(u,(unsigned)load,1);combine>=0;
            combine=lp_next(u,(unsigned)combine,1)){
            LpLine *op=&u->lines[combine];
            if(!lp_is(op,"ora")||op->m8)break;
            if(!lp_operand_is(op,home,n))continue;
            u->lines[load].deleted=1;
            lp_set(op,"    ora %.*s",(int)m,first);
            return 1;
        }
    }
    return 0;
}

/* Accumulator mode switches preserve carry. Look through them to a
 * straight-line overwrite when general register liveness is conservative. */
static int lp_carry_overwritten(const LpUnit *u,unsigned start)
{
    for(unsigned i=start+1;i<u->count;++i){
        const LpLine *l=&u->lines[i];
        if(lp_line_is(l,"sep #$20")||lp_line_is(l,"rep #$20"))continue;
        if(!l->op){
            if(l->text[0]==';'||!strncmp(l->text,".a8\n",4)||!strncmp(l->text,".a16\n",5))continue;
            return 0;
        }
        if(l->ends||l->call||l->target>=0||(l->use&LP_C))return 0;
        if(l->def&LP_C)return 1;
    }
    return 0;
}

/* If a shift-and-combine already has one input in A, shift it first.
 * The other input must be independent of the scratch store moved ahead
 * of its load. The final logical operation restores N/Z, but not carry. */
static int lp_forward_shifted_word(LpUnit *u,Function *f,size_t at)
{
    unsigned i;
    LpWorkspaceLive *memory=NULL;
    (void)f;(void)at;
    if(u->indirect||cg.lp_volatile||cg.parser->no_value_reuse||!lp_fixed_workspace(u))return 0;
    for(i=0;i<u->count;++i){
        LpLine *save=&u->lines[i];
        int load,left,stage,reload,right,combine,source,temporary,other_home;
        size_t n,m,other_n,used=0;
        const char *home=lp_operand(save,&n),*scratch,*other,*shift;
        unsigned count=0;
        char before[256];
        if(!lp_is(save,"sta")||save->m8||(source=lp_workspace_word(home,n))<0)continue;
        load=lp_next(u,i,1);
        if(load<0||u->lines[load].m8||!lp_is(&u->lines[load],"lda"))continue;
        other=lp_operand(&u->lines[load],&other_n);
        other_home=lp_workspace_word(other,other_n);
        if(other_home<0&&!(lp_private(other,other_n)&&other[other_n-1]=='s'))continue;
        left=lp_next(u,(unsigned)load,1);
        for(stage=left;stage>=0;stage=lp_next(u,(unsigned)stage,1))
            if(!lp_line_is(&u->lines[stage],"asl a")&&!lp_line_is(&u->lines[stage],"lsr a"))break;
        if(stage<0||stage==left||!lp_is(&u->lines[stage],"sta"))continue;
        scratch=lp_operand(&u->lines[stage],&m);
        temporary=lp_workspace_word(scratch,m);
        if(temporary<0||abs(source-temporary)<2||
           (other_home>=0&&abs(other_home-temporary)<2))continue;
        reload=lp_next(u,(unsigned)stage,1);
        if(reload<0||!lp_is(&u->lines[reload],"lda")||!lp_operand_is(&u->lines[reload],home,n))continue;
        right=lp_next(u,(unsigned)reload,1);
        if(right<0)continue;
        shift=lp_line_is(&u->lines[right],"lsr a")?"lsr a":"asl a";
        for(combine=right;combine>=0&&lp_line_is(&u->lines[combine],shift);
            combine=lp_next(u,(unsigned)combine,1))++count;
        if(!count||count>15||combine<0||!lp_operand_is(&u->lines[combine],scratch,m)||
           (!lp_is(&u->lines[combine],"ora")&&!lp_is(&u->lines[combine],"eor")&&
            !lp_is(&u->lines[combine],"and")))continue;
        if(!memory){
            lp_liveness(u);
            memory=allocate(u->count*sizeof *memory);
            lp_workspace_liveness(u,memory,0);
        }
        if((memory[combine].out&(3u<<temporary))||
           ((u->lines[combine].out&LP_C)&&!lp_carry_overwritten(u,(unsigned)combine)))continue;
        for(unsigned step=0;step<count;++step)
            used+=(size_t)snprintf(before+used,sizeof before-used,"    %s\n",shift);
        snprintf(before+used,sizeof before-used,"    sta %.*s\n",(int)m,scratch);
        lp_insert(&u->lines[load],before);
        u->lines[stage].deleted=u->lines[reload].deleted=1;
        for(;right<combine;++right)if(u->lines[right].op)u->lines[right].deleted=1;
        free(memory);
        return 1;
    }
    free(memory);
    return 0;
}

/* Compute a masked private word in unused divider wait slots, then
 * combine it with the result directly in A. Each replacement takes
 * at least as many cycles as the NOP it replaces. */
static int lp_divider_wait_mask(LpUnit *u,Function *f,size_t at)
{
    LpWorkspaceLive *memory=NULL;
    (void)f;(void)at;
    if(u->indirect||cg.lp_volatile||cg.parser->no_value_reuse||
       cg.parser->no_strength_reduction||!lp_fixed_workspace(u))return 0;
    for(unsigned trigger=0;trigger<u->count;++trigger){
        int first,ready=lp_divider_wait(u,trigger,&first),slot,result,stage,load,mask,join;
        size_t input_n,scratch_n,mask_n;
        const char *input,*scratch,*immediate;
        int input_home,scratch_home;
        uint32_t saved=0,input_bytes=0;
        if(ready<0)continue;
        for(slot=first;slot+2<ready;++slot)
            if(lp_line_is(&u->lines[slot],"nop")&&lp_line_is(&u->lines[slot+1],"nop")&&
               lp_line_is(&u->lines[slot+2],"nop"))break;
        if(slot+2>=ready)continue;
        result=ready;
        if(lp_line_is(&u->lines[ready],"lda f:$004214")){
            for(result=lp_next(u,(unsigned)ready,1);result>=0&&lp_is(&u->lines[result],"sta");
                result=lp_next(u,(unsigned)result,1)){
                int exact;
                size_t n;
                const char *o=lp_operand(&u->lines[result],&n);
                if(lp_workspace_word(o,n)<0)break;
                saved|=lp_workspace_access(&u->lines[result],&exact);
            }
        }
        if(result<0||!lp_line_is(&u->lines[result],"lda f:$004216"))continue;
        for(stage=lp_next(u,(unsigned)result,1);stage>=0;stage=lp_next(u,(unsigned)stage,1))
            if(!lp_line_is(&u->lines[stage],"asl a")&&!lp_line_is(&u->lines[stage],"lsr a"))break;
        if(stage<0||!lp_is(&u->lines[stage],"sta"))continue;
        scratch=lp_operand(&u->lines[stage],&scratch_n);
        scratch_home=lp_workspace_word(scratch,scratch_n);
        if(scratch_home<0)continue;
        load=lp_next(u,(unsigned)stage,1);
        mask=load<0?-1:lp_next(u,(unsigned)load,1);
        join=mask<0?-1:lp_next(u,(unsigned)mask,1);
        if(join<0||!lp_is(&u->lines[mask],"and")||
           lp_immediate(&u->lines[mask])<0||!lp_operand_is(&u->lines[join],scratch,scratch_n)||
           (!lp_is(&u->lines[join],"ora")&&!lp_is(&u->lines[join],"and")&&
            !lp_is(&u->lines[join],"eor")))continue;
        input=lp_operand(&u->lines[load],&input_n);
        input_home=lp_workspace_word(input,input_n);
        if(lp_is(&u->lines[load],"lda")){
            if(input_home<0||abs(input_home-scratch_home)<2)continue;
            input_bytes=3u<<input_home;
        }else{
            int k,from_x=lp_line_is(&u->lines[load],"txa");
            if(!from_x&&!lp_line_is(&u->lines[load],"tya"))continue;
            for(k=slot+3;k<ready;++k)
                if(lp_is(&u->lines[k],from_x?"inx":"iny")||
                   lp_is(&u->lines[k],from_x?"dex":"dey"))break;
            if(k<ready)continue;
        }
        if(saved&(input_bytes|(3u<<scratch_home)))continue;
        if(!memory){
            memory=allocate(u->count*sizeof *memory);
            lp_workspace_liveness(u,memory,0);
        }
        if(memory[join].out&(3u<<scratch_home))continue;
        immediate=lp_operand(&u->lines[mask],&mask_n);
        if(input_bytes)lp_set(&u->lines[slot],"    lda %.*s",(int)input_n,input);
        else lp_set(&u->lines[slot],"    %.3s",u->lines[load].op);
        lp_set(&u->lines[slot+1],"    and %.*s",(int)mask_n,immediate);
        lp_set(&u->lines[slot+2],"    sta %.*s",(int)scratch_n,scratch);
        u->lines[stage].deleted=u->lines[load].deleted=u->lines[mask].deleted=1;
        free(memory);
        return 1;
    }
    free(memory);
    return 0;
}

/* Only the low byte of this private load starts the divider. The
 * wait touches no part of A, and the first ready-result read overwrites
 * the full word before the old high byte can be observed. */
static int lp_narrow_divisor_load(LpUnit *u,Function *f,size_t at)
{
    unsigned i;
    (void)f;(void)at;
    if(cg.lp_volatile||u->indirect||cg.parser->no_strength_reduction)return 0;
    for(i=0;i+12<u->count;++i){
        LpLine *load=&u->lines[i];
        int sep=lp_next(u,i,1),trigger,first;
        size_t n;
        const char *operand=lp_operand(load,&n);
        if(!lp_is(load,"lda")||load->m8||!lp_private(operand,n)||sep<0||
           !lp_line_is(&u->lines[sep],"sep #$20")||
           (unsigned)sep+2>=u->count||strncmp(u->lines[sep+1].text,".a8\n",4))continue;
        trigger=lp_next(u,(unsigned)sep+1,1);
        if(trigger<0||lp_divider_wait(u,(unsigned)trigger,&first)<0)continue;
        lp_set(load,"    sep #$20\n.a8\n    lda %.*s",(int)n,operand);
        u->lines[sep].deleted=u->lines[sep+1].deleted=1;
        return 1;
    }
    return 0;
}

/* Drop straight-line stores to private frame locals right before teardown */
static int lp_frame_byte_private(Function *f,unsigned byte)
{
    unsigned i;
    for(i=0;i<cg.parser->symbol_count;++i){
        Symbol *v=&cg.parser->symbols[i];
        if(v->owner==f->id&&v->offset&&byte>=v->offset&&byte<v->offset+width(v->type))
            return loop_private(v)&&!object_volatile(v->type)&&!structure_object(v->type)&&
                   !v->type.array&&value_width(v->type)<=4;
    }
    return 1;
}
/* Keep a private argument in X while preparing other call operands */
static int lp_keep_frame_argument_in_x(LpUnit *u,Function *f,size_t at)
{
    (void)at;
    if(!f->slots||u->indirect||cg.parser->no_private_regions||
       cg.parser->no_value_reuse||body_asm_statements(f->body))return 0;
    for(unsigned i=0;i<(f->slots+1)/2&&i<384;++i)if(cg.frame_map[i])return 0;
    for(unsigned i=0;i<u->count;++i){
        size_t n;
        const char *operand=lp_operand(&u->lines[i],&n);
        if(lp_operand_has_s(operand,n))return 0;
    }
    int known;
    unsigned char *targets=lp_local_targets(u,&known);
    PrState *frames=pr_states(u);
    lp_liveness(u);
    int changed=0;
    for(unsigned i=0;i<u->count&&!changed;++i){
        LpLine *save=&u->lines[i];
        if(!lp_is(save,"sta")||save->m8||save->x8||!frames[i].frame||
           (save->out&(LP_N|LP_Z)))continue;
        int slot=lp_frame_indexed_offset(save,'y');
        if(slot<=0||(unsigned)(slot+1)>f->slots||!lp_frame_byte_private(f,(unsigned)slot)||
           !lp_frame_byte_private(f,(unsigned)slot+1))continue;
        int reload=(int)i;
        do{
            reload=lp_next_fallthrough(u,(unsigned)reload,1,targets,known);
            if(reload<0||(unsigned)reload>i+32){reload=-1;break;}
            LpLine *line=&u->lines[reload];
            if(lp_is(line,"ldx")&&!line->x8&&lp_frame_indexed_offset(line,'y')==slot)break;
            if(line->call||line->ends||lp_branch(line)||line->x8||
               ((line->use|line->def)&LP_X)){reload=-1;break;}
        }while(1);
        if(reload<0||!frames[reload].frame||(u->lines[reload].out&(LP_N|LP_Z)))continue;
        int exclusive=1;
        for(unsigned j=0;j<u->count&&exclusive;++j){
            if(j==i||j==(unsigned)reload)continue;
            int off=lp_frame_indexed_offset(&u->lines[j],'y');
            if(off>=0&&(!frames[j].frame||
               (off<=slot+1&&off+lp_width(&u->lines[j])>slot)))exclusive=0;
        }
        if(!exclusive)continue;
        lp_set(save,"    tax");
        u->lines[reload].deleted=1;
        changed=1;
    }
    free(frames);
    free(targets);
    return changed;
}
static int lp_dead_epilogue_stores(LpUnit *u,Function *f,size_t at)
{
    unsigned i;int changed=0;(void)at;
    if(cg.parser->no_private_regions||cg.lp_volatile||cg.lp_frame_address||u->indirect)return 0;
    for(i=0;i<u->count;++i){
        LpLine *l=&u->lines[i];size_t n;const char *o;char *end;
        unsigned off=0,w,k,steps=0;int is_y=0,dead=0;
        if(l->deleted||l->replace||l->call||!lp_is(l,"sta"))continue;
        w=(unsigned)lp_width(l);
        o=lp_operand(l,&n);
        if(n==9&&!strncmp(o,"a:$",3)&&o[7]==','&&o[8]=='y'){
            off=(unsigned)strtoul(o+3,&end,16);
            if(end!=o+7)continue;
            is_y=1;
        }else if(n>=3&&o[n-2]==','&&o[n-1]=='s'&&isdigit((unsigned char)o[0])){
            off=(unsigned)strtoul(o,&end,10);
            if(end!=o+n-2)continue;
            is_y=0;
        }else continue;
        if(!off||off+w-1>f->slots||!lp_frame_byte_private(f,off)||
           (w==2&&!lp_frame_byte_private(f,off+1)))continue;
        k=i+1;
        while(k<u->count&&steps++<64){
            LpLine *p=&u->lines[k];
            if(p->deleted){++k;continue;}
            if(p->replace||p->call)break;
            if(!p->op){
                if(!p->length||p->text[0]==';'||!strncmp(p->text,".a8",3)||!strncmp(p->text,".a16",4)||p->label){++k;continue;}
                break;
            }
            if(lp_is(p,"bra")||(lp_is(p,"jmp")&&p->target>=0)){
                if(p->target<0)break;
                k=(unsigned)p->target;continue;
            }
            if(lp_line_is(p,is_y?"tya":"tsc")){
                int c=lp_next(u,k,1),a=c<0?-1:lp_next(u,(unsigned)c,1),t=a<0?-1:lp_next(u,(unsigned)a,1);
                long freed;
                if(c>=0&&a>=0&&t>=0&&lp_line_is(&u->lines[c],"clc")&&lp_is(&u->lines[a],"adc")&&
                   !u->lines[a].m8&&(freed=lp_immediate(&u->lines[a]))>0&&lp_line_is(&u->lines[t],"tcs")){
                    if((unsigned long)(off+w-1)<=(unsigned long)freed)dead=1;
                }
                break;
            }
            if(p->ends||lp_branch(p)||lp_stack_op(p))break;
            if(is_y&&(p->def&LP_Y))break;
            if(lp_is(p,"sep")||lp_is(p,"rep")||lp_line_is(p,"clc")||lp_line_is(p,"sec")||
               lp_line_is(p,"tax")||lp_line_is(p,"txa")||(!is_y&&(lp_line_is(p,"tay")||lp_line_is(p,"tya")))||
               lp_line_is(p,"inc a")||lp_line_is(p,"dec a")||lp_line_is(p,"asl a")||lp_line_is(p,"lsr a")||
               lp_line_is(p,"xba")){++k;continue;}
            if(lp_is(p,"lda")||lp_is(p,"ldx")||lp_is(p,"sta")||lp_is(p,"stx")||lp_is(p,"stz")||
               lp_is(p,"adc")||lp_is(p,"sbc")||lp_is(p,"and")||lp_is(p,"ora")||lp_is(p,"eor")||lp_is(p,"cmp")){
                size_t pn;const char *po=lp_operand(p,&pn);
                if(pn&&po[0]=='#'){++k;continue;}
                if(lp_workspace_word(po,pn)>=0){++k;continue;}
                if(is_y&&pn==9&&!strncmp(po,"a:$",3)&&po[7]==','&&po[8]=='y'){
                    char *pe;unsigned po_off=(unsigned)strtoul(po+3,&pe,16),po_w=(unsigned)lp_width(p);
                    if(pe==po+7&&(po_off+po_w<=off||off+w<=po_off)){++k;continue;}
                }
            }
            break;
        }
        if(dead){l->deleted=1;changed=1;}
    }
    return changed;
}

/* A zero edge can bypass a dead frame counter step and the subsequent
 * repeat of the same two-word zero test. */
static int lp_skip_dead_loop_step(LpUnit *u,Function *f,size_t at)
{
    int known,matched=0;
    unsigned char *targets;
    (void)at;
    if(cg.lp_frame_address||cg.lp_volatile||cg.parser->no_private_regions||u->indirect||
       body_asm_statements(f->body))return 0;
    targets=lp_local_targets(u,&known);
    if(!known){free(targets);return 0;}
    for(unsigned i=0;i<u->count;++i){
        LpLine *edge=&u->lines[i];
        int after,join=lp_cond_branch_target(u,(int)i,&after);
        if(join<=(int)i||edge->m8||!lp_is(edge,after==(int)i?"beq":"bne"))continue;
        int first_or=lp_next(u,i,-1);
        int high=first_or<0?-1:lp_next(u,(unsigned)first_or,-1);
        int counter=lp_next_fallthrough(u,(unsigned)join,1,targets,known);
        int increment=counter<0?-1:lp_next(u,(unsigned)counter,1);
        int save=increment<0?-1:lp_next(u,(unsigned)increment,1);
        int reread=save<0?-1:lp_next_fallthrough(u,(unsigned)save,1,targets,known);
        int last_or=reread<0?-1:lp_next(u,(unsigned)reread,1);
        int repeat=last_or<0?-1:lp_next(u,(unsigned)last_or,1);
        int repeat_after,back=lp_cond_branch_target(u,repeat,&repeat_after);
        if(high<0||repeat<0||!lp_is(&u->lines[first_or],"ora")||
           (!lp_is(&u->lines[high],"lda")&&!lp_is(&u->lines[high],"sta"))||
           !lp_is(&u->lines[counter],"lda")||!lp_line_is(&u->lines[increment],"inc a")||
           !lp_is(&u->lines[save],"sta")||!lp_is(&u->lines[reread],"lda")||
           !lp_is(&u->lines[last_or],"ora")||back<0||back>=(int)i||
           !lp_is(&u->lines[repeat],repeat_after==repeat?"bne":"beq")||
           u->lines[counter].m8||u->lines[reread].m8||
           u->lines[repeat].m8)continue;
        int release=repeat_after+1;
        while((unsigned)release<u->count&&!u->lines[release].op)++release;
        int clear=(unsigned)release<u->count?lp_next(u,(unsigned)release,1):-1;
        int add=clear<0?-1:lp_next(u,(unsigned)clear,1);
        int set=add<0?-1:lp_next(u,(unsigned)add,1);
        if(set<0||!lp_line_is(&u->lines[release],"tya")||!lp_line_is(&u->lines[clear],"clc")||
           !lp_is(&u->lines[add],"adc")||!lp_line_is(&u->lines[set],"tcs"))continue;
        size_t n,upper_length,lower_length;
        const char *slot=lp_operand(&u->lines[counter],&n);
        const char *upper=lp_operand(&u->lines[high],&upper_length);
        const char *lower=lp_operand(&u->lines[first_or],&lower_length);
        if(n!=9||strncmp(slot,"a:$",3)||strncmp(slot+7,",y",2)||
           !lp_operand_is(&u->lines[save],slot,n)||!lp_private(upper,upper_length)||
           !lp_private(lower,lower_length)||!lp_operand_is(&u->lines[reread],upper,upper_length)||
           !lp_operand_is(&u->lines[last_or],lower,lower_length)||
           lp_may_write(&u->lines[save],lower,lower_length,2)||
           lp_may_write(&u->lines[save],upper,upper_length,2))continue;
        unsigned offset=(unsigned)strtoul(slot+3,NULL,16);
        if(!offset||offset+1>f->slots||(long)offset+1>lp_immediate(&u->lines[add])||
           !lp_frame_byte_private(f,offset)||!lp_frame_byte_private(f,offset+1))continue;
        unsigned label=++cg.label;
        char destination[96];
        snprintf(destination,sizeof destination,"cg_%s_%u = *\n",cg.parser->unit,label);
        lp_insert(&u->lines[release],destination);
        if(after==(int)i)lp_set(edge,"    beq cg_%s_%u",cg.parser->unit,label);
        else lp_set(&u->lines[i+1],"    jmp .loword(cg_%s_%u)",cg.parser->unit,label);
        matched=1;
        break;
    }
    free(targets);
    return matched;
}

static int lp_abs_x_operand(const char *o,size_t n)
{
    const char *comma;
    if(n<6||strncmp(o,"a:",2)||o[n-2]!=','||o[n-1]!='x')return 0;
    comma=memchr(o,',',n);
    return comma==o+n-2;
}
static int lp_can_wrap_fn_y(const LpUnit *u,const Function *f,unsigned *entry_out)
{
    unsigned i,entry=0,returns=0;
    if(f->symbol->interrupt||f->frame||u->indirect)return 0;
    while(entry<u->count&&!u->lines[entry].op)++entry;
    if(entry==u->count)return 0;
    for(i=entry;i<u->count;++i){
        const LpLine *l=&u->lines[i];
        size_t n;const char *o=lp_operand(l,&n);
        if(!l->op||l->deleted)continue;
        if(l->x8||(l->target>=0&&(unsigned)l->target<=entry))return 0;
        if(lp_is(l,"rti")||(l->call&&(lp_is(l,"jmp")||lp_is(l,"jml"))))return 0;
        if(lp_is(l,"rts")||lp_is(l,"rtl")){++returns;continue;}
        if(lp_is(l,"tcs")||lp_is(l,"txs")||lp_is(l,"tsc")||lp_is(l,"tsx")||lp_operand_has_s(o,n))return 0;
        if(!l->call&&!lp_line_is(l,"sep #$20")&&!lp_line_is(l,"rep #$20")&&
           (l->use==LP_ALL||((l->use|l->def)&LP_Y)))return 0;
    }
    if(!returns)return 0;
    *entry_out=entry;
    return 1;
}
/* Straight-line tax / (phx ... plx / sta|stz a:...,x)+ ending with dead X:
 * keep the saved index in Y and eliminate all X push/pull traffic. */
static int lp_y_saved_index(LpUnit *u,Function *f,size_t at)
{
    unsigned i,entry=0;
    int can_wrap_fn_y=!u->indirect&&lp_can_wrap_fn_y(u,f,&entry);
    (void)at;
    if(u->indirect)return 0;
    lp_liveness(u);
    for(i=0;i<u->count;++i){
        LpLine *tax=&u->lines[i];
        unsigned phxs[32],plxs[32],stores[32],saves=0,nstores=0,j;
        int in_save=0,x_clobbered=0,inner_x_def=0,done=0,y_live;
        if(!lp_line_is(tax,"tax")||tax->x8||tax->deleted||tax->replace||
           (tax->out&(LP_N|LP_Z)))continue;
        y_live=(tax->out&LP_Y)!=0;
        for(j=i+1;j<u->count&&!done;++j){
            LpLine *l=&u->lines[j];
            size_t n;const char *o=lp_operand(l,&n);
            if(l->deleted||l->replace||l->label)break;
            if(!l->op){
                if(!l->length)break;
                if(l->text[0]==';'||(l->length==3&&!strncmp(l->text,".a8",3))||
                   (l->length==4&&!strncmp(l->text,".a16",4)))continue;
                break;
            }
            if(l->x8||l->call||l->ends||lp_branch(l))break;
            if((l->use&LP_Y)||(l->def&LP_Y))break;
            if(l->use==LP_ALL&&!lp_line_is(l,"sep #$20")&&!lp_line_is(l,"rep #$20"))break;
            if(in_save){
                if(lp_line_is(l,"plx")){
                    if((l->out&(LP_N|LP_Z))||saves>=32)break;
                    plxs[saves++]=j;in_save=0;
                }else{
                    if(lp_stack_op(l)||lp_operand_has_s(o,n))break;
                    if((l->use&LP_X)&&x_clobbered&&!inner_x_def)break;
                    if((l->def&LP_X)&&!(l->use&LP_X))inner_x_def=1;
                    if(l->def&LP_X)x_clobbered=1;
                }
            }else{
                if(lp_line_is(l,"phx")){
                    if(saves>=32)break;
                    phxs[saves]=j;in_save=1;inner_x_def=0;
                }else if((lp_is(l,"sta")||lp_is(l,"stz")||lp_is(l,"lda")||lp_is(l,"adc")||
                          lp_is(l,"sbc")||lp_is(l,"and")||lp_is(l,"ora")||lp_is(l,"eor")||
                          lp_is(l,"cmp"))&&!(l->def&LP_X)&&lp_abs_x_operand(o,n)){
                    if(lp_is(l,"stz")&&(!l->m8||(l->out&(LP_A|LP_N|LP_Z))))break;
                    if(nstores>=32)break;
                    stores[nstores++]=j;
                    if(!(l->out&LP_X)){done=1;break;}
                }else if(lp_line_is(l,"sep #$20")||lp_line_is(l,"rep #$20")){
                    continue;
                }else if(!(l->use&LP_X)&&!(l->def&LP_X)&&!lp_stack_op(l)&&!lp_operand_has_s(o,n)){
                    continue;
                }else break;
            }
        }
        if(done&&!in_save&&saves>0&&nstores>0){
            unsigned k;
            if(y_live){
                if(can_wrap_fn_y){
                    lp_insert(&u->lines[entry],"    phy\n");
                    for(k=entry;k<u->count;++k)
                        if(!u->lines[k].deleted&&(lp_is(&u->lines[k],"rts")||lp_is(&u->lines[k],"rtl")))
                            lp_insert(&u->lines[k],"    ply\n");
                    lp_set(tax,"    tay");
                }else if(saves>=2&&!(u->lines[stores[nstores-1]].out&(LP_N|LP_Z))){
                    lp_set(tax,"    phy\n    tay");
                }else continue;
            }else{
                lp_set(tax,"    tay");
            }
            for(k=0;k<saves;++k)u->lines[phxs[k]].deleted=u->lines[plxs[k]].deleted=1;
            for(k=0;k<nstores;++k){
                LpLine *c=&u->lines[stores[k]];
                size_t n;const char *o=lp_operand(c,&n);
                const char *tail=(y_live&&!can_wrap_fn_y&&k+1==nstores)?"\n    ply":"";
                if(lp_is(c,"stz"))lp_set(c,"    lda #$00\n    sta %.*s,y%s",(int)(n-2),o,tail);
                else lp_set(c,"    %.3s %.*s,y%s",c->op,(int)(n-2),o,tail);
            }
            return 1;
        }
    }
    return 0;
}
static int lp_y_scratch_match(const LpUnit *u,const LpWorkspaceLive *memory,unsigned i,int slot,int *mul_out)
{
    int j,mul_at=-1;
    for(j=(int)i+1;(unsigned)j<u->count;++j){
        const LpLine *l=&u->lines[j];
        size_t m;const char *lo=lp_operand(l,&m);
        if(l->deleted)continue;
        if(l->replace||l->label)break;
        if(!l->op){
            if(!l->length)break;
            if(l->text[0]==';'||(l->length==3&&!strncmp(l->text,".a8",3))||
               (l->length==4&&!strncmp(l->text,".a16",4)))continue;
            break;
        }
        if(l->x8||l->call||l->ends||lp_branch(l))break;
        if((l->use&LP_Y)||(l->def&LP_Y))break;
        if(l->use==LP_ALL&&!lp_line_is(l,"sep #$20")&&!lp_line_is(l,"rep #$20"))break;
        if(lp_is(l,"lda")&&!l->m8&&lp_workspace_word(lo,m)==slot){
            if(!(memory[j].out&(3u<<slot))){
                if(mul_out)*mul_out=mul_at;
                return j;
            }
            break;
        }
        if((memory[j].read|memory[j].write)&(3u<<slot))break;
        if(lp_is(l,"sta")&&(lp_operand_is(l,"f:$004206",9)||(!l->m8&&lp_operand_is(l,"f:$004205",9))))break;
        if(lp_is(l,"sta")&&(lp_operand_is(l,"f:$004203",9)||(!l->m8&&lp_operand_is(l,"f:$004202",9))))mul_at=j;
    }
    return -1;
}
static int lp_y_scratch_mul_safe(const LpUnit *u,int mul_at,int found)
{
    int k,cycles=0;
    if(mul_at<0)return 1;
    for(k=mul_at+1;k<found;++k){
        const LpLine *l=&u->lines[k];
        if(l->deleted||!l->op)continue;
        cycles+=lp_line_is(l,"sep #$20")||lp_line_is(l,"rep #$20")?3:2;
    }
    cycles+=2; /* tya */
    for(k=found+1;(unsigned)k<u->count&&cycles<8;++k){
        const LpLine *l=&u->lines[k];
        if(l->deleted||l->label)break;
        if(!l->op){if(!l->length)break;continue;}
        if(lp_operand_is(l,"f:$004216",9)||lp_operand_is(l,"f:$004217",9))return cycles+4>=8;
        if(l->ends||lp_branch(l)||l->call)break;
        cycles+=2;
    }
    return 1;
}
static int lp_y_scratch_straight_ok(const LpLine *l)
{
    if(l->replace||l->label)return 0;
    if(!l->op)return !l->length?0:(l->text[0]==';'||(l->length==3&&!strncmp(l->text,".a8",3))||
                                   (l->length==4&&!strncmp(l->text,".a16",4)));
    if(l->x8||l->call||l->ends||lp_branch(l))return 0;
    if((l->use&LP_Y)||(l->def&LP_Y))return 0;
    if(l->use==LP_ALL&&!lp_line_is(l,"sep #$20")&&!lp_line_is(l,"rep #$20"))return 0;
    return 1;
}
/* Straight-line 16-bit workspace spill/reload pairs with Y dead (or wrappable
 * at function entry/exit, or across a run of 2+ pairs) keep temps in Y. */
static int lp_y_scratch_reuse(LpUnit *u,Function *f,size_t at)
{
    unsigned i,entry=0,back;
    int can_wrap_fn_y,changed=0,wrapped=0,wrap_loop=0;
    LpWorkspaceLive *memory;
    (void)at;
    if(u->indirect||cg.lp_volatile||cg.parser->no_value_reuse||!lp_fixed_workspace(u))return 0;
    can_wrap_fn_y=lp_can_wrap_fn_y(u,f,&entry);
    memory=allocate(u->count*sizeof *memory);
    lp_liveness(u);
    lp_workspace_liveness(u,memory,1);
    if(can_wrap_fn_y){
        for(i=0;i<u->count;++i){
            const LpLine *sta=&u->lines[i];
            size_t n;const char *o=lp_operand(sta,&n);
            int slot;
            if(sta->deleted||sta->replace||sta->m8||sta->x8||!lp_is(sta,"sta")||
               (sta->out&(LP_N|LP_Z))||!(sta->out&LP_Y))continue;
            slot=lp_workspace_word(o,n);
            if(slot<0||(slot&1)||!(memory[i].write&(3u<<slot)))continue;
            if(lp_y_scratch_match(u,memory,i,slot,NULL)>=0&&lp_loop(u,i,&back)>=0){
                wrap_loop=1;
                break;
            }
        }
        if(!wrap_loop)can_wrap_fn_y=0;
    }
    for(i=0;i<u->count;++i){
        LpLine *sta=&u->lines[i];
        size_t n;const char *o=lp_operand(sta,&n);
        int slot,mul_at=-1,found;
        if(sta->deleted||sta->replace||sta->m8||sta->x8||!lp_is(sta,"sta")||
           (sta->out&(LP_N|LP_Z)))continue;
        slot=lp_workspace_word(o,n);
        if(slot<0||(slot&1)||!(memory[i].write&(3u<<slot)))continue;
        if((sta->out&LP_Y)&&!can_wrap_fn_y)continue;
        found=lp_y_scratch_match(u,memory,i,slot,&mul_at);
        if(found<0||!lp_y_scratch_mul_safe(u,mul_at,found))continue;
        if((sta->out&LP_Y)&&!wrapped){
            unsigned k;
            if(!can_wrap_fn_y)continue;
            lp_insert(&u->lines[entry],"    phy\n");
            for(k=entry;k<u->count;++k)
                if(!u->lines[k].deleted&&(lp_is(&u->lines[k],"rts")||lp_is(&u->lines[k],"rtl")))
                    lp_insert(&u->lines[k],"    ply\n");
            wrapped=1;
        }
        lp_set(sta,"    tay");
        lp_set(&u->lines[found],"    tya");
        changed=1;
        break;
    }
    if(!changed){
        for(i=0;i<u->count;++i){
            unsigned stas[16],ldas[16],pairs=0,j;
            int slot;size_t n;const char *o;
            if(u->lines[i].deleted||u->lines[i].replace||u->lines[i].m8||u->lines[i].x8||
               !lp_is(&u->lines[i],"sta")||(u->lines[i].live&(LP_N|LP_Z))||(u->lines[i].out&(LP_N|LP_Z)))continue;
            o=lp_operand(&u->lines[i],&n);slot=lp_workspace_word(o,n);
            if(slot<0||(slot&1)||!(memory[i].write&(3u<<slot)))continue;
            j=i;
            while(j<u->count&&pairs<16){
                const LpLine *cur=&u->lines[j];
                int cur_slot,mul_at=-1,found;size_t cn;const char *co;
                if(cur->deleted){++j;continue;}
                if(!lp_y_scratch_straight_ok(cur))break;
                if(lp_is(cur,"sta")&&!cur->m8&&!(cur->out&(LP_N|LP_Z))){
                    co=lp_operand(cur,&cn);cur_slot=lp_workspace_word(co,cn);
                    if(cur_slot>=0&&!(cur_slot&1)&&(memory[j].write&(3u<<cur_slot))){
                        found=lp_y_scratch_match(u,memory,j,cur_slot,&mul_at);
                        if(found>=0&&lp_y_scratch_mul_safe(u,mul_at,found)){
                            stas[pairs]=j;ldas[pairs++]=(unsigned)found;j=(unsigned)found+1;continue;
                        }
                    }
                }
                ++j;
            }
            if(pairs>=2){
                unsigned last=ldas[pairs-1];
                int free_slot=-1;
                if(!(u->lines[last].out&(LP_N|LP_Z))){
                    for(int s=30;s>=0;s-=2){
                        int ok=1;
                        if((memory[stas[0]].live|memory[last].out)&(3u<<s)){ok=0;}
                        for(unsigned k=stas[0];k<=last&&ok;++k){
                            if((memory[k].read|memory[k].write|memory[k].live|memory[k].out)&(3u<<s))ok=0;
                            else{
                                size_t kn;const char *ko=lp_operand(&u->lines[k],&kn);
                                if(lp_text_words(ko,ko+kn)&(1u<<(s/2)))ok=0;
                            }
                        }
                        if(ok){free_slot=s;break;}
                    }
                }
                if(free_slot>=0){
                    lp_set(&u->lines[stas[0]],"    sty z:__arith_lhs+%d\n    tay",free_slot);
                    lp_set(&u->lines[ldas[0]],"    tya");
                    for(unsigned p=1;p<pairs;++p){
                        lp_set(&u->lines[stas[p]],"    tay");
                        lp_set(&u->lines[ldas[p]],"    tya");
                    }
                    lp_set(&u->lines[last],"    tya\n    ldy z:__arith_lhs+%d",free_slot);
                    changed=1;
                    break;
                }
            }
        }
    }
    free(memory);
    return changed;
}
/* Delay saving an incoming X bound until its positive arm uses it */
static int lp_delay_guarded_x_store(LpUnit *u,Function *f,size_t at)
{
    (void)at;
    if(u->indirect||cg.parser->no_value_reuse||!lp_fixed_workspace(u)||
       body_asm_statements(f->body))return 0;
    LpWorkspaceLive *memory=allocate(u->count*sizeof *memory);
    lp_workspace_liveness(u,memory,0);
    int changed=0;
    for(unsigned i=0;i<u->count&&!changed;++i){
        LpLine *save=&u->lines[i];
        if(!lp_is(save,"stx")||save->x8)continue;
        size_t n;
        const char *home=lp_operand(save,&n);
        int offset=lp_workspace_word(home,n);
        if(offset<0||(offset&1))continue;
        uint32_t mask=3u<<offset;
        int test=lp_next(u,i,1);
        if(test>=0&&lp_is(&u->lines[test],"sta")&&memory[test].write&&
           !(memory[test].write&mask))test=lp_next(u,(unsigned)test,1);
        if(test<0||!lp_line_is(&u->lines[test],"txa")||u->lines[test].m8)continue;
        int zero=lp_next(u,(unsigned)test,1),after_zero,after_negative;
        int zero_exit=lp_cond_branch_target(u,zero,&after_zero);
        if(zero_exit<0||!lp_is(&u->lines[zero],after_zero==zero?"beq":"bne")||
           (after_zero!=zero&&(u->lines[after_zero].first_incoming!=zero||u->lines[zero].next_incoming>=0))||
           (memory[zero_exit].live&mask))continue;
        int negative=lp_next(u,(unsigned)after_zero,1);
        int negative_exit=lp_cond_branch_target(u,negative,&after_negative);
        if(negative_exit<0||(unsigned)(after_negative+1)>=u->count||
           !lp_is(&u->lines[negative],after_negative==negative?"bmi":"bpl")||
           (after_negative!=negative&&(u->lines[after_negative].first_incoming!=negative||
                                       u->lines[negative].next_incoming>=0))||
           (memory[negative_exit].live&mask))continue;
        char text[64];
        snprintf(text,sizeof text,"    stx %.*s\n",(int)n,home);
        lp_insert(&u->lines[after_negative+1],text);
        save->deleted=1;
        changed=1;
    }
    free(memory);
    return changed;
}

/* Sink a 16-bit workspace store across guard branches when every taken target leaves the slot dead */
static int lp_sink_branch_store(LpUnit *u,Function *f,size_t at)
{
    unsigned i;
    LpWorkspaceLive *memory;
    (void)f;(void)at;
    if(u->indirect||cg.lp_volatile||cg.parser->no_value_reuse||!lp_fixed_workspace(u))return 0;
    memory=allocate(u->count*sizeof *memory);
    lp_liveness(u);
    lp_workspace_liveness(u,memory,1);
    for(i=0;i+3<u->count;++i){
        LpLine *store=&u->lines[i],*cmp,*after;
        size_t n;const char *o=lp_operand(store,&n);
        int slot,k1,k2,after1=-1,t1,fall;
        if(store->deleted||store->replace||store->m8||store->label||!lp_is(store,"sta"))continue;
        if(n<3||strncmp(o,"z:",2))continue;
        slot=lp_workspace_word(o,n);
        if(slot<0||(slot&1)||!(memory[i].write&(3u<<slot)))continue;
        k1=lp_next(u,i,1);
        if(k1<0)continue;
        cmp=&u->lines[k1];
        int remat_x=0;
        if(!cmp->deleted&&!cmp->replace&&!cmp->label&&!cmp->m8&&lp_is(cmp,"asl")&&
           lp_operand_is(cmp,"a",1)){
            int prev=lp_next(u,i,-1);
            int kx=lp_next(u,(unsigned)k1,1);
            if(prev>=0&&lp_is(&u->lines[prev],"and")&&lp_operand_is(&u->lines[prev],"#$00FF",6)&&
               kx>=0&&!u->lines[kx].label&&!u->lines[kx].x8&&lp_is(&u->lines[kx],"tax")){
                int cur=lp_next(u,(unsigned)kx,1);
                for(int steps=0;steps<4&&cur>=0;++steps){
                    LpLine *cl=&u->lines[cur];
                    if(cl->deleted||cl->replace||cl->label||cl->m8||cl->x8||cl->call)break;
                    if(memory[cur].read&(3u<<slot))break;
                    if(lp_is(cl,"cmp")){k1=cur;cmp=cl;remat_x=1;break;}
                    if(cl->def&LP_X)break;
                    cur=lp_next(u,(unsigned)cur,1);
                }
            }
        }else if(!cmp->deleted&&!cmp->replace&&!cmp->label&&
                 (lp_is(cmp,"tax")||lp_is(cmp,"tay"))){
            int kc=lp_next(u,(unsigned)k1,1);
            if(kc>=0&&!u->lines[kc].label&&!u->lines[kc].m8&&lp_is(&u->lines[kc],"cmp")&&
               !(memory[kc].read&(3u<<slot))){
                k1=kc;cmp=&u->lines[k1];
            }
        }
        if(cmp->deleted||cmp->replace||cmp->label||cmp->m8||!lp_is(cmp,"cmp"))continue;
        if(memory[k1].read&(3u<<slot))continue;
        k2=lp_next(u,(unsigned)k1,1);
        t1=lp_cond_branch_target(u,k2,&after1);
        if(t1<0||(memory[t1].live&(3u<<slot)))continue;
        fall=after1+1;
        {
            int k3=lp_next(u,(unsigned)after1,1),after2=-1,t2;
            t2=lp_cond_branch_target(u,k3,&after2);
            if(t2>=0){
                if(memory[t2].live&(3u<<slot))continue;
                fall=after2+1;
            }
        }
        if((unsigned)fall>=u->count)continue;
        after=&u->lines[fall];
        if(remat_x&&(after->live&(LP_A|LP_N|LP_Z|LP_C)))continue;
        {
            char text[160];
            if(remat_x)snprintf(text,sizeof text,"    txa\n    lsr a\n    sta %.*s\n",(int)n,o);
            else snprintf(text,sizeof text,"    sta %.*s\n",(int)n,o);
            lp_insert(after,text);
        }
        store->deleted=1;
        free(memory);
        return 1;
    }
    free(memory);
    return 0;
}
static int lp_thread_equal_store(LpUnit *u,Function *f,size_t at)
{
    unsigned i;
    (void)f;(void)at;
    if(cg.lp_volatile||cg.parser->no_value_reuse)return 0;
    lp_liveness(u);
    for(i=0;i+2<u->count;++i){
        LpLine *cmp=&u->lines[i];
        size_t n,sn;
        const char *o,*so;
        int k1,after1=-1,t,k_sta,k_after;
        unsigned lbl;
        char ltext[64],btext[64];
        if(cmp->deleted||cmp->replace||cmp->label||!lp_is(cmp,"cmp"))continue;
        o=lp_operand(cmp,&n);
        if(n<3||strncmp(o,"z:",2))continue;
        k1=lp_next(u,i,1);
        if(k1<0||u->lines[k1].label||!lp_is(&u->lines[k1],"beq"))continue;
        t=lp_cond_branch_target(u,k1,&after1);
        if(t<0||after1!=k1)continue;
        k_sta=lp_next(u,(unsigned)t,1);
        if(k_sta<0||u->lines[k_sta].deleted||u->lines[k_sta].replace||
           u->lines[k_sta].label||u->lines[k_sta].m8!=cmp->m8||
           !lp_is(&u->lines[k_sta],"sta"))continue;
        so=lp_operand(&u->lines[k_sta],&sn);
        if(sn!=n||strncmp(so,o,n))continue;
        k_after=lp_next(u,(unsigned)k_sta,1);
        if(k_after<0||(u->lines[k_after].live&(LP_N|LP_Z)))continue;
        lbl=++cg.label;
        snprintf(ltext,sizeof ltext,"cg_lp_%u:\n",lbl);
        snprintf(btext,sizeof btext,"    beq cg_lp_%u\n",lbl);
        lp_insert(&u->lines[k_after],ltext);
        lp_insert(&u->lines[k1],btext);
        u->lines[k1].deleted=1;
        return 1;
    }
    return 0;
}
/* The target exit routine restores S and then transfers to main_exit */
/* A known C result overwrites an unpassed register before any caller use */
static int lp_dead_literal_before_call(LpUnit *u,Function *f,size_t at)
{
    (void)at;
    if(u->indirect||cg.parser->no_body_optimizations||cg.parser->no_value_reuse||
       body_asm_statements(f->body))return 0;
    int live=0,changed=0;
    for(unsigned i=0;i<u->count;++i){
        LpLine *load=&u->lines[i];
        unsigned reg=lp_is(load,"lda")?LP_A:lp_is(load,"ldx")?LP_X:0;
        if(!reg||load->m8||load->x8||lp_immediate(load)<0)continue;
        unsigned next=i+1;
        while(next<u->count&&lp_internal_path_marker(u,next,i))++next;
        if(next>=u->count)continue;
        LpLine *call=&u->lines[next];
        if(!call->call||call->ends||call->use&reg)continue;
        Symbol *callee=lp_callee(call);
        Function *body=callee?inl.by_symbol[callee-cg.parser->symbols]:NULL;
        if(!body||body->aggregate_abi||body->uses_wide||callee->interrupt||
           body_asm_statements(body->body)||!inl_definitely_returns(body->body))continue;
        int result=reg_width(callee->type);
        if(result!=4&&(reg==LP_X||result!=2))continue;
        if(!live){lp_liveness(u);live=1;}
        if(call->out&(LP_N|LP_Z))continue;
        load->deleted=1;
        ++changed;
    }
    return changed;
}

static int lp_jump_to_runtime_exit(LpUnit *u,Function *f,size_t at)
{
    int changed=0;
    (void)at;
    if(cg.parser->no_body_optimizations||u->indirect||body_asm_statements(f->body))return 0;
    for(unsigned i=0;i<u->count;++i){
        LpLine *call=&u->lines[i];
        int long_call=lp_is(call,"jsl");
        if((!long_call&&!lp_is(call,"jsr"))||call->m8||call->x8||!body_library_exit(lp_callee(call)))continue;
        size_t n;
        const char *operand=lp_operand(call,&n);
        lp_set(call,"    %s %.*s",long_call?"jml":"jmp",(int)n,operand);
        ++changed;
    }
    return changed;
}

typedef struct {
    int lines[9],join,low,high;
} LpFarStackAdvance;

static int lp_far_advance_offset(const LpLine *line)
{
    size_t n;
    const char *operand=lp_operand(line,&n);
    if(n<3||n>5||memcmp(operand+n-2,",s",2)||!isdigit((unsigned char)*operand))return -1;
    char *end;
    long offset=strtol(operand,&end,10);
    return end==operand+n-2&&offset>0&&offset<256?(int)offset:-1;
}

static int lp_far_stack_advance(const LpUnit *u,int first,LpFarStackAdvance *advance)
{
    advance->lines[0]=first;
    if(!lp_is(&u->lines[first],"lda"))return 0;
    for(unsigned i=1;i<9;++i){
        int next=lp_next(u,(unsigned)advance->lines[i-1],1);
        if(next<0||u->lines[next].m8||u->lines[next].x8)return 0;
        advance->lines[i]=next;
    }
    int *line=advance->lines;
    if(u->lines[first].m8||u->lines[first].x8||!lp_line_is(&u->lines[line[1]],"tax")||
       !lp_is(&u->lines[line[2]],"lda")||!lp_line_is(&u->lines[line[3]],"inc a")||
       !lp_is(&u->lines[line[4]],"bne")||!lp_line_is(&u->lines[line[5]],"inx")||
       !lp_is(&u->lines[line[6]],"cpx")||lp_immediate(&u->lines[line[6]])!=256||
       !lp_is(&u->lines[line[7]],"bne")||!lp_is(&u->lines[line[8]],"ldx")||
       lp_immediate(&u->lines[line[8]])!=0)return 0;
    int join=u->lines[line[4]].target;
    if(join!=line[8]+1||u->lines[line[7]].target!=join||
       u->lines[join].first_incoming!=line[4]||u->lines[line[4]].next_incoming!=line[7]||
       u->lines[line[7]].next_incoming>=0)return 0;
    advance->high=lp_far_advance_offset(&u->lines[first]);
    advance->low=lp_far_advance_offset(&u->lines[line[2]]);
    advance->join=join;
    return advance->low>0&&advance->high==advance->low+2;
}

/* An advanced far pointer is already in X:A before its bound comparison.
 * Save its low word in the dead cursor register for the selected return. */
static int lp_far_advance_return(LpUnit *u,Function *f,size_t at)
{
    (void)at;
    if(u->indirect||!far_pointer(f->symbol->type)||cg.lp_volatile||cg.parser->no_value_reuse||
       body_asm_statements(f->body))return 0;
    lp_liveness(u);
    for(unsigned i=0;i<u->count;++i){
        LpFarStackAdvance before,after;
        if(!lp_far_stack_advance(u,(int)i,&before)||(u->lines[before.join].live&LP_Y))continue;
        int clear=lp_next(u,(unsigned)before.join,1),low=clear<0?-1:lp_next(u,(unsigned)clear,1);
        int copy=low<0?-1:lp_next(u,(unsigned)low,1),high=copy<0?-1:lp_next(u,(unsigned)copy,1);
        int test=high<0?-1:lp_next(u,(unsigned)high,1),fallthrough=-1;
        if(test<0||!lp_line_is(&u->lines[clear],"clc")||!lp_is(&u->lines[low],"sbc")||
           !lp_line_is(&u->lines[copy],"txa")||!lp_is(&u->lines[high],"sbc")||
           lp_far_advance_offset(&u->lines[low])<0||lp_far_advance_offset(&u->lines[high])<0||
           lp_cond_branch_target(u,test,&fallthrough)<0||
           !lp_is(&u->lines[test],fallthrough==test?"bcs":"bcc"))continue;
        unsigned next=(unsigned)fallthrough+1;
        while(next<u->count&&lp_internal_path_marker(u,next,(unsigned)fallthrough))++next;
        if(next>=u->count||!lp_far_stack_advance(u,(int)next,&after)||
           after.low!=before.low||after.high!=before.high)continue;
        int tail=lp_next(u,(unsigned)after.join,1);
        if(tail<0||!lp_is(&u->lines[tail],"jmp")||u->lines[tail].target<0)continue;
        LpLine *target=&u->lines[u->lines[tail].target];
        if(strncmp(target->text,"return_",7)||(target->live&(LP_Y|LP_FLAGS)))continue;
        lp_insert(&u->lines[clear],"    tay\n");
        lp_set(&u->lines[next],"    tya");
        for(unsigned k=1;k<9;++k)u->lines[after.lines[k]].deleted=1;
        return 1;
    }
    return 0;
}

/* Both runtime termination paths reset S. An earlier stack adjustment
 * is redundant if every subsequent path reaches one without using S. */
static int lp_stack_cleanup_before_exit(LpUnit *u,Function *f,size_t at)
{
    (void)at;
    if(u->indirect||cg.parser->no_stack_frames||body_asm_statements(f->body))return 0;
    int changed=0;
    unsigned char *resets=NULL;
    for(unsigned i=0;i<u->count;++i){
        LpLine *stack=&u->lines[i];
        if(!lp_line_is(stack,"tsc")||stack->m8||stack->x8)continue;
        int carry=lp_next(u,i,1),adjust=carry<0?-1:lp_next(u,(unsigned)carry,1);
        int commit=adjust<0?-1:lp_next(u,(unsigned)adjust,1);
        if(commit<0||!lp_line_is(&u->lines[carry],"clc")||!lp_is(&u->lines[adjust],"adc")||
           lp_immediate(&u->lines[adjust])<=0||!lp_line_is(&u->lines[commit],"tcs"))continue;
        if(!resets){
            resets=allocate(u->count+1);
            for(unsigned j=u->count;j-->i;){
                LpLine *line=&u->lines[j];
                if(!line->op){resets[j]=resets[j+1];continue;}
                Symbol *callee=line->call?lp_callee(line):NULL;
                if(callee){
                    Expr call={.kind=EX_CALL,.symbol=callee,
                               .arg_count=(unsigned)callee->param_count};
                    if(body_termination_call(&call))resets[j]=1;
                    continue;
                }
                if(lp_stack_op(line)||lp_is(line,"tsc")||lp_is(line,"tsx")||line->use==LP_ALL)continue;
                size_t n;
                const char *operand=lp_operand(line,&n);
                int stack_operand=0;
                for(size_t k=1;k<n;++k)if(operand[k-1]==','&&operand[k]=='s')stack_operand=1;
                if(stack_operand||((line->ends||lp_branch(line))&&line->target<0))continue;
                int taken=line->target<0||(line->target>(int)j&&resets[line->target]);
                resets[j]=(unsigned char)(taken&&(line->ends||resets[j+1]));
            }
            lp_liveness(u);
        }
        if(!resets[commit+1]||(u->lines[commit].out&(LP_A|LP_FLAGS)))continue;
        stack->deleted=u->lines[carry].deleted=u->lines[adjust].deleted=u->lines[commit].deleted=1;
        changed=1;
        break;
    }
    free(resets);
    return changed;
}

/* A private slot cannot be read after the runtime discards this frame */
static int lp_dead_exit_frame_store(LpUnit *u,Function *f,size_t at)
{
    (void)at;
    if(cg.parser->no_private_regions||cg.lp_volatile||u->indirect||
       !f->slots||body_asm_statements(f->body))return 0;
    for(unsigned i=0;i<(f->slots+1)/2&&i<384;++i)if(cg.frame_map[i])return 0;
    PrState *frames=NULL;
    int changed=0;
    for(unsigned i=0;i<u->count;++i){
        LpLine *exit=&u->lines[i];
        if((!lp_is(exit,"jmp")&&!lp_is(exit,"jml"))||!body_library_exit(lp_callee(exit)))continue;
        for(unsigned j=i;j-->0;){
            LpLine *line=&u->lines[j];
            if(!line->op||lp_line_is(line,"rep #$20")||lp_line_is(line,"sep #$20")||
               ((lp_is(line,"lda")||lp_is(line,"ldx"))&&lp_immediate(line)>=0))continue;
            if(!lp_is(line,"sta")&&!lp_is(line,"stz"))break;
            size_t n;
            const char *p=lp_operand(line,&n);
            if(n!=9||strncmp(p,"a:$",3)||memcmp(p+7,",y",2)||line->x8)break;
            char *end;
            unsigned slot=(unsigned)strtoul(p+3,&end,16);
            unsigned bytes=(unsigned)lp_width(line);
            if(end!=p+7||!slot||slot+bytes-1>f->slots)break;
            if(!frames)frames=pr_states(u);
            if(!frames[j].frame)break;
            for(unsigned k=0;k<cg.parser->symbol_count;++k){
                Symbol *v=&cg.parser->symbols[k];
                if(v->owner!=f->id||!v->offset||!v->scope||v->storage||
                   slot<v->offset||object_volatile(v->type))continue;
                unsigned char read[512]={0};
                unsigned size=width(v->type);
                if(slot-v->offset+bytes>size||size>sizeof read)continue;
                if(v->type.array?object_volatile(array_element(v->type))||
                   !body_unread_fixed_stores(f->body,v,read,0):
                   structure_object(v->type)||!loop_private(v))break;
                line->deleted=1;
                changed=1;
                break;
            }
            break;
        }
        if(changed)break;
    }
    free(frames);
    return changed;
}

/* A frame used only for one outgoing local address need not hold Y.
 * The stack reservations and pushed arguments keep their relative layout. */
static int lp_address_only_frame(LpUnit *u,Function *f,size_t at)
{
    (void)at;
    if(!f->slots||u->calls!=1||u->indirect||cg.parser->no_stack_frames||
       f->uses_varargs||f->aggregate_abi||body_asm_statements(f->body))return 0;
    LpLine *ops[48];
    unsigned count=0;
    for(unsigned i=0;i<u->count;++i){
        LpLine *l=&u->lines[i];
        if(!l->op)continue;
        if(count==sizeof ops/sizeof *ops||l->m8||l->x8||lp_branch(l)||l->target>=0)return 0;
        ops[count++]=l;
    }
    if(count<9||!lp_is(ops[0],"phy"))return 0;
    unsigned i=1,frame=0;
    while(i<count&&lp_is(ops[i],"pha")){++i;++frame;}
    if(!frame||i+3>=count||!lp_is(ops[i++],"tsc")||!lp_is(ops[i],"tay"))return 0;
    LpLine *save=ops[i++];
    unsigned outgoing=0;
    while(i<count&&lp_is(ops[i],"pea")){++i;++outgoing;}
    if(!outgoing||i>=count||!lp_is(ops[i],"tyx"))return 0;
    LpLine *address=ops[i++];
    unsigned offset=0;
    while(i<count&&lp_is(ops[i],"inx")){++i;++offset;}
    if(!offset||offset>2*frame||i>=count||!ops[i]->call||ops[i]->ends||
       (ops[i]->use&LP_A)||!(ops[i]->use&LP_X))return 0;
    unsigned pops=0;
    int result=0;
    for(++i;i<count;++i){
        if(lp_is(ops[i],"plx")){++pops;continue;}
        if(!result&&lp_is(ops[i],"lda")&&lp_immediate(ops[i])>=0){result=1;continue;}
        break;
    }
    if(pops!=frame+outgoing||i+2!=count||!lp_is(ops[i],"ply")||
       (!lp_is(ops[i+1],"rts")&&!lp_is(ops[i+1],"rtl")))return 0;
    ops[0]->deleted=save->deleted=ops[i]->deleted=1;
    lp_set(address,"    tax");
    return 1;
}

/* Retain an unescaped near cursor in a free caller-clobbered DP word.
 * No value of the cursor may be live across a call. */
static int lp_home_private_cursor(LpUnit *u,Function *f,size_t at)
{
    (void)at;
    if(!f->slots||u->indirect||cg.parser->no_dp_homes||cg.parser->no_direct_dpage||
       cg.parser->no_private_regions||!lp_fixed_workspace(u)||body_asm_statements(f->body))return 0;
    for(unsigned i=0;i<(f->slots+1)/2&&i<384;++i)if(cg.frame_map[i]&&cg.frame_map[i]!=2*i+1)return 0;
    uint32_t used=0;
    for(unsigned i=0;i<u->count;++i){
        LpLine *l=&u->lines[i];
        size_t n;
        const char *operand=lp_operand(l,&n);
        if(lp_operand_has_s(operand,n)||(l->op&&!l->call&&l->use==LP_ALL))return 0;
        int exact;
        uint32_t bytes=lp_workspace_access(l,&exact);
        if(exact)used|=bytes;
    }
    /* Named workspace references can also feed indirect operands.
     * Indexed C object addresses cannot designate compiler-owned scratch. */
    unsigned words=lp_text_words(u->text,u->text+strlen(u->text));
    for(unsigned i=0;i<16;++i)if(words&(1u<<i))used|=3u<<(2*i);
    unsigned word=0;
    while(word<32&&(used&(3u<<word)))word+=2;
    if(word>=32)return 0;
    PrState *frames=NULL;
    unsigned char *access=NULL,*live=NULL;
    int changed=0;
    for(unsigned i=0;i<cg.parser->symbol_count&&!changed;++i){
        Symbol *v=&cg.parser->symbols[i];
        if(v->owner!=f->id||!v->offset||!v->type.pointers||!body_private(v)||
           value_width(v->type)!=2||v->offset+1>f->slots)continue;
        int slot=(int)v->offset,valid=1,loop_use=0;
        unsigned count=0;
        if(!frames){
            frames=pr_states(u);
            access=allocate(u->count*2);
            live=access+u->count;
        }else memset(access,0,u->count*2);
        for(unsigned j=0;j<u->count;++j){
            LpLine *l=&u->lines[j];
            int off=lp_frame_indexed_offset(l,'y');
            if(off<0)continue;
            if(!frames[j].frame){valid=0;break;}
            if(!lp_overlaps(l,off,slot))continue;
            if(off!=slot||l->m8||(!lp_is(l,"lda")&&!lp_is(l,"sta"))){valid=0;break;}
            access[j]=(unsigned char)(lp_is(l,"lda")?1:2);
            unsigned back;
            if(!loop_use&&lp_loop(u,j,&back)>=0)loop_use=1;
            ++count;
        }
        if(!valid||!loop_use||count<3)continue;
        int again=1;
        while(again){
            again=0;
            for(unsigned j=u->count;j-->0;){
                LpLine *l=&u->lines[j];
                int out=(!l->ends&&j+1<u->count&&live[j+1])||
                        (l->target>=0&&live[l->target]);
                unsigned char in=(unsigned char)(access[j]==1||(out&&access[j]!=2));
                if(live[j]!=in){live[j]=in;again=1;}
            }
        }
        for(unsigned j=0;j<u->count&&valid;++j)
            if(u->lines[j].call&&live[j])valid=0;
        if(!valid)continue;
        for(unsigned j=0;j<u->count;++j)
            if(access[j])lp_set(&u->lines[j],"    %.3s z:__arith_lhs+%u",u->lines[j].op,word);
        cg.arithmetic=1;
        changed=1;
    }
    free(frames);
    free(access);
    return changed;
}

/* A leaf can move its mutable far stack argument into two free DP
 * words. A loop with two cursor bases avoids rebasing D for each test. */
static int lp_home_far_stack_argument(LpUnit *u,Function *f,size_t at)
{
    (void)at;
    if(u->calls||u->indirect||cg.lp_volatile||cg.lp_frame_address||f->uses_varargs||
       cg.parser->no_dp_homes||cg.parser->no_direct_dpage||cg.parser->no_private_regions||
       body_asm_statements(f->body))return 0;
    unsigned entry=0;
    while(entry<u->count&&!u->lines[entry].op)++entry;
    if(entry==u->count||u->lines[entry].m8||u->lines[entry].x8)return 0;
    lp_liveness(u);
    if(u->lines[entry].live&(LP_A|LP_N|LP_Z))return 0;
    int *depth=allocate(u->count*sizeof *depth);
    unsigned char *mark=allocate(u->count);
    if(!lp_stack_depths(u,entry,depth)){free(mark);free(depth);return 0;}
    int home=-1,valid=1,loop=0,second_cursor=0;
    unsigned touched=0;
    for(unsigned i=entry;i<u->count;++i){
        if(!lp_line_is(&u->lines[i],"phd"))continue;
        if(lp_far_stack_byte_test(u,(int)i)<0){valid=0;break;}
        int stack=lp_next_mode(u,i),page=lp_next_mode(u,(unsigned)stack);
        int mode=lp_next_mode(u,(unsigned)page),load=lp_next_mode(u,(unsigned)mode);
        int restore=lp_next_mode(u,(unsigned)load);
        size_t n;
        const char *operand=lp_operand(&u->lines[load],&n);
        int base=(int)strtol(operand+2,NULL,16)-depth[load];
        if(depth[load]<0||base<3||base>253||(home>=0&&home!=base)||
           (u->lines[restore].out&(LP_AH|LP_N|LP_Z))){valid=0;break;}
        home=base;
        mark[i]=mark[stack]=mark[page]=mark[restore]=1;
        mark[load]=2;
        unsigned back;
        if(!loop&&lp_loop(u,i,&back)>=0)loop=1;
    }
    uint32_t used=0;
    for(unsigned i=entry;i<u->count&&valid&&home>=0&&loop;++i){
        LpLine *l=&u->lines[i];
        if(!l->op||mark[i])continue;
        if(lp_is(l,"tcd")||lp_is(l,"pld")||lp_is(l,"plb")||lp_is(l,"xce")||l->use==LP_ALL||
           (lp_is(l,"rtl")&&home<4)){valid=0;break;}
        size_t n;
        const char *p=lp_operand(l,&n);
        if(lp_operand_has_s(p,n)){
            char *end;
            long s=strtol(p,&end,10);
            if(n<3||end!=p+n-2||p[n-2]!=','||p[n-1]!='s'||depth[i]<0||
               s<0||s>255){valid=0;break;}
            int off=(int)s-depth[i];
            if(!lp_overlaps_n(l,off,home,4))continue;
            if((off!=home&&off!=home+2)||l->m8||!lp_accumulator_memory(l)){valid=0;break;}
            mark[i]=(unsigned char)(3+(off-home)/2);
            ++touched;
        }else{
            int exact;
            uint32_t bytes=lp_workspace_access(l,&exact);
            if(exact)used|=bytes;
            if(n>2&&p[0]=='['&&lp_text_words(p,p+n))second_cursor=1;
        }
    }
    int changed=0;
    if(valid&&home>=0&&loop&&second_cursor&&touched>=5){
        unsigned words=lp_text_words(u->text,u->text+strlen(u->text));
        for(unsigned i=0;i<16;++i)if(words&(1u<<i))used|=3u<<(2*i);
        unsigned word=0;
        while(word<=28&&(used&(15u<<word)))word+=2;
        if(word<=28){
            char setup[120];
            snprintf(setup,sizeof setup,
                "    lda %d,s\n    sta z:__arith_lhs+%u\n    lda %d,s\n    sta z:__arith_lhs+%u\n",
                home,word,home+2,word+2);
            lp_insert(&u->lines[entry],setup);
            for(unsigned i=entry;i<u->count;++i){
                LpLine *l=&u->lines[i];
                if(mark[i]==1)l->deleted=1;
                else if(mark[i]==2)lp_set(l,"    lda [__arith_lhs+%u]",word);
                else if(mark[i]>=3)lp_set(l,"    %.3s z:__arith_lhs+%u",l->op,word+2*(mark[i]-3));
            }
            cg.arithmetic=1;
            changed=1;
        }
    }
    free(mark);
    free(depth);
    return changed;
}

/* A word read from direct page can go straight into its index register */
static int lp_load_index_from_workspace(LpUnit *u,Function *f,size_t at)
{
    (void)f;(void)at;
    lp_liveness(u);
    int changed=0;
    for(unsigned i=0;i<u->count;++i){
        LpLine *load=&u->lines[i];
        if(!lp_is(load,"lda")||load->m8||load->x8)continue;
        size_t n;
        const char *p=lp_operand(load,&n);
        if(lp_workspace_word(p,n)<0)continue;
        int next=lp_next(u,i,1);
        if(next<0)continue;
        LpLine *move=&u->lines[next];
        int x=lp_line_is(move,"tax");
        if((!x&&!lp_line_is(move,"tay"))||(move->out&LP_A))continue;
        lp_set(load,"    %s %.*s",x?"ldx":"ldy",(int)n,p);
        move->deleted=1;
        changed=1;
    }
    return changed;
}

/* A terminal transfer cannot expose the wide-result workspace */
static void lp_wide_runtime_exit(Function *f,size_t at)
{
    LpRunner runner={0};
    if(cg.parser->no_line_passes||f->symbol->interrupt)return;
    cg.lp_word_result=0;
    cg.lp_value_result=1;
    if(lp_run(&runner,f,at,lp_jump_to_runtime_exit))lp_run(&runner,f,at,lp_unreachable);
    while(lp_run(&runner,f,at,lp_repeated_inexact_raise)){}
    lp_invalidate(&runner);
    free(runner.work);
}

static int lp_prune_before_frames(Function *f,size_t at)
{
    LpRunner runner={0};
    int changed;
    if(cg.parser->no_line_passes)return 0;
    changed=lp_run(&runner,f,at,lp_unreachable);
    lp_invalidate(&runner);free(runner.work);
    return changed;
}
/* Set a literal return value after dismantling the stack frame */
static int lp_delay_epilogue_literal(LpUnit *u,Function *f,size_t at)
{
    (void)at;
    if(u->indirect||body_asm_statements(f->body))return 0;
    lp_liveness(u);
    for(unsigned i=0;i<u->count;++i){
        LpLine *load=&u->lines[i];
        long value=lp_immediate(load);
        unsigned j=i+1;
        if(j+1<u->count&&lp_is(&u->lines[j],"jmp")&&u->lines[j].target==(int)j+1&&
           u->lines[j+1].first_incoming==(int)j&&u->lines[j].next_incoming<0)j+=2;
        else if(j<u->count&&u->lines[j].label&&u->lines[j].first_incoming<0&&
                !strncmp(u->lines[j].text,"return_",7))++j;
        if(j+5>=u->count)continue;
        LpLine *save=&u->lines[j],*base=&u->lines[j+1],*carry=&u->lines[j+2];
        LpLine *size=&u->lines[j+3],*stack=&u->lines[j+4],*restore=&u->lines[j+5];
        if(value<0||load->m8||load->x8||!lp_is(load,"lda")||
           !lp_line_is(save,"tax")||(!lp_line_is(base,"tya")&&!lp_line_is(base,"tsc"))||
           !lp_line_is(carry,"clc")||!lp_is(size,"adc")||lp_immediate(size)<0||
           !lp_line_is(stack,"tcs")||!lp_line_is(restore,"txa")||(restore->out&LP_X))continue;
        lp_set(restore,"    lda #$%04lX",value);
        load->deleted=save->deleted=1;
        return 1;
    }
    return 0;
}
static void line_passes(Function *f,size_t at)
{
    LpRunner runner={0};
    if(cg.parser->no_line_passes)return;
    if(f->symbol->interrupt){
        if(!statement_inline_markers(f->body)){
            lp_run(&runner,f,at,lp_byte_region_modes);
            if(!cg.parser->no_value_reuse)lp_run(&runner,f,at,lp_reuse_store_immediates);
        }
        goto done;
    }
    cg.lp_volatile=volatile_statements(f->body);
    cg.lp_frame_address=frame_address_visible(f->body);
    cg.lp_word_result=reg_width(f->symbol->type)==2;
    cg.lp_value_result=!cg.parser->no_body_optimizations&&strcmp(f->symbol->name,"main")?body_value_returns(f->body):1;
    if(!cg.parser->no_index_elimination)lp_run(&runner,f,at,lp_stop_bounds);
    while(lp_run(&runner,f,at,lp_step_literal_store)){}
    lp_cleanup(&runner,f,at,0);
    if(lp_run(&runner,f,at,lp_y_promote))lp_cleanup(&runner,f,at,0);
    if(lp_run(&runner,f,at,lp_y_promote_split))lp_cleanup(&runner,f,at,0);
    lp_run(&runner,f,at,lp_trim_private_frame);
    if(lp_run(&runner,f,at,lp_call_frame_homes)){
        lp_cleanup(&runner,f,at,1);
        if(lp_run(&runner,f,at,lp_late_call_save))lp_cleanup(&runner,f,at,1);
    }else if(lp_run(&runner,f,at,lp_pointer_frame_home)){
        lp_run(&runner,f,at,lp_y_forms);
        lp_run(&runner,f,at,lp_push_parameter_frame);
        lp_run(&runner,f,at,lp_snapshot_index);
        while(lp_run(&runner,f,at,lp_equal_sum))lp_run(&runner,f,at,lp_relocated_dead_stores);
        while(lp_run(&runner,f,at,lp_stage_subtract_before_sum)){}
    }
    if(lp_run(&runner,f,at,lp_tail_wrapper))lp_run(&runner,f,at,lp_unreachable);
    if(lp_run(&runner,f,at,lp_register_parameter_frame))lp_cleanup(&runner,f,at,0);
    if(lp_run(&runner,f,at,lp_leaf_stack_arguments)){
        lp_run(&runner,f,at,lp_dead_inner_y_save);
        lp_run(&runner,f,at,lp_reload_saved_x);
        lp_run(&runner,f,at,lp_delay_byte_extract);
        lp_run(&runner,f,at,lp_test_indexed_mask);
        lp_cleanup(&runner,f,at,0);
    }
    if(lp_run(&runner,f,at,lp_remove_index_save)){
        while(lp_run(&runner,f,at,lp_remove_index_save)){}
        lp_run(&runner,f,at,lp_register_values);
    }
    lp_run(&runner,f,at,lp_store_zero);
    lp_run(&runner,f,at,lp_outgoing_move_frame);
    lp_run(&runner,f,at,lp_unused_push_frame);
    lp_run(&runner,f,at,lp_unused_call_save);
    if(lp_run(&runner,f,at,lp_closed_frame)&&!cg.lp_volatile)lp_cleanup(&runner,f,at,0);
    if(lp_run(&runner,f,at,lp_dead_stack_frame_stores))lp_cleanup(&runner,f,at,0);
    lp_run(&runner,f,at,lp_far_frame_cache);
    if(lp_run(&runner,f,at,lp_hoist_local_y_saves))lp_cleanup(&runner,f,at,0);
    if(lp_run(&runner,f,at,lp_ax_reuse))lp_run(&runner,f,at,lp_dead_code);
    while(lp_run(&runner,f,at,lp_retain_word_index)){}
    lp_run(&runner,f,at,lp_tail_index_dispatch);
    if(!cg.parser->no_value_reuse)lp_run(&runner,f,at,lp_reuse_store_immediates);
    if(lp_run(&runner,f,at,lp_mmio_addressing)&&!cg.parser->no_value_reuse)
        lp_run(&runner,f,at,lp_reuse_store_immediates);
    while(lp_run(&runner,f,at,lp_keep_post_cursors)){}
    while(lp_run(&runner,f,at,lp_word_scan_cursor)){}
    while(lp_run(&runner,f,at,lp_divider_index_wait)){}
    while(lp_run(&runner,f,at,lp_forward_interleaved_words)){}
    while(lp_run(&runner,f,at,lp_divider_remainder_last)){}
    while(lp_run(&runner,f,at,lp_keep_loop_word_in_a)){}
    while(lp_run(&runner,f,at,lp_chain_reduction_in_a)){}
    while(lp_run(&runner,f,at,lp_keep_reduction_in_a)){
        lp_run(&runner,f,at,lp_forward_constants);
        lp_run(&runner,f,at,lp_reloads);
    }
    while(lp_run(&runner,f,at,lp_forward_conditional_word)){}
    lp_run(&runner,f,at,lp_forward_shifted_word);
    lp_run(&runner,f,at,lp_forward_or_chain);
    lp_run(&runner,f,at,lp_reuse_clear_carry);
    while(lp_run(&runner,f,at,lp_redundant_y_offset)){}
    lp_run(&runner,f,at,lp_commute_spilled_add);
    lp_run(&runner,f,at,lp_drop_dead_workspace_stores);
    lp_run(&runner,f,at,lp_scaled_word_latch);
    while(lp_run(&runner,f,at,lp_rmw_reload)){}
    while(lp_run(&runner,f,at,lp_narrow_divisor_load)){}
    lp_run(&runner,f,at,lp_divider_wait_mask);
    lp_run(&runner,f,at,lp_sink_branch_store);
    lp_run(&runner,f,at,lp_thread_equal_store);
    if(lp_run(&runner,f,at,lp_cache_stored_word)){
        while(lp_run(&runner,f,at,lp_cache_stored_word)){}
        lp_cleanup(&runner,f,at,0);
        lp_run(&runner,f,at,lp_dead_stack_frame_stores);
    }
    while(lp_run(&runner,f,at,lp_demanded_masks)){}
    lp_run(&runner,f,at,lp_sign_extension_branch);
    lp_run(&runner,f,at,lp_duplicate_stores);
    lp_run(&runner,f,at,lp_known_accumulator_mode);
    while(lp_run(&runner,f,at,lp_y_saved_index)){
        lp_run(&runner,f,at,lp_reloads);
        lp_run(&runner,f,at,lp_register_values);
    }
    while(lp_run(&runner,f,at,lp_y_scratch_reuse)){
        lp_run(&runner,f,at,lp_reloads);
        lp_run(&runner,f,at,lp_register_values);
    }
    lp_run(&runner,f,at,lp_dead_x_save);
    lp_run(&runner,f,at,lp_byte_rmw);
    while(lp_run(&runner,f,at,lp_demanded_masks)){}
    lp_run(&runner,f,at,lp_dead_epilogue_stores);
    lp_run(&runner,f,at,lp_dead_code);
    lp_run(&runner,f,at,lp_dead_stack_word_save);
    lp_run(&runner,f,at,lp_store_pulled_pair);
    if(lp_run(&runner,f,at,lp_store_low_before_high))lp_cleanup(&runner,f,at,0);
    while(lp_run(&runner,f,at,lp_post_index_test)){}
    while(lp_run(&runner,f,at,lp_scaled_displacement)){}
    if(lp_run(&runner,f,at,lp_literal_shifts))lp_cleanup(&runner,f,at,0);
    while(lp_run(&runner,f,at,lp_signed_difference_flags)){}
    while(lp_run(&runner,f,at,lp_stage_pair_words)){}
    if(lp_run(&runner,f,at,lp_pair_store_order)){
        while(lp_run(&runner,f,at,lp_pair_store_order)){}
        if(lp_run(&runner,f,at,lp_dead_stack_frame_stores))lp_cleanup(&runner,f,at,0);
    }
    if(lp_run(&runner,f,at,lp_reloads))lp_run(&runner,f,at,lp_dead_stack_frame_stores);
    if(lp_run(&runner,f,at,lp_push_register_pair))lp_run(&runner,f,at,lp_dead_stack_frame_stores);
    lp_run(&runner,f,at,lp_cancel_pull_push);
    lp_run(&runner,f,at,lp_index_carry);
    lp_run(&runner,f,at,lp_increment_wrap_test);
    lp_run(&runner,f,at,lp_postdecrement_truth);
    lp_run(&runner,f,at,lp_small_accumulator_steps);
    while(lp_run(&runner,f,at,lp_index_transfer_steps)){}
    if(lp_run(&runner,f,at,lp_materialized_zero_flag))lp_run(&runner,f,at,lp_jump_threading);
    lp_run(&runner,f,at,lp_sign_bit_order);
    if(lp_run(&runner,f,at,lp_reuse_far_byte)){
        while(lp_run(&runner,f,at,lp_reuse_far_byte)){}
        lp_run(&runner,f,at,lp_drop_dead_workspace_stores);
    }
    while(lp_run(&runner,f,at,lp_keep_mask_source)){}
    while(lp_run(&runner,f,at,lp_signed_home_positive)){}
    while(lp_run(&runner,f,at,lp_keep_loop_word_in_a)){}
    if(lp_run(&runner,f,at,lp_fixed_stack_argument)){
        while(lp_run(&runner,f,at,lp_fixed_stack_argument)){}
        while(lp_run(&runner,f,at,lp_dead_stack_frame_stores))lp_cleanup(&runner,f,at,0);
    }
    lp_run(&runner,f,at,lp_store_zero);
    while(lp_run(&runner,f,at,lp_byte_region_modes)){}
    lp_run(&runner,f,at,lp_store_zero);
    lp_run(&runner,f,at,lp_sink_branch_store);
    lp_run(&runner,f,at,lp_thread_equal_store);
    if(lp_run(&runner,f,at,lp_cache_stored_word)){
        while(lp_run(&runner,f,at,lp_cache_stored_word)){}
        lp_cleanup(&runner,f,at,0);
        lp_run(&runner,f,at,lp_dead_stack_frame_stores);
    }
    while(lp_run(&runner,f,at,lp_demanded_masks)){}
    lp_run(&runner,f,at,lp_duplicate_stores);
    lp_run(&runner,f,at,lp_known_accumulator_mode);
    while(lp_run(&runner,f,at,lp_reverse_signed_literal))lp_run(&runner,f,at,lp_drop_dead_workspace_stores);
    while(lp_run(&runner,f,at,lp_far_stack_read)){}
    lp_run(&runner,f,at,lp_varargs_stack_read);
    if(!cg.parser->no_private_regions)lp_run(&runner,f,at,lp_pushed_index_checks);
    lp_run(&runner,f,at,lp_varargs_tail_call);
    if(lp_run(&runner,f,at,lp_literal_to_index))lp_run(&runner,f,at,lp_dead_push_pairs);
    lp_run(&runner,f,at,lp_literal_stack_argument_bytes);
    lp_run(&runner,f,at,lp_push_immediate_word);
    while(lp_run(&runner,f,at,lp_indexed_alu_rhs)){}
    while(lp_run(&runner,f,at,lp_preserved_range_pointer)){}
    while(lp_run(&runner,f,at,lp_saved_index_steps)){}
    while(lp_run(&runner,f,at,lp_scaled_base_steps)){}
    while(lp_run(&runner,f,at,lp_restore_indirect_index)){}
    while(lp_run(&runner,f,at,lp_carry_from_shift_byte)){}
    lp_run(&runner,f,at,lp_test_index);
    if(lp_run(&runner,f,at,lp_saved_x_read))lp_run(&runner,f,at,lp_reuse_far_byte);
    while(lp_run(&runner,f,at,lp_cleared_byte_loop)){}
    if(lp_run(&runner,f,at,lp_const_branches))lp_cleanup(&runner,f,at,0);
    if(lp_run(&runner,f,at,lp_published_frame_read)){
        while(lp_run(&runner,f,at,lp_published_frame_read)){}
        lp_run(&runner,f,at,lp_forward_constants);
        lp_cleanup(&runner,f,at,0);
    }
    lp_run(&runner,f,at,lp_zero_high_across_byte_load);
    while(lp_run(&runner,f,at,lp_delay_index_literal)){}
    if(lp_run(&runner,f,at,lp_overwritten_stores))lp_cleanup(&runner,f,at,0);
    if(lp_run(&runner,f,at,lp_unused_push_frame))lp_cleanup(&runner,f,at,0);
    while(lp_run(&runner,f,at,lp_step_literal_store)){}
    if(lp_run(&runner,f,at,lp_zero_index_address)){
        while(lp_run(&runner,f,at,lp_zero_index_address)){}
        if(lp_run(&runner,f,at,lp_forward_constants))lp_cleanup(&runner,f,at,0);
    }
    if(lp_run(&runner,f,at,lp_direct_relocated_read))lp_cleanup(&runner,f,at,0);
    if(lp_run(&runner,f,at,lp_dead_stack_frame_stores))lp_cleanup(&runner,f,at,0);
    lp_run(&runner,f,at,lp_skip_dead_loop_step);
    while(lp_run(&runner,f,at,lp_delay_epilogue_literal)){}
    while(lp_run(&runner,f,at,lp_delay_guarded_y_init)){}
    while(lp_run(&runner,f,at,lp_delay_guarded_x_store)){}
    while(lp_run(&runner,f,at,lp_keep_frame_argument_in_x)){}
    while(lp_run(&runner,f,at,lp_forward_named_latch_load)){}
    while(lp_run(&runner,f,at,lp_named_counter_in_x)){}
    while(lp_run(&runner,f,at,lp_skip_repeated_far_loop_guard)){}
    while(lp_run(&runner,f,at,lp_repeated_inexact_raise)){}
    lp_run(&runner,f,at,lp_far_advance_return);
    lp_run(&runner,f,at,lp_dead_retained_varargs_cursor);
    lp_run(&runner,f,at,lp_dead_literal_before_call);
    if(lp_run(&runner,f,at,lp_literal_limb_carry))lp_cleanup(&runner,f,at,0);
    if(lp_run(&runner,f,at,lp_compare_past_frame_clear))lp_cleanup(&runner,f,at,0);
    if(lp_run(&runner,f,at,lp_compare_saved_frame_offset))lp_cleanup(&runner,f,at,0);
    if(lp_run(&runner,f,at,lp_forward_frame_clear))lp_cleanup(&runner,f,at,0);
    lp_run(&runner,f,at,lp_byte_loop_test_exits);
    if(lp_run(&runner,f,at,lp_jump_to_runtime_exit))lp_run(&runner,f,at,lp_unreachable);
    if(lp_run(&runner,f,at,lp_stack_cleanup_before_exit))lp_cleanup(&runner,f,at,0);
    while(lp_run(&runner,f,at,lp_dead_exit_frame_store))lp_cleanup(&runner,f,at,0);
    while(lp_run(&runner,f,at,lp_home_private_cursor)){}
    lp_run(&runner,f,at,lp_address_only_frame);
    lp_run(&runner,f,at,lp_home_far_stack_argument);
    lp_run(&runner,f,at,lp_load_index_from_workspace);
done:
    lp_invalidate(&runner);
    free(runner.work);
}
