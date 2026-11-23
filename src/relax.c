/* Choose branch instructions that can reach their targets. Measure offsets
 * within CODE using the compiler's own ca65 output. */
#include "headers/relax.h"
#include <ctype.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

enum { RAW, LABEL, CONDITIONAL, JUMP, RETURN };
typedef struct {
    char *text,*label,*target;
    char op[4];
    unsigned bytes,refs;
    size_t destination,placement,prefix;
    int kind,anonymous,removed,in_code,in_function,widths;
    int64_t offset;
} Line;
typedef struct { Line *lines;size_t count,*hash,hash_size; } Layout;

static char *copy_text(const char *p,size_t n)
{
    char *s=malloc(n+1);if(s){memcpy(s,p,n);s[n]=0;}return s;
}
static char *trim(char *s)
{
    char *end;while(isspace((unsigned char)*s))++s;
    end=s+strlen(s);while(end>s&&isspace((unsigned char)end[-1]))--end;*end=0;return s;
}
static int identifier(const char *s)
{
    if(!isalpha((unsigned char)*s)&&*s!='_')return 0;
    for(++s;*s;++s)if(!isalnum((unsigned char)*s)&&*s!='_')return 0;
    return 1;
}
static const char *inverse(const char *op)
{
    static const char *pairs[][2]={{"beq","bne"},{"bcc","bcs"},{"bmi","bpl"},{"bvc","bvs"}};
    size_t i;for(i=0;i<sizeof pairs/sizeof pairs[0];++i){
        if(!strcmp(op,pairs[i][0]))return pairs[i][1];
        if(!strcmp(op,pairs[i][1]))return pairs[i][0];
    }
    return NULL;
}
static uint32_t hash_name(const char *s)
{
    uint32_t h=2166136261u;for(;*s;++s)h=(h^(unsigned char)*s)*16777619u;return h;
}
static size_t find_label(Layout *l,const char *name)
{
    size_t slot=hash_name(name)&(l->hash_size-1),index;
    while((index=l->hash[slot])!=SIZE_MAX){
        if(!strcmp(l->lines[index].label,name))return index;
        slot=(slot+1)&(l->hash_size-1);
    }
    return SIZE_MAX;
}
static int number(const char *s,unsigned *value)
{
    char *end;unsigned long n;int base=10;
    if(*s=='$'){++s;base=16;}
    if (!*s) {
        return 0;
    }
    n = strtoul(s, &end, base);
    while(isspace((unsigned char)*end))++end;
    if(*end&&*end!=',')return 0;
    if (n > 0x10000000UL) {
        return 0;
    }
    *value = (unsigned)n;
    return 1;
}
static unsigned instruction_size(const char *op,const char *operand,int a16,int i16)
{
    static const char *implied=" clc sec cld sed cli sei clv nop wai tax tay txa tya txy tyx tsc tcs tcd tdc tsx txs xba xce pha pla phx plx phy ply phd pld phb plb phk php plp rts rtl rti inx dex iny dey ";
    char needle[8];snprintf(needle,sizeof needle," %s ",op);
    if(strstr(implied,needle))return 1;
    if(!strcmp(op,"rep")||!strcmp(op,"sep"))return 2;
    if(!strcmp(op,"pea")||!strcmp(op,"mvn"))return 3;
    if(!strcmp(op,"pei"))return 2;
    if(!strcmp(op,"jsr")||!strcmp(op,"jmp"))return 3;
    if(!strcmp(op,"jsl")||!strcmp(op,"jml"))return 4;
    if(!strcmp(op,"tsb")||!strcmp(op,"trb")){
        if(!strncmp(operand,"z:",2))return 2;
        if(!strncmp(operand,"a:",2))return 3;
        return 0;
    }
    if(!strcmp(op,"asl")||!strcmp(op,"lsr")||!strcmp(op,"rol")||!strcmp(op,"ror")||!strcmp(op,"inc")||!strcmp(op,"dec")){
        if(!strcmp(operand,"a")||!*operand)return 1;
    }else{
        static const char *memory=" lda ldx ldy sta stx sty stz adc sbc and ora eor cmp cpx cpy bit ";
        if(!strstr(memory,needle))return 0;
    }
    if(*operand=='#'){
        int index=!strcmp(op,"ldx")||!strcmp(op,"ldy")||!strcmp(op,"cpx")||!strcmp(op,"cpy");
        return 2u+(unsigned)(index?i16:a16);
    }
    if(!strncmp(operand,"z:",2)||*operand=='('||*operand=='['||strstr(operand,",s"))return 2;
    if(!strncmp(operand,"a:",2))return 3;
    if(!strncmp(operand,"f:",2))return 4;
    return 0;
}
static int parse(Layout *layout,const char *assembly,const char *unit)
{
    const char *start=assembly,*end;size_t count=0,i,anon=0,placement=0;int code=0,in_function=0,a16=1,i16=1;
    for(end=assembly;*end;++end)if(*end=='\n')++count;
    if(end>assembly&&end[-1]!='\n')++count;
    layout->lines=calloc(count?count:1,sizeof *layout->lines);if(!layout->lines)return 0;
    layout->count=count;
    for(i=0;i<count;++i){
        Line *line=&layout->lines[i];char *scratch,*s,*comment,*p;size_t length;
        end=strchr(start,'\n');if(!end)end=start+strlen(start);length=(size_t)(end-start);
        line->text=copy_text(start,length);scratch=copy_text(start,length);
        if(!line->text||!scratch){free(scratch);return 0;}
        start=*end?end+1:end;line->destination=SIZE_MAX;
        s=trim(scratch);
        /* ROM allocation can move the code between these markers as a unit */
        if(!strncmp(s,"; allocation function ",22)){
            ++placement;in_function=!strcmp(strrchr(s,' ')," begin");
        }
        line->in_function=in_function;
        line->placement=placement;
        comment=strchr(s,';');if(comment)*comment=0;s=trim(s);
        if(!strncmp(s,".segment",8))code=!strcmp(trim(s+8),"\"CODE\"");
        line->in_code=code;
        if(!strcmp(s,".a16"))a16=1;else if(!strcmp(s,".a8"))a16=0;
        else if(!strcmp(s,".i16"))i16=1;else if(!strcmp(s,".i8"))i16=0;
        line->widths=a16+2*i16;
        if(!code||!*s||*s=='.'){
            if(code&&!strncmp(s,".res ",5)){
                if(!number(trim(s+5),&line->bytes)){free(scratch);return 0;}
            }else if(code&&!strncmp(s,".byte ",6)){
                unsigned byte;
                if(!number(trim(s+6),&byte)||byte>255){free(scratch);return 0;}
                line->bytes=1;
            }else if(code&&*s=='.'&&strncmp(s,".segment",8)&&strncmp(s,".export",7)&&strncmp(s,".assert",7)&&
                     strncmp(s,".import",7)&&strncmp(s,".setcpu",7)&&strcmp(s,".a16")&&
                     strcmp(s,".a8")&&strcmp(s,".i16")&&strcmp(s,".i8")){
                fprintf(stderr,"branch layout: unsupported CODE directive: %s\n",s);free(scratch);return 0;
            }
            free(scratch);continue;
        }
        if(!strcmp(s,":")){
            char name[128];snprintf(name,sizeof name,"cg_%s_relax_anon_%zu",unit,++anon);
            line->label=copy_text(name,strlen(name));line->anonymous=1;
        }else if((p=strchr(s,'='))!=NULL){
            *p=0;if(!strcmp(trim(p+1),"*")&&identifier(trim(s)))line->label=copy_text(trim(s),strlen(trim(s)));
            free(scratch);if(line->label)line->kind=LABEL;continue;
        }else if((p=strchr(s,':'))!=NULL&&p[1]==0){
            *p=0;if(identifier(s))line->label=copy_text(s,strlen(s));
        }
        if(line->label){line->kind=LABEL;free(scratch);continue;}
        p=s;while(isalpha((unsigned char)*p))++p;
        if(p-s!=3){fprintf(stderr,"branch layout: invalid backend instruction: %s\n",s);free(scratch);return 0;}
        memcpy(line->op,s,3);line->op[3]=0;p=trim(p);
        if(inverse(line->op)||!strcmp(line->op,"bra")){
            line->kind=!strcmp(line->op,"bra")?JUMP:CONDITIONAL;
            line->bytes=line->kind==JUMP?3:5;line->target=copy_text(p,strlen(p));
        }else if(!strcmp(line->op,"jmp")){
            size_t n=strlen(p);line->kind=JUMP;line->bytes=3;
            if(n>9&&!strncmp(p,".loword(",8)&&p[n-1]==')')line->target=copy_text(p+8,n-9);
            else if(identifier(p))line->target=copy_text(p,n);
            else{fprintf(stderr,"branch layout: unsupported jump: %s\n",p);free(scratch);return 0;}
        }else{
            line->bytes=instruction_size(line->op,p,a16,i16);
            if(!line->bytes){fprintf(stderr,"branch layout: unknown size: %s\n",s);free(scratch);return 0;}
        }
        free(scratch);
        if((line->kind==JUMP||line->kind==CONDITIONAL)&&!line->target)return 0;
    }
    layout->hash_size=1;while(layout->hash_size<count*2+1)layout->hash_size*=2;
    layout->hash=malloc(layout->hash_size*sizeof *layout->hash);if(!layout->hash)return 0;
    for(i=0;i<layout->hash_size;++i)layout->hash[i]=SIZE_MAX;
    for(i=0;i<count;++i)if(layout->lines[i].label){
        size_t slot=hash_name(layout->lines[i].label)&(layout->hash_size-1);
        while(layout->hash[slot]!=SIZE_MAX)slot=(slot+1)&(layout->hash_size-1);
        layout->hash[slot]=i;
    }
    for(i=0;i<count;++i){
        Line *line=&layout->lines[i];if(!line->target)continue;
        if(line->target[0]==':'){
            size_t j=i,n=strlen(line->target+1);int forward=line->target[1]=='+';
            if(!n){fputs("branch layout: invalid anonymous reference\n",stderr);return 0;}
            while(n){
                if(forward){if(++j>=count)break;}else{if(!j)break;--j;}
                if(layout->lines[j].anonymous)--n;
            }
            if(n){fputs("branch layout: unresolved anonymous reference\n",stderr);return 0;}
            line->destination=j;
            free(line->target);line->target=copy_text(layout->lines[j].label,strlen(layout->lines[j].label));
            if(!line->target)return 0;
        }else{
            size_t destination=find_label(layout,line->target);
            if(destination!=SIZE_MAX&&layout->lines[destination].placement==line->placement)
                line->destination=destination;
        }
        if(line->destination!=SIZE_MAX)++layout->lines[line->destination].refs;
    }
    /* Fold only an otherwise-unreferenced anonymous skip label */
    for(i=0;i+2<count;++i){
        Line *a=&layout->lines[i],*b=&layout->lines[i+1],*c=&layout->lines[i+2];
        if(a->kind==CONDITIONAL&&b->kind==JUMP&&c->anonymous&&c->refs==1&&a->destination==i+2){
            strcpy(a->op,inverse(a->op));free(a->target);a->target=b->target;b->target=NULL;
            a->destination=b->destination;b->removed=c->removed=1;
        }
    }
    return 1;
}
/* A named compiler label can also mark the fallthrough of a conditional
     * skip over an unconditional jump. Keep all labels, and remove the jump
     * only when no other branch can enter between the two instructions. */
static void fold_named(Layout *layout)
{
    size_t i,count=layout->count;
    for(i=0;i<count;++i)layout->lines[i].refs=0;
    for(i=0;i<count;++i){
        Line *line=&layout->lines[i];
        if(!line->removed&&line->bytes&&line->destination!=SIZE_MAX)
            ++layout->lines[line->destination].refs;
    }
    for(i=0;i<count;++i){
        Line *a=&layout->lines[i],*b;size_t j,k;int reaches=0;
        if(a->removed||a->kind!=CONDITIONAL||a->destination==SIZE_MAX)continue;
        for(j=i+1;j<count;++j){
            Line *line=&layout->lines[j];const char *p=line->text;
            if(line->removed)continue;
            while(isspace((unsigned char)*p))++p;
            if(line->placement!=a->placement||!line->in_code)break;
            if(line->kind==LABEL){
                if(line->refs||strncmp(line->label,"cg_",3))break;
                continue;
            }
            if(line->kind==RAW&&(*p==';'||!*p))continue;
            break;
        }
        if(j>=count||(b=&layout->lines[j])->kind!=JUMP||b->removed)continue;
        for(k=j+1;k<count;++k){
            Line *line=&layout->lines[k];const char *p=line->text;
            if(line->removed)continue;
            while(isspace((unsigned char)*p))++p;
            if(line->placement!=a->placement||!line->in_code)break;
            if(k==a->destination)reaches=1;
            if(line->kind==LABEL||(line->kind==RAW&&(*p==';'||!*p)))continue;
            break;
        }
        if(!reaches)continue;
        strcpy(a->op,inverse(a->op));free(a->target);a->target=b->target;b->target=NULL;
        a->destination=b->destination;
        if(a->destination==SIZE_MAX)a->bytes=5;
        b->removed=1;
    }
}
static void offsets(Layout *l)
{
    size_t i;int64_t pc=0;
    for(i=0;i<l->count;++i){
        Line *line=&l->lines[i];
        if(line->prefix&&!line->removed)pc+=l->lines[line->prefix-1].bytes;
        line->offset=pc;
        if(line->in_code&&!line->removed)pc+=line->bytes;
    }
}
static void relax(Layout *l)
{
    int changed;size_t i;
    /* Start at the smallest layout. This also handles mutually dependent
     * branches that only fit when both are short. Remove fallthroughs first;
     * subsequent widening can only increase the remaining distances. */
    for(i=0;i<l->count;++i){Line *line=&l->lines[i];
        if(!line->removed&&(line->kind==JUMP||line->kind==CONDITIONAL)&&line->destination!=SIZE_MAX)line->bytes=2;
    }
    do{
        changed=0;offsets(l);
        for(i=0;i<l->count;++i){
            Line *line=&l->lines[i];
            if(!line->removed&&line->bytes==2&&(line->kind==JUMP||line->kind==CONDITIONAL)&&line->destination!=SIZE_MAX&&
               l->lines[line->destination].offset==line->offset+2){line->bytes=0;changed=1;}
        }
    }while(changed);
    do{
        changed=0;offsets(l);
        for(i=0;i<l->count;++i){
            Line *line=&l->lines[i];int64_t displacement;
            if(line->removed||line->bytes!=2||(line->kind!=JUMP&&line->kind!=CONDITIONAL)||line->destination==SIZE_MAX)continue;
            displacement=l->lines[line->destination].offset-(line->offset+2);
            if(displacement< -128||displacement>127){line->bytes=line->kind==JUMP?3:5;changed=1;}
        }
    }while(changed);
}
/* A local branch landing directly on a return can return at its source.
 * Keep the shared return for every other entry and use its actual ABI. */
static void fold_return_jumps(Layout *layout)
{
    for(size_t i=0;i<layout->count;++i){
        Line *line=&layout->lines[i];
        if(!line->in_function||line->removed||line->kind!=JUMP||line->destination==SIZE_MAX)continue;
        for(size_t j=line->destination;j<layout->count;++j){
            Line *next=&layout->lines[j];
            if(!next->in_code||next->placement!=line->placement)break;
            if(next->removed||!next->bytes)continue;
            if(!strcmp(next->op,"rts")||!strcmp(next->op,"rtl")){
                strcpy(line->op,next->op);
                line->kind=RETURN;line->bytes=1;line->destination=SIZE_MAX;
            }
            break;
        }
    }
}
/* A short backward jump to a comparison and exit test can test locally.
 * The taken edge then returns to the body, and the last trip falls through. */
static int fold_loop_tests(Layout *layout)
{
    int changed=0;
    for(size_t i=0;i<layout->count;++i){
        Line *edge=&layout->lines[i];
        if(!edge->in_function||edge->removed||edge->kind!=JUMP||edge->bytes!=2||
           edge->destination>=i)continue;
        size_t cmp=edge->destination;
        while(cmp<i&&(layout->lines[cmp].removed||!layout->lines[cmp].bytes))++cmp;
        Line *test=&layout->lines[cmp];
        const char *immediate=strchr(test->text,'#');unsigned literal;
        if((strcmp(test->op,"cmp")&&strcmp(test->op,"cpx")&&strcmp(test->op,"cpy"))||
           !immediate||!number(immediate+1,&literal)||test->widths!=edge->widths||test->placement!=edge->placement)continue;
        size_t j=cmp+1;
        while(j<i&&(layout->lines[j].removed||!layout->lines[j].bytes))++j;
        Line *guard=&layout->lines[j];
        if(guard->kind!=CONDITIONAL||guard->bytes!=2||guard->destination==SIZE_MAX||
           layout->lines[guard->destination].offset!=edge->offset+edge->bytes)continue;
        size_t body=j+1;
        while(body<i&&(layout->lines[body].removed||!layout->lines[body].bytes)){
            if(!layout->lines[body].removed&&layout->lines[body].kind==LABEL)break;
            ++body;
        }
        if(body>=i||layout->lines[body].kind!=LABEL||layout->lines[body].placement!=edge->placement)continue;
        strcpy(edge->op,inverse(guard->op));
        edge->kind=CONDITIONAL;edge->destination=body;edge->prefix=cmp+1;changed=1;
    }
    return changed;
}
/* Both endpoints are already laid out. Bypass a jump only when the
 * conditional instruction retains its short encoding and its placement. */
static int thread_short_branches(Layout *layout)
{
    int changed=0;
    for(size_t i=0;i<layout->count;++i){
        Line *line=&layout->lines[i];
        if(!line->in_function||line->removed||line->kind!=CONDITIONAL||line->bytes!=2||
           line->destination==SIZE_MAX)continue;
        for(size_t j=line->destination;j<layout->count;++j){
            Line *next=&layout->lines[j];int64_t displacement;
            if(!next->in_code||next->placement!=line->placement)break;
            if(next->removed||!next->bytes)continue;
            if(next->kind!=JUMP||next->destination==SIZE_MAX)break;
            Line *target=&layout->lines[next->destination];
            displacement=target->offset-(line->offset+2);
            if(target->placement==line->placement&&displacement>=-128&&displacement<=127&&
               line->destination!=next->destination){
                line->destination=next->destination;
                changed=1;
            }
            break;
        }
    }
    return changed;
}
/* Inspect straight-line instructions separated only by compiler markers.
 * A branch target in that interval can enter with different accumulator bits. */
static size_t bit_test_successor(Layout *layout,size_t start)
{
    size_t i=start+1;
    for(;i<layout->count;++i){
        Line *l=&layout->lines[i];
        if(!l->in_function||l->placement!=layout->lines[start].placement||l->prefix)return SIZE_MAX;
        if(l->removed)continue;
        if(l->bytes)return i;
        if(l->kind==LABEL){
            if(l->refs||(strncmp(l->label,"cg_",3)&&strncmp(l->label,"__inlined_",10)))return SIZE_MAX;
        }else{
            const char *p=l->text;
            while(isspace((unsigned char)*p))++p;
            if(*p&&*p!=';'&&strncmp(p,".export __inlined_",18))return SIZE_MAX;
        }
    }
    return SIZE_MAX;
}
static int fold_bit_tests(Layout *layout)
{
    int changed=0;
    for(size_t i=0;i<layout->count;++i)layout->lines[i].refs=0;
    for(size_t i=0;i<layout->count;++i){
        Line *branch=&layout->lines[i];
        if(!branch->removed&&branch->bytes&&branch->destination!=SIZE_MAX)++layout->lines[branch->destination].refs;
    }
    for(size_t i=0;i<layout->count;++i){
        Line *a=&layout->lines[i];
        if(!a->in_function||a->removed||a->prefix||strcmp(a->op,"bit")||!(a->widths&1))continue;
        size_t first=bit_test_successor(layout,i);
        size_t second=first==SIZE_MAX?SIZE_MAX:bit_test_successor(layout,first);
        size_t last=second==SIZE_MAX?SIZE_MAX:bit_test_successor(layout,second);
        if(last==SIZE_MAX)continue;
        Line *b=&layout->lines[first],*c=&layout->lines[second],*d=&layout->lines[last];
        unsigned x,y;
        if(strcmp(b->op,"bne")||b->destination==SIZE_MAX||strcmp(c->op,"bit")||
           c->widths!=a->widths||strcmp(d->op,"bne")||b->destination!=d->destination||
           strncmp(a->text,"    bit #$",10)||strncmp(c->text,"    bit #$",10)||
           strlen(a->text)!=14||strlen(c->text)!=14||!number(a->text+9,&x)||!number(c->text+9,&y))continue;
        /* Keep the later test; another pair can then be merged in this pass */
        char result[32];
        snprintf(result,sizeof result,"    bit #$%04X",x|y);
        char *text=copy_text(result,strlen(result));
        if(!text)continue;
        free(c->text);c->text=text;a->removed=b->removed=1;changed=1;
    }
    return changed;
}
int relax_assembly(FILE *out,const char *assembly,const char *unit,int enabled)
{
    Layout layout={0};size_t i;int ok=1;
    if(!enabled)return fputs(assembly,out)>=0;
    if(!parse(&layout,assembly,unit)){ok=0;goto cleanup;}
    relax(&layout);
    for(i=0;i<layout.count;++i)
        if((layout.lines[i].kind==JUMP||layout.lines[i].kind==CONDITIONAL)&&!layout.lines[i].bytes)
            layout.lines[i].removed=1;
    fold_named(&layout);
    fold_return_jumps(&layout);
    relax(&layout);
    if(fold_loop_tests(&layout))relax(&layout);
    if(thread_short_branches(&layout)){
        fold_named(&layout);
        relax(&layout);
    }
    if(fold_bit_tests(&layout))relax(&layout);
    for(i=0;i<layout.count;++i){
        Line *line=&layout.lines[i];if(line->removed)continue;
        if(line->prefix)fprintf(out,"%s\n",layout.lines[line->prefix-1].text);
        if(line->kind==LABEL&&line->anonymous)fprintf(out,"%s = *\n",line->label);
        else if(line->kind==RETURN)fprintf(out,"    %s\n",line->op);
        else if(line->kind==JUMP||line->kind==CONDITIONAL){
            if(!line->bytes)continue;
            if(line->bytes==2)fprintf(out,"    %s %s\n",line->kind==JUMP?"bra":line->op,layout.lines[line->destination].label);
            else if(line->kind==JUMP)fprintf(out,"    jmp .loword(%s)\n",line->target);
            else fprintf(out,"    %s :+\n    jmp .loword(%s)\n:\n",inverse(line->op),line->destination==SIZE_MAX?line->target:layout.lines[line->destination].label);
        }else fprintf(out,"%s\n",line->text);
    }
    ok=!ferror(out);
cleanup:
    for(i=0;i<layout.count;++i){free(layout.lines[i].text);free(layout.lines[i].label);free(layout.lines[i].target);}
    free(layout.lines);free(layout.hash);return ok;
}
