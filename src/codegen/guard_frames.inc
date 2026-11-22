enum { GUARD_FRAME_LINES=160, GUARD_FRAME_WORDS=4 };
typedef struct {
    int frame,argument,entry,early,body,tail;
    int homes[GUARD_FRAME_WORDS],scratch[GUARD_FRAME_WORDS],count;
    unsigned stores[GUARD_FRAME_LINES],defined[GUARD_FRAME_LINES];
    unsigned char reachable[GUARD_FRAME_LINES];
    int carry,save_argument;
} GuardFrame;

static int lp_y_frame_word(const LpLine *line,int frame)
{
    size_t n;
    const char *operand=lp_operand(line,&n);
    if(n!=9||strncmp(operand,"a:$",3)||strncmp(operand+7,",y",2)||line->x8)return 0;
    int slot=(int)strtol(operand+3,NULL,16);
    return slot>0&&slot+lp_width(line)-1<=frame?slot:0;
}

static int lp_y_frame_release(const LpUnit *u,int start,int frame,int *last)
{
    static const char *const ops[]={"tya","clc",NULL,"tcs","ply"};
    int i=start;
    for(unsigned k=0;k<sizeof ops/sizeof *ops;++k){
        if(i<0||u->lines[i].m8||u->lines[i].x8)return 0;
        if(ops[k]){
            if(!lp_line_is(&u->lines[i],ops[k]))return 0;
        }else if(!lp_is(&u->lines[i],"adc")||lp_immediate(&u->lines[i])!=frame)return 0;
        if(k+1<sizeof ops/sizeof *ops)i=lp_next(u,(unsigned)i,1);
    }
    *last=i;
    return 1;
}

static int lp_guard_frame_call(const LpLine *line,int tail)
{
    Symbol *callee=lp_callee(line);
    if(!callee||callee->interrupt||callee->variadic||callee->old_style||
       structure_object(callee->type)||reg_width(callee->type)>2||
       callee->param_count<0||callee->param_count>(tail?1:2)||
       line->m8||line->x8)return 0;
    for(int i=0;i<callee->param_count;++i)
        if(!register_parameter((unsigned)i,callee->params[i]))return 0;
    return 1;
}

static void lp_guard_frame_edge(GuardFrame *p,int target,unsigned definitions)
{
    if(p->reachable[target])p->defined[target]&=definitions;
    else p->defined[target]=definitions;
    p->reachable[target]=1;
}

/* Validate the frame-free guard and track which words were assigned on every
 * edge into its framed continuation */
static int lp_guard_frame_prefix(const LpUnit *u,GuardFrame *p)
{
    unsigned taken=lp_text_words(u->text,u->lines[u->count-1].text+u->lines[u->count-1].length);
    p->reachable[p->entry]=1;
    for(int i=p->entry;i<p->early;++i){
        const LpLine *l=&u->lines[i];
        unsigned definitions=p->defined[i];
        if(!p->reachable[i])return 0;
        if(l->op){
            int slot=lp_y_frame_word(l,p->frame);
            size_t n;
            const char *operand=lp_operand(l,&n);
            if(l->m8||l->x8||l->use==LP_ALL||lp_stack_op(l)||
               lp_is(l,"tsc")||lp_is(l,"tsx")||(l->def&(LP_X|LP_Y))||
               (n>=2&&operand[n-2]==','&&operand[n-1]=='s'))return 0;
            if(slot){
                int word=0;
                if(!lp_is(l,"sta")||abs(slot-p->argument)<2)return 0;
                while(word<p->count&&p->homes[word]!=slot){
                    if(abs(slot-p->homes[word])<2)return 0;
                    ++word;
                }
                if(word==p->count){
                    int scratch=0;
                    while(scratch<16&&(taken&(1u<<scratch)))++scratch;
                    if(word==GUARD_FRAME_WORDS||scratch==16)return 0;
                    taken|=1u<<scratch;
                    p->scratch[word]=scratch*2;
                    p->homes[p->count++]=slot;
                }
                definitions|=1u<<word;
                p->stores[i]=(unsigned)word+1;
            }else if((l->use&LP_Y)||(lp_store_op(l)&&!lp_operand_is(l,"a",1)))return 0;
            if(l->target>=0){
                if(l->target<=i||l->target>p->body||
                   (l->target>=p->early&&l->target!=p->early&&l->target!=p->body))return 0;
                lp_guard_frame_edge(p,l->target,definitions);
            }else if(l->ends||lp_branch(l))return 0;
        }
        if(!l->ends)lp_guard_frame_edge(p,i+1,definitions);
    }
    return p->reachable[p->body]&&p->defined[p->body]==(1u<<p->count)-1;
}

/* The short arm may call register-only functions and reload its original
 * argument. Both ordinary returns and tail calls release that one saved word. */
static int lp_guard_frame_early(const LpUnit *u,GuardFrame *p,const char *ret)
{
    int ops=0,exits=0;
    for(int i=p->early;i<p->body;++i){
        const LpLine *l=&u->lines[i];
        if(!l->op)continue;
        ++ops;
        int slot=lp_y_frame_word(l,p->frame);
        size_t n;
        const char *operand=lp_operand(l,&n);
        if(l->x8||l->use==LP_ALL||(n>=2&&operand[n-2]==','&&operand[n-1]=='s'))return 0;
        if(slot){
            if(slot!=p->argument||l->m8||(!lp_is(l,"ldx")&&!lp_is(l,"lda")))return 0;
            p->save_argument=1;
        }else if(l->call){
            if(!lp_guard_frame_call(l,0))return 0;
        }else if(lp_is(l,"tya")){
            int last,jump;
            if(p->tail>=0||!lp_y_frame_release(u,i,p->frame,&last)||
               (jump=lp_next(u,(unsigned)last,1))<0||jump>=p->body||
               !(lp_is(&u->lines[jump],"jmp")||lp_is(&u->lines[jump],"jml"))||
               u->lines[jump].target>=0||!lp_guard_frame_call(&u->lines[jump],1))return 0;
            p->tail=i;
            ++exits;
            i=jump;
        }else if(l->ends&&l->target>=p->body){
            int target=l->target,last;
            if(l->m8||strncmp(u->lines[target].text,"return_",7))return 0;
            while(++target<(int)u->count&&!u->lines[target].op){}
            if(target>=(int)u->count||!lp_y_frame_release(u,target,p->frame,&last)||
               (target=lp_next(u,(unsigned)last,1))<0||!lp_line_is(&u->lines[target],ret))return 0;
            ++exits;
        }else if(l->target>=0){
            if(l->target<=p->early||l->target<=i||l->target>=p->body)return 0;
        }else if(l->ends||lp_stack_op(l)||lp_is(l,"tsc")||lp_is(l,"tsx")||
                 ((l->use|l->def)&LP_Y))return 0;
    }
    int last=p->body;
    while(--last>=p->early&&!u->lines[last].op){}
    return ops&&exits&&last>=p->early&&u->lines[last].ends;
}

static void lp_guard_frame_emit(LpUnit *u,const GuardFrame *p,int prologue,int save,
                                const char *ret)
{
    char text[96];
    int body=p->body,early=p->early;
    while(!u->lines[body].op)++body;
    while(!u->lines[early].op)++early;
    if(p->save_argument)lp_insert(&u->lines[early],"    phx\n");
    lp_insert(&u->lines[body],"; allocate frame after entry guards\n");
    for(int i=prologue;i<=save;++i){
        if(!u->lines[i].op)continue;
        snprintf(text,sizeof text,"%.*s\n",(int)u->lines[i].length,u->lines[i].text);
        lp_insert(&u->lines[body],text);
        u->lines[i].deleted=1;
    }
    for(int i=p->entry;i<p->early;++i){
        if(!p->stores[i])continue;
        int word=(int)p->stores[i]-1;
        lp_set(&u->lines[i],"    sta z:__arith_lhs+%d",p->scratch[word]);
        snprintf(text,sizeof text,"    lda z:__arith_lhs+%d\n    sta a:$%04X,y\n",
                 p->scratch[word],p->homes[word]);
        lp_insert(&u->lines[body],text);
    }
    if(p->carry>=0)lp_insert(&u->lines[body],p->carry?"    sec\n":"    clc\n");
    for(int i=early;i<p->body;++i){
        LpLine *l=&u->lines[i];
        if(i==p->tail){
            int last;
            if(!lp_y_frame_release(u,i,p->frame,&last))return;
            if(p->save_argument)lp_insert(l,"    pla\n");
            for(;i<=last;++i)if(u->lines[i].op)u->lines[i].deleted=1;
            --i;
        }else if(l->op&&lp_y_frame_word(l,p->frame)==p->argument){
            if(lp_is(l,"lda"))lp_set(l,"    lda 1,s");
            else if(!l->m8&&!(l->out&LP_A)){
                lp_insert(l,"    lda 1,s\n");
                lp_set(l,"    tax");
            }else{
                lp_insert(l,"    plx\n");
                lp_set(l,"    phx");
            }
        }else if(l->ends&&l->target>=p->body){
            if(p->save_argument)lp_insert(l,"    pla\n");
            lp_set(l,"    %s",ret);
        }
    }
}

static int lp_delay_guard_frame(LpUnit *u,Function *f,size_t at)
{
    static const char *const setup[]={"phy","tsc","sec",NULL,"tcs","tay","txa","sta"};
    int start=0,i,frame=0;
    const char *ret=cg.parser->long_return?"rtl":"rts";
    (void)at;
    if(!f->frame||cg.lp_value_result||cg.lp_volatile||cg.lp_frame_address||
       cg.parser->no_private_regions||cg.parser->no_stack_frames||cg.parser->no_direct_dpage||
       f->aggregate_abi||f->uses_varargs||f->symbol->interrupt||f->symbol->variadic||
       f->jump_label_count||u->indirect||
       f->symbol->param_count!=1||!register_parameter(0,f->symbol->params[0])||
       body_asm_statements(f->body)||!lp_fixed_workspace(u))return 0;
    while((unsigned)start<u->count&&!u->lines[start].op)++start;
    if((unsigned)start==u->count)return 0;
    i=start;
    for(unsigned k=0;k<sizeof setup/sizeof *setup;++k){
        if(i<0||u->lines[i].m8||u->lines[i].x8)return 0;
        if(k==3){
            if(!lp_is(&u->lines[i],"sbc")||(frame=(int)lp_immediate(&u->lines[i]))<2)return 0;
        }else if(k==7){
            if(!lp_is(&u->lines[i],setup[k]))return 0;
        }else if(!lp_line_is(&u->lines[i],setup[k]))return 0;
        if(k<7)i=lp_next(u,(unsigned)i,1);
    }
    int argument=lp_y_frame_word(&u->lines[i],frame);
    int entry=i+1;
    if(!argument||(unsigned)entry>=u->count)return 0;
    lp_liveness(u);
    if(u->lines[entry].live&(LP_A|LP_FLAGS))return 0;
    for(int branch=entry;branch<GUARD_FRAME_LINES&&(unsigned)branch<u->count;++branch){
        int after,body=lp_cond_branch_target(u,branch,&after);
        if(u->lines[branch].call)break;
        if(body<0||body>=GUARD_FRAME_LINES||body<=after+1)continue;
        GuardFrame p={0};
        p.frame=frame;p.argument=argument;p.entry=entry;
        p.early=after+1;p.body=body;p.tail=-1;p.carry=-1;
        if(!lp_guard_frame_prefix(u,&p)||!lp_guard_frame_early(u,&p,ret))continue;
        int body_op=body;
        while((unsigned)body_op<u->count&&!u->lines[body_op].op)++body_op;
        if((unsigned)body_op>=u->count||(u->lines[body_op].live&(LP_A|LP_N|LP_Z|LP_V)))continue;
        /* Every external edge into the rewritten region must cross its entry */
        int external=0;
        for(int k=entry;k<body_op;++k){
            for(int pred=u->lines[k].first_incoming;pred>=0;pred=u->lines[pred].next_incoming)
                if(pred<entry||pred>=body||(pred>=p.early&&(k<=p.early||k>=body)))external=1;
        }
        if(external)continue;
        if(u->lines[body_op].live&LP_C){
            if(u->lines[body].first_incoming!=(after==branch?branch:branch+1)||
               u->lines[u->lines[body].first_incoming].next_incoming>=0||
               (!lp_is(&u->lines[branch],"bcc")&&!lp_is(&u->lines[branch],"bcs")))continue;
            p.carry=lp_is(&u->lines[branch],after==branch?"bcs":"bcc");
        }
        lp_guard_frame_emit(u,&p,start,i,ret);
        return 1;
    }
    return 0;
}
