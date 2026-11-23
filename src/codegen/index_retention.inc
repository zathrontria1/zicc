/* Loop-local retained displacements. Selection is typed and speculative: the
 * emitted body must respect the reserved registers, including scratch saves.
 * Y can hold the C counter only when no frame-base access remains in the body.
 * Otherwise a second trial retains just the dominant byte displacement in X. */
typedef struct { unsigned stride[16],uses[16],count;Symbol *other[16];unsigned other_scale[16],other_uses[16],others; } RetainedPlan;
static void retained_record_stride(RetainedPlan *plan,unsigned scale)
{
    unsigned i;
    if(!scale||scale>65535)return;
    for(i=0;i<plan->count&&plan->stride[i]!=scale;++i){}
    if(i==plan->count&&i<16){plan->stride[i]=scale;plan->uses[i]=0;++plan->count;}
    if(i<16)++plan->uses[i];
}
static int retained_expression(Expr *e,RetainedPlan *plan)
{
    IndexedOperand operand;unsigned a,b,i,scale;
    DotProduct *dp;
    if(!e)return 1;
    /* A named aggregate base contributes no register operations itself */
    if(e->kind==EX_OBJECT&&structure_object(e->type)&&!e->symbol->owner)return 1;
    if(e->kind==EX_CALL||(!e->type.array&&!e->type.pointers&&!structure_object(e->type)&&reg_width(e->type)>2))return 0;
    dp=dot_match_expr(e);
    if(dp){
        for(i=0;i<dp->term_count;++i){
            Expr *idx=NULL;unsigned off=0,term_scale=0;
            if(dot_indexed_byte(dp->terms[i].value_expr,NULL,&idx,&off,&term_scale,NULL)){
                if(!retained_expression(idx,plan))return 0;
                if(retained_affine(idx,&a,&b)&&a&&(int16_t)b>=0)
                    retained_record_stride(plan,a*term_scale);
            }
        }
        return 1;
    }
    if(indexed_operand(e,&operand)&&retained_affine(operand.index,&a,&b)&&a&&(int16_t)b>=0){
        retained_record_stride(plan,a*operand.scale);
    }else if((e->kind==EX_MEMBER||e->kind==EX_DEREF)&&!volatile_expression(e)&&
             !e->type.array&&!structure_object(e->type)&&reg_width(e->type)==2){
        Expr *root=e,*address;unsigned offset=0;int pointer=0;
        if(e->kind==EX_MEMBER)root=member_root(e,&offset,&pointer);
        address=pointer?root:(root->kind==EX_DEREF?root->left:NULL);
        if(address&&address->kind==EX_BINARY&&address->op=='+'&&address->left->kind==EX_OBJECT&&
           address->left->symbol->type.array&&address->left->symbol->type.banked&&
           !address->left->symbol->wram&&
           width(address->left->symbol->type)<=65536&&
           retained_affine(address->right,&a,&b)&&a&&(int16_t)b>=0){
            scale=width(pointed_type(value_type(address->left->type)));
            retained_record_stride(plan,a*scale);
        }
    }
    if(indexed_operand(e,&operand)){
        Expr *index=operand.index;
        while(index->kind==EX_CAST&&width(index->type)==2)index=index->left;
        if(index->kind==EX_OBJECT&&index->symbol!=cg.retained_index&&loop_private(index->symbol)&&
           width(index->type)==1&&index->type.is_unsigned&&operand.offset==0&&operand.scale>1&&operand.scale<=128&&!(operand.scale&(operand.scale-1))){
            for(i=0;i<plan->others&&(plan->other[i]!=index->symbol||plan->other_scale[i]!=operand.scale);++i){}
            if(i==plan->others&&i<16){plan->other[i]=index->symbol;plan->other_scale[i]=operand.scale;++plan->others;}
            if(i<16)++plan->other_uses[i];
        }
    }
    if(!retained_expression(e->left,plan)||!retained_expression(e->right,plan)||!retained_expression(e->third,plan))return 0;
    return 1;
}
static int retained_statements(Statement *s,RetainedPlan *plan)
{
    for(;s;s=s->next){
        if(s->kind!=ST_BLOCK&&s->kind!=ST_EXPR&&s->kind!=ST_IF&&s->kind!=ST_EMPTY&&
           s->kind!=ST_BREAK&&s->kind!=ST_CONTINUE)return 0;
        if(!retained_expression(s->expression,plan)||!retained_statements(s->body,plan)||
           !retained_statements(s->alternate,plan))return 0;
    }return 1;
}
static int retained_op(const char *p,size_t n,const char *op)
{
    size_t k=strlen(op);return n>=k&&!strncmp(p,op,k)&&(n==k||p[k]==' '||p[k]=='\t');
}
static int retained_reject(const char *p,size_t n)
{
    if (getenv("ZICC_RETAINED_TRACE")) {
        fprintf(stderr, "retained selection rejected: %.*s\n", (int)n, p);
    }
    return 0;
}
static int retained_scan(size_t first,size_t last,int y,int counter_only)
{
    /* Mode 4 reserves only the enclosing Y binding; X belongs to the body.
     * Inspect inner-loop instructions too, including their setup and exits. */
    const char *p=cg.assembly+first,*end=cg.assembly+last;unsigned scratch=0,owned=0,bytes=0,y_uses=0;
    while(p<end){
        const char *q=memchr(p,'\n',(size_t)(end-p));size_t n;const char *op;
        if (!q) {
            q = end;
        }
        n = (size_t)(q - p);
        if(n==29&&!strncmp(p,"; retained byte indices begin",29)){if(bytes||counter_only)return retained_reject(p,n);bytes=1;}
        else if(n==27&&!strncmp(p,"; retained byte indices end",27)){if(!bytes)return retained_reject(p,n);bytes=0;}
        else if(bytes){/* The byte-region selector owns and restores both bindings */}
        else if(n==24&&!strncmp(p,"; retained scratch begin",24)){if(counter_only)return retained_reject(p,n);++scratch;}
        else if(n==22&&!strncmp(p,"; retained scratch end",22)){if(!scratch)return retained_reject(p,n);--scratch;}
        else if(n==24&&!strncmp(p,"; retained counter begin",24))++owned;
        else if(n==22&&!strncmp(p,"; retained counter end",22)){if(!owned)return retained_reject(p,n);--owned;}
        else if(n>4&&!strncmp(p,"    ",4)){
            const char *comma=NULL;size_t k;op=p+4;
            for(k=4;k+1<n;++k)if(p[k]==','&&(p[k+1]=='x'||p[k+1]=='y'))comma=p+k;
            if(retained_op(op,n-4,"jsr")||retained_op(op,n-4,"jsl")||retained_op(op,n-4,"mvn")||
               retained_op(op,n-4,"mvp")||retained_op(op,n-4,"plp")||retained_op(op,n-4,"xce")||
               retained_op(op,n-4,"rti")||retained_op(op,n-4,"rts")||retained_op(op,n-4,"jml")||
               retained_op(op,n-4,"pld")||retained_op(op,n-4,"tcd"))return retained_reject(p,n);
            if((retained_op(op,n-4,"sep")||retained_op(op,n-4,"rep"))&&
               ((n>=12&&!strncmp(op+4,"#$",2)&&strtoul(op+6,NULL,16)&16)))return retained_reject(p,n);
            if(y!=4&&y!=5&&!scratch&&(retained_op(op,n-4,"ldx")||retained_op(op,n-4,"tax")||retained_op(op,n-4,"plx")||
               retained_op(op,n-4,"inx")||retained_op(op,n-4,"dex")||retained_op(op,n-4,"tyx")||
               retained_op(op,n-4,"txa")||retained_op(op,n-4,"txy")||retained_op(op,n-4,"tsx")||
               retained_op(op,n-4,"txs")||retained_op(op,n-4,"stx")||retained_op(op,n-4,"cpx")||retained_op(op,n-4,"phx")))return retained_reject(p,n);
            if(y&&(retained_op(op,n-4,"ldy")||retained_op(op,n-4,"tay")||retained_op(op,n-4,"ply")||
               retained_op(op,n-4,"iny")||retained_op(op,n-4,"dey")||retained_op(op,n-4,"txy")||
               retained_op(op,n-4,"tyx")||retained_op(op,n-4,"sty")||retained_op(op,n-4,"cpy")||(!owned&&retained_op(op,n-4,"tya"))))return retained_reject(p,n);
            if(comma&&((comma[1]=='x'&&!scratch&&y!=4&&y!=5)||(comma[1]=='y'&&y))){
                if(counter_only)return retained_reject(p,n);
                /* Only explicit fixed-symbol operands refer to our offsets.
                 * Generic pointer dereferences and Y-frame homes reject. */
                int symbol=0;for(k=4;k<(size_t)(comma-p);++k)if(p[k]=='_')symbol=1;
                if(!symbol)return retained_reject(p,n);
            }
            if(comma&&comma[1]=='y'&&!scratch)++y_uses;
        }p=q+1;
    }
    if(y==5&&!y_uses)return 0;
    return !scratch&&!owned&&!bytes;
}
static void retained_advance_x(unsigned scale)
{
    unsigned i;
    if(scale<=3)for(i=0;i<scale;++i)code("    inx\n");
    else code("    txa\n    clc\n    adc #$%04X\n    tax\n",scale);
}
/* A for initializer may contain other private initializations. Fold only a
 * straight-line, literal final definition, with the counter's C conversion. */
static int retained_initial_constant(Statement *s,Symbol *index,uint32_t *value,int *found)
{
    for(;s;s=s->next){
        Expr *e=s->expression;
        if(s->kind==ST_BLOCK){if(!retained_initial_constant(s->body,index,value,found))return 0;}
        else if(s->kind==ST_EXPR){
            if(scalar_writes_expr(e,index)){
                *found=e->kind==EX_ASSIGN&&!e->op&&e->left->kind==EX_OBJECT&&e->left->symbol==index&&integer_constant(e->right,value);
                if(*found)*value=initializer_cast(*value,index->type)&65535;
            }
        }else if(s->kind!=ST_EMPTY)return 0;
    }return 1;
}
static int retained_initial_nonneg(Statement *s,Symbol *index,unsigned limit,int *found)
{
    for(;s;s=s->next){
        Expr *e=s->expression;
        if(s->kind==ST_BLOCK){if(!retained_initial_nonneg(s->body,index,limit,found))return 0;}
        else if(s->kind==ST_EXPR){
            if(scalar_writes_expr(e,index)){
                uint32_t v;
                if(e->kind!=EX_ASSIGN||e->op||e->left->kind!=EX_OBJECT||e->left->symbol!=index){*found=0;continue;}
                if(integer_constant(e->right,&v)){
                    v=initializer_cast(v,index->type)&65535;
                    *found=v<=limit;
                }else{
                    *found=e->right->known.valid&&e->right->known.min>=0&&e->right->known.max<=(int32_t)limit;
                }
            }
        }else if(s->kind!=ST_EMPTY)return 0;
    }return 1;
}
static unsigned lp_text_words(const char *p,const char *end);
static unsigned retained_count_sym_expr(Expr *e,Symbol *sym)
{
    unsigned n=0,i;
    if(!e)return 0;
    if(e->kind==EX_OBJECT&&e->symbol==sym)n=1;
    n+=retained_count_sym_expr(e->left,sym)+retained_count_sym_expr(e->right,sym)+
       retained_count_sym_expr(e->third,sym);
    for(i=0;i<e->arg_count;++i)n+=retained_count_sym_expr(e->args[i],sym);
    return n;
}
static unsigned retained_count_sym_stmt(Statement *s,Symbol *sym)
{
    unsigned n=0;
    for(;s;s=s->next){
        n+=retained_count_sym_expr(s->expression,sym)+retained_count_sym_expr(s->step,sym)+
           retained_count_sym_stmt(s->initial,sym)+retained_count_sym_stmt(s->body,sym)+
           retained_count_sym_stmt(s->alternate,sym);
    }return n;
}
static int retained_y5_scan_expr(Expr *e,Symbol *index,Symbol **ptr_out,unsigned *ptr_uses,int in_lvalue)
{
    unsigned i;
    if(!e)return 1;
    if(!in_lvalue&&e->kind==EX_DEREF&&!volatile_expression(e)){
        Expr *addr=e->left;
        while(addr&&addr->kind==EX_CAST&&value_type(addr->type).pointers&&
              !far_pointer(value_type(addr->type))&&reg_width(addr->left->type)==2&&
              value_type(addr->left->type).pointers)addr=addr->left;
        if(addr&&addr->kind==EX_BINARY&&addr->op=='+'){
            Expr *l=addr->left,*r=addr->right,*p_expr=NULL,*i_expr=NULL;
            while(l->kind==EX_CAST&&!value_type(l->type).pointers&&reg_width(l->left->type)==2)l=l->left;
            while(r->kind==EX_CAST&&!value_type(r->type).pointers&&reg_width(r->left->type)==2)r=r->left;
            if(l->kind==EX_OBJECT&&value_type(l->type).pointers&&r->kind==EX_OBJECT&&r->symbol==index){p_expr=l;i_expr=r;}
            else if(r->kind==EX_OBJECT&&value_type(r->type).pointers&&l->kind==EX_OBJECT&&l->symbol==index){p_expr=r;i_expr=l;}
            if(p_expr&&i_expr){
                Symbol *p=p_expr->symbol;
                if(!p->owner||p->type.array||far_pointer(value_type(p->type))||reg_width(p->type)!=2||
                   object_volatile(p->type)||width(pointed_type(value_type(p->type)))!=1)return 0;
                if(*ptr_out&&*ptr_out!=p)return 0;
                *ptr_out=p;++(*ptr_uses);return 1;
            }
        }
    }
    if(e->kind==EX_ADDRESS)return retained_y5_scan_expr(e->left,index,ptr_out,ptr_uses,1);
    if(e->kind==EX_ASSIGN)
        return retained_y5_scan_expr(e->left,index,ptr_out,ptr_uses,1)&&
               retained_y5_scan_expr(e->right,index,ptr_out,ptr_uses,0);
    if(!retained_y5_scan_expr(e->left,index,ptr_out,ptr_uses,0)||
       !retained_y5_scan_expr(e->right,index,ptr_out,ptr_uses,0)||
       !retained_y5_scan_expr(e->third,index,ptr_out,ptr_uses,0))return 0;
    for(i=0;i<e->arg_count;++i)if(!retained_y5_scan_expr(e->args[i],index,ptr_out,ptr_uses,0))return 0;
    return 1;
}
static int retained_y5_scan_stmt(Statement *s,Symbol *index,Symbol **ptr_out,unsigned *ptr_uses)
{
    for(;s;s=s->next){
        if(!retained_y5_scan_expr(s->expression,index,ptr_out,ptr_uses,0)||
           !retained_y5_scan_expr(s->step,index,ptr_out,ptr_uses,0)||
           !retained_y5_scan_stmt(s->initial,index,ptr_out,ptr_uses)||
           !retained_y5_scan_stmt(s->body,index,ptr_out,ptr_uses)||
           !retained_y5_scan_stmt(s->alternate,index,ptr_out,ptr_uses))return 0;
    }return 1;
}
static Symbol *retained_y5_find_ptr(Statement *loop,Symbol *index)
{
    Symbol *ptr=NULL;unsigned uses=0,word;uint32_t start=0;int found=0,in,out;
    if(!dp_state.homes||!retained_initial_constant(loop->initial,index,&start,&found)||!found||start)return NULL;
    region_home_liveness(cg.function,loop,index->offset,&in,&out);
    if(out)return NULL;
    if(!retained_y5_scan_stmt(loop->body,index,&ptr,&uses)||!ptr||!uses)return NULL;
    word=(ptr->offset-1)/2;
    if(!ptr->offset||word>=dp_state.words||!dp_state.map[word])return NULL;
    if(scalar_writes(loop->body,ptr)||retained_count_sym_stmt(loop->body,ptr)!=uses)return NULL;
    region_home_liveness(cg.function,loop,ptr->offset,&in,&out);
    if(out)return NULL;
    return ptr;
}
typedef struct {
    Symbol *base[16];
    unsigned offset[16],scale[16],uses[16],unconditional[16],count;
} RetainedCursorPlan;
static void retained_collect_cursors_expr(Expr *e,Symbol *index,unsigned limit,unsigned x_scale,
                                          int conditional,RetainedCursorPlan *plan)
{
    IndexedOperand operand;unsigned a,b,scale,offset,i;
    if(!e||dot_match_expr(e))return;
    if(e->kind==EX_PRE||e->kind==EX_POST){
        if(indexed_operand(e->left,&operand))return;
    }
    if(indexed_operand(e,&operand)&&retained_affine_for(operand.index,index,&a,&b)&&a&&(int16_t)b>=0){
        scale=a*operand.scale;offset=b*operand.scale+operand.offset;
        if(scale>=2&&scale<=8&&scale!=x_scale&&offset<=65535&&
           (limit<=1||scale<=(65535-offset)/(limit-1))){
            for(i=0;i<plan->count;++i)
                if(plan->base[i]==operand.base&&plan->offset[i]==offset&&plan->scale[i]==scale)break;
            if(i==plan->count&&i<16){
                plan->base[i]=operand.base;plan->offset[i]=offset;plan->scale[i]=scale;
                plan->uses[i]=0;plan->unconditional[i]=0;++plan->count;
            }
            if(i<16){++plan->uses[i];if(!conditional)++plan->unconditional[i];}
        }
    }
    retained_collect_cursors_expr(e->left,index,limit,x_scale,conditional,plan);
    retained_collect_cursors_expr(e->right,index,limit,x_scale,conditional,plan);
    retained_collect_cursors_expr(e->third,index,limit,x_scale,conditional,plan);
    for(i=0;i<e->arg_count;++i)
        retained_collect_cursors_expr(e->args[i],index,limit,x_scale,conditional,plan);
}
static void retained_collect_cursors(Statement *s,Symbol *index,unsigned limit,unsigned x_scale,
                                     int conditional,RetainedCursorPlan *plan)
{
    for(;s;s=s->next){
        retained_collect_cursors_expr(s->expression,index,limit,x_scale,conditional,plan);
        retained_collect_cursors(s->body,index,limit,x_scale,conditional||s->kind==ST_IF,plan);
        retained_collect_cursors(s->alternate,index,limit,x_scale,1,plan);
    }
}
static int retained_unrollable_expr(Expr *e)
{
    unsigned i;
    if(!e)return 1;
    if(e->kind==EX_CALL)return 0;
    if(!retained_unrollable_expr(e->left)||!retained_unrollable_expr(e->right)||!retained_unrollable_expr(e->third))return 0;
    for(i=0;i<e->arg_count;++i)if(!retained_unrollable_expr(e->args[i]))return 0;
    return 1;
}
static int retained_unrollable_body(Statement *s)
{
    for(;s;s=s->next){
        if(s->kind==ST_BLOCK){if(!retained_unrollable_body(s->body))return 0;}
        else if(s->kind==ST_EXPR){if(!retained_unrollable_expr(s->expression))return 0;}
        else if(s->kind!=ST_EMPTY)return 0;
    }
    return 1;
}
static unsigned retained_body_insns(size_t first,size_t last)
{
    unsigned count=0;
    const char *p=cg.assembly+first,*end=cg.assembly+last;
    while(p<end){
        const char *q=memchr(p,'\n',(size_t)(end-p));
        size_t n=q?(size_t)(q-p):(size_t)(end-p);
        if(n>4&&!strncmp(p,"    ",4))++count;
        p=q?q+1:end;
    }
    return count;
}
static int retained_trial(Statement *s,Symbol *index,unsigned limit,unsigned scale,int y,Symbol *second,unsigned second_scale)
{
    CodegenCheckpoint *saved=malloc(sizeof *saved);size_t at=cg.length,first,last;unsigned enter,body,step,end,done,step_scale=scale;
    Statement *previous=loop_previous,*current=loop_current;
    int borrowed=second&&second==cg.retained_second&&second_scale==cg.retained_second_scale&&cg.retained_y==3&&!cg.retained_index;
    RetainedCursor cursors[MAX_RETAINED_CURSORS];unsigned cursor_count=0,cursor_mask=0;
    if(!saved){fputs("out of memory emitting retained loop\n",stderr);exit(EXIT_FAILURE);}cg_checkpoint_save(saved);
    Symbol *y5_ptr=y==5?retained_y5_find_ptr(s,index):NULL;
    for(int attempt=0;attempt<2;++attempt){
        uint32_t initial=0;int found=0;
        enter=++cg.label;body=++cg.label;step=++cg.label;end=++cg.label;done=++cg.label;
        if(borrowed)code("; retained nested begin\n");
        code("; retained loop indices: %c=stride %u%s\n",y==5?'Y':'X',scale,
             y==5?", X free":y==4?", counter eliminated":y==1?", Y=counter":y?", Y=scaled":"");
        if(second)code("; second retained displacement: %s stride %u\n",second->name,second_scale);
        for(unsigned ci=0;ci<cursor_count;++ci)
            code("; retained y-cursor: _%s+$%04X -> __arith_lhs+%u (stride %u)\n",
                 cursors[ci].base->asm_name,cursors[ci].offset,cursors[ci].dp_word*2u,cursors[ci].scale);
        branch(s->expression,enter,done,enter);label(enter);
        if(y==5){
            if(retained_initial_constant(s->initial,index,&initial,&found)&&found)
                code("    phy\n    ldy #$%04X\n",(initial*scale)&65535);
            else{Expr value={0};value.kind=EX_OBJECT;value.symbol=index;value.type=index->type;
                load_symbol(index);strength_scale(scale,&value);code("    phy\n    tay\n");}
        }else{
            if(retained_initial_constant(s->initial,index,&initial,&found)&&found)code("    ldx #$%04X\n",(initial*scale)&65535);
            else{Expr value={0};value.kind=EX_OBJECT;value.symbol=index;value.type=index->type;
                load_symbol(index);strength_scale(scale,&value);code("    tax\n");}
            if(y&&y!=4&&!borrowed){
                load_symbol(second?second:index);
                if(second){Expr value={0};value.kind=EX_OBJECT;value.symbol=second;value.type=second->type;strength_scale(second_scale,&value);}
                code("    phy\n    tay\n");
            }
        }
        for(unsigned ci=0;ci<cursor_count;++ci){
            cursors[ci].base->used=1;
            if(found){
                unsigned init_off=(cursors[ci].offset+initial*(cursors[ci].scale-1u))&65535u;
                code("    lda #.loword(_%s+$%04X)\n    sta z:__arith_lhs+%u\n",
                     cursors[ci].base->asm_name,init_off,cursors[ci].dp_word*2u);
            }else{
                code("    tya\n");
                if(cursors[ci].scale>2){
                    Expr value={0};value.kind=EX_OBJECT;value.symbol=index;value.type=index->type;
                    strength_scale(cursors[ci].scale-1u,&value);
                }
                code("    clc\n    adc #.loword(_%s+$%04X)\n    sta z:__arith_lhs+%u\n",
                     cursors[ci].base->asm_name,cursors[ci].offset,cursors[ci].dp_word*2u);
            }
        }
        cg.retained_second=second;cg.retained_second_scale=second_scale;
        cg.retained_index=index;cg.retained_ptr=y5_ptr;cg.retained_scale=scale;cg.retained_limit=limit;cg.retained_bias=0;cg.retained_unroll=0;
        cg.retained_y=y;cg.retained_scratch=0;cg.retained_failed=0;
        cg.retained_cursor_count=cursor_count;
        if(cursor_count)memcpy(cg.retained_cursors,cursors,cursor_count*sizeof cursors[0]);
        cg.retained_cursor_mask=saved->cg.retained_cursor_mask|cursor_mask;
        cg.loop_start[cg.loop_count]=step;cg.loop_end[cg.loop_count++]=end;
        divmod_state.available=0;label(body);first=cg.length;emit_statements(s->body);last=cg.length;
        if(cg.retained_failed||!retained_scan(first,last,y==4?0:y,0)){
            if(y5_ptr){
                y5_ptr=NULL;cg_checkpoint_restore(saved, at);loop_previous=previous;loop_current=current;continue;
            }
            cg_checkpoint_restore(saved, at);loop_previous=previous;loop_current=current;free(saved);return 0;
        }
        if(attempt==0&&y==4&&!cg.parser->no_loop_unroll&&!borrowed&&!cursor_count&&found&&initial<limit&&
           !body_asm_statements(s->body)&&retained_unrollable_body(s->body)){
            unsigned trips=limit-(unsigned)initial;
            unsigned insns=retained_body_insns(first,last);
            unsigned factor=(trips>=16&&(uint32_t)limit*scale<=65535u)?
                (!(trips%8)&&insns>=1&&insns<=6?8u:!(trips%4)&&insns>=1&&insns<=10?4u:0u):0u;
            if(factor>1){
                int unrolled_fail=0;
                cg.retained_unroll=factor;
                for(unsigned k=1;k<factor;++k){
                    size_t copy_start=cg.length;
                    cg.retained_bias=k;
                    emit_statements(s->body);
                    if(cg.retained_failed||!retained_scan(copy_start,cg.length,0,0)){unrolled_fail=1;break;}
                }
                cg.retained_bias=0;cg.retained_unroll=0;
                if(unrolled_fail){
                    cg.length=last;cg.assembly[last]=0;cg.retained_failed=0;
                }else{
                    step_scale=scale*factor;
                    code("; unrolled retained loop: %ux\n",factor);
                }
            }
        }
        if(attempt==0&&y==1&&!saved->cg.retained_cursor_count){
            RetainedCursorPlan plan={0};
            retained_collect_cursors(s->body,index,limit,scale,0,&plan);
            if(plan.count){
                unsigned used=lp_text_words(cg.assembly+first,cg.assembly+last)|0x05u|saved->cg.retained_cursor_mask;
                unsigned order[16],ocount=0;
                if(dp_state.homes)for(unsigned w=0;w<dp_state.words;++w)if(dp_state.map[w])used|=1u<<(dp_state.map[w]-1u);
                for(unsigned ci=0;ci<plan.count;++ci){
                    if(!plan.unconditional[ci]&&plan.uses[ci]<2)continue;
                    unsigned score=(plan.unconditional[ci]?1000u:0u)+plan.uses[ci]*4u+(plan.scale[ci]==2?100u:0u);
                    unsigned pos=ocount;
                    while(pos){
                        unsigned prev=order[pos-1];
                        unsigned prev_score=(plan.unconditional[prev]?1000u:0u)+plan.uses[prev]*4u+(plan.scale[prev]==2?100u:0u);
                        if(prev_score>=score)break;
                        order[pos]=order[pos-1];--pos;
                    }
                    order[pos]=ci;++ocount;
                }
                for(unsigned oi=0;oi<ocount&&cursor_count<MAX_RETAINED_CURSORS;++oi){
                    unsigned ci=order[oi];int free_word=-1;
                    for(int w=15;w>=1;--w)if(!(used&(1u<<w))){free_word=w;break;}
                    if(free_word<0)break;
                    used|=1u<<free_word;cursor_mask|=1u<<free_word;
                    cursors[cursor_count++]=(RetainedCursor){plan.base[ci],plan.offset[ci],plan.scale[ci],(unsigned)free_word};
                }
                if(cursor_count){
                    cg_checkpoint_restore(saved, at);loop_previous=previous;loop_current=current;
                    continue;
                }
            }
        }
        break;
    }
    divmod_state.available=0;label(step);
    for(unsigned ci=0;ci<cg.retained_cursor_count;++ci){
        unsigned dp_off=cg.retained_cursors[ci].dp_word*2u;
        unsigned delta=cg.retained_cursors[ci].scale-1u;
        if(delta==1)code("    inc z:__arith_lhs+%u\n",dp_off);
        else code("    lda z:__arith_lhs+%u\n    clc\n    adc #$%04X\n    sta z:__arith_lhs+%u\n",dp_off,delta,dp_off);
    }
    if(y==4){/* X alone carries the unobserved C counter */}
    else if(y==5&&cg.retained_ptr){code("    inc %s\n",frame_operand(cg.retained_ptr->offset));}
    else if(y==1)code("    iny\n");
    else if(y==2){unsigned j;for(j=0;j<second_scale;++j)code("    iny\n");}
    else{load_symbol(index);code("    inc a\n");narrow_char(index->type);store_symbol(index);}
    if(y==5){
        if(scale<=3){unsigned j;for(j=0;j<scale;++j)code("    iny\n");}
        else code("    tya\n    clc\n    adc #$%04X\n    tay\n",scale);
        code("    cpy #$%04X\n",limit*scale);
    }else{
        retained_advance_x(step_scale);
        if(y==1)code("    cpy #$%04X\n",limit);
        else if(y==2)code("    cpy #$%04X\n",limit*second_scale);
        else code("    cpx #$%04X\n",limit*scale);
    }
    code("    bcs :+\n");jump(body);code(":\n");
    label(end);--cg.loop_count;
    cg.retained_index=NULL;cg.retained_ptr=NULL;cg.retained_scale=cg.retained_limit=cg.retained_bias=cg.retained_unroll=0;cg.retained_y=cg.retained_scratch=0;cg.retained_failed=0;
    cg.retained_second=NULL;cg.retained_second_scale=0;
    cg.retained_cursor_count=0;cg.retained_cursor_mask=saved->cg.retained_cursor_mask;
    if(y==1||y==2){unsigned j=second_scale;code("    tya\n");if(y==2)while(j>1){code("    lsr a\n");j>>=1;}code("    ply\n");store_symbol(index);}
    else if(y&&y!=4&&!borrowed)code("    ply\n");
    if(borrowed){cg.retained_second=second;cg.retained_second_scale=second_scale;cg.retained_y=3;}
    label(done);divmod_state.available=0;
    if(borrowed)code("; retained nested end\n");
    loop_previous=previous;loop_current=current;free(saved);return 1;
}
/* Keep an enclosing displacement in Y while inner retained loops own X.
 * Counter homes remain synchronized at outer steps, including break exits.
 * The complete emitted region is checked for frame uses and Y clobbers. */
static int retained_nested_plan(Statement *s,RetainedPlan *plan,unsigned *loops)
{
    for(;s;s=s->next){
        if(s->kind==ST_FOR){
            if(++*loops>1||!retained_statements(s->body,plan)||
               !retained_expression(s->expression,plan)||!retained_expression(s->step,plan))return 0;
        }else if(s->kind!=ST_BLOCK&&s->kind!=ST_EXPR&&s->kind!=ST_IF&&s->kind!=ST_EMPTY&&
                 s->kind!=ST_BREAK&&s->kind!=ST_CONTINUE)return 0;
        if(!retained_expression(s->expression,plan)||
           (s->kind!=ST_FOR&&!retained_nested_plan(s->body,plan,loops))||
           !retained_nested_plan(s->alternate,plan,loops))return 0;
    }return 1;
}
static int retained_nested_trial(Statement *s,Symbol *index,unsigned limit,unsigned scale)
{
    CodegenCheckpoint *saved=malloc(sizeof *saved);size_t at=cg.length,first,last;unsigned enter,body,step,end,done,j;
    Statement *previous=loop_previous,*current=loop_current;
    if(!saved){fputs("out of memory emitting nested retained loop\n",stderr);exit(EXIT_FAILURE);}cg_checkpoint_save(saved);
    enter=++cg.label;body=++cg.label;step=++cg.label;end=++cg.label;done=++cg.label;
    code("; retained enclosing displacement: %s stride %u\n",index->name,scale);
    branch(s->expression,enter,done,enter);label(enter);load_symbol(index);
    {Expr value={0};value.kind=EX_OBJECT;value.symbol=index;value.type=index->type;strength_scale(scale,&value);}
    code("    phy\n    tay\n");
    cg.retained_second=index;cg.retained_second_scale=scale;cg.retained_y=3;
    cg.loop_start[cg.loop_count]=step;cg.loop_end[cg.loop_count++]=end;
    label(body);first=cg.length;emit_statements(s->body);last=cg.length;
    if(cg.retained_failed||!strstr(cg.assembly+first,"; retained nested begin\n")||!retained_scan(first,last,4,0)){
        cg_checkpoint_restore(saved, at);loop_previous=previous;loop_current=current;free(saved);return 0;
    }
    label(step);for(j=0;j<scale;++j)code("    iny\n");
    load_symbol(index);store_symbol(index);
    code("    cpy #$%04X\n    bcs :+\n",limit*scale);jump(body);code(":\n");label(end);--cg.loop_count;
    cg.retained_second=NULL;cg.retained_second_scale=0;cg.retained_y=0;
    code("    ply\n");label(done);divmod_state.available=0;
    loop_previous=previous;loop_current=current;free(saved);return 1;
}
/* A constant byte fill of a fixed near object can use word stores. The
 * loop counter is dead on exit and every byte is written exactly once. */
static int retained_byte_fill(Statement *s,Symbol *index,unsigned limit)
{
    Statement *body=body_single(s->body);
    Expr *assignment;
    IndexedOperand operand;
    uint32_t first,value;
    unsigned count,offset,loop,words,tail;
    int found=0;
    if(!body||body->next||body->kind!=ST_EXPR||!(assignment=body->expression)||
       assignment->kind!=EX_ASSIGN||assignment->op||width(assignment->left->type)!=1||
       assignment->left->type.is_bool||!integer_constant(assignment->right,&value)||
       !indexed_operand(assignment->left,&operand)||operand.scale!=1||
       operand.index->kind!=EX_OBJECT||operand.index->symbol!=index||
       !retained_initial_constant(s->initial,index,&first,&found)||!found||first>=limit||
       limit+operand.offset>width(operand.base->type))return 0;
    count=limit-first;
    if(count<2||count>32768)return 0;
    offset=operand.offset+first;
    operand.base->used=1;
    value=(value&255u)*257u;
    words=count/2;
    code("; constant indexed byte fill\n");
    if(words>=32&&!cg.parser->no_loop_unroll){
        enum { GROUP_WORDS=8,GROUP_BYTES=2*GROUP_WORDS };
        const char *store=value?"sta":"stz";
        tail=words%GROUP_WORDS;
        if(value&&tail)code("    lda #$%04X\n",(unsigned)value);
        for(unsigned i=0;i<tail;++i){
            code("    %s ",store);array_operand(operand.base,offset+i*2);code("\n");
        }
        loop=++cg.label;
        code("    ldx #$%04X\n",2*(words-tail)-GROUP_BYTES);
        label(loop);
        if(value)code("    lda #$%04X\n",(unsigned)value);
        for(unsigned i=0;i<GROUP_WORDS;++i){
            operand.offset=offset+2*(tail+i);
            code("    %s ",store);indexed_text(&operand);code("\n");
        }
        code("    txa\n    sec\n    sbc #$%04X\n    tax\n    bpl cg_%s_%u\n",
             GROUP_BYTES,cg.parser->unit,loop);
        if(count&1)code("    lda #$%04X\n",(unsigned)value);
    }else if(count<=8){
        code("    lda #$%04X\n",(unsigned)value);
        for(unsigned i=0;i+1<count;i+=2){
            code("    sta ");array_operand(operand.base,offset+i);code("\n");
        }
    }else{
        loop=++cg.label;
        code("    lda #$%04X\n    ldx #$%04X\n",(unsigned)value,(count&~1u)-2);
        label(loop);operand.offset=offset;
        code("    sta ");indexed_text(&operand);
        code("\n    dex\n    dex\n    bpl cg_%s_%u\n",cg.parser->unit,loop);
    }
    if(count&1){
        code("    sep #$20\n.a8\n    sta ");array_operand(operand.base,offset+count-1);
        code("\n    rep #$20\n.a16\n");
    }
    divmod_state.available=0;
    return 1;
}
static int retained_loop(Statement *s)
{
    Expr *condition=s->expression,*step=s->step;Symbol *index;RetainedPlan plan={0};unsigned i,scale=0,best=0;uint32_t n;
    if(cg.parser->no_loop_index_retention||cg.parser->no_indexed_operands||cg.parser->no_register_cursors||
       cg.parser->no_body_optimizations||cg.retained_index||cg.numeric_index||bound_state.cursor||cg.affine_active||lftr_state.active||
       cg.scalar_first||cg.scalar_leaf||cg.stack_leaf||cg.switch_depth||cg.loop_count==64||s->kind!=ST_FOR||
       !condition||condition->kind!=EX_BINARY||(condition->op!='<'&&condition->op!=TOK_LE)||
       condition->left->kind!=EX_OBJECT||!integer_constant(condition->right,&n))return 0;
    index=condition->left->symbol;
    if(!loop_private(index)||index->type.pointers||index->type.array||index->type.is_bool||reg_width(index->type)!=2||
       object_volatile(index->type)||!step||(step->kind!=EX_PRE&&step->kind!=EX_POST)||step->op!=TOK_INC||
       step->left->kind!=EX_OBJECT||step->left->symbol!=index||scalar_writes(s->body,index)||volatile_statement(s))return 0;
    /* The retained step replaces the C increment. A strength-reduced address
     * tied to that increment still needs the ordinary cursor updates. */
    for(i=0;i<cg.cursor_count;++i)if(cg.cursors[i].index==index)return 0;
    if(condition->op==TOK_LE)++n;
    if(!n||n>(width(index->type)==1?(index->type.is_unsigned?255u:127u):(index->type.is_unsigned?65535u:32767u)))return 0;
    /* Unsigned counters can enter from any value; signed entries must be
     * visibly nonnegative so the retained unsigned termination test agrees. */
    if(!index->type.is_unsigned){
        int found=0;
        unsigned limit=width(index->type)==1?127u:32767u;
        if(!retained_initial_nonneg(s->initial,index,limit,&found)||!found)return 0;
    }
    if(!cg.retained_second){
        RetainedPlan nested={0};unsigned loops=0;
        cg.retained_index=index;
        i=retained_nested_plan(s->body,&nested,&loops);cg.retained_index=NULL;
        if(i&&loops){
            for(i=0;i<nested.count;++i)if(nested.stride[i]<=8&&!(nested.stride[i]&(nested.stride[i]-1))&&
               nested.stride[i]<=65535/n&&nested.uses[i]>=3&&
               retained_nested_trial(s,index,n,nested.stride[i]))return 1;
        }
    }
    cg.retained_index=index;
    i=retained_statements(s->body,&plan);cg.retained_index=NULL;if(!i)return 0;
    for(i=0;i<plan.count;++i)if(plan.stride[i]>1&&plan.stride[i]<=65535/n&&plan.uses[i]>best){scale=plan.stride[i];best=plan.uses[i];}
    if(!scale)for(i=0;i<plan.count;++i)if(plan.stride[i]==1){scale=1;break;}
    if(!scale)return 0;
    if(cg.retained_second)return !scalar_writes(s->body,cg.retained_second)&&
        retained_trial(s,index,n,scale,3,cg.retained_second,cg.retained_second_scale);
    /* Prefer removing repeated outer-index rebuilds. A second scaled view of
     * the same induction value is the next choice. Every trial validates frame
     * ownership and register clobbers before accepting its emitted region. */
    for(i=0;i<plan.others;++i)if(plan.other_uses[i]>=3&&!scalar_writes(s->body,plan.other[i])&&
       retained_trial(s,index,n,scale,3,plan.other[i],plan.other_scale[i]))return 1;
    {int in,out;region_home_liveness(cg.function,s,index->offset,&in,&out);
        if(!out&&retained_byte_fill(s,index,n))return 1;
        if(!out&&retained_trial(s,index,n,scale,4,NULL,0))return 1;
    }
    int has_byte_stride=0;
    for(i=0;i<plan.count;++i)if(plan.stride[i]==1){has_byte_stride=1;break;}
    for(i=0;i<plan.count;++i)if(plan.stride[i]!=scale&&plan.stride[i]>1&&plan.stride[i]<=4&&
       !(plan.stride[i]&(plan.stride[i]-1))&&plan.stride[i]<=65535/n&&plan.uses[i]>=2&&
       !(has_byte_stride&&plan.stride[i]==2)&&
       retained_trial(s,index,n,scale,2,index,plan.stride[i]))return 1;
    if(retained_trial(s,index,n,scale,1,NULL,0))return 1;
    for(i=0;i<plan.count;++i)if(has_byte_stride&&plan.stride[i]==2&&plan.stride[i]!=scale&&
       plan.stride[i]<=65535/n&&plan.uses[i]>=2&&
       retained_trial(s,index,n,scale,2,index,2))return 1;
    if(retained_trial(s,index,n,scale,0,NULL,0))return 1;
    return retained_trial(s,index,n,scale,5,NULL,0);
}

static int body_asm_statements(Statement *s);
static unsigned retained_countdown_unroll(Statement *s,Symbol *index,Statement *previous,unsigned *chunks)
{
    Statement *body=body_single(s->body);
    Expr *initial=previous&&previous->next==s&&previous->kind==ST_EXPR?previous->expression:NULL;
    Expr *update=body?body->expression:NULL;
    uint32_t trips;
    if(cg.parser->no_loop_unroll||!body||body->kind!=ST_EXPR||body->next||
       !update||!update->left||update->left->kind!=EX_OBJECT||!known_integer(update->left->type)||
       !body_step_direction(update,update->left->symbol)||
       statement_inline_markers(s->body)||!initial||initial->kind!=EX_ASSIGN||initial->op||
       initial->left->kind!=EX_OBJECT||initial->left->symbol!=index||
       !integer_constant(initial->right,&trips))return 0;
    trips=initializer_cast(trips,index->type);
    if(!trips)trips=index->type.base==TY_CHAR?256u:65536u;
    if(trips<16||trips%4)return 0;
    /* Sixteen near word updates still fit a short back edge. Amortize
     * their code cost only over a long, statically known trip count. */
    unsigned factor=trips>=256&&!(trips%16)&&width(update->left->type)==2&&
        !update->left->symbol->owner&&!update->left->type.banked?16u:4u;
    *chunks=trips/factor;
    return factor;
}
static int retained_countdown_for_loop(Statement *s,int before_initial)
{
    Symbol *index=NULL;
    Expr *condition=s->expression,*step=s->step,*init_expr=NULL,*start_expr=NULL,*bound=NULL;
    CodegenCheckpoint *saved;
    Statement *previous=loop_previous,*current=loop_current,*init;
    unsigned body,step_label,end;
    size_t at,body_start;
    int descending=0,signed_gt_zero=0,observed=0;
    Type t={0};
    uint32_t k,start_u,bound_u;
    int32_t trips=0;
    if(cg.parser->no_loop_index_retention||cg.parser->no_register_cursors||
       cg.parser->no_strength_reduction||cg.parser->no_body_optimizations||
       cg.retained_index||cg.retained_second||cg.numeric_index||bound_state.cursor||
       bound_state.pending||cg.affine_active||lftr_state.active||cg.scan_cursor||
       cg.scalar_first||cg.scalar_leaf||cg.stack_leaf||cg.switch_depth||cg.loop_count==64||
       s->kind!=ST_FOR||cg.function->symbol->interrupt||cg.function->jump_label_count||
       volatile_statement(s)||body_asm_statements(s->body))return 0;
    if(before_initial){
        init=body_single(s->initial);
        init_expr=init&&!init->next&&init->kind==ST_EXPR?init->expression:NULL;
        if(!init_expr||init_expr->kind!=EX_ASSIGN||init_expr->op||
           init_expr->left->kind!=EX_OBJECT||volatile_expression(init_expr))return 0;
    }
    if((index=for_countdown_index(s,&signed_gt_zero))!=NULL){
        descending=1;
        if(before_initial&&init_expr->left->symbol!=index)return 0;
        observed=loop_observed_outside(cg.function->body,s,index);
        if(observed&&before_initial)return 0;
    }else{
        Expr *left;uint32_t delta;
        if(!condition||condition->kind!=EX_BINARY||(condition->op!='<'&&condition->op!=TOK_LE)||!step)return 0;
        left=condition->left;bound=condition->right;
        while(left->kind==EX_CAST&&word_integer(left->type)&&
              (left->left->type.base==TY_CHAR||left->left->type.base==TY_INT)&&!left->left->type.pointers)
            left=left->left;
        if(left->kind!=EX_OBJECT)return 0;
        index=left->symbol;
        if(!(((step->kind==EX_PRE||step->kind==EX_POST)&&step->op==TOK_INC)||
             (step->kind==EX_ASSIGN&&step->op=='+'&&integer_constant(step->right,&delta)&&delta==1))||
           step->left->kind!=EX_OBJECT||step->left->symbol!=index)return 0;
        if((index->type.base!=TY_INT&&index->type.base!=TY_CHAR)||index->type.is_bool||
           index->type.pointers||object_volatile(index->type)||!loop_private(index)||
           statement_references(s->body,index)||dp_counter_modified(s->body,index))return 0;
        if(loop_observed_outside(cg.function->body,s,index))return 0;
        t=common_type(condition->left->type,condition->right->type);
        if(t.pointers||reg_width(t)!=2)return 0;
        if(!dp_counter_invariant_bound(s,bound)||loop_mentions(bound,index))return 0;
        if(before_initial){
            if(init_expr->left->symbol!=index)return 0;
            start_expr=init_expr->right;
        }
    }
    if(descending){
        if(before_initial&&integer_constant(init_expr->right,&k)){
            k=initializer_cast(k,index->type);
            if(!k||(!index->type.is_unsigned&&(int32_t)(int16_t)k<=0))return 0;
            trips=(int32_t)(k&65535);
        }
    }else{
        if(before_initial&&integer_constant(start_expr,&start_u)&&integer_constant(bound,&bound_u)){
            int32_t s_val,b_val,end_val;
            start_u=initializer_cast(start_u,index->type);
            bound_u=initializer_cast(bound_u,bound->type);
            s_val=t.is_unsigned?(int32_t)(start_u&65535):(int32_t)(int16_t)start_u;
            b_val=t.is_unsigned?(int32_t)(bound_u&65535):(int32_t)(int16_t)bound_u;
            end_val=b_val+(condition->op==TOK_LE);
            if(s_val>=end_val)return 0;
            trips=end_val-s_val;
            if(trips<=0||trips>65535)return 0;
            if(index->type.base==TY_CHAR&&
               (s_val<0||end_val>(index->type.is_unsigned?255:127)))return 0;
            if(!t.is_unsigned&&end_val>32767)return 0;
        }else{
            if(condition->op!='<')return 0;
            if(index->type.base==TY_CHAR&&
               !(bound->known.valid&&bound->known.min>=0&&bound->known.max<=(index->type.is_unsigned?255:127)))
                return 0;
            if(!(before_initial&&integer_constant(start_expr,&start_u)&&!initializer_cast(start_u,index->type))){
                if(!direct_operand(condition->left,t,0,0))return 0;
                if(!t.is_unsigned&&!(condition->left->known.valid&&condition->left->known.min>=0&&
                                      bound->known.valid&&bound->known.min>=0))return 0;
            }
        }
    }
    saved=allocate(sizeof *saved);cg_checkpoint_save(saved);at=cg.length;
    body=++cg.label;step_label=++cg.label;end=++cg.label;
    if(trips>0){
        code("; register countdown\n    ldx #$%04X\n",(unsigned)trips);
    }else if(descending){
        if(before_initial){emit_value(init_expr->right);convert_registers(init_expr->right->type,index->type);}
        else load_symbol(index);
        code("    bne :+\n");jump(end);code(":\n");
        if(signed_gt_zero){code("    bpl :+\n");jump(end);code(":\n");}
        code("    tax\n");
    }else if(before_initial&&integer_constant(start_expr,&start_u)&&!initializer_cast(start_u,index->type)){
        emit_value(bound);convert_registers(bound->type,t);
        code("    bne :+\n");jump(end);code(":\n");
        if(!t.is_unsigned){code("    bpl :+\n");jump(end);code(":\n");}
        code("    tax\n");
    }else{
        if(before_initial){emit_value(start_expr);convert_registers(start_expr->type,index->type);store_symbol(index);}
        emit_value(bound);convert_registers(bound->type,t);
        code("    sec\n    sbc ");
        if(!direct_operand(condition->left,t,0,1)){
            cg_checkpoint_restore(saved, at);
            loop_previous=previous;loop_current=current;free(saved);return 0;
        }
        code("\n    bcc :+\n    bne :++\n:\n");jump(end);code(":\n");
        if(!t.is_unsigned){code("    bpl :+\n");jump(end);code(":\n");}
        code("    tax\n");
    }
    cg.loop_start[cg.loop_count]=step_label;cg.loop_end[cg.loop_count++]=end;
    divmod_state.available=0;label(body);body_start=cg.length;
    emit_statements(s->body);
    if(!retained_scan(body_start,cg.length,0,1)){
        cg_checkpoint_restore(saved, at);
        loop_previous=previous;loop_current=current;free(saved);return 0;
    }
    label(step_label);code("    dex\n");flag_branch("bne","beq",body,0,0);
    label(end);--cg.loop_count;
    if(observed){
        code("    txa\n");
        if(index->type.base==TY_CHAR)narrow_char(index->type);
        store_symbol(index);
    }
    divmod_state.available=0;loop_previous=previous;loop_current=current;free(saved);
    return 1;
}
/* Reuse normal body emission so volatile accesses keep their original width
 * and order. Only the private loop-control value moves into X. */
static int retained_countdown_loop(Statement *s)
{
    Symbol *index;
    CodegenCheckpoint *saved;
    Statement *previous=loop_previous,*current=loop_current;
    unsigned body,step,end,chunks=0,factor;
    size_t body_start;
    if(s->kind==ST_FOR)return retained_countdown_for_loop(s,0);
    if(cg.parser->no_loop_index_retention||cg.parser->no_register_cursors||
       cg.parser->no_strength_reduction||cg.parser->no_body_optimizations||
       cg.retained_index||cg.retained_second||cg.numeric_index||bound_state.cursor||
       bound_state.pending||cg.affine_active||lftr_state.active||cg.scan_cursor||
       cg.scalar_first||cg.scalar_leaf||cg.stack_leaf||cg.switch_depth||cg.loop_count==64||
       !(index=post_test_countdown(s))||body_asm_statements(s->body))return 0;
    saved=allocate(sizeof *saved);cg_checkpoint_save(saved);
    body=++cg.label;step=++cg.label;end=++cg.label;
    factor=retained_countdown_unroll(s,index,previous,&chunks);
    if(factor)code("; unrolled register countdown: %u trips\n    ldx #$%04X\n",factor,chunks);
    else{
        load_symbol(index);
        /* A zero byte takes 256 trips. X has room for that distance */
        if(index->type.base==TY_CHAR)code("    bne :+\n    lda #$0100\n:\n");
        code("    tax\n");
    }
    cg.loop_start[cg.loop_count]=step;cg.loop_end[cg.loop_count++]=end;
    divmod_state.available=0;label(body);body_start=cg.length;
    for(unsigned i=0;i<(factor?factor:1u);++i)emit_statements(s->body);
    if(!retained_scan(body_start,cg.length,0,1)){
        cg_checkpoint_restore_length(saved);
        loop_previous=previous;loop_current=current;free(saved);return 0;
    }
    label(step);code("    dex\n");flag_branch("bne","beq",body,0,0);
    label(end);--cg.loop_count;
    if(loop_observed_outside(cg.function->body,s,index)){
        code("    txa\n");
        if(index->type.base==TY_CHAR)narrow_char(index->type);
        store_symbol(index);
    }
    divmod_state.available=0;loop_previous=previous;loop_current=current;free(saved);
    return 1;
}
