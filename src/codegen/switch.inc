typedef struct { unsigned key,label; } WordSwitchCase;
/* The range is already checked, so a singleton has exactly one target */
static void dense_word_switch_tree(const WordSwitchCase *cases,unsigned count)
{
    if(count==1){jump(cases[0].label);return;}
    unsigned mid=count/2,upper=++cg.label;
    code("    cmp #$%04X\n    bcc :+\n",cases[mid].key);
    jump(upper);code(":\n");
    dense_word_switch_tree(cases,mid);label(upper);
    dense_word_switch_tree(cases+mid,count-mid);
}
/* Sharing an emitted arm also shares the value-analysis decisions made
 * for that occurrence. Require the same facts for every subexpression. */
static int switch_same_facts(const Expr *a,const Expr *b)
{
    if(!a)return 1;
    if(memcmp(&a->known,&b->known,sizeof a->known)||memcmp(&a->range,&b->range,sizeof a->range)||
       a->known_no_conversion!=b->known_no_conversion||a->known_nonnull!=b->known_nonnull)return 0;
    for(unsigned i=0;i<a->arg_count;++i)if(!switch_same_facts(a->args[i],b->args[i]))return 0;
    return switch_same_facts(a->left,b->left)&&switch_same_facts(a->right,b->right)&&
        switch_same_facts(a->third,b->third);
}
/* Cases may appear in any source order. Direct edges preserve X and keep
 * ordinary control-flow and scratch analysis valid. */
static int split_word_switch(Statement *s,unsigned fallback,int retain_word)
{
    Statement *item;
    Expr *control=s->expression;
    WordSwitchCase cases[64];
    unsigned count=0,i,j,mid,upper;
    Expr *action=NULL;
    int same_action=1;
    int flags,negated=!retain_word&&control->kind==EX_UNARY&&control->op=='-'&&
        reg_width(control->left->type)==2;
    if(cg.parser->no_strength_reduction||reg_width(control->type)!=2)return 0;
    for(item=s->cases;item;item=item->case_next)if(!item->is_default){
        if(count==64)return 0;
        Statement *body=item->body;
        if(!body||body->kind!=ST_EXPR||body->next||!item->next||item->next->kind!=ST_BREAK||
           !body->expression||(action&&(!body_equal(action,body->expression)||
            !switch_same_facts(action,body->expression))))same_action=0;
        else action=body->expression;
        cases[count].key=(negated?0u-item->case_value:item->case_value)&65535;
        cases[count++].label=item->case_label;
    }
    if(count<3||(!same_action&&count<6))return 0;
    for(i=1;i<count;++i){
        WordSwitchCase entry=cases[i];
        j=i;
        while(j&&cases[j-1].key>entry.key){cases[j]=cases[j-1];--j;}
        cases[j]=entry;
    }
    for(i=1;i<count;++i)if(cases[i-1].key+1!=cases[i].key)return 0;
    /* Negation permutes the word keys, so the dispatch can read its input */
    emit_value(negated?control->left:control);divmod_state.available=0;
    flags=accumulator_zero_flags();
    if(retain_word)code("    tax\n");
    if(same_action){
        unsigned lo=cases[0].key;
        if(lo)code("    sec\n    sbc #$%04X\n",lo);
        code("    cmp #$%04X\n    bcc :+\n",count);
        jump(fallback);code(":\n");jump(cases[0].label);
        return 1;
    }
    if(count>16){
        unsigned lo=cases[0].key,hi=cases[count-1].key;
        code("; bounded dense word switch\n");
        if(lo){code("    cmp #$%04X\n    bcs :+\n",lo);jump(fallback);code(":\n");}
        if(hi<65535){code("    cmp #$%04X\n    bcc :+\n",hi+1);jump(fallback);code(":\n");}
        dense_word_switch_tree(cases,count);
        return 1;
    }
    mid=(count+1)/2;upper=++cg.label;
    code("; split dense word switch\n");
    if(!flags||cases[0].key)code("    cmp #$%04X\n",cases[0].key);
    code("    bne :+\n");jump(cases[0].label);code(":\n");
    code("    cmp #$%04X\n    bcs cg_%s_%u\n",cases[mid].key,cg.parser->unit,upper);
    for(i=1;i<mid;++i){
        code("    cmp #$%04X\n    bne :+\n",cases[i].key);
        jump(cases[i].label);code(":\n");
    }
    jump(fallback);label(upper);
    code("    bne :+\n");jump(cases[mid].label);code(":\n");
    for(i=mid+1;i<count;++i){
        code("    cmp #$%04X\n    bne :+\n",cases[i].key);
        jump(cases[i].label);code(":\n");
    }
    jump(fallback);
    return 1;
}

static int const_lut_word_switch(Statement *s,unsigned end)
{
    typedef struct { uint16_t key; uint16_t val; } LutEntry;
    LutEntry entries[64];
    Statement *cur,*item;
    Symbol *target=NULL;
    unsigned total_cases=0,seen_cases=0,count=0,i,j,span,id,done_lbl;
    int is_return=-1,has_default=0,default_sets=0,update=-1;
    uint16_t default_val=0,min_key=0,max_key=0,table[64];
    unsigned char present[64];
    if(cg.parser->no_strength_reduction||cg.parser->no_body_optimizations||
       cg.function->jump_label_count||reg_width(s->expression->type)!=2||
       s->expression->type.pointers||volatile_expression(s->expression)||
       !s->body||s->body->kind!=ST_BLOCK||s->body->inline_callee)return 0;
    for(item=s->cases;item;item=item->case_next)++total_cases;
    if(total_cases<4)return 0;
    cur=s->body->body;
    while(cur){
        Statement *group[64];
        unsigned gcount=0;
        Statement *leaf=cur,*after=cur->next;
        Statement *stmt=NULL;
        if(cur->kind!=ST_CASE)return 0;
        while(leaf&&leaf->kind==ST_CASE){
            if(gcount==64)return 0;
            group[gcount++]=leaf;
            leaf=leaf->body;
        }
        seen_cases+=gcount;
        while(leaf&&leaf->kind==ST_BLOCK&&!leaf->inline_callee){
            if(!leaf->body||leaf->next)return 0;
            /* Allow `{ v = K; break; }` or `{ return K; }` inside braced case */
            stmt=leaf->body;
            break;
        }
        if(!stmt)stmt=leaf;
        if(!stmt)return 0;
        if(stmt->kind==ST_RETURN){
            uint32_t rv;
            Type rt=cg.function->symbol->type;
            Statement *tail=stmt->next;
            if(is_return==0||reg_width(rt)!=2||rt.pointers||!stmt->expression||
               !integer_constant(stmt->expression,&rv))return 0;
            if(tail){
                if(tail->kind!=ST_BREAK||tail->next)return 0;
            }else if(leaf==stmt&&after&&after->kind==ST_BREAK)after=after->next;
            is_return=1;
            {
                uint16_t kv=(uint16_t)initializer_cast(rv,rt);
                for(i=0;i<gcount;++i){
                    if(group[i]->is_default){has_default=1;default_sets=1;default_val=kv;}
                    else{
                        if(count==64)return 0;
                        entries[count].key=(uint16_t)(group[i]->case_value&65535);
                        entries[count++].val=kv;
                    }
                }
            }
        }else if(stmt->kind==ST_EXPR&&stmt->expression&&stmt->expression->kind==EX_ASSIGN&&
                 stmt->expression->left->kind==EX_OBJECT){
            Expr *ae=stmt->expression;Symbol *lhs=ae->left->symbol;uint32_t rv;
            Statement *tail=stmt->next;
            if(is_return==1||lhs->type.array||lhs->type.pointers||lhs->type.is_bool||
               lhs->type.banked||lhs->type.constant||object_volatile(lhs->type)||
               width(lhs->type)>2||(target&&target!=lhs)||!integer_constant(ae->right,&rv))return 0;
            if((update>=0&&update!=ae->op)||(ae->op&&ae->op!='^'&&ae->op!='&'&&ae->op!='|'))return 0;
            if(ae->op&&(width(lhs->type)!=2||!known_integer(lhs->type)))return 0;
            target=lhs;is_return=0;update=ae->op;
            if(tail){
                if(tail->kind!=ST_BREAK||tail->next)return 0;
            }else if(after&&after->kind==ST_BREAK)after=after->next;
            else if(after)return 0;
            {
                uint16_t kv=(uint16_t)initializer_cast(rv,lhs->type);
                if(width(lhs->type)==1&&!lhs->type.is_unsigned&&(kv&0x80u))kv|=0xFF00u;
                for(i=0;i<gcount;++i){
                    if(group[i]->is_default){has_default=1;default_sets=1;default_val=kv;}
                    else{
                        if(count==64)return 0;
                        entries[count].key=(uint16_t)(group[i]->case_value&65535);
                        entries[count++].val=kv;
                    }
                }
            }
        }else if(stmt->kind==ST_BREAK&&gcount==1&&group[0]->is_default&&!stmt->next){
            if(is_return==1)return 0;
            has_default=1;default_sets=0;
            if(leaf==stmt&&after&&after->kind==ST_BREAK)after=after->next;
        }else return 0;
        cur=after;
    }
    if(seen_cases!=total_cases||is_return<0)return 0;
    if(update>0||(update==0&&count==3&&target&&width(target->type)==2&&!default_sets)){
        Expr home={.kind=EX_OBJECT,.symbol=target,.type=target->type};
        if(count<3||count>6||default_sets||!direct_operand(&home,home.type,0,0))return 0;
        emit_value(s->expression);divmod_state.available=0;
        unsigned apply=++cg.label,arms[6];
        for(i=0;i<count;++i)arms[i]=++cg.label;
        if(count==3&&entries[0].key+1==entries[1].key&&entries[1].key+2<entries[2].key){
            unsigned adjacent=++cg.label;
            /* Test the isolated key on fallthrough. Most word values are
             * above the adjacent low pair and take only the default branch. */
            if(entries[1].key<32768){
                code("    cmp #$%04X\n    bcc cg_%s_%u\n    cmp #$%04X\n",
                     entries[1].key+1,cg.parser->unit,adjacent,entries[2].key);
                code("    bne cg_%s_%u\n",cg.parser->unit,end);
                jump(arms[2]);label(adjacent);
                code("    cmp #$%04X\n    bcc cg_%s_%u\n    beq cg_%s_%u\n",
                     entries[0].key,cg.parser->unit,end,cg.parser->unit,arms[0]);
                jump(arms[1]);
            }else{
                code("    cmp #$%04X\n    bcs cg_%s_%u\n    cmp #$%04X\n",
                     entries[1].key+1,cg.parser->unit,adjacent,entries[0].key);
                code("    bcc cg_%s_%u\n    beq cg_%s_%u\n",cg.parser->unit,end,cg.parser->unit,arms[0]);
                jump(arms[1]);label(adjacent);
                code("    cmp #$%04X\n    bne cg_%s_%u\n",entries[2].key,cg.parser->unit,end);
            }
        }else for(i=0;i<count;++i){
            code("    cmp #$%04X\n",entries[i].key);
            if(i+1==count)code("    bne cg_%s_%u\n",cg.parser->unit,end);
            else code("    beq cg_%s_%u\n",cg.parser->unit,arms[i]);
        }
        for(i=count;i--;){
            label(arms[i]);code("    lda #$%04X\n",entries[i].val);
            if(i)jump(apply);
        }
        label(apply);
        if(update){
            code("    %s ",update=='^'?"eor":update=='|'?"ora":"and");
            direct_operand(&home,home.type,0,1);code("\n");
        }
        store_symbol(target);
        label(end);divmod_state.available=0;return 1;
    }
    if(count<4)return 0;
    for(i=1;i<count;++i){
        LutEntry tmp=entries[i];j=i;
        while(j&&entries[j-1].key>tmp.key){entries[j]=entries[j-1];--j;}
        entries[j]=tmp;
    }
    min_key=entries[0].key;max_key=entries[count-1].key;
    if((unsigned)(max_key-min_key)>=64u)return 0;
    span=(unsigned)(max_key-min_key)+1;
    if(span<4)return 0;
    if(span!=count&&!(has_default&&default_sets&&count*2>=span))return 0;
    memset(present,0,span);
    for(i=0;i<span;++i)table[i]=default_val;
    for(i=0;i<count;++i){
        unsigned idx=entries[i].key-min_key;
        if(idx>=span||present[idx])return 0;
        present[idx]=1;table[idx]=entries[i].val;
    }
    if(span!=count)for(i=0;i<span;++i)if(!present[i]&&!(has_default&&default_sets))return 0;
    code("; constant dense switch lookup table (%u entries)\n",span);
    emit_value(s->expression);divmod_state.available=0;
    if(min_key)code("    sec\n    sbc #$%04X\n",min_key);
    id=++cg.label;
    if(has_default&&default_sets){
        done_lbl=++cg.label;
        code("    cmp #$%04X\n    bcc :+\n    lda #$%04X\n    bra cg_%s_%u\n:\n",
             span,default_val,cg.parser->unit,done_lbl);
        code("    asl a\n    tax\n    lda f:switch_lut_%s_%u,x\n",cg.parser->unit,id);
        label(done_lbl);
    }else{
        code("    cmp #$%04X\n    bcc :+\n",span);
        jump(end);
        code(":\n    asl a\n    tax\n    lda f:switch_lut_%s_%u,x\n",cg.parser->unit,id);
    }
    code(".segment \"RODATA\"\nswitch_lut_%s_%u:\n    .word ",cg.parser->unit,id);
    for(i=0;i<span;++i)code("%s$%04X",i?",":"",table[i]);
    code("\n.segment \"%s\"\n",code_segment());
    if(is_return){
        if(cg.scalar_leaf){
            unsigned spill;
            for(spill=0;spill<(unsigned)cg.scalar_spill;++spill)code("    plx\n");
            code("    rts\n");
        }else code("    jmp .loword(return_%s)\n",cg.function->symbol->asm_name);
        if(!has_default)label(end);
    }else{
        store_symbol(target);
        label(end);
    }
    divmod_state.available=0;
    return 1;
}

static int emit_word_row_switch(Statement *s,unsigned end);

static unsigned assign_switch_labels(Statement *s,unsigned fallback)
{
    Statement *item;
    for(item=s->cases;item;item=item->case_next){
        item->case_label=++cg.label;
        if(item->is_default)fallback=item->case_label;
    }
    return fallback;
}

static Statement *switch_constant_case(Statement *s)
{
    Expr *control=s->expression;
    uint64_t value=initializer_cast64(((uint64_t)control->value_high<<32)|control->value,control->type);
    unsigned low=(uint32_t)value,high=reg_width(control->type)==8?(uint32_t)(value>>32):0;
    Statement *item,*fallback=NULL;
    for(item=s->cases;item;item=item->case_next){
        if(item->is_default)fallback=item;
        else if(item->case_value==low&&item->case_value_high==high)return item;
    }
    return fallback;
}

/* Read the promoted controlling value once. Word comparisons preserve X */
static void emit_switch_dispatch(Statement *s,unsigned fallback,int retain_word)
{
    Statement *item;unsigned next;int flags;
    if(!retain_word&&!cg.parser->no_strength_reduction&&s->expression->kind==EX_INT){
        item=switch_constant_case(s);
        jump(item?item->case_label:fallback);divmod_state.available=0;
        return;
    }
    if(wide_scalar(value_type(s->expression->type))){
        unsigned part;
        emit_wide_operand(s->expression);divmod_state.available=0;
        code("; linear switch dispatch: 64-bit controlling value\n");
        for(item=s->cases;item;item=item->case_next)if(!item->is_default){
            uint64_t value=((uint64_t)item->case_value_high<<32)|item->case_value;
            next=++cg.label;
            for(part=0;part<8;part+=2)
                code("    lda z:__arith_lhs+%u\n    cmp #$%04X\n    bne cg_%s_%u\n",
                     part,(unsigned)((value>>(part*8))&65535u),cg.parser->unit,next);
            jump(item->case_label);label(next);
        }
        jump(fallback);return;
    }
    if(split_word_switch(s,fallback,retain_word))return;
    emit_value(s->expression);divmod_state.available=0;
    /* The first case may reuse the controlling value's Z flag for zero */
    flags=accumulator_zero_flags();
    if(retain_word)code("    tax\n");
    code("; linear switch dispatch: %u-bit controlling value\n",reg_width(s->expression->type)*8);
    for(item=s->cases;item;item=item->case_next)if(!item->is_default){
        if(!(flags&&!(item->case_value&65535)))code("    cmp #$%04X\n",item->case_value&65535);
        flags=0;
        if(reg_width(s->expression->type)==2){
            code("    bne :+\n");jump(item->case_label);code(":\n");
        }else{
            next=++cg.label;
            code("    bne cg_%s_%u\n",cg.parser->unit,next);
            code("    cpx #$%04X\n    bne cg_%s_%u\n",item->case_value>>16,cg.parser->unit,next);
            jump(item->case_label);label(next);
        }
    }
    jump(fallback);
}

/* Bodies retain source order and independent labels for fallthrough */
static void emit_switch(Statement *s)
{
    unsigned end=++cg.label;
    if(cg.loop_count==64)error_at(s->location,"too many nested loops or switches");
    if(emit_word_row_switch(s,end))return;
    if(const_lut_word_switch(s,end))return;
    emit_switch_dispatch(s,assign_switch_labels(s,end),0);
    /* A zero continue target marks a switch. Continue searches outward for a
     * real loop, while break uses the nearest entry of either kind. */
    cg.loop_start[cg.loop_count]=0;cg.loop_end[cg.loop_count++]=end;
    ++cg.switch_depth;emit_statements(s->body);--cg.switch_depth;--cg.loop_count;
    divmod_state.available=0;label(end);
}
