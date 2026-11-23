/* Fixed banks use native MVN; runtime banks use long-indirect transfers */
typedef struct { unsigned mode,cycles,bytes; } CopyPlan;
/* Shared copy policy: one code byte costs eight nominal CPU cycles, with a
 * 128-byte expansion limit. Callers supply costs for their addressing modes. */
static void copy_consider(CopyPlan *plan,unsigned mode,unsigned cycles,unsigned bytes)
{
    if(plan->bytes>128||cycles+8*bytes<plan->cycles+8*plan->bytes){
        plan->mode=mode;plan->cycles=cycles;plan->bytes=bytes;
    }
}
static Expr *memset_destination(Expr *e)
{
    Symbol *fn;
    if(e->kind!=EX_CALL||e->left||e->string||cg.parser->no_copy_selection)return NULL;
    fn=e->symbol;
    if(strcmp(fn->asm_name,"memset")||fn->defined||fn->internal||fn->old_style||
       fn->variadic||fn->param_count!=3||e->arg_count!=3||
       fn->type.base!=TY_VOID||fn->type.pointers!=1||far_pointer(fn->type)||
       !same_type(value_type(fn->type),value_type(fn->params[0]))||
       !word_integer(fn->params[1])||!word_integer(fn->params[2]))return NULL;
    return e->args[0];
}
static int short_memset(Expr *e,int needed)
{
    Expr *destination=memset_destination(e);
    uint32_t count,fill=0;
    unsigned i;
    int literal;
    if(!destination||cg.function->symbol->interrupt||volatile_expression(e)||
       !integer_constant(e->args[2],&count)||!count||count>8)return 0;
    literal=integer_constant(e->args[1],&fill);
    code("; inline short memset: %u bytes\n",(unsigned)count);
    if(!literal){emit_value(e->args[1]);push_value(type(TY_INT,0));}
    emit_value_x(destination);
    if(!literal)pop_value(type(TY_INT,0));
    fill&=255;
    i=0;
    if(literal&&count>1){
        code("    lda #$%04X\n",fill*257u);
        for(;i+1<count;i+=2)code("    sta a:$%04X,x\n",i);
    }
    if(i<count){
        code("    sep #$20\n.a8\n");
        if(literal&&count==1)code("    lda #$%02X\n",fill);
        for(;i<count;++i)code("    sta a:$%04X,x\n",i);
        code("    rep #$20\n.a16\n");
    }
    if(needed)code("    txa\n");
    divmod_state.available=0;
    return 1;
}
/* A short literal format without conversions is a string copy and a count */
static int literal_sprintf(Expr *e,int needed)
{
    Symbol *fn=e->symbol;
    String *format;
    Type dst,src;
    unsigned n=0,i;
    if(cg.parser->no_copy_selection||strcmp(fn->asm_name,"sprintf")||fn->defined||fn->internal||
       fn->old_style||!fn->variadic||fn->param_count!=2||e->arg_count!=2||
       !word_integer(fn->type)||fn->type.is_unsigned||volatile_expression(e))return 0;
    dst=value_type(fn->params[0]);src=value_type(fn->params[1]);
    if(dst.base!=TY_CHAR||dst.pointers!=1||far_pointer(dst)||
       src.base!=TY_CHAR||src.pointers!=1||!far_pointer(src)||
       object_volatile(pointed_type(dst))||object_volatile(pointed_type(src)))return 0;
    format=scalar_string_literal(e->args[1]);
    if(!format)return 0;
    while(n<format->size&&n<16&&format->bytes[n]&&format->bytes[n]!='%')++n;
    if(n==format->size||n==16||format->bytes[n])return 0;
    emit_value_x(e->args[0]);
    for(i=0;i<n;i+=2)
        code("    lda #$%04X\n    sta a:$%04X,x\n",format->bytes[i]|((unsigned)format->bytes[i+1]<<8),i);
    if(i==n){
        code("    sep #$20\n.a8\n    stz a:$%04X,x\n    rep #$20\n.a16\n",n);
    }
    if(needed)code("    lda #$%04X\n",n);
    divmod_state.available=0;
    return 1;
}
static int literal_strcpy(Expr *e)
{
    Symbol *fn=e->symbol;Expr *source,*destination;String *string;
    unsigned n=0,i,fallback,end;int save_bank=cg.parser->no_body_optimizations;Type result=value_type(fn->type),dst,src;
    CopyPlan plan;
    if(cg.parser->no_copy_selection||strcmp(fn->name,"strcpy")||fn->defined||fn->internal||
       fn->variadic||fn->param_count!=2||e->arg_count!=2||volatile_expression(e))return 0;
    dst=value_type(fn->params[0]);src=value_type(fn->params[1]);
    if(result.base!=TY_CHAR||result.pointers!=1||far_pointer(result)||
       dst.base!=TY_CHAR||dst.pointers!=1||far_pointer(dst)||
       src.base!=TY_CHAR||src.pointers!=1||!far_pointer(src)||
       object_volatile(pointed_type(dst))||object_volatile(pointed_type(src)))return 0;
    source=e->args[1];destination=e->args[0];
    while(source->kind==EX_CAST&&value_type(source->type).pointers&&
          far_pointer(value_type(source->type))&&far_pointer(value_type(source->left->type)))source=source->left;
    if(source->kind!=EX_STRING)return 0;
    string=source->string;
    while(n<string->size&&string->bytes[n])++n;
    if (n == string->size) {
        return 0;
    }
    ++n; /* Include only the first terminating NUL */
    plan.mode=0;plan.cycles=12*n+6;plan.bytes=8*n+4;
    copy_consider(&plan,2,7*n+(save_bank?32:25),save_bank?36:34);
    string->used=1;
    code("; literal strcpy: %s %u bytes, estimated %u cycles / %u code bytes\n",
         plan.mode?"mvn":"inline",n,plan.cycles,plan.bytes);
    /* Destination evaluation can call or recurse. Its original value belongs
     * to this invocation, never to shared scratch, throughout the transfer. */
    emit_value(destination);push_value(type(TY_INT,0));
    if(!plan.mode){
        code("    tax\n    sep #$20\n.a8\n");
        for(i=0;i<n;++i){
            code("    lda f:str_%s_%u+$%04X\n    sta a:$0000,x\n",cg.parser->unit,string->id,i);
            if(i+1<n)code("    inx\n");
        }
        code("    rep #$20\n.a16\n");
    }else{
        fallback=++cg.label;end=++cg.label;
        code("    ldx #.loword(str_%s_%u)\n    cpx #$%04X\n    bcs cg_%s_%u\n",
             cg.parser->unit,string->id,65537-n,cg.parser->unit,fallback);
        /* Generated C enters with DBR=$7E; MVN's destination bank restores
         * that same value. As with near aggregate copies, no bank save is
         * necessary. Interrupt entry/exit retains its own DBR contract. */
        code("    phy\n    tay\n");if(save_bank)code("    phb\n");
        code("    lda #$%04X\n    mvn #.bankbyte(str_%s_%u), #$7E\n",n-1,cg.parser->unit,string->id);
        if (save_bank) {
            code("    plb\n");
        }
        code("    ply\n");
        jump(end);label(fallback);
        /* MVN cannot carry its source bank. The public far-source routine
         * handles a literal straddling a bank, with no second destination
         * evaluation. Its destination is below the two source argument words. */
        code("    lda #.bankbyte(str_%s_%u)\n    pha\n    txa\n    pha\n    lda 5,s\n    tax\n",cg.parser->unit,string->id);
        {char name[132];snprintf(name,sizeof name,"_%s",fn->asm_name);call_entry(name);}
        code("    plx\n    plx\n");
        fn->used=1;label(end);
    }
    pop_value(type(TY_INT,0));divmod_state.available=0;return 1;
}
/* A short fixed copy can visit the same bytes without a scratch pointer or
 * a loop counter. Keep address evaluation ahead of the transfer. */
static int volatile_fixed_copy(Expr *e,int needed)
{
    Expr *from=e->right,*to=e->left,*call=NULL;
    unsigned source_offset=0,destination_offset=0,n=width(e->type);
    Symbol *source,*destination;
    if(cg.parser->no_copy_selection||n>12)return 0;
    destination=direct_memory_object(to,&destination_offset);
    if(destination&&from->kind==EX_CALL&&from->third&&from->third->kind==EX_OBJECT){
        call=from;from=from->third;
    }
    source=direct_memory_object(from,&source_offset);
    if((!source&&!destination)||(!source&&from->type.banked)||(!destination&&to->type.banked))return 0;
    if(call)emit_call(call,0);
    if(!destination)emit_address_x(to);
    if(!source)emit_address_x(from);
    code("; volatile aggregate: %u byte accesses, fixed operands\n    sep #$20\n.a8\n",n);
    for(unsigned i=0;i<n;++i){
        code("    lda ");
        if(source)array_operand(source,source_offset+i);else code("a:$%04X,x",i);
        code("\n    sta ");
        if(destination)array_operand(destination,destination_offset+i);else code("a:$%04X,x",i);
        code("\n");
    }
    code("    rep #$20\n.a16\n");
    if(needed){if(destination)emit_address(to);else code("    txa\n");}
    divmod_state.available=0;
    return 1;
}
/* Advance both long bases between Y windows. A complete window terminates
 * when Y wraps, including word transfers whose final offset is $FFFE. */
static void wide_aggregate_transfer(unsigned n,int copying,int byte,int restore_destination)
{
    code("    phy\n");
    if(byte)code("    sep #$20\n.a8\n");
    for(unsigned offset=0;offset<n;offset+=65536){
        unsigned loop=++cg.label,count=n-offset;
        if(offset){
            /* The pointer's padded bank word is updated at 16-bit width */
            if(byte)code("    rep #$20\n.a16\n");
            code("    inc z:__arith_lhs+2\n");
            if(copying)code("    inc z:__arith_rhs+2\n");
            if(byte)code("    sep #$20\n.a8\n");
        }
        code("    ldy #0\n");label(loop);
        code("    lda [__arith_lhs],y\n");
        if(copying)code("    sta [__arith_rhs],y\n");
        code("    iny\n");
        if(!byte)code("    iny\n");
        if(count<65536)code("    cpy #$%04X\n    bcc cg_%s_%u\n",count,cg.parser->unit,loop);
        else code("    bne cg_%s_%u\n",cg.parser->unit,loop);
    }
    if(byte)code("    rep #$20\n.a16\n");
    if(restore_destination&&n>65536)code("    dec z:__arith_rhs+2\n");
    code("    ply\n");
}
/* Volatile aggregate transfers deliberately visit every object byte, padding
 * included, in increasing address order. No MVN or widened padding access. */
static void volatile_aggregate(Expr *e,int copying,int needed)
{
    Expr *source=copying?e->right:e;
    Type address=far_type(type(TY_CHAR,1));unsigned loop,n=width(e->type);
    if(copying&&volatile_fixed_copy(e,needed))return;
    loop=++cg.label;
    if(copying){
        emit_address(e->left);if(!e->left->type.banked)code("    ldx #$007E\n");push_value(address);
    }
    emit_address(source);if(!source->type.banked)code("    ldx #$007E\n");stage(0,address);
    if(copying){pop_value(address);stage(1,address);}
    if(n>=65536)
        wide_aggregate_transfer(n,copying,1,copying&&needed&&e->left->type.banked);
    else{
        code("; volatile aggregate: %u byte accesses\n    phy\n    ldy #0\n    sep #$20\n.a8\n",n);label(loop);
        code("    lda [__arith_lhs],y\n");
        if(copying)code("    sta [__arith_rhs],y\n");
        code("    iny\n    cpy #$%04X\n    bcc cg_%s_%u\n    rep #$20\n.a16\n    ply\n",n,cg.parser->unit,loop);
    }
    if(copying&&needed){code("    lda z:__arith_rhs\n");if(e->left->type.banked)code("    ldx z:__arith_rhs+2\n");}
    divmod_state.available=0;
}
static void emit_aggregate_copy(Expr *e,int needed)
{
    if(volatile_type(e->left->type)||volatile_type(e->right->type)){volatile_aggregate(e,1,needed);return;}
    unsigned n=width(e->type),source_offset,destination_offset,i,start;
    Symbol *source=direct_memory_object(e->right,&source_offset),*destination=direct_memory_object(e->left,&destination_offset);
    int fixed=source&&destination&&!source->owner&&!destination->owner;
    /* A short named-object-to-frame copy can address each word directly. MVN
     * would need to form both addresses and save the frame register first. */
    int short_frame=source&&!source->owner&&!source->type.banked&&destination&&destination->owner&&
        n<=8&&!(n&1);
    int direct=fixed||(source&&destination&&(n<=4||short_frame)&&!cg.parser->no_copy_selection);
    int expanded=(source&&source->wram)||(destination&&destination->wram);
    int call_result=e->right->kind==EX_CALL&&e->right->third&&e->right->third->kind==EX_OBJECT;
    if(!cg.parser->no_copy_selection&&!e->left->type.banked&&!e->right->type.banked&&
       (n==2||n==4)&&(call_result||(!direct&&(source||destination)))){
        if(call_result){
            /* The destination belongs to this invocation while the call fills its buffer */
            code("; aggregate copy: inline %u bytes from a call result\n",n);
            if(!destination){emit_address(e->left);push_value(type(TY_INT,0));}
            emit_call(e->right,0);
            if(!destination){code("    plx\n");if(cg.stack_leaf)cg.stack_bias-=2;}
            source=e->right->third->symbol;
            source_offset=0;
        }else{
            code("; aggregate copy: inline %u bytes with one fixed address\n",n);
            emit_address_x(source?e->left:e->right);
        }
        for(i=0;i<n;i+=2){
            code("    lda ");
            if(source)array_operand(source,source_offset+i);
            else code("a:$%04X,x",i);
            code("\n    sta ");
            if(destination)array_operand(destination,destination_offset+i);
            else code("a:$%04X,x",i);
            code("\n");
        }
        if(needed){
            if(destination)emit_address(e->left);
            else code("    txa\n");
        }
        divmod_state.available=0;
        return;
    }
    if(n>=65536||((e->left->type.banked||e->right->type.banked)&&(!direct||(expanded&&n>12)))){
        Type address=far_type(type(TY_CHAR,1));unsigned loop=++cg.label;
        emit_address(e->left);if(!e->left->type.banked)code("    ldx #$007E\n");push_value(address);
        emit_address(e->right);if(!e->right->type.banked)code("    ldx #$007E\n");stage(0,address);
        pop_value(address);stage(1,address);
        if(n>=65536)
            wide_aggregate_transfer(n,1,0,needed&&e->left->type.banked);
        else{
            code("; aggregate copy: runtime banks, %u bytes\n    phy\n    ldy #0\n",n);label(loop);
            code("    lda [__arith_lhs],y\n    sta [__arith_rhs],y\n    iny\n    iny\n    cpy #$%04X\n    bcc cg_%s_%u\n    ply\n",n,cg.parser->unit,loop);
        }
        if(needed){code("    lda z:__arith_rhs\n");if(e->left->type.banked)code("    ldx z:__arith_rhs+2\n");}
        divmod_state.available=0;return;
    }
    unsigned long_words=direct&&source->type.banked?n/2:0;
    CopyPlan plan={0,(direct?5:6)*n+long_words,3*n+long_words};
    unsigned cycles,bytes,mode;
    /* Policy: one code byte costs eight nominal CPU cycles. Bound expansion
     * to 128 bytes; --no-copy-selection retains the simple inline reference.
     * Address/result staging common to candidates is omitted from the score. */
    if(!expanded&&!cg.parser->no_copy_selection&&(fixed||!direct)){
        unsigned candidate_cycles=7*n+(fixed?18:3),candidate_bytes=fixed?14:6;
        copy_consider(&plan,2,candidate_cycles,candidate_bytes);
        if(fixed&&n<=32768){
            candidate_cycles=19*(n/2)+2+long_words;candidate_bytes=13+(long_words!=0);
            copy_consider(&plan,1,candidate_cycles,candidate_bytes);
        }
    }
    mode=plan.mode;cycles=plan.cycles;bytes=plan.bytes;
    code("; aggregate copy: %s %u bytes, estimated %u cycles / %u code bytes\n",mode==0?"inline":mode==1?"loop":"mvn",n,cycles,bytes);
    if(direct){
        source->used=destination->used=1;
        if(mode==0){
            for(i=0;i<n;i+=2){
                code("    lda ");array_operand(source,source_offset+i);code("\n    sta ");array_operand(destination,destination_offset+i);code("\n");
            }
        }else if(mode==1){
            start=++cg.label;code("    ldx #$%04X\n",n-2);label(start);
            code("    lda %s:_%s+$%04X,x\n    sta a:_%s+$%04X,x\n    dex\n    dex\n",source->type.banked?"f":"a",source->asm_name,source_offset,destination->asm_name,destination_offset);
            code("    bpl cg_%s_%u\n",cg.parser->unit,start);
        }else{
            code("    phy\n    ldx #.loword(_%s+$%04X)\n    ldy #.loword(_%s+$%04X)\n    lda #$%04X\n    mvn #.bankbyte(_%s), #$7E\n    ply\n",source->asm_name,source_offset,destination->asm_name,destination_offset,n-1,source->asm_name);
        }
        if(needed)emit_address(e->left);
    }else{
        /* Evaluate each operand once. A stack-owned destination survives calls
         * and nested assignments on the right. A direct source X load can keep
         * the destination in A. Only value uses need a second destination home
         * across the transfer. No DP scratch. */
        emit_address(e->left);
        if(address_x_preserves_a(e->right))emit_address_x(e->right);
        else{code("    pha\n");emit_address(e->right);code("    tax\n    pla\n");}
        code("    phy\n");if(needed)code("    pha\n");code("    tay\n");
        if(mode==0){
            for(i=0;i<n;i+=2)code("    lda a:$%04X,x\n    sta a:$%04X,y\n",i,i);
        }else code("    lda #$%04X\n    mvn #$7E, #$7E\n",n-1);
        if (needed) {
            code("    pla\n");
        }
        code("    ply\n");
    }
    /* Embedded scalar/pointer fields may have changed through an alias */
    divmod_state.available=0;
}

static void copy_prepare_expr(Function *f,Expr *e)
{
    unsigned i;Symbol *s;if(!e)return;
    if(e->kind==EX_OBJECT&&(s=e->symbol)->copy_temporary&&!s->offset){
        s->offset=f->slots+2;f->slots+=width(s->type)+2;
        if(f->slots+4>768)error_at(e->location,"aggregate value temporary exceeds frame budget");
    }
    copy_prepare_expr(f,e->left);copy_prepare_expr(f,e->right);copy_prepare_expr(f,e->third);
    for(i=0;i<e->arg_count;++i)copy_prepare_expr(f,e->args[i]);
}
static void copy_prepare(Function *f,Statement *s)
{
    for(;s;s=s->next){
        Expr *store=s->expression;
        if(!cg.parser->no_copy_selection&&!cg.parser->no_body_optimizations&&
           !find_symbol(cg.parser,"$basic_asm")&&s->kind==ST_EXPR&&store&&store->kind==EX_ASSIGN&&
           !store->op&&structure_object(store->type)&&store->left->kind==EX_OBJECT&&
           store->right->kind==EX_CALL&&!volatile_type(store->left->type)&&!volatile_type(store->right->type)&&
           store->left->symbol->offset&&
           !store->left->type.banked&&loop_private(store->left->symbol)){
            /* The callee cannot reach a private destination except through
             * the hidden result pointer. Arguments are still passed by value. */
            Expr *call=store->right;
            free_expression(call->third);
            call->third=store->left;
            s->expression=call;
            free(store);
        }
        copy_prepare_expr(f,s->expression);copy_prepare_expr(f,s->step);
        copy_prepare(f,s->initial);copy_prepare(f,s->body);copy_prepare(f,s->alternate);
    }
}
