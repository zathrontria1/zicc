/* Two discarded low/high-byte stores to adjacent near RAM can share one A16
 * store. Only private word sources and pure, stable indices participate. */
static int store_integer(Type t)
{
    return !t.pointers&&!t.array&&!t.is_bool&&(t.base==TY_INT||t.base==TY_CHAR);
}
static Expr *store_casts(Expr *e)
{
    while(e&&e->kind==EX_CAST&&store_integer(e->type)&&store_integer(e->left->type))e=e->left;
    return e;
}
static Expr *store_word_casts(Expr *e)
{
    while(e&&e->kind==EX_CAST&&store_integer(e->type)&&width(e->type)==2&&
          store_integer(e->left->type)&&width(e->left->type)==2)e=e->left;
    return e;
}
static Symbol *store_bytes_source(Expr *low,Expr *high)
{
    uint32_t n;Expr *source;
    low=store_casts(low);high=store_casts(high);
    if(low&&low->kind==EX_BINARY&&low->op=='&'&&integer_constant(low->right,&n)&&n==255)low=store_casts(low->left);
    if(!high||high->kind!=EX_BINARY||high->op!=TOK_SHR||!integer_constant(high->right,&n)||n!=8)return NULL;
    source=store_word_casts(high->left);
    if(!source||source->kind!=EX_OBJECT||source->type.array||source->type.pointers||
       source->type.base!=TY_INT||object_volatile(source->type)||!loop_private(source->symbol))return NULL;
    /* Low-byte casts may truncate; the shift input must retain the full word */
    low=store_word_casts(low);
    return low&&low->kind==EX_OBJECT&&low->symbol==source->symbol?source->symbol:NULL;
}
static int store_index_pure(Expr *e)
{
    if(!e||!store_integer(e->type))return 0;
    if(e->kind==EX_INT)return 1;
    if(e->kind==EX_OBJECT)return !object_volatile(e->type)&&loop_private(e->symbol);
    if(e->kind==EX_CAST)return store_index_pure(e->left);
    return e->kind==EX_BINARY&&(e->op=='+'||e->op=='-'||e->op=='*'||e->op=='&'||e->op=='|'||e->op=='^'||
        e->op==TOK_SHL||e->op==TOK_SHR)&&store_index_pure(e->left)&&store_index_pure(e->right);
}
static int store_same_index(Expr *a,Expr *b)
{
    if(!a||!b)return a==b;
    if(a->kind!=b->kind||a->op!=b->op||!same_type(unqualified_value(a->type),unqualified_value(b->type)))return 0;
    if(a->kind==EX_OBJECT)return a->symbol==b->symbol;
    if(a->kind==EX_INT)return a->value==b->value;
    return store_same_index(a->left,b->left)&&store_same_index(a->right,b->right);
}
static Expr *store_index_base(Expr *e,int32_t *offset)
{
    uint32_t n;
    /* Only peel non-narrowing casts and a literal final displacement. The
     * original first index is still evaluated; this does not fold its wrap. */
    e=store_word_casts(e);*offset=0;
    if(e->kind==EX_BINARY&&(e->op=='+'||e->op=='-')&&integer_constant(e->right,&n)&&reg_width(e->right->type)==2){
        *offset=e->right->type.is_unsigned?(int32_t)(n&65535):(int32_t)(int16_t)n;
        if (e->op == '-') {
            *offset = -*offset;
        }
        return e->left;
    }return e;
}
static int store_ram(Symbol *s)
{
    return s&&!s->dpage&&!s->type.banked&&!object_volatile(s->type)&&!object_constant(s->type)&&width(s->type)<=65536;
}

/* Keep the payload in the function's indivisible code segment so MVN
 * cannot wrap into another source bank. */
static Statement *local_byte_block(Statement *s)
{
    Symbol *array=NULL;
    unsigned char bytes[128];
    unsigned n=0,offset,id;
    Statement *p,*last=NULL;
    if(cg.parser->no_copy_selection||cg.parser->no_body_optimizations||
       cg.function->symbol->interrupt||cg.stack_leaf||cg.numeric_index||
       cg.bound||cg.affine_active||cg.lftr_active||cg.retained_index)return NULL;
    for(p=s;p&&p->kind==ST_EXPR&&!p->inline_callee&&n<sizeof bytes;p=p->next){
        Expr *e=p->expression;
        Symbol *base;
        uint32_t byte;
        if(!e||e->kind!=EX_ASSIGN||e->op||!store_integer(e->type)||width(e->type)!=1||
           volatile_expression(e)||!integer_constant(e->right,&byte))break;
        base=fixed_memory_object(e->left,&offset);
        if(!store_ram(base)||!base->owner||!base->type.array||
           width(array_element(base->type))!=1||offset!=n||(array&&array!=base))break;
        array=base;bytes[n++]=(unsigned char)byte;last=p;
    }
    /* Paired immediate stores win for short initializers */
    if(n<18||n!=width(array->type))return NULL;
    /* A short repeated word needs one immediate load and no ROM payload.
     * Limit code growth to sixteen indexed stores. */
    if(n<=32&&!(n&1)&&!memcmp(bytes,bytes+2,n-2)){
        code("    lda #$%04X\n",bytes[0]|((unsigned)bytes[1]<<8));
        for(unsigned i=0;i<n;i+=2){
            code("    sta ");array_operand(array,i);code("\n");
        }
        return last;
    }
    id=++cg.label;
    require_frame_home(array);
    if(cg.dp_homes)cg.dp_failed=1;
    code("; local byte initializer: mvn\n    tya\n    clc\n    adc #$%04X\n    phy\n    tay\n",
         frame_offset(array->offset));
    code("    ldx #.loword(cg_%s_%u_data)\n    lda #$%04X\n"
         "    mvn #.bankbyte(cg_%s_%u_data), #$7E\n    ply\n",
         cg.parser->unit,id,n-1,cg.parser->unit,id);
    code("; block copy payload %u ",id);
    for(unsigned i=0;i<n;++i)code("%02X",bytes[i]);
    code("\n");
    return last;
}
static int store_pair_candidate(Statement *s)
{
    Expr *a,*b,*first,*second;IndexedOperand low,high;int32_t x,y;
    uint32_t val_a=0,val_b=0;int const_bytes;
    if(cg.parser->no_store_fusion||cg.parser->no_strength_reduction||cg.parser->no_body_optimizations||
       s->kind!=ST_EXPR||!s->next||s->next->kind!=ST_EXPR||s->inline_callee||s->next->inline_callee)return 0;
    a=s->expression;b=s->next->expression;
    if(!a||!b||a->kind!=EX_ASSIGN||b->kind!=EX_ASSIGN||a->op||b->op||
       !store_integer(a->type)||!store_integer(b->type)||width(a->type)!=1||width(b->type)!=1||
       volatile_expression(a)||volatile_expression(b))return 0;
    const_bytes=integer_constant(a->right,&val_a)&&integer_constant(b->right,&val_b);
    if(!const_bytes&&!store_bytes_source(a->right,b->right))return 0;
    {
        unsigned off_a=0,off_b=0;
        Symbol *base_a=fixed_memory_object(a->left,&off_a);
        Symbol *base_b=fixed_memory_object(b->left,&off_b);
        if(base_a&&base_a==base_b&&store_ram(base_a)&&off_b==off_a+1&&off_a+2<=width(base_a->type))return 1;
    }
    if(!store_bytes_source(a->right,b->right))return 0;
    if(!indexed_operand(a->left,&low)||!indexed_operand(b->left,&high)||low.base!=high.base||
       low.scale!=1||high.scale!=1||low.base->owner||!store_ram(low.base)||!store_index_pure(low.index)||!store_index_pure(high.index))return 0;
    first=store_index_base(low.index,&x);second=store_index_base(high.index,&y);
    return store_same_index(first,second)&&(int64_t)y+high.offset==(int64_t)x+low.offset+1;
}
static int adjacent_store(Statement *s)
{
    Statement *next=s->next;Expr *a,*b,*first,*second;Symbol *source,*base,*other;
    IndexedOperand low,high;unsigned offset=0,other_offset=0;int32_t x,y;uint32_t maximum;
    uint32_t val_a=0,val_b=0;int const_bytes;
    if(cg.parser->no_store_fusion||cg.parser->no_strength_reduction||cg.parser->no_body_optimizations||
       cg.function->symbol->interrupt||cg.numeric_index||cg.bound||cg.affine_active||cg.lftr_active||cg.scalar_first||
       !next||next->kind!=ST_EXPR||s->inline_callee||next->inline_callee)return 0;
    a=s->expression;b=next->expression;
    if(!a||!b||a->kind!=EX_ASSIGN||b->kind!=EX_ASSIGN||a->op||b->op||
       volatile_expression(a)||volatile_expression(b))return 0;
    first=word_bits(a->right);second=word_bits(b->right);
    if(first->kind==EX_BITFIELD&&second->kind==EX_BITFIELD&&
       first->type.bit_field_width==second->type.bit_field_width&&body_equal(first,second)&&
       word_integer(a->type)&&word_integer(b->type)&&
       (base=direct_memory_object(a->left,&offset))&&!base->owner&&store_ram(base)&&
       (other=direct_memory_object(b->left,&other_offset))&&!other->owner&&store_ram(other)){
        unsigned field_offset;
        Symbol *field=direct_memory_object(first->left,&field_offset);
        if(field&&field!=base&&loop_private(field)&&!field->type.banked){
            emit_value(first);
            code("    sta ");array_operand(base,offset);code("\n");
            code("    sta ");array_operand(other,other_offset);code("\n");
            divmod_written(a->left);divmod_written(b->left);return 1;
        }
    }
    if(!store_integer(a->type)||!store_integer(b->type)||width(a->type)!=1||width(b->type)!=1)return 0;
    source=store_bytes_source(a->right,b->right);
    const_bytes=!source&&integer_constant(a->right,&val_a)&&integer_constant(b->right,&val_b);
    if(!source&&!const_bytes)return 0;
    base=fixed_memory_object(a->left,&offset);other=fixed_memory_object(b->left,&other_offset);
    if(base&&other==base&&store_ram(base)&&other_offset==offset+1&&offset+2<=width(base->type)){
        code("; fused adjacent RAM byte stores\n");
        if(const_bytes){
            uint32_t val16=(val_a&0xFF)|((val_b&0xFF)<<8);
            code("    lda #$%04X\n",(unsigned)val16);
        }else load_symbol(source);
        code("    sta ");array_operand(base,offset);code("\n");
        divmod_written(a->left);divmod_written(b->left);return 1;
    }
    if(!source)return 0;
    if(!indexed_operand(a->left,&low)||!indexed_operand(b->left,&high)||low.base!=high.base||
       low.scale!=1||high.scale!=1||low.base->owner||!store_ram(low.base))return 0;
    if(indexed_retained(&low,1)&&indexed_retained(&high,1)&&low.reg==high.reg&&low.reg!='c'&&high.offset==low.offset+1){
        maximum=low.offset+(cg.retained_limit-1)*(low.reg=='x'?cg.retained_scale:1);
    }else{
        /* Failed retained matching may have changed an operand plan */
        if(!indexed_operand(a->left,&low)||!indexed_operand(b->left,&high))return 0;
        first=store_index_base(low.index,&x);second=store_index_base(high.index,&y);
        if(!store_index_pure(low.index)||!store_index_pure(high.index)||!store_same_index(first,second)||
           (int64_t)y+high.offset!=(int64_t)x+low.offset+1||
           !low.index->known.valid||low.index->known.min<0||!high.index->known.valid||high.index->known.min<0||
           (int64_t)high.index->known.max+high.offset!=(int64_t)low.index->known.max+low.offset+1)return 0;
        maximum=(unsigned)low.index->known.max+low.offset;
    }
    if(maximum+2>width(low.base->type))return 0;
    code("; fused adjacent RAM byte stores\n");indexed_index(&low);load_symbol(source);
    code("    sta ");indexed_text(&low);code("\n");indexed_finish(&low);
    divmod_written(a->left);divmod_written(b->left);return 1;
}

typedef struct {
    Statement *first,*last;
    Symbol *home;
    unsigned offset,mask;
} BitfieldStores;

/* RHS operands cannot observe the destination before the combined store */
static int bitfield_store_group(Statement *s,BitfieldStores *group)
{
    Statement *next;
    *group=(BitfieldStores){0};group->first=s;
    for(next=s;next&&next->kind==ST_EXPR&&!next->inline_callee;next=next->next){
        Expr *e=next->expression;
        unsigned at;
        Symbol *base;
        if(!e||e->kind!=EX_ASSIGN||e->op||e->left->kind!=EX_BITFIELD||volatile_expression(e))break;
        Expr *field=e->left,*rhs=word_bits(e->right);
        if(!store_integer(rhs->type)||width(rhs->type)!=2||
           (rhs->kind!=EX_INT&&rhs->kind!=EX_OBJECT))break;
        base=direct_memory_object(field->left,&at);
        if(!base||!store_ram(base)||(rhs->kind==EX_OBJECT&&rhs->symbol==base))break;
        if(!group->home){group->home=base;group->offset=at;}
        if(base!=group->home||at!=group->offset)break;
        unsigned bits=((1u<<field->type.bit_field_width)-1)<<field->value;
        if(group->mask&bits)break;
        group->mask|=bits;group->last=next;
    }
    return group->last&&group->last!=s;
}

static Statement *bitfield_store_region(Statement *s,BitfieldStores *group)
{
    if(s&&s->kind==ST_BLOCK&&!s->inline_callee){
        if(bitfield_store_group(s->body,group)&&!group->last->next)return s;
    }else if(bitfield_store_group(s,group))return group->last;
    return NULL;
}

static int same_bitfield_payload(BitfieldStores *first,BitfieldStores *second)
{
    if(first->mask!=second->mask)return 0;
    for(Statement *a=first->first,*b=second->first;;a=a->next,b=b->next){
        Expr *lhs=a->expression->left,*rhs=b->expression->left;
        Expr *value=word_bits(a->expression->right);
        if(lhs->value!=rhs->value||lhs->type.bit_field_width!=rhs->type.bit_field_width||
           !body_equal(value,word_bits(b->expression->right)))return 0;
        if(a==first->last||b==second->last)return a==first->last&&b==second->last;
    }
}

static void store_bitfield_payload(BitfieldStores *group)
{
    if(group->mask!=65535){
        code("    lda ");array_operand(group->home,group->offset);
        code("\n    and #$%04X\n    ora z:__arith_rhs\n",65535^group->mask);
    }
    code("    sta ");array_operand(group->home,group->offset);code("\n");
}

static Statement *adjacent_bitfield_stores(Statement *s)
{
    BitfieldStores first,next;
    Statement *step,*last,*end;
    if(cg.parser->no_store_fusion||cg.parser->no_strength_reduction||cg.stack_leaf||
       cg.function->symbol->interrupt||!(last=bitfield_store_region(s,&first)))return NULL;
    code("; fused adjacent bit-field stores\n");
    cg.arithmetic=1;
    for(step=first.first;;step=step->next){
        Expr *e=step->expression,*field=e->left;
        emit_value(word_bits(e->right));
        code("    and #$%04X\n",(1u<<field->type.bit_field_width)-1);
        bitfield_shift(field->value,1);
        if(step!=first.first)code("    ora z:__arith_rhs\n");
        if(step==first.last)break;
        code("    sta z:__arith_rhs\n");
    }
    if(first.mask!=65535)code("    sta z:__arith_rhs\n");
    store_bitfield_payload(&first);
    while((end=bitfield_store_region(last->next,&next))&&same_bitfield_payload(&first,&next)){
        code("; shared packed bit-field payload\n");
        store_bitfield_payload(&next);last=end;
    }
    cg.divmod_available=0;
    return last;
}
