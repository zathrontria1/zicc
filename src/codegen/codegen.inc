#define DP_SCRATCH_BASE 0x02

typedef struct BankVariant BankVariant;
// Each call keeps its C locals in a stack frame. Calls can overwrite arithmetic scratch space
typedef struct { Symbol *base,*index;unsigned scale,offset;int wram; } InductionCursor;
typedef struct { Expr *address;unsigned offset,stride; } AffineAccess;
typedef struct {
    Symbol *index;
    Expr *bound;
    int update_index,recover_index,wide,countdown,descending,inclusive,wrap_at_limit,starts_zero,bound_loaded,entry_test;
} DpCounter;
typedef struct {
    unsigned factor,span,width,stride,bytes,cost,rolled;
    int known,full,hoist;
    DpCounter counter;
} UnrollPlan;
typedef struct {
    Statement *statement;Symbol *index;int delta;
    AffineAccess accesses[8];unsigned count;
    Symbol *dependencies[32];unsigned dependency_count;
    UnrollPlan unroll;int unroll_selected,dead_index;
} AffineLoop;

typedef struct { Expr *expression;unsigned operations,offset;int reused; } DivmodCache;
typedef struct {
    Symbol *source,*destination,*font,*buffer;
    unsigned source_uses,destination_uses,max_offset;
    int failed;
} FixedWordRows;
enum { MAX_DOT_TERMS=8, MAX_DOT_PRODUCTS=16, MAX_DOT_PACKS=24 };
typedef struct {
    Expr *value_expr;
    Symbol *coeff_sym,*pack_sym;
    int negate;
} DotTerm;
typedef struct {
    Statement *loop;
    Expr *expr;
    Symbol *bias_sym;
    DotTerm terms[MAX_DOT_TERMS];
    unsigned term_count;
    int uses_x;
} DotProduct;
typedef struct {
    Statement *loop;
    Symbol *coeff_sym,*pack_sym;
    int negate,swapped;
} DotPack;
enum { MAX_RETAINED_CURSORS=4 };
typedef struct {
    Symbol *base;
    unsigned offset,scale,dp_word;
} RetainedCursor;
typedef struct {
    Parser *parser; Function *function; unsigned label,inline_label;
    BankVariant *banks[256];unsigned bank_count;
    int arithmetic,require_float_format,require_int64_format;
    Symbol *retained_index,*retained_second,*retained_ptr;unsigned retained_scale,retained_limit,retained_second_scale,retained_bias,retained_unroll;int retained_y,retained_scratch,retained_failed;
    RetainedCursor retained_cursors[MAX_RETAINED_CURSORS];unsigned retained_cursor_count,retained_cursor_mask;
    Symbol *numeric_index,*numeric_recurrence;unsigned numeric_limit,numeric_scale,numeric_offset;
    unsigned interrupt_scratch;
    const char *helpers[64]; unsigned helper_count;
    unsigned loop_start[64],loop_end[64],loop_count,switch_depth,jump_base;
    InductionCursor cursors[32];unsigned cursor_count;
    DivmodCache divmod[16];unsigned divmod_count,divmod_available;
    Symbol *divmod_version;int divmod_wide_version;
    AffineLoop affine[32],*affine_active;unsigned affine_count;
    Symbol *dead_indices[32];unsigned dead_index_count;
    Symbol *omitted_parameters[2];unsigned omitted_parameter_count,register_homes,register_spills;
    int stack_leaf;unsigned stack_bias;
    int lp_volatile,lp_frame_address,lp_word_result,lp_value_result;
    int loop_y_borrowed;
    FixedWordRows *fixed_rows;
    Symbol *scalar_first;int scalar_leaf,scalar_spill;
    Symbol *leaf_count;
    int near_strcmp,need_smul8,need_pack_coeff;
    DotProduct dots[MAX_DOT_PRODUCTS];unsigned dot_count;
    DotPack dot_packs[MAX_DOT_PACKS];unsigned dot_pack_count;
    Symbol *scan_cursor;
    int scan_failed;
    /* Direct-page homes (dp_homes.inc): dp_map[word] is 1+workspace word */
    int dp_homes,dp_frameless,dp_trial,dp_failed,dp_byte_operand;unsigned dp_words;
    unsigned dp_incoming_base;int dp_zero_stack;
    unsigned short frame_map[384];unsigned frame_saved;
    unsigned char dp_map[384];unsigned dp_weight[384];
    /* Register-resident cursor (bound_cursors.inc): X holds bound->offset's
     * value plus bound_delta between bound_start and bound_end. */
    InductionCursor *bound,*bound_pending;unsigned bound_delta,bound_mark_count;
    int bound_failed,bound_own,bound_entered;size_t bound_start,bound_end,bound_marks[128];
    /* Eliminated C indices (lftr.inc); lftr_failed records any use of a home */
    Symbol *lftr[8];unsigned lftr_count;int lftr_active,lftr_failed;
    char *assembly;size_t length,capacity;
} Codegen;
static Codegen cg;
static int integer_constant(Expr *e,uint32_t *value);
static int parameter_incoming_live(Symbol *v);
/* The caller's automatic objects stay live while a callee runs. Once
 * their addresses can be observed, even a zero-argument call may read them
 * through a previously published pointer. Use a function-wide guard until
 * stack-pointer provenance is available at each individual call. */
static int automatic_designator(Expr *e)
{
    while(e&&e->kind==EX_MEMBER&&e->op!=TOK_ARROW)e=e->left;
    return e&&e->kind==EX_OBJECT&&e->symbol->owner;
}

static int frame_address_expression(Expr *e)
{
    unsigned i;
    if(!e)return 0;
    /* A direct scalar field access does not publish the enclosing address */
    if(e->kind==EX_MEMBER&&!e->type.array&&!structure_object(e->type)&&automatic_designator(e))
        return 0;
    if(e->kind==EX_VA_START||e->kind==EX_RESULT_ADDR||
       (e->kind==EX_ADDRESS&&automatic_designator(e->left))||
       (e->kind==EX_OBJECT&&e->symbol->owner&&
        (e->symbol->type.array||structure_object(e->symbol->type))))return 1;
    if(frame_address_expression(e->left)||frame_address_expression(e->right)||
       frame_address_expression(e->third))return 1;
    for(i=0;i<e->arg_count;++i)if(frame_address_expression(e->args[i]))return 1;
    return 0;
}

static const char frame_address_marker[]="; caller frame address visible\n";

static int frame_address_visible(Statement *s)
{
    for(;s;s=s->next)
        if(frame_address_expression(s->expression)||frame_address_expression(s->step)||
           frame_address_visible(s->initial)||frame_address_visible(s->body)||
           frame_address_visible(s->alternate))return 1;
    return 0;
}

static int loop_escapes(Statement *s,Symbol *symbol);
static int known_integer(Type t);
static int vr_immutable(Symbol *s);
static int body_private(Symbol *v);
static int body_equal(Expr *a,Expr *b);
static int body_address_pure(Expr *e);
static int body_has_deref(Expr *e);
static int mapped_word_home(Symbol *v);
static int structured_byte_loop(Statement *s);
static int fixed_byte_copy_loop(Statement *s);
static void known_prepare(Function *f);
static unsigned scalar_writes(Statement *s,Symbol *v);
static int dot_reserved_symbol(const Symbol *v);
static void region_home_liveness(Function *f,Statement *s,unsigned offset,int *in,int *out);
static DotProduct *dot_match_expr(Expr *e);
static int dot_indexed_byte(Expr *e,Symbol **base_out,Expr **idx_out,
                            unsigned *off_out,unsigned *scale_out,int *far_out);
static int dot_preserves_x(Expr *e);
static void dot_emit_loop_setup(Statement *s);
static int dot_emit_expr(Expr *e);
static void zicc_smul8_name(char *name,size_t size);
static void zicc_pack_coeff_name(char *name,size_t size);
static void require_frame_home(Symbol *s)
{
    unsigned i;
    if(s==cg.scan_cursor)cg.scan_failed=1;
    if(s==cg.retained_index&&(cg.retained_y==1||cg.retained_y==2||cg.retained_y==4||(cg.retained_y==5&&cg.retained_ptr)))cg.retained_failed=1;
    for(i=0;i<cg.dead_index_count;++i)if(cg.dead_indices[i]==s)
        error_at(here(cg.parser),"internal read/write of eliminated induction home '%s'",s->name);
    for(i=0;i<cg.omitted_parameter_count;++i)if(cg.omitted_parameters[i]==s)
        error_at(here(cg.parser),"internal read/write of eliminated parameter home '%s'",s->name);
}
static void code(const char *format,...)
{
    va_list args,copy;int n;char *buffer;
    va_start(args,format);va_copy(copy,args);n=vsnprintf(NULL,0,format,args);va_end(args);
    if(n<0){va_end(copy);fputs("assembly formatting failed\n",stderr);exit(EXIT_FAILURE);}
    if(cg.length+(size_t)n+1>cg.capacity){
        size_t capacity=cg.capacity?cg.capacity:4096;
        while(capacity<cg.length+(size_t)n+1)capacity*=2;
        buffer=realloc(cg.assembly,capacity);
        if(!buffer){va_end(copy);fputs("out of memory emitting assembly\n",stderr);exit(EXIT_FAILURE);}
        cg.assembly=buffer;cg.capacity=capacity;
    }
    vsnprintf(cg.assembly+cg.length,cg.capacity-cg.length,format,copy);va_end(copy);cg.length+=(size_t)n;
}
static void inline_marker(Statement *s)
{
    if(!s->inline_callee)return;
    unsigned id=++cg.inline_label;
    code("; inlined call: %s %s\n.export __inlined_%s_%u_%s\n__inlined_%s_%u_%s:\n",
        cg.function->symbol->asm_name,s->inline_callee->asm_name,cg.parser->unit,id,s->inline_callee->asm_name,
        cg.parser->unit,id,s->inline_callee->asm_name);
}
static int statement_inline_markers(Statement *s)
{
    for(;s;s=s->next)if(s->inline_callee||statement_inline_markers(s->body)||
        statement_inline_markers(s->alternate)||statement_inline_markers(s->initial))return 1;return 0;
}
/* Operand text for the general path's frame byte at offset. Every Y-relative
 * frame access is formatted here so individual slots can later be relocated
 * without touching emitters. Rotating buffers allow several per call. */
static unsigned frame_offset(unsigned offset)
{
    unsigned word=(offset-1)/2;
    if(offset>cg.function->slots)return offset-cg.frame_saved;
    if(offset&&word<384&&cg.frame_map[word])return cg.frame_map[word]+((offset-1)&1);
    return offset;
}
static const char *frame_operand(unsigned offset)
{
    static char buffers[8][24];static unsigned next;
    char *text=buffers[next++&7];unsigned word;
    if(cg.retained_index&&(cg.retained_y==1||cg.retained_y==2||cg.retained_y==4||(cg.retained_y==5&&cg.retained_ptr))&&offset>=cg.retained_index->offset&&offset<cg.retained_index->offset+2)cg.retained_failed=1;
    if(cg.dp_homes&&cg.dp_zero_stack&&offset>=cg.dp_incoming_base){
        if(cg.loop_y_borrowed)cg.dp_failed=1;
        snprintf(text,sizeof buffers[0],"a:$%04X,y",offset-cg.dp_incoming_base+5+cg.parser->long_return);return text;
    }
    if(cg.bound&&!cg.bound_own&&offset==cg.bound->offset)cg.bound_failed=1;
    if(cg.lftr_active){unsigned k;for(k=0;k<cg.lftr_count;++k)
        if(offset>=cg.lftr[k]->offset&&offset<=cg.lftr[k]->offset+1)cg.lftr_failed=1;}
    word=offset?(offset-1)/2:0;
    if((cg.dp_trial)&&offset&&word<384){
        unsigned depth=cg.loop_count<4?cg.loop_count:4;
        cg.dp_weight[word]+=1u<<(3*depth);
    }
    if(cg.dp_homes){
        /* A promoted word is spelled as a placeholder until the function is
         * validated, so the workspace scan can tell homes from other uses. */
        if(offset&&word<cg.dp_words&&cg.dp_map[word]&&(!((offset-1)&1)||cg.dp_byte_operand)){
            snprintf(text,sizeof buffers[0],"z:__dp_home_%02u%s",cg.dp_map[word]-1u,
                     (offset-1)&1?"+1":"");return text;
        }
        if(cg.dp_frameless||(offset&&word<cg.dp_words&&cg.dp_map[word]))cg.dp_failed=1;
    }
    if(cg.loop_y_borrowed)cg.dp_failed=1;
    offset=frame_offset(offset);
    snprintf(text,sizeof buffers[0],"a:$%04X,y",offset);
    return text;
}
static int affine_pointer(Expr *e,int in_x);
/* The build driver supplies cross-bank public entries before relaxation */
static void call_entry(const char *name)
{
    const char *p=cg.parser->long_calls;int far=cg.parser->long_return||!strcmp(name,"_main");size_t n=strlen(name);
    if(cg.parser->source_lto&&name[0]=='_'){
        Function *f;for(f=cg.parser->functions;f;f=f->next)
            if(!strcmp(f->symbol->asm_name,name+1)&&!f->symbol->inline_omit&&
               (!f->symbol->inline_hint||f->symbol->internal||f->symbol->inline_external)){p=NULL;break;}
    }
    while(p&&*p){
        const char *end=strchr(p,',');size_t length=end?(size_t)(end-p):strlen(p);
        if(length==n&&!strncmp(p,name,n))far=1;
        p=end?end+1:NULL;
    }
    if(far)code("    jsl %s\n",name);else code("    jsr .loword(%s)\n",name);
}
static void helper(const char *name)
{
    if(cg.function&&cg.function->symbol->interrupt){
        /* Word bits are relative to the scratch base. Helper contracts are audited against
         * the assembly modules by tests/check-interrupt-scratch.py. */
        static const struct { const char *name;unsigned writes;const char *entry; } safe[]={
            {"__ucmp16",0},{"__scmp16",0},{"__ucmp32",0},{"__scmp32",0},
            {"__shl32",3},{"__ushr32",3},{"__sshr32",3},
            {"__ucmp64",0},{"__scmp64",0},
            {"__shl64",0x000f},{"__ushr64",0x000f},{"__sshr64",0x000f},
            {"__mul64",0x0fff,"__mul64_soft"},
            {"__uquot64",0x1f0f,"__udiv64_soft"},{"__umod64",0x1f0f,"__umod64_soft"},
            {"__sdiv64",0x1fff,"__sdiv64_soft"},{"__smod64",0x1fff,"__smod64_soft"},
            {"__dcmp",0},{"__dcmp_signal",0},{"__dneg",0x0008},
            {"__dadd",0x3fff},{"__dsub",0x3fff},{"__dmul",0x1fff,"__dmul_soft"},{"__ddiv",0x7fff,"__ddiv_soft"},
            {"__fext32_64",0x01ff},{"__ftrunc64_32",0x0ff3},
            {"__sfloat64_32",0x00ff},{"__ufloat64_32",0x00ff},
            {"__sfloat64_64",0x003f},{"__ufloat64_64",0x003f},
            {"__sfloat32_64",0x007f},{"__ufloat32_64",0x007f},
            {"__fix64_32",0x0073},{"__ufix64_32",0x0073},
            {"__fix64_64",0x001f},{"__ufix64_64",0x001f}
        };
        unsigned i;
        for(i=0;i<sizeof safe/sizeof *safe;++i)if(!strcmp(name,safe[i].name))break;
        if(i==sizeof safe/sizeof *safe)
            error_at(here(cg.parser),"interrupt handler requires unsafe arithmetic helper '%s'",name);
        cg.interrupt_scratch|=safe[i].writes;
        if(safe[i].entry)name=safe[i].entry;
    }
    unsigned i;cg.arithmetic=1;
    for(i=0;i<cg.helper_count;++i)if(!strcmp(cg.helpers[i],name))break;
    if(i==cg.helper_count)cg.helpers[cg.helper_count++]=name;
    call_entry(name);
}
static const char *code_segment(void)
{
    return cg.function&&cg.function->symbol->interrupt==INT_NMI?"NMI_USER":"CODE";
}
static void label(unsigned id){code("cg_%s_%u = *\n",cg.parser->unit,id);}
static void jump(unsigned id){code("    jmp .loword(cg_%s_%u)\n",cg.parser->unit,id);}
static void push_value(Type t){if(reg_width(t)==4)code("    phx\n");code("    pha\n");if(cg.stack_leaf)cg.stack_bias+=reg_width(t);}
static void pop_value(Type t){code("    pla\n");if(reg_width(t)==4)code("    plx\n");if(cg.stack_leaf)cg.stack_bias-=reg_width(t);}
static void cleanup(unsigned bytes,Type result)
{
    if(!bytes)return;
    if(reg_width(result)==8){
        /* Eight-byte call results already reside in scratch; stack cleanup
         * must not overwrite their low word with A. */
        if(bytes>=6)code("    tsc\n    clc\n    adc #$%04X\n    tcs\n",bytes);
        else while(bytes){code("    plx\n");bytes-=2;}
        return;
    }
    if(reg_width(result)==2){
        if(!cg.parser->no_strength_reduction&&bytes>=6)
            code("; register-preserved argument cleanup\n    tax\n    tsc\n    clc\n    adc #$%04X\n    tcs\n    txa\n",bytes);
        else while(bytes){code("    plx\n");bytes-=2;}
        return;
    }
    cg.arithmetic=1;
    code("    sta z:__arith_lhs\n    tsc\n    clc\n    adc #$%04X\n    tcs\n    lda z:__arith_lhs\n",bytes);
}
static void narrow_char(Type t)
{
    if(t.pointers||t.base!=TY_CHAR)return;
    if(t.is_bool){code("    and #$00FF\n    beq :+\n    lda #1\n:\n");return;}
    code("    and #$00FF\n");
    if(!t.is_unsigned)code("    cmp #$0080\n    bcc :+\n    ora #$FF00\n:\n");
}
static void convert_registers(Type from,Type to)
{
    unsigned a=reg_width(from),b=reg_width(to);from=value_type(from);to=value_type(to);
    if(from.pointers&&to.pointers){
        if(!far_pointer(from)&&far_pointer(to))code("    ldx #$0000\n    cmp #0\n    beq :+\n    ldx #$007E\n:\n");
        return;
    }
    if(to.pointers&&far_pointer(to)){
        if(a==2){
            code("    ldx #0\n");
            if(!from.is_unsigned&&!from.pointers)code("    cmp #$8000\n    bcc :+\n    ldx #$00FF\n:\n");
        }
        else code("    pha\n    txa\n    and #$00FF\n    tax\n    pla\n");
        return;
    }
    if((from.base==TY_FLOAT&&!from.pointers)!=(to.base==TY_FLOAT&&!to.pointers)){
        if(from.base!=TY_FLOAT&&a==2){
            if(!cg.parser->no_strength_reduction&&!from.pointers){
                helper(from.is_unsigned?"__ufloat16":"__sfloat16");
                return;
            }
            code("    ldx #0\n");
            if(!from.is_unsigned)code("    cmp #$8000\n    bcc :+\n    ldx #$FFFF\n:\n");
        }
        cg.arithmetic=1;
        code("    sta z:__arith_lhs\n    stx z:__arith_lhs+2\n");
        helper(from.base==TY_FLOAT?"__fix32":from.is_unsigned?"__ufloat32":"__sfloat32");
        if(to.base!=TY_FLOAT)narrow_char(to);
        return;
    }
    if(b==4&&a==2){
        code("    ldx #$0000\n");
        if(!from.is_unsigned&&!from.pointers)code("    cmp #$8000\n    bcc :+\n    ldx #$FFFF\n:\n");
    }
    if(!(from.base==TY_CHAR&&!from.pointers&&to.base==TY_CHAR&&!to.pointers&&
         from.is_unsigned==to.is_unsigned))narrow_char(to);
}
static int known_conversion(Expr *e,Type to)
{
    KnownValue v=e->known;
    if(!v.valid||to.pointers||to.array||reg_width(e->type)!=2)return 0;
    if(to.base==TY_CHAR)return v.min>=(to.is_unsigned||to.is_bool?0:-128)&&v.max<=(to.is_bool?1:to.is_unsigned?255:127);
    return to.base==TY_INT;
}
static int binary32_integer_literal_bits(Expr *value,Type target,uint32_t *bits)
{
    uint32_t sign=0;
    if(target.pointers||target.array||target.is_bool||
       (target.base!=TY_CHAR&&target.base!=TY_INT&&target.base!=TY_LONG)||
       value->type.pointers||value->type.base!=TY_FLOAT)return 0;
    while(value->kind==EX_UNARY&&(value->op=='+'||value->op=='-')){
        if(value->op=='-')sign^=UINT32_C(0x80000000);
        value=value->left;
    }
    return value->kind==EX_INT&&binary32_integer_bits(value->value^sign,target,bits);
}
static int fold_binary32_integer_cast(Expr *value,Type target)
{
    uint32_t bits;
    if(!binary32_integer_literal_bits(value,target,&bits))return 0;
    code("    lda #$%04X\n",bits&0xffffu);
    if(reg_width(target)==4)code("    ldx #$%04X\n",bits>>16);
    return 1;
}
static int emit_statements(Statement *s);
static int numeric_loop(Statement *s);
static void emit_value(Expr *e);
static int wide_compare_supported(Expr *e);
static void emit_wide_compare(Expr *e);
static int fixed_wide_compare(Expr *e,unsigned yes,unsigned no,unsigned fallthrough);
static int wide_word_zero_flags(Expr *e);
static Symbol *wide_fixed_home(Expr *e,unsigned *offset);
static int wide_scalar(Type t);
static int wide_address_safe(Expr *e);
static unsigned expression_references(Expr *e,Symbol *v);
static int wide_value_supported(Expr *e);
static int wide_mixed_narrow_supported(Expr *e);
static void emit_wide_operand(Expr *e);
static int wide_narrow_supported(Expr *e);
static int wide_pointer_supported(Expr *e);
static int wide_address_expression_supported(Expr *e);
static int wide_lvalue_address_supported(Expr *e);
static int wide_discard_supported(Expr *e);
static int narrow_wide_compound_supported(Expr *e);
static void emit_narrow_wide_compound(Expr *e);
static void emit_narrow_wide_operation_loaded(Expr *e);
static void emit_wide_narrow(Expr *e);
static int address_bank_byte(Expr *e,int emit);
static int body_equal(Expr *a,Expr *b);
static int body_effect(Expr *e);
static int compare_memory_operand(Expr *e,int emit);
static void emit_value_x(Expr *e);
static int strength_pointer(Expr *e,int in_x);
static InductionCursor *strength_pointer_plan(Expr *e,unsigned *delta);
static int strength_wram_pointer(Expr *e);
/* Named object fields and constant elements of declared arrays have fixed
 * addresses. Their bases cannot be changed by evaluating the RHS. */
static Symbol *near_object_address(Expr *e,unsigned *offset);
static Symbol *fixed_memory_object(Expr *e,unsigned *offset)
{
    Expr *address,*base,*index;Symbol *s;int64_t n;unsigned base_offset=0,stride,extent;
    if(e->kind==EX_MEMBER&&e->op=='.'){
        s=e->left->kind==EX_OBJECT?e->left->symbol:fixed_memory_object(e->left,&base_offset);
        if(s){*offset=base_offset+e->value;return s;}
        return NULL;
    }
    if(e->kind==EX_MEMBER&&e->op==TOK_ARROW&&!cg.parser->no_strength_reduction&&
       !far_pointer(value_type(e->left->type))){
        s=near_object_address(e->left,&base_offset);
        if(!s||base_offset+e->value>width(s->type)||
           (!e->type.array&&base_offset+e->value+width(e->type)>width(s->type)))return NULL;
        *offset=base_offset+e->value;
        return s;
    }
    if(e->kind!=EX_DEREF)return NULL;
    address=e->left;
    if(!cg.parser->no_strength_reduction&&address->kind!=EX_BINARY){
        base=address;
        while(base->kind==EX_CAST&&value_type(base->type).pointers&&
              !far_pointer(value_type(base->type))&&value_type(base->left->type).pointers&&
              !far_pointer(value_type(base->left->type)))base=base->left;
        if(base->kind==EX_OBJECT&&base->type.array&&!base->type.banked&&
           width(e->type)<=width(base->symbol->type)){
            *offset=0;return base->symbol;
        }
        if(base->kind==EX_ADDRESS&&!far_pointer(base->type)&&base->left->kind==EX_OBJECT&&
           !base->left->symbol->function&&width(e->type)<=width(base->left->type)){
            *offset=0;return base->left->symbol;
        }
    }
    if(address->kind!=EX_BINARY||address->op!='+')return NULL;
    base=address->left;
    while(base->kind==EX_CAST&&value_type(base->type).pointers&&
          !far_pointer(value_type(base->type))&&value_type(base->left->type).pointers&&
          !far_pointer(value_type(base->left->type)))base=base->left;
    index=address->right;
    if(index->kind!=EX_INT||index->type.pointers||index->type.base==TY_FLOAT)return NULL;
    if(!cg.parser->no_strength_reduction&&base->kind==EX_ADDRESS&&!far_pointer(base->type)&&
       base->left->kind==EX_OBJECT&&!base->left->symbol->function){
        base=base->left;s=base->symbol;
    }else if(!base->type.array)return NULL;
    else if(base->kind==EX_OBJECT&&base->symbol->type.array)s=base->symbol;
    else if((base->kind==EX_DEREF||base->kind==EX_MEMBER)&&!cg.parser->no_strength_reduction)
        s=fixed_memory_object(base,&base_offset);
    else return NULL;
    if(!s)return NULL;
    n=index->type.is_unsigned?(int64_t)index->value:reg_width(index->type)==4?(int32_t)index->value:(int16_t)index->value;
    stride=width(pointed_type(value_type(address->left->type)));
    extent=width(base->type);
    /* A trailing array may have extra storage in the actual backing object */
    if(base->kind==EX_MEMBER&&base_offset<=width(s->type))extent=width(s->type)-base_offset;
    if(n<0||n*stride+width(e->type)>extent)return NULL;
    *offset=base_offset+(unsigned)n*stride;
    return s;
}
static Symbol *direct_memory_object(Expr *e,unsigned *offset)
{
    *offset=0;
    return e->kind==EX_OBJECT?e->symbol:fixed_memory_object(e,offset);
}
static Symbol *near_object_address(Expr *e,unsigned *offset)
{
    Symbol *s=NULL;Expr *target=NULL;*offset=0;
    while(e->kind==EX_CAST&&value_type(e->type).pointers&&!far_pointer(value_type(e->type))&&
          value_type(e->left->type).pointers&&!far_pointer(value_type(e->left->type)))e=e->left;
    if(e->kind==EX_ADDRESS&&e->left->kind==EX_DEREF&&
       e->left->left->kind==EX_BINARY&&e->left->left->op=='+'){
        target=e->left;e=target->left;
    }
    if(e->kind==EX_BINARY&&e->op=='+'){
        Expr *base=e->left;
        uint32_t n;
        while(base->kind==EX_CAST&&value_type(base->type).pointers&&
              !far_pointer(value_type(base->type))&&value_type(base->left->type).pointers&&
              !far_pointer(value_type(base->left->type)))base=base->left;
        if(base->type.array&&integer_constant(e->right,&n)){
            unsigned stride=width(pointed_type(value_type(e->left->type)));
            if(stride&&n<=width(base->type)/stride&&(s=direct_memory_object(base,offset))){
                *offset+=stride*n;
                return s&&!s->function&&!s->type.banked?s:NULL;
            }
        }
        if(!target)return NULL;
        e=target;
    }
    else if(e->kind==EX_ADDRESS)e=e->left;
    else if(!e->type.array)return NULL;
    s=e->kind==EX_OBJECT?e->symbol:fixed_memory_object(e,offset);
    return s&&!s->function&&!s->type.banked?s:NULL;
}
static int wram_near(Symbol *s)
{
    return s->wram_near&&cg.function&&!cg.function->symbol->interrupt;
}
static void array_operand(Symbol *s,unsigned offset)
{
    require_frame_home(s);
    s->used=1;
    if(s->owner&&cg.stack_leaf)code("%u,s",s->offset+offset+cg.stack_bias);
    else if(s->owner)code("%s",frame_operand(s->offset+offset));
    else if(s->dpage){code("z:_%s",s->asm_name);if(offset)code("+$%04X",offset);}
    else if(!offset&&!s->type.array&&!structure_object(s->type))code(s->type.banked&&!wram_near(s)?"f:_%s":"a:.loword(_%s)",s->asm_name);
    else code(s->type.banked&&!wram_near(s)?"f:_%s+$%04X":"a:.loword(_%s+$%04X)",s->asm_name,offset);
}
static void load_array_element(Symbol *s,unsigned offset,Type t)
{
    if(object_volatile(t)&&reg_width(t)==4){
        code("    lda ");array_operand(s,offset);code("\n");
        if(!s->owner&&(!s->type.banked||wram_near(s))){
            code("    ldx ");array_operand(s,offset+2);code("\n");
        }else{
            code("    pha\n    lda ");array_operand(s,offset+2);code("\n    tax\n    pla\n");
        }
        return;
    }
    if(reg_width(t)==4){
        if(!s->owner&&(!s->type.banked||wram_near(s))){
            code("    ldx ");array_operand(s,offset+2);code("\n");
        }else{
            code("    lda ");array_operand(s,offset+2);code("\n    tax\n");
        }
    }
    int byte=(s->wram||object_volatile(t))&&width(t)==1;
    if(byte)code("    sep #$20\n.a8\n");
    code("    lda ");array_operand(s,offset);code("\n");
    if(byte)code("    rep #$20\n.a16\n");
    narrow_char(t);
}
static void store_array_element(Symbol *s,unsigned offset,Type t)
{
    if(width(t)==1)code("    sep #$20\n.a8\n");
    code("    sta ");array_operand(s,offset);code("\n");
    if(width(t)==1)code("    rep #$20\n.a16\n");
    if(reg_width(t)==4){
        if((object_volatile(t)&&!s->owner&&!s->type.banked)||wram_near(s)){
            code("    stx ");array_operand(s,offset+2);code("\n");
        }else{
            code("    pha\n    txa\n    sta ");array_operand(s,offset+2);code("\n    pla\n");
        }
    }
}
/* Collapse dotted nesting to one displacement. Arrow bases are evaluated as
 * pointer values; other roots supply an object address. Neither is re-evaluated. */
static Expr *member_root(Expr *e,unsigned *offset,int *pointer)
{
    *offset=0;*pointer=0;
    for(;;){
        if(e->kind==EX_MEMBER){
            *offset+=e->value;
            if(e->op==TOK_ARROW){*pointer=1;return e->left;}
            e=e->left;
        }else if(e->kind==EX_DEREF&&e->left->kind==EX_BINARY&&e->left->op=='+'&&
                 e->left->left->kind==EX_MEMBER&&e->left->left->type.array&&
                 e->left->right->kind==EX_INT&&e->left->right->value<e->left->left->type.array){
            /* A constant element of an embedded array is part of the
             * enclosing object, so its field displacement can stay intact. */
            *offset+=e->left->right->value*width(e->type);
            e=e->left->left;
        }else return e;
    }
}
enum { CALL_LOW_BYTE=2 };
static void emit_call(Expr *e,int needed);
static void emit_discarded(Expr *e);
static void emit_address(Expr *e)
{
    if(e->kind==EX_CALL&&structure_object(e->type)){emit_call(e,1);return;}
    if(e->kind==EX_ASSIGN&&structure_object(e->type)){emit_value(e);return;}
    if(e->kind==EX_COMMA&&structure_object(e->type)){
        emit_discarded(e->left);emit_address(e->right);return;
    }
    if(e->kind==EX_OBJECT){
        Symbol *s=e->symbol;s->used=1;
        if(s->function){
            const char *prefix=wide_scalar(value_type(s->type))?"__fnptr64_":"__fnptr_";
            s->adapter_used=1;
            code("    lda #.loword(%s%s)\n    ldx #.bankbyte(%s%s)\n",prefix,s->asm_name,prefix,s->asm_name);
            return;
        }
        if(s->owner){if(cg.dp_homes)cg.dp_failed=1;code("    tya\n    clc\n    adc #$%04X\n",frame_offset(s->offset));}
        else {code("    lda #.loword(_%s)\n",s->asm_name);if(s->type.banked)code("    ldx #.bankbyte(_%s)\n",s->asm_name);}
    }else if(e->kind==EX_DEREF)emit_value(e->left);
    else if(e->kind==EX_MEMBER){
        unsigned offset;Symbol *s=fixed_memory_object(e,&offset);
        if(s&&s->wram){
            s->used=1;
            code("    lda #.loword(_%s+$%X)\n    ldx #.bankbyte(_%s+$%X)\n",s->asm_name,offset,s->asm_name,offset);
            return;
        }
        if(s&&!s->type.banked&&!s->owner){
            s->used=1;
            code("    lda #.loword(_%s+$%04X)\n",s->asm_name,offset);
            return;
        }
        int pointer;Expr *root=member_root(e,&offset,&pointer);
        if(pointer)emit_value(root);else emit_address(root);
        if(offset){
            code("    clc\n    adc #$%04X\n",offset&65535);
            if(e->type.banked){
                if(offset<=65535)code("    pha\n    txa\n    adc #0\n    and #$00FF\n    tax\n    pla\n");
                else code("    pha\n    txa\n    adc #$%04X\n    and #$00FF\n    tax\n    pla\n",offset>>16);
            }
        }
    }else error_at(e->location,"expression has no address");
}
static void frame_address_x(unsigned offset)
{
    unsigned i;if(cg.dp_homes)cg.dp_failed=1;
    offset=frame_offset(offset);
    /* TYX and each INX cost two CPU cycles. Up to three increments beat
     * TYA/CLC/ADC #word/TAX (nine cycles); larger offsets use the add. */
    if(offset<=3){code("    tyx\n");for(i=0;i<offset;++i)code("    inx\n");}
    else code("    tya\n    clc\n    adc #$%04X\n    tax\n",offset);
}
static void emit_address_x(Expr *e)
{
    if((e->kind==EX_ASSIGN||e->kind==EX_CALL||e->kind==EX_COMMA)&&structure_object(e->type)){emit_address(e);code("    tax\n");}
    else if(e->kind==EX_OBJECT){
        Symbol *s=e->symbol;s->used=1;
        if(s->owner)frame_address_x(s->offset);
        else code("    ldx #.loword(_%s)\n",s->asm_name);
    }else if(e->kind==EX_DEREF)emit_value_x(e->left);
    else if(e->kind==EX_MEMBER){
        unsigned offset;Symbol *s=fixed_memory_object(e,&offset);
        if(s){
            s->used=1;
            if(s->owner)frame_address_x(s->offset+offset);
            else code("    ldx #.loword(_%s+$%04X)\n",s->asm_name,offset);
        }else{emit_address(e);code("    tax\n");}
    }else error_at(e->location,"expression has no address");
}
static Expr *near_displaced_deref(Expr *e,unsigned *offset)
{
    uint32_t bits;unsigned scale,limit;int64_t index;Expr *addr,*base;
    if(!e||e->kind!=EX_DEREF||e->type.array||function_type(e->type)||structure_object(e->type))return NULL;
    addr=e->left;
    if(addr->kind!=EX_BINARY||addr->op!='+'||!value_type(addr->left->type).pointers||
       far_pointer(value_type(addr->left->type))||!integer_constant(addr->right,&bits)||
       value_width(addr->right->type)!=2)return NULL;
    scale=width(pointed_type(value_type(addr->left->type)));
    limit=reg_width(e->type)==4?65533u:65535u;
    index=addr->right->type.is_unsigned?(int64_t)(uint16_t)bits:(int64_t)(int16_t)bits;
    if(!scale||index<=0||index>(int64_t)(limit/scale))return NULL;
    base=addr->left;
    while(base->kind==EX_CAST&&value_type(base->type).pointers&&!far_pointer(value_type(base->type))&&
          value_type(base->left->type).pointers&&!far_pointer(value_type(base->left->type)))
        base=base->left;
    if(base->kind!=EX_OBJECT||base->type.array||!base->symbol->near_nowrap)return NULL;
    *offset=(unsigned)index*scale;
    return base;
}
static unsigned member_base_x(Expr *e)
{
    unsigned offset;int pointer;Expr *root=member_root(e,&offset,&pointer);
    if(pointer)emit_value_x(root);else emit_address_x(root);
    return offset;
}
static int direct_operand(Expr *e,Type target,unsigned high,int emit);
static unsigned frame_byte_index_x(Expr *lhs)
{
    Expr *addr,*base,*index;
    uint32_t constant;
    if(cg.parser->no_indexed_operands||cg.parser->no_strength_reduction||
       cg.stack_leaf||cg.retained_y||cg.numeric_recurrence||
       lhs->kind!=EX_DEREF||volatile_expression(lhs)||width(lhs->type)!=1)return 0;
    addr=lhs->left;
    if(addr->kind!=EX_BINARY||addr->op!='+')return 0;
    base=addr->left;index=addr->right;
    if(base->kind!=EX_OBJECT||!base->symbol->owner||!base->type.array||base->type.banked||
       width(pointed_type(value_type(base->type)))!=1||index->type.base!=TY_INT||
       index->type.pointers||integer_constant(index,&constant)||
       !direct_operand(index,type(TY_INT,0),0,0))return 0;
    if(cg.dp_homes)cg.dp_failed=1;
    base->symbol->used=1;
    /* A valid subscript of a stack array stays in the near bank. Keep the
     * array's fixed frame displacement in the final indexed access. */
    code("    tya\n    clc\n    adc ");direct_operand(index,type(TY_INT,0),0,1);
    code("\n    tax\n");return frame_offset(base->symbol->offset);
}
static unsigned assign_base_x(Expr *lhs)
{
    unsigned offset=0;Expr *displaced;
    if(lhs->kind==EX_MEMBER)return member_base_x(lhs);
    if((displaced=near_displaced_deref(lhs,&offset))){emit_value_x(displaced);return offset;}
    if((offset=frame_byte_index_x(lhs))!=0)return offset;
    emit_address_x(lhs);return 0;
}
static int indirect_near_long(Expr *e)
{
    unsigned offset;
    return (e->kind==EX_MEMBER||e->kind==EX_DEREF)&&e->type.base==TY_LONG&&
        !e->type.pointers&&!e->type.banked&&!direct_memory_object(e,&offset);
}
static void load_indirect_at(Type t,int wram,unsigned offset)
{
    if(object_volatile(t)&&reg_width(t)==4)code("    lda %s:$%04X,x\n    pha\n    lda %s:$%04X,x\n    tax\n    pla\n",wram?"z":"a",offset,wram?"z":"a",offset+2);
    else if(reg_width(t)==4)code("    lda %s:$%04X,x\n    pha\n    lda %s:$%04X,x\n    plx\n",wram?"z":"a",offset+2,wram?"z":"a",offset);
    else{
        if(object_volatile(t)&&width(t)==1)code("    sep #$20\n.a8\n");
        code("    lda %s:$%04X,x\n",wram?"z":"a",offset);
        if(object_volatile(t)&&width(t)==1)code("    rep #$20\n.a16\n");
        narrow_char(t);
    }
}
static void load_indirect(Type t,int wram){load_indirect_at(t,wram,0);}
static int full_accumulator_flags(const char *line,size_t length)
{
    if(length>=8&&(!strncmp(line,"    lda ",8)||!strncmp(line,"    and ",8)||
       !strncmp(line,"    ora ",8)||!strncmp(line,"    eor ",8)||
       !strncmp(line,"    adc ",8)||!strncmp(line,"    sbc ",8)))return 1;
    if(length==7&&(!strncmp(line,"    pla",7)||!strncmp(line,"    txa",7)||!strncmp(line,"    tya",7)))return 1;
    return length==9&&(!strncmp(line,"    inc a",9)||!strncmp(line,"    dec a",9)||
        !strncmp(line,"    asl a",9)||!strncmp(line,"    lsr a",9)||!strncmp(line,"    ror a",9));
}
static size_t previous_instruction(size_t end,size_t *length)
{
    while(end){
        size_t start,limit=end;if(cg.assembly[limit-1]=='\n')--limit;
        start=limit;while(start&&cg.assembly[start-1]!='\n')--start;
        if(start==limit||cg.assembly[start]==';'){end=start;continue;}
        *length=limit-start;return start;
    }
    *length=0;return 0;
}
static int frame_value_in_a(Symbol *s)
{
    char store[48];size_t start,length;int n;
    if(object_volatile(s->type)||!s->owner||s->type.array||width(s->type)!=2||cg.stack_leaf)return 0;
    n=snprintf(store,sizeof store,"    sta %s",frame_operand(s->offset));
    start=previous_instruction(cg.length,&length);
    /* PHA changes S, but preserves A/N/Z and every Y-relative frame home */
    while(length==7&&!strncmp(cg.assembly+start,"    pha",7))start=previous_instruction(start,&length);
    if(length==(size_t)n&&!strncmp(cg.assembly+start,"    lda ",8)&&
       !strncmp(cg.assembly+start+8,store+8,length-8))return 1;
    if(length!=(size_t)n||strncmp(cg.assembly+start,store,length))return 0;
    /* STA preserves A and flags. Require its producer's full-word N/Z so
     * omitting LDA also preserves flags; labels and mode changes are barriers. */
    start=previous_instruction(start,&length);
    return full_accumulator_flags(cg.assembly+start,length);
}
static void load_symbol(Symbol *s)
{
    if(s->wram&&!s->type.array){load_array_element(s,0,s->type);return;}
    s->used=1;
    if(s==cg.scan_cursor){code("    txa\n");return;}
    if(s==cg.retained_index&&(cg.retained_y==4||(cg.retained_y==5&&cg.retained_ptr)))cg.retained_failed=1;
    if(cg.retained_y&&((s==cg.retained_index&&cg.retained_y==1)||s==cg.retained_second)){
        unsigned scale=s==cg.retained_second?cg.retained_second_scale:1;
        code("; retained counter begin\n    tya\n");while(scale>1){code("    lsr a\n");scale>>=1;}code("; retained counter end\n");return;
    }
    if(s==cg.numeric_index){code("    txa\n    inc a\n");return;}
    if(s==cg.numeric_recurrence){code("    tya\n");return;}
    if(s==cg.scalar_first){code("    txa\n");narrow_char(s->type);return;}
    if(s==cg.leaf_count){code("    lda z:__arith_rhs\n");return;}
    if(object_volatile(s->type)&&!s->type.array){load_array_element(s,0,s->type);return;}
    if(frame_value_in_a(s))return;
    if(s->type.array){Expr e={0};e.kind=EX_OBJECT;e.symbol=s;emit_address(&e);return;}
    if(s->owner){
        if(reg_width(s->type)==4){code("    lda ");array_operand(s,2);code("\n    tax\n");}
        code("    lda ");array_operand(s,0);code("\n");
    }else{
        if(reg_width(s->type)==4){
            if(s->type.banked){code("    lda ");array_operand(s,2);code("\n    tax\n");}
            else code("    ldx %s:_%s+2\n",s->dpage?"z":"a",s->asm_name);
        }
        code("    lda ");array_operand(s,0);code("\n");
    }
    /* If a local Boolean or Boolean parameter never escapes, its low byte is
     * already 0 or 1. Clear only the high byte after loading the word. */
    if(!cg.parser->no_strength_reduction&&s->type.is_bool&&s->owner&&
       !loop_escapes(cg.function->body,s))code("    and #$00FF\n");
    else narrow_char(s->type);
}
static void store_symbol(Symbol *s)
{
    require_frame_home(s);
    s->used=1;
    if(s->wram||object_volatile(s->type)){store_array_element(s,0,s->type);return;}
    if(s->owner){
        code("    sta %s\n",frame_operand(s->offset));
        if(reg_width(s->type)==4)code("    pha\n    txa\n    sta %s\n    pla\n",frame_operand(s->offset+2));
    }else{
        int byte=!s->type.pointers&&s->type.base==TY_CHAR;
        if(byte)code("    sep #$20\n.a8\n");
        code("    sta %s:_%s\n",s->dpage?"z":"a",s->asm_name);
        if(byte)code("    rep #$20\n.a16\n");
        if(reg_width(s->type)==4)code("    stx %s:_%s+2\n",s->dpage?"z":"a",s->asm_name);
    }
}
static void stage(unsigned right,Type t)
{
    cg.arithmetic=1;
    code("    sta z:__arith_%s\n",right?"rhs":"lhs");
    if(reg_width(t)==4)code("    stx z:__arith_%s+2\n",right?"rhs":"lhs");
}
static unsigned char byte_symbols[1024];
static int narrow_unsigned_value(Expr *e,unsigned bits)
{
    if(e->known.valid&&e->known.min>=0&&e->known.max<(int32_t)(1u<<bits))return 1;
    if(e->kind==EX_BITFIELD)return !e->op&&e->type.bit_field_width<=bits;
    if(e->kind==EX_CAST&&!e->type.pointers&&!e->type.is_bool&&e->type.base==TY_INT)
        return narrow_unsigned_value(e->left,bits);
    return 0;
}
static int unsigned_byte_value(Expr *e)
{
    if(e->type.pointers||e->type.array||e->type.base==TY_FLOAT)return 0;
    if(narrow_unsigned_value(e,8))return 1;
    if(e->type.base==TY_CHAR)return e->type.is_unsigned;
    if(e->kind==EX_INT)return e->value<=255;
    if(e->kind==EX_OBJECT&&byte_symbols[e->symbol-cg.parser->symbols])return 1;
    return e->kind==EX_CAST&&e->type.base==TY_INT&&unsigned_byte_value(e->left);
}
enum { MUL_TWO_BIT_RIGHT=4, MUL_TWO_BIT_LEFT=5, MUL_KNOWN_S8=6, MUL_INLINE_U8=7 };
static int hw_plain_global_byte(Expr *e);
static int char_typed_expr(Expr *e)
{
    while(e->kind==EX_CAST&&!e->type.pointers&&!e->type.array&&
          reg_width(e->type)>=reg_width(e->left->type))
        e=e->left;
    return !e->type.pointers&&!e->type.array&&e->type.base==TY_CHAR;
}
static int arithmetic_byte_inputs(int op,Type t,Expr *left,Expr *right)
{
    int rhs=unsigned_byte_value(right);
    if(op=='*'){
        if(!cg.parser->no_strength_reduction&&reg_width(t)==2&&!t.pointers&&t.base!=TY_FLOAT){
            if(narrow_unsigned_value(right,2))return MUL_TWO_BIT_RIGHT;
            if(narrow_unsigned_value(left,2))return MUL_TWO_BIT_LEFT;
        }
        if(unsigned_byte_value(left)){
            if(!rhs)return 2;
            if(!cg.parser->no_strength_reduction&&!cg.parser->no_body_optimizations&&
               (!cg.function||!cg.function->symbol->interrupt)&&
               reg_width(t)==2&&!t.pointers&&t.base!=TY_FLOAT&&
               (cg.loop_count>0||!hw_plain_global_byte(left)||!hw_plain_global_byte(right)))
                return MUL_INLINE_U8;
            return 1;
        }
        if(rhs)return 3;
        /* Keep signed char * signed char on __mul16 as expected by ABI/small-int tests */
        if(!cg.parser->no_strength_reduction&&!cg.parser->no_body_optimizations&&
           (!cg.function||!cg.function->symbol->interrupt)&&
           reg_width(t)==2&&!t.pointers&&t.base!=TY_FLOAT&&
           !(char_typed_expr(left)&&char_typed_expr(right))&&
           left->known.valid&&right->known.valid&&
           left->known.min>=-255&&left->known.max<=255&&
           right->known.min>=-255&&right->known.max<=255)
            return MUL_KNOWN_S8;
        return 0;
    }
    /* The unsigned divider accepts a word dividend. Signed operands
     * still need sign handling unless the dividend is nonnegative. */
    return rhs&&(t.is_unsigned||unsigned_byte_value(left)||(left->known.valid&&left->known.min>=0));
}
static void boolean_from_compare(int op)
{
    unsigned yes=++cg.label,end=++cg.label;
    switch(op){
    case TOK_EQ:code("    cmp #$0000\n    bne :+\n");jump(yes);code(":\n");break;
    case TOK_NE:code("    cmp #$0000\n    beq :+\n");jump(yes);code(":\n");break;
    case '<':code("    cmp #$FFFF\n    bne :+\n");jump(yes);code(":\n");break;
    case '>':code("    cmp #$0001\n    bne :+\n");jump(yes);code(":\n");break;
    case TOK_LE:case TOK_GE:
        code("    cmp #$0000\n    bne :+\n");jump(yes);code(":\n    cmp #$%04X\n    bne :+\n",op==TOK_LE?0xFFFF:1);jump(yes);code(":\n");break;
    }
    code("    lda #0\n");jump(end);label(yes);code("    lda #1\n");label(end);
}

static void two_bit_operand(const char *op,Expr *e,Type t,const char *slot)
{
    code("    %s ",op);
    if(e)direct_operand(e,t,0,1);
    else code("z:__arith_%s",slot);
    code("\n");
}

static void two_bit_word_product(Type t,int byte_inputs,Expr *left,Expr *right)
{
    int right_factor=byte_inputs==MUL_TWO_BIT_RIGHT;
    Expr *factor=right_factor?right:left,*word=right_factor?left:right;
    const char *factor_slot=right_factor?"rhs":"lhs",*word_slot=right_factor?"lhs":"rhs";
    /* LSR leaves factor bit 0 in carry and tests factor bit 1.
     * LDA preserves carry. Factor 3 adds the original word once more. */
    code("; two-bit word multiply\n");
    two_bit_operand("lda",factor,t,factor_slot);
    code("    lsr a\n    beq :++\n");
    two_bit_operand("lda",word,t,word_slot);
    code("    bcc :+\n    asl a\n    clc\n");
    two_bit_operand("adc",word,t,word_slot);
    code("    bra :+++\n:\n    asl a\n    bra :++\n:\n    bcc :+\n");
    two_bit_operand("lda",word,t,word_slot);
    code(":\n");
}

static void binary_loaded(int op,Type t,int byte_inputs)
{
    int floating=t.base==TY_FLOAT&&!t.pointers;unsigned w=reg_width(t);
    if(comparison(op)){
        helper(floating?(op==TOK_EQ||op==TOK_NE?"__fcmp32_equal":"__fcmp32"):w==4?((t.is_unsigned||t.pointers)?"__ucmp32":"__scmp32"):
            (t.is_unsigned||t.pointers)?"__ucmp16":"__scmp16");boolean_from_compare(op);return;
    }
    if(floating){
        helper(op=='+'?"__fadd32":op=='-'?"__fsub32":op=='*'?"__fmul32":"__fdiv32");return;
    }
    if(op=='*'){
        if(byte_inputs==MUL_TWO_BIT_RIGHT||byte_inputs==MUL_TWO_BIT_LEFT)
            two_bit_word_product(t,byte_inputs,NULL,NULL);
        else if(byte_inputs==MUL_KNOWN_S8){
            char name[132];
            zicc_smul8_name(name,sizeof name);
            cg.need_smul8=1;cg.arithmetic=1;
            call_entry(name);
        }else if(byte_inputs==MUL_INLINE_U8){
            code("    sep #$20\n.a8\n    lda z:__arith_lhs\n    sta f:$004202\n"
                 "    lda z:__arith_rhs\n    sta f:$004203\n    rep #$20\n.a16\n"
                 "    nop\n    lda f:$004216\n");
        }else helper(w==4?"__mul32":byte_inputs==1?"__mul8":byte_inputs==2?"__mul8x16":byte_inputs==3?"__mul16x8":"__mul16");
        return;
    }
    if(op=='/'||op=='%'){
        if(w==2)helper(op=='/'?(byte_inputs?"__uquot8":t.is_unsigned?"__uquot16":"__sdiv16"):
                              (byte_inputs?"__umod8":t.is_unsigned?"__umod16":"__smod16"));
        else helper(op=='/'?(t.is_unsigned?"__uquot32":"__sdiv32"):(t.is_unsigned?"__umod32":"__smod32"));return;
    }
    if(op==TOK_SHL||op==TOK_SHR){helper(op==TOK_SHL?"__shl32":t.is_unsigned?"__ushr32":"__sshr32");return;}
    code("    lda z:__arith_lhs\n");
    if(op=='+')code("    clc\n    adc z:__arith_rhs\n");
    else if(op=='-')code("    sec\n    sbc z:__arith_rhs\n");
    else code("    %s z:__arith_rhs\n",op=='&'?"and":op=='|'?"ora":"eor");
    if(w==4){
        code("    pha\n    lda z:__arith_lhs+2\n");
        code("    %s z:__arith_rhs+2\n",op=='+'?"adc":op=='-'?"sbc":op=='&'?"and":op=='|'?"ora":"eor");
        code("    tax\n    pla\n");
    }
}
static void branch(Expr *e,unsigned yes,unsigned no,unsigned fallthrough);
static int lftr_branch(Expr *e,unsigned yes,unsigned no,unsigned fallthrough);
static int word_compare_branch(Expr *e,unsigned yes,unsigned no,unsigned fallthrough);
static int word_comparison(Expr *e)
{
    Type t;
    if(e->kind!=EX_BINARY||!comparison(e->op))return 0;
    t=common_type(e->left->type,e->right->type);
    return reg_width(t)==2&&(t.pointers||t.base!=TY_FLOAT);
}
static Type binary_operands(Expr *left,Expr *right,int op)
{
    Type t;
    if(op=='-'&&value_type(left->type).pointers&&value_type(right->type).pointers)
        return type(far_pointer(common_type(left->type,right->type))?TY_LONG:TY_INT,0);
    t=op==TOK_SHL||op==TOK_SHR?promoted(left->type):common_type(left->type,right->type);
    if((op==TOK_SHL||op==TOK_SHR)&&!t.pointers&&t.base==TY_INT)t.base=TY_LONG;
    return t;
}
static int home_rhs_pure(Expr *e);
static int fixed_memory_word(Expr *e,unsigned bytes,unsigned part,int emit);
static int compare_memory_operand(Expr *e,int emit);
#include "wide.inc"
#include "word_shifts.inc"
#include "word_expr.inc"
#include "indexed_operands.inc"
/* Full addresses use the existing four-byte value ABI, with a zero pad byte */
static int far_small_displacement(Expr *base,Expr *offset,unsigned *bytes)
{
    uint32_t value;
    unsigned stride=width(pointed_type(value_type(base->type)));
    if(!stride||offset->kind!=EX_INT||!integer_constant(offset,&value)||value>65535u/stride)return 0;
    *bytes=(unsigned)value*stride;
    return 1;
}
/* Only the low word needs arithmetic on the usual no-crossing path */
static void far_offset_ax(unsigned bytes,int add)
{
    if(!bytes)return;
    code("    %s\n    %s #$%04X\n    %s :+\n    %s\n    cpx #$%04X\n    bne :+\n    ldx #$%04X\n:\n",
         add?"clc":"sec",add?"adc":"sbc",bytes,add?"bcc":"bcs",add?"inx":"dex",
         add?0x100:0xffff,add?0:0xff);
}
static void far_after_left(Expr *left,Expr *right,int op)
{
    Type t=common_type(left->type,right->type),integer=type(TY_LONG,0);
    int offset=!value_type(right->type).pointers&&!comparison(op);
    convert_registers(value_type(left->type),t);
    if(offset&&right->kind==EX_INT){
        unsigned bytes;
        if(!cg.parser->no_strength_reduction&&far_small_displacement(left,right,&bytes)){
            far_offset_ax(bytes,op=='+');return;
        }
        uint32_t displacement=right->value*width(pointed_type(t));
        if(reg_width(right->type)==2&&!right->type.is_unsigned)displacement=(uint32_t)(int16_t)right->value*width(pointed_type(t));
        code("    %s\n    %s #$%04X\n    pha\n    txa\n    %s #$%04X\n    and #$00FF\n    tax\n    pla\n",op=='+'?"clc":"sec",op=='+'?"adc":"sbc",displacement&65535,op=='+'?"adc":"sbc",(displacement>>16)&255);return;
    }
    push_value(t);emit_value(right);
    if(offset){
        unsigned scale=width(pointed_type(t)),factor=scale&(~scale+1u);
        if(scale>1&&!(scale&(scale-1))){
            unsigned count=0;while(scale>1){scale>>=1;++count;}
            convert_registers(value_type(right->type),integer);
            if(count<=4&&!cg.parser->no_strength_reduction)constant_shift32(TOK_SHL,integer,count);
            else{stage(0,integer);code("    lda #%u\n",count);stage(1,type(TY_INT,0));helper("__shl32");}
        }else if(scale>1&&!cg.parser->no_strength_reduction&&scale<=60&&factor<=8&&
                 !((scale/factor)&((scale/factor)+1u))){
            unsigned odd=scale/factor,before=0,after=0,i;
            while(odd>1){odd>>=1;++before;}
            ++before;
            for(odd=scale;!(odd&1);odd>>=1)++after;
            convert_registers(value_type(right->type),integer);
            cg.arithmetic=1;
            code("; far offset multiply by shifted difference\n"
                 "    sta z:__arith_rhs\n    stx z:__arith_rhs+2\n    stx z:__arith_lhs+2\n");
            for(i=0;i<before;++i)code("    asl a\n    rol z:__arith_lhs+2\n");
            code("    sec\n    sbc z:__arith_rhs\n    pha\n    lda z:__arith_lhs+2\n"
                 "    sbc z:__arith_rhs+2\n    sta z:__arith_lhs+2\n    pla\n");
            for(i=0;i<after;++i)code("    asl a\n    rol z:__arith_lhs+2\n");
            code("    ldx z:__arith_lhs+2\n");
        }else if(scale>1){
            convert_registers(value_type(right->type),integer);
            stage(0,integer);
            code("    lda #$%04X\n",scale&65535);
            if(scale<=65535)code("    ldx #0\n");
            else code("    ldx #$%04X\n",scale>>16);
            stage(1,integer);helper("__mul32");
        }else convert_registers(value_type(right->type),integer);
    }else convert_registers(value_type(right->type),t);
    stage(1,integer);pop_value(t);stage(0,t);binary_loaded(op,t,0);
    if(!comparison(op)&&offset)code("    pha\n    txa\n    and #$00FF\n    tax\n    pla\n");
}
static int value_x_preserves_a(Expr *e);
static int member_binary_loaded(Expr *left,Expr *right,int op)
{
    Type t=binary_operands(left,right,op);
    Expr *root;unsigned offset;int pointer;
    if(t.pointers||t.base==TY_FLOAT||reg_width(t)!=2||!basic_integer_op(op)||
       cg.parser->no_indexed_operands||cg.retained_index||
       right->kind!=EX_MEMBER||width(right->type)!=2||right->type.banked||
       volatile_expression(right))
        return 0;
    root=member_root(right,&offset,&pointer);
    if(!pointer||far_pointer(value_type(root->type)))return 0;
    if(root->kind!=EX_OBJECT&&root->kind!=EX_CAST)return 0;
    if(root->kind==EX_CAST&&root->left->kind!=EX_OBJECT)return 0;
    if(offset>65535)return 0;
    convert_registers(value_type(left->type),t);
    if(value_x_preserves_a(root)){
        emit_value_x(root);
    }else{
        push_value(type(TY_INT,0));
        emit_value_x(root);
        pop_value(type(TY_INT,0));
    }
    if(op=='+'||op=='-')code("    %s\n",op=='+'?"clc":"sec");
    code("    %s a:$%04X,x\n",op=='+'?"adc":op=='-'?"sbc":op=='&'?"and":op=='|'?"ora":"eor",offset);
    return 1;
}
static int last_use_binary_home(Expr *left,Expr *right,int op,Type t);
static int post_cursor_binary(Expr *left,Expr *right,int op,Type t);
static int near_dpage_binary(Expr *left,Expr *right,int op,Type t);
static int incoming_word_parameter(Symbol *v)
{
    if(!v->owner||v->scope)return 0;
    for(int i=0;i<2&&i<cg.function->symbol->param_count;++i)
        if(register_parameter((unsigned)i,v->type)&&v==leaf_parameter(cg.function,(unsigned)i))return 1;
    return 0;
}
static void binary_after_left(Expr *left,Expr *right,int op)
{
    Type t=binary_operands(left,right,op);Type rhs=t;
    int pointer=t.pointers!=0;
    if(far_pointer(t)){far_after_left(left,right,op);return;}
    if(power_divmod_loaded(left,right,op,t)||variable_word_shift(left,right,op))return;
    if(!cg.parser->no_strength_reduction&&pointer&&value_type(left->type).pointers&&
       width(pointed_type(value_type(left->type)))==1&&(op=='+'||op=='-')){
        Expr *index=right;
        int subtract=op=='-';
        if(index->kind==EX_UNARY&&index->op=='-'&&width(index->type)==2){
            subtract=!subtract;
            index=index->left;
        }
        if(!index->type.pointers&&!volatile_expression(index)&&width(index->type)==2&&
           index->type.base==TY_INT&&direct_operand(index,type(TY_INT,0),0,0)){
            code("    %s\n    %s ",subtract?"sec":"clc",subtract?"sbc":"adc");
            direct_operand(index,type(TY_INT,0),0,1);
            code("\n");
            return;
        }
    }
    if(op=='*'&&word_multiply_loaded(left,right,t))return;
    if(post_cursor_binary(left,right,op,t))return;
    if(near_dpage_binary(left,right,op,t))return;
    if(indexed_binary_loaded(left,right,op))return;
    if(member_binary_loaded(left,right,op))return;
    /* Read fixed volatile words in the same order and width as staging */
    if(!pointer&&t.base!=TY_FLOAT&&basic_integer_op(op)&&
       (direct_operand(right,t,0,0)||(volatile_expression(right)&&
                                     fixed_memory_word(right,reg_width(t),0,0)))){
        convert_registers(value_type(left->type),t);register_binary(op,t,right);return;
    }
    if(right->kind==EX_INT&&right->type.base!=TY_FLOAT&&!right->type.pointers){
        if(pointer&&!far_pointer(t)&&value_type(left->type).pointers&&(op=='+'||op=='-')){
            Type element=pointed_type(value_type(left->type));unsigned displacement;
            displacement=(right->value*width(element))&0xFFFF;
            code("    %s\n    %s #$%04X\n",op=='+'?"clc":"sec",op=='+'?"adc":"sbc",displacement);return;
        }
        if(!pointer&&t.base!=TY_FLOAT&&reg_width(t)==2&&(op=='+'||op=='-'||op=='&'||op=='|'||op=='^')){
            if((op=='+'||op=='-')&&(right->value&0xFFFF)==0)return;
            if(op=='+'||op=='-')code("    %s\n",op=='+'?"clc":"sec");
            code("    %s #$%04X\n",op=='+'?"adc":op=='-'?"sbc":op=='&'?"and":op=='|'?"ora":"eor",right->value&0xFFFF);return;
        }
    }
    if(!pointer&&t.base!=TY_FLOAT&&right->kind==EX_INT&&
       ((op=='*'&&right->value&&!(right->value&(right->value-1)))||op==TOK_SHL||op==TOK_SHR)){
        unsigned count=right->value,i;
        Type result=op=='*'?t:promoted(left->type);
        if(op=='*'){count=0;while((1u<<count)!=right->value&&count<31)++count;}
        if(count<width(result)*8){
            convert_registers(value_type(left->type),result);
            if(reg_width(result)==4){constant_shift32(op,result,count);return;}
            if(word_shift_loaded(left,op,result,count))return;
            for(i=0;i<count;++i){
                if(op=='*'||op==TOK_SHL)code("    asl a\n");
                else code(result.is_unsigned||(left->known.valid&&left->known.min>=0)?"    lsr a\n":"    cmp #$8000\n    ror a\n");
            }
            return;
        }
    }
    /* A simple word scalar cannot call or overwrite the saved pointer. Keep
     * the pointer in separate scratch while the bounded inline scale consumes
     * A; unlike the general recursive path this needs no stack spill. */
    if(pointer&&value_type(left->type).pointers&&(op=='+'||op=='-')&&
       right->kind==EX_OBJECT&&!right->type.pointers&&!right->type.array&&
       numeric(right->type)&&right->type.base!=TY_FLOAT&&width(right->type)==2){
        unsigned scale=width(pointed_type(value_type(left->type)));WordScale plan;
        WordScaleEmission emission={0};
        if(scale&&scale<=65535&&word_scale_plan(scale,1,&plan)){
            cg.arithmetic=1;code("; direct pointer scale: no stack staging\n    sta z:__arith_lhs\n");
            emit_value(right);
            emission.base=right;emission.type=value_type(right->type);
            emission.scratch=volatile_expression(right)||!direct_operand(right,emission.type,0,0)||
                (left->kind==EX_OBJECT&&incoming_word_parameter(left->symbol)&&incoming_word_parameter(right->symbol));
            if(emission.scratch&&word_scale_needs_base(&plan))code("    sta z:__arith_rhs\n");
            word_scale_steps(&plan,word_scale_emit,&emission);
            /* base - scaled equals base + ~scaled + 1 */
            code(op=='-'?"    eor #$FFFF\n    sec\n":"    clc\n");
            code("    adc z:__arith_lhs\n");return;
        }
    }

    /* A scalar load or literal cannot call, alter locals, or use arithmetic
     * scratch. Stage the left operand directly instead of spilling it to the
     * stack and immediately reloading it. Complex expressions retain the
     * recursive, call-safe stack path. */
    if(!pointer&&!(t.base==TY_FLOAT&&right->type.base!=TY_FLOAT)&&(right->kind==EX_INT||
       (right->kind==EX_OBJECT&&!right->type.array))){
        convert_registers(value_type(left->type),t);stage(0,t);
        emit_value(right);
        if(op==TOK_SHL||op==TOK_SHR)rhs=type(TY_INT,0);
        else convert_registers(value_type(right->type),t);
        stage(1,rhs);binary_loaded(op,t,arithmetic_byte_inputs(op,t,left,right));return;
    }
    if(last_use_binary_home(left,right,op,t))return;
    convert_registers(value_type(left->type),t);push_value(t);
    emit_value(right);
    if(pointer&&!value_type(right->type).pointers){
        Type element=pointed_type(t);unsigned scale;scale=width(element);
        if(!scale)error_at(right->location,"pointer arithmetic requires a complete object type");
        if(!(scale&(scale-1))){while(scale>1){code("    asl a\n");scale>>=1;}}
        else{
            Expr factor={0};factor.kind=EX_INT;factor.type=type(TY_INT,0);factor.value=scale;
            if(!word_multiply_loaded(right,&factor,type(TY_INT,0))){
                stage(0,type(TY_INT,0));code("    lda #$%04X\n",scale);
                stage(1,type(TY_INT,0));helper("__mul16");
            }
        }
        rhs=type(TY_INT,0);
    }else if(op==TOK_SHL||op==TOK_SHR)rhs=type(TY_INT,0);
    else convert_registers(value_type(right->type),t);
    stage(1,rhs);pop_value(t);
    if(!pointer&&t.base!=TY_FLOAT&&basic_integer_op(op))register_binary(op,t,NULL);
    else{stage(0,t);binary_loaded(op,t,arithmetic_byte_inputs(op,t,left,right));}
}
#include "divmod.inc"
/* Only reuse flags from an immediately preceding instruction known to set
 * Z from the full A result. Labels, calls, index loads and mode changes
 * deliberately stop this check. */
static int accumulator_zero_flags(void)
{
    size_t start,length;
    /* Stores preserve A and flags; labels, directives and comments-only
     * boundaries are handled by previous_instruction (labels are barriers). */
    start=previous_instruction(cg.length,&length);
    while(length>8&&(!strncmp(cg.assembly+start,"    sta ",8)||!strncmp(cg.assembly+start,"    stx ",8)||
          !strncmp(cg.assembly+start,"    sty ",8)||!strncmp(cg.assembly+start,"    stz ",8)))
        start=previous_instruction(start,&length);
    return full_accumulator_flags(cg.assembly+start,length);
}
static void truth(Expr *e)
{
    if(!cg.parser->no_strength_reduction&&e->kind==EX_BINARY&&e->op=='&'&&
       e->type.base==TY_LONG&&!e->type.pointers){
        Expr *value=e->left;
        uint32_t mask;
        if(integer_constant(e->right,&mask)||(value=e->right,integer_constant(e->left,&mask))){
            if(mask&&(!(mask>>16)||!(mask&65535))&&reg_width(value->type)==4){
                unsigned part=mask>>16?2:0;
                Expr *home=value;
                if(!part&&home->kind==EX_CAST&&home->type.base==TY_LONG&&
                   far_pointer(value_type(home->left->type)))home=home->left;
                if(!volatile_expression(home)&&fixed_memory_word(home,4,part,0)){
                    code("    lda ");fixed_memory_word(home,4,part,1);code("\n");
                }else{
                    emit_value(value);
                    if(part)code("    txa\n");
                }
                unsigned bits=(part?mask>>16:mask)&65535;
                if(bits!=65535)code("    and #$%04X\n",bits);
                else if(!accumulator_zero_flags())code("    cmp #0\n");
                return;
            }
        }
    }
    if(!cg.parser->no_strength_reduction&&e->kind==EX_OBJECT&&e->type.is_bool&&
       !e->type.pointers&&!volatile_expression(e)&&e->symbol!=cg.scalar_first&&
       e->symbol!=cg.numeric_index&&e->symbol!=cg.numeric_recurrence&&
       e->symbol!=cg.leaf_count&&e->symbol!=cg.retained_index&&e->symbol!=cg.retained_second){
        code("    lda ");array_operand(e->symbol,0);code("\n    and #$00FF\n");return;
    }
    if(!cg.parser->no_strength_reduction&&!e->type.pointers&&!volatile_expression(e)&&
       reg_width(e->type)==4&&fixed_memory_word(e,4,2,0)){
        code("    lda ");fixed_memory_word(e,4,2,1);code("\n");
        if(e->type.base==TY_FLOAT)code("    and #$7FFF\n");
        code("    ora ");fixed_memory_word(e,4,0,1);code("\n");return;
    }
    emit_value(e);
    if(reg_width(e->type)==4){
        cg.arithmetic=1;code("    sta z:__arith_lhs\n    txa\n");
        if(e->type.base==TY_FLOAT&&!e->type.pointers)code("    and #$7FFF\n");
        code("    ora z:__arith_lhs\n");
    }
    else if(!accumulator_zero_flags())code("    cmp #0\n");
}
static void flag_branch(const char *when_true,const char *when_false,unsigned yes,unsigned no,unsigned fallthrough)
{
    if(fallthrough==yes){code("    %s :+\n",when_true);jump(no);code(":\n");}
    else{code("    %s :+\n",when_false);jump(yes);code(":\n");if(fallthrough!=no)jump(no);}
}
/* Test a fixed byte without first materializing a promoted C int */
static int fixed_byte_test(Expr *e)
{
    Expr *value=e;
    IndexedOperand indexed;
    Symbol *s=NULL;
    unsigned offset=0;
    uint32_t mask=255,address=0;
    int update=0;
    if(cg.parser->no_strength_reduction)return 0;
    if(e->kind==EX_BINARY&&e->op=='&'&&e->right->kind==EX_INT){
        mask=e->right->value;value=e->left;
        if(!mask||mask>255)return 0;
    }
    while(value->kind==EX_CAST&&!value->type.pointers&&
          (value->type.base==TY_INT||value->type.base==TY_CHAR)&&
          !value->type.is_bool&&width(value->left->type)==1)value=value->left;
    if(value->type.array||value->type.pointers||width(value->type)!=1)return 0;
    if(value->kind==EX_PRE&&mask==255&&!value->type.is_bool&&!volatile_expression(value)&&
       (value->op==TOK_INC||value->op==TOK_DEC)){
        update=value->op;
        value=value->left;
    }
    s=value->kind==EX_OBJECT?value->symbol:fixed_memory_object(value,&offset);
    if(!s&&indexed_operand(value,&indexed)&&
       (!cg.retained_index||cg.retained_y==5||indexed_retained(&indexed,!update))&&(!update||indexed.reg=='x')){
        indexed_index_mode(&indexed,!update);
        code("    sep #$20\n.a8\n    %s ",update==TOK_INC?"inc":update==TOK_DEC?"dec":"lda");
        indexed_text(&indexed);code("\n");
        if(mask!=255)code("    and #$%02X\n",mask);
        code("    rep #$20\n.a16\n");
        indexed_finish(&indexed);
        if(update)divmod_written(value);
        return 1;
    }
    if(!s&&value->kind==EX_MEMBER&&!value->type.banked&&!cg.retained_index&&
       !cg.parser->no_indexed_operands){
        Expr *root;int pointer;
        root=member_root(value,&offset,&pointer);
        if(!pointer||!far_pointer(value_type(root->type))){
            offset=member_base_x(value);
            code("    sep #$20\n.a8\n    %s a:$%04X,x\n",
                 update==TOK_INC?"inc":update==TOK_DEC?"dec":"lda",offset);
            if(mask!=255)code("    and #$%02X\n",mask);
            code("    rep #$20\n.a16\n");
            if(update)divmod_written(value);
            return 1;
        }
    }
    if(update&&(!s||s->owner||s->type.banked))return 0;
    if(!s){
        if(value->kind!=EX_DEREF||value->left->kind!=EX_INT||
           !far_pointer(value_type(value->left->type)))return 0;
        address=value->left->value&0xffffffu;
    }
    code("    sep #$20\n.a8\n    %s ",update==TOK_INC?"inc":update==TOK_DEC?"dec":"lda");
    if(s)array_operand(s,offset);else code("f:$%06X",address);
    code("\n");
    if(mask!=255)code("    and #$%02X\n",mask);
    code("    rep #$20\n.a16\n");
    if(update)divmod_written(value);
    return 1;
}
static Expr *byte_zero_operand(Expr *e,int *zero)
{
    uint32_t constant;
    *zero=0;
    if(e->kind==EX_BINARY&&(e->op==TOK_EQ||e->op==TOK_NE)&&
       integer_constant(e->right,&constant)&&!constant){*zero=e->op==TOK_EQ;e=e->left;}
    while(e->kind==EX_CAST&&!e->type.pointers&&e->type.base==TY_INT&&width(e->left->type)==1)e=e->left;
    return width(e->type)==1&&!e->type.pointers&&!e->type.is_bool?e:NULL;
}
/* A guarded update of the byte just tested needs only one A8 region and
 * one address evaluation. Both exits restore the ordinary accumulator mode. */
static int branch_byte_update(Expr *e,unsigned yes,unsigned no,unsigned fallthrough)
{
    Expr *value,*update;
    Symbol *home;
    unsigned offset=0,fail;
    int zero,result_zero;
    if(cg.parser->no_strength_reduction||cg.retained_index||e->op!=TOK_LAND||volatile_expression(e))return 0;
    value=byte_zero_operand(e->left,&zero);update=byte_zero_operand(e->right,&result_zero);
    if(!value||!update||update->kind!=EX_PRE||(update->op!=TOK_INC&&update->op!=TOK_DEC)||
       !body_equal(value,update->left)||body_effect(value))return 0;
    home=value->kind==EX_OBJECT?value->symbol:fixed_memory_object(value,&offset);
    if(home){if(home->owner||home->type.banked)return 0;}
    else{
        int pointer;
        Expr *root;
        if(value->kind!=EX_MEMBER||value->type.banked||cg.parser->no_indexed_operands)return 0;
        root=member_root(value,&offset,&pointer);
        if(pointer&&far_pointer(value_type(root->type)))return 0;
        offset=member_base_x(value);
    }
    fail=++cg.label;
    code("    sep #$20\n.a8\n    lda ");
    if(home)array_operand(home,offset);else code("a:$%04X,x",offset);
    code("\n    %s :+\n",zero?"beq":"bne");jump(fail);code(":\n    %s ",update->op==TOK_INC?"inc":"dec");
    if(home)array_operand(home,offset);else code("a:$%04X,x",offset);
    code("\n    %s :+\n",result_zero?"beq":"bne");jump(fail);code(":\n    rep #$20\n.a16\n");jump(yes);
    label(fail);code(".a8\n    rep #$20\n.a16\n");
    if(no!=fallthrough)jump(no);
    divmod_written(value);
    return 1;
}
static Expr *word_bits(Expr *e)
{
    while(e&&e->kind==EX_CAST&&e->type.base==TY_INT&&e->left->type.base==TY_INT&&
          !e->type.pointers&&!e->left->type.pointers&&!e->type.is_bool&&!e->left->type.is_bool)e=e->left;
    return e;
}
static int reverse_order(int op)
{
    return op=='<'?'>':op=='>'?'<':op==TOK_LE?TOK_GE:TOK_LE;
}
static int invert_order(int op)
{
    return op=='<'?TOK_GE:op==TOK_LE?'>':op=='>'?TOK_LE:'<';
}
static int word_range_bound(Expr *e,Expr **value,int32_t *bound,int *lower,int *is_unsigned,int invert)
{
    uint32_t bits;int op;
    Type t;
    if(e->kind!=EX_BINARY||!comparison(e->op)||e->op==TOK_EQ||e->op==TOK_NE)return 0;
    t=common_type(e->left->type,e->right->type);
    if(!word_integer(t))return 0;
    op=e->op;
    if(integer_constant(e->right,&bits))*value=e->left;
    else if(integer_constant(e->left,&bits)){*value=e->right;op=reverse_order(op);}
    else return 0;
    if(invert)op=invert_order(op);
    *is_unsigned=t.is_unsigned;
    *lower=op=='>'||op==TOK_GE;
    *bound=(t.is_unsigned?(int32_t)(uint16_t)bits:(int16_t)bits)+(op=='>'||op==TOK_LE);
    return 1;
}
/* Subtracting the lower bound maps the contiguous interval to [0, span).
 * Inspect carry in the unsigned domain, including for signed inputs. */
static int known_binary_constant(Expr *e);
static int word_range_pair(Expr *left,Expr *right,int is_or,int emit)
{
    Expr *a,*b;int32_t first,last,lo,span;int lower_a,lower_b,unsigned_a,unsigned_b;
    int left_const=known_binary_constant(left),right_const=known_binary_constant(right);
    if(cg.parser->no_strength_reduction||
       (left_const&&right_const)||
       (left_const&&((left->known.min!=0)==is_or))||
       (right_const&&((right->known.min!=0)==is_or))||
       !word_range_bound(left,&a,&first,&lower_a,&unsigned_a,is_or)||
       !word_range_bound(right,&b,&last,&lower_b,&unsigned_b,is_or)||
       lower_a==lower_b||unsigned_a!=unsigned_b||body_effect(a)||
       !body_equal(a,b))return 0;
    lo=lower_a?first:last;
    span=(lower_a?last:first)-lo;
    if(span<=0||span>=65536)return 0;
    if(!emit)return 1;
    code("; contiguous word range\n");
    emit_value(a);
    if(lo)code("    sec\n    sbc #$%04X\n",(unsigned)lo&65535);
    code("    cmp #$%04X\n",(unsigned)span);
    return 1;
}
static int word_range_flags(Expr *e)
{
    if(e->op!=TOK_LAND&&e->op!=TOK_LOR)return 0;
    return word_range_pair(e->left,e->right,e->op==TOK_LOR,1);
}
static int checked_word_operand(Expr *e,const char *op,int emit)
{
    uint32_t value;
    if(integer_constant(e,&value)){
        if(emit)code("    %s #$%04X\n",op,value&65535);
        return 1;
    }
    if(!compare_memory_operand(e,0))return 0;
    if(emit){code("    %s ",op);compare_memory_operand(e,1);code("\n");}
    return 1;
}
/* Use a direct accumulator chain when it can leave the checked sum in DP */
static int checked_word_chain(Expr *e,int emit)
{
    e=word_bits(e);
    if(checked_word_operand(e,"lda",emit))return 1;
    if(e->kind!=EX_BINARY||(e->op!='+'&&e->op!='-')||e->type.pointers||e->type.base!=TY_INT||
       !checked_word_operand(e->right,"",0)||!checked_word_chain(e->left,emit))return 0;
    if(emit){
        code("    %s\n",e->op=='+'?"clc":"sec");
        checked_word_operand(e->right,e->op=='+'?"adc":"sbc",1);
    }
    return 1;
}
/* An unsigned add guarded by a <= UINT_MAX-b can use the add's carry.
 * Retain short-circuit evaluation of the remaining comparison operand. */
static int branch_checked_sum(Expr *e,unsigned yes,unsigned no,unsigned fallthrough)
{
    Expr *guard=e->left,*test=e->right,*limit,*sum,*a,*b;
    Type t;
    uint32_t max;
    unsigned fail;
    if(cg.parser->no_strength_reduction||cg.retained_index||cg.scan_cursor||e->op!=TOK_LAND||
       guard->kind!=EX_BINARY||guard->op!=TOK_LE||test->kind!=EX_BINARY||test->op!='>'||
       body_effect(guard)||body_effect(test))return 0;
    t=common_type(guard->left->type,guard->right->type);
    if(t.pointers||t.base!=TY_INT||!t.is_unsigned)return 0;
    t=common_type(test->left->type,test->right->type);
    if(t.pointers||t.base!=TY_INT||!t.is_unsigned)return 0;
    limit=word_bits(guard->right);sum=word_bits(test->right);a=word_bits(guard->left);
    if(sum->kind!=EX_BINARY||sum->op!='+')return 0;
    if(limit->kind==EX_UNARY&&limit->op=='~'&&reg_width(limit->type)==2)b=word_bits(limit->left);
    else if(limit->kind==EX_BINARY&&limit->op=='^'&&reg_width(limit->type)==2&&
            integer_constant(limit->right,&max)&&(max&65535)==65535)b=word_bits(limit->left);
    else if(limit->kind==EX_BINARY&&limit->op=='-'&&reg_width(limit->type)==2&&
            integer_constant(limit->left,&max)&&(max&65535)==65535)b=word_bits(limit->right);
    else return 0;
    if(!((body_equal(a,word_bits(sum->left))&&body_equal(b,word_bits(sum->right)))||
         (body_equal(a,word_bits(sum->right))&&body_equal(b,word_bits(sum->left))))||
       !compare_memory_operand(b,0))return 0;
    fail=++cg.label;
    code("; carry-guarded word sum\n");
    emit_value(a);code("    clc\n    adc ");compare_memory_operand(b,1);code("\n");
    code("    bcc :+\n");jump(no);code(":\n");
    if(!cg.parser->no_direct_dpage&&checked_word_chain(test->left,0)){
        cg.arithmetic=1;
        code("    sta z:__arith_rhs\n");
        checked_word_chain(test->left,1);
        code("    cmp z:__arith_rhs\n    bne :+\n");jump(no);code(":\n");
        flag_branch("bcs","bcc",yes,no,fallthrough);
        cg.divmod_available=0;
        return 1;
    }
    code("    pha\n");
    if(cg.stack_leaf)cg.stack_bias+=2;
    emit_value(test->left);
    if(cg.stack_leaf)cg.stack_bias-=2;
    code("    cmp 1,s\n    beq cg_%s_%u\n    bcc cg_%s_%u\n    pla\n",cg.parser->unit,fail,cg.parser->unit,fail);
    jump(yes);label(fail);code("    pla\n");
    if(no!=fallthrough)jump(no);
    cg.divmod_available=0;
    return 1;
}
static Expr *promoted_byte_source(Expr *e)
{
    while(e&&e->kind==EX_CAST&&!e->type.pointers&&e->type.base==TY_INT&&
          !e->type.is_unsigned&&width(e->left->type)==1)e=e->left;
    return e&&e->type.base==TY_CHAR&&!e->type.pointers&&!e->type.array&&
        !e->type.is_bool&&!volatile_expression(e)?e:NULL;
}
static Symbol *rom_index_base(Expr *address,Expr **index,unsigned *scale,int64_t *offset);
/* Two short-circuited tests may share an immutable indexed ROM byte. The
 * second index is the preceding word index and retains 16-bit wrap. */
static int branch_rom_byte_predecessor(Expr *e,unsigned yes,unsigned no,unsigned fallthrough)
{
    Expr *first,*second,*a,*b,*previous,*index1=NULL,*index2=NULL,*index3=NULL,*term;
    Symbol *base1,*base2,*base3;unsigned scale1=0,scale2=0,scale3=0;
    int64_t offset1=0,offset2=0,offset3=0;uint32_t zero,one;
    if(cg.parser->no_strength_reduction||cg.parser->no_indexed_operands||
       cg.retained_index||cg.scan_cursor||e->kind!=EX_BINARY||e->op!=TOK_LAND||volatile_expression(e))return 0;
    first=e->left;second=e->right;
    if(first->kind!=EX_BINARY||first->op!=TOK_NE||!integer_constant(first->right,&zero)||zero||
       second->kind!=EX_BINARY||second->op!=TOK_NE)return 0;
    a=promoted_byte_source(first->left);b=promoted_byte_source(second->left);
    previous=promoted_byte_source(second->right);
    if(!a||!b||!previous||!object_constant(a->type)||!a->type.is_unsigned||!b->type.is_unsigned||!previous->type.is_unsigned||
       a->kind!=EX_DEREF||b->kind!=EX_DEREF||previous->kind!=EX_DEREF||!body_equal(a,b))return 0;
    base1=rom_index_base(a->left,&index1,&scale1,&offset1);
    base2=rom_index_base(b->left,&index2,&scale2,&offset2);
    base3=rom_index_base(previous->left,&index3,&scale3,&offset3);
    if(!base1||base1!=base2||base1!=base3||scale1!=1||scale2!=1||scale3!=1||
       offset1||offset2||offset3||!index1||!index2||!index3)return 0;
    term=word_bits(index1);index3=word_bits(index3);
    if(term->kind!=EX_OBJECT||term->type.pointers||width(term->type)!=2||!term->type.is_unsigned||
       !body_private(term->symbol)||index3->kind!=EX_BINARY||index3->op!='-'||!index3->type.is_unsigned||
       !body_equal(term,word_bits(index3->left))||!integer_constant(index3->right,&one)||one!=1)return 0;
    base1->used=1;
    code("; short-circuit immutable ROM bytes\n");emit_value_x(term);
    code("    lda f:_%s,x\n    and #$00FF\n    bne :+\n",base1->asm_name);
    jump(no);code(":\n    sep #$20\n.a8\n    dex\n    cmp f:_%s,x\n    rep #$20\n.a16\n",base1->asm_name);
    flag_branch("bne","beq",yes,no,fallthrough);return 1;
}

static Expr *private_pointer_definition(Expr *base)
{
    Symbol *s;
    if(base->kind!=EX_OBJECT||!base->type.pointers||far_pointer(base->type)||
       width(pointed_type(base->type))!=1)return NULL;
    s=base->symbol;
    if(!s->scope||!body_private(s)||scalar_writes(cg.function->body,s)!=1)return NULL;
    if(cg.function->body->kind!=ST_BLOCK)return NULL;
    for(Statement *entry=cg.function->body->body;entry;entry=entry->next){
        Expr *assign=entry->expression;
        if(entry->kind==ST_EXPR&&assign&&assign->kind==EX_ASSIGN&&!assign->op&&
           assign->left->kind==EX_OBJECT&&assign->left->symbol==s)return assign->right;
    }
    return NULL;
}

/* Two byte predicates on pointers with the same index can use one
 * candidate in X/Y. The second read still short-circuits on the first. */
static int branch_shared_byte_index(Expr *e,unsigned yes,unsigned no,unsigned fallthrough,Expr *result)
{
    Expr *first=e->left,*second=e->right,*a,*b,*against,*left,*right,*index,*delta,*base;
    Symbol *pointer,*array;
    uint32_t zero;
    unsigned fail,done;
    int subtract=0;
    const char *home;
    if(e->kind!=EX_BINARY||cg.parser->no_strength_reduction||cg.parser->no_indexed_operands||cg.loop_count||cg.switch_depth||
       cg.retained_index||cg.scan_cursor||e->op!=TOK_LAND||volatile_expression(e)||
       first->kind!=EX_BINARY||first->op!=TOK_EQ||second->kind!=EX_BINARY||
       second->op!=TOK_EQ||!integer_constant(second->right,&zero)||zero)return 0;
    a=promoted_byte_source(first->left);against=promoted_byte_source(first->right);
    b=promoted_byte_source(second->left);
    if(!a||!b||!against||a->type.is_unsigned!=against->type.is_unsigned||
       a->kind!=EX_DEREF||b->kind!=EX_DEREF||against->kind!=EX_OBJECT||
       a->left->kind!=EX_BINARY||b->left->kind!=EX_BINARY||
       a->left->op!='+'||b->left->op!='+'||!body_equal(a->left->right,b->left->right))return 0;
    left=private_pointer_definition(a->left->left);right=private_pointer_definition(b->left->left);
    if(!left||!right||left->kind!=EX_BINARY||right->kind!=EX_BINARY||
       left->op!='+'||right->op!='+'||!body_equal(left->right,right->right))return 0;
    index=word_bits(left->right);delta=word_bits(a->left->right);base=left->left;
    if(index->kind!=EX_OBJECT||index->symbol->scope||!body_private(index->symbol)||scalar_writes(cg.function->body,index->symbol)||
       index->type.pointers||width(index->type)!=2||base->kind!=EX_OBJECT||!base->type.pointers||
       far_pointer(base->type)||width(pointed_type(base->type))!=1||right->left->kind!=EX_OBJECT)return 0;
    pointer=base->symbol;array=right->left->symbol;
    if(!private_pointer_definition(base)||
       !array->type.array||array->owner||array->type.banked||width(pointed_type(value_type(array->type)))!=1||
       against->symbol==cg.scalar_first||against->symbol==cg.numeric_index||against->symbol==cg.numeric_recurrence)return 0;
    if(delta->kind==EX_UNARY&&delta->op=='-'){subtract=1;delta=word_bits(delta->left);}
    if(delta->kind!=EX_OBJECT||delta->type.pointers||width(delta->type)!=2||
       !body_private(delta->symbol)||!compare_memory_operand(delta,0)||
       !body_private(against->symbol)||!cg.dp_homes||!pointer->offset||!(pointer->offset&1)||
       (pointer->offset-1)/2>=cg.dp_words||!cg.dp_map[(pointer->offset-1)/2]||
       !against->symbol->offset||!(against->symbol->offset&1)||
       (against->symbol->offset-1)/2>=cg.dp_words||
       !cg.dp_map[(against->symbol->offset-1)/2])return 0;
    if(result){
        result=word_bits(result);
        if(result->kind!=EX_BINARY||result->op!=(subtract?'-':'+')||
           !body_equal(word_bits(result->left),index)||!body_equal(word_bits(result->right),delta))return 0;
    }
    /* The adjusted field pointer is already evaluated before the search.
     * Test through it first and only form the reservation index on a match.
     * Both offsets still wrap as 16-bit additions, without an indexed
     * indirect read carrying into the next bank. */
    if(result){
        Symbol *field=a->left->left->symbol;
        unsigned offset=field->offset;
        if(offset&&(offset&1)&&(offset-1)/2<cg.dp_words&&cg.dp_map[(offset-1)/2]){
            fail=++cg.label;
            code("; reuse field address before probing reservation\n");
            load_symbol(field);
            code("    %s\n    %s ",subtract?"sec":"clc",subtract?"sbc":"adc");
            compare_memory_operand(delta,1);
            code("\n    tax\n    sep #$20\n.a8\n    lda a:0,x\n    cmp ");
            array_operand(against->symbol,0);
            code("\n    rep #$20\n.a16\n    bne cg_%s_%u\n",cg.parser->unit,fail);
            /* X still holds the wrapped field address. The difference
             * from the original pointer is the wrapped candidate index. */
            array->used=pointer->used=1;
            code("    txa\n    sec\n    sbc %s\n    tax\n"
                 "    lda a:.loword(_%s),x\n    and #$00FF\n"
                 "    bne cg_%s_%u\n    txa\n    jmp .loword(return_%s)\n",
                 frame_operand(pointer->offset),array->asm_name,cg.parser->unit,fail,
                 cg.function->symbol->asm_name);
            label(fail);
            cg.divmod_available=0;
            return 1;
        }
    }
    home=frame_operand(pointer->offset);
    if(strncmp(home,"z:",2))return 0;
    pointer->used=array->used=against->symbol->used=1;
    fail=++cg.label;done=++cg.label;
    code("; shared index for ordered byte predicates\n");
    emit_value(index);
    code("    %s\n    %s ",subtract?"sec":"clc",subtract?"sbc":"adc");
    compare_memory_operand(delta,1);
    code("\n    tax\n    clc\n    adc %s\n    phy\n    tay\n    sep #$20\n.a8\n    lda a:0,y\n    cmp ",home);
    array_operand(against->symbol,0);
    code("\n    bne cg_%s_%u\n    lda a:.loword(_%s),x\n    bne cg_%s_%u\n"
         "    rep #$20\n.a16\n    ply\n",cg.parser->unit,fail,array->asm_name,cg.parser->unit,fail);
    if(result){
        code("    txa\n    jmp .loword(return_%s)\n",cg.function->symbol->asm_name);
    }else if(yes!=fallthrough)jump(yes);else jump(done);
    label(fail);code(".a8\n    rep #$20\n.a16\n    ply\n");
    if(no!=fallthrough)jump(no);
    label(done);
    return 1;
}

static Expr *single_bit_test(Expr *e,uint32_t *mask)
{
    uint32_t expected=0;
    int compared=e->kind==EX_BINARY&&e->op==TOK_EQ;
    if(compared){
        if(!integer_constant(e->right,&expected))return NULL;
        e=e->left;
    }
    if(e->kind!=EX_BINARY||e->op!='&'||!word_integer(e->type)||
       !integer_constant(e->right,mask)||!*mask||*mask>65535||(*mask&(*mask-1))||
       (compared&&expected!=*mask))return NULL;
    return e->left;
}

static int branch_word_bits(Expr *e,unsigned yes,unsigned no,unsigned fallthrough)
{
    uint32_t left_mask,right_mask;
    Expr *left,*right;
    if(cg.parser->no_value_reuse||cg.parser->no_strength_reduction||
       body_effect(e))return 0;
    left=single_bit_test(e->left,&left_mask);right=single_bit_test(e->right,&right_mask);
    if(!left||!right||!body_equal(left,right))return 0;
    emit_value(left);
    code("    and #$%04X\n",left_mask|right_mask);
    if(e->op==TOK_LAND){
        code("    cmp #$%04X\n",left_mask|right_mask);
        flag_branch("beq","bne",yes,no,fallthrough);
    }else flag_branch("bne","beq",yes,no,fallthrough);
    return 1;
}

static int known_binary_constant(Expr *e)
{
    return e->kind==EX_BINARY&&e->known.valid&&e->known.min==e->known.max&&
           (e->op=='&'||e->op=='|'||e->op=='^'||comparison(e->op))&&
           !cg.function->jump_label_count&&!find_symbol(cg.parser,"$basic_asm")&&!body_effect(e);
}

/* Equality alternatives and inequality conjunctions can compare one
 * unchanged word twice. Preserve short-circuiting for effectful reads. */
static int branch_literal_alternatives(Expr *e,unsigned yes,unsigned no,unsigned fallthrough)
{
    int equal=e->op==TOK_LOR;
    int op=equal?TOK_EQ:TOK_NE;
    Expr *a=e->left,*b=e->right;
    uint32_t first,second;
    if(cg.parser->no_strength_reduction||cg.parser->no_body_optimizations||
       a->kind!=EX_BINARY||a->op!=op||b->kind!=EX_BINARY||b->op!=op||
       !word_integer(common_type(a->left->type,a->right->type))||
       !word_integer(common_type(b->left->type,b->right->type))||
       !integer_constant(a->right,&first)||!integer_constant(b->right,&second)||
       !body_equal(a->left,b->left)||body_effect(a->left)||volatile_expression(a->left))return 0;
    unsigned next=++cg.label;
    emit_value(a->left);
    code("    cmp #$%04X\n",(unsigned)first&65535);
    flag_branch("beq","bne",equal?yes:no,next,next);
    label(next);code("    cmp #$%04X\n",(unsigned)second&65535);
    flag_branch(equal?"beq":"bne",equal?"bne":"beq",yes,no,fallthrough);
    return 1;
}
static Symbol *fixed_byte_check(Expr *e,int op,unsigned *offset,unsigned *bits)
{
    Expr *value,*literal;
    uint32_t n;
    if(e->kind!=EX_BINARY||e->op!=op||
       !word_integer(common_type(e->left->type,e->right->type)))return NULL;
    value=e->left;literal=e->right;
    if(!integer_constant(literal,&n)){value=e->right;literal=e->left;}
    if(value->kind==EX_CAST&&word_integer(value->type)&&!value->type.is_unsigned&&
       value->left->type.base==TY_CHAR)value=value->left;
    if(value->type.pointers||value->type.array||value->type.base!=TY_CHAR||value->type.is_bool||
       !integer_constant(literal,&n)||n!=initializer_cast(n,value->type))return NULL;
    *bits=n&255;
    return direct_memory_object(value,offset);
}
/* One word comparison checks both bytes. Short-circuiting may skip the
 * second C read, so only widen inside the same nonvolatile object. */
static int branch_adjacent_byte_checks(Expr *e,unsigned yes,unsigned no,unsigned fallthrough)
{
    Symbol *home;
    unsigned first,second,a,b;
    int equal=e->op==TOK_LAND;
    int op=equal?TOK_EQ:TOK_NE;
    Expr *left=e->left,*prefix=NULL;
    if(left->kind==EX_BINARY&&left->op==e->op){
        prefix=left->left;left=left->right;
    }
    if(cg.parser->no_strength_reduction||cg.parser->no_body_optimizations||
       volatile_expression(left)||volatile_expression(e->right)||
       !(home=fixed_byte_check(left,op,&first,&a))||home->type.banked||
       (home->owner&&cg.dp_homes)||home!=fixed_byte_check(e->right,op,&second,&b)||
       (first+1!=second&&second+1!=first))return 0;
    if(first>second){unsigned swap=a;a=b;b=swap;first=second;}
    if(first+2>width(home->type))return 0;
    if(prefix){
        unsigned next=++cg.label;
        branch(prefix,equal?next:yes,equal?no:next,next);
        label(next);
    }
    code("    lda ");array_operand(home,first);
    code("\n    cmp #$%04X\n",a|(b<<8));
    flag_branch(equal?"beq":"bne",equal?"bne":"beq",yes,no,fallthrough);
    return 1;
}

static int branch_long_mask(Expr *e,unsigned yes,unsigned no,unsigned fallthrough)
{
    Expr *value,*mask;
    unsigned high;
    uint32_t bits;
    if(cg.parser->no_strength_reduction||e->kind!=EX_BINARY||e->op!='&'||
       e->type.pointers||(e->type.base!=TY_LONG&&e->type.base!=TY_INT))return 0;
    value=e->left;mask=e->right;
    if(integer_constant(value,&bits)){value=e->right;mask=e->left;}
    if(value->type.pointers||value->type.base==TY_FLOAT||!integer_constant(mask,&bits))return 0;
    if(e->type.base==TY_INT){
        if((bits&0xffffu)!=0x8000u)return 0;
        if(value->type.base==TY_INT&&direct_operand(value,e->type,0,0)){
            code("    lda ");direct_operand(value,e->type,0,1);code("\n");
        }else{
            if(volatile_expression(value))return 0;
            emit_value(value);convert_registers(value->type,e->type);
            if(!accumulator_zero_flags())code("    cmp #0\n");
        }
        flag_branch("bmi","bpl",yes,no,fallthrough);
        return 1;
    }
    if(value->type.base!=TY_LONG||!bits||((bits>>16)&&(bits&0xffffu)))return 0;
    high=(bits>>16)!=0;
    if(!direct_operand(value,e->type,high,0))return 0;
    code("    lda ");direct_operand(value,e->type,high,1);code("\n");
    bits=(bits>>(16*high))&0xffffu;
    if(bits==0x8000u)flag_branch("bmi","bpl",yes,no,fallthrough);
    else{
        if(bits!=0xffffu)code("    and #$%04X\n",bits);
        flag_branch("bne","beq",yes,no,fallthrough);
    }
    return 1;
}
static void branch(Expr *e,unsigned yes,unsigned no,unsigned fallthrough)
{
    if(structure_object(value_type(e->type)))error_at(e->location,"aggregate condition requires a scalar value");
    if(e->kind==EX_INT&&e->type.base==TY_LONGLONG&&!e->type.pointers){
        unsigned target=(e->value||e->value_high)?yes:no;
        if(target!=fallthrough)jump(target);
        return;
    }
    if(wide_compare_supported(e)){
        if(fixed_wide_compare(e,yes,no,fallthrough))return;
        emit_wide_compare(e);code("    cmp #0\n");flag_branch("bne","beq",yes,no,fallthrough);return;
    }
    if(wide_scalar(value_type(e->type))&&wide_value_supported(e)){
        if(wide_word_zero_flags(e)){flag_branch("bne","beq",yes,no,fallthrough);return;}
        unsigned offset;
        Symbol *home=wide_fixed_home(e,&offset);
        if(home){
            code("    lda ");array_operand(home,offset);
            code("\n    ora ");array_operand(home,offset+2);
            code("\n    ora ");array_operand(home,offset+4);
            if(e->type.base==TY_DOUBLE){
                code("\n    tax\n    lda ");array_operand(home,offset+6);
                code("\n    and #$7FFF\n    bne :+\n    cpx #0\n:\n");
            }else{
                code("\n    ora ");array_operand(home,offset+6);code("\n");
            }
            flag_branch("bne","beq",yes,no,fallthrough);return;
        }
        emit_wide_operand(e);
        if(e->type.base==TY_DOUBLE)
            code("    lda z:__arith_lhs+6\n    and #$7FFF\n    ora z:__arith_lhs+4\n    ora z:__arith_lhs+2\n    ora z:__arith_lhs\n");
        else code("    lda z:__arith_lhs\n    ora z:__arith_lhs+2\n    ora z:__arith_lhs+4\n    ora z:__arith_lhs+6\n");
        flag_branch("bne","beq",yes,no,fallthrough);return;
    }
    if(lftr_branch(e,yes,no,fallthrough))return;
    if(e->kind==EX_COMMA){
        emit_discarded(e->left);
        branch(e->right,yes,no,fallthrough);
        return;
    }
    if(e->kind==EX_CAST&&e->type.is_bool&&!e->type.pointers){
        branch(e->left,yes,no,fallthrough);return;
    }
    if(e->kind==EX_INT){
        uint32_t value=e->value;unsigned target;
        if(e->type.base==TY_FLOAT&&!e->type.pointers)value&=0x7FFFFFFF;
        target=value?yes:no;if(target!=fallthrough)jump(target);return;
    }
    if(known_binary_constant(e)){
        unsigned target=e->known.min?yes:no;
        if(target!=fallthrough)jump(target);
        return;
    }
    if(e->kind==EX_BINARY&&(e->op==TOK_LAND||e->op==TOK_LOR)){
        if(branch_adjacent_byte_checks(e,yes,no,fallthrough))return;
        if(branch_literal_alternatives(e,yes,no,fallthrough))return;
        if(word_range_flags(e)){
            flag_branch(e->op==TOK_LOR?"bcs":"bcc",e->op==TOK_LOR?"bcc":"bcs",yes,no,fallthrough);
            return;
        }
        if(e->left->kind==EX_BINARY&&e->left->op==e->op&&
           word_range_pair(e->left->right,e->right,e->op==TOK_LOR,0)){
            unsigned middle=++cg.label;
            if(e->op==TOK_LAND)branch(e->left->left,middle,no,middle);
            else branch(e->left->left,yes,middle,middle);
            {unsigned available=cg.divmod_available;
                label(middle);
                word_range_pair(e->left->right,e->right,e->op==TOK_LOR,1);
                flag_branch(e->op==TOK_LOR?"bcs":"bcc",e->op==TOK_LOR?"bcc":"bcs",yes,no,fallthrough);
                cg.divmod_available&=available;
            }return;
        }
        if(!cg.function->uses_wide&&(branch_word_bits(e,yes,no,fallthrough)||
           branch_byte_update(e,yes,no,fallthrough)||branch_checked_sum(e,yes,no,fallthrough)||
           branch_rom_byte_predecessor(e,yes,no,fallthrough)||
           branch_shared_byte_index(e,yes,no,fallthrough,NULL)))return;
        unsigned middle=++cg.label;
        if(e->op==TOK_LAND)branch(e->left,middle,no,middle);else branch(e->left,yes,middle,middle);
        {unsigned available=cg.divmod_available;
            label(middle);branch(e->right,yes,no,fallthrough);
            cg.divmod_available&=available;
        }return;
    }
    if(e->kind==EX_UNARY&&e->op=='!'){branch(e->left,no,yes,fallthrough);return;}
    if(!cg.parser->no_strength_reduction&&e->kind==EX_CHOOSE&&
       e->right->kind==EX_INT&&e->third->kind==EX_INT&&
       !e->type.pointers&&(e->type.base==TY_CHAR||e->type.base==TY_INT)&&
       ((e->right->value==0)!=(e->third->value==0))){
        if(e->right->value)branch(e->left,yes,no,fallthrough);
        else branch(e->left,no,yes,fallthrough);
        return;
    }
    /* Integer division truncates toward zero. The quotient is zero
     * within the signed interval [1-d,d-1], or below d when unsigned.
     * Bias the signed interval into a single modulo-word comparison. */
    if(!cg.parser->no_strength_reduction&&e->kind==EX_BINARY&&e->op=='/'&&
       e->type.base==TY_INT&&!e->type.pointers&&e->right->kind==EX_INT){
        unsigned divisor=e->right->value&65535;
        if(!e->type.is_unsigned&&divisor>32767)divisor=65536-divisor;
        if(divisor>1){
            emit_value(e->left);
            convert_registers(value_type(e->left->type),e->type);
            if(!e->type.is_unsigned)
                code("    clc\n    adc #$%04X\n",divisor-1);
            code("    cmp #$%04X\n",e->type.is_unsigned?divisor:divisor*2-1);
            flag_branch("bcs","bcc",yes,no,fallthrough);return;
        }
    }
    if(fixed_byte_test(e)){flag_branch("bne","beq",yes,no,fallthrough);return;}
    if(branch_long_mask(e,yes,no,fallthrough))return;
    if(word_comparison(e)){word_compare_branch(e,yes,no,fallthrough);return;}
    if(e->kind==EX_BINARY&&comparison(e->op)){wide_compare_branch(e,yes,no,fallthrough);return;}
    truth(e);flag_branch("bne","beq",yes,no,fallthrough);
}
static void store_saved_address(Type t,int wram,unsigned offset)
{
    if(reg_width(t)==2){
        code("    plx\n");
        if(width(t)==1)code("    sep #$20\n.a8\n");
        code("    sta %s:$%04X,x\n",wram?"z":"a",offset);
        if(width(t)==1)code("    rep #$20\n.a16\n");
        return;
    }
    cg.arithmetic=1;stage(0,t);code("    pla\n    tax\n    lda z:__arith_lhs\n");
    if(width(t)==1)code("    sep #$20\n.a8\n");
    code("    sta %s:$%04X,x\n",wram?"z":"a",offset);
    if(width(t)==1)code("    rep #$20\n.a16\n");
    if(reg_width(t)==4)code("    lda z:__arith_lhs+2\n    sta %s:$%04X,x\n",wram?"z":"a",offset+2);
    code("    lda z:__arith_lhs\n");if(reg_width(t)==4)code("    ldx z:__arith_lhs+2\n");
}
static unsigned increment_step(Type t)
{
    if(t.pointers)return width(pointed_type(t));return 1;
}
static void increment_value(Type t,int op)
{
    unsigned step=increment_step(t);
    if(t.is_bool&&!t.pointers&&op==TOK_INC){code("    lda #1\n");return;}
    if(t.base==TY_FLOAT&&!t.pointers){
        stage(0,t);code("    stz z:__arith_rhs\n    lda #$3F80\n    sta z:__arith_rhs+2\n");
        helper(op==TOK_INC?"__fadd32":"__fsub32");return;
    }
    if(reg_width(t)==2&&step==1)code("    %s a\n",op==TOK_INC?"inc":"dec");
    else code("    %s\n    %s #$%04X\n",op==TOK_INC?"clc":"sec",op==TOK_INC?"adc":"sbc",step&65535);
    if(reg_width(t)==4){
        if(step<=65535)code("    pha\n    txa\n    %s #0\n",op==TOK_INC?"adc":"sbc");
        else code("    pha\n    txa\n    %s #$%04X\n",op==TOK_INC?"adc":"sbc",step>>16);
        if(far_pointer(t))code("    and #$00FF\n");code("    tax\n    pla\n");
    }
    narrow_char(t);
}
/* Keep the base of an indirect far-byte cursor in X while updating its
 * two-word home. Preserve the original pointer as the post-update result. */
static int indirect_far_post(Expr *e)
{
    Expr *home=e->left;
    unsigned offset;
    if(cg.parser->no_strength_reduction||e->kind!=EX_POST||!far_pointer(e->type)||
       increment_step(e->type)!=1||home->type.banked||volatile_expression(e)||
       (home->kind!=EX_MEMBER&&home->kind!=EX_DEREF)||direct_memory_object(home,&offset)||
       cg.retained_index||cg.retained_second||cg.scan_cursor)return 0;
    const char *mode=home->kind==EX_DEREF&&strength_wram_pointer(home->left)?"z":"a";
    emit_address_x(home);
    code("    lda %s:$0002,x\n    pha\n    lda %s:$0000,x\n",mode,mode);
    if(e->op==TOK_INC)code("    inc %s:$0000,x\n",mode);
    code("    bne :+\n    pha\n    lda %s:$0002,x\n",mode);
    code(e->op==TOK_INC?"    inc a\n":"    dec a\n");
    code("    and #$00FF\n    sta %s:$0002,x\n    pla\n:\n",mode);
    if(e->op==TOK_DEC)code("    dec %s:$0000,x\n",mode);
    code("    plx\n");
    divmod_written(home);
    return 1;
}
static int fixed_binary32_increment(Expr *e,int needed)
{
    unsigned offset;
    Symbol *home;
    if(cg.parser->no_strength_reduction||cg.stack_leaf||
       (e->kind!=EX_PRE&&e->kind!=EX_POST)||e->type.base!=TY_FLOAT||e->type.pointers||
       !(home=direct_memory_object(e->left,&offset)))return 0;
    int save_old=needed&&e->kind==EX_POST;
    load_array_element(home,offset,e->left->type);
    if(save_old)push_value(e->type);
    increment_value(e->type,e->op);
    store_array_element(home,offset,e->left->type);
    if(save_old)pop_value(e->type);
    divmod_written(e->left);
    return 1;
}
static int fixed_long_increment(Expr *e,int needed)
{
    Expr *home;
    int post,inc,compound=e->kind==EX_ASSIGN;
    uint32_t amount=1;
    unsigned done=0;
    if(cg.parser->no_strength_reduction||e->type.base!=TY_LONG||e->type.pointers||volatile_expression(e))return 0;
    if(compound){
        if((e->op!='+'&&e->op!='-')||e->right->kind!=EX_INT||reg_width(e->right->type)>4||
           !integer_constant(e->right,&amount)||!amount||
           ((amount&65535)&&(needed||amount>65535)))return 0;
    }else if(e->kind!=EX_PRE&&e->kind!=EX_POST)return 0;
    home=e->left;
    if(!fixed_memory_word(home,4,0,0))return 0;
    post=needed&&e->kind==EX_POST;
    inc=compound?e->op=='+':e->op==TOK_INC;
    if(post){
        unsigned offset;
        Symbol *s=direct_memory_object(home,&offset);
        if(s&&!s->owner&&!s->type.banked){
            /* Snapshot the original result in X:A. Absolute INC/DEC updates
             * the low word in place, touching the high word only on wrap. */
            code("    ldx ");array_operand(s,offset+2);code("\n    lda ");array_operand(s,offset);
            if(inc){
                code("\n    inc ");array_operand(s,offset);code("\n    bne :+\n    inc ");
                array_operand(s,offset+2);code("\n:\n");
            }else{
                code("\n    bne :+\n    dec ");array_operand(s,offset+2);code("\n:\n    dec ");
                array_operand(s,offset);code("\n");
            }
            code("    ora #0\n");
            divmod_written(home);return 1;
        }
    }
    if(!(amount&65535)){
        code("    lda ");fixed_memory_word(home,4,2,1);code("\n");
        code(inc?"    clc\n    adc #$%04X\n":"    sec\n    sbc #$%04X\n",amount>>16);
        code("    sta ");fixed_memory_word(home,4,2,1);code("\n");
        if(needed){code("    tax\n    lda ");fixed_memory_word(home,4,0,1);code("\n");}
        divmod_written(home);return 1;
    }
    code("    lda ");fixed_memory_word(home,4,0,1);code("\n");
    if(post){code("    pha\n");if(cg.stack_leaf)cg.stack_bias+=2;}
    if(compound)code(inc?"    clc\n    adc #$%04X\n":"    sec\n    sbc #$%04X\n",amount);
    else code(inc?"    clc\n    adc #1\n":"    sec\n    sbc #1\n");
    code("    sta ");fixed_memory_word(home,4,0,1);code("\n");
    if(compound){
        done=++cg.label;
        flag_branch(inc?"bcc":"bcs",inc?"bcs":"bcc",done,0,0);
    }
    code("    lda ");
    fixed_memory_word(home,4,2,1);code("\n");
    if(post)code("    tax\n");
    if(compound)code(inc?"    inc a\n":"    dec a\n");
    else code(inc?"    adc #0\n":"    sbc #0\n");
    code("    sta ");fixed_memory_word(home,4,2,1);code("\n");
    if(done)label(done);
    if(post){code("    pla\n");if(cg.stack_leaf)cg.stack_bias-=2;}
    else if(needed){code("    tax\n    lda ");fixed_memory_word(home,4,0,1);code("\n");}
    divmod_written(home);
    return 1;
}
static int direct_increment(Expr *e)
{
    return !volatile_expression(e)&&(e->kind==EX_POST||e->kind==EX_PRE)&&e->left->kind==EX_OBJECT&&
        !e->left->symbol->wram&&
        ((width(e->type)==2&&reg_width(e->type)==2)||
         (width(e->type)==1&&!e->type.pointers&&!e->type.is_bool&&!e->left->symbol->type.banked));
}
static int constant_address(Expr *e)
{
    return e->kind==EX_INT||e->kind==EX_STRING||(e->kind==EX_OBJECT&&function_type(e->type))||
        (e->kind==EX_ADDRESS&&e->left->kind==EX_OBJECT&&!e->left->symbol->owner);
}
static void immediate(Expr *e,unsigned high)
{
    if(e->kind==EX_INT)code("$%04X",(e->value>>(high?16:0))&0xFFFFu);
    else if(e->kind==EX_STRING){e->string->used=1;code(high?".bankbyte(str_%s_%u)":".loword(str_%s_%u)",cg.parser->unit,e->string->id);}
    else{
        Symbol *s=(e->kind==EX_OBJECT?e:e->left)->symbol;
        const char *prefix=s->function?(wide_scalar(value_type(s->type))?"__fnptr64_":"__fnptr_"):"_";
        s->used=1;if(s->function)s->adapter_used=1;
        code(high?".bankbyte(%s%s)":".loword(%s%s)",prefix,s->asm_name);
    }
}
/* Integer offsets from a function address include the carry out of the
 * address bank. Keep the function identity and unsigned byte displacement. */
static Symbol *function_address_relocation(Expr *e,uint32_t *offset)
{
    if(!e||e->type.pointers||e->type.base!=TY_LONG||!e->type.is_unsigned)return NULL;
    Expr *address=e;
    *offset=0;
    if(e->kind==EX_BINARY&&e->op=='+'){
        address=e->left;
        if(!integer_constant(e->right,offset)){
            address=e->right;
            if(!integer_constant(e->left,offset))return NULL;
        }
    }
    if(*offset>65535||address->kind!=EX_CAST||address->type.pointers||
       address->type.base!=TY_LONG||!address->type.is_unsigned)return NULL;
    address=address->left;
    if(address->kind==EX_ADDRESS)address=address->left;
    return address->kind==EX_OBJECT&&address->symbol->function?address->symbol:NULL;
}
static int function_address_sum(Expr *e)
{
    uint32_t offset;
    if(cg.parser->no_strength_reduction||e->op!='+')return 0;
    Symbol *s=function_address_relocation(e,&offset);
    if(!s)return 0;
    const char *prefix=wide_scalar(value_type(s->type))?"__fnptr64_":"__fnptr_";
    s->adapter_used=s->used=1;
    code("    ldx #.hiword(%s%s+$%X)\n    lda #.loword(%s%s+$%X)\n",
         prefix,s->asm_name,offset,prefix,s->asm_name,offset);
    return 1;
}
static int near_small_offset(Expr *e,Expr **base,int *delta)
{
    uint32_t bits;unsigned scale;int d;
    if(e->kind!=EX_BINARY||(e->op!='+'&&e->op!='-')||!value_type(e->left->type).pointers||
       far_pointer(value_type(e->left->type))||!integer_constant(e->right,&bits)||value_width(e->right->type)!=2)return 0;
    scale=width(pointed_type(value_type(e->left->type)));d=(int)(int16_t)((bits*scale)&65535);
    if(e->op=='-')d=(int)(int16_t)(0u-(unsigned)d);
    if(d<-3||d>3)return 0;*base=e->left;*delta=d;return 1;
}
/* Select X as the result register at the use site. A and flags are not outputs
 * here; callers needing the value in A continue to use emit_value. */
static void emit_value_x(Expr *e)
{
    Expr *base;int delta;
    if(affine_pointer(e,1))return;
    if(volatile_expression(e)){emit_value(e);code("    tax\n");return;}
    if(strength_pointer(e,1))return;
    if(!cg.parser->no_strength_reduction&&e->kind==EX_BINARY&&e->op=='+'&&
       value_type(e->type).pointers&&!far_pointer(value_type(e->type))){
        unsigned offset;
        Symbol *home=near_object_address(e,&offset);
        if(home&&offset&&!home->owner){
            home->used=1;
            code("    ldx #.loword(_%s+$%04X)\n",home->asm_name,offset);
            return;
        }
    }
    if(!cg.parser->no_strength_reduction&&near_small_offset(e,&base,&delta)){
        emit_value_x(base);
        while(delta>0){code("; near pointer wrap\n    inx\n");--delta;}
        while(delta<0){code("; near pointer wrap\n    dex\n");++delta;}return;
    }
    if(!cg.parser->no_strength_reduction&&e->kind==EX_POST&&e->type.pointers&&
       !far_pointer(e->type)&&increment_step(e->type)<=2){
        unsigned offset;
        Symbol *home=fixed_memory_object(e->left,&offset);
        if(home&&!home->owner&&!home->type.banked){
            unsigned steps=increment_step(e->type);
            code("    ldx ");array_operand(home,offset);code("\n    txa\n");
            while(steps--)code("    %s a\n",e->op==TOK_INC?"inc":"dec");
            store_array_element(home,offset,e->type);divmod_written(e->left);return;
        }
    }
    if(direct_increment(e)){
        load_symbol(e->left->symbol);
        if(e->kind==EX_POST)code("    tax\n");
        increment_value(e->type,e->op);store_symbol(e->left->symbol);
        if(e->kind==EX_PRE)code("    tax\n");
        divmod_written(e->left);return;
    }
    if(e->kind==EX_CAST&&value_width(e->type)==2&&value_width(e->left->type)==2){
        emit_value_x(e->left);return;
    }
    if(e->kind==EX_ADDRESS){emit_address_x(e->left);return;}
    if(e->type.banked&&width(e->type)==2){
        unsigned offset;
        Symbol *home=direct_memory_object(e,&offset);
        if(home&&wram_near(home)){code("    ldx ");array_operand(home,offset);code("\n");return;}
    }
    if(e->kind==EX_OBJECT){
        Symbol *s=e->symbol;s->used=1;
        if(s==cg.scan_cursor)return;
        if(s->type.array){emit_address_x(e);return;}
        if(width(s->type)==2&&!s->type.banked){
            if(s->owner&&(cg.stack_leaf||(s==cg.retained_index&&(cg.retained_y==1||cg.retained_y==2))||s==cg.retained_second)){emit_value(e);code("    tax\n");return;}
            if(s->owner){
                char store[48];size_t start,length;int n;
                n=snprintf(store,sizeof store,"    sta %s",frame_operand(s->offset));
                start=previous_instruction(cg.length,&length);
                if(length==(size_t)n&&!strncmp(cg.assembly+start,store,length)){
                    code("    tax\n");return;
                }
                code("    ldx %s\n",frame_operand(s->offset));
            }
            else code("    ldx %s:_%s\n",s->dpage?"z":"a",s->asm_name);
            return;
        }
    }
    if(reg_width(e->type)==2&&constant_address(e)){
        code("    ldx #");immediate(e,0);code("\n");return;
    }
    emit_value(e);code("    tax\n");
}
static int fixed_memory_word(Expr *e,unsigned bytes,unsigned part,int emit)
{
    Symbol *s;unsigned offset;
    e=word_bits(e);
    /* Arrays decay to addresses, and banked values need long reads */
    if(e->type.array||e->type.banked||reg_width(e->type)!=bytes||width(value_type(e->type))!=bytes)return 0;
    if(e->kind==EX_OBJECT&&!e->type.array){
        s=e->symbol;
        if(s==cg.scalar_first||s==cg.numeric_index||s==cg.numeric_recurrence||(s==cg.retained_index&&(cg.retained_y==1||cg.retained_y==2)))return 0;
        if(emit)array_operand(s,part);
        return 1;
    }
    s=fixed_memory_object(e,&offset);
    if(s){if(emit)array_operand(s,offset+part);return 1;}
    return 0;
}
static int compare_memory_operand(Expr *e,int emit)
{
    return fixed_memory_word(e,2,0,emit);
}
static void integer_relation_flags(int op,int signed_order,unsigned yes,unsigned no,unsigned fallthrough)
{
    int less=op=='<'||op==TOK_LE;
    const char *lower=signed_order?"bmi":"bcc";
    const char *higher=signed_order?"bpl":"bcs";
    flag_branch(less?lower:higher,less?higher:lower,yes,no,fallthrough);
}
/* Equality of equally signed byte values needs only their low bytes. The
 * usual signed-int promotion preserves that equality; mixed signedness and
 * other conversions retain full-word comparison. Never widen/narrow volatile
 * accesses or evaluate an arbitrary expression in byte accumulator mode. */
static Expr *comparison_byte(Expr *e,int *is_unsigned)
{
    Symbol *home;unsigned offset;
    while(e->kind==EX_CAST&&e->type.base==TY_INT&&!e->type.pointers&&!e->type.is_unsigned&&
          e->left->type.base==TY_CHAR&&!e->left->type.pointers)e=e->left;
    if(e->type.pointers||e->type.array)return NULL;
    if(volatile_expression(e)&&(e->type.base!=TY_CHAR||e->type.is_bool||
       (e->kind!=EX_OBJECT&&e->kind!=EX_MEMBER&&e->kind!=EX_DEREF)))return NULL;
    if(e->type.base!=TY_CHAR&&!unsigned_byte_value(e))return NULL;
    *is_unsigned=e->type.base==TY_CHAR?e->type.is_unsigned:1;
    while(e->kind==EX_CAST&&!e->left->type.pointers&&reg_width(e->left->type)==2&&
          (e->left->type.base==TY_CHAR||e->left->type.base==TY_INT))e=e->left;
    if(e->kind==EX_OBJECT&&e->symbol==cg.retained_index&&(cg.retained_y==1||cg.retained_y==2))return NULL;
    if(e->kind==EX_OBJECT||e->kind==EX_INT)return e;
    home=fixed_memory_object(e,&offset);
    return home&&!home->type.banked?e:NULL;
}
static int byte_equal_branch(Expr *e,unsigned yes,unsigned no,unsigned fallthrough)
{
    Expr *left,*right,*computed=NULL;
    int a,b,ordered=e->op!=TOK_EQ&&e->op!=TOK_NE;
    int exact_byte=volatile_expression(e),strict,signed_order,subtract;
    if(ordered&&(cg.parser->no_strength_reduction||cg.parser->no_body_optimizations))return 0;
    /* Bounded promoted values can use A16 CMP without an A8 region */
    if(ordered&&e->left->known.valid&&e->right->known.valid&&e->left->known.min>=0&&
       e->right->known.min>=0&&e->left->known.max<255&&e->right->known.max<=255)return 0;
    /* For immediate equality, word loading/narrowing costs less than two
     * accumulator-width switches. Proven word-byte homes need no narrowing. */
    if(!ordered&&e->right->kind==EX_INT)return 0;
    left=comparison_byte(e->left,&a);right=comparison_byte(e->right,&b);
    if(!ordered&&!exact_byte&&!cg.parser->no_strength_reduction){
        if(left&&a&&!right&&!compare_memory_operand(e->left,0)&&
           unsigned_byte_value(e->right)&&!body_effect(e->right)){
            computed=e->right;right=left;b=a;
        }else if(right&&b&&!left&&!compare_memory_operand(e->right,0)&&
                 unsigned_byte_value(e->left)&&!body_effect(e->left)){
            computed=e->left;a=b;
        }
    }
    if((!left&&!computed)||!right||a!=b||(ordered&&!a&&!exact_byte)||
       (right->kind==EX_OBJECT&&right->symbol==cg.scalar_first))return 0;
    signed_order=ordered&&!a;
    strict=e->op=='>'||e->op==TOK_LE;
    unsigned cmp_val=right->kind==EX_INT?(right->value&255u):0u;
    int cmp_op=e->op;
    if(ordered&&a&&!exact_byte&&right->kind==EX_INT&&strict&&cmp_val<255u){
        ++cmp_val;strict=0;cmp_op=e->op==TOK_LE?'<':TOK_GE;
    }
    subtract=exact_byte&&(signed_order||strict);
    if(ordered&&a&&!exact_byte)code("; unsigned byte relation\n");
    if(computed)emit_value(computed);
    code("    sep #$20\n.a8\n");
    if(!computed){
        if(left->kind==EX_INT)code("    lda #$%02X\n",left->value&255);
        else if(left->kind==EX_OBJECT&&left->symbol==cg.scalar_first)code("    txa\n");
        else{unsigned offset=0;Symbol *home=left->kind==EX_OBJECT?left->symbol:fixed_memory_object(left,&offset);
            code("    lda ");array_operand(home,offset);code("\n");}
    }
    if(subtract)code(strict?"    clc\n    sbc ":"    sec\n    sbc ");
    else code("    cmp ");
    if(right->kind==EX_INT)code("#$%02X",cmp_val);
    else{unsigned offset=0;Symbol *home=right->kind==EX_OBJECT?right->symbol:fixed_memory_object(right,&offset);array_operand(home,offset);}
    code("\n");
    if(signed_order)code("    bvc :+\n    eor #$80\n:\n");
    code("    rep #$20\n.a16\n");
    if(!ordered)flag_branch(e->op==TOK_EQ?"beq":"bne",e->op==TOK_EQ?"bne":"beq",yes,no,fallthrough);
    else{
        if(strict&&!subtract){code("    bne :+\n");jump(cmp_op==TOK_LE?yes:no);code(":\n");}
        integer_relation_flags(cmp_op,signed_order,yes,no,fallthrough);
    }
    return 1;
}

typedef struct {
    Expr *value;
    IndexedOperand indexed;
    unsigned high;
    int index;
} ByteComparison;

static int comparison_high_byte(Expr *e,ByteComparison *operand)
{
    uint32_t count;
    e=word_bits(e);
    if(e->kind!=EX_BINARY||e->op!=TOK_SHR||e->type.base!=TY_INT||
       !e->type.is_unsigned||reg_width(e->type)!=2||
       width(e->left->type)!=2||!integer_constant(e->right,&count)||count!=8)return 0;
    operand->value=e->left;
    operand->high=1;
    return 1;
}

static Expr *comparison_low_byte(Expr *e)
{
    int uns;
    Expr *value=comparison_byte(e,&uns);
    if(!value||!uns)return NULL;
    for(;e!=value&&e->kind==EX_CAST;e=e->left)
        if(e->type.is_bool)return NULL;
    if(value->kind==EX_OBJECT&&(value->symbol==cg.numeric_index||
       value->symbol==cg.numeric_recurrence))return NULL;
    return value;
}

static int comparison_byte_home(ByteComparison *operand)
{
    Expr *value=operand->value;
    if(operand->high){
        if(fixed_memory_word(value,2,1,0))return 1;
        if(!indexed_operand(value,&operand->indexed)||!indexed_available(&operand->indexed)||
           operand->indexed.cursor_word||!indexed_pure(operand->indexed.index))return 0;
        ++operand->indexed.offset;
        operand->index=1;
        return 1;
    }
    return value->kind!=EX_OBJECT||value->symbol!=cg.scalar_first;
}

static void comparison_byte_text(ByteComparison *operand)
{
    Expr *value=operand->value;
    if(operand->index)indexed_text(&operand->indexed);
    else if(operand->high){
        cg.dp_byte_operand=1;
        fixed_memory_word(value,2,1,1);
        cg.dp_byte_operand=0;
    }
    else if(value->kind==EX_INT)code("#$%02X",value->value&255);
    else{
        unsigned offset=0;
        Symbol *home=value->kind==EX_OBJECT?value->symbol:fixed_memory_object(value,&offset);
        array_operand(home,offset);
    }
}

/* Compare an extracted high byte directly against another zero-extended
 * byte. Choose the index before entering A8 and evaluate an effectful or
 * volatile expression with the ordinary word path. */
static int branch_high_byte_equal(Expr *e,unsigned yes,unsigned no,unsigned fallthrough)
{
    ByteComparison left={0},right={0};
    int left_high,right_high;
    if(cg.parser->no_byte_shuffles||cg.parser->no_strength_reduction||
       (e->op!=TOK_EQ&&e->op!=TOK_NE)||body_effect(e)||
       reg_width(common_type(e->left->type,e->right->type))!=2)return 0;
    left_high=comparison_high_byte(e->left,&left);
    right_high=comparison_high_byte(e->right,&right);
    if(!left_high&&!right_high)return 0;
    if(!left_high&&!(left.value=comparison_low_byte(e->left)))return 0;
    if(!right_high&&!(right.value=comparison_low_byte(e->right)))return 0;
    if(!comparison_byte_home(&left)||!comparison_byte_home(&right))return 0;
    if(left.index&&right.index&&
       (left.indexed.reg!=right.indexed.reg||
        (!left.indexed.reg&&(left.indexed.scale!=right.indexed.scale||
                             !body_equal(left.indexed.index,right.indexed.index)))))return 0;
    if(left.index)indexed_index(&left.indexed);
    else if(right.index)indexed_index(&right.indexed);
    code("    sep #$20\n.a8\n    lda ");
    comparison_byte_text(&left);
    code("\n    cmp ");
    comparison_byte_text(&right);
    code("\n    rep #$20\n.a16\n");
    flag_branch(e->op==TOK_EQ?"beq":"bne",e->op==TOK_EQ?"bne":"beq",yes,no,fallthrough);
    return 1;
}

static int word_difference_safe(Expr *a,Expr *b)
{
    return a->known.valid&&b->known.valid&&reg_width(a->type)==2&&reg_width(b->type)==2&&
        (int64_t)a->known.min-b->known.max>=-32768&&(int64_t)a->known.max-b->known.min<=32767;
}
static int destination_x_preserves_a(Expr *e);
static const char *far_pointer_dp_home(Expr *base);
static const char *direct_far_compare_home(Expr *e)
{
    Expr *root;
    unsigned offset;
    int pointer;
    if(cg.parser->no_indexed_operands||e->kind!=EX_MEMBER||!e->type.banked||
       width(e->type)!=2||volatile_expression(e))return NULL;
    root=member_root(e,&offset,&pointer);
    if(offset)return NULL;
    if(!pointer){
        if(root->kind!=EX_DEREF)return NULL;
        root=root->left;
    }
    return far_pointer_dp_home(root);
}
static int word_compare_cursor(Expr *e)
{
    unsigned delta;
    InductionCursor *cursor;
    if(cg.parser->no_indexed_operands||cg.retained_index||cg.retained_second||
       cg.affine_active||cg.scan_cursor||cg.numeric_index||cg.lftr_active||
       e->kind!=EX_DEREF||!word_integer(e->type)||volatile_expression(e)||
       !(cursor=strength_pointer_plan(e->left,&delta)))return 0;
    return cursor==cg.bound?delta==cg.bound_delta:delta<=3||delta>=0xfffd;
}
static int word_compare_loaded(Expr *e,unsigned yes,unsigned no,unsigned fallthrough)
{
    Type t=common_type(e->left->type,e->right->type);
    uint32_t next_bound=0;
    int op=e->op,adjusted=0;
    unsigned address_offset=0;
    Symbol *address=t.pointers&&!far_pointer(t)?near_object_address(e->right,&address_offset):NULL;
    int immediate_rhs=constant_address(e->right),memory_rhs=compare_memory_operand(e->right,0);
    if(address&&!address->owner)immediate_rhs=1;else address=NULL;
    IndexedOperand indexed;
    int indexed_rhs=!immediate_rhs&&!memory_rhs&&width(e->right->type)==2&&reg_width(t)==2&&indexed_operand(e->right,&indexed)&&indexed_available(&indexed);
    int member_rhs=!cg.parser->no_indexed_operands&&!cg.retained_index&&
        !immediate_rhs&&!memory_rhs&&!indexed_rhs&&e->right->kind==EX_MEMBER&&
        width(e->right->type)==2&&!e->right->type.banked&&!volatile_expression(e->right)&&
        destination_x_preserves_a(e->right);
    int cursor_rhs=!immediate_rhs&&!memory_rhs&&!indexed_rhs&&!member_rhs&&word_integer(t)&&
        word_compare_cursor(e->right);
    const char *far_rhs=direct_far_compare_home(e->right);
    unsigned member_offset=0;
    int equality=e->op==TOK_EQ||e->op==TOK_NE;
    int signed_order=!equality&&!t.is_unsigned&&!t.pointers;
    if(signed_order&&e->left->known.valid&&e->right->known.valid&&
       e->left->known.min>=0&&e->right->known.min>=0)signed_order=0;
    if(!cg.parser->no_strength_reduction&&!signed_order&&!t.pointers&&
       word_integer(t)&&(op==TOK_LE||op=='>')&&integer_constant(e->right,&next_bound)&&
       (next_bound&65535)!=65535){
        ++next_bound;
        op=op==TOK_LE?'<':TOK_GE;
        adjusted=1;
    }
    /* Signed order against an integer constant: overflow of x-c is only
     * possible on one side (c>0: x<c; c<0: x>c) and never for c==0, whose
     * sign test needs only N/Z of x itself. */
    int constant=signed_order&&e->right->kind==EX_INT&&reg_width(t)==2;
    int c=constant?(int)(int16_t)(e->right->value&0xFFFF):0;
    if(!signed_order&&!equality&&e->right->kind==EX_INT&&!e->right->value&&reg_width(t)==2){
        if(e->op=='<'||e->op==TOK_GE){jump(e->op=='<'?no:yes);return 1;}
        if(!accumulator_zero_flags())code("    cmp #$0000\n");
        flag_branch(e->op=='>'?"bne":"beq",e->op=='>'?"beq":"bne",yes,no,fallthrough);return 1;
    }
    if(constant){
        if(!cg.parser->no_strength_reduction){
            if(c>0&&c<32767&&(op==TOK_LE||op=='>')&&!word_difference_safe(e->left,e->right)){
                /* Flipping the sign bit orders all signed words as unsigned */
                code("    eor #$8000\n    cmp #$%04X\n",(unsigned)(c+1)^0x8000u);
                integer_relation_flags(op==TOK_LE?'<':TOK_GE,0,yes,no,fallthrough);
                return 1;
            }
            if(c==1&&(op=='<'||op==TOK_GE)){c=0;op=op=='<'?TOK_LE:'>';}
            if(c==-1&&(op==TOK_LE||op=='>')){c=0;op=op==TOK_LE?'<':TOK_GE;}
            if(c>0&&(op=='<'||op==TOK_GE)&&accumulator_zero_flags()&&
               !word_difference_safe(e->left,e->right)){
                /* The existing sign flag decides negatives before the unsigned comparison */
                unsigned negative=op=='<'?yes:no;
                unsigned skip=negative==fallthrough?++cg.label:0;
                flag_branch("bmi","bpl",skip?skip:negative,0,0);
                code("    cmp #$%04X\n",(unsigned)c);
                integer_relation_flags(op,0,yes,no,fallthrough);
                if(skip)label(skip);
                return 1;
            }
        }
        if(c){code("    sec\n    sbc #$%04X\n",(unsigned)c&0xFFFF);}
        else if(!accumulator_zero_flags())code("    cmp #$0000\n");
        if(op=='>'||op==TOK_LE){
            unsigned equal=op=='>'?no:yes;
            if(!c&&!cg.parser->no_strength_reduction){
                unsigned done=equal==fallthrough?++cg.label:0;
                flag_branch("beq","bne",done?done:equal,0,0);
                integer_relation_flags(op,1,yes,no,fallthrough);
                if(done)label(done);
                return 1;
            }
            code("    bne :+\n");jump(equal);code(":\n");
        }
        int less=op=='<'||op==TOK_LE;
        if(c&&!word_difference_safe(e->left,e->right)){code("    bvc :+\n");jump((c>0)==less?yes:no);code(":\n");}
        integer_relation_flags(op,1,yes,no,fallthrough);
        return 1;
    }
    if(indexed_rhs)indexed_preserve_a(&indexed);
    if(member_rhs)member_offset=member_base_x(e->right);
    if(cursor_rhs)strength_pointer(e->right->left,1);
    if(!immediate_rhs&&!memory_rhs&&!indexed_rhs&&!member_rhs&&!cursor_rhs&&!far_rhs){
        code("    pha\n");if(cg.stack_leaf)cg.stack_bias+=2;
        emit_value(e->right);convert_registers(e->right->type,t);
        if(cg.stack_leaf)cg.stack_bias-=2;
        cg.arithmetic=1;code("    sta z:__arith_rhs\n    pla\n");
    }
    /* Equality with zero needs only Z, which a full-width producer of A set */
    if(equality&&e->right->kind==EX_INT&&!(e->right->value&0xFFFF)&&reg_width(t)==2&&accumulator_zero_flags()){
        flag_branch(e->op==TOK_EQ?"beq":"bne",e->op==TOK_EQ?"bne":"beq",yes,no,fallthrough);return 1;
    }
    int safe=signed_order&&word_difference_safe(e->left,e->right);
    /* Subtract one more for strict greater-than, including the equality case */
    int borrow=signed_order&&!cg.parser->no_strength_reduction&&(op=='>'||op==TOK_LE)&&
        (!safe||(int64_t)e->left->known.min-e->right->known.max>-32768);
    if(signed_order)code(borrow?"    clc\n":"    sec\n");
    code("    %s ",signed_order?"sbc":"cmp");
    if(address){address->used=1;code("#.loword(_%s+$%04X)",address->asm_name,address_offset);}
    else if(adjusted)code("#$%04X",next_bound&65535);
    else if(immediate_rhs){code("#");immediate(e->right,0);}
    else if(memory_rhs)compare_memory_operand(e->right,1);
    else if(indexed_rhs)indexed_text(&indexed);
    else if(member_rhs)code("a:$%04X,x",member_offset);
    else if(cursor_rhs)code("%s:$0000,x",strength_wram_pointer(e->right->left)?"z":"a");
    else if(far_rhs)code("[%s]",far_rhs);
    else code("z:__arith_rhs");
    code("\n");
    if(equality){flag_branch(e->op==TOK_EQ?"beq":"bne",e->op==TOK_EQ?"bne":"beq",yes,no,fallthrough);return 1;}
    if(!borrow&&(op=='>'||op==TOK_LE)){
        code("    bne :+\n");jump(op=='>'?no:yes);code(":\n");
    }
    if(signed_order){
        if(!safe)code("    bvc :+\n    eor #$8000\n:\n");
        if(e->op=='<'||e->op==TOK_LE)flag_branch("bmi","bpl",yes,no,fallthrough);
        else flag_branch("bpl","bmi",yes,no,fallthrough);
    }else{
        if(op=='<'||op==TOK_LE)flag_branch("bcc","bcs",yes,no,fallthrough);
        else flag_branch("bcs","bcc",yes,no,fallthrough);
    }
    return 1;
}
static Expr *word_initializer(Statement *s,Symbol *symbol)
{
    for(;s;s=s->next){
        Expr *e=s->expression,*found;
        if(s->kind==ST_EXPR&&e&&e->kind==EX_ASSIGN&&!e->op&&
           e->left->kind==EX_OBJECT&&e->left->symbol==symbol)return e->right;
        found=word_initializer(s->initial,symbol);
        if(!found)found=word_initializer(s->body,symbol);
        if(!found)found=word_initializer(s->alternate,symbol);
        if(found)return found;
    }
    return NULL;
}

/* A private scalar with a unique definition retains the sign of a
 * constant selection even across calls that invalidate other facts. */
static int word_strict_sign(Expr *e,int definition)
{
    uint32_t value;
    if(!e||e->type.pointers||e->type.is_unsigned||e->type.base!=TY_INT)return 0;
    if(e->known.valid){
        if(e->known.min>0)return 1;
        if(e->known.max<0)return -1;
    }
    if(integer_constant(e,&value))return (int16_t)value>0?1:(int16_t)value<0?-1:0;
    if(e->kind==EX_CHOOSE){
        int a=word_strict_sign(e->right,0),b=word_strict_sign(e->third,0);
        return a==b?a:0;
    }
    if(e->kind==EX_UNARY&&e->op=='-'&&word_strict_sign(e->left,definition)>0)return -1;
    if(definition&&e->kind==EX_OBJECT&&e->symbol->scope&&body_private(e->symbol)&&
       scalar_writes(cg.function->body,e->symbol)==1)
        return word_strict_sign(word_initializer(cg.function->body,e->symbol),0);
    return 0;
}

static int masked_word_operand(Expr *e)
{
    uint32_t mask;
    return e->kind==EX_BINARY&&e->op=='&'&&width(e->left->type)==2&&
           !e->left->type.pointers&&compare_memory_operand(e->left,0)&&
           integer_constant(e->right,&mask)&&mask<=65535;
}

/* A pure masked RHS can be evaluated first. When the LHS is directly
 * addressable, subtract with borrow to get strict unsigned order from C. */
static int branch_masked_word(Expr *e,unsigned yes,unsigned no,unsigned fallthrough)
{
    Expr *left=e->left,*right=e->right;
    Type t=common_type(left->type,right->type);
    int op=e->op,direct,carry;
    if(cg.parser->no_strength_reduction||t.base!=TY_INT||!t.is_unsigned||
       t.pointers||volatile_expression(e)||!masked_word_operand(right)||
       (op!='<'&&op!='>'&&op!=TOK_LE&&op!=TOK_GE))return 0;
    direct=width(left->type)==2&&!left->type.pointers&&compare_memory_operand(left,0);
    if(!direct&&(!masked_word_operand(left)||(op!='<'&&op!=TOK_GE)))return 0;
    emit_value(right);
    if(direct){
        int strict=op=='<'||op==TOK_GE;
        if(strict)code("    clc\n");
        code("    %s ",strict?"sbc":"cmp");
        compare_memory_operand(left,1);code("\n");
        carry=op=='<'||op==TOK_LE;
    }else{
        stage(1,t);emit_value(left);code("    cmp z:__arith_rhs\n");
        carry=op==TOK_GE;
    }
    flag_branch(carry?"bcs":"bcc",carry?"bcc":"bcs",yes,no,fallthrough);
    return 1;
}

static int fixed_bitfield_equality(Expr *e,unsigned yes,unsigned no,unsigned fallthrough)
{
    Expr *field=word_bits(e->left),*literal=e->right;
    uint32_t value,mask;
    unsigned bits,offset;
    Symbol *storage;
    if(cg.parser->no_strength_reduction||(e->op!=TOK_EQ&&e->op!=TOK_NE)||
       !word_integer(common_type(e->left->type,e->right->type)))return 0;
    if(field->kind!=EX_BITFIELD){field=word_bits(e->right);literal=e->left;}
    if(field->kind!=EX_BITFIELD||volatile_expression(field)||
       !integer_constant(literal,&value)||!(storage=direct_memory_object(field->left,&offset)))return 0;
    bits=field->type.bit_field_width;
    if(!bits||bits>=16||field->value+bits>16)return 0;
    mask=(1u<<bits)-1;
    value&=65535;
    if(field->op){
        uint32_t sign=1u<<(bits-1);
        if(((((value&mask)^sign)-sign)&65535)!=value)return 0;
    }else if(value>mask)return 0;
    value=(value&mask)<<field->value;
    code("    lda ");array_operand(storage,offset);
    code("\n    and #$%04X\n",mask<<field->value);
    if(value&&bits==1)flag_branch(e->op==TOK_EQ?"bne":"beq",e->op==TOK_EQ?"beq":"bne",yes,no,fallthrough);
    else{
        if(value)code("    cmp #$%04X\n",value);
        flag_branch(e->op==TOK_EQ?"beq":"bne",e->op==TOK_EQ?"bne":"beq",yes,no,fallthrough);
    }
    return 1;
}

static int branch_signed_byte_call(Expr *e,Type t,unsigned yes,unsigned no,unsigned fallthrough)
{
    Expr *call=e->left,*literal=e->right;
    uint32_t bits;
    int equal=e->op==TOK_EQ;
    if(cg.parser->no_strength_reduction||(!equal&&e->op!=TOK_NE)||!word_integer(t))return 0;
    if(call->kind==EX_INT){call=e->right;literal=e->left;}
    call=word_bits(call);
    if(call->kind==EX_CAST&&word_integer(call->type)&&call->left->type.base==TY_CHAR)
        call=call->left;
    if(call->kind!=EX_CALL||call->type.pointers||call->type.base!=TY_CHAR||
       call->type.is_unsigned||call->type.is_bool||
       !integer_constant(literal,&bits)||(uint16_t)(int8_t)bits!=(uint16_t)bits)return 0;
    emit_call(call,CALL_LOW_BYTE);
    code("    sep #$20\n.a8\n    cmp #$%02X\n    rep #$20\n.a16\n",(unsigned)bits&255);
    flag_branch(equal?"beq":"bne",equal?"bne":"beq",yes,no,fallthrough);
    return 1;
}

/* For near equality, move a constant pointer displacement into the known
 * frame address. This leaves the other pointer as a direct CMP operand. */
static int compare_frame_pointer_offset(Expr *a,Expr *b)
{
    unsigned offset,delta=0;
    Expr *base=a;
    if(cg.parser->no_strength_reduction||cg.dp_homes||cg.stack_leaf||
       !value_type(a->type).pointers||far_pointer(value_type(a->type)))return 0;
    if(a->kind==EX_BINARY&&(a->op=='+'||a->op=='-')){
        base=a->left;
        if(!value_type(base->type).pointers||!far_small_displacement(base,a->right,&delta))return 0;
        if(a->op=='+')delta=65536u-delta;
    }
    Symbol *home=near_object_address(b,&offset);
    if(!home||!home->owner||far_pointer(value_type(b->type))||!compare_memory_operand(base,0))return 0;
    offset=(frame_offset(home->offset)+offset+delta)&65535u;
    home->used=1;
    code("    tya\n");
    if(offset)code("    clc\n    adc #$%04X\n",offset);
    code("    cmp ");compare_memory_operand(base,1);code("\n");
    return 1;
}
static int word_compare_branch(Expr *e,unsigned yes,unsigned no,unsigned fallthrough)
{
    Expr *left=e->left,*right=e->right;
    Type t=common_type(left->type,right->type);
    uint32_t mask,value;
    int sign=0;
    if((e->op==TOK_EQ||e->op==TOK_NE)&&t.pointers&&!far_pointer(t)&&
       (compare_frame_pointer_offset(left,right)||compare_frame_pointer_offset(right,left))){
        flag_branch(e->op==TOK_EQ?"beq":"bne",e->op==TOK_EQ?"bne":"beq",yes,no,fallthrough);return 1;
    }
    if(!cg.parser->no_strength_reduction&&word_integer(t)&&!t.is_unsigned&&
       (e->op=='<'||e->op=='>'||e->op==TOK_LE||e->op==TOK_GE)&&
       left->kind==EX_INT&&right->kind!=EX_INT&&(int16_t)left->value>=-1&&(int16_t)left->value<=1){
        Expr swapped=*e;
        swapped.left=right;swapped.right=left;swapped.op=reverse_order(e->op);
        emit_value(right);convert_registers(right->type,t);
        return word_compare_loaded(&swapped,yes,no,fallthrough);
    }
    if(!cg.parser->no_strength_reduction&&(e->op==TOK_EQ||e->op==TOK_NE)&&
       left->kind==EX_BINARY&&left->op=='&'&&integer_constant(left->right,&mask)&&
       mask&&!(mask&(mask-1))&&mask<=65535&&integer_constant(right,&value)&&value==mask){
        emit_value(left);
        if(!accumulator_zero_flags())code("    cmp #0\n");
        flag_branch(e->op==TOK_EQ?"bne":"beq",e->op==TOK_EQ?"beq":"bne",yes,no,fallthrough);
        return 1;
    }
    if(!cg.parser->no_strength_reduction&&!t.pointers&&!t.is_unsigned&&t.base==TY_INT&&
       (e->op==TOK_GE||e->op=='<'||e->op==TOK_LE||e->op=='>')&&
       !(left->known.valid&&(left->known.min>=0||left->known.max<0))&&
       !body_effect(left)&&!body_effect(right)&&right->kind!=EX_INT&&
       (sign=word_strict_sign(right,1))!=0){
        int negative=sign<0,less=e->op=='<'||e->op==TOK_LE;
        int direct=compare_memory_operand(right,0);
        int reverse=!direct&&compare_memory_operand(left,0)&&e->op==TOK_LE;
        if(direct||reverse){
            unsigned different=(negative==less)?no:yes;
            emit_value(left);
            if(!accumulator_zero_flags())code("    cmp #0\n");
            code("    %s :+\n",negative?"bmi":"bpl");jump(different);code(":\n");
            if(reverse)emit_value(right);
            code("    cmp ");compare_memory_operand(reverse?left:right,1);code("\n");
            if(!reverse&&(e->op==TOK_LE||e->op=='>')){
                code("    bne :+\n");jump(e->op==TOK_LE?yes:no);code(":\n");
            }
            if(!reverse&&less)flag_branch("bcc","bcs",yes,no,fallthrough);
            else flag_branch("bcs","bcc",yes,no,fallthrough);
            return 1;
        }
    }
    if((e->op==TOK_EQ||e->op==TOK_NE)&&e->right->kind==EX_INT&&!e->right->value&&
       fixed_byte_test(e->left)){
        flag_branch(e->op==TOK_EQ?"beq":"bne",e->op==TOK_EQ?"bne":"beq",yes,no,fallthrough);
        return 1;
    }
    if(branch_signed_byte_call(e,t,yes,no,fallthrough)||fixed_bitfield_equality(e,yes,no,fallthrough)||
       branch_high_byte_equal(e,yes,no,fallthrough)||byte_equal_branch(e,yes,no,fallthrough)||
       branch_masked_word(e,yes,no,fallthrough))return 1;
    if(!cg.parser->no_strength_reduction&&(e->op==TOK_EQ||e->op==TOK_NE)&&word_integer(t)&&
       word_compare_cursor(left)&&!direct_operand(right,t,0,0)&&!body_effect(e)){
        Expr swap=*e;swap.left=right;swap.right=left;
        emit_value(right);convert_registers(right->type,t);
        return word_compare_loaded(&swap,yes,no,fallthrough);
    }
    if(!cg.parser->no_strength_reduction&&(e->op==TOK_EQ||e->op==TOK_NE)&&word_integer(t)&&
       !integer_constant(right,&value)&&!compare_memory_operand(right,0)&&
       compare_memory_operand(left,0)&&!body_effect(e)){
        emit_value(right);convert_registers(right->type,t);
        code("    cmp ");compare_memory_operand(left,1);code("\n");
        flag_branch(e->op==TOK_EQ?"beq":"bne",e->op==TOK_EQ?"bne":"beq",yes,no,fallthrough);
        return 1;
    }
    emit_value(e->left);convert_registers(e->left->type,common_type(e->left->type,e->right->type));
    return word_compare_loaded(e,yes,no,fallthrough);
}
/* A stored far pointer has a zero-padded bank word. Compare it first, then the
 * low word, without staging either operand or calling the integer helper.
 * Expressions with calls, conversions or indirect reads retain the fallback. */
static Expr *far_compare_home(Expr *e)
{
    if(volatile_expression(e))return NULL;
    while(e->kind==EX_CAST&&far_pointer(value_type(e->type))&&far_pointer(value_type(e->left->type)))e=e->left;
    return e->kind==EX_OBJECT&&!e->type.array&&!e->type.banked&&far_pointer(value_type(e->type))?e:NULL;
}
static int null_pointer_operand(Expr *e)
{
    uint32_t bits;
    while(e->kind==EX_CAST&&e->type.pointers)e=e->left;
    return e->kind==EX_INT&&e->type.pointers?!e->value:
        integer_constant(e,&bits)&&!bits;
}
static String *scalar_string_offset(Expr *e,unsigned *offset);
static String *scalar_string_address(Expr *e,unsigned *offset,int bounded);
static int far_compare_branch(Expr *e,unsigned yes,unsigned no,unsigned fallthrough)
{
    Expr *left=far_compare_home(e->left),*right=far_compare_home(e->right);unsigned decide;
    Expr *value=e->left,*zero=e->right;
    if(cg.parser->no_strength_reduction)return 0;
    if(null_pointer_operand(value)){zero=value;value=e->right;}
    if((e->op==TOK_EQ||e->op==TOK_NE)&&far_pointer(value_type(value->type))&&
       null_pointer_operand(zero)){
        Expr *home=far_compare_home(value);
        if(home){
            code("    lda ");array_operand(home->symbol,0);
            code("\n    ora ");array_operand(home->symbol,2);code("\n");
        }else{
            emit_value(value);
            code("    cmp #0\n    bne :+\n    cpx #0\n:\n");
        }
        flag_branch(e->op==TOK_EQ?"beq":"bne",e->op==TOK_EQ?"bne":"beq",yes,no,fallthrough);
        return 1;
    }
    unsigned literal_offset;
    Expr *tested=e->left;
    String *literal=scalar_string_offset(e->right,&literal_offset);
    if(!literal&&(e->op==TOK_EQ||e->op==TOK_NE)){
        literal=scalar_string_offset(e->left,&literal_offset);
        tested=e->right;
    }
    if(literal){
        literal->used=1;
        emit_value(tested);convert_registers(tested->type,common_type(e->left->type,e->right->type));
        decide=++cg.label;
        code("    cpx #.bankbyte(str_%s_%u+$%X)\n    bne cg_%s_%u\n"
             "    cmp #.loword(str_%s_%u+$%X)\n",
             cg.parser->unit,literal->id,literal_offset,cg.parser->unit,decide,
             cg.parser->unit,literal->id,literal_offset);
        label(decide);
    }else if(e->right->kind==EX_OBJECT&&e->right->type.array&&e->right->type.banked){
        Symbol *array=e->right->symbol;
        emit_value(e->left);convert_registers(e->left->type,common_type(e->left->type,e->right->type));
        decide=++cg.label;
        array->used=1;
        code("    cpx #.bankbyte(_%s)\n    bne cg_%s_%u\n    cmp #.loword(_%s)\n",
             array->asm_name,cg.parser->unit,decide,array->asm_name);
        label(decide);
    }else if(left&&right&&e->op!=TOK_EQ&&e->op!=TOK_NE){
        int relation=e->op;
        if(relation=='>'||relation==TOK_LE){
            Expr *swap=left;left=right;right=swap;
            relation=relation=='>'?'<':TOK_GE;
        }
        /* Both homes are stable. Compare low words first so the bank
         * subtraction includes their borrow without a separate branch. */
        code("; direct far-pointer comparison: low borrow into bank\n    lda ");array_operand(left->symbol,0);
        code("\n    cmp ");array_operand(right->symbol,0);
        code("\n    lda ");array_operand(left->symbol,2);
        code("\n    sbc ");array_operand(right->symbol,2);code("\n");
        integer_relation_flags(relation,0,yes,no,fallthrough);return 1;
    }else if(!left&&right&&far_pointer(value_type(e->left->type))&&e->op!=TOK_EQ&&e->op!=TOK_NE){
        emit_value(e->left);
        /* The low-word borrow, including equality for <= and >, carries
         * directly into the bank subtraction. TXA preserves carry. */
        code(e->op==TOK_LE||e->op=='>'?"    clc\n    sbc ":"    cmp ");
        array_operand(right->symbol,0);
        code("\n    txa\n    sbc ");array_operand(right->symbol,2);code("\n");
        integer_relation_flags(e->op,0,yes,no,fallthrough);
        return 1;
    }else if(!left||!right){
        unsigned offset;
        Expr *operand=left?left:e->right,*other=left?e->right:e->left;
        Symbol *home;
        if((e->op!=TOK_EQ&&e->op!=TOK_NE)||!far_pointer(value_type(other->type))||
           (left&&body_effect(other)))return 0;
        while(operand->kind==EX_CAST&&far_pointer(value_type(operand->type))&&
              far_pointer(value_type(operand->left->type)))operand=operand->left;
        if(operand->type.array||!far_pointer(operand->type)||
           !(home=direct_memory_object(operand,&offset)))return 0;
        emit_value(other);
        decide=++cg.label;
        code("    cmp ");array_operand(home,offset);
        code("\n    bne cg_%s_%u\n    txa\n    cmp ",cg.parser->unit,decide);
        array_operand(home,offset+2);code("\n");label(decide);
        flag_branch(e->op==TOK_EQ?"beq":"bne",e->op==TOK_EQ?"bne":"beq",yes,no,fallthrough);
        return 1;
    }else{
        decide=++cg.label;
        code("; direct far-pointer comparison: bank then low word\n    lda ");array_operand(left->symbol,2);
        code("\n    cmp ");array_operand(right->symbol,2);code("\n    bne cg_%s_%u\n    lda ",cg.parser->unit,decide);
        array_operand(left->symbol,0);code("\n    cmp ");array_operand(right->symbol,0);code("\n");label(decide);
    }
    if(e->op==TOK_EQ||e->op==TOK_NE){
        flag_branch(e->op==TOK_EQ?"beq":"bne",e->op==TOK_EQ?"bne":"beq",yes,no,fallthrough);return 1;
    }
    if(e->op=='>'||e->op==TOK_LE){code("    bne :+\n");jump(e->op=='>'?no:yes);code(":\n");}
    if(e->op=='<'||e->op==TOK_LE)flag_branch("bcc","bcs",yes,no,fallthrough);
    else flag_branch("bcs","bcc",yes,no,fallthrough);
    return 1;
}
static Expr *binary32_compare_operand(Expr *e,Type t,Expr *literal)
{
    if(e->kind==EX_UNARY&&(e->op=='+'||e->op=='-')&&
       e->left->kind==EX_INT&&e->left->type.base==TY_FLOAT&&!e->left->type.pointers){
        *literal=*e->left;
        if(e->op=='-')literal->value^=0x80000000u;
        return literal;
    }
    if(e->kind!=EX_INT||e->type.pointers||e->type.array||
       (e->type.base!=TY_CHAR&&e->type.base!=TY_INT&&e->type.base!=TY_LONG))return e;
    *literal=*e;
    return convert(literal,t);
}
static int binary32_zero(Expr *e)
{
    return e->kind==EX_INT&&!e->type.pointers&&e->type.base==TY_FLOAT&&!(e->value&0x7fffffffu);
}
/* A finite nonzero binary32 value has one representation */
static int binary32_constant_equality(Expr *e,unsigned yes,unsigned no,unsigned fallthrough)
{
    Expr *value=e->left,*literal=e->right;
    int equal=e->op==TOK_EQ;
    uint32_t bits;
    if(value->kind==EX_INT){value=e->right;literal=e->left;}
    if(literal->kind!=EX_INT||literal->type.pointers||literal->type.base!=TY_FLOAT||
       value->type.pointers||value->type.base!=TY_FLOAT||volatile_expression(value)||
       !fixed_memory_word(value,4,0,0))return 0;
    bits=literal->value&0x7fffffffu;
    if(!bits||bits>=0x7f800000u)return 0;
    code("    lda ");fixed_memory_word(value,4,2,1);
    code("\n    cmp #$%04X\n    beq :+\n",literal->value>>16);
    jump(equal?no:yes);code(":\n    lda ");fixed_memory_word(value,4,0,1);code("\n");
    if(bits&65535)code("    cmp #$%04X\n",bits&65535);
    flag_branch(equal?"beq":"bne",equal?"bne":"beq",yes,no,fallthrough);
    return 1;
}
/* Reduce a negative threshold to positive order by flipping both signs.
 * The only exceptional inputs that need a low-word read off a tie are infinities. */
static int binary32_constant_order(Expr *e,unsigned yes,unsigned no,unsigned fallthrough)
{
    Expr *value=e->left,*literal=e->right;
    unsigned high,low,done,tie,y,n;
    uint32_t bits;
    int op=e->op,negate,less,equal;
    if(op!='<'&&op!='>'&&op!=TOK_LE&&op!=TOK_GE)return 0;
    if(value->kind==EX_INT){value=e->right;literal=e->left;op=reverse_order(op);}
    if(literal->kind!=EX_INT||literal->type.base!=TY_FLOAT||value->type.base!=TY_FLOAT||
       literal->type.pointers||value->type.pointers||volatile_expression(value)||
       !fixed_memory_word(value,4,0,0))return 0;
    bits=literal->value&0x7fffffffu;
    if(!bits&&(op=='<'||op=='>')){
        /* Reject the opposite sign immediately. At zero and infinity the
         * fraction low word distinguishes subnormals and NaNs respectively. */
        unsigned infinity=++cg.label;
        code("    lda ");fixed_memory_word(value,4,2,1);code("\n");
        if(op=='>')code("    eor #$8000\n");
        code("    bpl cg_%s_%u\n    cmp #$FF80\n    beq cg_%s_%u\n    bcs cg_%s_%u\n",
             cg.parser->unit,no,cg.parser->unit,infinity,cg.parser->unit,no);
        code("    cmp #$8000\n    bne cg_%s_%u\n    lda ",cg.parser->unit,yes);
        fixed_memory_word(value,4,0,1);code("\n");
        flag_branch("bne","beq",yes,no,0);label(infinity);
        code("    lda ");fixed_memory_word(value,4,0,1);code("\n");
        flag_branch("beq","bne",yes,no,fallthrough);return 1;
    }
    if(!bits||bits>=0x7f800000u)return 0;
    negate=(literal->value>>31)!=0;
    if(negate)op=reverse_order(op);
    less=op=='<'||op==TOK_LE;equal=op==TOK_LE||op==TOK_GE;
    high=bits>>16;low=bits&65535;
    done=(yes==fallthrough||no==fallthrough)?++cg.label:0;
    tie=(low||op=='>'||op==TOK_LE)?++cg.label:0;
    y=yes==fallthrough?done:yes;n=no==fallthrough?done:no;
    code("; ordered binary32 comparison against a constant\n    lda ");
    fixed_memory_word(value,4,2,1);code("\n");
    if(negate)code("    eor #$8000\n");
    code("    cmp #$%04X\n",high);
    flag_branch("bcc","bcs",less?y:n,0,0);
    if(tie)flag_branch("beq","bne",tie,0,0);
    if(less){
        code("    cmp #$8000\n");
        flag_branch("bcc","bcs",n,0,0);
    }
    code("    cmp #$%04X\n",less?0xff80:0x7f80);
    flag_branch("bcc","bcs",y,0,0);
    flag_branch("bne","beq",n,0,0);
    code("    lda ");fixed_memory_word(value,4,0,1);code("\n");
    flag_branch("beq","bne",y,n,0);
    if(tie){
        label(tie);code("    lda ");fixed_memory_word(value,4,0,1);code("\n");
        if(low){code("    cmp #$%04X\n",low);
            flag_branch("bcc","bcs",less?y:n,0,0);
        }
        if(equal!=less)jump(less?n:y);
        else flag_branch("beq","bne",equal?y:n,less?n:y,0);
    }
    if(done)label(done);
    return 1;
}
/* Unequal high words decide unsigned order without reading either low word */
static void unsigned_long_order(Expr *left,Expr *right,Type type,int op,
                                unsigned yes,unsigned no,unsigned fallthrough)
{
    unsigned below,above,done=yes==fallthrough||no==fallthrough?++cg.label:0;
    if(op=='>'||op==TOK_LE){Expr *swap=left;left=right;right=swap;op=op=='>'?'<':TOK_GE;}
    below=op=='<'?yes:no;above=op=='<'?no:yes;
    code("; compare unsigned long high word first\n    lda ");direct_operand(left,type,1,1);
    code("\n    cmp ");direct_operand(right,type,1,1);code("\n");
    flag_branch("bcc","bcs",below==fallthrough?done:below,0,0);
    flag_branch("bne","beq",above==fallthrough?done:above,0,0);
    code("    lda ");direct_operand(left,type,0,1);
    code("\n    cmp ");direct_operand(right,type,0,1);code("\n");
    integer_relation_flags(op,0,yes,no,fallthrough);
    if(done)label(done);
}
static int literal_integer_tree(Expr *e);
static Expr *long_low_source(Expr *e)
{
    uint32_t mask;
    if(e->kind==EX_BINARY&&(e->op=='^'||e->op=='|')&&
       e->right->kind==EX_BINARY&&e->right->op=='&'&&
       integer_constant(e->right->right,&mask)&&!(mask&65535u))return e->left;
    return e;
}
static void emit_long_high_word(Expr *e,Type t)
{
    Expr *low;
    if(direct_operand(e,t,1,0)){
        code("    lda ");direct_operand(e,t,1,1);code("\n");
    }else if(e->kind==EX_BINARY&&e->type.base==TY_LONG&&!e->type.pointers&&
             (e->op=='&'||e->op=='|'||e->op=='^')&&!body_effect(e)){
        Expr *left=e->left,*right=e->right;
        const char *op=e->op=='&'?"and":e->op=='|'?"ora":"eor";
        if(!direct_operand(right,t,1,0)&&direct_operand(left,t,1,0)){
            left=e->right;right=e->left;
        }
        emit_long_high_word(left,t);
        if(direct_operand(right,t,1,0)){
            code("    %s ",op);direct_operand(right,t,1,1);code("\n");
        }else{
            code("    pha\n");cg.stack_bias+=2;
            emit_long_high_word(right,t);
            code("    %s 1,s\n    plx\n    cmp #0\n",op);cg.stack_bias-=2;
        }
    }else if(e->kind==EX_BINARY&&e->op=='-'&&e->type.base==TY_LONG&&!e->type.pointers&&
             direct_operand(low=long_low_source(e->left),t,0,0)&&direct_operand(e->right,t,0,0)&&
             direct_operand(e->right,t,1,0)&&literal_integer_tree(e)){
        code("    lda ");direct_operand(low,t,0,1);
        code("\n    cmp ");direct_operand(e->right,t,0,1);
        code("\n    php\n");++cg.stack_bias;
        emit_long_high_word(e->left,t);
        code("    plp\n    sbc ");--cg.stack_bias;
        direct_operand(e->right,t,1,1);code("\n");
    }else{
        emit_value(e);convert_registers(e->type,t);code("    txa\n");
    }
}
/* For a literal 64-bit integer, only the choice of rounded endpoint is
 * dynamic. Preserve both the current rounding mode and sticky inexact flag. */
static int branch_wide_float_literal(Expr *e,unsigned yes,unsigned no,unsigned fallthrough)
{
    Expr *cast=e->left,*bound=e->right,*integer;
    uint64_t raw,magnitude,significant,discarded,half;
    uint32_t bits,toward,away;
    float lower,upper,value;
    unsigned shift=0;
    int swapped=cast->kind!=EX_CAST,negative,nearest;
    if(cg.function->symbol->interrupt)return 0;
    if(swapped){cast=e->right;bound=e->left;}
    if(cast->kind!=EX_CAST||cast->type.base!=TY_FLOAT||cast->type.pointers||
       !binary32_literal(bound,&value,0))return 0;
    integer=cast->left;
    if(integer->kind!=EX_INT||integer->type.base!=TY_LONGLONG||integer->type.pointers)return 0;
    raw=((uint64_t)integer->value_high<<32)|integer->value;
    negative=!integer->type.is_unsigned&&(raw>>63);
    magnitude=negative?0-raw:raw;
    significant=magnitude;
    while(significant>0xffffffu){significant>>=1;++shift;}
    discarded=magnitude-(significant<<shift);
    if(!discarded)return 0;
    half=UINT64_C(1)<<(shift-1);
    nearest=discarded>half||(discarded==half&&(significant&1));
    /* The truncated integer is exactly representable. Its next bit pattern
     * increases the magnitude by one ULP, including at a power of two. */
    lower=(float)(significant<<shift);
    memcpy(&bits,&lower,sizeof bits);
    if(negative)bits|=UINT32_C(0x80000000);
    memcpy(&lower,&bits,sizeof lower);
    ++bits;
    memcpy(&upper,&bits,sizeof upper);
    if(binary32_constant_operation(e->op,swapped?value:lower,swapped?lower:value,&toward)||
       binary32_constant_operation(e->op,swapped?value:upper,swapped?upper:value,&away))return 0;
    /* The folded operation still raises its sticky inexact flag */
    code("    lda #$0010\n    tsb a:.loword(__fp_exceptions)\n");
    if(toward==away||cg.parser->rom_default_rounding){
        uint32_t result=nearest?away:toward;
        unsigned target=result?yes:no;
        if(target!=fallthrough)jump(target);
        return 1;
    }
    /* The runtime mode and exception words share the near BSS bank */
    code("    lda a:.loword(__fp_round_mode)\n");
    /* FE_TONEAREST is 0, FE_DOWNWARD is 1 and FE_UPWARD is 2 */
    if(nearest&&!negative){
        code("    lsr a\n");
        flag_branch("bcc","bcs",away?yes:no,away?no:yes,fallthrough);
    }else{
        if(nearest)code("    bit #$0002\n");
        else code("    cmp #$%04X\n",negative?1:2);
        flag_branch("beq","bne",away?yes:no,away?no:yes,fallthrough);
    }
    return 1;
}
/* A fixed nonvolatile pre-update needs its high word only on wrap or when
 * the new low word matches the literal. Branch consumers need no X:A result. */
static int branch_preupdated_long(Expr *e,unsigned yes,unsigned no,unsigned fallthrough)
{
    Expr *step=e->left,*home;
    uint32_t value;
    if(cg.parser->no_strength_reduction||(e->op!=TOK_EQ&&e->op!=TOK_NE)||
       step->kind!=EX_PRE||(step->op!=TOK_INC&&step->op!=TOK_DEC)||
       step->type.base!=TY_LONG||step->type.pointers||volatile_expression(step)||
       !integer_constant(e->right,&value)||!fixed_memory_word(step->left,4,0,0))return 0;
    int inc=step->op==TOK_INC;
    unsigned mismatch=e->op==TOK_EQ?no:yes,match=e->op==TOK_EQ?yes:no;
    home=step->left;
    code("    lda ");fixed_memory_word(home,4,0,1);
    code(inc?"\n    clc\n    adc #1\n    sta ":"\n    sec\n    sbc #1\n    sta ");
    fixed_memory_word(home,4,0,1);code(inc?"\n    bcc :+\n    lda ":"\n    bcs :+\n    lda ");
    fixed_memory_word(home,4,2,1);code(inc?"\n    inc a\n    sta ":"\n    dec a\n    sta ");
    fixed_memory_word(home,4,2,1);
    code("\n    lda #$%04X\n:\n",inc?0:65535);
    if(value&65535)code("    cmp #$%04X\n",value&65535);
    code("    bne cg_%s_%u\n    lda ",cg.parser->unit,mismatch);
    fixed_memory_word(home,4,2,1);code("\n");
    if(value>>16)code("    cmp #$%04X\n",value>>16);
    flag_branch("beq","bne",match,mismatch,fallthrough);
    divmod_written(home);return 1;
}
/* The register comparison can reuse a just-stored high frame word.
 * A wide result store may restore its low accumulator word with PLA. */
static int recent_frame_high_store(Expr *value)
{
    unsigned offset;
    Symbol *home=direct_memory_object(value,&offset);
    if(!home||!home->owner)return 0;
    char store[48];
    int n=cg.stack_leaf?snprintf(store,sizeof store,"    sta %u,s",home->offset+offset+2+cg.stack_bias):
        snprintf(store,sizeof store,"    sta %s",frame_operand(home->offset+offset+2));
    size_t length,start=previous_instruction(cg.length,&length);
    if(length==7&&!strncmp(cg.assembly+start,"    pla",7))start=previous_instruction(start,&length);
    return n>0&&(size_t)n==length&&!strncmp(cg.assembly+start,store,length);
}
static void wide_compare_branch(Expr *e,unsigned yes,unsigned no,unsigned fallthrough)
{
    Type t=common_type(e->left->type,e->right->type);int floating=t.base==TY_FLOAT&&!t.pointers;
    Expr comparison,left_literal,right_literal;
    uint32_t constant;
    if(!cg.parser->no_strength_reduction&&floating){
        comparison=*e;
        comparison.left=binary32_compare_operand(e->left,t,&left_literal);
        comparison.right=binary32_compare_operand(e->right,t,&right_literal);
        e=&comparison;
        if(branch_wide_float_literal(e,yes,no,fallthrough))return;
        if(binary32_constant_order(e,yes,no,fallthrough))return;
        if(e->op==TOK_EQ||e->op==TOK_NE){
            if(binary32_constant_equality(e,yes,no,fallthrough))return;
            Expr *value=binary32_zero(e->left)?e->right:binary32_zero(e->right)?e->left:NULL;
            if(value&&value->type.base==TY_FLOAT&&!value->type.pointers){
                truth(value);
                flag_branch(e->op==TOK_EQ?"beq":"bne",e->op==TOK_EQ?"bne":"beq",yes,no,fallthrough);
                return;
            }
        }
    }
    if(!cg.parser->no_strength_reduction&&!floating&&!t.pointers&&
       !volatile_expression(e->right)&&!direct_operand(e->right,t,0,0)&&
       (integer_constant(e->left,&constant)||
        (t.base==TY_LONG&&e->op!=TOK_EQ&&e->op!=TOK_NE&&
         !volatile_expression(e->left)&&!body_effect(e->right)&&
         direct_operand(e->left,t,0,0)&&direct_operand(e->left,t,1,0)))){
        comparison=*e;comparison.left=e->right;comparison.right=e->left;
        switch(e->op){
        case '<':comparison.op='>';break;
        case '>':comparison.op='<';break;
        case TOK_LE:comparison.op=TOK_GE;break;
        case TOK_GE:comparison.op=TOK_LE;break;
        }
        e=&comparison;
    }
    if(!floating&&!t.pointers&&t.base==TY_LONG&&branch_preupdated_long(e,yes,no,fallthrough))return;
    if(far_pointer(t)&&!volatile_expression(e)&&far_compare_branch(e,yes,no,fallthrough))return;
    if(!cg.parser->no_strength_reduction&&!t.pointers&&t.base==TY_LONG&&!t.is_unsigned){
        int negative=e->op=='<'||e->op=='>';
        int reversed=e->op=='>'||e->op==TOK_LE;
        Expr *value=reversed?e->right:e->left,*zero=reversed?e->left:e->right;
        if((e->op=='>'||e->op==TOK_LE)&&integer_constant(e->right,&constant)&&!constant&&
           e->left->type.base==TY_LONG&&!e->left->type.pointers){
            unsigned positive=e->op=='>'?yes:no,other=e->op=='>'?no:yes;
            /* The sign and every nonzero high word decide without testing the low word */
            emit_value(e->left);
            code("    cpx #0\n    bmi cg_%s_%u\n    bne cg_%s_%u\n    cmp #0\n",
                 cg.parser->unit,other,cg.parser->unit,positive);
            flag_branch("bne","beq",positive,other,fallthrough);return;
        }
        if((negative||e->op==TOK_GE||e->op==TOK_LE)&&integer_constant(zero,&constant)&&!constant&&
           value->type.base==TY_LONG&&!value->type.pointers){
            if(value->kind==EX_BINARY&&(value->op=='&'||value->op=='|')&&
               !direct_operand(value->left,t,1,0)&&!direct_operand(value->right,t,1,0)&&
               literal_integer_tree(value)){
                unsigned next=++cg.label;
                int either=value->op=='|';
                unsigned early=either==negative?yes:no;
                emit_long_high_word(value->left,t);
                flag_branch(either?"bmi":"bpl",either?"bpl":"bmi",early,next,next);
                label(next);value=value->right;
            }
            emit_long_high_word(value,t);
            flag_branch(negative?"bmi":"bpl",negative?"bpl":"bmi",yes,no,fallthrough);
            return;
        }
    }
    if(!cg.parser->no_strength_reduction&&!cg.parser->no_indexed_operands&&
       !cg.retained_index&&!cg.retained_second&&!cg.scan_cursor&&
       t.base==TY_LONG&&!t.pointers&&(e->op==TOK_EQ||e->op==TOK_NE)&&indirect_near_long(e->left)&&
       !volatile_expression(e)&&integer_constant(e->right,&constant)){
        unsigned offset=assign_base_x(e->left);
        int equal=e->op==TOK_EQ;
        code("    lda a:$%04X,x\n",offset);
        if(!constant)code("    ora a:$%04X,x\n",offset+2);
        else{
            if(constant&65535)code("    cmp #$%04X\n",constant&65535);
            code("    beq :+\n");jump(equal?no:yes);code(":\n    lda a:$%04X,x\n",offset+2);
            if(constant>>16)code("    cmp #$%04X\n",constant>>16);
        }
        flag_branch(equal?"beq":"bne",equal?"bne":"beq",yes,no,fallthrough);
        return;
    }
    if(!cg.parser->no_strength_reduction&&!t.pointers&&t.base==TY_LONG&&
       (e->op==TOK_EQ||e->op==TOK_NE)){
        Expr *value=integer_constant(e->right,&constant)&&!constant?e->left:
                    integer_constant(e->left,&constant)&&!constant?e->right:NULL;
        uint32_t high;
        if(!value&&!volatile_expression(e->left)&&e->left->type.base==TY_LONG&&
           !e->left->type.pointers&&integer_constant(e->right,&constant)&&
           fixed_memory_word(e->left,4,0,0)&&!known_high_word(e->left,&high)&&
           !recent_frame_high_store(e->left)){
            int equal=e->op==TOK_EQ;
            code("    lda ");fixed_memory_word(e->left,4,0,1);code("\n");
            if(constant&65535)code("    cmp #$%04X\n",constant&65535);
            code("    beq :+\n");jump(equal?no:yes);code(":\n    lda ");
            fixed_memory_word(e->left,4,2,1);code("\n");
            if(constant>>16)code("    cmp #$%04X\n",constant>>16);
            flag_branch(equal?"beq":"bne",equal?"bne":"beq",yes,no,fallthrough);
            return;
        }
        if(value&&value->type.base==TY_LONG&&!value->type.pointers&&
           (volatile_expression(value)||(fixed_memory_word(value,4,0,0)&&!known_high_word(value,&high)))){
            if(volatile_expression(value)&&fixed_memory_word(value,4,0,0)){
                code("    lda ");fixed_memory_word(value,4,0,1);
                code("\n    ora ");fixed_memory_word(value,4,2,1);code("\n");
            }else truth(value);
            flag_branch(e->op==TOK_EQ?"beq":"bne",e->op==TOK_EQ?"bne":"beq",yes,no,fallthrough);
            return;
        }
    }
    if(!floating&&!t.pointers&&volatile_expression(e)&&fixed_memory_word(e->right,4,0,0)){
        int equality=e->op==TOK_EQ||e->op==TOK_NE;
        emit_value(e->left);convert_registers(e->left->type,t);
        if(equality)code("    eor ");
        else code(e->op=='>'||e->op==TOK_LE?"    clc\n    sbc ":"    sec\n    sbc ");
        fixed_memory_word(e->right,4,0,1);code("\n");
        if(equality){
            cg.arithmetic=1;
            code("    sta z:__arith_lhs\n    txa\n    eor ");
        }else code("    txa\n    sbc ");
        fixed_memory_word(e->right,4,2,1);code("\n");
        if(equality){
            code("    ora z:__arith_lhs\n");
            flag_branch(e->op==TOK_EQ?"beq":"bne",e->op==TOK_EQ?"bne":"beq",yes,no,fallthrough);
        }else{
            if(!t.is_unsigned)code("    bvc :+\n    eor #$8000\n:\n");
            integer_relation_flags(e->op,!t.is_unsigned,yes,no,fallthrough);
        }
        return;
    }
    if(!volatile_expression(e)&&!floating&&!t.pointers&&(e->op==TOK_EQ||e->op==TOK_NE)&&direct_operand(e->right,t,0,0)&&direct_operand(e->right,t,1,0)){
        uint32_t high,right;
        emit_value(e->left);convert_registers(e->left->type,t);
        if(known_high_word(e->left,&high)&&integer_constant(e->right,&right)){
            if(high!=(right>>16)){unsigned target=e->op==TOK_EQ?no:yes;if(target!=fallthrough)jump(target);return;}
            code("    cmp ");direct_operand(e->right,t,0,1);code("\n");
            flag_branch(e->op==TOK_EQ?"beq":"bne",e->op==TOK_EQ?"bne":"beq",yes,no,fallthrough);return;
        }
        /* A zero low word needs only Z, which a full-width producer of A set */
        if(!(integer_constant(e->right,&right)&&!(right&0xFFFF)&&accumulator_zero_flags())){
            code("    cmp ");direct_operand(e->right,t,0,1);code("\n");
        }
        code("    beq :+\n");jump(e->op==TOK_EQ?no:yes);code(":\n");
        if(integer_constant(e->right,&right))code("    cpx #$%04X\n",right>>16);
        else{code("    txa\n    cmp ");direct_operand(e->right,t,1,1);code("\n");}
        flag_branch(e->op==TOK_EQ?"beq":"bne",e->op==TOK_EQ?"bne":"beq",yes,no,fallthrough);return;
    }
    if(!cg.parser->no_strength_reduction&&!floating&&!t.pointers&&!volatile_expression(e)&&
       e->op!=TOK_EQ&&e->op!=TOK_NE&&direct_operand(e->right,t,0,0)&&direct_operand(e->right,t,1,0)){
        Expr *left=e->left,*right=e->right;
        int op=e->op,direct=direct_operand(left,t,0,0)&&direct_operand(left,t,1,0);
        int strict=op=='>'||op==TOK_LE;
        if(t.base==TY_LONG&&integer_constant(right,&constant)&&(constant&65535)==(strict?65535u:0u)){
            /* The low-word subtraction has a constant borrow at this boundary */
            if(direct){code("    lda ");direct_operand(left,t,1,1);code("\n");}
            else{emit_value(left);convert_registers(left->type,t);code("    txa\n");}
            if(t.is_unsigned&&!strict)code("    cmp #$%04X\n",constant>>16);
            else code(strict?"    clc\n    sbc #$%04X\n":"    sec\n    sbc #$%04X\n",constant>>16);
            if(!t.is_unsigned)code("    bvc :+\n    eor #$8000\n:\n");
            integer_relation_flags(op,!t.is_unsigned,yes,no,fallthrough);return;
        }
        if(direct&&t.is_unsigned&&t.base==TY_LONG){unsigned_long_order(left,right,t,op,yes,no,fallthrough);return;}
        if(direct){code("    lda ");direct_operand(left,t,0,1);code("\n");}
        else{emit_value(left);convert_registers(left->type,t);}
        /* Subtract an extra one for <= and >, so equality belongs to the lower side */
        code(op=='>'||op==TOK_LE?"    clc\n    sbc ":"    sec\n    sbc ");
        direct_operand(right,t,0,1);code("\n");
        if(direct){code("    lda ");direct_operand(left,t,1,1);code("\n");}
        else code("    txa\n");
        code("    sbc ");direct_operand(right,t,1,1);code("\n");
        if(!t.is_unsigned)code("    bvc :+\n    eor #$8000\n:\n");
        integer_relation_flags(op,!t.is_unsigned,yes,no,fallthrough);
        return;
    }
    if(!cg.parser->no_strength_reduction&&!volatile_expression(e)&&
       ((!t.pointers&&t.base==TY_LONG)||(far_pointer(t)&&(e->op==TOK_EQ||e->op==TOK_NE)))){
        emit_value(e->left);convert_registers(e->left->type,t);push_value(t);
        emit_value(e->right);convert_registers(e->right->type,t);stage(1,t);
        if(cg.stack_leaf)cg.stack_bias-=4;
        if(e->op==TOK_EQ||e->op==TOK_NE){
            code("    pla\n    eor z:__arith_rhs\n    sta z:__arith_rhs\n"
                 "    pla\n    eor z:__arith_rhs+2\n    ora z:__arith_rhs\n");
            flag_branch(e->op==TOK_EQ?"beq":"bne",e->op==TOK_EQ?"bne":"beq",yes,no,fallthrough);
            return;
        }
        code(e->op=='>'||e->op==TOK_LE?"    clc\n":"    sec\n");
        code("    pla\n    sbc z:__arith_rhs\n    pla\n    sbc z:__arith_rhs+2\n");
        if(!t.is_unsigned)code("    bvc :+\n    eor #$8000\n:\n");
        integer_relation_flags(e->op,!t.is_unsigned,yes,no,fallthrough);
        return;
    }
    if(!t.pointers&&stage_expression(e->left,t,0,0)&&stage_expression(e->right,t,1,0)){
        stage_expression(e->left,t,0,1);stage_expression(e->right,t,1,1);
    }else{
        emit_value(e->left);convert_registers(e->left->type,t);
        if(!t.pointers&&stage_expression(e->right,t,1,0)){
            stage(0,t);stage_expression(e->right,t,1,1);
        }else{
            push_value(t);emit_value(e->right);convert_registers(e->right->type,t);
            stage(1,t);pop_value(t);stage(0,t);
        }
    }
    helper(floating?(e->op==TOK_EQ||e->op==TOK_NE?"__fcmp32_equal":"__fcmp32"):(t.is_unsigned||t.pointers)?"__ucmp32":"__scmp32");
    switch(e->op){
    case TOK_EQ:case TOK_NE:
        code("    cmp #0\n");flag_branch(e->op==TOK_EQ?"beq":"bne",e->op==TOK_EQ?"bne":"beq",yes,no,fallthrough);break;
    case '<':case '>':
        code("    cmp #$%04X\n",e->op=='<'?65535:1);flag_branch("beq","bne",yes,no,fallthrough);break;
    default:
        if(!floating){
            code("    cmp #$%04X\n",e->op==TOK_LE?1:65535);flag_branch("bne","beq",yes,no,fallthrough);
        }else{
            /* Less, equal, greater and unordered return -1, 0, 1 and 2 */
            if(e->op==TOK_LE)code("    inc a\n");
            code("    cmp #2\n");flag_branch("bcc","bcs",yes,no,fallthrough);
        }break;
    }
}
static void load_argument(Expr *e,int x)
{
    if(x)emit_value_x(e);
    else if(constant_address(e)&&reg_width(e->type)==2){code("    lda #");immediate(e,0);code("\n");}
    else emit_value(e);
}
/* Unsigned word shifts commute with an offset aligned to the discarded bits.
 * The shifted result wraps at 2^(16-count), even if the original sum wraps. */
static int word_shift_pair(Expr *left,Expr *right,unsigned *delta,unsigned *mask)
{
    Expr *offset;
    uint32_t count,other,amount;
    if(cg.parser->no_strength_reduction||cg.parser->no_value_reuse||
       left->kind!=EX_BINARY||right->kind!=EX_BINARY||
       left->op!=TOK_SHR||right->op!=TOK_SHR||
       !word_integer(left->type)||!left->type.is_unsigned||
       !word_integer(right->type)||!right->type.is_unsigned||
       !integer_constant(left->right,&count)||count<3||count>15||
       !integer_constant(right->right,&other)||count!=other)return 0;
    offset=word_bits(right->left);
    if(offset->kind!=EX_BINARY||(offset->op!='+'&&offset->op!='-')||
       !word_integer(offset->type)||!integer_constant(offset->right,&amount)||
       (amount&((1u<<count)-1))||!body_equal(word_bits(left->left),word_bits(offset->left))||
       body_effect(left)||body_effect(right))return 0;
    *mask=65535u>>count;
    *delta=((offset->op=='+'?amount:0u-amount)&65535u)>>count;
    return 1;
}
static void load_word_pair(Expr *left,Expr *right)
{
    unsigned delta,mask;
    if(word_shift_pair(left,right,&delta,&mask)){
        code("; shared unsigned word shift\n");
        emit_value(left);
        code("    tax\n");
        if(delta==1)code("    inc a\n");
        else if(delta==mask)code("    dec a\n");
        else if(delta)code("    clc\n    adc #$%04X\n",delta);
        if(delta)code("    and #$%04X\n",mask);
    }else if(!cg.parser->no_strength_reduction&&word_preserves_x(right)&&!body_effect(left)&&!body_effect(right)){
        load_argument(left,1);load_argument(right,0);
    }else{load_argument(right,0);code("    pha\n");load_argument(left,1);code("    pla\n");}
}
static int bank_call(Expr *e);
static int short_memset(Expr *e,int needed);
static int literal_strcpy(Expr *e);
static int literal_sprintf(Expr *e,int needed);
static String *scalar_string_literal(Expr *e);
#include "near_libcalls.inc"
/* Qualifier-only pointer casts do not change the pushed representation.
 * Read simple far homes directly, retaining all four bytes of the public ABI.
 * A real near object address uses the same non-NULL $7E conversion as emit_value. */
static int direct_call_argument(Expr *e)
{
    Expr *root=e,*home;unsigned w=reg_width(e->type),offset=0;
    if(cg.parser->no_strength_reduction)return 0;
    while(root->kind==EX_CAST&&value_type(root->type).pointers&&value_type(root->left->type).pointers&&
          far_pointer(value_type(root->type))==far_pointer(value_type(root->left->type)))root=root->left;
    if(constant_address(root)||(root->kind==EX_OBJECT&&root->type.array&&!root->symbol->owner)){
        if(w==4){code("    pea ");immediate(root,1);code("\n");}
        code("    pea ");immediate(root,0);code("\n");return 1;
    }
    if(w==4&&root->kind==EX_CAST&&!root->type.pointers&&root->type.base!=TY_FLOAT){
        Expr *inner=root->left;
        while(inner->kind==EX_CAST&&value_type(inner->type).pointers&&value_type(inner->left->type).pointers&&
              far_pointer(value_type(inner->type))==far_pointer(value_type(inner->left->type)))inner=inner->left;
        if(far_pointer(value_type(inner->type))&&
           (constant_address(inner)||(inner->kind==EX_OBJECT&&inner->type.array&&!inner->symbol->owner))){
            code("    pea ");immediate(inner,1);code("\n    pea ");immediate(inner,0);code("\n");return 1;
        }
    }
    if(w==4&&far_pointer(value_type(root->type))){
        String *literal=scalar_string_offset(root,&offset);
        if(literal){
            literal->used=1;
            code("    pea .bankbyte(str_%s_%u+$%X)\n    pea .loword(str_%s_%u+$%X)\n",
                 cg.parser->unit,literal->id,offset,cg.parser->unit,literal->id,offset);
            return 1;
        }
    }
    if(far_pointer(value_type(root->type))&&root->kind==EX_CAST&&
       value_type(root->left->type).pointers&&!far_pointer(value_type(root->left->type))&&
       (near_object_address(root->left,&offset)||root->left->known_nonnull)){
        Symbol *s=near_object_address(root->left,&offset);
        if(s&&!s->owner){s->used=1;code("; fixed near object argument\n    pea $007E\n    pea .loword(_%s+$%04X)\n",s->asm_name,offset);}
        else{emit_value(root->left);code("    pea $007E\n    pha\n");}
        return 1;
    }
    home=far_compare_home(root);
    if(home){
        code("    lda ");array_operand(home->symbol,2);code("\n    pha\n");if(cg.stack_leaf)cg.stack_bias+=2;
        code("    lda ");array_operand(home->symbol,0);code("\n    pha\n");if(cg.stack_leaf)cg.stack_bias+=2;
        return 1;
    }
    return 0;
}
static int call_register(Expr *e,unsigned i)
{
    if(e->left){
        FunctionType *t=value_type(e->left->type).signature;
        return (!t->variadic||i<(unsigned)t->count)&&register_parameter(i,e->args[i]->type);
    }
    return register_argument(e->symbol,i,e->args[i]);
}
static void push_aggregate_argument(Expr *e)
{
    unsigned size=width(e->type),offset;
    if(!cg.parser->no_copy_selection&&!cg.stack_leaf&&size>12&&size<=65535&&
       !e->type.banked&&!volatile_type(e->type)&&direct_memory_object(e,&offset)){
        emit_address_x(e);
        /* S addresses bank-zero WRAM. Publish the argument above S while Y
         * and the caller's data bank are saved outside the argument bytes. */
        cg.arithmetic=1;
        code("; outgoing aggregate: mvn %u bytes\n"
             "    sty z:__arith_rhs\n    tsc\n    sec\n    sbc #$%04X\n    tcs\n"
             "    inc a\n    tay\n    phb\n    lda #$%04X\n    mvn #$7E, #$00\n"
             "    plb\n    ldy z:__arith_rhs\n",size,size,size-1);
        return;
    }
    /* Six short word pushes avoid the far-address setup and loop overhead */
    if(!cg.parser->no_copy_selection&&!cg.stack_leaf&&size<=12&&!volatile_type(e->type)){
        Symbol *source=direct_memory_object(e,&offset);
        if(source||!e->type.banked){
            if(!source)emit_address_x(e);
            for(unsigned part=size;part;part-=2){
                code("    lda ");
                if(source)array_operand(source,offset+part-2);else code("a:$%04X,x",part-2);
                code("\n    pha\n");
            }
            return;
        }
    }
    unsigned loop=++cg.label;
    Type address=far_type(type(TY_CHAR,1));
    emit_address(e);
    if(!e->type.banked)code("    ldx #$007E\n");
    stage(0,address);
    if(volatile_type(e->type)){
        code("    sty z:__arith_rhs+4\n    tsc\n    sec\n    sbc #$%04X\n    tcs\n"
             "    inc a\n    sta z:__arith_rhs\n    stz z:__arith_rhs+2\n"
             "    ldy #0\n    sep #$20\n.a8\n",width(e->type));
        label(loop);
        code("    lda [__arith_lhs],y\n    sta [__arith_rhs],y\n    iny\n    cpy #$%04X\n"
             "    bcc cg_%s_%u\n    rep #$20\n.a16\n    ldy z:__arith_rhs+4\n",
             width(e->type),cg.parser->unit,loop);
        return;
    }
    code("    sty z:__arith_rhs\n    ldy #$%04X\n",width(e->type)-2);
    label(loop);
    code("    lda [__arith_lhs],y\n    pha\n    dey\n    dey\n    cpy #$FFFE\n"
         "    bne cg_%s_%u\n    ldy z:__arith_rhs\n",cg.parser->unit,loop);
}
static void push_wide_argument(Expr *e)
{
    unsigned part,offset;
    Symbol *home;
    if(!cg.parser->no_strength_reduction&&!cg.stack_leaf){
        if(e->kind==EX_INT){
            uint64_t bits=((uint64_t)e->value_high<<32)|e->value;
            for(part=8;part;part-=2)code("    pea $%04X\n",(unsigned)(bits>>(8*(part-2)))&65535);
            return;
        }
        if(!volatile_expression(e)&&(home=wide_fixed_home(e,&offset))){
            for(part=8;part;part-=2){
                code("    lda ");array_operand(home,offset+part-2);code("\n    pha\n");
            }
            return;
        }
        if((e->kind==EX_MEMBER||e->kind==EX_DEREF)&&!e->type.banked&&
           wide_scalar(value_type(e->type))&&!volatile_expression(e)){
            emit_address_x(e);
            for(part=8;part;part-=2)code("    lda a:$%04X,x\n    pha\n",part-2);
            return;
        }
    }
    emit_wide_operand(e);
    for(part=8;part;part-=2)code("    lda z:__arith_lhs+%u\n    pha\n",part-2);
}
static void bound_mark(void);
static void bound_emit(const char *instruction,const char *operand);
static void emit_call(Expr *e,int needed)
{
    if(e->string){
        const char *p=(char *)e->string->bytes;
        while(*p){while(isspace((unsigned char)*p))++p;if(*p){code("    %.3s\n",p);p+=3;}}
        cg.divmod_available=0;return;
    }
    if(!e->left){
        if(near_library_call(e))return;
        if(short_memset(e,needed))return;
        if(literal_strcpy(e))return;
        if(literal_sprintf(e,needed))return;
        if(bank_call(e))return;
    }
    unsigned i,bytes=0,continuation=0;int aggregate=structure_object(e->type);
    {
        int variadic=e->left?(value_type(e->left->type).signature->variadic||value_type(e->left->type).signature->count<0):
            (e->symbol->variadic||e->symbol->old_style);
        int formatting=e->left||!strcmp(e->symbol->name,"printf")||
            !strcmp(e->symbol->name,"sprintf")||!strcmp(e->symbol->name,"snprintf");
        if(variadic&&formatting)for(i=0;i<e->arg_count;++i){
            Type argument=value_type(e->args[i]->type);
            if(!argument.pointers&&argument.base==TY_DOUBLE)cg.require_float_format=1;
            if(!argument.pointers&&argument.base==TY_LONGLONG)cg.require_int64_format=1;
        }
    }
    int rx=e->arg_count&&call_register(e,0);
    int ra=e->arg_count>1&&call_register(e,1);
    if(e->left){
        continuation=++cg.label;
        code("    phy\n    phk\n    pea .loword(cg_%s_%u-1)\n",cg.parser->unit,continuation);
    }
    for(i=e->arg_count;i;--i)if(!call_register(e,i-1)){
        Expr *a=e->args[i-1];unsigned w=argument_width(a->type);bytes+=w;
        if(structure_object(value_type(a->type)))push_aggregate_argument(a);
        else if(w==8)push_wide_argument(a);
        else if(direct_call_argument(a)){}
        else if(constant_address(a)){
            if(w==4){code("    pea ");immediate(a,1);code("\n");}
            code("    pea ");immediate(a,0);code("\n");
        }else{emit_value(a);push_value(a->type);}
    }
    if(aggregate){emit_address(e->third);code("    pha\n");bytes+=2;}
    if(e->left){emit_value(e->left);push_value(e->left->type);}
    if(rx&&ra&&!constant_address(e->args[1])){
        load_word_pair(e->args[0],e->args[1]);
    }else{if(rx)load_argument(e->args[0],1);if(ra)load_argument(e->args[1],0);}
    if(e->left){
        cg.arithmetic=1;
        /* Keep the callee address on the stack while evaluating register args.
         * Y identifies the synthetic long return below the outgoing arguments. */
        code("    pha\n    phx\n    lda 5,s\n    sta z:__arith_rhs\n"
             "    lda 7,s\n    sta z:__arith_rhs+2\n    plx\n    pla\n    ply\n    ply\n"
             "    pha\n    tsc\n    clc\n    adc #$%04X\n    tay\n    pla\n"
             "    jml [__arith_rhs]\n",bytes+2);
        label(continuation);code("    ply\n");
        if(aggregate&&needed)emit_address(e->third);
        cg.divmod_available=0;return;
    }
    e->symbol->used=1;
    {
        char name[132];
        int save_cursor=cg.bound&&!e->arg_count&&!aggregate&&!needed;
        snprintf(name,sizeof name,"_%s",e->symbol->asm_name);
        if(save_cursor){code("    phx\n");bound_mark();}
        if(e->symbol->param_count<0&&bytes&&!aggregate&&!rx&&!ra)
            code("; unprototyped stack arguments: %s\n",e->symbol->asm_name);
        call_entry(name);
        if(save_cursor)bound_emit("plx",NULL);
    }
    if(aggregate){
        if(bytes>=6)code("    tsc\n    clc\n    adc #$%04X\n    tcs\n",bytes);
        else while(bytes){code("    plx\n");bytes-=2;}
        if(needed)emit_address(e->third);
    }else if(!cg.parser->no_strength_reduction&&(!needed||(!e->type.pointers&&e->type.base==TY_VOID))){
        if(bytes>=6)code("; discarded-result argument cleanup\n    tsc\n    clc\n    adc #$%04X\n    tcs\n",bytes);
        else while(bytes){code("    plx\n");bytes-=2;}
    }else{
        cleanup(bytes,e->type);
        /* C Boolean returns are normalized in the callee's word result */
        if(needed!=CALL_LOW_BYTE&&(!e->type.is_bool||cg.parser->no_strength_reduction))narrow_char(e->type);
    }
    cg.divmod_available=0;
}
static int word_preserves_x(Expr *e)
{
    unsigned offset,bits;int neg;uint32_t factor;WordScale plan;
    if(volatile_expression(e)||reg_width(e->type)!=2)return 0;
    if(dot_match_expr(e))return dot_preserves_x(e);
    if(e->kind==EX_INT||e->kind==EX_STRING||e->kind==EX_OBJECT)return 1;
    if((e->kind==EX_MEMBER||e->kind==EX_DEREF)&&!e->type.array&&
       fixed_memory_object(e,&offset))return 1;
    if(e->kind==EX_CAST)return word_preserves_x(e->left);
    if(e->kind==EX_UNARY&&(e->op=='+'||e->op=='-'||e->op=='~'))return word_preserves_x(e->left);
    if(e->kind==EX_BINARY&&!e->type.pointers&&e->type.base!=TY_FLOAT){
        if(basic_integer_op(e->op))return word_preserves_x(e->left)&&word_preserves_x(e->right);
        if((e->op==TOK_SHL||e->op==TOK_SHR)&&integer_constant(e->right,&bits)&&bits<16)
            return word_preserves_x(e->left);
        if((e->op=='/'||e->op=='%')&&power_divisor(e->right,e->type,&bits,&neg))
            return word_preserves_x(e->left);
        if(e->op=='*'&&word_preserves_x(e->left)&&word_preserves_x(e->right)&&
           ((integer_constant(e->right,&factor)&&word_scale_plan(factor,1,&plan))||
            arithmetic_byte_inputs('*',e->type,e->left,e->right)!=0))
            return 1;
    }
    return e->kind==EX_ADDRESS&&e->left->kind==EX_OBJECT;
}
static int simple_index(Expr *e)
{
    if(e->type.pointers||e->type.array||e->type.base==TY_FLOAT||reg_width(e->type)!=2)return 0;
    if(e->kind==EX_OBJECT||e->kind==EX_INT)return 1;
    if(e->kind==EX_CAST)return simple_index(e->left);
    return e->kind==EX_BINARY&&(e->op=='+'||e->op=='-')&&e->right->kind==EX_INT&&simple_index(e->left)&&simple_index(e->right);
}
static int indexed_pointer_sum(Expr *e)
{
    Symbol *s;Type element;unsigned scale;
    Expr *index=e->right;
    uint32_t constant;
    if(strength_pointer(e,0))return 1;
    if(e->op!='+'||e->left->kind!=EX_OBJECT||
       (!simple_index(index)&&(cg.parser->no_strength_reduction||index->type.base!=TY_LONG||
                               integer_constant(index,&constant)||!readonly_integer_expression(index))))return 0;
    s=e->left->symbol;if(s->type.array||!s->type.pointers||far_pointer(s->type))return 0;
    element=pointed_type(s->type);scale=width(element);
    if(scale!=1&&scale!=2&&scale!=4){
        WordScale plan;
        if(cg.parser->no_strength_reduction||!scale||scale>65535||index->kind!=EX_OBJECT||
           !word_integer(index->type)||!fixed_memory_word(e->left,2,0,0)||
           !word_scale_plan(scale,!direct_operand(index,type(TY_INT,0),0,0),&plan))return 0;
        /* The incoming register base can feed the staged path directly.
         * A memory operand here would force a parameter spill and frame. */
        if(incoming_word_parameter(s))return 0;
    }
    /* Pure scalar operands let the scaled index consume A before the
     * base is read. The near address uses only the low word. */
    emit_value(index);
    strength_scale(scale,index);
    code("    clc\n    adc ");array_operand(s,0);code("\n");
    return 1;
}
static int fixed_near_pointer_sum(Expr *e)
{
    Symbol *s;
    unsigned offset,stride;
    uint32_t bits;
    int64_t index,displacement;
    Type pointer=value_type(e->type),term;
    if(cg.parser->no_strength_reduction||e->kind!=EX_BINARY||
       (e->op!='+'&&e->op!='-')||!pointer.pointers||far_pointer(pointer)||
       !(s=near_object_address(e->left,&offset))||s->owner||width(s->type)>65536||
       !integer_constant(e->right,&bits))return 0;
    term=e->right->type;
    index=term.is_unsigned?(int64_t)bits:(int64_t)(int32_t)bits;
    stride=width(pointed_type(value_type(e->left->type)));
    if(!stride||stride>65535)return 0;
    displacement=(int64_t)offset+(e->op=='+'?index:-index)*stride;
    if(displacement<0||displacement>=width(s->type))return 0;
    s->used=1;
    code("    lda #.loword(_%s+$%04X)\n",s->asm_name,(unsigned)displacement);
    return 1;
}
static int near_address_scaled_sum(Expr *e)
{
    Expr *base,*idx;Symbol *s;unsigned offset,stride;Type ptr=value_type(e->type);
    if(cg.parser->no_strength_reduction||e->kind!=EX_BINARY||e->op!='+'||
       !ptr.pointers||far_pointer(ptr))return 0;
    if(value_type(e->left->type).pointers){base=e->left;idx=e->right;}
    else if(value_type(e->right->type).pointers){base=e->right;idx=e->left;}
    else return 0;
    stride=width(pointed_type(value_type(base->type)));
    if(!stride||stride>65535||reg_width(idx->type)>2||volatile_expression(idx)||
       idx->type.pointers||!numeric(idx->type)||idx->type.base==TY_FLOAT)return 0;
    s=near_object_address(base,&offset);
    if(!s||s->owner||s->type.banked)return 0;
    uint32_t bias;
    if(idx->kind==EX_BINARY&&(idx->op=='+'||idx->op=='-')&&reg_width(idx->type)==2&&
       reg_width(idx->left->type)==2&&integer_constant(idx->right,&bias)){
        /* Both the index and the near address use word arithmetic. Fold
         * the scaled index bias into the relocated low word of the base. */
        offset=(offset+(idx->op=='+'?bias:0u-bias)*stride)&65535u;
        idx=idx->left;
    }
    s->used=1;
    emit_value(idx);
    strength_scale(stride,idx);
    code("    clc\n    adc #.loword(_%s+$%04X)\n",s->asm_name,offset);
    return 1;
}
static int store_previous_element(Expr *e)
{
    Expr *destination,*source,*index;unsigned size=width(e->type);
    if(e->left->type.banked||e->right->type.banked||e->op||e->left->kind!=EX_DEREF||e->right->kind!=EX_DEREF||size>2)return 0;
    destination=e->left->left;source=e->right->left;
    if(destination->kind!=EX_BINARY||source->kind!=EX_BINARY||destination->op!='+'||source->op!='+')return 0;
    if(destination->left->kind!=EX_OBJECT||source->left->kind!=EX_OBJECT||
       destination->left->symbol!=source->left->symbol)return 0;
    if(destination->right->kind!=EX_OBJECT||!simple_index(destination->right))return 0;
    index=source->right;
    if(index->kind!=EX_BINARY||index->op!='-'||index->left->kind!=EX_OBJECT||
       index->left->symbol!=destination->right->symbol||index->right->kind!=EX_INT||
       index->right->type.base==TY_FLOAT||index->right->value!=1)return 0;
    /* p[j] = p[j-1]: both indices/bases are pure object reads. Compute the
     * source once and reuse X for the adjacent destination. */
    emit_value_x(source);load_indirect(e->type,strength_wram_pointer(source));
    if(size==1)code("    sep #$20\n.a8\n");
    code("    sta %s:$%04X,x\n",strength_wram_pointer(destination)?"z":"a",size);
    if(size==1)code("    rep #$20\n.a16\n");
    return 1;
}
#include "strength.inc"
#include "lftr.inc"
static int loop_private(Symbol *s);
static unsigned scalar_writes(Statement *s,Symbol *v);
static unsigned scalar_writes_expr(Expr *e,Symbol *v);
#include "numeric_loops.inc"
/* Reordering a pure RHS across the home read is safe. C calls and writes
 * retain the established snapshot-before-RHS order, including aliases. */
static int home_rhs_pure(Expr *e)
{
    unsigned i;if(!e)return 1;
    if(volatile_expression(e))return 0;
    if(e->kind==EX_CALL||e->kind==EX_ASSIGN||e->kind==EX_PRE||e->kind==EX_POST)return 0;
    if(!home_rhs_pure(e->left)||!home_rhs_pure(e->right)||!home_rhs_pure(e->third))return 0;
    for(i=0;i<e->arg_count;++i)if(!home_rhs_pure(e->args[i]))return 0;
    return 1;
}
/* These exact X-load paths leave A intact. Stack-relative homes and general
 * address arithmetic need A, so retain their normal snapshot/save sequence. */
static int address_x_preserves_a(Expr *e);
static int value_x_preserves_a(Expr *e)
{
    Expr *base;int delta;
    if(volatile_expression(e)||reg_width(e->type)!=2)return 0;
    if(e->kind==EX_CAST&&value_width(e->type)==2&&value_width(e->left->type)==2)
        return value_x_preserves_a(e->left);
    if(e->kind==EX_ADDRESS)return address_x_preserves_a(e->left);
    if(!cg.parser->no_strength_reduction&&near_small_offset(e,&base,&delta))return value_x_preserves_a(base);
    return e->kind==EX_OBJECT&&!e->type.array&&width(e->symbol->type)==2&&
        !e->symbol->type.banked&&e->symbol!=cg.scalar_first&&!(e->symbol->owner&&cg.stack_leaf);
}
static int address_x_preserves_a(Expr *e)
{
    Symbol *s;unsigned offset=0;
    if(e->type.banked||volatile_expression(e))return 0;
    if(e->kind==EX_DEREF){
        unsigned unused;Expr *base=near_displaced_deref(e,&unused);
        return value_x_preserves_a(base?base:e->left);
    }
    s=e->kind==EX_OBJECT?e->symbol:fixed_memory_object(e,&offset);
    return s&&(!s->owner||(!cg.stack_leaf&&s->offset+offset<=3));
}
static int destination_x_preserves_a(Expr *e)
{
    unsigned offset;int pointer;Expr *root;
    if(e->kind!=EX_MEMBER)return address_x_preserves_a(e);
    root=member_root(e,&offset,&pointer);
    return pointer?value_x_preserves_a(root):address_x_preserves_a(root);
}
static void store_home_result(Symbol *s,int needed)
{
    if(needed||reg_width(s->type)!=4){store_symbol(s);return;}
    code("    sta ");array_operand(s,0);code("\n    txa\n    sta ");array_operand(s,2);code("\n");
}
static int fixed_byte_assignment(Expr *e);
static int fixed_shift_assignment(Expr *e);
static Expr *indirect_long_base(Expr *e,unsigned *offset)
{
    Expr *base;
    int pointer;
    if(!indirect_near_long(e))return NULL;
    if(e->kind==EX_MEMBER){
        base=member_root(e,offset,&pointer);
        if(!pointer)return NULL;
    }else{
        base=near_displaced_deref(e,offset);
        if(!base){base=e->left;*offset=0;}
    }
    if(*offset>65533||base->kind!=EX_OBJECT||base->type.array||
       !base->type.pointers||far_pointer(base->type)||
       base->symbol==cg.scalar_first||base->symbol==cg.leaf_count)return NULL;
    return base;
}

static int shifted_indexed_long_bits(Expr *e)
{
    Expr *shift=e->left,*indexed=e->right;
    Symbol *home;
    unsigned at,offset;
    uint32_t count;
    const char *op;
    if(cg.parser->no_strength_reduction||cg.parser->no_byte_shuffles||cg.parser->no_indexed_operands||
       cg.retained_index||cg.retained_second||cg.scan_cursor||cg.numeric_index||
       e->type.base!=TY_LONG||e->type.pointers||(e->op!='^'&&e->op!='&'&&e->op!='|'))return 0;
    if(indexed->kind!=EX_DEREF){shift=e->right;indexed=e->left;}
    if(shift->kind!=EX_BINARY||shift->op!=TOK_SHR||shift->type.base!=TY_LONG||!shift->type.is_unsigned||
       !integer_constant(shift->right,&count)||count!=8||indexed->kind!=EX_DEREF||
       far_pointer(value_type(indexed->left->type))||!indirect_near_long(indexed)||body_effect(indexed)||
       !(home=direct_memory_object(shift->left,&at))||home->owner||home->type.banked)return 0;
    op=e->op=='^'?"eor":e->op=='&'?"and":"ora";
    offset=assign_base_x(indexed);
    code("    lda ");array_operand(home,at+1);
    code("\n    %s a:$%04X,x\n    pha\n    lda ",op,offset);array_operand(home,at+2);
    code("\n    xba\n    and #$00FF\n    %s a:$%04X,x\n    tax\n    pla\n",op,offset+2);
    return 1;
}
static int indirect_long_binary(Expr *e)
{
    unsigned left_offset,right_offset;
    Expr *left,*right;
    const char *op;
    if(cg.parser->no_strength_reduction||cg.parser->no_indexed_operands||
       cg.retained_index||cg.retained_second||cg.scan_cursor||cg.numeric_index||
       e->type.base!=TY_LONG||
       e->type.pointers||!basic_integer_op(e->op)||volatile_expression(e)||
       !(left=indirect_long_base(e->left,&left_offset))||
       !(right=indirect_long_base(e->right,&right_offset)))return 0;
    /* Plain pointer loads leave the two staged words intact */
    cg.arithmetic=1;
    emit_value_x(right);
    code("    lda a:$%04X,x\n    sta z:__arith_rhs\n"
         "    lda a:$%04X,x\n    sta z:__arith_rhs+2\n",right_offset,right_offset+2);
    if(!body_equal(left,right))emit_value_x(left);
    op=e->op=='+'?"adc":e->op=='-'?"sbc":e->op=='&'?"and":e->op=='|'?"ora":"eor";
    code("    lda a:$%04X,x\n",left_offset);
    if(e->op=='+'||e->op=='-')code("    %s\n",e->op=='+'?"clc":"sec");
    code("    %s z:__arith_rhs\n    pha\n    lda a:$%04X,x\n"
         "    %s z:__arith_rhs+2\n    tax\n    pla\n",op,left_offset+2,op);
    return 1;
}

static Symbol *near_word_address(Expr *address,unsigned *offset)
{
    *offset=0;
    for(;;){
        Type t=value_type(address->type);
        uint32_t index;
        if(!t.pointers||far_pointer(t))return NULL;
        if(address->kind==EX_OBJECT&&!address->type.array)return address->symbol;
        if(address->kind==EX_CAST||(address->kind==EX_DEREF&&address->type.array)){
            address=address->left;
        }else if(address->kind==EX_ADDRESS&&address->left->kind==EX_DEREF){
            address=address->left->left;
        }else if(address->kind==EX_BINARY&&(address->op=='+'||address->op=='-')&&
                 value_type(address->left->type).pointers&&
                 value_width(address->right->type)==2&&integer_constant(address->right,&index)){
            unsigned bytes=index*width(pointed_type(value_type(address->left->type)));
            *offset+=address->op=='+'?bytes:0u-bytes;
            address=address->left;
        }else return NULL;
    }
}

static int near_word_pair(Expr *e)
{
    Expr *left=word_bits(e->left),*right=word_bits(e->right);
    Symbol *base;
    unsigned a,b;
    int delta;
    const char *op;
    if(cg.parser->no_strength_reduction||cg.parser->no_indexed_operands||
       cg.retained_index||cg.retained_second||cg.scan_cursor||cg.numeric_index||
       !basic_integer_op(e->op)||!word_integer(e->type)||
       left->kind!=EX_DEREF||right->kind!=EX_DEREF||
       !word_integer(left->type)||!word_integer(right->type)||
       strength_wram_pointer(left->left)||strength_wram_pointer(right->left)||
       !(base=near_word_address(left->left,&a))||base!=near_word_address(right->left,&b))return 0;
    delta=(int)(int16_t)(b-a);
    if(delta<-3||delta>3)return 0;
    emit_value_x(left->left);
    code("    lda a:$0000,x\n");
    /* Move the low word of the pointer so it still wraps within its bank */
    for(int i=0;i<(delta<0?-delta:delta);++i)
        code("; near pointer wrap\n    %s\n",delta<0?"dex":"inx");
    if(e->op=='+'||e->op=='-')code("    %s\n",e->op=='+'?"clc":"sec");
    op=e->op=='+'?"adc":e->op=='-'?"sbc":e->op=='&'?"and":e->op=='|'?"ora":"eor";
    code("    %s a:$0000,x\n",op);
    return 1;
}

/* Advance the cursor before the read, while X still addresses the old slot */
static int advanced_cursor_load(Expr *e)
{
    Expr *address=e->left,*advance,*home;
    uint32_t back,forward;
    unsigned bytes;
    if(cg.parser->no_strength_reduction||cg.parser->no_register_cursors||
       cg.retained_index||cg.retained_second||cg.affine_active||cg.bound||
       cg.numeric_index||cg.scan_cursor||width(e->type)!=2||
       reg_width(e->type)!=2||e->type.banked||volatile_expression(e))return 0;
    while(address->kind==EX_CAST&&value_type(address->type).pointers&&
          !far_pointer(value_type(address->type))&&value_type(address->left->type).pointers&&
          !far_pointer(value_type(address->left->type)))address=address->left;
    if(address->kind!=EX_BINARY||address->op!='-'||!address->type.pointers||
       far_pointer(address->type)||!integer_constant(address->right,&back)||
       !back||back>3)return 0;
    advance=address->left;
    if(advance->kind!=EX_ASSIGN||advance->op!='+'||
       !same_type(advance->type,address->type)||!integer_constant(advance->right,&forward)||
       forward!=back)return 0;
    home=advance->left;
    bytes=(unsigned)back*width(pointed_type(address->type));
    if(!bytes||bytes>3||home->kind!=EX_OBJECT||!loop_private(home->symbol)||
       home->symbol==cg.scalar_first||home->symbol==cg.leaf_count)return 0;
    emit_value_x(home);
    code("    txa\n");
    for(unsigned i=0;i<bytes;++i)code("    inc a\n");
    store_symbol(home->symbol);divmod_written(home);
    load_indirect(e->type,0);
    return 1;
}

static Expr *unwrap_same_width_cast(Expr *e,unsigned w)
{
    while(e->kind==EX_CAST&&!e->type.pointers&&!e->type.array&&
          !e->type.is_bool&&e->type.base!=TY_FLOAT&&reg_width(e->type)==w)
        e=e->left;
    return e;
}
static int scalar_home_update(Expr *e,int needed)
{
    Symbol *s;Type t;unsigned w,offset;const char *instruction;
    if(e->kind!=EX_ASSIGN||!e->op||e->left->type.array)return 0;
    if(!cg.parser->no_strength_reduction&&e->type.base==TY_FLOAT&&!e->type.pointers&&
       (e->op=='+'||e->op=='-'||e->op=='*'||e->op=='/')&&
       (s=direct_memory_object(e->left,&offset))!=NULL&&
       stage_expression(e->left,e->type,0,0)&&
       (stage_expression(e->right,e->type,1,0)||
        (e->right->kind==EX_DEREF&&e->right->type.base==TY_FLOAT&&!e->right->type.pointers&&
         !volatile_expression(e->left)&&!body_effect(e->right)))){
        if(stage_expression(e->right,e->type,1,0)){
            stage_expression(e->left,e->type,0,1);stage_expression(e->right,e->type,1,1);
        }else{
            /* Read the pure indirect source first while both result registers
             * are free. The fixed left operand then stages without spilling. */
            emit_value(e->right);stage(1,e->type);stage_expression(e->left,e->type,0,1);
        }
        binary_loaded(e->op,e->type,0);
        if(needed)store_array_element(s,offset,e->type);
        else{code("    sta ");array_operand(s,offset);code("\n    txa\n    sta ");array_operand(s,offset+2);code("\n");}
        divmod_written(e->left);return 1;
    }
    if(e->left->kind!=EX_OBJECT)return 0;
    if(fixed_long_increment(e,needed)||(!needed&&(fixed_shift_assignment(e)||fixed_byte_assignment(e))))return 1;
    s=e->left->symbol;t=binary_operands(e->left,e->right,e->op);w=reg_width(t);
    if(volatile_expression(e)){
        uint32_t constant;
        if(!object_volatile(s->type)||s->type.pointers||s->type.base!=TY_INT||
           width(s->type)!=2||w!=2||!basic_integer_op(e->op)||
           !integer_constant(e->right,&constant))return 0;
        cg.divmod_available=0;
        load_symbol(s);
        register_binary(e->op,t,e->right);
        store_symbol(s);
        return 1;
    }
    if(!needed&&!cg.parser->no_strength_reduction&&!s->type.pointers&&s->type.base!=TY_FLOAT&&
       !t.pointers&&t.base!=TY_FLOAT&&width(s->type)==4&&w==4&&basic_integer_op(e->op)){
        uint32_t constant,shift_count;
        Expr *inner;
        if(integer_constant(e->right,&constant)){
            uint16_t lo=(uint16_t)constant,hi=(uint16_t)(constant>>16);
            if(e->op=='+'||e->op=='-'){
                if(lo){
                    code("    %s\n    lda ",e->op=='+'?"clc":"sec");
                    array_operand(s,0);code("\n    %s #$%04X\n    sta ",e->op=='+'?"adc":"sbc",lo);
                    array_operand(s,0);code("\n    lda ");array_operand(s,2);
                    code("\n    %s #$%04X\n    sta ",e->op=='+'?"adc":"sbc",hi);array_operand(s,2);code("\n");
                }else if(hi){
                    code("    %s\n    lda ",e->op=='+'?"clc":"sec");
                    array_operand(s,2);code("\n    %s #$%04X\n    sta ",e->op=='+'?"adc":"sbc",hi);
                    array_operand(s,2);code("\n");
                }
                return 1;
            }
            for(unsigned half=0;half<2;++half){
                uint16_t word=half?hi:lo;
                if((e->op=='^'||e->op=='|')&&!word)continue;
                if(e->op=='&'&&word==0xffffu)continue;
                if(e->op=='&'&&!word){
                    if(!s->owner&&!s->type.banked){code("    stz ");array_operand(s,half*2);code("\n");}
                    else{code("    lda #$0000\n    sta ");array_operand(s,half*2);code("\n");}
                }else if(e->op=='|'&&word==0xffffu){
                    code("    lda #$FFFF\n    sta ");array_operand(s,half*2);code("\n");
                }else{
                    code("    lda ");array_operand(s,half*2);
                    code("\n    %s #$%04X\n    sta ",e->op=='&'?"and":e->op=='|'?"ora":"eor",word);
                    array_operand(s,half*2);code("\n");
                }
            }
            return 1;
        }
        inner=unwrap_same_width_cast(e->right,4);
        if((e->op=='^'||e->op=='|'||e->op=='+'||e->op=='-')&&
           inner->kind==EX_BINARY&&inner->op==TOK_SHL&&
           integer_constant(inner->right,&shift_count)&&shift_count>=16&&shift_count<32){
            Expr *src=inner->left;
            unsigned rem=(unsigned)shift_count-16;
            while(src->kind==EX_CAST&&!src->type.pointers&&!src->type.array&&
                  !src->type.is_bool&&!src->left->type.pointers&&!src->left->type.array&&
                  !src->left->type.is_bool&&src->left->type.base!=TY_FLOAT&&
                  src->left->kind!=EX_BITFIELD&&width(src->type)>=width(src->left->type))
                src=src->left;
            if(!src->type.pointers&&!src->type.array&&src->type.base!=TY_FLOAT&&
               (width(src->type)<=2||direct_operand(src,src->type,0,0))){
                if(width(src->type)<=2){
                    emit_value(src);
                    convert_registers(value_type(src->type),type(TY_INT,0));
                }else{
                    code("    lda ");direct_operand(src,src->type,0,1);code("\n");
                }
                if(rem>=8){code("    xba\n    and #$FF00\n");rem-=8;}
                while(rem--)code("    asl a\n");
                if(e->op=='-')code("    eor #$FFFF\n    sec\n    adc ");
                else{
                    if(e->op=='+')code("    clc\n");
                    code("    %s ",e->op=='+'?"adc":e->op=='|'?"ora":"eor");
                }
                array_operand(s,2);code("\n    sta ");array_operand(s,2);code("\n");
                return 1;
            }
        }
    }
    if(!s->type.pointers&&s->type.base!=TY_FLOAT&&!t.pointers&&t.base!=TY_FLOAT&&width(s->type)>=2&&
       w==reg_width(s->type)&&basic_integer_op(e->op)&&home_rhs_pure(e->right)){
        emit_value(e->right);convert_registers(e->right->type,t);
        instruction=e->op=='+'?"adc":e->op=='-'?"sbc":e->op=='&'?"and":e->op=='|'?"ora":"eor";
        if(e->op=='-'){
            stage(1,t);code("    lda ");array_operand(s,0);code("\n    sec\n    sbc z:__arith_rhs\n");
        }else{
            if(e->op=='+')code("    clc\n");
            code("    %s ",instruction);array_operand(s,0);code("\n");
        }
        code("    sta ");array_operand(s,0);code("\n");
        if(w==4){
            if(e->op=='-'){code("    lda ");array_operand(s,2);code("\n    sbc z:__arith_rhs+2\n");}
            else{code("    txa\n    %s ",instruction);array_operand(s,2);code("\n");}
            code("    sta ");array_operand(s,2);code("\n");
            if(needed){code("    tax\n    lda ");array_operand(s,0);code("\n");}
        }
        return 1;
    }
    load_symbol(s);binary_after_left(e->left,e->right,e->op);
    if(!e->known_no_conversion)convert_registers(t,e->type);store_home_result(s,needed);return 1;
}
#include "shared_elements.inc"
#include "aggregate_copy.inc"
#include "dpage_access.inc"
#include "far.inc"
#include "selections.inc"
static int body_equal(Expr *a,Expr *b);
static int body_effect(Expr *e);
static int near_memory_update(Expr *e,int needed)
{
    Expr *target=e->left;unsigned offset=0;uint32_t one,count=1;int decrement,post,byte;
    IndexedOperand operand;
    Symbol *home;
    if(cg.parser->no_strength_reduction||volatile_expression(e)||!target||
       (!target->type.pointers&&target->type.base!=TY_INT&&target->type.base!=TY_CHAR)||
       width(target->type)>2||target->type.is_bool||target->type.banked||
       (target->kind!=EX_DEREF&&target->kind!=EX_MEMBER))return 0;
    if(target->kind==EX_DEREF&&far_pointer(value_type(target->left->type)))return 0;
    if(e->kind==EX_ASSIGN){
        if(!e->op&&!needed&&width(target->type)==1&&target->type.is_unsigned){
            Expr *value=e->right,*read;
            while(value->kind==EX_CAST&&!value->type.pointers&&!value->type.is_bool&&
                  (value->type.base==TY_CHAR||value->type.base==TY_INT))value=value->left;
            if(value->kind!=EX_BINARY||(value->op!='+'&&value->op!='-')||
               !integer_constant(value->right,&one)||one!=1||body_effect(target))return 0;
            read=value->left;
            while(read->kind==EX_CAST&&!read->type.pointers&&!read->type.is_bool&&
                  read->type.base==TY_INT&&width(read->type)>=width(target->type))read=read->left;
            if(!body_equal(target,read))return 0;
            decrement=value->op=='-';post=0;
        }else{
            if((e->op!='+'&&e->op!='-')||!integer_constant(e->right,&one))return 0;
            if(target->type.pointers){if(!one)return 0;}
            else if(one!=1)return 0;
            count=one;decrement=e->op=='-';post=0;
        }
    }else if(e->kind==EX_PRE||e->kind==EX_POST){decrement=e->op==TOK_DEC;post=e->kind==EX_POST;}
    else return 0;
    byte=width(target->type)==1;
    home=fixed_memory_object(target,&offset);
    if(target->type.pointers){
        unsigned delta=(count*increment_step(target->type))&65535u;
        if(!home){
            if(e->kind==EX_ASSIGN||target->kind!=EX_DEREF||far_pointer(target->type)||
               cg.retained_index||cg.retained_second)return 0;
            offset=assign_base_x(target);
            int wram=strength_wram_pointer(target->left);
            if((delta==1&&(!needed||post))||(delta==2&&needed&&post)){
                if(needed)load_indirect_at(target->type,wram,offset);
                for(unsigned i=0;i<delta;++i)
                    code("    %s %s:$%04X,x\n",decrement?"dec":"inc",wram?"z":"a",offset);
                divmod_written(target);
                return 1;
            }
            load_indirect_at(target->type,wram,offset);
            if(needed&&post)code("    pha\n");
            increment_value(target->type,e->op);
            code("    sta %s:$%04X,x\n",wram?"z":"a",offset);
            if(needed&&post)code("    pla\n");
            divmod_written(target);
            return 1;
        }
        if(home->type.banked)return 0;
        load_array_element(home,offset,target->type);
        if(needed&&post&&delta)code("    tax\n");
        if(delta==1)code("    %s a\n",decrement?"dec":"inc");
        else if(delta)code("    %s\n    %s #$%04X\n",decrement?"sec":"clc",decrement?"sbc":"adc",delta);
        if(delta){store_array_element(home,offset,target->type);divmod_written(target);}
        if(needed&&post&&delta)code("    txa\n");
        return 1;
    }
    if(home&&!home->owner&&!home->type.banked){
        if(byte)code("    sep #$20\n.a8\n");
        if(needed&&post){code("    lda ");array_operand(home,offset);code("\n");}
        code("    %s ",decrement?"dec":"inc");array_operand(home,offset);code("\n");
        if(needed&&!post){code("    lda ");array_operand(home,offset);code("\n");}
        if(byte)code("    rep #$20\n.a16\n");
        if(needed&&byte)narrow_char(e->type);
        divmod_written(target);return 1;
    }
    if(indexed_operand(target,&operand)&&
       (!indexed_retained(&operand,1)||operand.reg=='x')){
        indexed_index_mode(&operand,0);
        if(byte)code("    sep #$20\n.a8\n");
        if(needed&&post){code("    lda ");indexed_text(&operand);code("\n");}
        code("    %s ",decrement?"dec":"inc");indexed_text(&operand);code("\n");
        if(needed&&!post){code("    lda ");indexed_text(&operand);code("\n");}
        if(byte)code("    rep #$20\n.a16\n");
        indexed_finish(&operand);
        if(needed&&byte)narrow_char(e->type);
        divmod_written(target);return 1;
    }
    if(!needed&&home&&home->owner&&!home->type.banked&&!cg.stack_leaf&&!cg.scalar_leaf&&
       !cg.dp_homes&&!cg.loop_y_borrowed&&!cg.retained_index&&!cg.retained_second&&!cg.scan_cursor){
        /* RMW has an X-indexed form. Use the frame base and displacement
         * directly instead of adding the field's address into X. */
        require_frame_home(home);home->used=1;
        offset+=frame_offset(home->offset);
        code("    tyx\n");
    }else if(target->kind==EX_MEMBER){
        unsigned unused;int pointer;Expr *root=member_root(target,&unused,&pointer);
        if(pointer&&far_pointer(value_type(root->type)))return 0;
        offset=member_base_x(target);
    }else emit_address_x(target);
    if(byte)code("    sep #$20\n.a8\n");
    if(needed&&post)code("    lda a:$%04X,x\n",offset);
    code("    %s a:$%04X,x\n",decrement?"dec":"inc",offset);
    if(needed&&!post)code("    lda a:$%04X,x\n",offset);
    if(byte)code("    rep #$20\n.a16\n");
    if(needed&&byte)narrow_char(e->type);
    divmod_written(target);return 1;
}
/* Demand only the low word, or the high word after an unsigned >>16, of a
 * nonvolatile fixed 32-bit home. Casts retained here do not change its bits. */
static int project_word(Expr *e,unsigned bits)
{
    Expr *source=e;
    Symbol *s;
    unsigned offset=0,part=0;
    uint32_t count,n;
    if(source->kind==EX_BINARY&&!source->type.pointers&&source->type.base!=TY_FLOAT&&reg_width(source->type)==4&&
       (basic_integer_op(source->op))&&integer_constant(source->right,&n)&&
       project_word(source->left,bits)){
        int op=source->op;
        if(op=='+'||op=='-')code("    %s\n",op=='+'?"clc":"sec");
        if(op!='&'||(n&65535)!=(bits==8?255u:65535u))
            code("    %s #$%04X\n",op=='+'?"adc":op=='-'?"sbc":op=='&'?"and":op=='|'?"ora":"eor",n&65535);
        return 1;
    }
    if(source->kind==EX_BINARY&&source->op==TOK_SHR&&reg_width(source->left->type)==4&&
       integer_constant(source->right,&count)&&(count==16||(bits==8&&count==24))){
        part=(unsigned)count/8;source=source->left;
    }
    if(part&&source->kind==EX_CAST&&!source->type.pointers&&source->type.base==TY_LONG&&
       source->type.is_unsigned&&source->left->kind==EX_OBJECT&&
       value_type(source->left->type).pointers&&!far_pointer(value_type(source->left->type))&&
       !volatile_expression(source->left)){
        code("; zero-extended near pointer high word\n    lda #0\n");return 1;
    }
    while(source->kind==EX_CAST&&!source->type.pointers&&source->type.base!=TY_FLOAT&&
          reg_width(source->type)==4&&reg_width(source->left->type)==4&&
          (source->left->type.pointers||source->left->type.base!=TY_FLOAT))source=source->left;
    if(source->type.array||reg_width(source->type)!=4||(!source->type.pointers&&source->type.base==TY_FLOAT))return 0;
    s=source->kind==EX_OBJECT?source->symbol:fixed_memory_object(source,&offset);
    if(!s)return 0;
    code("; demanded word projection\n    lda ");array_operand(s,offset+(part&~1u));code("\n");
    if(part&1)code("    xba\n    and #$00FF\n");
    return 1;
}
static int demanded_word_projection(Expr *e)
{
    if(cg.parser->no_strength_reduction||e->kind!=EX_CAST||e->type.pointers||
       (e->type.base!=TY_INT&&e->type.base!=TY_CHAR)||e->type.is_bool||volatile_expression(e)||
       !project_word(e->left,8*width(e->type)))return 0;
    narrow_char(e->type);return 1;
}
static void bitfield_address(Expr *field)
{
    Type address=far_type(type(TY_CHAR,1));
    emit_address(field->left);
    if(!field->left->type.banked)code("    ldx #$007E\n");
    stage(0,address);
}
static void bitfield_normalize(Expr *field)
{
    unsigned width=field->type.bit_field_width;
    if(width<16){
        code("    and #$%04X\n",(1u<<width)-1);
        if(field->op){
            unsigned sign=1u<<(width-1);
            code("    eor #$%04X\n    sec\n    sbc #$%04X\n",sign,sign);
        }
    }
}
static void bitfield_shift(unsigned offset,int insert)
{
    if(offset>=8&&!cg.parser->no_strength_reduction){
        code(insert?"    xba\n":"    xba\n    and #$00FF\n");
        offset-=8;
    }
    for(unsigned i=0;i<offset;++i)code(insert?"    asl a\n":"    lsr a\n");
}
static void bitfield_extract(Expr *field)
{
    bitfield_shift(field->value,0);
    bitfield_normalize(field);
}
static int discarded_fixed_bitfield_store(Expr *e)
{
    if(cg.parser->no_strength_reduction||e->kind!=EX_ASSIGN||e->left->kind!=EX_BITFIELD)return 0;
    Expr *field=e->left;
    unsigned offset,mask=(1u<<field->type.bit_field_width)-1;
    uint32_t constant;
    Symbol *storage=direct_memory_object(field->left,&offset);
    if(!e->op&&mask!=65535&&!volatile_expression(field)&&integer_constant(e->right,&constant)){
        int near=!field->left->type.banked;
        if(!storage){
            if(near)emit_address_x(field->left);else bitfield_address(field);
        }
        code("    lda ");if(storage)array_operand(storage,offset);else code(near?"a:$0000,x":"[__arith_lhs]");
        constant=(constant&mask)<<field->value;
        unsigned clear=(mask<<field->value)&~constant;
        code("\n");
        if(clear)code("    and #$%04X\n",65535^clear);
        if(constant)code("    ora #$%04X\n",constant);
        code("    sta ");if(storage)array_operand(storage,offset);else code(near?"a:$0000,x":"[__arith_lhs]");
        code("\n");
        divmod_written(field);return 1;
    }
    if(!storage)return 0;
    if(e->op){
        if(!basic_integer_op(e->op)||!word_integer(common_type(field->type,e->right->type))||
           volatile_expression(field)||body_effect(e->right))return 0;
        if(e->op=='+'){
            unsigned packed_mask=mask<<field->value;
            emit_value(e->right);
            if(mask!=65535)code("    and #$%04X\n",mask);
            bitfield_shift(field->value,1);
            code("    clc\n    adc ");array_operand(storage,offset);code("\n");
            /* A carry out of the field must leave neighboring fields intact */
            if(!(packed_mask&0x8000)){
                code("    eor ");array_operand(storage,offset);
                code("\n    and #$%04X\n    eor ",packed_mask);array_operand(storage,offset);code("\n");
            }
            code("    sta ");array_operand(storage,offset);code("\n");
            divmod_written(field);return 1;
        }
        code("    lda ");array_operand(storage,offset);code("\n");
        bitfield_extract(field);
        binary_after_left(field,e->right,e->op);
    }else emit_value(e->right);
    if(mask!=65535||volatile_expression(field)){
        code("    and #$%04X\n",mask);
        bitfield_shift(field->value,1);
        cg.arithmetic=1;
        code("    sta z:__arith_rhs\n    lda ");array_operand(storage,offset);
        code("\n    and #$%04X\n    ora z:__arith_rhs\n",65535^(mask<<field->value));
    }
    code("    sta ");array_operand(storage,offset);code("\n");
    cg.divmod_available=0;
    return 1;
}
static void bitfield_update(Expr *e)
{
    Expr *field=e->left;
    int plain=e->kind==EX_ASSIGN&&!e->op,post=e->kind==EX_POST;
    unsigned offset=0,mask=(1u<<field->type.bit_field_width)-1;
    Symbol *storage=NULL;
    unsigned original=post?5:3;
    if(!cg.parser->no_strength_reduction&&!cg.stack_leaf)
        storage=direct_memory_object(field->left,&offset);
    if(plain){emit_value(e->right);code("    pha\n");}
    if(storage){
        code("    lda ");array_operand(storage,offset);code("\n    pha\n");
    }else{
        bitfield_address(field);
        code("    phx\n    pha\n    lda [__arith_lhs]\n    pha\n");
    }
    if(plain)code("    lda %u,s\n",storage?3:7);
    else{
        bitfield_extract(field);
        if(post)code("    pha\n");
        if(e->kind==EX_ASSIGN&&narrow_wide_compound_supported(e))
            emit_narrow_wide_operation_loaded(e);
        else if(e->kind==EX_ASSIGN)binary_after_left(field,e->right,e->op);
        else code("    %s a\n",e->op==TOK_INC?"inc":"dec");
    }
    bitfield_normalize(field);
    code("    pha\n    and #$%04X\n",mask);
    bitfield_shift(field->value,1);
    cg.arithmetic=1;
    code("    sta z:__arith_rhs\n");
    if(!storage)code("    lda %u,s\n    sta z:__arith_lhs\n    lda %u,s\n    sta z:__arith_lhs+2\n",original+2,original+4);
    code("    lda %u,s\n    and #$%04X\n    ora z:__arith_rhs\n    sta ",original,~(mask<<field->value)&65535);
    if(storage)array_operand(storage,offset);else code("[__arith_lhs]");
    code("\n    pla\n");
    if(post)code("    pla\n");
    code("    plx\n");if(!storage)code("    plx\n    plx\n");
    if(plain)code("    plx\n");
    cg.divmod_available=0;
}
static int identity_binary(Expr *e)
{
    Expr *keep=0;
    if(!identity_binary_operand(e,&keep))return 0;
    emit_value(keep);
    if(!known_conversion(keep,e->type)){
        if(reg_width(e->type)==4&&e->type.base!=TY_FLOAT&&!e->type.pointers&&
           reg_width(value_type(keep->type))==2&&!value_type(keep->type).pointers&&
           keep->type.base!=TY_FLOAT&&keep->known.valid&&keep->known.min>=0)
            code("    ldx #$0000\n");
        else convert_registers(value_type(keep->type),e->type);
    }
    return 1;
}
static int signed_byte_cast_sign(Expr *e)
{
    uint32_t bits;
    Expr *value;
    if(e->known.valid){
        if(e->known.one&128)return -1;
        if(e->known.zero&128)return 1;
    }
    if(e->kind!=EX_BINARY||(e->op!='&'&&e->op!='|'&&e->op!='^'))return 0;
    if(integer_constant(e->right,&bits))value=e->left;
    else if(integer_constant(e->left,&bits))value=e->right;
    else return 0;
    if(e->op=='&'&&!(bits&128))return 1;
    if(e->op=='|'&&(bits&128))return -1;
    if(value->type.is_bool||(value->kind==EX_UNARY&&value->op=='!')||
       (value->kind==EX_BINARY&&(comparison(value->op)||value->op==TOK_LAND||value->op==TOK_LOR)))
        return e->op!='&'&&(bits&128)?-1:1;
    return 0;
}
static int load_raw_signed_byte(Expr *input)
{
    Symbol *home;
    unsigned offset;
    if(input->kind!=EX_OBJECT||input->type.base!=TY_CHAR||input->type.is_unsigned||
       volatile_expression(input))return 0;
    if(input->symbol==cg.scalar_first)code("    txa\n");
    else{
        home=fixed_byte_home(input,0,&offset);
        if(!home||home->type.banked)return 0;
        home->used=1;code("    lda ");array_operand(home,offset);code("\n");
    }
    return 1;
}
static int narrow_byte_product(Expr *value,Type result)
{
    Expr *input=value->left;
    uint32_t factor;
    if(cg.parser->no_strength_reduction||result.pointers||result.base!=TY_CHAR||result.is_bool||
       value->kind!=EX_BINARY||value->op!='*'||!word_integer(value->type))return 0;
    if(!integer_constant(value->right,&factor)){
        if(!integer_constant(value->left,&factor))return 0;
        input=value->right;
    }
    if(factor<2||factor>128||(factor&(factor-1)))return 0;
    /* The product's low byte is independent of the input's sign extension */
    if(!load_raw_signed_byte(word_uncast(input)))return 0;
    for(;factor>1;factor>>=1)code("    asl a\n");
    narrow_char(result);return 1;
}
enum { HW_BYTE_NONE,HW_BYTE_IMM,HW_BYTE_MEM,HW_BYTE_INDEXED_READY,HW_BYTE_INDEXED,HW_BYTE_FAR_INDEXED };
typedef struct {
    int kind;
    uint32_t imm;
    Symbol *sym;
    unsigned offset;
    Expr *far_idx;
    IndexedOperand iop;
} HwByteOperand;
static Expr *hw_byte_unwrap(Expr *e)
{
    while(e->kind==EX_CAST&&!e->type.pointers&&!e->type.is_bool&&!e->type.array&&
          e->type.base==TY_INT&&unsigned_byte_value(e->left))
        e=e->left;
    return e;
}
static int hw_plain_global_byte(Expr *e)
{
    e=hw_byte_unwrap(e);
    return e->kind==EX_OBJECT&&!e->symbol->owner&&!e->type.pointers&&!e->type.array&&
           !e->type.is_bool&&e->type.base==TY_CHAR;
}
static int hw_expr_clobbers_alu(Expr *e)
{
    unsigned i;
    if(!e)return 0;
    if(volatile_expression(e)||e->kind==EX_CALL)return 1;
    if((e->kind==EX_BINARY||e->kind==EX_ASSIGN)&&(e->op=='*'||e->op=='/'||e->op=='%'))return 1;
    if(hw_expr_clobbers_alu(e->left)||hw_expr_clobbers_alu(e->right)||hw_expr_clobbers_alu(e->third))return 1;
    for(i=0;i<e->arg_count;++i)if(hw_expr_clobbers_alu(e->args[i]))return 1;
    return 0;
}
static HwByteOperand hw_byte_classify(Expr *e)
{
    HwByteOperand op={0};
    Expr *u=hw_byte_unwrap(e);
    Symbol *s;
    unsigned offset=0;
    if(integer_constant(u,&op.imm)){op.kind=HW_BYTE_IMM;return op;}
    if(volatile_expression(u)||u->type.pointers||u->type.array||
       u->type.base==TY_FLOAT||u->type.bit_field_width)return op;
    if(width(u->type)!=1&&!(reg_width(u->type)==2&&u->known.valid&&u->known.min>=0&&u->known.max<=255))
        return op;
    s=u->kind==EX_OBJECT?u->symbol:fixed_memory_object(u,&offset);
    if(s&&s!=cg.scalar_first&&s!=cg.numeric_index&&s!=cg.numeric_recurrence&&
       s!=cg.retained_index&&s!=cg.retained_second&&!cg.bound){
        op.kind=HW_BYTE_MEM;op.sym=s;op.offset=offset;return op;
    }
    if(!indexed_affine_owned(u)&&indexed_operand(u,&op.iop)){
        op.kind=indexed_retained(&op.iop,1)?HW_BYTE_INDEXED_READY:HW_BYTE_INDEXED;
        return op;
    }
    if(u->kind==EX_DEREF&&width(u->type)==1&&!u->type.is_bool&&u->left&&
       u->left->kind==EX_BINARY&&u->left->op=='+'&&u->left->left->kind==EX_OBJECT){
        Symbol *fs=u->left->left->symbol;Expr *idx=u->left->right;
        if(fs->type.array&&fs->type.banked&&width(pointed_type(value_type(fs->type)))==1&&
           width(fs->type)<=65536&&!cg.retained_index&&!body_effect(idx)&&
           reg_width(idx->type)==2&&!idx->type.pointers&&!idx->type.array&&
           idx->type.base!=TY_FLOAT&&(idx->type.is_unsigned||(idx->known.valid&&idx->known.min>=0))){
            op.kind=HW_BYTE_FAR_INDEXED;op.sym=fs;op.far_idx=idx;return op;
        }
    }
    return op;
}
static void hw_byte_emit_m8_load(const HwByteOperand *op)
{
    if(op->kind==HW_BYTE_IMM){
        code("    lda #$%02X\n",(unsigned)(op->imm&255u));
    }else if(op->kind==HW_BYTE_MEM){
        cg.dp_byte_operand=1;
        code("    lda ");
        if(op->sym==cg.leaf_count)code("z:__arith_rhs");
        else array_operand(op->sym,op->offset);
        code("\n");
        cg.dp_byte_operand=0;
    }else if(op->kind==HW_BYTE_FAR_INDEXED){
        op->sym->used=1;
        code("    lda f:_%s+$0000,x\n",op->sym->asm_name);
    }else{
        code("    lda ");
        indexed_text(&((HwByteOperand *)op)->iop);
        code("\n");
    }
}
static void hw_byte_emit_m8_op(const char *opname,const HwByteOperand *op)
{
    if(op->kind==HW_BYTE_IMM){
        code("    %s #$%02X\n",opname,(unsigned)(op->imm&255u));
    }else if(op->kind==HW_BYTE_MEM){
        cg.dp_byte_operand=1;
        code("    %s ",opname);
        if(op->sym==cg.leaf_count)code("z:__arith_rhs");
        else array_operand(op->sym,op->offset);
        code("\n");
        cg.dp_byte_operand=0;
    }else{
        code("    %s ",opname);
        indexed_text(&((HwByteOperand *)op)->iop);
        code("\n");
    }
}
static void emit_m8_byte_value(Expr *e)
{
    HwByteOperand op;
    e=hw_byte_unwrap(e);
    if(e->kind==EX_CAST&&width(e->type)==1&&!e->type.pointers&&!e->type.is_bool&&
       !e->left->type.pointers&&!e->left->type.array&&e->left->type.base!=TY_FLOAT){
        emit_m8_byte_value(e->left);return;
    }
    if(e->kind==EX_UNARY&&e->op=='~'){
        emit_m8_byte_value(e->left);
        code("    eor #$FF\n");
        return;
    }
    op=hw_byte_classify(e);
    if(op.kind==HW_BYTE_IMM||op.kind==HW_BYTE_MEM||op.kind==HW_BYTE_INDEXED_READY){
        code("    sep #$20\n.a8\n");
        hw_byte_emit_m8_load(&op);
        return;
    }
    if(op.kind==HW_BYTE_INDEXED){
        indexed_index(&op.iop);
        code("    sep #$20\n.a8\n");
        hw_byte_emit_m8_load(&op);
        indexed_finish(&op.iop);
        return;
    }
    if(op.kind==HW_BYTE_FAR_INDEXED){
        emit_value_x(op.far_idx);
        code("    sep #$20\n.a8\n");
        hw_byte_emit_m8_load(&op);
        return;
    }
    emit_value(e);
    code("    sep #$20\n.a8\n");
}
static int byte_bitwise_binary(Expr *e)
{
    Type t;HwByteOperand lo,ro;const char *mnemonic;
    if(e->kind!=EX_BINARY||(e->op!='&'&&e->op!='|'&&e->op!='^')||
       cg.parser->no_strength_reduction||cg.parser->no_body_optimizations||
       volatile_expression(e)||body_effect(e->left)||body_effect(e->right))return 0;
    t=binary_operands(e->left,e->right,e->op);
    if(t.pointers||t.array||t.base!=TY_INT)return 0;
    if(e->op=='&'){if(!unsigned_byte_value(e->left)&&!unsigned_byte_value(e->right))return 0;}
    else{if(!unsigned_byte_value(e->left)||!unsigned_byte_value(e->right))return 0;}
    if(e->left->kind==EX_INT||e->right->kind==EX_INT)return 0;
    lo=hw_byte_classify(e->left);ro=hw_byte_classify(e->right);
    if(lo.kind==HW_BYTE_IMM||ro.kind==HW_BYTE_IMM)return 0;
    if(lo.kind==HW_BYTE_MEM&&ro.kind==HW_BYTE_MEM&&
       width(hw_byte_unwrap(e->left)->type)==2&&width(hw_byte_unwrap(e->right)->type)==2)return 0;
    mnemonic=e->op=='&'?"and":e->op=='|'?"ora":"eor";
    if(lo.kind==HW_BYTE_INDEXED||ro.kind==HW_BYTE_INDEXED){
        HwByteOperand *idx=lo.kind==HW_BYTE_INDEXED?&lo:&ro;
        Expr *other=lo.kind==HW_BYTE_INDEXED?e->right:e->left;
        if(lo.kind==HW_BYTE_INDEXED&&(ro.kind==HW_BYTE_MEM||ro.kind==HW_BYTE_INDEXED_READY))idx=NULL;
        else if(ro.kind==HW_BYTE_INDEXED&&(lo.kind==HW_BYTE_MEM||lo.kind==HW_BYTE_INDEXED_READY))idx=NULL;
        if(idx){
            indexed_index(&idx->iop);
            code("    phx\n");if(cg.stack_leaf)cg.stack_bias+=2;
            emit_m8_byte_value(other);
            if(cg.stack_leaf)cg.stack_bias-=2;code("    plx\n");
            code("    %s ",mnemonic);indexed_text(&idx->iop);
            code("\n    rep #$20\n.a16\n    and #$00FF\n");
            indexed_finish(&idx->iop);
            return 1;
        }
    }
    if(ro.kind==HW_BYTE_MEM||ro.kind==HW_BYTE_INDEXED_READY){
        emit_m8_byte_value(e->left);
        hw_byte_emit_m8_op(mnemonic,&ro);
        code("    rep #$20\n.a16\n    and #$00FF\n");
        return 1;
    }
    if(lo.kind==HW_BYTE_MEM||lo.kind==HW_BYTE_INDEXED_READY){
        emit_m8_byte_value(e->right);
        hw_byte_emit_m8_op(mnemonic,&lo);
        code("    rep #$20\n.a16\n    and #$00FF\n");
        return 1;
    }
    return 0;
}
static int hardware_byte_product(Expr *e)
{
    Type t;HwByteOperand lo,ro;int right_safe,shared_x,in_m8=0;
    if(e->kind!=EX_BINARY||e->op!='*'||cg.parser->no_strength_reduction||cg.parser->no_body_optimizations||
       (cg.function&&cg.function->symbol->interrupt))return 0;
    t=binary_operands(e->left,e->right,'*');
    if(t.pointers||t.array||t.base!=TY_INT||!unsigned_byte_value(e->left)||!unsigned_byte_value(e->right))return 0;
    if(narrow_unsigned_value(e->left,2)||narrow_unsigned_value(e->right,2))return 0;
    if(!cg.loop_count&&hw_plain_global_byte(e->left)&&hw_plain_global_byte(e->right))return 0;
    right_safe=!hw_expr_clobbers_alu(e->right);
    if(!right_safe){
        emit_value(e->left);push_value(t);
        emit_value(e->right);
        cg.arithmetic=1;code("    sta z:__arith_rhs\n");
        pop_value(t);
        code("    sep #$20\n.a8\n    sta f:$004202\n    lda z:__arith_rhs\n    sta f:$004203\n"
             "    rep #$20\n.a16\n    nop\n    lda f:$004216\n");
        return 1;
    }
    lo=hw_byte_classify(e->left);ro=hw_byte_classify(e->right);
    shared_x=lo.kind==HW_BYTE_INDEXED&&ro.kind==HW_BYTE_INDEXED&&
        lo.iop.scale==ro.iop.scale&&body_equal(lo.iop.index,ro.iop.index)&&indexed_pure(lo.iop.index);
    if(lo.kind==HW_BYTE_IMM||lo.kind==HW_BYTE_MEM||lo.kind==HW_BYTE_INDEXED_READY){
        code("    sep #$20\n.a8\n");in_m8=1;
        hw_byte_emit_m8_load(&lo);
    }else if(lo.kind==HW_BYTE_INDEXED){
        indexed_index(&lo.iop);
        code("    sep #$20\n.a8\n");in_m8=1;
        hw_byte_emit_m8_load(&lo);
    }else if(lo.kind==HW_BYTE_FAR_INDEXED){
        emit_value_x(lo.far_idx);
        code("    sep #$20\n.a8\n");in_m8=1;
        hw_byte_emit_m8_load(&lo);
    }else{
        emit_value(e->left);
        code("    sep #$20\n.a8\n");in_m8=1;
    }
    code("    sta f:$004202\n");
    if(lo.kind==HW_BYTE_INDEXED&&!shared_x)indexed_finish(&lo.iop);
    if(shared_x){
        ro.iop.reg='x';
        hw_byte_emit_m8_load(&ro);
        code("    sta f:$004203\n");
        indexed_finish(&lo.iop);
    }else if(ro.kind==HW_BYTE_IMM||ro.kind==HW_BYTE_MEM||ro.kind==HW_BYTE_INDEXED_READY){
        hw_byte_emit_m8_load(&ro);
        code("    sta f:$004203\n");
    }else if(ro.kind==HW_BYTE_INDEXED){
        if(in_m8)code("    rep #$20\n.a16\n");
        indexed_index(&ro.iop);
        code("    sep #$20\n.a8\n");
        hw_byte_emit_m8_load(&ro);
        code("    sta f:$004203\n");
        indexed_finish(&ro.iop);
    }else if(ro.kind==HW_BYTE_FAR_INDEXED){
        if(in_m8)code("    rep #$20\n.a16\n");
        emit_value_x(ro.far_idx);
        code("    sep #$20\n.a8\n");
        hw_byte_emit_m8_load(&ro);
        code("    sta f:$004203\n");
    }else{
        if(in_m8)code("    rep #$20\n.a16\n");
        emit_value(e->right);
        code("    sep #$20\n.a8\n    sta f:$004203\n");
    }
    code("    rep #$20\n.a16\n    nop\n    lda f:$004216\n");
    return 1;
}
static void emit_value(Expr *e)
{
    if(wide_compare_supported(e)){emit_wide_compare(e);return;}
    if(wide_narrow_supported(e)){emit_wide_narrow(e);return;}
    if(narrow_wide_compound_supported(e)&&e->left->kind!=EX_BITFIELD){
        emit_narrow_wide_compound(e);return;
    }
    if(e->kind==EX_BITFIELD){
        unsigned offset=0;
        Symbol *storage=cg.parser->no_strength_reduction?NULL:direct_memory_object(e->left,&offset);
        if(storage){code("    lda ");array_operand(storage,offset);code("\n");}
        else if(!cg.parser->no_strength_reduction&&!e->left->type.banked){
            emit_address_x(e->left);code("    lda a:$0000,x\n");
        }
        else{bitfield_address(e);code("    lda [__arith_lhs]\n");}
        bitfield_extract(e);return;
    }
    if((e->kind==EX_ASSIGN||e->kind==EX_PRE||e->kind==EX_POST)&&e->left->kind==EX_BITFIELD){
        bitfield_update(e);return;
    }
    if(e->kind==EX_RESULT_ADDR){
        unsigned offset=cg.function->frame+cg.frame_saved+5+cg.parser->long_return;
        code("    lda %s\n",frame_operand(offset));
        return;
    }
    if(e->kind==EX_CALL&&structure_object(e->type)){emit_call(e,1);return;}
    if(e->kind==EX_VA_START){
        Symbol *function=cg.function->symbol;
        unsigned i,offset=cg.function->frame+cg.frame_saved+5+cg.parser->long_return+
                          (structure_object(function->type)?2:0);
        for(i=0;i<(unsigned)function->param_count;++i)
            if(!register_parameter(i,function->params[i]))offset+=argument_width(function->params[i]);
        code("    tya\n    clc\n    adc #$%04X\n",offset);
        return;
    }
    if(function_type(e->type)){emit_address(e);return;}
    if(e->kind==EX_COMMA){
        emit_discarded(e->left);
        emit_value(e->right);return;
    }
    if(e->kind==EX_CAST&&e->type.base==TY_VOID&&!e->type.pointers){emit_discarded(e->left);return;}
    unsigned yes,no,end,offset;Symbol *array;
    if(e->kind==EX_ASSIGN&&structure_object(e->type)&&!e->type.array){emit_aggregate_copy(e,1);return;}
    if(volatile_expression(e))cg.divmod_available=0;
    if(known_binary_constant(e)){
        code("    lda #$%04X\n",(unsigned)e->known.min&65535);
        return;
    }
    if(wide_address_safe(e)&&demanded_word_projection(e))return;
    if(structure_object(e->type)&&!e->type.array&&volatile_type(e->type)){volatile_aggregate(e,0,0);return;}
    if(wide_address_safe(e)){
        if(numeric_value(e))return;
        if(emit_far(e,1))return;
        if(near_memory_update(e,1))return;
        if(affine_pointer(e,0))return;
        if(indexed_access(e))return;
        if(selection_value(e))return;
    }else if(emit_far(e,0))return;
    if(structure_object(e->type)&&!e->type.array)error_at(e->location,"struct values are not implemented yet");
    switch(e->kind){
    case EX_INT:
        code("    lda #$%04X\n",e->value&0xFFFFu);if(reg_width(e->type)==4)code("    ldx #$%04X\n",e->value>>16);break;
    case EX_STRING:e->string->used=1;code("    lda #.loword(str_%s_%u)\n    ldx #.bankbyte(str_%s_%u)\n",cg.parser->unit,e->string->id,cg.parser->unit,e->string->id);break;
    case EX_OBJECT:if(function_type(e->type))emit_address(e);else load_symbol(e->symbol);break;
    case EX_MEMBER:
        if(e->type.array||function_type(e->type)){emit_address(e);break;}
        array=fixed_memory_object(e,&offset);
        if(array){load_array_element(array,offset,e->type);break;}
        if(direct_dpage_load(e))break;
        offset=member_base_x(e);load_indirect_at(e->type,0,offset);break;
    case EX_ADDRESS:
        if(near_object_address(e,&offset)){
            Symbol *s=near_object_address(e,&offset);
            if(s&&!s->owner&&!s->type.banked){
                s->used=1;
                code("    lda #.loword(_%s+$%04X)\n",s->asm_name,offset);
                break;
            }
        }
        emit_address(e->left);break;
    case EX_CAST:
        if(!cg.parser->no_strength_reduction&&fold_binary32_integer_cast(e->left,e->type))break;
        if(narrow_byte_product(e->left,e->type))break;
        if(!e->type.pointers&&!e->type.is_bool&&e->type.base==TY_CHAR&&e->left->kind==EX_CHOOSE&&
           accumulator_zero_choose(e->left,e->type))break;
        if(!cg.parser->no_strength_reduction&&!e->type.pointers&&e->type.base==TY_CHAR&&
           e->type.is_unsigned&&!e->type.is_bool&&address_bank_byte(e,0)){
            code("    lda ");address_bank_byte(e,1);code("\n");break;
        }
        if(!cg.parser->no_strength_reduction&&!e->type.pointers&&!e->type.array&&
           e->type.base!=TY_FLOAT&&!e->type.is_bool&&reg_width(e->type)<=2&&
           e->left->kind==EX_CAST&&!e->left->type.pointers&&!e->left->type.array&&
           e->left->type.base!=TY_FLOAT&&reg_width(e->left->type)==4&&
           (e->left->left->type.pointers?!far_pointer(value_type(e->left->left->type)):
            (e->left->left->type.base!=TY_FLOAT&&reg_width(e->left->left->type)<=2))){
            emit_value(e->left->left);
            if(!known_conversion(e->left->left,e->type))convert_registers(e->left->left->type,e->type);
            break;
        }
        emit_value(e->left);
        /* Real object addresses and deref-proven pointers cannot be NULL.
         * Other pointer expressions retain the NULL-preserving general conversion. */
        if(far_pointer(value_type(e->type))&&!far_pointer(value_type(e->left->type))&&
           value_type(e->left->type).pointers&&
           (e->left->known_nonnull||near_object_address(e->left,&offset)||
            (e->left->kind==EX_BINARY&&(e->left->op=='+'||e->left->op=='-')&&
             value_type(e->left->left->type).pointers)))code("    ldx #$007E\n");
        else if(!known_conversion(e->left,e->type)){
            int sign;
            if(reg_width(e->type)==4&&e->type.base!=TY_FLOAT&&!e->type.pointers&&
               reg_width(value_type(e->left->type))==2&&!value_type(e->left->type).pointers&&
               e->left->type.base!=TY_FLOAT&&e->left->known.valid&&e->left->known.min>=0)
                code("    ldx #$0000\n");
            else if(!cg.parser->no_strength_reduction&&!e->type.pointers&&e->type.base==TY_CHAR&&
                    !e->type.is_unsigned&&!e->type.is_bool&&reg_width(e->left->type)==2&&
                    (sign=signed_byte_cast_sign(e->left)))
                code(sign<0?"    ora #$FF00\n":"    and #$00FF\n");
            else convert_registers(e->left->type,e->type);
        }
        break;
    case EX_CALL:emit_call(e,1);break;
    case EX_DEREF:
        if(e->type.array||function_type(e->type)){emit_address(e);break;}
        array=fixed_memory_object(e,&offset);
        if(array){load_array_element(array,offset,e->type);break;}
        if(direct_dpage_load(e)||post_cursor_load(e)||advanced_cursor_load(e))break;
        if(!cg.parser->no_direct_dpage&&!volatile_expression(e)&&e->left->kind==EX_POST&&e->left->left->kind==EX_OBJECT&&e->left->left->symbol->dpage&&width(e->type)==1){
            Symbol *s=e->left->left->symbol;s->used=1;code("    lda (_%s)\n    %s z:_%s\n",s->asm_name,e->left->op==TOK_INC?"inc":"dec",s->asm_name);narrow_char(e->type);
        }else{
            Expr *displaced=near_displaced_deref(e,&offset);
            Expr *rc_base=NULL;
            if(!displaced&&cg.retained_y==5&&cg.retained_ptr&&cg.retained_index&&!volatile_expression(e)){
                Expr *addr=e->left;
                while(addr&&addr->kind==EX_CAST&&value_type(addr->type).pointers&&
                      !far_pointer(value_type(addr->type))&&reg_width(addr->left->type)==2&&
                      value_type(addr->left->type).pointers)addr=addr->left;
                if(addr&&addr->kind==EX_BINARY&&addr->op=='+'){
                    Expr *l=addr->left,*r=addr->right;
                    while(l->kind==EX_CAST&&!value_type(l->type).pointers&&reg_width(l->left->type)==2)l=l->left;
                    while(r->kind==EX_CAST&&!value_type(r->type).pointers&&reg_width(r->left->type)==2)r=r->left;
                    if(l->kind==EX_OBJECT&&l->symbol==cg.retained_ptr&&r->kind==EX_OBJECT&&r->symbol==cg.retained_index)
                        rc_base=l;
                    else if(r->kind==EX_OBJECT&&r->symbol==cg.retained_ptr&&l->kind==EX_OBJECT&&l->symbol==cg.retained_index)
                        rc_base=r;
                }
            }
            if(rc_base){emit_value_x(rc_base);load_indirect(e->type,strength_wram_pointer(rc_base));}
            else if(displaced){emit_value_x(displaced);load_indirect_at(e->type,strength_wram_pointer(displaced),offset);}
            else{emit_value_x(e->left);load_indirect(e->type,strength_wram_pointer(e->left));}
        }break;
    case EX_ASSIGN:
        if(!volatile_expression(e)&&strength_update(e,1))break;
        if(scalar_home_update(e,1))break;
        if(!e->op&&e->left->kind==EX_OBJECT){emit_value(e->right);store_symbol(e->left->symbol);break;}
        if(!volatile_expression(e)&&store_previous_element(e))break;
        array=fixed_memory_object(e->left,&offset);
        if(!e->op&&array){emit_value(e->right);store_array_element(array,offset,e->type);break;}
        if(array&&reg_width(e->type)==2&&width(e->type)==2&&
           !e->type.pointers&&!volatile_expression(e)&&!cg.parser->no_indexed_operands){
            load_array_element(array,offset,e->left->type);
            binary_after_left(e->left,e->right,e->op);
            if(!e->known_no_conversion)convert_registers(binary_operands(e->left,e->right,e->op),e->type);
            store_array_element(array,offset,e->type);break;
        }
        if(direct_dpage_store(e)||post_cursor_store(e))break;
        {
            Expr *rep=e->op?NULL:indexed_repeated_word_update(e);
            Expr *rhs=rep?rep->right:e->right;
            int op=rep?rep->op:e->op;
            Type bt=binary_operands(e->left,rhs,op);
            if(!cg.parser->no_body_optimizations&&width(e->type)==2&&!volatile_expression(e)&&
               (op=='+'||op=='&'||op=='|'||op=='^')&&bt.base==TY_INT&&!bt.pointers&&
               indexed_pure(rhs)&&home_rhs_pure(rhs)&&
               (!cg.retained_index||cg.retained_y==5||cg.retained_scratch)){
                int wram=e->left->kind==EX_DEREF&&strength_wram_pointer(e->left->left);
                const char *mnemonic=op=='+'?"adc":op=='&'?"and":op=='|'?"ora":"eor";
                emit_value(rhs);convert_registers(value_type(rhs->type),bt);
                if(destination_x_preserves_a(e->left)){
                    offset=assign_base_x(e->left);
                }else{
                    code("    pha\n");if(cg.stack_leaf)cg.stack_bias+=2;
                    offset=assign_base_x(e->left);
                    if(cg.stack_leaf)cg.stack_bias-=2;code("    pla\n");
                }
                if(op=='+')code("    clc\n");
                code("    %s %s:$%04X,x\n",mnemonic,wram?"z":"a",offset);
                if(!e->known_no_conversion)convert_registers(bt,e->type);
                code("    sta %s:$%04X,x\n",wram?"z":"a",offset);
                break;
            }
        }
        if(!e->op&&word_preserves_x(e->right)){
            offset=assign_base_x(e->left);
            emit_value(e->right);
            if(width(e->type)==1)code("    sep #$20\n.a8\n");
            code("    sta %s:$%04X,x\n",e->left->kind==EX_DEREF&&strength_wram_pointer(e->left->left)?"z":"a",offset);
            if(width(e->type)==1)code("    rep #$20\n.a16\n");
            break;
        }
        if(!e->op&&reg_width(e->type)==2&&!volatile_expression(e)&&wide_address_safe(e->right)&&
           home_rhs_pure(e->right)&&destination_x_preserves_a(e->left)){
            emit_value(e->right);offset=assign_base_x(e->left);
            if(width(e->type)==1)code("    sep #$20\n.a8\n");
            code("    sta %s:$%04X,x\n",e->left->kind==EX_DEREF&&strength_wram_pointer(e->left->left)?"z":"a",offset);
            if(width(e->type)==1)code("    rep #$20\n.a16\n");
            break;
        }
        offset=assign_base_x(e->left);
        code("    phx\n");if(cg.stack_leaf)cg.stack_bias+=2;
        if(e->op){
            load_indirect_at(e->left->type,e->left->kind==EX_DEREF&&strength_wram_pointer(e->left->left),offset);binary_after_left(e->left,e->right,e->op);
            if(!e->known_no_conversion)convert_registers(binary_operands(e->left,e->right,e->op),e->type);
        }else emit_value(e->right);
        if(cg.stack_leaf)cg.stack_bias-=2;
        store_saved_address(e->type,e->left->kind==EX_DEREF&&strength_wram_pointer(e->left->left),offset);break;
    case EX_POST:case EX_PRE:
        if(!volatile_expression(e)&&strength_update(e,1))break;
        if(indirect_far_post(e))break;
        if(fixed_binary32_increment(e,1))break;
        if(fixed_long_increment(e,1))break;
        if(!cg.parser->no_strength_reduction&&object_volatile(e->left->type)&&
           !e->type.pointers&&(e->type.base==TY_CHAR||e->type.base==TY_INT||e->type.base==TY_LONG)&&
           (array=direct_memory_object(e->left,&offset))!=NULL){
            load_array_element(array,offset,e->left->type);
            if(e->kind==EX_POST)push_value(e->type);
            increment_value(e->type,e->op);
            store_array_element(array,offset,e->left->type);
            if(e->kind==EX_POST)pop_value(e->type);
            break;
        }
        if(direct_increment(e)){
            Symbol *v=e->left->symbol;
            if(!cg.parser->no_strength_reduction&&e->kind==EX_POST&&word_integer(e->type)){
                load_symbol(v);
                if(!v->owner&&!v->type.banked){
                    code("    %s ",e->op==TOK_INC?"inc":"dec");array_operand(v,0);code("\n");
                }else{
                    increment_value(e->type,e->op);
                    store_symbol(v);
                    increment_value(e->type,e->op==TOK_INC?TOK_DEC:TOK_INC);
                }
                divmod_written(e->left);break;
            }
            if(width(e->type)==1&&!v->owner&&!v->type.banked&&!e->type.pointers&&!e->type.is_bool){
                v->used=1;
                if(e->type.is_unsigned)code("    lda #0\n");
                code("    sep #$20\n.a8\n");
                if(e->kind==EX_POST){code("    lda ");array_operand(v,0);code("\n");}
                code("    %s ",e->op==TOK_INC?"inc":"dec");array_operand(v,0);code("\n");
                if(e->kind==EX_PRE){code("    lda ");array_operand(v,0);code("\n");}
                code("    rep #$20\n.a16\n");
                if(!e->type.is_unsigned)narrow_char(e->type);
                divmod_written(e->left);break;
            }
            load_symbol(v);
            if(e->kind==EX_POST)push_value(e->type);
            increment_value(e->type,e->op);store_symbol(v);
            if(e->kind==EX_POST)pop_value(e->type);
            divmod_written(e->left);break;
        }
        emit_address(e->left);code("    pha\n    tax\n");load_indirect(e->type,e->left->kind==EX_DEREF&&strength_wram_pointer(e->left->left));
        if(e->kind==EX_POST)push_value(e->type);
        increment_value(e->type,e->op);stage(0,e->type);
        code("    lda %u,s\n    tax\n    lda z:__arith_lhs\n",(e->kind==EX_POST?reg_width(e->type):0)+1);
        if(width(e->type)==1)code("    sep #$20\n.a8\n");code("    sta %s:$0000,x\n",e->left->kind==EX_DEREF&&strength_wram_pointer(e->left->left)?"z":"a");
        if(width(e->type)==1)code("    rep #$20\n.a16\n");
        if(reg_width(e->type)==4)code("    lda z:__arith_lhs+2\n    sta %s:$0002,x\n",e->left->kind==EX_DEREF&&strength_wram_pointer(e->left->left)?"z":"a");
        if(e->kind==EX_POST)pop_value(e->type);
        else{code("    lda z:__arith_lhs\n");if(reg_width(e->type)==4)code("    ldx z:__arith_lhs+2\n");}
        cleanup(2,e->type);break;
    case EX_UNARY:
        if(e->op=='!'){
            Expr *inner=e->left;
            if(!cg.parser->no_strength_reduction&&word_integer(inner->type)&&
               !volatile_expression(inner)&&compare_memory_operand(inner,0)){
                /* Comparing unsigned zero sets carry only for a zero operand */
                code("    lda #0\n    cmp ");compare_memory_operand(inner,1);
                code("\n    rol a\n");break;
            }
            if(!cg.parser->no_strength_reduction&&inner->kind==EX_UNARY&&inner->op=='!'&&
               !volatile_expression(inner->left)){
                Expr *x=inner->left;
                while(x->kind==EX_CAST&&!x->type.pointers&&x->type.base==TY_INT&&x->left->type.is_bool)x=x->left;
                if(x->kind==EX_OBJECT&&x->type.is_bool&&x->symbol->owner&&
                   !object_volatile(x->symbol->type)&&!loop_escapes(cg.function->body,x->symbol)){
                    emit_value(x);break;
                }
            }
            yes=++cg.label;no=++cg.label;end=++cg.label;branch(e,yes,no,yes);label(yes);code("    lda #1\n");jump(end);label(no);code("    lda #0\n");label(end);break;
        }
        emit_value(e->left);convert_registers(e->left->type,e->type);
        if(e->op==TOK_SRAM){
            /* Move the logical window number into the bank word */
            code("    pha\n    stx z:__arith_rhs\n");
            for(unsigned window=sram_window_size;window<65536;window*=2)
                code("    asl a\n    rol z:__arith_rhs\n");
            code("    ldx z:__arith_rhs\n    pla\n    and #$%04X\n",sram_window_size-1);
        }else if(e->op=='-'){
            if(e->type.base==TY_FLOAT){code("    pha\n    txa\n    eor #$8000\n    tax\n    pla\n");}
            else native_negate(e->type);
        }else if(e->op=='~'){
            code("    eor #$FFFF\n");if(reg_width(e->type)==4)code("    pha\n    txa\n    eor #$FFFF\n    tax\n    pla\n");
        }break;
    case EX_BINARY:
        if(function_address_sum(e))break;
        if(e->op==TOK_LAND||e->op==TOK_LOR||comparison(e->op)){
            if(word_range_flags(e)){
                code(e->op==TOK_LOR?"    lda #0\n    rol a\n":"    lda #0\n    rol a\n    eor #$0001\n");
                break;
            }
            yes=++cg.label;no=++cg.label;end=++cg.label;branch(e,yes,no,yes);label(yes);code("    lda #1\n");jump(end);label(no);code("    lda #0\n");label(end);break;
        }
        if(identity_binary(e))break;
        if(fold_constant_choose(e))break;
        if(!cg.parser->no_value_reuse&&!cg.parser->no_body_optimizations&&
           (e->op=='+'||e->op=='|'||e->op=='^'||e->op=='&')&&word_integer(e->type)&&
           e->right->kind==EX_CHOOSE&&!body_effect(e->right)&&!volatile_expression(e)&&
           direct_operand(e->left,e->type,0,0)){
            emit_value(e->right);binary_after_left(e->right,e->left,e->op);break;
        }
        if(!cg.parser->no_value_reuse&&!cg.parser->no_body_optimizations&&
           e->op=='-'&&word_integer(e->type)&&e->right->kind==EX_CHOOSE&&
           !body_effect(e->right)&&!volatile_expression(e)&&
           direct_operand(e->left,e->type,0,0)){
            uint32_t k1,k2;
            if(integer_constant(e->right->right,&k1)&&integer_constant(e->right->third,&k2)){
                unsigned y=++cg.label,n=++cg.label,d=++cg.label;
                branch(e->right->left,y,n,y);
                label(y);code("    lda ");direct_operand(e->left,e->type,0,1);code("\n");
                if(k1&0xFFFFu)code("    sec\n    sbc #$%04X\n",(unsigned)(k1&0xFFFFu));
                jump(d);
                label(n);code("    lda ");direct_operand(e->left,e->type,0,1);code("\n");
                if(k2&0xFFFFu)code("    sec\n    sbc #$%04X\n",(unsigned)(k2&0xFFFFu));
                label(d);break;
            }
        }
        if(!volatile_expression(e)&&dot_emit_expr(e))break;
        if(wide_address_safe(e)&&!volatile_expression(e)&&(power_divmod(e)||divmod_emit(e)||bounded_word_shift(e->left,e->right,e->op)||bounded_expression_lut(e)||word_shift_combined(e)||word_expression(e)||word_constant_product(e)||hardware_byte_product(e)||byte_bitwise_binary(e)||direct_large_shift(e)||
           indexed_pair_binary(e)||indexed_immediate_pair(e)||shifted_indexed_long_bits(e)||indirect_long_binary(e)||near_word_pair(e)||deferred_binary(e)||
           shared_adjusted_members(e)||shared_element_binary(e)||widened_word_product(e)||staged_binary(e)))break;
        if((volatile_expression(e)||(!fixed_near_pointer_sum(e)&&!indexed_pointer_sum(e)))&&!near_address_scaled_sum(e)){
            Type bt=binary_operands(e->left,e->right,e->op);uint32_t cv;
            if(!cg.parser->no_strength_reduction&&!volatile_expression(e)&&!bt.pointers&&
               !far_pointer(bt)&&bt.base!=TY_FLOAT&&reg_width(bt)==2&&
               (e->op=='+'||e->op=='-'||e->op=='&'||e->op=='|'||e->op=='^')&&
               direct_operand(e->left,bt,0,0)&&!direct_operand(e->right,bt,0,0)&&
               (integer_constant(e->left,&cv)||
                (!body_effect(e->left)&&readonly_integer_expression(e->right)))){
                emit_value(e->right);
                if(e->op=='-'){
                    convert_registers(value_type(e->right->type),bt);
                    code("    eor #$FFFF\n    sec\n    adc ");
                    direct_operand(e->left,bt,0,1);
                    code("\n");
                }else{
                    binary_after_left(e->right,e->left,e->op);
                }
            }else{
                emit_value(e->left);binary_after_left(e->left,e->right,e->op);
            }
        }break;
    case EX_CHOOSE:
        if(accumulator_choose(e))break;
        if(!volatile_expression(e)&&!body_effect(e->right)&&!body_effect(e->third)){
            uint32_t rv,tv;
            if(!e->type.pointers&&numeric(e->type)&&e->type.base!=TY_FLOAT&&width(e->type)<=2&&
               integer_constant(e->right,&rv)&&integer_constant(e->third,&tv)&&
               initializer_cast(rv,e->type)==initializer_cast(tv,e->type)){
                if(body_effect(e->left))emit_discarded(e->left);
                code("    lda #$%04X\n",(unsigned)(initializer_cast(rv,e->type)&65535));
                break;
            }
            if(e->type.base!=TY_VOID&&body_equal(e->right,e->third)&&same_type(e->right->type,e->type)){
                if(body_effect(e->left))emit_discarded(e->left);
                emit_value(e->right);
                break;
            }
        }
        yes=++cg.label;no=++cg.label;end=++cg.label;branch(e->left,yes,no,yes);
        {unsigned available=cg.divmod_available,right_available;
            label(yes);emit_value(e->right);right_available=cg.divmod_available;jump(end);
            cg.divmod_available=available;label(no);emit_value(e->third);label(end);
            cg.divmod_available&=right_available;
        }break;
    case EX_COMMA:break; /* Sequenced before scalar/address selection above */
    }
    if(e->kind==EX_ASSIGN||e->kind==EX_PRE||e->kind==EX_POST)divmod_written(e->left);
}
/* Only discarded low-byte results enter A8. A later word consumer still goes
 * through the normal signed/unsigned extension path. */
static int indexed_byte_discard(Expr *e)
{
    Expr *rhs,*source;IndexedOperand to={0},from={0};int negate=0,to_index=0,from_index=0;
    if(cg.parser->no_body_optimizations||cg.parser->no_indexed_operands||!cg.retained_index||
       e->kind!=EX_ASSIGN||e->op||width(e->type)!=1||e->type.is_bool||volatile_expression(e))return 0;
    rhs=e->right;while(rhs->kind==EX_CAST&&reg_width(rhs->type)==2&&!rhs->type.is_bool)rhs=rhs->left;
    if(rhs->kind==EX_UNARY&&rhs->op=='-'){negate=1;rhs=rhs->left;while(rhs->kind==EX_CAST&&reg_width(rhs->type)==2&&!rhs->type.is_bool)rhs=rhs->left;}
    source=rhs;if(width(source->type)>2||source->type.pointers||source->type.is_bool||
        (source->type.base!=TY_CHAR&&source->type.base!=TY_INT))return 0;
    if(indexed_operand(e->left,&to)&&indexed_retained(&to,1))to_index=1;
    else if(e->left->kind!=EX_OBJECT||!loop_private(e->left->symbol))return 0;
    if(indexed_operand(source,&from)&&indexed_retained(&from,1))from_index=1;
    else if(source->kind!=EX_OBJECT||!loop_private(source->symbol))return 0;
    if(!to_index&&!from_index)return 0;
    code("; discarded indexed byte region\n    sep #$20\n.a8\n    lda ");
    if(from_index)indexed_text(&from);else array_operand(source->symbol,0);code("\n");
    if(negate)code("    eor #$FF\n    inc a\n");
    code("    sta ");if(to_index)indexed_text(&to);else array_operand(e->left->symbol,0);code("\n    rep #$20\n.a16\n");
    divmod_written(e->left);return 1;
}
static int physical_integer_byte(Type t,unsigned byte)
{
    return !t.pointers&&!t.array&&!t.is_bool&&!t.bit_field_width&&
        (t.base==TY_CHAR||t.base==TY_INT||t.base==TY_LONG)&&byte<width(t);
}
static Symbol *fixed_byte_home(Expr *e,unsigned byte,unsigned *offset)
{
    Symbol *s;
    if(!physical_integer_byte(e->type,byte)||e->kind==EX_BITFIELD)return NULL;
    *offset=0;
    s=e->kind==EX_OBJECT?e->symbol:fixed_memory_object(e,offset);
    if(!s||s->function||s==cg.scalar_first||s==cg.leaf_count||s==cg.scan_cursor||
       s==cg.numeric_index||s==cg.numeric_recurrence||
       s==cg.retained_index||s==cg.retained_second)return NULL;
    *offset+=byte;
    return s;
}
static int fixed_shift_assignment(Expr *e)
{
    Expr *target=e->left,*count;
    Symbol *home;
    unsigned offset,bytes;
    uint32_t steps;
    int op=e->op;
    if(cg.parser->no_strength_reduction||cg.parser->no_body_optimizations||
       e->kind!=EX_ASSIGN||!physical_integer_byte(target->type,0)||volatile_expression(e))return 0;
    bytes=width(target->type);
    count=e->right;
    if(!op){
        Expr *shift=e->right,*read;
        if(shift->kind==EX_CAST&&same_type(unqualified_value(shift->type),unqualified_value(target->type)))
            shift=shift->left;
        if(shift->kind!=EX_BINARY||
           !same_type(unqualified_value(shift->type),promoted(value_type(target->type))))return 0;
        read=shift->left;
        if(bytes==1&&read->kind==EX_CAST&&same_type(read->type,promoted(value_type(read->left->type))))
            read=read->left;
        if(!body_equal(target,read))return 0;
        op=shift->op;count=shift->right;
    }
    if((op!=TOK_SHL&&op!=TOK_SHR)||!integer_constant(count,&steps))return 0;
    home=fixed_byte_home(target,0,&offset);
    if(!home||home->type.banked)return 0;
    if(bytes==4){
        if(steps==1){
            unsigned first=op==TOK_SHL?0:2,second=2-first;
            code("    lda ");array_operand(home,offset+first);code("\n");
            if(op==TOK_SHL)code("    asl a\n");
            else if(target->type.is_unsigned)code("    lsr a\n");
            else code("    cmp #$8000\n    ror a\n");
            code("    sta ");array_operand(home,offset+first);
            code("\n    lda ");array_operand(home,offset+second);
            code("\n    %s a\n    sta ",op==TOK_SHL?"rol":"ror");
            array_operand(home,offset+second);code("\n");
            divmod_written(target);
            return 1;
        }
        unsigned sign=steps==7?0x0100:0x0080,slot=0;
        if(cg.parser->no_byte_shuffles||op!=TOK_SHR||(steps!=7&&steps!=8))return 0;
        if(home->owner){
            unsigned at=home->offset+offset,word=(at-1)/2;
            /* Reserve the fallback's scratch while the frame layout is chosen */
            if(cg.dp_trial)return 0;
            if(cg.dp_homes){
                if(!(at&1)||word+1>=cg.dp_words||!(slot=cg.dp_map[word])||
                   cg.dp_map[word+1]!=slot+1)return 0;
            }else if(!cg.stack_leaf&&frame_offset(at+1)+1!=frame_offset(at+2))return 0;
        }
        code("; shift long in its fixed home\n");
        if(steps==7){
            code("    lda ");array_operand(home,offset);code("\n    xba\n    asl a\n");
        }
        if(slot)code("    lda z:__dp_home_%02u+1\n",slot-1);
        else{code("    lda ");array_operand(home,offset+1);code("\n");}
        if(steps==7)code("    rol a\n");
        code("    sta ");array_operand(home,offset);
        code("\n    lda ");array_operand(home,offset+2);code("\n    xba\n    and #$00FF\n");
        if(steps==7)code("    rol a\n");
        if(!target->type.is_unsigned)
            code("    eor #$%04X\n    sec\n    sbc #$%04X\n",sign,sign);
        code("    sta ");array_operand(home,offset+2);code("\n");
        divmod_written(target);
        return 1;
    }
    if(steps!=1)return 0;
    if(bytes==1)code("    sep #$20\n.a8\n");
    code("    lda ");array_operand(home,offset);
    if(op==TOK_SHL)code("\n    asl a\n");
    else if(target->type.is_unsigned||(target->known.valid&&target->known.min>=0))code("\n    lsr a\n");
    else code(bytes==1?"\n    cmp #$80\n    ror a\n":"\n    cmp #$8000\n    ror a\n");
    code("    sta ");array_operand(home,offset);code("\n");
    if(bytes==1)code("    rep #$20\n.a16\n");
    divmod_written(target);
    return 1;
}
/* Project a byte through integer casts, masks and byte-aligned shifts. The
 * requested byte must exist at every step, including in the original home.
 * Bytes manufactured by sign or zero extension keep the ordinary path. */
static Symbol *fixed_byte_source(Expr *e,unsigned byte,unsigned *offset,unsigned *mask)
{
    uint32_t bits;
    if(!physical_integer_byte(e->type,byte))return NULL;
    if(e->kind==EX_CAST)return fixed_byte_source(e->left,byte,offset,mask);
    if(e->kind==EX_BINARY&&e->op=='&'){
        Expr *source=e->left;
        if(!integer_constant(e->right,&bits)){
            if(!integer_constant(e->left,&bits))return NULL;
            source=e->right;
        }
        *mask&=(bits>>(8*byte))&255;
        return fixed_byte_source(source,byte,offset,mask);
    }
    if(e->kind==EX_BINARY&&e->op==TOK_SHR&&integer_constant(e->right,&bits)&&
       bits<=24&&!(bits%8))
        return fixed_byte_source(e->left,byte+(unsigned)bits/8,offset,mask);
    return fixed_byte_home(e,byte,offset);
}
/* A discarded byte assignment needs only the destination byte. For bitwise
 * compound assignments, both operands can be read in A8 before the single
 * store. A pure fixed RHS and LHS can be read in either order. */
static int fixed_byte_assignment(Expr *e)
{
    Symbol *dst,*src=NULL;
    unsigned to,from=0,mask=255;
    uint32_t literal=0;
    const char *op;
    if(cg.parser->no_strength_reduction||cg.parser->no_body_optimizations||
       e->kind!=EX_ASSIGN||width(e->left->type)!=1||volatile_expression(e))return 0;
    if(e->op&&e->op!='&'&&e->op!='|'&&e->op!='^')return 0;
    dst=fixed_byte_home(e->left,0,&to);
    if(!dst||dst->type.banked)return 0;
    if(!integer_constant(e->right,&literal)){
        src=fixed_byte_source(e->right,0,&from,&mask);
        if(!src)return 0;
        /* Keep the word path for scalar frame stores, single-definition
         * inputs and wide values already split across A and X. */
        if(!e->op&&((dst->owner&&e->left->kind==EX_OBJECT)||
           (src->owner&&!src->type.array&&!structure_object(src->type)&&
            (width(src->type)>2||scalar_writes(cg.function->body,src)<=1))))return 0;
    }else if(!e->op)return 0; /* keep the existing constant-store selectors */
    code("; fixed byte assignment\n    sep #$20\n.a8\n    lda ");
    op=e->op=='&'?"and":e->op=='|'?"ora":"eor";
    if(src){
        array_operand(src,from);code("\n");
        if(mask!=255)code("    and #$%02X\n",mask);
        if(e->op){code("    %s ",op);array_operand(dst,to);code("\n");}
    }else{
        array_operand(dst,to);code("\n    %s #$%02X\n",op,literal&255);
    }
    code("    sta ");array_operand(dst,to);
    code("\n    rep #$20\n.a16\n");
    divmod_written(e->left);
    return 1;
}
/* The indexed byte store discards both high operands. Keep the index
 * calculation in word mode and perform the pure arithmetic in byte mode. */
static int indexed_byte_arithmetic(Expr *e)
{
    if(cg.parser->no_body_optimizations||e->kind!=EX_ASSIGN||e->op||
       !physical_integer_byte(e->left->type,0)||width(e->left->type)!=1||volatile_expression(e))return 0;
    Expr *value=e->right;
    while(value->kind==EX_CAST&&physical_integer_byte(value->type,0))value=value->left;
    if(value->kind!=EX_BINARY||!basic_integer_op(value->op)||!physical_integer_byte(value->type,0))return 0;
    unsigned lo,ro;
    Symbol *left=fixed_byte_home(value->left,0,&lo),*right=fixed_byte_home(value->right,0,&ro);
    if(!left||!right||left->type.banked||right->type.banked)return 0;
    unsigned offset=frame_byte_index_x(e->left);
    if(!offset)return 0;
    int op=value->op;
    code("    sep #$20\n.a8\n    lda ");array_operand(left,lo);code("\n");
    if(op=='+'||op=='-')code("    %s\n",op=='+'?"clc":"sec");
    code("    %s ",op=='+'?"adc":op=='-'?"sbc":op=='&'?"and":op=='|'?"ora":"eor");
    array_operand(right,ro);code("\n    sta a:$%04X,x\n    rep #$20\n.a16\n",offset);
    divmod_written(e->left);return 1;
}
/* Low-byte arithmetic agrees with int promotion followed by truncation.
 * Keep the original volatile read widths and left-to-right evaluation. */
static Symbol *arithmetic_byte_home(Expr *e,unsigned *offset)
{
    while(e->kind==EX_CAST&&physical_integer_byte(e->type,0)&&
          (e->type.base==TY_CHAR||e->type.base==TY_INT))e=e->left;
    return width(e->type)==1?fixed_byte_home(e,0,offset):NULL;
}
static int discarded_volatile_byte_arithmetic(Expr *e)
{
    Expr *value;
    Symbol *dst,*left,*right=NULL;
    unsigned to,lo,ro=0;
    int op,shift=0,divide,is_unsigned=0,rhs_unsigned=0,signed_result=0;
    if(cg.parser->no_strength_reduction||cg.parser->no_body_optimizations||
       e->kind!=EX_ASSIGN||e->op||width(e->left->type)!=1||!volatile_expression(e))return 0;
    dst=fixed_byte_home(e->left,0,&to);
    if(!dst)return 0;
    value=e->right;
    while(value->kind==EX_CAST&&physical_integer_byte(value->type,0)&&
          (value->type.base==TY_CHAR||value->type.base==TY_INT))value=value->left;
    op=value->op;
    divide=value->kind==EX_BINARY&&(op=='/'||op=='%');
    if((op=='*'||divide)&&cg.function->symbol->interrupt)return 0;
    if(divide){
        Expr *lhs=comparison_byte(value->left,&is_unsigned);
        Expr *rhs=comparison_byte(value->right,&rhs_unsigned);
        if(value->type.base!=TY_INT||value->type.is_unsigned||
           !lhs||width(lhs->type)!=1||!rhs||width(rhs->type)!=1)return 0;
        signed_result=!is_unsigned||(op=='/'&&!rhs_unsigned);
    }
    if(value->kind==EX_BINARY&&(op==TOK_SHL||op==TOK_SHR)&&
       value->type.base==TY_INT&&!value->type.is_unsigned){
        Expr *operand=comparison_byte(value->left,&is_unsigned);
        if(!operand||width(operand->type)!=1)return 0;
        shift=1;
    }
    if(value->kind==EX_BINARY&&(basic_integer_op(op)||shift||op=='*'||divide)){
        right=arithmetic_byte_home(value->right,&ro);
        if(!right)return 0;
    }else if(value->kind!=EX_UNARY||(op!='-'&&op!='~'))return 0;
    left=arithmetic_byte_home(value->left,&lo);
    if(!left)return 0;
    if(signed_result)code("    ldx #0\n");
    code("    sep #$20\n.a8\n    lda ");array_operand(left,lo);code("\n");
    if(shift){
        unsigned loop=++cg.label,done=++cg.label;
        code("    pha\n    lda ");if(cg.stack_leaf)++cg.stack_bias;
        array_operand(right,ro);if(cg.stack_leaf)--cg.stack_bias;
        code("\n    rep #$20\n.a16\n    and #$000F\n    tax\n    sep #$20\n.a8\n    pla\n"
             "    cpx #0\n    beq cg_%s_%u\n",cg.parser->unit,done);
        label(loop);
        code(op==TOK_SHL?"    asl a\n":is_unsigned?"    lsr a\n":"    cmp #$80\n    ror a\n");
        code("    dex\n    bne cg_%s_%u\n",cg.parser->unit,loop);
        label(done);
    }else if(op=='*'){
        /* The low product byte is independent of the operands' signs.
         * CLC, NOP and the long fetch cover the multiplier latency. */
        code("    sta f:$004202\n    lda ");array_operand(right,ro);
        code("\n    sta f:$004203\n    clc\n    nop\n    lda f:$004216\n");
    }else if(divide){
        unsigned wait;
        if(!is_unsigned)code("    bpl :+\n    eor #$FF\n    inc a\n    inx\n:\n");
        code("    sta f:$004204\n    lda #0\n    sta f:$004205\n    lda ");
        array_operand(right,ro);code("\n");
        if(!rhs_unsigned){
            code("    bpl :+\n    eor #$FF\n    inc a\n");
            if(op=='/')code("    dex\n");
            code(":\n");
        }
        /* Seven NOPs and the long load fetch cover the divider latency */
        code("    sta f:$004206\n");
        for(wait=0;wait<7;++wait)code("    nop\n");
        code(op=='/'?"    lda f:$004214\n":"    lda f:$004216\n");
        if(signed_result)code("    cpx #0\n    beq :+\n    eor #$FF\n    inc a\n:\n");
    }else if(right){
        if(op=='+'||op=='-')code("    %s\n",op=='+'?"clc":"sec");
        code("    %s ",op=='+'?"adc":op=='-'?"sbc":op=='&'?"and":op=='|'?"ora":"eor");
        array_operand(right,ro);code("\n");
    }else{
        code("    eor #$FF\n");
        if(op=='-')code("    inc a\n");
    }
    code("    sta ");array_operand(dst,to);code("\n    rep #$20\n.a16\n");
    divmod_written(e->left);return 1;
}
/* A discarded byte store only demands the selected source byte. Retain
 * full-width volatile reads, and leave local frame/DP layout to normal code. */
static int store_projected_byte(Expr *e)
{
    Expr *value,*cursor=NULL;
    Symbol *src,*dst,*pointer=NULL;
    unsigned from=0,to=0,byte=0;
    uint32_t mask,count,address=0;
    if(cg.parser->no_strength_reduction||e->kind!=EX_ASSIGN||e->op||
       width(e->left->type)!=1||e->left->type.is_bool)return 0;
    dst=e->left->kind==EX_OBJECT?e->left->symbol:fixed_memory_object(e->left,&to);
    if(!dst){
        Expr *post=e->left->kind==EX_DEREF?e->left->left:NULL;
        if(!post||post->kind!=EX_POST||(post->op!=TOK_INC&&post->op!=TOK_DEC)||
           !post->type.pointers||far_pointer(post->type)||volatile_expression(e))return 0;
        cursor=post->left;
        pointer=cursor->kind==EX_OBJECT?cursor->symbol:fixed_memory_object(cursor,&to);
        if(!pointer||pointer->owner||pointer->type.banked)return 0;
    }else if(dst->owner||dst->type.banked)return 0;
    value=e->right;
    while(value->kind==EX_CAST&&!value->type.pointers&&!value->type.is_bool&&
          (value->type.base==TY_CHAR||value->type.base==TY_INT))value=value->left;
    if(value->kind==EX_BINARY&&value->op=='&'&&integer_constant(value->right,&mask)&&(mask&255)==255)
        value=value->left;
    if(value->kind==EX_BINARY&&value->op==TOK_SHR&&integer_constant(value->right,&count)&&
       count<=24&&!(count%8)&&count+8<=8*width(value->left->type)){
        byte=(unsigned)count/8;value=value->left;
    }
    if(value->type.pointers||value->type.base==TY_FLOAT||value->type.array||
       (byte?volatile_expression(e->right):width(value->type)!=1))return 0;
    src=value->kind==EX_OBJECT?value->symbol:fixed_memory_object(value,&from);
    if(src){if(src->owner)return 0;}
    else{
        if(byte||value->kind!=EX_DEREF||value->left->kind!=EX_INT||
           !far_pointer(value_type(value->left->type)))return 0;
        address=value->left->value&0xffffffu;
    }
    if(pointer){
        code("    ldx ");array_operand(pointer,to);
        code("\n    %s ",e->left->left->op==TOK_INC?"inc":"dec");array_operand(pointer,to);code("\n");
    }
    code("    sep #$20\n.a8\n    lda ");
    if(src)array_operand(src,from+byte);else code("f:$%06X",address);
    code("\n    sta ");if(dst)array_operand(dst,to);else code("a:$0000,x");
    code("\n    rep #$20\n.a16\n");
    if(cursor)divmod_written(cursor);
    return 1;
}
/* All discarded contexts (statements, comma operands and for steps) share
 * the same update selection; none needs the old postincrement value. */
static int discarded_direct_increment(Expr *e)
{
    Symbol *v;
    if((e->kind==EX_POST||e->kind==EX_PRE)&&e->left->type.banked&&direct_wram_access(e,0))return 1;
    if(fixed_binary32_increment(e,0))return 1;
    if(!direct_increment(e))return 0;
    if(strength_update(e,0))return 1;
    v=e->left->symbol;
    if(width(e->type)==1){
        if(cg.parser->no_strength_reduction)return 0;
        if((!v->owner&&!v->type.banked)||(!cg.retained_index&&!cg.scan_cursor&&mapped_word_home(v))){
            if(!v->owner)v->used=1;
            code("; direct discarded byte update\n    sep #$20\n.a8\n    %s ",e->op==TOK_INC?"inc":"dec");array_operand(v,0);code("\n    rep #$20\n.a16\n");
        }else{
            load_symbol(v);increment_value(e->type,e->op);store_symbol(v);
        }
        divmod_written(e->left);return 1;
    }
    if(!cg.retained_index&&!cg.scan_cursor&&increment_step(e->type)==1&&mapped_word_home(v)){
        code("    %s ",e->op==TOK_INC?"inc":"dec");array_operand(v,0);code("\n");
    }else if(v->owner||increment_step(e->type)!=1){
        load_symbol(v);increment_value(e->type,e->op);store_symbol(v);
    }else{
        v->used=1;code("    %s %s:_%s\n",e->op==TOK_INC?"inc":"dec",v->dpage?"z":"a",v->asm_name);
    }
    divmod_written(e->left);return 1;
}
/* A discarded byte compound subtraction can evaluate a narrowed difference
 * in A8, provided all homes are private, nonvolatile word-sized locals.  The
 * cast before the shift is essential: it truncates before the shift. */
static int discarded_byte_shift_difference(Expr *e)
{
    Expr *target,*sum,*shift,*cast,*diff,*other;Symbol *v,*w;unsigned n,k;
    if(cg.parser->no_strength_reduction||e->kind!=EX_ASSIGN||e->op!='-'||
       volatile_expression(e)||(target=e->left)->kind!=EX_OBJECT||
       width(target->type)!=1||!target->type.is_unsigned||target->type.is_bool||target->type.pointers)return 0;
    v=target->symbol;if(!v->owner||v->type.array||v==cg.scalar_first||v==cg.leaf_count||v==cg.scan_cursor||
                         v==cg.numeric_index||v==cg.numeric_recurrence||v==cg.retained_index)return 0;
    sum=e->right;
    if(sum->kind!=EX_BINARY||sum->op!='+'||sum->right->kind!=EX_INT)return 0;
    n=sum->right->value;if(n>255)return 0;
    shift=sum->left;
    if(shift->kind!=EX_BINARY||shift->op!=TOK_SHR||shift->right->kind!=EX_INT||shift->right->value>7)return 0;
    k=shift->right->value;cast=shift->left;
    if(cast->kind!=EX_CAST||width(cast->type)!=1||!cast->type.is_unsigned||cast->type.is_bool||cast->type.pointers)return 0;
    diff=cast->left;
    if(diff->kind!=EX_BINARY||diff->op!='-'||diff->left->kind!=EX_OBJECT||diff->left->symbol!=v)return 0;
    other=diff->right;
    if(other->kind==EX_CAST&&width(other->type)==1&&other->type.is_unsigned&&!other->type.is_bool&&!other->type.pointers)other=other->left;
    if(other->kind!=EX_OBJECT||width(other->type)>2||!other->type.is_unsigned||other->type.pointers)return 0;
    w=other->symbol;if(!w->owner||w->type.array||w==cg.scalar_first||w==cg.leaf_count||w==cg.scan_cursor||
                         w==cg.numeric_index||w==cg.numeric_recurrence||w==cg.retained_index)return 0;
    code("; discarded byte narrowed difference\n    sep #$20\n.a8\n    lda ");array_operand(v,0);
    code("\n    sec\n    sbc ");array_operand(w,0);code("\n");
    while(k--)code("    lsr a\n");
    if(n)code("    clc\n    adc #$%02X\n",n);
    code("    pha\n");if(cg.stack_leaf)++cg.stack_bias;
    code("    lda ");array_operand(v,0);code("\n    sec\n    sbc 1,s\n    xba\n    pla\n    xba\n");
    if(cg.stack_leaf)--cg.stack_bias;
    code("    rep #$20\n.a16\n    and #$00FF\n    sta ");array_operand(v,0);code("\n");
    divmod_written(target);return 1;
}
static int discarded_fixed_long_unary(Expr *e)
{
    Expr *value,*input;
    Symbol *destination;
    unsigned offset=0;
    int integer;
    if(e->kind!=EX_ASSIGN||e->op||e->type.pointers||
       (e->type.base!=TY_LONG&&e->type.base!=TY_FLOAT))return 0;
    value=e->right;
    if(value->kind!=EX_UNARY||(value->op!='-'&&value->op!='~')||value->type.base!=e->type.base)return 0;
    input=value->left;
    if(input->type.base!=e->type.base||!fixed_memory_word(input,4,0,0)||!fixed_memory_word(e->left,4,0,0))return 0;
    destination=e->left->kind==EX_OBJECT?e->left->symbol:fixed_memory_object(e->left,&offset);
    if(!destination||(destination->owner&&volatile_expression(e)))return 0;

    integer=e->type.base==TY_LONG;
    /* Retain the low result in X until both input words have been read */
    if(integer&&value->op=='-')code("    sec\n    lda #0\n    sbc ");
    else code("    lda ");
    fixed_memory_word(input,4,0,1);code("\n");
    if(value->op=='~')code("    eor #$FFFF\n");
    code("    tax\n");
    if(integer&&value->op=='-')code("    lda #0\n    sbc ");
    else code("    lda ");
    fixed_memory_word(input,4,2,1);code("\n");
    if(value->op=='~')code("    eor #$FFFF\n");
    else if(!integer)code("    eor #$8000\n");
    if(destination->owner){
        code("    sta ");array_operand(destination,offset+2);
        code("\n    txa\n    sta ");array_operand(destination,offset);code("\n");
    }else{
        code("    stx ");array_operand(destination,offset);
        code("\n    sta ");array_operand(destination,offset+2);code("\n");
    }
    divmod_written(e->left);
    return 1;
}
static Expr *doubled_long_source(Expr *e)
{
    uint32_t factor;
    if(e->kind!=EX_BINARY||e->type.base!=TY_LONG||e->type.pointers)return NULL;
    if((e->op==TOK_SHL||e->op=='*')&&integer_constant(e->right,&factor)&&
       factor==(e->op==TOK_SHL?1u:2u))return e->left;
    if(e->op=='*'&&integer_constant(e->left,&factor)&&factor==2)return e->right;
    return NULL;
}
static void indirect_long_constant_x(unsigned offset,uint32_t bits)
{
    for(unsigned i=0;i<4;i+=2){
        unsigned word=(bits>>(8*i))&65535;
        if(word&&(!i||word!=(bits&65535)))code("    lda #$%04X\n",word);
        code("    %s a:$%04X,x\n",word?"sta":"stz",offset+i);
    }
}
static int discarded_indirect_long_store(Expr *e)
{
    unsigned at;
    uint32_t bits;
    if(cg.parser->no_strength_reduction||cg.parser->no_indexed_operands||
       cg.retained_index||cg.retained_second||cg.scan_cursor||e->kind!=EX_ASSIGN||e->op||
       !indirect_near_long(e->left)||volatile_expression(e))return 0;
    if(integer_constant(e->right,&bits)){
        at=assign_base_x(e->left);
        indirect_long_constant_x(at,bits);
    }else{
        if(!indirect_near_long(e->right)||!destination_x_preserves_a(e->left))return 0;
        /* Snapshot both words before writing through a possibly aliased base */
        at=assign_base_x(e->right);
        code("    lda a:$%04X,x\n    pha\n    lda a:$%04X,x\n",at+2,at);
        at=assign_base_x(e->left);
        code("    sta a:$%04X,x\n    pla\n    sta a:$%04X,x\n",at,at+2);
    }
    divmod_written(e->left);
    return 1;
}
static Expr *indirect_long_member_base(Expr *e,unsigned *offset)
{
    int pointer;
    Expr *base;
    if(e->kind!=EX_MEMBER||!indirect_near_long(e)||volatile_expression(e))return NULL;
    base=member_root(e,offset,&pointer);
    return pointer&&*offset<=65532&&base->kind==EX_OBJECT&&
        !far_pointer(value_type(base->type))&&loop_private(base->symbol)?base:NULL;
}
/* Keep both private structure pointers in registers for successive field
 * copies and source resets. Snapshot a complete word pair before each store. */
static Statement *indirect_long_fields(Statement *s)
{
    Expr *src=NULL,*dst=NULL;
    Statement *p,*last=NULL;
    unsigned count=0;
    if(cg.parser->no_strength_reduction||cg.parser->no_body_optimizations||cg.parser->no_indexed_operands||
       cg.scan_cursor||cg.bound||cg.bound_pending||cg.affine_active||cg.retained_index||
       cg.retained_second||cg.numeric_index||cg.scalar_leaf)return NULL;
    for(p=s;p&&p->kind==ST_EXPR;p=p->next){
        Expr *e=p->expression,*to,*from;
        unsigned offset;
        uint32_t bits;
        if(!e||e->kind!=EX_ASSIGN||e->op||!(to=indirect_long_member_base(e->left,&offset)))break;
        from=indirect_long_member_base(e->right,&offset);
        if(!src){
            if(!from||from->symbol==to->symbol)break;
            src=from;dst=to;
        }
        if(from){
            if(from->symbol!=src->symbol||to->symbol!=dst->symbol)break;
        }else if(to->symbol!=src->symbol||!integer_constant(e->right,&bits))break;
        last=p;++count;
    }
    if(count<3)return NULL;
    emit_value_x(src);emit_value(dst);code("; shared structure pointers\n    phy\n    tay\n");
    for(p=s;;p=p->next){
        Expr *e=p->expression;
        unsigned to,from;
        int pointer;
        uint32_t bits;
        member_root(e->left,&to,&pointer);
        if(integer_constant(e->right,&bits))indirect_long_constant_x(to,bits);
        else{
            member_root(e->right,&from,&pointer);
            code("    lda a:$%04X,x\n    pha\n    lda a:$%04X,x\n    sta a:$%04X,y\n"
                 "    pla\n    sta a:$%04X,y\n",from+2,from,to,to+2);
        }
        if(p==last)break;
    }
    code("    ply\n");cg.divmod_available=0;
    return last;
}
/* An unescaped scalar home cannot alias an indirect operand. Keep the
 * address in X and move each word through A, carrying a doubling if needed. */
static int discarded_indirect_long_transfer(Expr *e)
{
    Expr *fixed,*indirect;
    Symbol *home=NULL;
    unsigned offset=0,at;
    Expr *doubled;
    int load,inplace,double_value;
    const char *mode;
    if(cg.parser->no_strength_reduction||cg.parser->no_body_optimizations||
       cg.retained_index||cg.retained_second||cg.scan_cursor||e->kind!=EX_ASSIGN||e->op||
       e->type.base!=TY_LONG||e->type.pointers||volatile_expression(e))return 0;
    load=e->left->kind==EX_OBJECT;
    fixed=load?e->left:e->right;
    indirect=load?e->right:e->left;
    doubled=doubled_long_source(e->right);
    inplace=!load&&doubled&&indirect->kind==EX_DEREF&&doubled->kind==EX_DEREF&&
        element_address_pure(indirect->left)&&same_element_address(indirect->left,doubled->left);
    double_value=(load&&doubled)||inplace;
    if(load&&doubled)indirect=doubled;
    if(indirect->kind!=EX_DEREF||indirect->type.base!=TY_LONG||indirect->type.pointers||
       indirect->type.banked||far_pointer(value_type(indirect->left->type))||
       direct_memory_object(indirect,&at))return 0;
    if(!inplace&&(fixed->kind!=EX_OBJECT||fixed->type.base!=TY_LONG||fixed->type.pointers||
       !(home=fixed_byte_home(fixed,0,&offset))||!loop_private(home)))return 0;
    mode=strength_wram_pointer(indirect->left)?"z":"a";
    at=assign_base_x(indirect);
    for(unsigned i=0;i<4;i+=2){
        if(load||inplace){
            code("    lda %s:$%04X,x\n",mode,at+i);
            if(double_value)code(i?"    rol a\n":"    asl a\n");
            if(inplace)code("    sta %s:$%04X,x\n",mode,at+i);
            else{code("    sta ");array_operand(home,offset+i);code("\n");}
        }else{
            code("    lda ");array_operand(home,offset+i);code("\n    sta %s:$%04X,x\n",mode,at+i);
        }
    }
    divmod_written(e->left);
    return 1;
}
/* A narrow unsigned load can feed a doubling recurrence without pushing a
 * widened RHS and a shifted accumulator through the general binary ABI. */
static Expr *far_doubling_sum(Expr *e,Symbol **destination)
{
    Expr *value,*product,*load;
    Symbol *sum;
    uint32_t factor;
    unsigned bytes;
    if(cg.parser->no_strength_reduction||!e||e->kind!=EX_ASSIGN||e->op||
       e->left->kind!=EX_OBJECT||volatile_expression(e))return NULL;
    sum=e->left->symbol;bytes=width(sum->type);value=e->right;
    if(!sum->owner||sum->type.banked||sum->type.pointers||!sum->type.is_unsigned||
       (sum->type.base!=TY_INT&&sum->type.base!=TY_LONG)||(bytes!=2&&bytes!=4)||
       value->kind!=EX_BINARY||value->op!='+'||!same_value_representation(sum->type,value->type))return NULL;
    product=value->left;load=value->right;
    if(product->kind!=EX_BINARY||product->op!='*'||product->left->kind!=EX_OBJECT||
       product->left->symbol!=sum||!same_value_representation(product->type,sum->type)||
       !integer_constant(product->right,&factor)||factor!=2)return NULL;
    while(load->kind==EX_CAST&&!load->type.pointers&&!load->type.is_bool&&load->type.is_unsigned&&
          (load->type.base==TY_CHAR||load->type.base==TY_INT||load->type.base==TY_LONG)&&
          width(load->type)>=width(load->left->type))load=load->left;
    if(load->kind!=EX_DEREF||!load->type.banked||!load->type.is_unsigned||load->type.pointers||
       (load->type.base!=TY_CHAR&&load->type.base!=TY_INT)||load->type.is_bool||
       width(load->type)>2||!loop_private(sum)||scalar_writes_expr(load,sum))return NULL;
    *destination=sum;return load;
}
static void add_far_doubling_sum(Symbol *sum)
{
    unsigned bytes=width(sum->type);
    cg.arithmetic=1;
    code("    sta z:__arith_rhs\n    lda ");
    array_operand(sum,0);code("\n    asl a\n");
    if(bytes==4){
        code("    tax\n    lda ");array_operand(sum,2);code("\n    rol a\n    sta ");
        array_operand(sum,2);code("\n    txa\n");
    }
    code("    clc\n    adc z:__arith_rhs\n    sta ");array_operand(sum,0);code("\n");
    if(bytes==4){
        code("    bcc :+\n    lda ");array_operand(sum,2);code("\n    inc a\n    sta ");
        array_operand(sum,2);code("\n:\n");
    }
}
static int discarded_far_doubling_sum(Expr *e)
{
    Symbol *sum;Expr *load=far_doubling_sum(e,&sum);
    if(!load)return 0;
    emit_value(load);
    code("; far load into unsigned doubling sum\n");
    add_far_doubling_sum(sum);
    divmod_written(e->left);return 1;
}
/* Keep the base for the entire span. A word-sized sum can also stay in A
 * between elements because the only other work is the indexed load. */
static void emit_far_doubling_span(Symbol *sum,Type element,unsigned first,int step,unsigned count)
{
    unsigned i;
    if(width(sum->type)==2){
        unsigned value_bytes=width(element);
        unsigned previous=0;
        code("    lda ");array_operand(sum,0);
        code("\n    phy\n");
        for(i=0;i<count;++i){
            unsigned displacement=(unsigned)((int)first+(int)i*step);
            code("    asl a\n    sta z:__arith_rhs\n");
            if(displacement){
                if(previous&&(step==1||step==-1))
                    code("    %s\n",step>0?"iny":"dey");
                else code("    ldy #$%04X\n",displacement);
            }
            previous=displacement;
            if(value_bytes==1)code("    sep #$20\n.a8\n");
            code("    lda [__arith_lhs]%s\n",displacement?",y":"");
            if(value_bytes==1)code("    rep #$20\n.a16\n    and #$00FF\n");
            code("    clc\n    adc z:__arith_rhs\n");
        }
        code("    ply\n    sta ");array_operand(sum,0);code("\n");
    }else for(i=0;i<count;++i){
        unsigned displacement=(unsigned)((int)first+(int)i*step);
        load_far_pointer_home("__arith_lhs",element,displacement);
        add_far_doubling_sum(sum);
    }
}
/* Keep one long-indirect base across a small constant-trip reduction */
static int unroll_far_doubling_sum(Statement *s)
{
    Statement *initial=s->initial,*body=s->body;
    Expr *test=s->expression,*init,*load,*address,*base,*index,*step=s->step;
    Symbol *sum,*counter;
    uint32_t first,limit;
    unsigned count,stride;
    int descending;
    if(cg.parser->no_loop_unroll||cg.parser->no_strength_reduction||cg.function->jump_label_count||
       cg.switch_depth||cg.retained_index||cg.retained_second||cg.scan_cursor||cg.affine_active||
       s->kind!=ST_FOR||!initial||initial->next||initial->kind!=ST_EXPR||!test||test->kind!=EX_BINARY||
       (test->op!='<'&&test->op!='>')||test->left->kind!=EX_OBJECT||test->right->kind!=EX_INT||
       !integer_constant(test->right,&limit))return 0;
    init=initial->expression;counter=test->left->symbol;
    if(!init||init->kind!=EX_ASSIGN||init->op||init->left->kind!=EX_OBJECT||init->left->symbol!=counter||
       !body_private(counter)||counter->type.base!=TY_INT||!counter->type.is_unsigned||counter->type.pointers||
       init->right->kind!=EX_INT||!integer_constant(init->right,&first)||first>65535||limit>65535||
       !common_type(test->left->type,test->right->type).is_unsigned)return 0;
    while(body&&body->kind==ST_BLOCK&&!body->next)body=body->body;
    if(!body||body->next||body->kind!=ST_EXPR||!(load=far_doubling_sum(body->expression,&sum))||sum==counter)return 0;
    address=load->left;
    if(address->kind!=EX_BINARY||address->op!='+')return 0;
    base=address->left;index=address->right;
    if(base->kind!=EX_OBJECT||base->type.array||!far_pointer(value_type(base->type)))return 0;
    descending=test->op=='>';
    if(descending){
        if(step||first<=limit||index->kind!=EX_PRE||index->op!=TOK_DEC)return 0;
        index=index->left;count=(unsigned)(first-limit);
    }else{
        if(first>=limit||!step||(step->kind!=EX_PRE&&step->kind!=EX_POST)||step->op!=TOK_INC||
           step->left->kind!=EX_OBJECT||step->left->symbol!=counter)return 0;
        count=(unsigned)(limit-first);
    }
    stride=width(pointed_type(value_type(base->type)));
    if(index->kind!=EX_OBJECT||index->symbol!=counter||count>4||stride!=width(load->type)||
       (first>limit?first:limit)>65535u/stride)return 0;
    code("; unrolled indexed far doubling sum: %u elements\n",count);
    stage_far_home(base->symbol);
    emit_far_doubling_span(sum,load->type,(unsigned)(descending?first-1:first)*stride,
                          descending?-(int)stride:(int)stride,count);
    code("    lda #$%04X\n    sta ",(unsigned)limit);array_operand(counter,0);code("\n");
    cg.divmod_available=0;return 1;
}
/* One private far cursor, one source read, and one recurrence per element.
 * The loop has no calls and publishes its cursor at the sentinel. */
static int far_sentinel_doubling_loop(Statement *s)
{
    Statement *body=s->body,*guard=NULL;
    Expr *test=s->expression,*value,*load,*step=s->step;
    Symbol *sum,*cursor;
    uint32_t sentinel=0;
    unsigned start,done,stride;
    int increment,goto_loop=s->kind==ST_LABEL;
    const char *home;
    char indirect[32];
    if(cg.parser->no_strength_reduction||cg.parser->no_register_cursors||cg.affine_active||
       cg.retained_index||cg.retained_second||cg.scan_cursor||
       (!goto_loop&&(cg.function->jump_label_count||cg.switch_depth||
        (s->kind!=ST_FOR&&s->kind!=ST_WHILE))))return 0;
    while(body&&body->kind==ST_BLOCK&&!body->next)body=body->body;
    if(!body)return 0;
    if(goto_loop){
        Statement *advance,*back;
        if(body->kind!=ST_IF||body->next||body->alternate)return 0;
        test=body->expression;body=body->body;
        while(body&&body->kind==ST_BLOCK&&!body->next)body=body->body;
        if(!body||!(advance=body->next)||advance->kind!=ST_EXPR||!(back=advance->next)||
           back->kind!=ST_GOTO||back->next||back->jump_label!=s->jump_label)return 0;
    }else if(!test||(test->kind==EX_INT&&test->value)){
        Statement *leave;
        guard=body;
        if(guard->kind!=ST_IF||guard->alternate||!(leave=guard->body)||
           leave->kind!=ST_BREAK||leave->next)return 0;
        test=guard->expression;body=guard->next;
    }
    if(!test||volatile_expression(test)||!body||body->kind!=ST_EXPR||
       !(load=far_doubling_sum(body->expression,&sum)))return 0;
    value=test;
    if(test->kind==EX_BINARY){
        if(test->op!=(guard?TOK_EQ:TOK_NE)||test->right->kind!=EX_INT||!integer_constant(test->right,&sentinel)||
           reg_width(common_type(test->left->type,test->right->type))!=2)return 0;
        value=test->left;
    }else if(guard)return 0;
    while(value->kind==EX_CAST&&!value->type.pointers&&!value->type.is_bool&&
          (value->type.base==TY_INT||value->type.base==TY_CHAR)&&
          (width(value->type)>width(value->left->type)||
           same_value_representation(value->type,value->left->type)))value=value->left;
    if(value->kind!=EX_DEREF||!same_value_representation(value->type,load->type)||
       value->left->kind!=EX_OBJECT)return 0;
    stride=width(load->type);
    if(sentinel>(stride==1?255u:65535u))return 0;
    if(load->left->kind==EX_POST){
        if(step||body->next)return 0;
        step=load->left;
    }else{
        if(!body_equal(value->left,load->left)||(step&&body->next))return 0;
        if(body->next){
            if((!goto_loop&&body->next->next)||body->next->kind!=ST_EXPR)return 0;
            step=body->next->expression;
        }
    }
    if(!step||!(cursor=far_update_home(step))||cursor!=value->left->symbol||
       !loop_private(cursor)||increment_step(step->type)!=stride)return 0;
    increment=step->op==TOK_INC;
    if(s->initial)emit_statements(s->initial);
    code("; far sentinel doubling sum: one load per element\n");
    home=far_pointer_dp_home(value->left);
    if(home)snprintf(indirect,sizeof indirect,"%s",home);
    else{
        stage_far_home(cursor);
        snprintf(indirect,sizeof indirect,"__arith_lhs");
    }
    start=++cg.label;done=++cg.label;
    label(start);
    if(stride==1)code("    sep #$20\n.a8\n");
    code("    lda [%s]\n",indirect);
    if(sentinel)code("    cmp #$%0*X\n",stride*2,(unsigned)sentinel);
    if(stride==1)code("    rep #$20\n.a16\n");
    code("    beq cg_%s_%u\n",cg.parser->unit,done);
    if(stride==1)code("    and #$00FF\n");
    add_far_doubling_sum(sum);
    if(increment&&stride==1)
        code("    inc z:%s\n    bne cg_%s_%u\n",indirect,cg.parser->unit,start);
    else if(stride==1)
        code("    lda z:%s\n    dec a\n    sta z:%s\n"
             "    cmp #$FFFF\n    bne cg_%s_%u\n",indirect,indirect,cg.parser->unit,start);
    else
        code("    lda z:%s\n    %s\n    %s #$%04X\n    sta z:%s\n    %s cg_%s_%u\n",
             indirect,increment?"clc":"sec",increment?"adc":"sbc",stride,indirect,increment?"bcc":"bcs",
             cg.parser->unit,start);
    code("    sep #$20\n.a8\n    %s ",increment?"inc":"dec");
    if(home)array_operand(cursor,2);else code("z:__arith_lhs+2");
    code("\n    rep #$20\n.a16\n");
    jump(start);label(done);
    if(!home){
        code("    lda z:__arith_lhs\n    sta ");array_operand(cursor,0);
        code("\n    lda z:__arith_lhs+2\n    sta ");array_operand(cursor,2);code("\n");
    }
    cg.divmod_available=0;return 1;
}
/* Hoist a bounded pointer difference into the fixed unroll planner. The
 * cursor must start at a constant offset from the exact base in the test. */
static int unroll_far_pointer_sum(Statement *previous,Statement *loop)
{
    Statement *body=loop->body;
    Expr *init,*test=loop->expression,*from,*to,*load,*update,*base;
    Symbol *sum,*cursor;
    unsigned first,limit,stride,count;
    int increment;
    if(cg.parser->no_loop_unroll||cg.parser->no_strength_reduction||cg.function->jump_label_count||
       cg.switch_depth||cg.affine_active||cg.retained_index||cg.retained_second||cg.scan_cursor||
       loop->kind!=ST_DO||!previous||previous->kind!=ST_EXPR||!(init=previous->expression)||
       init->kind!=EX_ASSIGN||init->op||init->left->kind!=EX_OBJECT||volatile_expression(init)||
       !test||test->kind!=EX_BINARY||test->op!=TOK_NE||volatile_expression(test))return 0;
    cursor=init->left->symbol;from=init->right;to=test->right;
    if(test->left->kind!=EX_OBJECT||test->left->symbol!=cursor||
       from->kind!=EX_BINARY||from->op!='+'||to->kind!=EX_BINARY||to->op!='+'||
       !(base=far_compare_home(from->left))||!body_equal(from->left,to->left)||
       !same_value_representation(from->type,cursor->type)||!loop_private(cursor)||
       base->symbol==cursor||!far_small_displacement(from->left,from->right,&first)||
       !far_small_displacement(to->left,to->right,&limit))return 0;
    while(body&&body->kind==ST_BLOCK&&!body->next)body=body->body;
    if(!body||body->next||body->kind!=ST_EXPR||!(load=far_doubling_sum(body->expression,&sum)))return 0;
    update=load->left;stride=width(load->type);
    if(far_update_home(update)!=cursor||increment_step(update->type)!=stride)return 0;
    increment=update->op==TOK_INC;
    if((increment?first>=limit:first<=limit))return 0;
    count=increment?limit-first:first-limit;
    if(count%stride||(count/=stride)>4)return 0;
    code("; unrolled far pointer doubling sum: %u elements\n",count);
    stage_far_home(base->symbol);
    if(update->kind==EX_PRE)first=increment?first+stride:first-stride;
    emit_far_doubling_span(sum,load->type,first,increment?(int)stride:-(int)stride,count);
    emit_value(to);
    code("    sta ");array_operand(cursor,0);code("\n    txa\n    sta ");array_operand(cursor,2);code("\n");
    cg.divmod_available=0;return 1;
}
static int body_discard_effect(Expr *e);
static int body_pure_discard_call(Expr *e);
static int store_wide_integer_literal(Expr *e,Symbol *home,unsigned offset);
static void emit_word_imm_bitwise(int op,uint16_t imm)
{
    if(op=='^'){if(imm)code("    eor #$%04X\n",imm);}
    else if(op=='|'){
        if(imm==0xffffu)code("    lda #$FFFF\n");
        else if(imm)code("    ora #$%04X\n",imm);
    }else if(op=='&'){
        if(!imm)code("    lda #$0000\n");
        else if(imm!=0xffffu)code("    and #$%04X\n",imm);
    }
}
static int discarded_long_shift_bitwise(Expr *e)
{
    Expr *target,*rhs,*lhs_val,*imm,*sh;
    Symbol *dst,*src;
    unsigned dst_off,src_off,first,second;
    uint32_t poly,steps;
    int bit_op,unsigned_shr;
    if(cg.parser->no_strength_reduction||cg.parser->no_body_optimizations||
       e->kind!=EX_ASSIGN||e->op||!physical_integer_byte(e->left->type,0)||
       width(e->left->type)!=4||volatile_expression(e))return 0;
    target=e->left;
    dst=fixed_byte_home(target,0,&dst_off);
    if(!dst||dst->type.banked)return 0;
    rhs=unwrap_same_width_cast(e->right,4);
    if(rhs->kind!=EX_BINARY||(rhs->op!='^'&&rhs->op!='|'&&rhs->op!='&')||
       rhs->type.pointers||rhs->type.base!=TY_LONG)return 0;
    bit_op=rhs->op;
    lhs_val=rhs->left;imm=rhs->right;
    if(integer_constant(lhs_val,&poly)){lhs_val=rhs->right;imm=rhs->left;}
    if(!integer_constant(imm,&poly))return 0;
    sh=unwrap_same_width_cast(lhs_val,4);
    if(sh->kind!=EX_BINARY||(sh->op!=TOK_SHL&&sh->op!=TOK_SHR)||
       sh->type.pointers||sh->type.base!=TY_LONG||
       !integer_constant(sh->right,&steps)||steps!=1)return 0;
    src=fixed_byte_home(sh->left,0,&src_off);
    if(!src||src->type.banked)return 0;
    if(dst==src&&dst_off!=src_off&&dst_off<src_off+4&&src_off<dst_off+4)return 0;
    first=sh->op==TOK_SHL?0:2;
    second=2-first;
    unsigned_shr=sh->type.is_unsigned||(sh->left->known.valid&&sh->left->known.min>=0);
    code("    lda ");array_operand(src,src_off+first);code("\n");
    if(sh->op==TOK_SHL)code("    asl a\n");
    else if(unsigned_shr)code("    lsr a\n");
    else code("    cmp #$8000\n    ror a\n");
    emit_word_imm_bitwise(bit_op,(uint16_t)(poly>>(first*8)));
    code("    sta ");array_operand(dst,dst_off+first);code("\n");
    code("    lda ");array_operand(src,src_off+second);code("\n");
    code("    %s a\n",sh->op==TOK_SHL?"rol":"ror");
    emit_word_imm_bitwise(bit_op,(uint16_t)(poly>>(second*8)));
    code("    sta ");array_operand(dst,dst_off+second);code("\n");
    divmod_written(target);
    return 1;
}
static int copy_fixed_long_scalar(Expr *e)
{
    Symbol *from,*to;
    unsigned source,destination;
    if(cg.parser->no_strength_reduction||cg.parser->no_body_optimizations||e->kind!=EX_ASSIGN||e->op||
       (e->type.base!=TY_LONG&&e->type.base!=TY_FLOAT)||e->type.pointers||
       e->right->type.base!=e->type.base||e->right->type.pointers)return 0;
    from=direct_memory_object(e->right,&source);
    if(!from&&e->right->kind==EX_DEREF&&e->right->left->kind==EX_OBJECT&&
       e->right->left->type.array&&!far_pointer(value_type(e->right->left->type))&&
       width(pointed_type(value_type(e->right->left->type)))==4){
        /* A named array's first element also has a fixed relocatable address */
        from=e->right->left->symbol;source=0;
    }
    if(!from||!(to=direct_memory_object(e->left,&destination))||
       (!!from->owner==!!to->owner)||(!loop_private(from)&&!loop_private(to))||
       (volatile_expression(e->left)&&volatile_expression(e->right)))return 0;
    for(unsigned part=0;part<4;part+=2){
        code("    lda ");array_operand(from,source+part);
        code("\n    sta ");array_operand(to,destination+part);code("\n");
    }
    cg.divmod_available=0;
    return 1;
}
/* Track uses of a private word through low-byte casts and bitwise operators.
 * A full-width read, an update, or an escaping address requires both bytes. */
static int low_byte_uses(Expr *e,Symbol *v,int low)
{
    if(!e)return 1;
    if(e->kind==EX_CALL&&e->symbol&&!strcmp(e->symbol->name,"$basic_asm"))return 0;
    if(e->kind==EX_OBJECT&&e->symbol==v)return low;
    if(e->kind==EX_ASSIGN&&!e->op){
        if(!(e->left->kind==EX_OBJECT&&e->left->symbol==v)&&!low_byte_uses(e->left,v,0))return 0;
        return low_byte_uses(e->right,v,width(e->left->type)==1&&!e->left->type.is_bool);
    }
    if(e->kind==EX_CAST&&!e->type.pointers&&known_integer(e->type)&&!e->type.is_bool)
        return low_byte_uses(e->left,v,low||width(e->type)==1);
    if(e->kind==EX_BINARY&&low&&(e->op=='|'||e->op=='&'||e->op=='^'))
        return low_byte_uses(e->left,v,1)&&low_byte_uses(e->right,v,1);
    for(unsigned i=0;i<e->arg_count;++i)if(!low_byte_uses(e->args[i],v,0))return 0;
    return low_byte_uses(e->left,v,0)&&low_byte_uses(e->right,v,0)&&low_byte_uses(e->third,v,0);
}
static int private_low_byte_uses(Statement *s,Symbol *v)
{
    for(;s;s=s->next)
        if(!low_byte_uses(s->expression,v,0)||!low_byte_uses(s->step,v,0)||
           !private_low_byte_uses(s->body,v)||!private_low_byte_uses(s->initial,v)||
           !private_low_byte_uses(s->alternate,v))return 0;
    return 1;
}
static int store_private_low_byte(Expr *e)
{
    if(cg.parser->no_strength_reduction||e->kind!=EX_ASSIGN||e->op||e->left->kind!=EX_OBJECT)return 0;
    Symbol *v=e->left->symbol;
    Expr *rhs=e->right;
    if(rhs->kind==EX_CAST&&word_integer(rhs->type))rhs=rhs->left;
    if(rhs->kind!=EX_DEREF||rhs->type.base!=TY_CHAR||rhs->type.pointers||rhs->type.is_bool||
       (rhs->left->kind!=EX_PRE&&rhs->left->kind!=EX_POST)||
       far_pointer(value_type(rhs->left->type))||volatile_expression(rhs)||
       !word_integer(v->type)||!v->scope||v->storage||!body_private(v)||
       !private_low_byte_uses(cg.function->body,v))return 0;
    /* The normal nonvolatile near-byte lowering already reads a word.
     * Its upper byte cannot affect any use of this local. */
    emit_value_x(rhs->left);
    load_indirect(type(TY_INT,0),strength_wram_pointer(rhs->left));
    store_symbol(v);divmod_written(e->left);return 1;
}
static void emit_discarded(Expr *e)
{
    unsigned offset;
    Symbol *home;
    if(e->kind==EX_ASSIGN&&!e->op&&!cg.parser->no_body_optimizations&&
       known_integer(e->type)&&!body_effect(e->left)&&!body_effect(e->right)&&
       body_equal(e->left,e->right)&&direct_memory_object(e->left,&offset)){
        /* A discarded copy to the same fixed nonvolatile scalar has no effect */
        return;
    }
    if(e->kind==EX_DEREF&&!cg.parser->no_body_optimizations&&!cg.parser->no_strength_reduction&&
       !e->type.array&&!structure_object(e->type)&&!volatile_expression(e)&&!object_volatile(e->type)){
        /* A discarded scalar load still evaluates its address exactly once */
        if(body_discard_effect(e->left)&&!discarded_far_update(e->left))emit_discarded(e->left);
        return;
    }
    if(e->kind==EX_CAST&&numeric(e->type)&&numeric(e->left->type)&&
       e->type.base!=TY_FLOAT&&e->type.base!=TY_DOUBLE&&
       e->left->type.base!=TY_FLOAT&&e->left->type.base!=TY_DOUBLE&&
       !cg.parser->no_body_optimizations&&!cg.parser->no_strength_reduction){
        if(body_discard_effect(e->left))emit_discarded(e->left);
        return;
    }
    if(e->kind==EX_BINARY&&!cg.parser->no_body_optimizations&&!cg.parser->no_strength_reduction&&
       (e->op=='|'||e->op=='&'||e->op=='^'||
        ((comparison(e->op)||e->op==TOK_SHL||e->op==TOK_SHR||e->op=='+'||e->op=='-'||
           e->op=='*'||e->op=='/'||e->op=='%')&&
         numeric(e->left->type)&&numeric(e->right->type)&&
         e->left->type.base!=TY_FLOAT&&e->left->type.base!=TY_DOUBLE&&
         e->right->type.base!=TY_FLOAT&&e->right->type.base!=TY_DOUBLE))){
        if(body_discard_effect(e->left))emit_discarded(e->left);
        if(body_discard_effect(e->right))emit_discarded(e->right);
        return;
    }
    if(e->kind==EX_CALL&&!cg.parser->no_body_optimizations&&!cg.parser->no_strength_reduction&&
       body_pure_discard_call(e)){
        Expr *effect=NULL;
        unsigned i;
        for(i=0;i<e->arg_count;++i)if(body_discard_effect(e->args[i])){
            if(effect)break;
            effect=e->args[i];
        }
        if(i==e->arg_count){
            if(effect)emit_discarded(effect);
            return;
        }
    }
    if(e->kind==EX_COMMA){emit_discarded(e->left);emit_discarded(e->right);}
    else if(e->kind==EX_ASSIGN&&wide_scalar(value_type(e->type))&&e->right->kind==EX_INT&&
            (home=wide_fixed_home(e->left,&offset))&&store_wide_integer_literal(e,home,offset))
        divmod_written(e->left);
    else if(wide_scalar(value_type(e->type))&&wide_value_supported(e))emit_wide_operand(e);
    else if(narrow_wide_compound_supported(e)&&e->left->kind!=EX_BITFIELD)emit_narrow_wide_compound(e);
    else if(e->kind==EX_CALL)emit_call(e,0);
    else if(store_private_low_byte(e)){}
    else if(copy_fixed_long_scalar(e)){}
    else if(discarded_fixed_bitfield_store(e)){}
    else if(indexed_byte_arithmetic(e)||discarded_volatile_byte_arithmetic(e)){}
    else if(discarded_fixed_long_unary(e)){}
    else if(discarded_indirect_long_transfer(e)){}
    else if(discarded_indirect_long_store(e)){}
    else if(discarded_far_doubling_sum(e)){}
    else if(discarded_long_shift_bitwise(e)){}
    else if(fixed_shift_assignment(e)||fixed_byte_assignment(e)){}
    else if(store_projected_byte(e)){}
    else if(volatile_expression(e)&&fixed_byte_test(e)){}
    else if(e->kind==EX_ASSIGN&&structure_object(e->type)&&!e->type.array)emit_aggregate_copy(e,0);
    else if(structure_object(e->type)){
        if(volatile_type(e->type))volatile_aggregate(e,0,0);
        else emit_address(e);
    }
    else if(e->kind==EX_CAST&&e->type.base==TY_VOID&&!e->type.pointers)emit_discarded(e->left);
    else if(discarded_byte_shift_difference(e)){}
    else if(indexed_byte_discard(e)){}
    else if(near_memory_update(e,0)){}
    else if(discarded_direct_increment(e)){}
    else if(fixed_long_increment(e,0)){}
    else if(!cg.parser->no_strength_reduction&&!volatile_expression(e)&&
            (e->kind==EX_PRE||e->kind==EX_POST)&&width(e->type)==1&&!e->type.is_bool&&e->left->kind==EX_OBJECT){
        Symbol *v=e->left->symbol;
        code("; direct discarded byte update\n    sep #$20\n.a8\n");
        if(!v->owner&&!v->type.banked){code("    %s ",e->op==TOK_INC?"inc":"dec");array_operand(v,0);code("\n");}
        else{
            code("    lda ");array_operand(v,0);
            code("\n    %s a\n    sta ",e->op==TOK_INC?"inc":"dec");array_operand(v,0);code("\n");
        }
        code("    rep #$20\n.a16\n");divmod_written(e->left);
    }
    else emit_value(e);
}
static int contains_break(Statement *s)
{
    for(;s;s=s->next){if(s->kind==ST_BREAK)return 1;if(s->kind==ST_WHILE||s->kind==ST_FOR||s->kind==ST_DO||s->kind==ST_SWITCH)continue;
        if(contains_break(s->body)||contains_break(s->alternate))return 1;}return 0;
}
#include "register_loops.inc"
#include "far_loops.inc"
static unsigned expression_references(Expr *e,Symbol *v)
{
    unsigned i,n;if(!e)return 0;
    n=e->kind==EX_OBJECT&&e->symbol==v;
    n+=expression_references(e->left,v)+expression_references(e->right,v)+expression_references(e->third,v);
    for(i=0;i<e->arg_count;++i)n+=expression_references(e->args[i],v);
    return n;
}
static unsigned statement_references(Statement *s,Symbol *v)
{
    unsigned n=0;
    for(;s;s=s->next){
        n+=expression_references(s->expression,v)+expression_references(s->step,v);
        n+=statement_references(s->initial,v)+statement_references(s->body,v)+statement_references(s->alternate,v);
    }
    return n;
}
/* Forward a private word temporary into its immediately following return.
 * Exactly two references prove one definition/use and exclude address escape.
 * A commutative operation can consume the RHS in A and read its other operand
 * afterward, preserving observations made by calls in the RHS. */
static void forward_return(Function *f,Statement *s)
{
    for(;s;s=s->next){
        Expr *assignment,*result,*temporary,*other;Symbol *v;
        forward_return(f,s->initial);forward_return(f,s->body);forward_return(f,s->alternate);
        if(s->kind!=ST_EXPR||!s->next||s->next->kind!=ST_RETURN)continue;
        assignment=s->expression;result=s->next->expression;
        if(assignment->kind!=EX_ASSIGN||assignment->op||assignment->left->kind!=EX_OBJECT||
           !result||result->kind!=EX_BINARY||result->type.base!=TY_INT||result->type.pointers||
           (result->op!='+'&&result->op!='&'&&result->op!='|'&&result->op!='^'))continue;
        v=assignment->left->symbol;
        if(v->owner!=f->id||!v->scope||v->type.base!=TY_INT||v->type.pointers||v->type.array)continue;
        temporary=result->right;other=result->left;
        if(temporary->kind!=EX_OBJECT||temporary->symbol!=v){temporary=result->left;other=result->right;}
        if(temporary->kind!=EX_OBJECT||temporary->symbol!=v||
           !direct_operand(other,result->type,0,0)||statement_references(f->body,v)!=2)continue;
        result->left=assignment->right;result->right=other;
        free(temporary);free(assignment->left);free(assignment);
        s->expression=NULL;s->kind=ST_EMPTY;
        /* Only a trailing home can disappear without relocating other locals */
        if(v->offset+1==f->slots)f->slots-=2;
    }
}
static unsigned region_trips(Statement *s);
static Statement *body_single(Statement *s);
#include "dp_counters.inc"
#include "affine_loops.inc"
#include "switch.inc"
#include "entry_cursors.inc"
static int emit_loop_statement(Statement *s);
static void bound_enter(void);
static void bound_exit(void);
static void region_enter(Statement *s);
/* The statement being emitted and its predecessor: a loop's entry assignment
 * is whichever of them is immediately followed by the loop. */
static Statement *loop_previous,*loop_current;
static void region_exit(Statement *s);
/* Case labels are entry points from an enclosing switch (Duff's device) */
static int statement_has_case(Statement *s)
{
    for(;s;s=s->next){
        if(s->kind==ST_CASE)return 1;
        if(s->kind!=ST_SWITCH&&(statement_has_case(s->body)||statement_has_case(s->alternate)||statement_has_case(s->initial)))return 1;
    }
    return 0;
}
#include "store_fusion.inc"
#include "byte_regions.inc"
/* Build consecutive flag bits through carry when their tests are independent
 * direct reads. Reverse the tests so each rotate puts its bit in order. */
static Statement *carry_mask_sequence(Statement *s)
{
    Expr *init=s->expression,*values[4];
    Statement *next=s->next,*last=NULL;
    Symbol *home;
    uint32_t bits,thresholds[4],masks[4];
    unsigned count=0,word,i;
    int byte=1;
    if(!cg.dp_homes||cg.parser->no_strength_reduction||s->kind!=ST_EXPR||
       !init||init->kind!=EX_ASSIGN||init->op||init->left->kind!=EX_OBJECT||
       !integer_constant(init->right,&bits)||bits)return NULL;
    home=init->left->symbol;
    if(!home->offset||!(home->offset&1)||!body_private(home)||home->type.base!=TY_INT||
       width(home->type)!=2)return NULL;
    word=(home->offset-1)/2;
    if(word>=cg.dp_words||!cg.dp_map[word])return NULL;
    for(;count<4&&next&&next->kind==ST_IF&&!next->alternate;next=next->next){
        Statement *arm=next->body;
        Expr *set,*condition=next->expression,*value;
        uint32_t mask=65535,threshold=1;
        if(arm&&arm->kind==ST_BLOCK&&!arm->next&&!arm->inline_callee)arm=arm->body;
        if(!arm||arm->next||arm->kind!=ST_EXPR)break;
        set=arm->expression;
        if(!set||set->kind!=EX_ASSIGN||set->left->kind!=EX_OBJECT||set->left->symbol!=home)break;
        value=set->right;
        if(!set->op&&count){
            if(value->kind!=EX_BINARY||value->op!='|'||
               value->left->kind!=EX_OBJECT||value->left->symbol!=home)break;
            value=value->right;
        }else if(set->op&&set->op!='|')break;
        if(!integer_constant(value,&bits)||bits!=(1u<<count)||body_effect(condition))break;
        if(condition->kind==EX_BINARY&&condition->op==TOK_GE&&
           common_type(condition->left->type,condition->right->type).is_unsigned&&
           integer_constant(condition->right,&threshold)&&threshold<=65535){
            condition=word_bits(condition->left);
            if(condition->kind==EX_BINARY&&condition->op=='&'&&
               integer_constant(condition->right,&mask)&&mask<=65535)
                condition=word_bits(condition->left);
        }else if(!condition->type.is_bool)break;
        if(condition->kind!=EX_OBJECT||condition->symbol==home||condition->type.pointers||
           !known_integer(condition->type)||reg_width(condition->type)!=2)break;
        values[count]=condition;thresholds[count]=threshold;masks[count++]=mask;
        last=next;
    }
    if(count<3)return NULL;
    for(i=0;i<count;++i){
        Symbol *source=values[i]->symbol;
        if(thresholds[i]>255||(!source->type.is_bool&&masks[i]>255)||
           source==cg.scalar_first||source==cg.scan_cursor||source==cg.leaf_count||
           source==cg.numeric_index||source==cg.numeric_recurrence||
           source==cg.retained_index||source==cg.retained_second)byte=0;
    }
    code("; collect independent flag bits through carry\n    stz %s\n",frame_operand(home->offset));
    if(byte)code("    sep #$20\n.a8\n");
    while(count--){
        if(byte){
            Symbol *source=values[count]->symbol;
            source->used=1;
            code("    lda ");array_operand(source,0);code("\n");
            if((masks[count]&255)!=255)code("    and #$%02X\n",masks[count]&255);
            code("    cmp #$%02X\n",thresholds[count]);
        }else{
            emit_value(values[count]);
            if(masks[count]!=65535)code("    and #$%04X\n",masks[count]);
            code("    cmp #$%04X\n",thresholds[count]);
        }
        code("    rol %s\n",frame_operand(home->offset));
    }
    if(byte)code("    rep #$20\n.a16\n");
    divmod_written(init->left);
    return last;
}

/* A byte assignment observes only the low byte of a masked increment.
 * Keep the load, arithmetic and store in a single byte-width region. */
static int masked_byte_assignment(Expr *e)
{
    Expr *target,*rhs,*step,*source;
    Symbol *v;
    uint32_t mask,one;
    if(cg.parser->no_strength_reduction||e->kind!=EX_ASSIGN||e->op||
       e->left->kind!=EX_OBJECT||volatile_expression(e))return 0;
    target=e->left;v=target->symbol;
    if(v->owner||target->type.banked||target->type.pointers||
       target->type.base!=TY_CHAR)return 0;
    rhs=e->right;
    if(integer_constant(rhs,&mask)&&!mask){
        code("    sep #$20\n.a8\n    stz ");array_operand(v,0);
        code("\n    rep #$20\n.a16\n");
        return 1;
    }
    if(target->type.is_bool)return 0;
    if(rhs->kind==EX_CAST&&width(rhs->type)==1)rhs=rhs->left;
    rhs=word_bits(rhs);
    if(rhs->kind!=EX_BINARY||rhs->op!='&'||!integer_constant(rhs->right,&mask)||mask>255)return 0;
    step=word_bits(rhs->left);
    if(step->kind!=EX_BINARY||(step->op!='+'&&step->op!='-')||
       !integer_constant(step->right,&one)||one!=1)return 0;
    source=promoted_byte_source(step->left);
    if(!source||source->kind!=EX_OBJECT||source->symbol!=v)return 0;
    code("    sep #$20\n.a8\n    lda ");array_operand(v,0);
    code("\n    %s a\n    and #$%02X\n    sta ",step->op=='+'?"inc":"dec",mask);
    array_operand(v,0);code("\n    rep #$20\n.a16\n");
    return 1;
}

static int fixed_volatile_byte(Expr *e,uint32_t *address)
{
    while(e&&e->kind==EX_CAST&&!e->type.pointers&&!e->type.is_bool&&
          e->type.base!=TY_FLOAT&&(width(e->type)==2||
          (width(e->type)==1&&e->type.is_unsigned)))e=e->left;
    return e&&e->kind==EX_DEREF&&e->type.base==TY_CHAR&&e->type.is_unsigned&&
           !e->type.is_bool&&volatile_expression(e)&&far_pointer(value_type(e->left->type))&&
           e->left->kind==EX_INT&&(*address=e->left->value)<=0xffffffu;
}

/* Compare two ordered byte reads packed into a word without materializing
 * the word. The high read still occurs on every path, including low misses. */
static Statement *packed_read_guard(Statement *s)
{
    Statement *combine=s->next,*test=combine?combine->next:NULL;
    Statement *initial=s;
    Expr *init,*merge,*high,*predicate;
    Symbol *word;
    uint32_t low_address,high_address,shift,bit,limit;
    unsigned fail,done;
    while(initial->kind==ST_BLOCK&&initial->body&&!initial->body->next)
        initial=initial->body;
    init=initial->expression;
    if(cg.parser->no_strength_reduction||cg.parser->no_body_optimizations||
       cg.switch_depth||initial->kind!=ST_EXPR||!combine||combine->kind!=ST_EXPR||
       !test||test->kind!=ST_IF||test->alternate||!init||
       init->kind!=EX_ASSIGN||init->op||init->left->kind!=EX_OBJECT||
       !fixed_volatile_byte(init->right,&low_address))return NULL;
    word=init->left->symbol;merge=combine->expression;predicate=test->expression;
    if(!body_private(word)||word->type.base!=TY_INT||!word->type.is_unsigned||
       width(word->type)!=2||!merge||merge->kind!=EX_ASSIGN||
       merge->left->kind!=EX_OBJECT||merge->left->symbol!=word||
       !predicate||predicate->kind!=EX_BINARY||predicate->op!='<'||
       word_bits(predicate->left)->kind!=EX_OBJECT||word_bits(predicate->left)->symbol!=word||
       !integer_constant(predicate->right,&limit)||!limit||limit>255)return NULL;
    high=word_bits(merge->right);
    if(!merge->op){
        if(high->kind!=EX_BINARY||high->op!='|'||word_bits(high->left)->kind!=EX_OBJECT||
           word_bits(high->left)->symbol!=word)return NULL;
        high=word_bits(high->right);
    }else if(merge->op!='|')return NULL;
    if(high->kind!=EX_BINARY||high->op!=TOK_SHL||
       !integer_constant(high->right,&shift)||shift!=8)return NULL;
    high=word_bits(high->left);
    if(high->kind!=EX_BINARY||high->op!='&'||!integer_constant(high->right,&bit)||bit!=1||
       !fixed_volatile_byte(high->left,&high_address)||
       statement_references(cg.function->body,word)!=(merge->op?3u:4u))return NULL;
    fail=++cg.label;done=++cg.label;
    code("; ordered packed byte comparison\n    sep #$20\n.a8\n"
         "    lda f:$%06X\n    pha\n    lda f:$%06X\n    lsr a\n    pla\n"
         "    bcs cg_%s_%u\n    cmp #$%02X\n    bcs cg_%s_%u\n    rep #$20\n.a16\n",
         low_address,high_address,cg.parser->unit,fail,limit,cg.parser->unit,fail);
    cg.divmod_available=0;
    if(emit_statements(test->body))jump(done);
    label(fail);code(".a8\n    rep #$20\n.a16\n");label(done);
    cg.divmod_available=0;
    return test;
}

static Statement *single_statement(Statement *s)
{
    while(s&&s->kind==ST_BLOCK&&!s->inline_callee&&s->body&&!s->body->next)s=s->body;
    return s;
}

static Expr *plain_assignment(Statement *s)
{
    Expr *e;
    s=single_statement(s);e=s&&s->kind==ST_EXPR?s->expression:NULL;
    return e&&e->kind==EX_ASSIGN&&!e->op&&e->left->kind==EX_OBJECT?e:NULL;
}

/* Keep a private word in A across adjacent conditional bit updates.
 * A mask of all tested bits skips the whole chain when none is set. */
static Statement *guarded_word_bits(Statement *first)
{
    Statement *s=first->next,*last=first;
    Expr *init=plain_assignment(first);
    Symbol *value;
    unsigned masks[4],keeps[4],sets[4],count=0,combined=0,done;
    int sign_ready;
    if(cg.parser->no_body_optimizations||cg.parser->no_strength_reduction||
       cg.switch_depth||first->kind!=ST_EXPR||first->inline_callee||!init||
       !word_integer(init->left->type)||init->left->type.is_bool||
       !body_private(value=init->left->symbol)||cg.retained_index==value||
       cg.retained_second==value||cg.numeric_index==value||cg.numeric_recurrence==value)return NULL;
    for(;s&&count<4;s=s->next){
        if(s->kind==ST_EMPTY)continue;
        Statement *arm=single_statement(s->body);
        Expr *test=s->expression,*assign=plain_assignment(arm),*rhs,*masking;
        uint32_t mask,keep,set;
        if(s->kind!=ST_IF||s->alternate||!arm||arm->next||!assign||
           s->inline_callee||statement_inline_markers(s->body)||
           !body_equal(assign->left,init->left)||!test||test->kind!=EX_BINARY||test->op!='&'||
           !body_equal(test->left,init->left)||!integer_constant(test->right,&mask)||
           !mask||mask>65535)break;
        rhs=word_bits(assign->right);
        if(!word_integer(rhs->type)||rhs->kind!=EX_BINARY||rhs->op!='|'||
           !integer_constant(rhs->right,&set))break;
        masking=word_bits(rhs->left);
        if(!word_integer(masking->type)||masking->kind!=EX_BINARY||masking->op!='&'||
           !body_equal(masking->left,init->left)||!integer_constant(masking->right,&keep))break;
        masks[count]=mask;keeps[count]=keep&65535;sets[count++]=set&65535;
        combined|=mask;last=s;
    }
    if(count<2)return NULL;
    done=++cg.label;
    emit_value(init->right);
    /* Only the non-destructive tests and A16 logical updates below can
     * intervene. They preserve N or set it from the updated word. */
    sign_ready=accumulator_zero_flags();
    code("; combined word bit guards\n    bit #$%04X\n    beq cg_%s_%u\n",
         combined,cg.parser->unit,done);
    for(unsigned i=0;i<count;++i){
        unsigned skip=++cg.label;
        if(sign_ready&&masks[i]==0x8000)code("    bpl cg_%s_%u\n",cg.parser->unit,skip);
        else code("    bit #$%04X\n    beq cg_%s_%u\n",masks[i],cg.parser->unit,skip);
        if(keeps[i]!=65535)code("    and #$%04X\n",keeps[i]);
        if(sets[i])code("    ora #$%04X\n",sets[i]);
        label(skip);
    }
    label(done);store_symbol(value);divmod_written(init->left);return last;
}

static int mapped_word_home(Symbol *v)
{
    unsigned offset=v->offset;
    return cg.dp_homes&&offset&&(offset&1)&&(offset-1)/2<cg.dp_words&&cg.dp_map[(offset-1)/2];
}

static void zero_mapped_high_byte(Symbol *v)
{
    code("    stz z:__dp_home_%02u+1\n",cg.dp_map[(v->offset-1)/2]-1);
}

/* Load a byte, guard its lower bound and form the decremented value without
 * giving the original byte a home or round-tripping through word mode. */
static Statement *guarded_byte_decrement(Statement *s)
{
    Statement *test=s->next,*next=test?test->next:NULL,*arm;
    Expr *init,*read,*predicate,*set,*rhs,*source;
    Symbol *value,*result;
    uint32_t limit,one;
    unsigned pass;
    if(cg.parser->no_strength_reduction||!cg.dp_homes||cg.switch_depth||
       cg.retained_index||cg.scan_cursor||!test||test->kind!=ST_IF||test->alternate||!next)return NULL;
    init=plain_assignment(s);set=plain_assignment(next);predicate=test->expression;
    if(!init||!set||predicate->kind!=EX_BINARY||(predicate->op!='<'&&predicate->op!=TOK_LE)||
       !integer_constant(predicate->right,&limit)||limit>=255)return NULL;
    arm=single_statement(test->body);
    if(!arm||arm->next||arm->kind!=ST_RETURN)return NULL;
    value=init->left->symbol;result=set->left->symbol;
    if(!body_private(value)||!body_private(result)||!mapped_word_home(result)||
       value->type.base!=TY_CHAR||!value->type.is_unsigned||value->type.is_bool||value->type.pointers||
       result->type.base!=TY_CHAR||!result->type.is_unsigned||result->type.is_bool||result->type.pointers||
       statement_references(cg.function->body,value)!=3)return NULL;
    read=promoted_byte_source(init->right);source=promoted_byte_source(predicate->left);
    if(!read||read->kind!=EX_DEREF||far_pointer(value_type(read->left->type))||
       !source||source->kind!=EX_OBJECT||source->symbol!=value)return NULL;
    rhs=set->right;
    if(rhs->kind==EX_CAST&&width(rhs->type)==1)rhs=rhs->left;
    if(rhs->kind!=EX_BINARY||rhs->op!='-'||!integer_constant(rhs->right,&one)||one!=1)return NULL;
    source=promoted_byte_source(rhs->left);
    if(!source||source->kind!=EX_OBJECT||source->symbol!=value)return NULL;
    if(predicate->op==TOK_LE)++limit;
    pass=++cg.label;
    emit_value_x(read->left);
    code("; byte load, lower-bound guard and decrement\n    sep #$20\n.a8\n"
         "    lda %s:$0000,x\n    cmp #$%02X\n    bcs cg_%s_%u\n    rep #$20\n.a16\n",
         strength_wram_pointer(read->left)?"z":"a",limit,cg.parser->unit,pass);
    cg.divmod_available=0;
    emit_statements(test->body);
    label(pass);code(".a8\n    dec a\n    sta ");array_operand(result,0);code("\n");
    zero_mapped_high_byte(result);
    code("    rep #$20\n.a16\n");cg.divmod_available=0;
    return next;
}

typedef struct { Expr *address; Symbol *value; Statement *test; unsigned limit; } ByteIncrement;

static int incremented_byte_plan(Statement *s,ByteIncrement *plan)
{
    Statement *test=s?s->next:NULL;
    Expr *assign,*rhs,*read,*relation;
    Symbol *value;
    uint32_t one,limit;
    if(cg.parser->no_strength_reduction||!cg.dp_homes||cg.retained_index||
       cg.scan_cursor||cg.switch_depth||!test||test->kind!=ST_IF||test->alternate)return 0;
    assign=plain_assignment(s);relation=test->expression;
    if(!assign||!assign->left->type.is_unsigned||assign->left->type.base!=TY_CHAR||
       assign->left->type.pointers||assign->left->type.is_bool||volatile_expression(assign))return 0;
    value=assign->left->symbol;rhs=assign->right;
    if(!body_private(value)||!mapped_word_home(value))return 0;
    if(rhs->kind==EX_CAST&&width(rhs->type)==1)rhs=rhs->left;
    if(rhs->kind!=EX_BINARY||rhs->op!='+'||!integer_constant(rhs->right,&one)||one!=1)return 0;
    read=promoted_byte_source(rhs->left);
    if(!read||read->kind!=EX_DEREF||far_pointer(value_type(read->left->type))||
       relation->kind!=EX_BINARY||relation->op!='>'||!integer_constant(relation->right,&limit)||
       limit>=255)return 0;
    rhs=promoted_byte_source(relation->left);
    if(!rhs||rhs->kind!=EX_OBJECT||rhs->symbol!=value)return 0;
    *plan=(ByteIncrement){read->left,value,test,(unsigned)limit+1};
    return 1;
}

static Statement *incremented_byte_guard(Statement *s)
{
    ByteIncrement p;
    unsigned skip;
    if(!incremented_byte_plan(s,&p))return NULL;
    skip=++cg.label;
    emit_value_x(p.address);
    code("; byte increment with wrapped result guard\n    sep #$20\n.a8\n"
         "    lda %s:$0000,x\n    inc a\n    sta ",strength_wram_pointer(p.address)?"z":"a");
    array_operand(p.value,0);code("\n");
    zero_mapped_high_byte(p.value);
    code("    cmp #$%02X\n    rep #$20\n.a16\n    bcs :+\n",p.limit);
    jump(skip);code(":\n");
    cg.divmod_available=0;emit_statements(p.test->body);
    label(skip);cg.divmod_available=0;
    return p.test;
}

typedef struct {
    Expr *address;
    Symbol *value;
    Statement *tail;
} ByteGuard;

static int byte_guard_plan(Statement *s,ByteGuard *guard)
{
    Statement *first=s->body;
    Expr *test=s->expression,*read,*write,*rhs;
    Symbol *value;
    uint32_t zero;
    if(s->kind!=ST_IF||s->alternate||!test||test->kind!=EX_BINARY||test->op!=TOK_EQ||
       !integer_constant(test->right,&zero)||zero)return 0;
    read=promoted_byte_source(test->left);
    if(!read||read->kind!=EX_DEREF||far_pointer(value_type(read->left->type))||
       !body_address_pure(read->left))return 0;
    if(first&&first->kind==ST_BLOCK&&!first->inline_callee)first=first->body;
    if(!first||first->kind!=ST_EXPR)return 0;
    write=first->expression;
    if(write->kind!=EX_ASSIGN||write->op||!body_equal(read,write->left)||
       volatile_expression(write))return 0;
    rhs=write->right;
    if(rhs->kind!=EX_OBJECT||rhs->type.pointers||rhs->type.base!=TY_CHAR||rhs->type.is_bool)return 0;
    value=rhs->symbol;
    if(value==cg.scalar_first||value==cg.numeric_index||value==cg.numeric_recurrence)return 0;
    *guard=(ByteGuard){read->left,value,first->next};
    return 1;
}

/* Read a guarded byte and perform the first store through the same X */
static int guarded_byte_store(Statement *s)
{
    ByteGuard g;
    unsigned store,skip;
    const char *mode;
    if(cg.parser->no_strength_reduction||cg.parser->no_indexed_operands||
       cg.retained_index||cg.scan_cursor||cg.switch_depth||!byte_guard_plan(s,&g))return 0;
    store=++cg.label;skip=++cg.label;
    emit_value_x(g.address);
    mode=strength_wram_pointer(g.address)?"z":"a";
    code("; shared address for byte guard and store\n    sep #$20\n.a8\n"
         "    lda %s:$0000,x\n    beq cg_%s_%u\n    rep #$20\n.a16\n",
         mode,cg.parser->unit,store);
    jump(skip);label(store);
    code(".a8\n    lda ");array_operand(g.value,0);
    code("\n    sta %s:$0000,x\n    rep #$20\n.a16\n",mode);
    cg.divmod_available=0;
    if(g.tail)emit_statements(g.tail);
    label(skip);cg.divmod_available=0;
    return 1;
}

static int guard_dp_home(Symbol *v)
{
    unsigned offset=v->offset;
    return !v->owner||(offset&&(offset&1)&&(offset-1)/2<cg.dp_words&&cg.dp_map[(offset-1)/2]);
}

/* A group borrows Y only if every other live automatic home is in DP and
 * the taken arms consist of straight-line near scalar operations. */
static int guard_tail_operand(Expr *e,Symbol *base)
{
    if(!e)return 1;
    if(volatile_expression(e)||far_pointer(value_type(e->type))||
       (!e->type.array&&reg_width(e->type)>2))return 0;
    switch(e->kind){
    case EX_OBJECT:return e->symbol!=base&&guard_dp_home(e->symbol);
    case EX_INT:return e->type.base!=TY_FLOAT;
    case EX_CAST:case EX_DEREF:break;
    case EX_ASSIGN:if(e->op)return 0;break;
    case EX_BINARY:if(e->op!='+'&&e->op!='-'&&e->op!='&')return 0;break;
    default:return 0;
    }
    return guard_tail_operand(e->left,base)&&guard_tail_operand(e->right,base);
}

static int guard_tail_ok(Statement *s,Symbol *base)
{
    for(;s;s=s->next)
        if(s->kind!=ST_EXPR||!guard_tail_operand(s->expression,base))return 0;
    return 1;
}

static void emit_byte_guard_cursor(ByteGuard *guard,const int16_t *delta,unsigned count)
{
    unsigned i;
    code("    tay\n    sep #$20\n.a8\n");
    for(i=0;i<count;++i){
        unsigned skip=++cg.label;
        if(i){
            int step=(int16_t)(delta[i]-delta[i-1]);
            if(step>=-3&&step<=3){
                while(step>0){code("    iny\n");--step;}
                while(step<0){code("    dey\n");++step;}
            }else code("    rep #$20\n.a16\n    tya\n    clc\n    adc #$%04X\n"
                       "    tay\n    sep #$20\n.a8\n",(unsigned)step&65535u);
        }
        code("    lda a:0,y\n    bne cg_%s_%u\n    lda ",cg.parser->unit,skip);
        array_operand(guard[i].value,0);
        code("\n    sta a:0,y\n");
        if(guard[i].tail){
            code("    rep #$20\n.a16\n");
            cg.divmod_available=0;
            emit_statements(guard[i].tail);
            code("    sep #$20\n.a8\n");
        }
        label(skip);
    }
    code("    rep #$20\n.a16\n");
}

typedef struct {
    ByteGuard guards[8];
    int16_t delta[8];
    Symbol *base;
    Statement *last;
    unsigned count,large_steps;
    int min,max;
} ByteGuardGroup;

static int plan_byte_guard_group(Statement *s,ByteGuardGroup *g)
{
    Statement *entry;
    if(!cg.dp_homes||!cg.loop_count||cg.stack_leaf||cg.retained_index||
       cg.scan_cursor||cg.bound||cg.cursor_count||cg.affine_active||cg.switch_depth||
       cg.parser->no_register_cursors||cg.parser->no_strength_reduction||
       cg.parser->no_indexed_operands)return 0;
    memset(g,0,sizeof *g);g->min=32767;g->max=-32768;
    for(entry=s;entry&&g->count<sizeof g->guards/sizeof *g->guards;entry=entry->next){
        unsigned i=g->count;
        ByteGuard *guard=&g->guards[i];
        Expr *a;
        uint32_t offset;
        if(!byte_guard_plan(entry,guard))break;
        a=guard->address;
        if(a->kind!=EX_BINARY||a->op!='+'||a->left->kind!=EX_OBJECT||
           !a->left->type.pointers||width(pointed_type(a->left->type))!=1||
           !integer_constant(a->right,&offset)||!body_private(a->left->symbol)||
           !guard_dp_home(a->left->symbol)||!guard_dp_home(guard->value)||
           (g->base&&g->base!=a->left->symbol)||!guard_tail_ok(guard->tail,a->left->symbol))break;
        g->base=a->left->symbol;g->delta[i]=(int16_t)offset;g->last=entry;
        if(g->delta[i]<g->min)g->min=g->delta[i];
        if(g->delta[i]>g->max)g->max=g->delta[i];
        if(i&&(g->delta[i]-g->delta[i-1]>3||g->delta[i]-g->delta[i-1]<-3))++g->large_steps;
        ++g->count;
    }
    return g->count>=2;
}

static int fixed_guard_displacements(const ByteGuardGroup *g)
{
    return g->count>=4&&g->large_steps>=2&&g->max-g->min<=255;
}

static void emit_guard_increment(const ByteIncrement *step,unsigned reject,unsigned offset,int wrapping)
{
    if(wrapping){
        code("    tya\n");
        if(offset)code("    clc\n    adc #$%04X\n",offset);
        code("    tax\n    sep #$20\n.a8\n    lda a:0,x\n");
    }else code("    lda a:0+$%04X,y\n",offset);
    code("    inc a\n    cmp #$%02X\n    bcs cg_%s_%u\n    sta ",step->limit,cg.parser->unit,reject);
    array_operand(step->value,0);code("\n");
}

/* Keep the final tail shared because both paths have the same continuation.
 * A short intermediate tail can be copied into the cold path to remove its
 * fast-path dispatch. Longer tails still share one copy. */
static int copy_cold_guard_tail(Statement *s)
{
    return !s||!s->next||!s->next->next;
}

static void emit_shared_wrapping_guards(ByteGuardGroup *g,const ByteIncrement *step)
{
    unsigned fast[8],cold[8],tail[8],i,done=++cg.label;
    unsigned reject=step?++cg.label:0,boundary=(unsigned)(65536-(g->max-g->min));
    unsigned char copied[8];
    for(i=0;i<g->count;++i){
        fast[i]=++cg.label;cold[i]=++cg.label;tail[i]=++cg.label;
        copied[i]=(unsigned char)(step&&i+1<g->count&&copy_cold_guard_tail(g->guards[i].tail));
    }
    code("    tay\n    cmp #$%04X\n    bcc :+\n",boundary);
    jump(cold[0]);code(":\n    sep #$20\n.a8\n");
    if(step)emit_guard_increment(step,reject,(unsigned)-g->min,0);
    for(i=0;i<g->count;++i){
        ByteGuard *guard=&g->guards[i];
        unsigned offset=(unsigned)(g->delta[i]-g->min);
        unsigned skip=i+1<g->count?fast[i+1]:++cg.label;
        label(fast[i]);
        code("    lda a:0+$%04X,y\n    bne cg_%s_%u\n    lda ",offset,cg.parser->unit,skip);
        array_operand(guard->value,0);
        code("\n    sta a:0+$%04X,y\n    rep #$20\n.a16\n",offset);
        label(tail[i]);cg.divmod_available=0;
        if(guard->tail)emit_statements(guard->tail);
        if(i+1<g->count){
            if(!copied[i]){
                code("    cpy #$%04X\n    bcc :+\n",boundary);
                jump(cold[i+1]);code(":\n");
            }
            code("    sep #$20\n.a8\n");
        }else{
            jump(done);label(skip);code(".a8\n    rep #$20\n.a16\n");jump(done);
        }
    }
    for(i=0;i<g->count;++i){
        ByteGuard *guard=&g->guards[i];
        unsigned skip=++cg.label,offset=(unsigned)(g->delta[i]-g->min);
        label(cold[i]);
        if(step&&!i){emit_guard_increment(step,reject,(unsigned)-g->min,1);code("    rep #$20\n.a16\n");}
        code("    tya\n");
        if(offset)code("    clc\n    adc #$%04X\n",offset);
        code("    tax\n    sep #$20\n.a8\n    lda a:0,x\n"
             "    bne cg_%s_%u\n    lda ",cg.parser->unit,skip);
        array_operand(guard->value,0);
        code("\n    sta a:0,x\n    rep #$20\n.a16\n");
        if(copied[i]){
            cg.divmod_available=0;
            if(guard->tail)emit_statements(guard->tail);
            jump(cold[i+1]);
        }else jump(tail[i]);
        label(skip);code(".a8\n    rep #$20\n.a16\n");
    }
    if(step){
        jump(done);label(reject);code(".a8\n    rep #$20\n.a16\n");
        emit_statements(step->test->body);
    }
    label(done);
}

static Statement *byte_guard_group(Statement *s)
{
    ByteGuardGroup g;
    if(!plan_byte_guard_group(s,&g))return NULL;
    code("; shared wrapping Y cursor for byte guards\n");
    if(!cg.loop_y_borrowed)code("    phy\n");
    if(fixed_guard_displacements(&g)){
        load_symbol(g.base);
        if(g.min)code("    clc\n    adc #$%04X\n",(unsigned)g.min&65535u);
        emit_shared_wrapping_guards(&g,NULL);
    }else{
        emit_value(g.guards[0].address);
        emit_byte_guard_cursor(g.guards,g.delta,g.count);
    }
    if(!cg.loop_y_borrowed)code("    ply\n");
    cg.divmod_available=0;
    return g.last;
}

/* A private pointer and byte used only by this group need neither a
 * materialized pointer home nor a zero-extended byte home. */
static Statement *byte_cursor_increment_group(Statement *s)
{
    Expr *init;
    ByteIncrement step;
    ByteGuardGroup g;
    Statement *arm;
    unsigned i;
    if(!cg.loop_y_borrowed||!(init=plain_assignment(s))||
       !incremented_byte_plan(s->next,&step)||!plan_byte_guard_group(step.test->next,&g)||
       !fixed_guard_displacements(&g)||g.min>0||g.max<0||
       init->left->symbol!=g.base||!lftr_object(step.address,g.base)||
       statement_references(cg.function->body,g.base)!=2+2*g.count||
       statement_references(cg.function->body,step.value)!=2+g.count)return NULL;
    arm=single_statement(step.test->body);
    if(!arm||arm->next||arm->kind!=ST_CONTINUE)return NULL;
    for(i=0;i<g.count;++i)if(g.guards[i].value!=step.value)return NULL;
    code("; retained byte step and biased guard cursor\n");
    emit_value(init->right);
    if(g.min)code("    clc\n    adc #$%04X\n",(unsigned)g.min&65535u);
    emit_shared_wrapping_guards(&g,&step);
    cg.divmod_available=0;
    return g.last;
}

static int return_shared_byte_index(Statement *s)
{
    Statement *arm=s->body;
    if(cg.scalar_leaf||s->alternate||reg_width(cg.function->symbol->type)!=2||
       cg.function->symbol->type.pointers||cg.function->symbol->type.base!=TY_INT)return 0;
    if(arm&&arm->kind==ST_BLOCK)arm=arm->body;
    if(!arm||arm->next||arm->kind!=ST_RETURN||!arm->expression)return 0;
    return branch_shared_byte_index(s->expression,0,0,0,arm->expression);
}

/* Keep the selected value in A across a guarded unsigned min/max store */
static int guarded_word_extreme(Statement *s)
{
    Expr *test=s->expression,*assign=plain_assignment(s->body),*value,*dest;
    Statement *body=single_statement(s->body);
    Type t;
    unsigned done;
    int maximum;
    if(cg.parser->no_strength_reduction||s->alternate||!body||body->next||!assign||
       !test||test->kind!=EX_BINARY||test->op!='<'||
       test->left->kind!=EX_OBJECT||test->right->kind!=EX_OBJECT||
       assign->right->kind!=EX_OBJECT||volatile_statement(s))return 0;
    t=common_type(test->left->type,test->right->type);
    if(!t.is_unsigned||t.pointers||t.base!=TY_INT||
       !same_value_representation(test->left->type,t)||
       !same_value_representation(test->right->type,t))return 0;
    maximum=assign->left->symbol==test->left->symbol;
    dest=maximum?test->left:test->right;value=maximum?test->right:test->left;
    if(dest->symbol!=assign->left->symbol||value->symbol!=assign->right->symbol||
       !compare_memory_operand(dest,0))return 0;
    done=++cg.label;
    emit_value(value);code("    cmp ");compare_memory_operand(dest,1);
    code("\n    %s cg_%s_%u\n",maximum?"bcc":"bcs",cg.parser->unit,done);
    if(maximum)code("    beq cg_%s_%u\n",cg.parser->unit,done);
    store_symbol(dest->symbol);label(done);cg.divmod_available=0;
    return 1;
}

/* A private cursor and its global shadow occupy disjoint storage. Copy the
 * two words through A rather than staging a far result in X:A. */
static int discarded_far_home_copy(Expr *e)
{
    Symbol *src,*dst;unsigned offset;
    if(cg.parser->no_strength_reduction||e->kind!=EX_ASSIGN||e->op||
       e->left->kind!=EX_OBJECT||e->right->kind!=EX_OBJECT||
       !far_pointer(e->left->type)||!same_value_representation(e->left->type,e->right->type)||
       volatile_expression(e))return 0;
    dst=e->left->symbol;src=e->right->symbol;
    if((dst->owner==0)==(src->owner==0)||dst->type.banked||src->type.banked||
       dst->function||src->function||dst->type.array||src->type.array||
       !far_pointer(dst->type)||!far_pointer(src->type))return 0;
    for(offset=0;offset<4;offset+=2){
        code("    lda ");array_operand(src,offset);
        code("\n    sta ");array_operand(dst,offset);code("\n");
    }
    return 1;
}

#include "word_rows.inc"

/* Project the bank directly from a side-effect-free object address */
static int address_bank_byte(Expr *e,int emit)
{
    Expr *address;
    Symbol *symbol;
    unsigned offset;
    if(e->kind==EX_CAST&&e->type.base==TY_CHAR&&!e->type.pointers&&!e->type.is_bool)e=e->left;
    if(e->kind!=EX_BINARY||e->op!=TOK_SHR||e->right->kind!=EX_INT||e->right->value!=16||
       e->left->kind!=EX_CAST||e->left->type.base!=TY_LONG||e->left->type.pointers)return 0;
    address=e->left->left;
    if(!far_pointer(value_type(address->type)))return 0;
    while(address->kind==EX_CAST&&value_type(address->left->type).pointers){
        if(!far_pointer(value_type(address->left->type))){
            if(!near_object_address(address->left,&offset))return 0;
            if(emit)code("#$7E");
            return 1;
        }
        address=address->left;
    }
    if(address->kind==EX_ADDRESS)address=address->left;
    else if(!address->type.array)return 0;
    if(address->kind!=EX_OBJECT)return 0;
    symbol=address->symbol;
    if(symbol->owner||symbol->function||!symbol->type.banked)return 0;
    if(emit){symbol->used=1;code("#.bankbyte(_%s)",symbol->asm_name);}
    return 1;
}

static Expr *fixed_byte_copy(Statement *s,uint32_t *address)
{
    Expr *e,*rhs;
    if(!s||s->kind!=ST_EXPR||s->inline_callee)return NULL;
    e=s->expression;
    if(!e||e->kind!=EX_ASSIGN||e->op||!fixed_volatile_byte(e->left,address))return NULL;
    rhs=e->right;
    if(rhs->kind==EX_INT&&!rhs->type.pointers&&rhs->type.base!=TY_FLOAT)return rhs;
    if(rhs->kind==EX_OBJECT&&width(rhs->type)==1&&!rhs->type.is_bool&&
       !rhs->symbol->owner)return rhs;
    if(!cg.parser->no_strength_reduction&&address_bank_byte(rhs,0))return rhs;
    return NULL;
}

/* The PPU register window is disjoint from CPU RAM and cannot start DMA */
static int ppu_port(uint32_t address)
{
    unsigned bank=address>>16,offset=address&0xffff;
    return !(bank&0x40)&&offset>=0x2100&&offset<0x2140;
}

static int same_byte_source(Expr *a,Expr *b)
{
    return a&&b&&a->kind==EX_OBJECT&&b->kind==EX_OBJECT&&
           a->symbol==b->symbol&&!volatile_expression(a)&&!volatile_expression(b);
}

static Statement *fixed_byte_copy_region(Statement *s)
{
    Statement *p=s,*last=NULL;
    Expr *low,*high;
    uint32_t first,second,third,fourth;
    if(cg.parser->no_body_optimizations||!(low=fixed_byte_copy(s,&first))||
       (!address_bank_byte(low,0)&&!fixed_byte_copy(s->next,&second)))return NULL;
    code("    sep #$20\n.a8\n");
    while((low=fixed_byte_copy(p,&first))!=NULL){
        Statement *next=p->next;
        high=fixed_byte_copy(next,&second);
        if(high&&first==second&&ppu_port(first)&&
           same_byte_source(low,fixed_byte_copy(next->next,&third))&&
           third!=first&&ppu_port(third)&&
           same_byte_source(high,fixed_byte_copy(next->next->next,&fourth))&&third==fourth){
            code("    lda ");array_operand(high->symbol,0);
            code("\n    xba\n    lda ");array_operand(low->symbol,0);
            code("\n    sta f:$%06X\n    xba\n    sta f:$%06X\n"
                 "    xba\n    sta f:$%06X\n    xba\n    sta f:$%06X\n",first,second,third,fourth);
            last=next->next->next;
        }else{
            if(low->kind==EX_INT)code("    lda #$%02X",low->value&0xffu);
            else {
                code("    lda ");
                if(!address_bank_byte(low,1))array_operand(low->symbol,0);
            }
            code("\n    sta f:$%06X\n",first);
            last=p;
        }
        p=last->next;
    }
    code("    rep #$20\n.a16\n");
    cg.divmod_available=0;
    return last;
}

/* Initial eight-byte value path: a value lives in arithmetic scratch +0..7.
 * Nested operands are saved on the CPU stack while the RHS is evaluated, so
 * all existing 64-bit assembly helpers see their documented +0/+8 inputs. */
static int wide_scalar(Type t){return !t.pointers&&!t.array&&(t.base==TY_LONGLONG||t.base==TY_DOUBLE);}
static int wide_call_supported(Expr *e);
static int wide_assignment_supported(Expr *e);
static int wide_update_supported(Expr *e);
static int wide_narrow_supported(Expr *e);
static int wide_compare_supported(Expr *e);
static int wide_operand_compatible(Expr *e,Type target);
static int wide_fixed_path_safe(Expr *e)
{
    if(!e)return 1;
    if(e->kind==EX_MEMBER)return wide_fixed_path_safe(e->left);
    if(e->kind==EX_DEREF&&e->left&&e->left->kind==EX_BINARY){
        if(e->left->right&&wide_scalar(value_type(e->left->right->type)))return 0;
        return wide_fixed_path_safe(e->left->left);
    }
    return 1;
}
static Symbol *wide_fixed_home(Expr *e,unsigned *offset)
{
    *offset=0;
    while(!cg.parser->no_strength_reduction&&e->kind==EX_CAST&&
          e->type.base==TY_LONGLONG&&e->left->type.base==TY_LONGLONG&&
          wide_scalar(value_type(e->type))&&wide_scalar(value_type(e->left->type)))e=e->left;
    if(e->kind==EX_OBJECT)return e->symbol;
    if(!wide_fixed_path_safe(e))return NULL;
    return fixed_memory_object(e,offset);
}
static int wide_address_safe(Expr *e)
{
    unsigned i;if(!e)return 1;
    if(!e->type.pointers&&!e->type.array&&e->type.base==TY_DOUBLE)return 0;
    if(wide_scalar(value_type(e->type)))return 0;
    if(!wide_address_safe(e->left)||!wide_address_safe(e->right)||!wide_address_safe(e->third))return 0;
    for(i=0;i<e->arg_count;++i)if(!wide_address_safe(e->args[i]))return 0;
    return 1;
}
static int wide_lvalue_supported(Expr *e)
{
    unsigned offset;
    if(!e||!wide_scalar(e->type))return 0;
    if(wide_fixed_home(e,&offset))return 1;
    return (e->kind==EX_DEREF||e->kind==EX_MEMBER)&&wide_lvalue_address_supported(e);
}
static int wide_condition_supported(Expr *e);
static int wide_value_supported(Expr *e)
{
    if(!e||e->type.pointers||e->type.array||!numeric(e->type)||e->type.base==TY_FLOAT)return 0;
    /* Narrow operands use the scalar path, then extend into the wide slot */
    if(!wide_scalar(value_type(e->type)))return wide_mixed_narrow_supported(e);
    if(e->kind==EX_INT||e->kind==EX_OBJECT)return 1;
    if(e->kind==EX_CALL&&wide_scalar(e->type))return wide_call_supported(e);
    if(e->kind==EX_ASSIGN)return wide_assignment_supported(e);
    if(e->kind==EX_PRE||e->kind==EX_POST)return wide_update_supported(e);
    if(wide_scalar(e->type)&&(e->kind==EX_MEMBER||e->kind==EX_DEREF))return wide_lvalue_supported(e);
    if(e->kind==EX_CAST){
        if(e->type.base==TY_LONGLONG&&value_type(e->left->type).pointers)
            return wide_address_safe(e->left)||wide_pointer_supported(e->left)||
                wide_narrow_supported(e->left)||wide_address_expression_supported(e->left);
        if(e->type.base==TY_DOUBLE){
            if(e->left->type.base==TY_FLOAT)return wide_mixed_narrow_supported(e->left);
            return wide_value_supported(e->left);
        }
        if(e->type.base==TY_LONGLONG&&e->left->type.base==TY_FLOAT)
            return wide_mixed_narrow_supported(e->left);
        if(e->left->type.base==TY_DOUBLE)return wide_value_supported(e->left);
        return wide_scalar(e->type)&&wide_value_supported(e->left);
    }
    if(e->kind==EX_UNARY&&wide_scalar(e->type)&&(e->op=='+'||e->op=='-'||e->op=='~'))
        return wide_value_supported(e->left);
    if(e->kind==EX_CHOOSE)return wide_condition_supported(e->left)&&
        wide_value_supported(e->right)&&wide_value_supported(e->third);
    if(e->kind==EX_COMMA)return
        (wide_address_safe(e->left)||wide_discard_supported(e->left))&&wide_value_supported(e->right);
    if(e->kind==EX_BINARY&&wide_scalar(e->type)){
        if(e->type.base==TY_DOUBLE)
            return (e->op=='+'||e->op=='-'||e->op=='*'||e->op=='/')&&
                wide_operand_compatible(e->left,e->type)&&wide_operand_compatible(e->right,e->type);
        switch(e->op){
        case '+':case '-':case '*':case '/':case '%':case '&':case '|':case '^':case TOK_SHL:case TOK_SHR:
            return wide_value_supported(e->left)&&wide_value_supported(e->right);
        }
    }
    return 0;
}
static int wide_call_supported(Expr *e)
{
    unsigned i;
    if(!e||e->kind!=EX_CALL)return 0;
    if(e->left){
        Type t=value_type(e->left->type);
        if(!function_pointer(t)||!t.signature||!wide_address_safe(e->left))return 0;
    }else if(!e->symbol)return 0;
    for(i=0;i<e->arg_count;++i){
        Expr *arg=e->args[i];Type t=value_type(arg->type);
        if(wide_scalar(t)){if(!wide_value_supported(arg))return 0;}
        else if(!wide_address_safe(arg)&&!wide_pointer_supported(arg)&&!wide_narrow_supported(arg)&&
                !wide_address_expression_supported(arg)&&
                !wide_mixed_narrow_supported(arg))return 0;
    }
    return 1;
}
static int wide_call_used(Expr *e)
{
    unsigned i;if(!wide_call_supported(e))return 0;
    if(wide_scalar(value_type(e->type)))return 1;
    for(i=0;i<e->arg_count;++i)if(wide_scalar(value_type(e->args[i]->type)))return 1;
    return 0;
}
static int wide_assignment_supported(Expr *e)
{
    if(!e||e->kind!=EX_ASSIGN||!wide_scalar(e->type)||!wide_lvalue_supported(e->left))return 0;
    if(e->op&&e->op!='+'&&e->op!='-'&&e->op!='*'&&e->op!='/'&&e->op!='%'&&
       e->op!='&'&&e->op!='|'&&e->op!='^'&&e->op!=TOK_SHL&&e->op!=TOK_SHR)return 0;
    if(e->type.base==TY_DOUBLE){
        if(e->op&&e->op!='+'&&e->op!='-'&&e->op!='*'&&e->op!='/')return 0;
        return wide_operand_compatible(e->right,e->type);
    }
    if(e->op&&e->right->type.base==TY_FLOAT)
        return wide_mixed_narrow_supported(e->right);
    return wide_value_supported(e->right);
}
static int wide_update_supported(Expr *e)
{
    return e&&(e->kind==EX_PRE||e->kind==EX_POST)&&wide_scalar(e->type)&&e->left&&
        wide_lvalue_supported(e->left)&&(e->op==TOK_INC||e->op==TOK_DEC);
}
static int wide_narrow_supported(Expr *e)
{
    return e&&e->kind==EX_CAST&&(e->type.pointers||numeric(e->type))&&
        !wide_scalar(e->type)&&e->left&&wide_scalar(value_type(e->left->type))&&
        (!e->type.pointers||e->left->type.base==TY_LONGLONG)&&wide_value_supported(e->left);
}
static int wide_pointer_supported(Expr *e)
{
    if(!e||!e->type.pointers||wide_address_safe(e))return 0;
    if(e->kind==EX_CAST&&value_type(e->left->type).pointers)
        return wide_pointer_supported(e->left)||wide_narrow_supported(e->left)||
            wide_address_expression_supported(e->left);
    if(e->kind==EX_CHOOSE)
        return wide_condition_supported(e->left)&&
            (wide_address_safe(e->right)||wide_pointer_supported(e->right)||
             wide_narrow_supported(e->right)||wide_address_expression_supported(e->right))&&
            (wide_address_safe(e->third)||wide_pointer_supported(e->third)||
             wide_narrow_supported(e->third)||wide_address_expression_supported(e->third));
    if(e->kind==EX_COMMA)
        return (wide_address_safe(e->left)||wide_discard_supported(e->left))&&
            (wide_address_safe(e->right)||wide_pointer_supported(e->right)||
             wide_narrow_supported(e->right)||wide_address_expression_supported(e->right));
    if(e->kind!=EX_BINARY||(e->op!='+'&&e->op!='-'))return wide_mixed_narrow_supported(e);
    return (wide_address_safe(e->left)||wide_pointer_supported(e->left)||
            wide_narrow_supported(e->left)||wide_address_expression_supported(e->left)||
            (e->left->kind==EX_DEREF&&e->left->type.array&&wide_lvalue_address_supported(e->left)))&&
        (wide_address_safe(e->right)||wide_mixed_narrow_supported(e->right));
}
static int wide_address_expression_supported(Expr *e)
{
    return e&&e->kind==EX_ADDRESS&&wide_lvalue_address_supported(e->left);
}
static int wide_lvalue_address_supported(Expr *e)
{
    if(!e)return 0;
    if(e->kind==EX_OBJECT)return 1;
    if(structure_object(e->type)&&e->kind==EX_CALL)return wide_call_supported(e);
    if(structure_object(e->type)&&e->kind==EX_COMMA)
        return (wide_address_safe(e->left)||wide_discard_supported(e->left))&&wide_lvalue_address_supported(e->right);
    if(structure_object(e->type)&&e->kind==EX_ASSIGN&&!e->op)
        return wide_lvalue_address_supported(e->left)&&
            (wide_address_safe(e->right)||wide_lvalue_address_supported(e->right));
    if(e->kind==EX_DEREF)
        return wide_address_safe(e->left)||wide_pointer_supported(e->left)||
            wide_narrow_supported(e->left)||wide_address_expression_supported(e->left);
    if(e->kind==EX_MEMBER){
        if(e->op==TOK_ARROW)
            return wide_address_safe(e->left)||wide_pointer_supported(e->left)||
                wide_narrow_supported(e->left)||wide_address_expression_supported(e->left);
        return wide_lvalue_address_supported(e->left);
    }
    if(e->kind==EX_BITFIELD)return wide_lvalue_address_supported(e->left);
    return 0;
}
static int narrow_wide_compound_supported(Expr *e)
{
    Type t;
    if(!e||e->kind!=EX_ASSIGN||!e->op||e->op==TOK_SHL||e->op==TOK_SHR||
       !e->left||e->left->kind==EX_OBJECT||e->type.pointers||e->type.array||
       e->type.is_bool||!numeric(e->type)||e->type.base==TY_FLOAT||
       e->type.base==TY_DOUBLE||e->type.base==TY_LONGLONG||
       !wide_scalar(value_type(e->right->type))||!wide_value_supported(e->right))
        return 0;
    if(!wide_lvalue_address_supported(e->left))return 0;
    t=common_type(e->left->type,e->right->type);
    return !t.pointers&&(t.base==TY_LONGLONG||t.base==TY_DOUBLE);
}
static int wide_narrow_assignment(Expr *e)
{
    return e&&e->kind==EX_ASSIGN&&!e->op&&e->left&&e->left->kind==EX_OBJECT&&
        wide_narrow_supported(e->right);
}
static int wide_compare_supported(Expr *e)
{
    return e&&e->kind==EX_BINARY&&comparison(e->op)&&
        wide_scalar(common_type(e->left->type,e->right->type))&&
        wide_operand_compatible(e->left,common_type(e->left->type,e->right->type))&&
        wide_operand_compatible(e->right,common_type(e->left->type,e->right->type));
}
static int wide_operand_compatible(Expr *e,Type target)
{
    Type source=value_type(e->type);
    if(target.base==TY_DOUBLE&&source.base==TY_FLOAT)return wide_mixed_narrow_supported(e);
    if(target.base!=TY_DOUBLE&&source.base==TY_DOUBLE)return 0;
    return wide_value_supported(e);
}
static int wide_mixed_narrow_supported(Expr *e)
{
    if(!e||wide_scalar(value_type(e->type)))return 0;
    if(wide_address_safe(e)||wide_compare_supported(e)||wide_narrow_supported(e)||
       narrow_wide_compound_supported(e))return 1;
    switch(e->kind){
    case EX_ADDRESS:return wide_lvalue_address_supported(e->left);
    case EX_MEMBER:case EX_DEREF:case EX_BITFIELD:return wide_lvalue_address_supported(e);
    case EX_PRE:case EX_POST:return wide_lvalue_address_supported(e->left);
    case EX_CALL:return wide_call_supported(e);
    case EX_BINARY:
        if(e->op==TOK_LAND||e->op==TOK_LOR)
            return wide_condition_supported(e->left)&&wide_condition_supported(e->right);
        return wide_mixed_narrow_supported(e->left)&&wide_mixed_narrow_supported(e->right);
    case EX_COMMA:
        return (wide_address_safe(e->left)||wide_discard_supported(e->left))&&
            wide_mixed_narrow_supported(e->right);
    case EX_UNARY:return e->op=='!'?wide_condition_supported(e->left):wide_mixed_narrow_supported(e->left);
    case EX_CAST:return wide_mixed_narrow_supported(e->left);
    case EX_CHOOSE:return wide_condition_supported(e->left)&&
        wide_mixed_narrow_supported(e->right)&&wide_mixed_narrow_supported(e->third);
    case EX_ASSIGN:return wide_lvalue_address_supported(e->left)&&
        wide_mixed_narrow_supported(e->right);
    default:return 0;
    }
}
static int wide_condition_supported(Expr *e)
{
    if(!e)return 0;
    if(wide_address_safe(e)||wide_compare_supported(e))return 1;
    if(wide_scalar(value_type(e->type)))return wide_value_supported(e);
    if(e->kind==EX_BINARY&&(e->op==TOK_LAND||e->op==TOK_LOR))
        return wide_condition_supported(e->left)&&wide_condition_supported(e->right);
    if((e->kind==EX_UNARY&&e->op=='!')||(e->kind==EX_CAST&&e->type.is_bool&&!e->type.pointers))
        return wide_condition_supported(e->left);
    return wide_mixed_narrow_supported(e);
}
static void emit_wide_value(Expr *e);
static void emit_wide_assignment(Expr *e,int discarded);
static void emit_wide_update(Expr *e,int discarded);
static void emit_wide_literal(Expr *e,unsigned offset)
{
    uint64_t value=initializer_cast64(((uint64_t)e->value_high<<32)|e->value,e->type);
    unsigned i,loaded=0;
    for(i=0;i<8;i+=2){
        unsigned word=(unsigned)(value>>(8*i))&65535;
        if(!word)code("    stz z:__arith_lhs+%u\n",offset+i);
        else{
            if(loaded!=word)code("    lda #$%04X\n",word);
            code("    sta z:__arith_lhs+%u\n",offset+i);
            loaded=word;
        }
    }
}
static void emit_wide_operand(Expr *e)
{
    unsigned i;Type source=value_type(e->type),word=type(TY_LONG,0);
    cg.arithmetic=1;
    if(wide_scalar(source)){emit_wide_value(e);return;}
    if(e->kind==EX_INT){emit_wide_literal(e,0);return;}
    word.is_unsigned=source.is_unsigned;emit_value(e);convert_registers(source,word);
    code("    sta z:__arith_lhs\n    stx z:__arith_lhs+2\n");
    if(source.is_unsigned)code("    lda #0\n");
    else code("    txa\n    cmp #$8000\n    lda #0\n    bcc :+\n    lda #$FFFF\n:\n");
    for(i=4;i<8;i+=2)code("    sta z:__arith_lhs+%u\n",i);
}
static void emit_wide_as(Expr *e,Type target)
{
    if(target.base==TY_DOUBLE&&value_type(e->type).base!=TY_DOUBLE){
        Expr cast={0};cast.kind=EX_CAST;cast.type=target;cast.left=e;cast.location=e->location;
        emit_wide_value(&cast);
    }else emit_wide_operand(e);
}
static void emit_wide_rhs(Expr *right,Type target)
{
    unsigned i,offset;Symbol *home;
    int same=target.base!=TY_DOUBLE||value_type(right->type).base==TY_DOUBLE;
    if(same&&right->kind==EX_INT){emit_wide_literal(right,8);return;}
    if(same&&wide_scalar(value_type(right->type))&&(home=wide_fixed_home(right,&offset))!=NULL){
        for(i=0;i<8;i+=2){code("    lda ");array_operand(home,offset+i);code("\n    sta z:__arith_lhs+%u\n",i+8);}
        return;
    }
    for(i=8;i;i-=2)code("    lda z:__arith_lhs+%u\n    pha\n",i-2);
    emit_wide_as(right,target);
    for(i=0;i<8;i+=2)code("    lda z:__arith_lhs+%u\n    sta z:__arith_lhs+%u\n",i,i+8);
    for(i=0;i<8;i+=2)code("    pla\n    sta z:__arith_lhs+%u\n",i);
}
static void emit_wide_pair(Expr *left,Expr *right,Type target)
{
    emit_wide_as(left,target);emit_wide_rhs(right,target);
}
static void wide_word_bounds(Expr *e,int *low,int *high)
{
    Type t=value_type(e->type);
    unsigned bits=width(t)*8;
    int a,b;
    *high=t.is_bool?1:(int)((1u<<(bits-!t.is_unsigned))-1);
    *low=t.is_unsigned||t.is_bool?0:-*high-1;
    if(e->kind==EX_INT){*low=*high=(int32_t)initializer_cast(e->value,t);return;}
    if((e->kind!=EX_CAST&&(e->kind!=EX_UNARY||e->op!='~'))||!known_integer(value_type(e->left->type)))return;
    wide_word_bounds(e->left,&a,&b);
    if(a<*low||b>*high)return;
    if(e->kind==EX_UNARY){
        int complement=t.is_unsigned?*high:-1;
        a=complement-a;b=complement-b;
        *low=b;*high=a;
    }else{*low=a;*high=b;}
}
static Expr *wide_word_source(Expr *e)
{
    while(e->kind==EX_CAST&&e->type.base==TY_LONGLONG&&!e->type.pointers)e=e->left;
    return known_integer(value_type(e->type))&&wide_address_safe(e)?e:NULL;
}
static int wide_integer_literal(Expr *e)
{
    return e->kind==EX_INT&&numeric(e->type)&&e->type.base!=TY_FLOAT&&e->type.base!=TY_DOUBLE;
}
static int wide_mask_zero_flags(Expr *left,Expr *right)
{
    Symbol *home;
    uint64_t bits;
    unsigned offset,i,end=0;
    int have=0;
    if(wide_integer_literal(left)){Expr *swap=left;left=right;right=swap;}
    if(!wide_integer_literal(right)||value_type(left->type).base!=TY_LONGLONG||
       !wide_scalar(value_type(left->type))||volatile_expression(left)||!(home=wide_fixed_home(left,&offset)))return 0;
    bits=initializer_cast64(((uint64_t)right->value_high<<32)|right->value,right->type);
    for(i=0;i<8;i+=2){
        unsigned word=(unsigned)(bits>>(8*i))&65535;
        if(!word)continue;
        if(have&&word!=65535){
            if(!end)end=++cg.label;
            code("    bne cg_%s_%u\n",cg.parser->unit,end);have=0;
        }
        code(have?"    ora ":"    lda ");array_operand(home,offset+i);code("\n");
        if(word!=65535)code("    and #$%04X\n",word);
        have=1;
    }
    if(!have)code("    lda #0\n");
    if(end)label(end);
    return 1;
}
/* Widening these operands preserves their low word. A range strictly
 * between the adjacent multiples of 65536 makes its zero test sufficient. */
static int wide_word_zero_flags(Expr *e)
{
    Expr *left,*right;
    int lmin,lmax,rmin,rmax,low,high;
    if(cg.parser->no_strength_reduction||e->kind!=EX_BINARY||e->type.base!=TY_LONGLONG||e->type.pointers)return 0;
    if(e->op=='&')return wide_mask_zero_flags(e->left,e->right);
    if(e->op!='+'&&e->op!='-')return 0;
    left=wide_word_source(e->left);right=wide_word_source(e->right);
    if(!left||!right)return 0;
    wide_word_bounds(left,&lmin,&lmax);
    wide_word_bounds(right,&rmin,&rmax);
    low=e->op=='+'?lmin+rmin:lmin-rmax;
    high=e->op=='+'?lmax+rmax:lmax-rmin;
    if(low<=-65536||high>=65536)return 0;
    code("; word zero test of widened arithmetic\n");
    emit_value(left);binary_after_left(left,right,e->op);
    code("    cmp #0\n");
    return 1;
}
static int wide_zero_compare(Expr *e,Type t,unsigned yes,unsigned no,unsigned fallthrough)
{
    Expr *value=e->left,*zero=e->right;
    int op=e->op,equality=op==TOK_EQ||op==TOK_NE;
    unsigned offset=0,middle;
    Symbol *home;
    if(cg.parser->no_strength_reduction)return 0;
    if(zero->kind!=EX_INT&&value->kind==EX_INT){
        zero=e->left;value=e->right;
        if(!equality)op=reverse_order(op);
    }
    if(zero->kind!=EX_INT||zero->value||zero->value_high)return 0;
    if(equality||(t.is_unsigned&&(op=='>'||op==TOK_LE))){
        if(op==TOK_EQ||op==TOK_LE){unsigned swap=yes;yes=no;no=swap;}
        branch(value,yes,no,fallthrough);
        return 1;
    }
    if(t.is_unsigned){
        unsigned target=op==TOK_GE?yes:no;
        if(body_effect(value))emit_discarded(value);
        if(target!=fallthrough)jump(target);
        return 1;
    }
    if(op=='<'||op==TOK_GE){
        Expr *word=wide_word_source(value);
        if(word){
            if(word->type.is_unsigned){
                unsigned target=op==TOK_GE?yes:no;
                if(!literal_integer_tree(word))emit_value(word);
                if(target!=fallthrough)jump(target);
            }else{
                emit_value(word);
                if(!accumulator_zero_flags())code("    cmp #0\n");
                integer_relation_flags(op,1,yes,no,fallthrough);
            }
            return 1;
        }
    }
    /* A sign test may skip the lower words of an ordinary memory operand */
    home=volatile_expression(value)?NULL:wide_fixed_home(value,&offset);
    if(home&&value_type(value->type).base!=TY_LONGLONG)home=NULL;
    if(home){
        code("    lda ");array_operand(home,offset+6);code("\n");
    }else{
        emit_wide_as(value,t);code("    lda z:__arith_lhs+6\n");
    }
    if(op=='<'||op==TOK_GE){
        integer_relation_flags(op,1,yes,no,fallthrough);
        return 1;
    }
    if(op==TOK_LE){unsigned swap=yes;yes=no;no=swap;}
    middle=++cg.label;
    flag_branch("bmi","bpl",no,middle,middle);label(middle);
    for(unsigned i=0;i<6;i+=2){
        code("    ora ");
        if(home)array_operand(home,offset+i);
        else code("z:__arith_lhs+%u",i);
        code("\n");
    }
    flag_branch("bne","beq",yes,no,fallthrough);
    return 1;
}
static int mixed_wide_equality(Expr *e,Type t,unsigned yes,unsigned no,unsigned fallthrough)
{
    Expr *lhs=e->left,*rhs=e->right;
    Type narrow=value_type(rhs->type);
    unsigned i,offset,left_offset,bytes,done;
    Symbol *left,*right;
    if(cg.parser->no_strength_reduction||value_type(lhs->type).base!=TY_LONGLONG||
       !wide_scalar(value_type(lhs->type))||narrow.pointers||
       (narrow.base!=TY_INT&&narrow.base!=TY_LONG)||volatile_expression(e)||
       !(right=wide_fixed_home(rhs,&offset)))return 0;
    left=wide_fixed_home(lhs,&left_offset);
    if(!left)emit_wide_as(lhs,t);
    bytes=width(narrow);done=++cg.label;
    if(!narrow.is_unsigned){
        code("    ldx #0\n    lda ");array_operand(right,offset+bytes-2);
        code("\n    bpl :+\n    dex\n:\n");
    }
    for(i=8;i;i-=2){
        unsigned part=i-2;
        int sign=part>=bytes&&!narrow.is_unsigned;
        code(sign?"    txa\n    cmp ":"    lda ");
        if(left)array_operand(left,left_offset+part);else code("z:__arith_lhs+%u",part);
        code("\n");
        if(part<bytes){code("    cmp ");array_operand(right,offset+part);code("\n");}
        if(part)code("    bne cg_%s_%u\n",cg.parser->unit,done);
    }
    label(done);
    flag_branch(e->op==TOK_EQ?"beq":"bne",e->op==TOK_EQ?"bne":"beq",yes,no,fallthrough);
    return 1;
}
static Expr *wide_word_magnitude_source(Expr *e)
{
    Expr *test,*negative,*positive,*word,*other;
    while(e->kind==EX_CAST&&e->type.base==TY_LONGLONG&&!e->type.pointers)e=e->left;
    if(e->kind!=EX_CHOOSE)return NULL;
    test=e->left;negative=e->right;positive=e->third;
    if(cg.parser->no_strength_reduction||e->type.base!=TY_LONGLONG||test->kind!=EX_BINARY||
       test->op!='<'||test->right->kind!=EX_INT||test->right->value||test->right->value_high||
       common_type(test->left->type,test->right->type).is_unsigned||
       !(word=wide_word_source(test->left))||!literal_integer_tree(word))return NULL;
    while(negative->kind==EX_CAST&&negative->type.base==TY_LONGLONG&&!negative->type.pointers)
        negative=negative->left;
    if(negative->kind!=EX_UNARY||negative->op!='-'||negative->type.base!=TY_LONGLONG||
       !(other=wide_word_source(negative->left))||!body_equal(word,other)||
       !(other=wide_word_source(positive))||!body_equal(word,other))return NULL;
    return word;
}
static void emit_word_magnitude(Expr *word)
{
    emit_value(word);
    if(!word->type.is_unsigned){
        if(!accumulator_zero_flags())code("    cmp #0\n");
        code("    bpl :+\n    eor #$FFFF\n    inc a\n:\n");
    }
}
static int wide_word_magnitude_equal(Expr *value,Expr *other,int op,unsigned yes,unsigned no,unsigned fallthrough)
{
    Expr *source=wide_word_magnitude_source(value),*input;
    Type word=type(TY_INT,0);
    if(!source)return 0;
    word.is_unsigned=1;
    input=wide_word_source(other);
    if(!input&&wide_integer_literal(other))input=other;
    if(input&&input->kind==EX_INT&&
       initializer_cast64(((uint64_t)input->value_high<<32)|input->value,input->type)>65535u){
        unsigned different=op==TOK_EQ?no:yes;
        if(different!=fallthrough)jump(different);
        return 1;
    }
    if(!input||!direct_operand(input,word,0,0))return 0;
    if(input->kind!=EX_INT&&!input->type.is_unsigned){
        unsigned nonnegative=++cg.label;
        code("    lda ");direct_operand(input,word,0,1);code("\n");
        flag_branch("bmi","bpl",op==TOK_EQ?no:yes,nonnegative,nonnegative);
        label(nonnegative);
    }
    emit_word_magnitude(source);
    code("    cmp ");direct_operand(input,word,0,1);code("\n");
    flag_branch(op==TOK_EQ?"beq":"bne",op==TOK_EQ?"bne":"beq",yes,no,fallthrough);
    return 1;
}
static int fixed_wide_compare(Expr *e,unsigned yes,unsigned no,unsigned fallthrough)
{
    Expr *lhs=e->left,*rhs=e->right;
    Type t=common_type(lhs->type,rhs->type);
    unsigned offset=0,left_offset=0,i;
    uint64_t bits=0;
    Symbol *home=NULL,*left=NULL;
    int op=e->op,equality=op==TOK_EQ||op==TOK_NE;
    if(t.base!=TY_LONGLONG)return 0;
    if(wide_zero_compare(e,t,yes,no,fallthrough))return 1;
    if(equality&&(wide_word_magnitude_equal(lhs,rhs,op,yes,no,fallthrough)||
                 wide_word_magnitude_equal(rhs,lhs,op,yes,no,fallthrough)))return 1;
    if(equality&&mixed_wide_equality(e,t,yes,no,fallthrough))return 1;
    if(!cg.parser->no_strength_reduction&&lhs->kind==EX_INT&&rhs->kind!=EX_INT){
        lhs=e->right;rhs=e->left;
        if(!equality)op=reverse_order(op);
    }
    if(!cg.parser->no_strength_reduction&&rhs->kind==EX_INT)
        bits=initializer_cast64(((uint64_t)rhs->value_high<<32)|rhs->value,rhs->type);
    else if(value_type(rhs->type).base!=TY_LONGLONG||!(home=wide_fixed_home(rhs,&offset)))return 0;
    if(equality&&!cg.parser->no_strength_reduction&&wide_integer_literal(rhs)){
        Expr *input=lhs;
        while(input->kind==EX_CAST&&input->type.base==TY_LONGLONG&&!input->type.pointers)input=input->left;
        Type narrow=value_type(input->type);
        if(numeric(narrow)&&narrow.base!=TY_FLOAT&&!wide_scalar(narrow)){
            if(initializer_cast64(bits,narrow)!=bits){
                unsigned different=op==TOK_EQ?no:yes;
                if(body_discard_effect(input))emit_discarded(input);
                if(different!=fallthrough)jump(different);
            }else{
                Expr literal={0},test=*e;
                literal.kind=EX_INT;literal.type=narrow;literal.value=(uint32_t)bits;
                test.left=input;test.right=&literal;test.op=op;
                branch(&test,yes,no,fallthrough);
            }
            return 1;
        }
    }
    if(!cg.parser->no_strength_reduction&&value_type(lhs->type).base==TY_LONGLONG&&
       !volatile_expression(e))
        left=wide_fixed_home(lhs,&left_offset);
    if(!left)emit_wide_as(lhs,t);
    if(equality&&(left||!home)){
        unsigned different=op==TOK_EQ?no:yes;
        for(i=8;i;i-=2){
            code("    lda ");
            if(left)array_operand(left,left_offset+i-2);
            else code("z:__arith_lhs+%u",i-2);
            code("\n    cmp ");
            if(home)array_operand(home,offset+i-2);
            else code("#$%04X",(unsigned)(bits>>(8*(i-2)))&65535);
            code("\n");
            if(i>2){
                unsigned same=++cg.label;
                flag_branch("bne","beq",different,same,same);label(same);
            }
        }
        flag_branch(op==TOK_EQ?"beq":"bne",op==TOK_EQ?"bne":"beq",yes,no,fallthrough);
        return 1;
    }
    if(!equality&&left&&home){
        unsigned ordered=++cg.label;
        if(op=='>'||op==TOK_LE){
            Symbol *swap=left;unsigned at=left_offset;
            left=home;left_offset=offset;home=swap;offset=at;
            op=reverse_order(op);
        }
        i=8;
        if(!t.is_unsigned){
            unsigned low=++cg.label;
            code("    sec\n    lda ");array_operand(left,left_offset+6);
            code("\n    sbc ");array_operand(home,offset+6);
            code("\n    beq cg_%s_%u\n    bvc :+\n    eor #$8000\n:\n",cg.parser->unit,low);
            integer_relation_flags(op,1,yes,no,0);
            label(low);i=6;
        }
        for(;i;i-=2){
            code("    lda ");array_operand(left,left_offset+i-2);
            code("\n    cmp ");array_operand(home,offset+i-2);code("\n");
            if(i>2)code("    bne cg_%s_%u\n",cg.parser->unit,ordered);
        }
        label(ordered);
        integer_relation_flags(op,0,yes,no,fallthrough);
        return 1;
    }
    i=0;
    if(!equality){
        int borrow=op=='>'||op==TOK_LE;
        if(left&&!home){
            /* Zero with carry set, or all ones with carry clear, preserves carry */
            unsigned neutral=borrow?65535:0;
            while(i<6&&((bits>>(8*i))&65535)==neutral)i+=2;
        }
        code(borrow?"    clc\n":"    sec\n");
    }
    for(;i<8;i+=2){
        code("    lda ");
        if(left)array_operand(left,left_offset+i);
        else code("z:__arith_lhs+%u",i);
        code("\n    %s ",equality?"eor":"sbc");
        if(home)array_operand(home,offset+i);
        else code("#$%04X",(unsigned)(bits>>(8*i))&65535);
        code("\n");
        if(equality&&i)code("    ora z:__arith_lhs\n");
        if(equality&&i<6)code("    sta z:__arith_lhs\n");
    }
    if(equality)flag_branch(op==TOK_EQ?"beq":"bne",op==TOK_EQ?"bne":"beq",yes,no,fallthrough);
    else{
        if(!t.is_unsigned)code("    bvc :+\n    eor #$8000\n:\n");
        integer_relation_flags(op,!t.is_unsigned,yes,no,fallthrough);
    }
    return 1;
}
static void emit_wide_compare(Expr *e)
{
    Type t=common_type(e->left->type,e->right->type);
    unsigned yes=++cg.label,no=++cg.label,end=++cg.label;
    if(fixed_wide_compare(e,yes,no,yes)){
        label(yes);code("    lda #1\n");jump(end);
        label(no);code("    lda #0\n");label(end);return;
    }
    emit_wide_pair(e->left,e->right,t);
    if(t.base==TY_DOUBLE)helper(e->op==TOK_EQ||e->op==TOK_NE?"__dcmp":"__dcmp_signal");
    else helper(t.is_unsigned?"__ucmp64":"__scmp64");
    boolean_from_compare(e->op);
}
static const char *wide_word_instruction(int op)
{
    return op=='+'?"adc":op=='-'?"sbc":op=='&'?"and":op=='|'?"ora":"eor";
}
static void emit_wide_immediate_operation(int op,Expr *literal)
{
    uint64_t bits=initializer_cast64(((uint64_t)literal->value_high<<32)|literal->value,literal->type);
    unsigned i=0;
    int carry=op=='+'||op=='-';
    if(carry){
        if(!bits)return;
        while(!((bits>>(8*i))&65535))i+=2;
        code(op=='+'?"    clc\n":"    sec\n");
    }
    for(;i<8;i+=2){
        unsigned word=(unsigned)(bits>>(8*i))&65535;
        if(!carry&&word==(op=='&'?65535u:0u))continue;
        if(op=='&'&&!word){code("    stz z:__arith_lhs+%u\n",i);continue;}
        if(op=='|'&&word==65535u)code("    lda #$FFFF\n");
        else code("    lda z:__arith_lhs+%u\n    %s #$%04X\n",i,wide_word_instruction(op),word);
        code("    sta z:__arith_lhs+%u\n",i);
    }
}
static void emit_wide_word_operation(int op,Symbol *left,unsigned left_offset,Symbol *right,unsigned offset)
{
    unsigned i;
    if(op=='+'||op=='-')code(op=='+'?"    clc\n":"    sec\n");
    for(i=0;i<8;i+=2){
        code("    lda ");
        if(left)array_operand(left,left_offset+i);else code("z:__arith_lhs+%u",i);
        code("\n    %s ",wide_word_instruction(op));
        if(right)array_operand(right,offset+i);
        else code("z:__arith_lhs+%u",i+8);
        code("\n    sta z:__arith_lhs+%u\n",i);
    }
}
static void emit_wide_operation(Type t,int op)
{
    if(t.base==TY_DOUBLE){
        helper(op=='+'?"__dadd":op=='-'?"__dsub":op=='*'?"__dmul":"__ddiv");return;
    }
    if(op=='*'||op=='/'||op=='%'||op==TOK_SHL||op==TOK_SHR){
        const char *name=op=='*'?"__mul64":op=='/'?(t.is_unsigned?"__uquot64":"__sdiv64"):
            op=='%'?(t.is_unsigned?"__umod64":"__smod64"):op==TOK_SHL?"__shl64":
            t.is_unsigned?"__ushr64":"__sshr64";
        helper(name);return;
    }
    emit_wide_word_operation(op,NULL,0,NULL,0);
}
static int wide_word_shift_bytes(Type t,int op,Expr *right)
{
    unsigned count;
    if(cg.parser->no_strength_reduction||t.base!=TY_LONGLONG||
       (op!=TOK_SHL&&op!=TOK_SHR)||!integer_constant(right,&count))return -1;
    count&=63;
    return count%16?-1:(int)(count/8);
}
static void wide_shift_slot(Symbol *home,unsigned offset,unsigned part)
{
    if(home)array_operand(home,offset+part);else code("z:__arith_lhs+%u",part);
}
static void emit_wide_word_shift(Type t,int op,unsigned bytes,Symbol *home,unsigned offset)
{
    unsigned i,first,end;
    int sign_fill=op==TOK_SHR&&!t.is_unsigned;
    int stz=!sign_fill&&(!home||(!home->owner&&!home->type.banked));
    if(!bytes)return;
    if(op==TOK_SHL){
        for(i=8;i>bytes;i-=2){
            code("    lda ");wide_shift_slot(home,offset,i-bytes-2);
            code("\n    sta ");wide_shift_slot(home,offset,i-2);code("\n");
        }
        first=0;end=bytes;
    }else{
        for(i=0;i<8-bytes;i+=2){
            code("    lda ");wide_shift_slot(home,offset,i+bytes);
            code("\n    sta ");wide_shift_slot(home,offset,i);code("\n");
        }
        first=i;end=8;
    }
    if(sign_fill)code("    bmi :+\n    lda #0\n    bra :++\n:\n    lda #$FFFF\n:\n");
    else if(!stz)code("    lda #0\n");
    for(i=first;i<end;i+=2){
        code(stz?"    stz ":"    sta ");wide_shift_slot(home,offset,i);code("\n");
    }
}
static int wide_power_divisor(Expr *e,Expr **shift)
{
    uint64_t bits;
    int count=0;
    *shift=NULL;
    if(e->kind==EX_BINARY&&e->op==TOK_SHL&&e->type.is_unsigned&&wide_address_safe(e->right)){
        *shift=e->right;e=e->left;
    }
    if(e->kind!=EX_INT)return -1;
    bits=initializer_cast64(((uint64_t)e->value_high<<32)|e->value,e->type);
    if(!bits||(bits&(bits-1)))return -1;
    while(bits>>=1)++count;
    return count;
}
static unsigned wide_unsigned_size(Expr *e)
{
    Type t;
    while(e->kind==EX_CAST&&!e->type.pointers&&e->type.base==TY_LONGLONG)e=e->left;
    t=value_type(e->type);
    if(!numeric(t)||t.pointers||t.base==TY_FLOAT||t.base==TY_DOUBLE)return 0;
    if(e->kind==EX_INT){
        uint64_t bits=initializer_cast64(((uint64_t)e->value_high<<32)|e->value,t);
        return bits<=65535?2:bits<=UINT32_MAX?4:0;
    }
    return (t.is_unsigned||t.is_bool)&&width(t)<=4?reg_width(t):0;
}
static Expr *wide_signed_long_source(Expr *e)
{
    while(e->kind==EX_CAST&&e->type.base==TY_LONGLONG&&!e->type.pointers)e=e->left;
    return e->type.base==TY_LONG&&!e->type.pointers&&!e->type.array&&!e->type.is_unsigned?e:NULL;
}
static int emit_wide_signed_long_product(Expr *left,Expr *right)
{
    Type t=type(TY_LONG,0);
    left=wide_signed_long_source(left);right=wide_signed_long_source(right);
    if(!left||!right)return 0;
    emit_value(left);push_value(t);
    emit_value(right);
    code("    sta z:__arith_lhs+8\n    stx z:__arith_lhs+10\n");
    pop_value(t);
    code("    sta z:__arith_lhs\n    stx z:__arith_lhs+2\n");
    helper("__smul32wide");
    return 1;
}
static int emit_wide_narrow_product(Expr *left,Expr *right,Type t)
{
    unsigned l=wide_unsigned_size(left),r=wide_unsigned_size(right);
    if(!l||!r||(l!=2&&r!=2))return 0;
    emit_wide_pair(left,right,t);
    /* The word helper leaves its inputs intact, with its product in A/X */
    if(l==4){
        code("    lda z:__arith_lhs+2\n    sta z:__arith_lhs+12\n"
             "    lda z:__arith_lhs\n    sta z:__arith_rhs\n"
             "    lda z:__arith_lhs+8\n    sta z:__arith_lhs\n");
    }else{
        if(r==4)code("    lda z:__arith_lhs+10\n    sta z:__arith_lhs+12\n");
        code("    lda z:__arith_lhs+8\n    sta z:__arith_rhs\n");
    }
    code("    stz z:__arith_lhs+2\n    stz z:__arith_rhs+2\n");
    helper("__mul16wide");
    if(l==2&&r==2){
        code("    sta z:__arith_lhs\n    stx z:__arith_lhs+2\n    stz z:__arith_lhs+4\n");
    }else{
        code("    sta z:__arith_lhs+14\n    stx z:__arith_lhs+16\n"
             "    lda z:__arith_lhs+12\n    sta z:__arith_rhs\n");
        helper("__mul16wide");
        code("    clc\n    adc z:__arith_lhs+16\n    sta z:__arith_lhs+2\n"
             "    txa\n    adc #0\n    sta z:__arith_lhs+4\n"
             "    lda z:__arith_lhs+14\n    sta z:__arith_lhs\n");
    }
    code("    stz z:__arith_lhs+6\n");
    return 1;
}
static int emit_wide_word_factor(Expr *left,Expr *right)
{
    while(right->kind==EX_CAST&&right->type.base==TY_LONGLONG&&!right->type.pointers)right=right->left;
    Type source=value_type(right->type);
    if(!word_integer(source)||width(source)!=2||!compare_memory_operand(right,0))return 0;
    emit_wide_operand(left);
    code("    lda ");compare_memory_operand(right,1);code("\n");
    helper(source.is_unsigned?"__umul64_word":"__smul64_word");
    return 1;
}
static int emit_wide_add_unsigned_word(Expr *left,Expr *right)
{
    Expr *input=right;
    while(input->kind==EX_CAST&&input->type.base==TY_LONGLONG&&!input->type.pointers)input=input->left;
    Type t=value_type(input->type);
    if(!wide_scalar(value_type(left->type))||!known_integer(t)||!t.is_unsigned||
       input->kind==EX_INT||body_effect(left)||body_effect(input))return 0;
    emit_value(input);push_value(t);
    emit_wide_operand(left);pop_value(t);
    code("    clc\n    adc z:__arith_lhs\n    sta z:__arith_lhs\n    bcc :+\n"
         "    inc z:__arith_lhs+2\n    bne :+\n"
         "    inc z:__arith_lhs+4\n    bne :+\n    inc z:__arith_lhs+6\n:\n");
    return 1;
}
static void emit_wide_shift_count(Expr *right,Type t)
{
    uint32_t count;
    unsigned i,offset;
    Symbol *home;
    if(integer_constant(right,&count)){
        code("    lda #$%04X\n    sta z:__arith_lhs+8\n",count&65535u);
        return;
    }
    if(compare_memory_operand(right,0)){
        code("    lda ");compare_memory_operand(right,1);code("\n    sta z:__arith_lhs+8\n");return;
    }
    if(wide_scalar(value_type(right->type))){
        if(!(home=wide_fixed_home(right,&offset))){emit_wide_rhs(right,t);return;}
        code("    lda ");array_operand(home,offset);code("\n    sta z:__arith_lhs+8\n");
        if(volatile_expression(right))for(i=2;i<8;i+=2){
            code("    lda ");array_operand(home,offset+i);code("\n");
        }
        return;
    }
    /* The shift helper consumes only the low word of the count */
    for(i=8;i;i-=2)code("    lda z:__arith_lhs+%u\n    pha\n",i-2);
    emit_value(right);code("    sta z:__arith_lhs+8\n");
    for(i=0;i<8;i+=2)code("    pla\n    sta z:__arith_lhs+%u\n",i);
}
static int emit_wide_rotate(Expr *left,Expr *right)
{
    Symbol *home;
    unsigned offset,other,i,shift,words;
    int bits;
    if(left->kind!=EX_BINARY||right->kind!=EX_BINARY)return 0;
    if(left->op==TOK_SHL){Expr *swap=left;left=right;right=swap;}
    if(left->op!=TOK_SHR||right->op!=TOK_SHL||left->type.base!=TY_LONGLONG||
       right->type.base!=TY_LONGLONG||left->right->kind!=EX_INT||right->right->kind!=EX_INT||
       left->right->value_high||right->right->value_high||
       !(shift=left->right->value)||shift>=64||right->right->value!=64-shift||
       volatile_expression(left)||volatile_expression(right)||
       !(home=wide_fixed_home(left->left,&offset))||
       wide_fixed_home(right->left,&other)!=home||offset!=other)return 0;
    words=(shift+8)/16;
    bits=(int)shift-(int)words*16;
    for(i=0;i<8;i+=2){
        code("    lda ");array_operand(home,offset+(i+2*words)%8);
        code("\n    sta z:__arith_lhs+%u\n",i);
    }
    if(bits){
        unsigned count=(unsigned)(bits>0?bits:-bits);
        if(count>1)code("    ldx #%u\n:\n",count);
        if(bits>0){
            code("    lda z:__arith_lhs\n    lsr a\n");
            for(i=8;i;i-=2)code("    ror z:__arith_lhs+%u\n",i-2);
        }else{
            code("    lda z:__arith_lhs+6\n    asl a\n");
            for(i=0;i<8;i+=2)code("    rol z:__arith_lhs+%u\n",i);
        }
        if(count>1)code("    dex\n    bne :-\n");
    }
    if(!left->type.is_unsigned){
        /* The original sign now sits immediately below the sign-fill bits */
        unsigned sign=63-shift,mask=1u<<(sign%16);
        i=2*(sign/16);
        code("    lda z:__arith_lhs+%u\n    bit #$%04X\n    beq :+\n",i,mask);
        if(mask!=0x8000)code("    ora #$%04X\n    sta z:__arith_lhs+%u\n",(0u-2*mask)&65535u,i);
        if(i<6){
            code("    lda #$FFFF\n");
            for(i+=2;i<8;i+=2)code("    sta z:__arith_lhs+%u\n",i);
        }
        code(":\n");
    }
    return 1;
}
static void emit_wide_binary(Expr *left,Expr *right,int op)
{
    int shift=op==TOK_SHL||op==TOK_SHR;
    Type t=shift?promoted(left->type):common_type(left->type,right->type);
    int bytes=wide_word_shift_bytes(t,op,right);
    unsigned offset;
    Symbol *home;
    if(!cg.parser->no_strength_reduction&&op=='|'&&t.base==TY_LONGLONG&&emit_wide_rotate(left,right))return;
    if(!cg.parser->no_strength_reduction&&!cg.function->symbol->interrupt&&
       t.base==TY_LONGLONG&&op=='*'&&
       (emit_wide_signed_long_product(left,right)||emit_wide_narrow_product(left,right,t)||
        emit_wide_word_factor(left,right)))return;
    if(!cg.parser->no_strength_reduction&&t.base==TY_LONGLONG&&op=='+'&&
       (emit_wide_add_unsigned_word(left,right)||emit_wide_add_unsigned_word(right,left)))return;
    if(!cg.parser->no_strength_reduction&&op=='/'&&t.base==TY_LONGLONG&&t.is_unsigned){
        Expr *shift_count;
        int power=wide_power_divisor(right,&shift_count);
        if(power>=0){
            Expr count={0},sum={0},input={0};
            count.kind=EX_INT;count.type=type(TY_INT,1);count.value=(unsigned)power;
            input.kind=EX_CAST;input.type=t;input.left=left;
            sum.kind=EX_BINARY;sum.op='+';sum.left=shift_count;sum.right=&count;
            if(shift_count)sum.type=common_type(shift_count->type,count.type);
            emit_wide_binary(&input,shift_count?(power?&sum:shift_count):&count,TOK_SHR);
            return;
        }
    }
    if(bytes>=0){
        emit_wide_as(left,t);emit_wide_word_shift(t,op,(unsigned)bytes,NULL,0);return;
    }
    if(shift){
        emit_wide_as(left,t);emit_wide_shift_count(right,t);emit_wide_operation(t,op);return;
    }
    if(!cg.parser->no_strength_reduction&&t.base==TY_LONGLONG&&basic_integer_op(op)){
        if(op!='-'&&wide_integer_literal(left)){Expr *swap=left;left=right;right=swap;}
        if(wide_integer_literal(right)){
            emit_wide_as(left,t);emit_wide_immediate_operation(op,right);return;
        }
    }
    if(t.base==TY_LONGLONG&&value_type(right->type).base==TY_LONGLONG&&basic_integer_op(op)&&
       (home=wide_fixed_home(right,&offset))!=NULL){
        Symbol *left_home=NULL;unsigned left_offset=0;
        if(!cg.parser->no_strength_reduction&&value_type(left->type).base==TY_LONGLONG&&
           !volatile_expression(left)&&!volatile_expression(right))left_home=wide_fixed_home(left,&left_offset);
        if(!left_home)emit_wide_as(left,t);
        emit_wide_word_operation(op,left_home,left_offset,home,offset);return;
    }
    emit_wide_pair(left,right,t);emit_wide_operation(t,op);
}
/* A/X contain the already-read narrow destination. Compute at the usual
 * wide arithmetic type, then convert the result back to that destination. */
static void emit_narrow_wide_operation_loaded(Expr *e)
{
    Type source=value_type(e->left->type),word=type(TY_LONG,0);
    Type common=common_type(e->left->type,e->right->type);
    unsigned i;
    cg.arithmetic=1;
    word.is_unsigned=source.is_unsigned;
    convert_registers(source,word);
    code("    sta z:__arith_lhs\n    stx z:__arith_lhs+2\n");
    if(source.is_unsigned)code("    lda #0\n");
    else code("    txa\n    cmp #$8000\n    lda #0\n    bcc :+\n    lda #$FFFF\n:\n");
    for(i=4;i<8;i+=2)code("    sta z:__arith_lhs+%u\n",i);
    if(common.base==TY_DOUBLE)
        helper(source.is_unsigned?"__ufloat64_64":"__sfloat64_64");
    emit_wide_rhs(e->right,common);
    emit_wide_operation(common,e->op);
    if(common.base==TY_DOUBLE)
        helper(e->type.is_unsigned?"__ufix64_32":"__fix64_32");
    code("    lda z:__arith_lhs\n");
    if(reg_width(e->type)==4)code("    ldx z:__arith_lhs+2\n");
    narrow_char(e->type);
}
static void emit_narrow_wide_compound(Expr *e)
{
    int far=e->left->type.banked;
    int wram=e->left->kind==EX_DEREF&&strength_wram_pointer(e->left->left);
    emit_address(e->left);
    if(far){
        Type address=far_type(type(TY_CHAR,1));
        push_value(address);far_load(e->left->type);
    }else{
        code("    pha\n    tax\n");
        load_indirect(e->left->type,wram);
    }
    emit_narrow_wide_operation_loaded(e);
    if(far){far_store(e->type,0);cleanup(4,e->type);}
    else store_saved_address(e->type,wram,0);
    divmod_written(e->left);
}
/* Address is in A (near) or A/X (far). Transfer four words without
 * borrowing Y across expression evaluation or overlapping the value slot. */
static void emit_wide_indirect_load(int far)
{
    unsigned i;cg.arithmetic=1;
    if(far){
        code("    sta z:__arith_lhs+28\n    stx z:__arith_lhs+30\n    phy\n");
        for(i=0;i<8;i+=2)code("    ldy #$%04X\n    lda [__arith_lhs+28],y\n    sta z:__arith_lhs+%u\n",i,i);
        code("    ply\n");
    }else{
        code("    tax\n");
        for(i=0;i<8;i+=2)code("    lda a:$%04X,x\n    sta z:__arith_lhs+%u\n",i,i);
    }
}
static void emit_wide_save_address(Expr *e)
{
    emit_address(e);
    if(e->type.banked)code("    phx\n");
    code("    pha\n");
}
static void emit_wide_store_saved(int far)
{
    unsigned i;
    if(far){
        code("    pla\n    sta z:__arith_lhs+28\n    pla\n    sta z:__arith_lhs+30\n    phy\n");
        for(i=0;i<8;i+=2)code("    ldy #$%04X\n    lda z:__arith_lhs+%u\n    sta [__arith_lhs+28],y\n",i,i);
        code("    ply\n");
    }else{
        code("    plx\n");
        for(i=0;i<8;i+=2)code("    lda z:__arith_lhs+%u\n    sta a:$%04X,x\n",i,i);
    }
}
static void emit_wide_value(Expr *e)
{
    unsigned i,offset;Symbol *home;
    if(!wide_scalar(value_type(e->type))){emit_wide_operand(e);return;}
    cg.arithmetic=1;
    switch(e->kind){
    case EX_INT:emit_wide_literal(e,0);return;
    case EX_OBJECT:case EX_MEMBER:case EX_DEREF:
        home=wide_fixed_home(e,&offset);
        if(!home){emit_address(e);emit_wide_indirect_load(e->type.banked);return;}
        for(i=0;i<8;i+=2){code("    lda ");array_operand(home,offset+i);code("\n    sta z:__arith_lhs+%u\n",i);}return;
    case EX_CAST:{
        Type source=value_type(e->left->type);
        if(e->type.base==TY_LONGLONG&&source.pointers){
            emit_value(e->left);
            code("    sta z:__arith_lhs\n");
            if(far_pointer(source))code("    stx z:__arith_lhs+2\n");
            else code("    stz z:__arith_lhs+2\n");
            code("    stz z:__arith_lhs+4\n    stz z:__arith_lhs+6\n");
            return;
        }
        if(e->type.base==TY_LONGLONG&&source.base==TY_FLOAT){
            emit_value(e->left);code("    sta z:__arith_lhs\n    stx z:__arith_lhs+2\n");
            helper("__fext32_64");helper(e->type.is_unsigned?"__ufix64_64":"__fix64_64");return;
        }
        if(e->type.base==TY_DOUBLE&&source.base==TY_FLOAT){
            emit_value(e->left);code("    sta z:__arith_lhs\n    stx z:__arith_lhs+2\n");
            helper("__fext32_64");return;
        }
        if(e->type.base==TY_DOUBLE&&source.base!=TY_DOUBLE){
            if(wide_scalar(source)){
                emit_wide_operand(e->left);helper(source.is_unsigned?"__ufloat64_64":"__sfloat64_64");
            }else{
                Type word=type(TY_LONG,0);word.is_unsigned=source.is_unsigned;
                emit_value(e->left);convert_registers(source,word);
                code("    sta z:__arith_lhs\n    stx z:__arith_lhs+2\n");
                helper(source.is_unsigned?"__ufloat64_32":"__sfloat64_32");
            }
            return;
        }
        emit_wide_operand(e->left);
        if(source.base==TY_DOUBLE&&e->type.base==TY_LONGLONG)
            helper(e->type.is_unsigned?"__ufix64_64":"__fix64_64");
        return;
    }
    case EX_CALL:emit_call(e,1);return;
    case EX_ASSIGN:emit_wide_assignment(e,0);return;
    case EX_PRE:case EX_POST:emit_wide_update(e,0);return;
    case EX_CHOOSE:{
        Expr *word=wide_word_magnitude_source(e);
        if(word){
            emit_word_magnitude(word);
            code("    sta z:__arith_lhs\n    stz z:__arith_lhs+2\n    stz z:__arith_lhs+4\n    stz z:__arith_lhs+6\n");
            return;
        }
        unsigned yes=++cg.label,no=++cg.label,end=++cg.label;
        branch(e->left,yes,no,yes);label(yes);emit_wide_operand(e->right);
        jump(end);label(no);emit_wide_operand(e->third);label(end);return;
    }
    case EX_COMMA:emit_discarded(e->left);emit_wide_operand(e->right);return;
    case EX_UNARY:
        if(!cg.parser->no_strength_reduction&&e->type.base==TY_LONGLONG&&e->op=='-'){
            Expr *word=wide_word_source(e->left);
            if(word){
                emit_value(word);
                code("    tax\n    lda #0\n    cpx #1\n    bcc :+\n");
                if(!word->type.is_unsigned)code("    cpx #$8000\n    bcs :+\n");
                code("    dec a\n:\n    sta z:__arith_lhs+2\n    sta z:__arith_lhs+4\n"
                     "    sta z:__arith_lhs+6\n    txa\n    eor #$FFFF\n    inc a\n    sta z:__arith_lhs\n");
                return;
            }
        }
        if(!cg.parser->no_strength_reduction&&e->type.base==TY_LONGLONG&&e->op!='+'&&
           !volatile_expression(e->left)&&(home=wide_fixed_home(e->left,&offset))!=NULL){
            if(e->op=='-')code("    sec\n");
            for(i=0;i<8;i+=2){
                code(e->op=='-'?"    lda #0\n    sbc ":"    lda ");
                array_operand(home,offset+i);code("\n");
                if(e->op=='~')code("    eor #$FFFF\n");
                code("    sta z:__arith_lhs+%u\n",i);
            }
            return;
        }
        emit_wide_operand(e->left);
        if(e->op=='+')return;
        if(e->type.base==TY_DOUBLE){code("    lda z:__arith_lhs+6\n    eor #$8000\n    sta z:__arith_lhs+6\n");return;}
        if(e->op=='-')code("    sec\n");
        for(i=0;i<8;i+=2){
            if(e->op=='-')code("    lda #0\n    sbc z:__arith_lhs+%u\n",i);
            else code("    lda z:__arith_lhs+%u\n    eor #$FFFF\n",i);
            code("    sta z:__arith_lhs+%u\n",i);
        }
        return;
    case EX_BINARY:emit_wide_binary(e->left,e->right,e->op);return;
    default:error_at(e->location,"unsupported 64-bit runtime expression");
    }
}
/* The left operand is already in the wide result slot. Compound assignment
 * performs the usual arithmetic conversions before converting back. */
static void emit_wide_compound_loaded(Expr *e)
{
    Type t=(e->op==TOK_SHL||e->op==TOK_SHR)?promoted(e->left->type):common_type(e->left->type,e->right->type);
    int integer_destination=e->type.base==TY_LONGLONG;
    int bytes=wide_word_shift_bytes(t,e->op,e->right);
    if(integer_destination&&t.base==TY_FLOAT){
        Type single=type(TY_FLOAT,0);
        helper(e->type.is_unsigned?"__ufloat32_64":"__sfloat32_64");
        code("    lda z:__arith_lhs\n    ldx z:__arith_lhs+2\n");
        push_value(single);
        emit_value(e->right);
        stage(1,single);pop_value(single);stage(0,single);
        binary_loaded(e->op,single,0);
        code("    sta z:__arith_lhs\n    stx z:__arith_lhs+2\n");
        helper("__fext32_64");
        helper(e->type.is_unsigned?"__ufix64_64":"__fix64_64");
        return;
    }
    if(integer_destination&&t.base==TY_DOUBLE)
        helper(e->type.is_unsigned?"__ufloat64_64":"__sfloat64_64");
    if(bytes>=0){emit_wide_word_shift(t,e->op,(unsigned)bytes,NULL,0);return;}
    if(!cg.parser->no_strength_reduction&&t.base==TY_LONGLONG&&
       basic_integer_op(e->op)&&wide_integer_literal(e->right)){
        emit_wide_immediate_operation(e->op,e->right);return;
    }
    if(e->op==TOK_SHL||e->op==TOK_SHR)emit_wide_shift_count(e->right,t);
    else emit_wide_rhs(e->right,t);
    emit_wide_operation(t,e->op);
    if(integer_destination&&t.base==TY_DOUBLE)
        helper(e->type.is_unsigned?"__ufix64_64":"__fix64_64");
}
static Symbol *vr_base(Expr *e);
static int add_fixed_wide_shift(Expr *e,Symbol *home,unsigned offset)
{
    Expr *shift=e->right,*input;
    Type source;
    int bytes;
    if((e->op!='+'&&e->op!='-')||e->type.base!=TY_LONGLONG||volatile_expression(e)||
       shift->kind!=EX_BINARY||shift->op!=TOK_SHL||
       (bytes=wide_word_shift_bytes(shift->type,shift->op,shift->right))<=0||
       body_effect(shift->left))return 0;
    input=shift->left;
    while(input->kind==EX_CAST&&input->type.base==TY_LONGLONG&&!input->type.pointers)
        input=input->left;
    source=value_type(input->type);
    if(bytes>=4&&numeric(source)&&source.base!=TY_FLOAT&&!wide_scalar(source)){
        Type retained=type(bytes==6?TY_INT:TY_LONG,source.is_unsigned);
        cg.arithmetic=1;
        emit_value(input);convert_registers(source,retained);
        code("    sta z:__arith_lhs\n");
        if(bytes==4)code("    stx z:__arith_lhs+2\n");
    }else emit_wide_operand(shift->left);
    code(e->op=='+'?"    clc\n":"    sec\n");
    for(unsigned i=(unsigned)bytes;i<8;i+=2){
        code("    lda ");array_operand(home,offset+i);
        code("\n    %s z:__arith_lhs+%u\n    sta ",wide_word_instruction(e->op),i-(unsigned)bytes);
        array_operand(home,offset+i);code("\n");
    }
    return 1;
}
static int update_fixed_wide_mask(Expr *e,Symbol *home,unsigned offset)
{
    Expr *literal=e->right;
    uint64_t bits;
    unsigned i,source_offset;
    int op=e->op;
    if(cg.parser->no_strength_reduction||e->type.base!=TY_LONGLONG||volatile_expression(e))return 0;
    if(!op&&literal->kind==EX_CAST&&literal->left->type.base==TY_LONGLONG&&
       wide_scalar(value_type(literal->left->type)))literal=literal->left;
    if(!op&&literal->kind==EX_BINARY&&wide_fixed_home(literal->left,&source_offset)==home&&source_offset==offset){
        op=literal->op;literal=literal->right;
    }
    if((op!='&'&&op!='|'&&op!='^')||!wide_integer_literal(literal))return 0;
    bits=initializer_cast64(((uint64_t)literal->value_high<<32)|literal->value,literal->type);
    for(i=0;i<8;i+=2){
        unsigned word=(unsigned)(bits>>(8*i))&65535;
        if(word==(op=='&'?65535u:0u))continue;
        if(op=='&'&&!word&&!home->owner&&!home->type.banked){
            code("    stz ");array_operand(home,offset+i);code("\n");continue;
        }
        if((op=='&'&&!word)||(op=='|'&&word==65535u))code("    lda #$%04X\n",word);
        else{
            code("    lda ");array_operand(home,offset+i);
            code("\n    %s #$%04X\n",wide_word_instruction(op),word);
        }
        code("    sta ");array_operand(home,offset+i);code("\n");
    }
    return 1;
}
enum { WIDEN_FULL, WIDEN_HIGH, WIDEN_LOW };
static int store_widened_integer(Expr *e,Symbol *home,unsigned offset,int part)
{
    Expr *input=e->right;
    Type source,word=type(TY_LONG,0);
    unsigned i,start=part==WIDEN_HIGH?4:0;
    if(cg.parser->no_strength_reduction||e->op||e->type.base!=TY_LONGLONG||volatile_expression(e))return 0;
    while(input->kind==EX_CAST&&input->type.base==TY_LONGLONG&&!input->type.pointers)input=input->left;
    source=value_type(input->type);
    if(!numeric(source)||source.base==TY_FLOAT||wide_scalar(source))return 0;
    word.is_unsigned=source.is_unsigned;
    emit_value(input);convert_registers(source,word);
    code("    sta ");array_operand(home,offset+start);code("\n    txa\n    sta ");array_operand(home,offset+start+2);code("\n");
    if(part!=WIDEN_FULL||source.is_unsigned)code("    lda #0\n");
    else code("    asl a\n    lda #0\n    bcc :+\n    dec a\n:\n");
    for(i=0;i<4;i+=2){code("    sta ");array_operand(home,offset+4-start+i);code("\n");}
    return 1;
}
static int adjacent_widened_store(Statement *s)
{
    Expr *store=s->expression,*update;
    Symbol *home;
    unsigned offset;
    int part;
    uint64_t value;
    if(cg.parser->no_strength_reduction||!store||store->kind!=EX_ASSIGN||store->op||
       store->type.base!=TY_LONGLONG||!store->type.is_unsigned||store->type.pointers||
       !s->next||s->next->kind!=ST_EXPR||!(update=s->next->expression)||update->kind!=EX_ASSIGN||
       !wide_integer_literal(update->right)||!body_equal(store->left,update->left)||
       !(home=wide_fixed_home(store->left,&offset)))return 0;
    value=initializer_cast64(((uint64_t)update->right->value_high<<32)|update->right->value,update->right->type);
    if(update->op==TOK_SHL&&value==32)part=WIDEN_HIGH;
    else if(update->op=='&'&&value==UINT32_MAX)part=WIDEN_LOW;
    else return 0;
    if(!store_widened_integer(store,home,offset,part))return 0;
    divmod_written(store->left);return 1;
}
static int copy_disjoint_wide_assignment(Expr *e,Symbol *home,unsigned offset)
{
    Expr *input=e->right;
    unsigned i,source_offset;
    Symbol *source;
    if(cg.parser->no_strength_reduction||e->op||input->type.base!=e->type.base||
       !wide_scalar(value_type(input->type))||volatile_expression(e))return 0;
    source=wide_fixed_home(input,&source_offset);
    if(source==home)return 0;
    if(!source){
        Symbol *base;
        if(input->kind!=EX_DEREF||far_pointer(value_type(input->left->type))||
           !(base=vr_base(input->left))||base==home)return 0;
        emit_address_x(input);
    }
    for(i=0;i<8;i+=2){
        code("    lda ");
        if(source)array_operand(source,source_offset+i);else code("a:$%04X,x",i);
        code("\n    sta ");array_operand(home,offset+i);code("\n");
    }
    return 1;
}
static int discarded_fixed_wide_assignment(Expr *e,Symbol *home,unsigned offset)
{
    Expr *value=e->right,*input=value;
    Symbol *source,*right=NULL;
    unsigned i,source_offset,right_offset=0;
    int base=e->left->type.base,unary=0;
    if(e->op||home->owner||home->type.banked||value->type.base!=base||!wide_scalar(value_type(value->type)))return 0;
    if(value->kind==EX_UNARY&&(value->op=='-'||value->op=='~')){
        unary=value->op;
        input=value->left;
    }else if(value->kind==EX_BINARY&&base==TY_LONGLONG&&basic_integer_op(value->op)){
        if(value->right->type.base!=base||!wide_scalar(value_type(value->right->type))||
           !(right=wide_fixed_home(value->right,&right_offset)))return 0;
        input=value->left;
    }
    if(!wide_scalar(value_type(input->type))||input->type.base!=base||!(source=wide_fixed_home(input,&source_offset)))return 0;

    /* Keep all reads in operand order before any destination writes.
     * The last result word stays in A while X stores the first three. */
    cg.arithmetic=1;
    if(unary=='-'&&base==TY_LONGLONG)code("    sec\n");
    for(i=0;i<8;i+=2){
        if(unary=='-'&&base==TY_LONGLONG)code("    lda #0\n    sbc ");
        else if(right&&i==6&&!source->owner&&!source->type.banked)code("    ldx ");
        else code("    lda ");
        array_operand(source,source_offset+i);code("\n");
        if(unary=='~')code("    eor #$FFFF\n");
        if(unary=='-'&&base==TY_DOUBLE&&i==6)code("    eor #$8000\n");
        if(i<6)code("    sta z:__arith_lhs+%u\n",i);
        else if(right&&(source->owner||source->type.banked))code("    tax\n");
    }
    if(right){
        if(value->op=='+'||value->op=='-')code(value->op=='+'?"    clc\n":"    sec\n");
        for(i=0;i<8;i+=2){
            if(i<6)code("    lda z:__arith_lhs+%u\n",i);
            else code("    txa\n");
            code("    %s ",wide_word_instruction(value->op));
            array_operand(right,right_offset+i);code("\n");
            if(i<6)code("    sta z:__arith_lhs+%u\n",i);
        }
    }
    for(i=0;i<6;i+=2){
        code("    ldx z:__arith_lhs+%u\n    stx ",i);array_operand(home,offset+i);code("\n");
    }
    code("    sta ");array_operand(home,offset+6);code("\n");
    return 1;
}
static int store_wide_integer_literal(Expr *e,Symbol *home,unsigned offset)
{
    Expr *literal=e->right;
    unsigned loaded=65536;
    uint64_t bits;
    if(cg.parser->no_strength_reduction||e->op||e->type.base!=TY_LONGLONG||
       !wide_integer_literal(literal)||volatile_expression(e))return 0;
    if(!home){
        if(e->left->type.banked)return 0;
        emit_address_x(e->left);
    }
    bits=initializer_cast64(((uint64_t)literal->value_high<<32)|literal->value,literal->type);
    for(unsigned i=0;i<8;i+=2){
        unsigned word=(unsigned)(bits>>(8*i))&65535;
        if(!word&&(!home||(!home->owner&&!home->type.banked)))code("    stz ");
        else{
            if(word!=loaded){code("    lda #$%04X\n",word);loaded=word;}
            code("    sta ");
        }
        if(home){array_operand(home,offset+i);code("\n");}
        else code("a:$%04X,x\n",i);
    }
    return 1;
}
static void emit_wide_assignment(Expr *e,int discarded)
{
    unsigned i,offset;
    Symbol *home=wide_fixed_home(e->left,&offset);
    if(!home){
        if(discarded&&store_wide_integer_literal(e,NULL,0))return;
        if(discarded&&!cg.parser->no_strength_reduction&&!e->op&&
           e->left->kind==EX_DEREF&&!e->left->type.banked&&
           e->left->left->kind==EX_OBJECT&&!volatile_expression(e)&&!body_effect(e->right)){
            emit_wide_as(e->right,e->type);
            emit_address_x(e->left);
            for(i=0;i<8;i+=2)code("    lda z:__arith_lhs+%u\n    sta a:$%04X,x\n",i,i);
            return;
        }
        emit_wide_save_address(e->left);
        if(e->op){
            emit_wide_indirect_load(e->left->type.banked);emit_wide_compound_loaded(e);
        }else emit_wide_as(e->right,e->type);
        emit_wide_store_saved(e->left->type.banked);return;
    }
    if(discarded&&!volatile_expression(e)){
        Type t=promoted(e->type);
        int bytes=wide_word_shift_bytes(t,e->op,e->right);
        if(bytes>=0){emit_wide_word_shift(t,e->op,(unsigned)bytes,home,offset);return;}
    }
    if(discarded&&(add_fixed_wide_shift(e,home,offset)||update_fixed_wide_mask(e,home,offset)||
                   store_wide_integer_literal(e,home,offset)||copy_disjoint_wide_assignment(e,home,offset)||
                   store_widened_integer(e,home,offset,WIDEN_FULL)||discarded_fixed_wide_assignment(e,home,offset)))return;
    if(e->op){emit_wide_operand(e->left);emit_wide_compound_loaded(e);}
    else emit_wide_as(e->right,e->type);
    for(i=0;i<8;i+=2){code("    lda z:__arith_lhs+%u\n    sta ",i);array_operand(home,offset+i);code("\n");}
}
static void emit_wide_update(Expr *e,int discarded)
{
    unsigned i,offset;Symbol *home=wide_fixed_home(e->left,&offset);
    if(!cg.parser->no_strength_reduction&&home&&e->type.base==TY_LONGLONG&&!volatile_expression(e->left)){
        int inc=e->op==TOK_INC,post=e->kind==EX_POST;
        unsigned done=discarded?++cg.label:0;
        if(!discarded)cg.arithmetic=1;
        code(inc?"    clc\n":"    sec\n");
        for(i=0;i<8;i+=2){
            code("    lda ");array_operand(home,offset+i);code("\n");
            if(!discarded&&post)code("    sta z:__arith_lhs+%u\n",i);
            code("    %s #$%04X\n    sta ",inc?"adc":"sbc",i?0:1);
            array_operand(home,offset+i);code("\n");
            if(!discarded&&!post)code("    sta z:__arith_lhs+%u\n",i);
            if(discarded&&i<6)code("    %s cg_%s_%u\n",inc?"bcc":"bcs",cg.parser->unit,done);
        }
        if(discarded)label(done);
        return;
    }
    if(home)emit_wide_operand(e->left);
    else{emit_wide_save_address(e->left);emit_wide_indirect_load(e->left->type.banked);}
    if(e->type.base==TY_DOUBLE){
        int post=e->kind==EX_POST,far=e->left->type.banked;
        if(post)for(i=8;i;i-=2)code("    lda z:__arith_lhs+%u\n    pha\n",i-2);
        code("    stz z:__arith_lhs+8\n    stz z:__arith_lhs+10\n"
             "    stz z:__arith_lhs+12\n    lda #$3FF0\n    sta z:__arith_lhs+14\n");
        helper(e->op==TOK_INC?"__dadd":"__dsub");
        if(home){
            for(i=0;i<8;i+=2){code("    lda z:__arith_lhs+%u\n    sta ",i);array_operand(home,offset+i);code("\n");}
        }else if(!post)emit_wide_store_saved(far);
        else if(far){
            code("    lda 9,s\n    sta z:__arith_lhs+28\n    lda 11,s\n    sta z:__arith_lhs+30\n    phy\n");
            for(i=0;i<8;i+=2)code("    ldy #$%04X\n    lda z:__arith_lhs+%u\n    sta [__arith_lhs+28],y\n",i,i);
            code("    ply\n");
        }else{
            code("    lda 9,s\n    tax\n");
            for(i=0;i<8;i+=2)code("    lda z:__arith_lhs+%u\n    sta a:$%04X,x\n",i,i);
        }
        if(post){
            for(i=0;i<8;i+=2)code("    pla\n    sta z:__arith_lhs+%u\n",i);
            if(!home){code("    plx\n");if(far)code("    plx\n");}
        }
        return;
    }
    if(e->kind==EX_POST)
        for(i=0;i<8;i+=2)code("    lda z:__arith_lhs+%u\n    sta z:__arith_lhs+%u\n",i,i+8);
    code(e->op==TOK_INC?"    clc\n":"    sec\n");
    for(i=0;i<8;i+=2)code("    lda z:__arith_lhs+%u\n    %s #$%04X\n    sta z:__arith_lhs+%u\n",
        i,e->op==TOK_INC?"adc":"sbc",i?0:1,i);
    if(!home)emit_wide_store_saved(e->left->type.banked);
    else for(i=0;i<8;i+=2){code("    lda z:__arith_lhs+%u\n    sta ",i);array_operand(home,offset+i);code("\n");}
    if(e->kind==EX_POST)
        for(i=0;i<8;i+=2)code("    lda z:__arith_lhs+%u\n    sta z:__arith_lhs+%u\n",i+8,i);
}
static void emit_wide_narrow(Expr *e)
{
    Expr *source=e->left;
    unsigned offset=0;
    int bytes=-1,byte_result=!e->type.pointers&&e->type.base==TY_CHAR;
    unsigned result_bytes=byte_result?1:reg_width(e->type);
    uint32_t mask,needed=result_bytes==4?UINT32_MAX:(1u<<(8*result_bytes))-1u;
    if(e->type.is_bool&&!e->type.pointers){
        unsigned yes=++cg.label,no=++cg.label,end=++cg.label;
        branch(e->left,yes,no,yes);label(yes);code("    lda #1\n");jump(end);
        label(no);code("    lda #0\n");label(end);return;
    }
    if(!cg.parser->no_strength_reduction&&!e->type.pointers&&e->type.base!=TY_FLOAT&&
       source->kind==EX_BINARY&&source->op=='&'&&
       integer_constant(source->right,&mask)&&(mask&needed)==needed)source=source->left;
    if(source->kind==EX_BINARY&&source->op==TOK_SHR&&e->type.base!=TY_FLOAT){
        Type t=promoted(source->left->type);
        bytes=wide_word_shift_bytes(t,TOK_SHR,source->right);
        if(bytes<0&&!cg.parser->no_strength_reduction&&!cg.parser->no_byte_shuffles&&
           t.base==TY_LONGLONG&&integer_constant(source->right,&mask)&&!(mask&7))
            bytes=(int)((mask&63)/8);
    }
    if(bytes>=0&&bytes+(int)result_bytes<=8){
        Expr *input=source->left;
        Symbol *home=volatile_expression(input)?NULL:wide_fixed_home(input,&offset);
        int last_byte=byte_result&&bytes==7;
        offset+=(unsigned)bytes;
        if(home){
            if(reg_width(e->type)==4){
                code("    lda ");array_operand(home,offset+2);code("\n    tax\n");
            }
            if(last_byte)code("    sep #$20\n.a8\n");
            code("    lda ");array_operand(home,offset);code("\n");
        }else{
            emit_wide_operand(input);
            if(last_byte)code("    sep #$20\n.a8\n");
            code("    lda z:__arith_lhs+%u\n",offset);
            if(reg_width(e->type)==4)code("    ldx z:__arith_lhs+%u\n",offset+2);
        }
        if(last_byte)code("    rep #$20\n.a16\n");
    }else{
        emit_wide_operand(source);
        if(source->type.base==TY_DOUBLE)
            helper(e->type.base==TY_FLOAT?"__ftrunc64_32":e->type.is_unsigned?"__ufix64_32":"__fix64_32");
        else if(!e->type.pointers&&e->type.base==TY_FLOAT)
            helper(source->type.is_unsigned?"__ufloat32_64":"__sfloat32_64");
        code("    lda z:__arith_lhs\n");
        if(reg_width(e->type)==4)code("    ldx z:__arith_lhs+2\n");
    }
    if(e->type.pointers&&far_pointer(e->type))
        code("    pha\n    txa\n    and #$00FF\n    tax\n    pla\n");
    narrow_char(e->type);
}
static int narrow_statements(Statement *s,int allow_return)
{
    for(;s;s=s->next){
        if((s->kind==ST_RETURN&&!allow_return)||!wide_address_safe(s->expression)||!wide_address_safe(s->step)||
           !narrow_statements(s->initial,allow_return)||!narrow_statements(s->body,allow_return)||
           !narrow_statements(s->alternate,allow_return))return 0;
    }
    return 1;
}
static int body_step_direction(Expr *e,Symbol *v);
static int body_asm_statements(Statement *s);
static int body_direct_integer_stores(Statement *s,Symbol *index,int literals);
static Symbol *bounded_wide_induction(Statement *s,uint32_t *begin,uint32_t *end)
{
    Statement *initial=body_single(s->initial);
    Expr *test=s->expression,*init;
    Symbol *index;
    if(cg.parser->no_strength_reduction||cg.function->jump_label_count||cg.switch_depth||
       s->kind!=ST_FOR||!test||test->kind!=EX_BINARY||(test->op!='<'&&test->op!=TOK_LE)||
       test->left->kind!=EX_OBJECT||test->left->type.pointers||test->left->type.base!=TY_LONGLONG||
       !initial||initial->next||initial->kind!=ST_EXPR||!(init=initial->expression)||
       init->kind!=EX_ASSIGN||init->op||!body_equal(init->left,test->left))return NULL;
    index=test->left->symbol;
    if(object_volatile(index->type)||(!loop_private(index)&&
       (index->owner||!body_direct_integer_stores(s->body,index,0)))||
       body_step_direction(s->step,index)!=1||
       dp_counter_modified(s->body,index)||body_asm_statements(s->body)||
       wide_unsigned_size(init->right)!=2||!integer_constant(init->right,begin)||*begin>65535||
       wide_unsigned_size(test->right)!=2||!integer_constant(test->right,end)||*end>65535)return NULL;
    *end+=test->op==TOK_LE;
    return *end<=65535?index:NULL;
}
static Expr *wide_loop_signed_count_bound(Statement *s)
{
    Statement *initial=body_single(s->initial);
    Expr *test=s->expression,*init;
    Symbol *index,*bound;
    uint32_t zero;
    if(cg.parser->no_strength_reduction||cg.parser->no_register_loops||cg.function->jump_label_count||
       cg.switch_depth||cg.function->symbol->interrupt||s->kind!=ST_FOR||!test||
       test->kind!=EX_BINARY||test->op!='<'||test->left->kind!=EX_OBJECT||
       test->right->kind!=EX_OBJECT||!initial||initial->next||initial->kind!=ST_EXPR||
       !(init=initial->expression)||init->kind!=EX_ASSIGN||init->op||
       !body_equal(init->left,test->left)||!integer_constant(init->right,&zero)||zero)return NULL;
    index=test->left->symbol;bound=test->right->symbol;
    if(index==bound||!word_integer(index->type)||!word_integer(bound->type)||
       width(index->type)!=2||width(bound->type)!=2||
       index->type.is_unsigned||bound->type.is_unsigned||object_volatile(index->type)||
       object_volatile(bound->type)||!loop_private(index)||!loop_private(bound)||
       body_step_direction(s->step,index)!=1||dp_counter_modified(s->body,index)||
       dp_counter_modified(s->body,bound)||body_asm_statements(s->body)||
       !compare_memory_operand(test->right,0))return NULL;
    return test->right;
}
static int emit_wide_loop(Statement *s)
{
    /* Complete narrow loops have no live wide temporary at either boundary */
    if(!cg.function->jump_label_count&&wide_address_safe(s->expression)&&wide_address_safe(s->step)&&
       narrow_statements(s->initial,0)&&narrow_statements(s->body,0))return emit_loop_statement(s);
    unsigned start=++cg.label,body=++cg.label,end=++cg.label,step;int falls;
    uint32_t begin,bound=0;
    Symbol *index=bounded_wide_induction(s,&begin,&bound);
    Expr *signed_bound=wide_loop_signed_count_bound(s);
    if(s->initial)emit_statements(s->initial);
    step=s->kind==ST_WHILE?start:++cg.label;
    if(cg.loop_count==64)error_at(s->location,"too many nested loops");
    cg.loop_start[cg.loop_count]=step;cg.loop_end[cg.loop_count++]=end;
    label(start);
    if(index){
        code("; bounded wide induction: low word only\n    lda ");
        array_operand(index,0);code("\n    cmp #$%04X\n",bound);
        flag_branch("bcc","bcs",body,end,body);
    }else if(signed_bound){
        unsigned nonzero=++cg.label;
        code("; signed count with unsigned back edge\n");
        emit_value(signed_bound);
        if(!accumulator_zero_flags())code("    cmp #0\n");
        flag_branch("beq","bne",end,nonzero,nonzero);label(nonzero);
        flag_branch("bmi","bpl",end,body,body);
    }else if(s->kind!=ST_DO&&s->expression)branch(s->expression,body,end,body);
    label(body);falls=emit_statements(s->body);
    if(s->kind!=ST_WHILE)label(step);
    if(index){
        code("    lda ");array_operand(index,0);
        code("\n    inc a\n    sta ");array_operand(index,0);code("\n");
    }else if(signed_bound){
        Symbol *counter=s->expression->left->symbol;
        load_symbol(counter);code("    inc a\n");store_symbol(counter);
        code("    cmp ");compare_memory_operand(signed_bound,1);code("\n");
        flag_branch("bcc","bcs",body,end,end);
    }else if(s->step){
        if(wide_assignment_supported(s->step))emit_wide_assignment(s->step,1);
        else if(wide_update_supported(s->step))emit_wide_update(s->step,1);
        else if(wide_narrow_assignment(s->step)){emit_wide_narrow(s->step->right);store_symbol(s->step->left->symbol);}
        else if(!volatile_expression(s->step)&&strength_update(s->step,0)){}
        else emit_discarded(s->step);
    }
    if(s->kind==ST_DO)branch(s->expression,start,end,end);
    else if(!signed_bound&&(falls||s->kind==ST_FOR))jump(start);
    --cg.loop_count;cg.divmod_available=0;label(end);
    if(s->kind!=ST_DO&&!s->expression&&!contains_break(s->body)&&!cg.switch_depth)return 0;
    return 1;
}
static int shifted_bit_update(Statement *s)
{
    Statement *a=body_single(s->body),*b=body_single(s->alternate);
    Expr *test=s->expression,*yes,*no,*value,*bits,*shift;
    uint32_t mask,count;
    int invert=0;
    Type t;
    if(cg.parser->no_strength_reduction||cg.function->jump_label_count||
       !a||!b||a->next||b->next||a->kind!=ST_EXPR||b->kind!=ST_EXPR||
       !(yes=a->expression)||!(no=b->expression)||yes->kind!=EX_ASSIGN||no->kind!=EX_ASSIGN)
        return 0;
    if(test->kind==EX_BINARY&&(test->op==TOK_EQ||test->op==TOK_NE)&&
       integer_constant(test->right,&mask)&&!mask){
        invert=test->op==TOK_EQ;test=test->left;
    }
    if(invert){Expr *swap=yes;yes=no;no=swap;}
    value=yes->left;t=value_type(value->type);
    if(value->kind!=EX_OBJECT||t.pointers||t.base!=TY_LONG||!t.is_unsigned||
       volatile_expression(value)||!body_equal(value,no->left)||
       test->kind!=EX_BINARY||test->op!='&'||!body_equal(test->left,value)||
       !integer_constant(test->right,&mask)||mask!=1)return 0;
    bits=yes->right;
    if(yes->op||bits->kind!=EX_BINARY||bits->op!='^'||!integer_constant(bits->right,&mask))return 0;
    shift=bits->left;
    if(shift->kind!=EX_BINARY||shift->op!=TOK_SHR||!body_equal(shift->left,value)||
       !integer_constant(shift->right,&count)||count!=1)return 0;
    if(no->op==TOK_SHR){
        if(!integer_constant(no->right,&count)||count!=1)return 0;
    }else if(no->op||!body_equal(no->right,shift))return 0;
    code("; shift carry selects the XOR mask\n");
    if(direct_operand(value,t,0,0)&&direct_operand(value,t,1,0)){
        code("    lda ");direct_operand(value,t,1,1);
        code("\n    lsr a\n    tax\n    lda ");direct_operand(value,t,0,1);
        code("\n    ror a\n");
        if(mask>>16){
            if(mask&65535u)code("    bcc :+\n    eor #$%04X\n:\n",mask&65535u);
            code("    sta ");array_operand(value->symbol,0);
            code("\n    txa\n    bcc :+\n    eor #$%04X\n:\n    sta ",mask>>16);
            array_operand(value->symbol,2);code("\n");
            cg.divmod_available=0;
            return 1;
        }
    }else{
        load_symbol(value->symbol);constant_shift32(TOK_SHR,t,1);
    }
    if(mask){
        code("    bcc :+\n");
        if(mask&65535u)code("    eor #$%04X\n",mask&65535u);
        if(mask>>16)code("    pha\n    txa\n    eor #$%04X\n    tax\n    pla\n",mask>>16);
        code(":\n");
    }
    store_symbol(value->symbol);cg.divmod_available=0;
    return 1;
}
static int discarded_near_double(Expr *e)
{
    Expr *target=e->left;
    if(cg.parser->no_strength_reduction||e->kind!=EX_ASSIGN||e->op!='+'||
       target->kind!=EX_DEREF||target->type.pointers||target->type.banked||
       (target->type.base!=TY_INT&&target->type.base!=TY_LONG&&target->type.base!=TY_LONGLONG)||
       far_pointer(value_type(target->left->type))||body_effect(target)||
       !body_equal(target,e->right))return 0;
    emit_value_x(target->left);
    code("    asl a:$0000,x\n");
    for(unsigned i=2;i<width(target->type);i+=2)code("    rol a:$%04X,x\n",i);
    divmod_written(target);
    return 1;
}
static int emit_statements(Statement *s)
{
    Statement *previous=NULL;
    for(;s;previous=s,s=s->next){
        unsigned end,body,step;int a,b;Statement *byte_end;
        loop_previous=previous;loop_current=s;
        code("; %s:%d:%d\n",s->location.path?s->location.path:"<generated>",s->location.line,s->location.column);
        if(!cg.function->jump_label_count&&!cg.function->uses_wide){
            if((byte_end=guarded_word_bits(s))!=NULL){s=byte_end;continue;}
            if((byte_end=fixed_byte_copy_region(s))!=NULL){s=byte_end;continue;}
            if((byte_end=fixed_word_row_region(s))!=NULL){s=byte_end;continue;}
            if((byte_end=word_row_region(s))!=NULL){s=byte_end;continue;}
            if((byte_end=byte_index_region(s))!=NULL){s=byte_end;continue;}
            if((byte_end=carry_mask_sequence(s))!=NULL){s=byte_end;continue;}
            if((byte_end=packed_read_guard(s))!=NULL){s=byte_end;continue;}
            if((byte_end=guarded_byte_decrement(s))!=NULL){s=byte_end;continue;}
            if((byte_end=byte_cursor_increment_group(s))!=NULL){s=byte_end;continue;}
            if((byte_end=incremented_byte_guard(s))!=NULL){s=byte_end;continue;}
            if((byte_end=byte_guard_group(s))!=NULL){s=byte_end;continue;}
        }
        switch(s->kind){
        case ST_EMPTY:break;
        case ST_GOTO:jump(cg.jump_base+s->jump_label);cg.divmod_available=0;break;
        case ST_LABEL:
            cg.divmod_available=0;label(cg.jump_base+s->jump_label);
            if(!far_sentinel_doubling_loop(s))emit_statements(s->body);
            break;
        case ST_BLOCK:
            inline_marker(s);
            if((byte_end=adjacent_bitfield_stores(s))!=NULL){s=byte_end;break;}
            if(!emit_statements(s->body))return 0;break;
        case ST_EXPR:
            if(adjacent_widened_store(s)){s=s->next;break;}
            if(discarded_near_double(s->expression))break;
            if(wide_assignment_supported(s->expression)){emit_wide_assignment(s->expression,1);break;}
            if(wide_update_supported(s->expression)){emit_wide_update(s->expression,1);break;}
            if(wide_narrow_assignment(s->expression)){
                emit_wide_narrow(s->expression->right);store_symbol(s->expression->left->symbol);break;
            }
            if(!wide_address_safe(s->expression)){emit_discarded(s->expression);break;}
            if(s->next&&unroll_far_pointer_sum(s,s->next)){s=s->next;break;}
            if((byte_end=local_byte_block(s))!=NULL){s=byte_end;break;}
            if((byte_end=indirect_long_fields(s))!=NULL){s=byte_end;break;}
            if((byte_end=adjacent_bitfield_stores(s))!=NULL){s=byte_end;break;}
            if(adjacent_store(s)){s=s->next;break;}
            if(discarded_byte_shift_difference(s->expression)){}
            else if(masked_byte_assignment(s->expression)){}
            else if(!volatile_expression(s->expression)&&strength_update(s->expression,0)){}
            else if(!volatile_expression(s->expression)&&discarded_far_update(s->expression)){}
            else if(discarded_far_home_copy(s->expression)){}
            else if(scalar_home_update(s->expression,0)){}
            else if(discarded_direct_increment(s->expression)){}
            else emit_discarded(s->expression);
            if(s->expression->kind==EX_ASSIGN||s->expression->kind==EX_PRE||s->expression->kind==EX_POST)
                divmod_written(s->expression->left);
            break;
        case ST_SWITCH:emit_switch(s);break;
        case ST_CASE:
            cg.divmod_available=0;label(s->case_label);emit_statements(s->body);break;
        case ST_RETURN:
            if(s->expression){
                if(wide_scalar(value_type(cg.function->symbol->type)))emit_wide_operand(s->expression);
                else emit_value(s->expression);
            }
            if(cg.scalar_leaf){unsigned spill;for(spill=0;spill<(unsigned)cg.scalar_spill;++spill)code("    plx\n");code("    rts\n");return 0;}
            code("    jmp .loword(return_%s)\n",cg.function->symbol->asm_name);
            if(!cg.switch_depth)return 0;cg.divmod_available=0;break;
        case ST_IF:
            if(shifted_bit_update(s))break;
            if(!cg.parser->no_body_optimizations&&!s->body&&!s->alternate){
                if(body_effect(s->expression))emit_discarded(s->expression);
                break;
            }
            if(!cg.function->uses_wide&&!cg.function->jump_label_count&&(return_shared_byte_index(s)||guarded_byte_store(s)||guarded_word_extreme(s)))break;
            if(!cg.function->jump_label_count&&s->expression->kind==EX_INT&&!wide_scalar(value_type(s->expression->type))&&!statement_has_case(s->body)&&!statement_has_case(s->alternate)){
                /* A literal condition emits only the arm that can run */
                Type t=s->expression->type;uint32_t v=s->expression->value;
                Statement *taken=(t.base==TY_FLOAT&&!t.pointers?(v&0x7fffffffu)!=0:v!=0)?s->body:s->alternate;
                if(taken&&!emit_statements(taken))return 0;
                break;
            }
            {unsigned available,body_available;
                body=++cg.label;end=++cg.label;step=++cg.label;branch(s->expression,body,step,body);
                available=cg.divmod_available;label(body);a=emit_statements(s->body);
                body_available=cg.divmod_available;if(a)jump(end);
                cg.divmod_available=available;label(step);b=s->alternate?emit_statements(s->alternate):1;label(end);
                if(!a&&!b)return 0;
                if(a&&b)cg.divmod_available&=body_available;
                else if(a)cg.divmod_available=body_available;
            }break;
        case ST_WHILE:case ST_FOR:case ST_DO:
            if(!cg.function->uses_wide)dot_emit_loop_setup(s);
            if(!(cg.function->uses_wide?emit_wide_loop(s):emit_loop_statement(s)))return 0;
            break;
        case ST_BREAK:case ST_CONTINUE:
            if(!cg.loop_count)error_at(s->location,"break/continue outside loop or switch");
            if(s->kind==ST_BREAK)jump(cg.loop_end[cg.loop_count-1]);
            else{
                unsigned context=cg.loop_count;
                while(context&&!cg.loop_start[context-1])--context;
                if(!context)error_at(s->location,"continue outside loop");
                jump(cg.loop_start[context-1]);
            }
            if(!cg.switch_depth)return 0;cg.divmod_available=0;break;
        }
    }
    return 1;
}
/* Emit one loop statement. Returns 0 when control cannot fall through */
/* A promoted region spans everything the loop statement emits: its
 * initializers and entry test as well, so every path to the end label,
 * including a zero-trip entry test, has copied the homes in. */
static int emit_loop_body(Statement *s);
static int bound_scan(void);
static int body_private(Symbol *v);
static int body_address_pure(Expr *e);
static int body_has_deref(Expr *e);
static Expr *guard_mismatch_call(Statement *body,Expr **comparison)
{
    Statement *guard=body_single(body),*failure;
    Expr *call;
    if(!guard||guard->next||guard->kind!=ST_IF||guard->alternate||
       !(*comparison=guard->expression)||(*comparison)->kind!=EX_BINARY||(*comparison)->op!=TOK_NE||
       !word_integer(common_type((*comparison)->left->type,(*comparison)->right->type)))return NULL;
    failure=body_single(guard->body);
    if(!failure||failure->next||failure->kind!=ST_EXPR||!(call=failure->expression)||
       call->kind!=EX_CALL||!call->symbol||call->arg_count)return NULL;
    return call;
}

/* Keep the counter and byte width across matching elements. Only the
 * mismatch edge crosses the calling convention and needs to save X. */
static int counted_indexed_guard_loop(Statement *s)
{
    DpCounter counter;
    IndexedOperand operand;
    Statement *init;
    Expr *assignment,*comparison,*load,*expected,*call;
    uint32_t first,end,value;
    unsigned scale,offset,loop,next,mismatch,done;
    int in,out;
    if(cg.parser->no_register_loops||cg.parser->no_register_cursors||cg.parser->no_loop_index_retention||
       cg.switch_depth||cg.bound||cg.bound_pending||cg.stack_leaf||cg.scalar_leaf||
       cg.retained_index||cg.retained_second||cg.scan_cursor||cg.affine_active||cg.lftr_active||
       cg.loop_y_borrowed||cg.function->symbol->interrupt||
       !dp_counter_ascending(s,NULL,&counter,s->expression&&s->expression->op==TOK_LE)||
       counter.wide||!integer_constant(counter.bound,&end))return 0;
    end+=counter.inclusive;
    init=body_single(s->initial);
    if(!init||init->next||init->kind!=ST_EXPR||!(assignment=init->expression)||
       assignment->kind!=EX_ASSIGN||assignment->op||assignment->left->kind!=EX_OBJECT||
       assignment->left->symbol!=counter.index||!integer_constant(assignment->right,&first)||
       first>=end||end>(counter.index->type.is_unsigned?65535u:32767u))return 0;
    if(!(call=guard_mismatch_call(s->body,&comparison)))return 0;
    load=comparison->left;expected=comparison->right;
    if(!integer_constant(expected,&value)){load=comparison->right;expected=comparison->left;}
    if(load->kind==EX_CAST&&word_integer(load->type)&&!load->type.is_unsigned&&
       !load->left->type.pointers&&load->left->type.base==TY_CHAR)load=load->left;
    if(load->type.pointers||load->type.base!=TY_CHAR||load->type.is_bool||
       !integer_constant(expected,&value)||value!=initializer_cast(value,load->type)||
       !indexed_operand(load,&operand)||operand.scale!=1||
       !retained_affine_for(operand.index,counter.index,&scale,&offset)||scale!=1||
       operand.offset+offset+end>width(operand.base->type))return 0;
    operand.offset+=offset;operand.reg='x';
    loop=++cg.label;next=++cg.label;mismatch=++cg.label;done=++cg.label;
    code("    ldx #$%04X\n    sep #$20\n.a8\n",(unsigned)first);
    label(loop);code("    lda ");indexed_text(&operand);code("\n");
    if(value)code("    cmp #$%02X\n",(unsigned)value&255);
    flag_branch("bne","beq",mismatch,0,0);
    label(next);code("    inx\n    cpx #$%04X\n",(unsigned)end);
    flag_branch("bne","beq",loop,0,0);code("    rep #$20\n.a16\n");
    region_home_liveness(cg.function,s,counter.index->offset,&in,&out);
    if(out){code("    txa\n");store_symbol(counter.index);strength_sync(counter.index,NULL);}
    jump(done);
    label(mismatch);code("    rep #$20\n.a16\n    phx\n");
    emit_discarded(call);code("    plx\n    sep #$20\n.a8\n");jump(next);
    code(".a16\n");label(done);cg.divmod_available=0;
    return 1;
}
/* The mismatch call is the only edge that can clobber the cursor registers.
 * Keep the full promoted comparison unless its constant fits in a byte. */
static int counted_pointer_guard_loop(Statement *s)
{
    Statement *init;
    Statement shape=*s;
    Expr *step=s->step,*test=s->expression,*comparison,*load,*expected,*call,*zero;
    Symbol *cursor;
    DpCounter counter;
    Type count_type;
    unsigned loop,match,done;
    uint32_t value;
    int literal,byte,in,out;
    if(cg.parser->no_register_loops||cg.parser->no_register_cursors||
       cg.switch_depth||cg.bound||cg.bound_pending||cg.stack_leaf||cg.scalar_leaf||
       cg.retained_index||cg.scan_cursor||cg.affine_active||cg.loop_y_borrowed||
       cg.function->symbol->interrupt||s->kind!=ST_FOR||!step||step->kind!=EX_COMMA||
       !test||volatile_statement(s))return 0;
    shape.step=step->left;
    if(!dp_counter_shape(&shape,NULL,&counter)){
        shape.step=step->right;
        if(!dp_counter_shape(&shape,NULL,&counter))return 0;
    }
    init=body_single(s->initial);
    if(!init||init->next||init->kind!=ST_EXPR||!(zero=init->expression)||
       zero->kind!=EX_ASSIGN||zero->op||zero->left->kind!=EX_OBJECT||
       zero->left->symbol!=counter.index||!integer_constant(zero->right,&value)||value)return 0;
    count_type=common_type(test->left->type,counter.bound->type);
    if(counter.wide||counter.index->type.is_bool||(!counter.index->type.is_unsigned&&count_type.is_unsigned&&
       (!integer_constant(counter.bound,&value)||value>32767)))return 0;
    if(!(call=guard_mismatch_call(s->body,&comparison)))return 0;
    load=comparison->left;expected=comparison->right;
    if(load->kind==EX_CAST&&load->type.base==TY_INT&&!load->type.is_unsigned)load=load->left;
    if(load->kind!=EX_DEREF){
        load=comparison->right;expected=comparison->left;
        if(load->kind==EX_CAST&&load->type.base==TY_INT&&!load->type.is_unsigned)load=load->left;
    }
    if(load->kind!=EX_DEREF||load->type.pointers||load->type.base!=TY_CHAR||load->type.is_bool||
       load->left->kind!=EX_OBJECT||far_pointer(load->left->type))return 0;
    cursor=load->left->symbol;
    if(!body_private(cursor)||body_step_direction(shape.step==step->left?step->right:step->left,cursor)!=1||
       increment_step(cursor->type)!=1)return 0;
    literal=integer_constant(expected,&value);
    if(!literal&&(expected->kind!=EX_OBJECT||!known_integer(expected->type)||
       !body_private(expected->symbol)||expected->symbol==counter.index))return 0;
    byte=literal&&(load->type.is_unsigned?value<=255:(int32_t)value>=-128&&(int32_t)value<=127);
    loop=++cg.label;match=++cg.label;done=++cg.label;
    emit_value(counter.bound);
    flag_branch("beq","bne",done,0,0);
    if(!count_type.is_unsigned)flag_branch("bmi","bpl",done,0,0);
    code("    phy\n    pha\n");
    if(!literal){emit_value(expected);code("    pha\n");}
    emit_value_x(load->left);
    code("    lda %u,s\n    tay\n",literal?1u:3u);
    if(byte)code("    sep #$20\n.a8\n");
    label(loop);
    code("    lda a:$0000,x\n");
    if(!byte)narrow_char(load->type);
    if(literal)code("    cmp #$%0*X\n",byte?2:4,value&(byte?255u:65535u));
    else code("    cmp 1,s\n");
    flag_branch("beq","bne",match,0,0);
    if(byte)code("    rep #$20\n.a16\n");
    code("    phx\n    phy\n");
    emit_discarded(call);
    code("    ply\n    plx\n");
    if(byte)code("    sep #$20\n.a8\n");
    label(match);
    code("    inx\n    dey\n");
    flag_branch("bne","beq",loop,0,0);
    if(byte)code("    rep #$20\n.a16\n");
    if(!literal)code("    pla\n");
    code("    pla\n    ply\n");
    region_home_liveness(cg.function,s,counter.index->offset,&in,&out);
    if(out)store_symbol(counter.index);
    region_home_liveness(cg.function,s,cursor->offset,&in,&out);
    if(out){code("    txa\n");store_symbol(cursor);}
    label(done);cg.divmod_available=0;
    return 1;
}
/* A private near cursor can stay in X while testing each element. A returning
 * call on a hit saves X; a return from the function uses the normal home.
 * Trial emission rejects predicates that need X for any other purpose. */
static int pointer_scan_loop(Statement *s)
{
    Expr *test=s->expression,*end,*advance;
    Statement *guard,*hit;
    Symbol *cursor;
    Codegen *saved;
    unsigned start,done,match,next,stride,in_range=0;
    int call_hit;
    if(cg.parser->no_register_loops||cg.parser->no_register_cursors||cg.switch_depth||
       cg.bound_pending||cg.bound||cg.scan_cursor||cg.scalar_leaf||
       (s->kind!=ST_WHILE&&s->kind!=ST_FOR)||!test||test->kind!=EX_BINARY||
       (test->op!=TOK_NE&&test->op!='<'&&test->op!=TOK_LE)||test->left->kind!=EX_OBJECT)return 0;
    cursor=test->left->symbol;end=test->right;
    if(!cursor->type.pointers||far_pointer(cursor->type)||!body_private(cursor)||
       end->kind!=EX_OBJECT||end->symbol==cursor||end->type.array||
       !end->type.pointers||far_pointer(end->type)||object_volatile(end->type)||
       (end->symbol->owner&&!compare_memory_operand(end,0)))return 0;
    guard=body_single(s->body);
    if(!guard||guard->kind!=ST_IF||guard->alternate||body_effect(guard->expression))return 0;
    if(s->kind==ST_FOR){if(guard->next)return 0;advance=s->step;}
    else{
        Statement *step=guard->next;
        if(!step||step->next||step->kind!=ST_EXPR)return 0;
        advance=step->expression;
    }
    if(!advance||body_step_direction(advance,cursor)!=1)return 0;
    hit=body_single(guard->body);
    call_hit=hit&&hit->kind==ST_EXPR&&!hit->next&&hit->expression&&hit->expression->kind==EX_CALL&&
        hit->expression->symbol&&!statement_references(guard->body,cursor);
    if(!call_hit){
        for(;hit&&hit->kind==ST_EXPR;hit=hit->next){}
        if(!hit||hit->kind!=ST_RETURN||hit->next)return 0;
    }
    stride=increment_step(cursor->type);
    if(!stride||stride>65535)return 0;

    saved=allocate(sizeof *saved);*saved=cg;
    start=++cg.label;done=++cg.label;match=++cg.label;next=++cg.label;
    if(test->op==TOK_LE)in_range=++cg.label;
    code("; register pointer scan\n");
    emit_value_x(test->left);label(start);
    if(end->symbol->owner||end->symbol->type.banked)code("    txa\n    cmp ");
    else code("    cpx ");
    array_operand(end->symbol,0);code("\n");
    if(in_range)code("    beq cg_%s_%u\n",cg.parser->unit,in_range);
    if(test->op==TOK_NE)flag_branch("beq","bne",done,0,0);
    else flag_branch("bcs","bcc",done,0,0);
    if(in_range)label(in_range);
    cg.divmod_available=0;
    cg.scan_cursor=cursor;cg.scan_failed=0;
    cg.bound_start=cg.length;cg.bound_mark_count=0;
    branch(guard->expression,match,next,next);
    cg.bound_end=cg.length;
    if(cg.scan_failed||!bound_scan()){
        char *assembly=cg.assembly;size_t capacity=cg.capacity;
        cg=*saved;cg.assembly=assembly;cg.capacity=capacity;cg.assembly[cg.length]=0;
        free(saved);return 0;
    }
    cg.scan_cursor=NULL;
    cg.bound_start=saved->bound_start;cg.bound_end=saved->bound_end;
    cg.bound_mark_count=saved->bound_mark_count;
    free(saved);
    label(next);
    if(stride<=3){unsigned i;for(i=0;i<stride;++i)code("    inx\n");}
    else code("    txa\n    clc\n    adc #$%04X\n    tax\n",stride);
    jump(start);
    label(match);cg.divmod_available=0;
    if(call_hit){
        code("    phx\n");if(cg.stack_leaf)cg.stack_bias+=2;
        emit_discarded(hit->expression);
        if(cg.stack_leaf)cg.stack_bias-=2;
        code("    plx\n");jump(next);
    }else{
        code("    txa\n");store_symbol(cursor);emit_statements(guard->body);
    }
    label(done);cg.divmod_available=0;code("    txa\n");store_symbol(cursor);
    return 1;
}
#include "index_retention.inc"
typedef struct {
    Symbol *index,*array;
    unsigned mask,updates,accesses;
} ScaledRing;
typedef struct {
    ScaledRing rings[4];
    unsigned count,edits,casts;
    Expr cast[16];
    struct { Expr *node,original,replacement; } edit[48];
} RingLoop;

static Expr *ring_step(Expr *e,Symbol **index,unsigned *mask)
{
    Expr *rhs,*step;
    uint32_t bits,one;
    if(!e||e->kind!=EX_ASSIGN||e->op||e->left->kind!=EX_OBJECT||
       e->left->type.base!=TY_INT||e->left->type.pointers||!e->left->type.is_unsigned||
       !body_private(e->left->symbol))return NULL;
    rhs=word_bits(e->right);
    if(rhs->kind!=EX_BINARY||rhs->op!='&'||!integer_constant(rhs->right,&bits)||
       !bits||bits>=0x8000||((bits+1)&bits))return NULL;
    step=word_bits(rhs->left);
    if(step->kind!=EX_BINARY||step->op!='+'||
       !lftr_object(word_bits(step->left),e->left->symbol)||
       !integer_constant(step->right,&one)||one!=1)return NULL;
    *index=e->left->symbol;*mask=(unsigned)bits;
    return rhs;
}

static ScaledRing *ring_find(RingLoop *p,Symbol *index)
{
    unsigned i;
    for(i=0;i<p->count;++i)if(p->rings[i].index==index)return &p->rings[i];
    return NULL;
}

static int ring_collect(RingLoop *p,Statement *s)
{
    for(;s;s=s->next){
        Symbol *index;unsigned mask;
        if(s->kind!=ST_BLOCK&&s->kind!=ST_EXPR&&s->kind!=ST_IF&&
           s->kind!=ST_EMPTY&&s->kind!=ST_BREAK&&s->kind!=ST_CONTINUE&&s->kind!=ST_RETURN)return 0;
        if(s->kind==ST_EXPR&&ring_step(s->expression,&index,&mask)){
            ScaledRing *r=ring_find(p,index);
            if(!r){
                if(p->count==sizeof p->rings/sizeof *p->rings)return 0;
                r=&p->rings[p->count++];r->index=index;r->mask=mask;
            }else if(r->mask!=mask)return 0;
        }
        if(!ring_collect(p,s->body)||!ring_collect(p,s->alternate))return 0;
    }
    return 1;
}

static int ring_edit(RingLoop *p,Expr *node,Expr replacement)
{
    unsigned i;
    for(i=0;i<p->edits;++i)if(p->edit[i].node==node)return 0;
    if(p->edits==sizeof p->edit/sizeof *p->edit)return 0;
    p->edit[i].node=node;p->edit[i].original=*node;p->edit[i].replacement=replacement;
    ++p->edits;
    return 1;
}

/* Only recurrence updates, equality between encoded indices, and indexed
 * accesses to fixed two-byte arrays observe the representation. A valid
 * subscript in those arrays has bit 15 clear. Rotating the word on entry
 * retains that bit for an equality check or an exit without an access. */
static int ring_uses(RingLoop *p,Expr *e,int discarded)
{
    ScaledRing *r;Symbol *index;unsigned mask,i;
    Expr *rhs,*a,*b;
    if(!e)return 1;
    if(discarded&&(rhs=ring_step(e,&index,&mask))!=NULL&&(r=ring_find(p,index))!=NULL){
        Expr *step=word_bits(rhs->left);
        Expr two=*step->right,scaled_mask=*rhs->right;
        if(two.kind!=EX_INT||scaled_mask.kind!=EX_INT)return 0;
        two.value=2;scaled_mask.value=mask*2;
        ++r->updates;
        return ring_edit(p,step->right,two)&&ring_edit(p,rhs->right,scaled_mask);
    }
    if(e->kind==EX_BINARY&&(e->op==TOK_EQ||e->op==TOK_NE)){
        a=word_bits(e->left);b=word_bits(e->right);
        if(a->kind==EX_OBJECT&&b->kind==EX_OBJECT&&ring_find(p,a->symbol)&&ring_find(p,b->symbol))return 1;
    }
    if(e->kind==EX_DEREF&&e->left->kind==EX_BINARY&&e->left->op=='+'){
        Expr *address=e->left,*base=address->left,*subscript=word_bits(address->right);
        if(subscript->kind==EX_OBJECT&&(r=ring_find(p,subscript->symbol))!=NULL){
            Expr byte_base={0},byte_address=*address;
            if(base->kind!=EX_OBJECT||!base->type.array||base->symbol->owner||
               !base->symbol->defined||base->symbol->dpage||base->type.banked||
               width(base->type)>65536||width(pointed_type(value_type(base->type)))!=2||
               width(e->type)!=2||width(base->type)<(r->mask+1)*2||
               (r->array&&r->array!=base->symbol))return 0;
            r->array=base->symbol;++r->accesses;
            byte_base.kind=EX_CAST;byte_base.type=type(TY_CHAR,1);
            byte_base.left=base;byte_base.location=base->location;
            if(p->casts==sizeof p->cast/sizeof *p->cast)return 0;
            p->cast[p->casts]=byte_base;
            byte_address.type=byte_base.type;
            byte_address.left=&p->cast[p->casts++];
            return ring_edit(p,address,byte_address);
        }
    }
    if(e->kind==EX_CALL||(e->kind==EX_OBJECT&&ring_find(p,e->symbol)))return 0;
    if(!ring_uses(p,e->left,0)||!ring_uses(p,e->right,0)||!ring_uses(p,e->third,0))return 0;
    for(i=0;i<e->arg_count;++i)if(!ring_uses(p,e->args[i],0))return 0;
    return 1;
}

static int ring_check_body(RingLoop *p,Statement *s)
{
    for(;s;s=s->next)
        if(!ring_uses(p,s->expression,s->kind==ST_EXPR)||
           !ring_check_body(p,s->body)||!ring_check_body(p,s->alternate))return 0;
    return 1;
}

static int ring_y_operand(Expr *e)
{
    unsigned i;
    if(!e)return 1;
    if(e->kind==EX_OBJECT&&e->symbol->owner&&
       (e->type.array||reg_width(e->type)>2||!guard_dp_home(e->symbol)))return 0;
    if(!ring_y_operand(e->left)||!ring_y_operand(e->right)||!ring_y_operand(e->third))return 0;
    for(i=0;i<e->arg_count;++i)if(!ring_y_operand(e->args[i]))return 0;
    return 1;
}

static int ring_y_region(Statement *s,unsigned *guards)
{
    for(;s;s=s->next){
        ByteGuard g;
        if(s->kind==ST_RETURN||!ring_y_operand(s->expression)||
           !ring_y_region(s->body,guards)||!ring_y_region(s->alternate,guards))return 0;
        if(byte_guard_plan(s,&g))++*guards;
    }
    return 1;
}

static int emit_scaled_ring_loop(Statement *s,int *result)
{
    RingLoop p={0};unsigned i,guards=0;int borrow_y;
    if(s->kind!=ST_DO||!cg.dp_homes||cg.parser->no_strength_reduction||
       cg.parser->no_indexed_operands||cg.bound||cg.affine_active||cg.retained_index||
       cg.loop_count||volatile_statement(s)||!ring_collect(&p,s->body)||!p.count||
       !ring_check_body(&p,s->body)||!ring_uses(&p,s->expression,0))return 0;
    for(i=0;i<p.count;++i){
        ScaledRing *r=&p.rings[i];unsigned offset=r->index->offset;
        if(!r->updates||!r->accesses||!offset||!(offset&1)||
           (offset-1)/2>=cg.dp_words||!cg.dp_map[(offset-1)/2])return 0;
    }
    for(i=0;i<p.edits;++i)*p.edit[i].node=p.edit[i].replacement;
    code("; scaled ring indices within loop\n");
    for(i=0;i<p.count;++i){
        load_symbol(p.rings[i].index);
        code("    asl a\n    adc #$0000\n");
        store_symbol(p.rings[i].index);
    }
    borrow_y=!cg.parser->no_register_cursors&&!cg.cursor_count&&ring_y_operand(s->expression)&&
        ring_y_region(s->body,&guards)&&guards>=2;
    if(borrow_y){code("    phy\n");cg.loop_y_borrowed=1;}
    *result=emit_loop_body(s);
    if(borrow_y){cg.loop_y_borrowed=0;code("    ply\n");}
    for(i=0;i<p.count;++i){
        load_symbol(p.rings[i].index);
        code("    lsr a\n    bcc :+\n    ora #$8000\n:\n");
        store_symbol(p.rings[i].index);
    }
    for(i=p.edits;i;--i)*p.edit[i-1].node=p.edit[i-1].original;
    return 1;
}

static int while_peel_cost(const Expr *e,int *budget)
{
    if(!e)return 1;
    if(--(*budget)<0||e->kind==EX_CALL||e->kind==EX_ASSIGN||
       e->kind==EX_PRE||e->kind==EX_POST||
       (e->type.base==TY_LONG&&!e->type.pointers)||
       e->type.base==TY_FLOAT||e->type.base==TY_DOUBLE)return 0;
    if(!while_peel_cost(e->left,budget)||!while_peel_cost(e->right,budget)||
       !while_peel_cost(e->third,budget))return 0;
    for(unsigned i=0;i<e->arg_count;++i)
        if(!while_peel_cost(e->args[i],budget))return 0;
    return 1;
}
static int while_peel_entry(Expr *e)
{
    int budget=16;
    return e&&!volatile_expression(e)&&while_peel_cost(e,&budget);
}
static int while_entry_true(Statement *previous,Expr *test)
{
    unsigned o1,o2;
    Symbol *s1,*s2;
    if(!previous||previous->kind!=ST_EXPR||!previous->expression||
       previous->expression->kind!=EX_ASSIGN||previous->expression->op||
       previous->expression->left->kind!=EX_OBJECT)return 0;
    if(!test||test->kind!=EX_BINARY||(test->op!=TOK_NE&&test->op!=TOK_EQ)||
       test->left->kind!=EX_OBJECT||
       test->left->symbol!=previous->expression->left->symbol)return 0;
    s1=near_object_address(previous->expression->right,&o1);
    s2=near_object_address(test->right,&o2);
    if(!s1||s1!=s2)return 0;
    return test->op==TOK_NE?(o1!=o2):(o1==o2);
}
static int emit_loop(Statement *s)
{
    int result;
    region_enter(s);
    if(emit_scaled_ring_loop(s,&result))code("; loop lowering: scaled ring indices\n");
    else result=emit_loop_body(s);
    region_exit(s);
    return result;
}
static int reduction_statements(Statement *s,Statement **out,unsigned *count,unsigned limit);
static int reduction_object(Expr *e,Symbol *s);
static int reduction_zero(Expr *e);
typedef struct {
    Expr *word,*count;
    Symbol *home;
    unsigned mask,shift,offset;
    int op,direction,while_zero,byte;
} WordShiftScan;

static int word_shift_scan_plan(Statement *s,WordShiftScan *scan)
{
    Statement *parts[2];
    Expr *test=s->expression,*update,*step,*value;
    uint32_t mask,shift;
    unsigned n=0;
    int direction;
    if(cg.parser->no_strength_reduction||cg.parser->no_register_cursors||
       cg.parser->no_body_optimizations||s->kind!=ST_WHILE||!test||
       volatile_statement(s)||!reduction_statements(s->body,parts,&n,2)||n!=2||
       parts[0]->kind!=ST_EXPR||parts[1]->kind!=ST_EXPR)return 0;
    update=parts[0]->expression;step=parts[1]->expression;
    if(update->kind!=EX_ASSIGN||(update->op!=TOK_SHR&&update->op!=TOK_SHL)){
        update=parts[1]->expression;step=parts[0]->expression;
    }
    if(update->kind!=EX_ASSIGN||(update->op!=TOK_SHR&&update->op!=TOK_SHL)||
       !integer_constant(update->right,&shift)||!shift||shift>4||
       !step->left||step->left->kind!=EX_OBJECT||!word_integer(step->left->type)||
       !(direction=body_step_direction(step,step->left->symbol)))return 0;
    scan->while_zero=0;
    if(test->kind==EX_UNARY&&test->op=='!'){test=test->left;scan->while_zero=1;}
    else if(test->kind==EX_BINARY&&(test->op==TOK_EQ||test->op==TOK_NE)){
        scan->while_zero=test->op==TOK_EQ;
        if(reduction_zero(test->right))test=test->left;
        else if(reduction_zero(test->left))test=test->right;
        else return 0;
    }
    if(test->kind!=EX_BINARY||test->op!='&'||reg_width(test->type)!=2)return 0;
    value=test->left;
    if(!integer_constant(test->right,&mask)){
        if(!integer_constant(test->left,&mask))return 0;
        value=test->right;
    }
    if(!body_equal(word_uncast(word_bits(value)),update->left)||
       !compare_memory_operand(step->left,0)||!(mask&65535))return 0;
    scan->byte=update->left->type.base==TY_CHAR;
    if(scan->byte){
        if((mask&65535)>255||
           !(scan->home=fixed_byte_home(update->left,0,&scan->offset))||scan->home->type.banked)return 0;
    }else if(!word_integer(update->left->type)||!compare_memory_operand(update->left,0)||
             !(scan->home=direct_memory_object(update->left,&scan->offset)))return 0;
    if(scan->home==step->left->symbol)return 0;
    scan->word=update->left;scan->count=step->left;
    scan->mask=mask&65535;scan->shift=shift;scan->op=update->op;scan->direction=direction;
    return 1;
}

static void emit_word_shift_scan(WordShiftScan *scan)
{
    unsigned start=++cg.label,done=++cg.label;
    code(scan->byte?"    bit #$%02X\n":"    bit #$%04X\n",scan->mask);
    flag_branch(scan->while_zero?"bne":"beq",scan->while_zero?"beq":"bne",done,0,0);
    label(start);
    for(unsigned i=0;i<scan->shift;++i){
        if(scan->op==TOK_SHL)code("    asl a\n");
        else if(scan->word->type.is_unsigned)code("    lsr a\n");
        else code(scan->byte?"    cmp #$80\n    ror a\n":"    cmp #$8000\n    ror a\n");
    }
    code("    %s\n",scan->direction>0?"inx":"dex");
    code(scan->byte?"    bit #$%02X\n":"    bit #$%04X\n",scan->mask);
    flag_branch(scan->while_zero?"beq":"bne",scan->while_zero?"bne":"beq",start,done,done);
    label(done);
    cg.divmod_available=0;
}

static int word_shift_scan_loop(Statement *s)
{
    WordShiftScan scan;
    if(cg.switch_depth||cg.retained_index||cg.retained_second||cg.affine_active||
       cg.scan_cursor||cg.bound||cg.bound_pending||cg.numeric_index||cg.lftr_active||
       !word_shift_scan_plan(s,&scan))return 0;
    code("; register word shift scan\n");
    emit_value_x(scan.count);
    if(scan.byte)code("    sep #$20\n.a8\n");
    code("    lda ");array_operand(scan.home,scan.offset);code("\n");
    emit_word_shift_scan(&scan);
    code("    sta ");array_operand(scan.home,scan.offset);code("\n");
    if(scan.byte)code("    rep #$20\n.a16\n");
    code("    txa\n");
    store_symbol(scan.count->symbol);
    return 1;
}

static int word_shift_scan_leaf(Function *f)
{
    WordShiftScan scan;
    Statement *parts[4];
    Symbol *arg,*count;
    Expr *word_init,*count_init,*seed;
    uint32_t initial;
    unsigned n=0;
    if(f->symbol->param_count!=1||!word_integer(f->symbol->type)||
       !reduction_statements(f->body,parts,&n,4)||n!=4||
       parts[0]->kind!=ST_EXPR||parts[1]->kind!=ST_EXPR||
       parts[3]->kind!=ST_RETURN||!word_shift_scan_plan(parts[2],&scan))return 0;
    count=scan.count->symbol;arg=leaf_parameter(f,0);
    word_init=parts[0]->expression;count_init=parts[1]->expression;
    if(word_init->kind!=EX_ASSIGN||word_init->op||count_init->kind!=EX_ASSIGN||count_init->op)return 0;
    if(reduction_object(word_init->left,count)){
        Expr *swap=word_init;word_init=count_init;count_init=swap;
    }
    seed=word_bits(word_init->right);
    if(scan.byte&&seed->kind==EX_CAST&&seed->type.base==TY_CHAR&&!seed->type.is_bool&&
       !seed->type.pointers)seed=word_bits(seed->left);
    if(!arg||arg==count||!word_integer(arg->type)||!register_parameter(0,arg->type)||
       !body_private(count)||scan.home->owner!=f->id||loop_escapes(f->body,scan.home)||
       !body_equal(word_init->left,scan.word)||!reduction_object(seed,arg)||
       !reduction_object(count_init->left,count)||!integer_constant(count_init->right,&initial)||
       !reduction_object(word_bits(parts[3]->expression),count))return 0;
    code(".segment \"CODE\"\n.export _%s\n_%s:\n; frameless word shift scan\n    txa\n    ldx #$%04X\n",
         f->symbol->asm_name,f->symbol->asm_name,initial&65535);
    if(scan.byte)code("    sep #$20\n.a8\n");
    emit_word_shift_scan(&scan);
    if(scan.byte)code("    rep #$20\n.a16\n");
    code("    txa\n    rts\n__size_%s = * - _%s\n",f->symbol->asm_name,f->symbol->asm_name);
    f->frame=0;return 1;
}

/* An unobserved fixed-word shift recurrence and its termination counter
 * can live in A and X for the whole loop. Publish both final values. */
static int fixed_shift_loop(Statement *s)
{
    Statement *body=s->body;
    Expr *test=s->expression,*update,*step,*value,*operand,*literal;
    Symbol *data,*counter;
    uint32_t shift,limit;
    unsigned at=0,index=0,again,done,i;
    if(cg.parser->no_register_cursors||cg.parser->no_strength_reduction||cg.switch_depth||
       cg.retained_index||cg.retained_second||cg.affine_active||cg.scan_cursor||s->kind!=ST_DO||
       !test||test->kind!=EX_BINARY||test->op!=TOK_NE||volatile_expression(test))return 0;
    operand=test->left;literal=test->right;
    if(!integer_constant(literal,&limit)){
        if(!integer_constant(operand,&limit))return 0;
        operand=test->right;literal=test->left;
    }
    while(body&&body->kind==ST_BLOCK&&!body->next&&!body->inline_callee)body=body->body;
    if(!body||body->kind!=ST_EXPR||body->inline_callee)return 0;
    step=operand;
    if(body->next){
        Statement *tail=body->next;
        if(tail->kind!=ST_EXPR||tail->next||tail->inline_callee)return 0;
        step=tail->expression;
        if(!step||(step->kind!=EX_PRE&&step->kind!=EX_POST)||
           !body_equal(step->left,operand)||volatile_expression(step))return 0;
    }else if(step->kind!=EX_PRE)return 0;
    if((step->op!=TOK_INC&&step->op!=TOK_DEC)||width(step->type)!=2||
       step->type.base!=TY_INT||step->type.pointers)return 0;
    update=body->expression;
    if(!update||update->kind!=EX_ASSIGN||(update->op!=TOK_SHR&&update->op!=TOK_SHL)||
       !integer_constant(update->right,&shift)||!shift||shift>4||volatile_expression(update))return 0;
    value=update->left;
    if(width(value->type)!=2||value->type.base!=TY_INT||value->type.pointers||!value->type.is_unsigned)return 0;
    data=value->kind==EX_OBJECT?value->symbol:fixed_memory_object(value,&at);
    counter=step->left->kind==EX_OBJECT?step->left->symbol:fixed_memory_object(step->left,&index);
    if(!data||!counter||data->owner||counter->owner||data->type.banked||counter->type.banked||
       (data==counter&&at<index+2&&index<at+2)||reg_width(common_type(operand->type,literal->type))!=2)return 0;
    again=++cg.label;done=++cg.label;
    code("; register-resident fixed word shift loop\n    lda ");array_operand(data,at);
    code("\n    ldx ");array_operand(counter,index);code("\n");
    label(again);
    for(i=0;i<shift;++i)code("    %s a\n",update->op==TOK_SHR?"lsr":"asl");
    code("    %s\n    cpx #$%04X\n",step->op==TOK_INC?"inx":"dex",limit&65535);
    flag_branch("bne","beq",again,done,done);label(done);
    code("    sta ");array_operand(data,at);code("\n    stx ");array_operand(counter,index);code("\n");
    cg.divmod_available=0;
    return 1;
}
static int empty_loop_body(Statement *s)
{
    for(;s;s=s->next){
        if(s->kind==ST_EMPTY)continue;
        if(s->kind==ST_CONTINUE&&!s->next)return 1;
        if(s->kind==ST_IF){
            Expr *test=s->expression;
            if(test->kind!=EX_BINARY||!comparison(test->op)||test->left->kind!=EX_OBJECT||
               !known_integer(test->left->type)||test->right->kind!=EX_INT||!known_integer(test->right->type)||
               volatile_expression(test)||!empty_loop_body(s->body)||!empty_loop_body(s->alternate))return 0;
            continue;
        }
        if(s->kind!=ST_BLOCK||!empty_loop_body(s->body))return 0;
    }
    return 1;
}
static int fold_fixed_update_loop(Statement *s)
{
    Statement *initial=body_single(s->initial),*body=body_single(s->body);
    Expr *test=s->expression,*step=s->step,*init,*update;
    unsigned off,init_off,step_off,update_off,width_bits;
    uint32_t begin,end,delta=1,limit;
    int op;
    Symbol *index,*value;
    if(cg.parser->no_strength_reduction||cg.parser->no_loop_unroll||cg.function->jump_label_count||
       s->kind!=ST_FOR||!initial||initial->kind!=ST_EXPR||initial->next||
       !step||!test||
       test->kind!=EX_BINARY||test->op!='<'||
       (step->kind!=EX_PRE&&step->kind!=EX_POST)||step->op!=TOK_INC||
       !word_integer(test->left->type)||width(test->left->type)!=2||volatile_statement(s))return 0;
    init=initial->expression;
    if(!init||init->kind!=EX_ASSIGN||init->op||
       !(index=fixed_byte_home(test->left,0,&off))||
       fixed_byte_home(init->left,0,&init_off)!=index||init_off!=off||
       fixed_byte_home(step->left,0,&step_off)!=index||step_off!=off||
       !same_type(test->left->type,init->left->type)||!same_type(test->left->type,step->left->type)||
       !integer_constant(init->right,&begin)||!integer_constant(test->right,&end))return 0;
    limit=test->left->type.is_unsigned?65535u:32767u;
    if(begin>=end||end-begin<2||end>limit)return 0;
    if(!empty_loop_body(s->body)){
        if(!body||body->kind!=ST_EXPR||body->next||!(update=body->expression))return 0;
        if(update->kind==EX_PRE||update->kind==EX_POST)op=update->op==TOK_INC?'+':'-';
        else if(update->kind==EX_ASSIGN&&(update->op=='+'||update->op=='-')&&
                integer_constant(update->right,&delta))op=update->op;
        else return 0;
        if(!known_integer(update->type)||!update->type.is_unsigned||update->type.is_bool||
           !(value=fixed_byte_home(update->left,0,&update_off))||value==index)return 0;
        width_bits=width(update->type)*8;
        delta=(delta*(end-begin))&((1u<<width_bits)-1);
        if(delta){
            if(width_bits==8)code("    sep #$20\n.a8\n");
            code("    lda ");array_operand(value,update_off);
            code("\n    %s\n    %s ",op=='+'?"clc":"sec",op=='+'?"adc":"sbc");
            code(width_bits==8?"#$%02X\n":"#$%04X\n",delta);
            code("    sta ");array_operand(value,update_off);code("\n");
            if(width_bits==8)code("    rep #$20\n.a16\n");
        }
    }
    code("    lda #$%04X\n    sta ",end);array_operand(index,off);code("\n");
    cg.divmod_available=0;
    return 1;
}
static int emit_loop_body(Statement *s)
{
    unsigned start,end,body,step;int a,infinite,counted,rotated_while;DpCounter counter={0};unsigned done;AffineLoop *affine,*saved_affine;
    Statement *previous=loop_previous;
    if(fold_fixed_update_loop(s)){code("; loop lowering: folded fixed update\n");return 1;}
    if(unroll_far_doubling_sum(s)){code("; loop lowering: unrolled far doubling sum\n");return 1;}
    if(far_sentinel_doubling_loop(s)){code("; loop lowering: far sentinel doubling sum\n");return 1;}
    affine=cg.switch_depth?NULL:affine_find(s);
    if(!cg.function->jump_label_count&&!affine&&counted_indexed_guard_loop(s)){code("; loop lowering: counted indexed byte guard\n");return 1;}
    if(!affine&&!cg.switch_depth&&s->kind==ST_FOR&&s->initial&&!s->initial->next&&s->initial->kind==ST_EXPR&&
       retained_countdown_for_loop(s,1)){code("; loop lowering: register countdown\n");return 1;}
    if(affine&&affine->dead_index){
        code("; eliminated induction home: %s\n",affine->index->name);
        affine_initialize_dead_index(affine);
    }else if(s->initial)emit_statements(s->initial);
    if(fixed_byte_copy_loop(s)){code("; loop lowering: fixed byte copy\n");return 1;}
    if(affine_pair_loop(s)){code("; loop lowering: paired affine stores\n");return 1;}
    if(!cg.switch_depth&&affine_register_loop(s,affine)){
        code("; loop lowering: %s register cursor\n",affine?"affine":"explicit");
        return 1;
    }
    if(!cg.function->jump_label_count&&fixed_shift_loop(s)){code("; loop lowering: fixed word shift\n");return 1;}
    if(!cg.function->jump_label_count&&word_shift_scan_loop(s)){code("; loop lowering: word shift scan\n");return 1;}
    if(!cg.switch_depth&&!volatile_statement(s)&&register_loop(s)){code("; loop lowering: register loop\n");return 1;}
    if(!affine&&retained_countdown_loop(s)){code("; loop lowering: register countdown\n");return 1;}
    if(!cg.function->jump_label_count&&!affine&&counted_pointer_guard_loop(s)){code("; loop lowering: counted pointer guard\n");return 1;}
    if(!cg.function->jump_label_count&&!affine&&pointer_scan_loop(s)){code("; loop lowering: register pointer scan\n");return 1;}
    if(!cg.switch_depth&&numeric_loop(s)){code("; loop lowering: numeric loop\n");return 1;}
    if(structured_byte_loop(s)){code("; loop lowering: structured byte loop\n");return 1;}
    if(!(affine&&affine->dead_index)&&retained_loop(s)){code("; loop lowering: retained index\n");return 1;}
    if(!affine&&dp_counter_word_fill(s)){code("; loop lowering: fixed-array DP word fill\n");return 1;}
    if(!cg.switch_depth&&s->kind!=ST_DO&&s->expression&&s->expression->kind==EX_INT&&!s->expression->value){code("; loop lowering: zero-trip elimination\n");return 1;}
    counted=(!cg.switch_depth||(cg.switch_depth==1&&cg.function->jump_label_count&&
             !dp_counter_has_jump_edge(s->initial)&&!dp_counter_has_jump_edge(s->body)))&&
            !volatile_statement(s)&&dp_counter_plan(s,affine,&counter);
    rotated_while=!counted&&!affine&&s->kind==ST_WHILE&&s->expression&&
        s->expression->kind!=EX_INT&&!divmod_test_produces(s->expression);
    code("; loop lowering: %s\n",counted?(affine?"affine cursor and DP counter":"DP counter"):
         affine?"affine frame cursor":cg.bound_pending?"bound register cursor":"generic fallback");
    start=++cg.label;body=++cg.label;end=++cg.label;done=counted?++cg.label:end;step=s->kind==ST_WHILE?start:++cg.label;
    if(cg.loop_count==64)error_at(s->location,"too many nested loops");
    cg.loop_start[cg.loop_count]=step;cg.loop_end[cg.loop_count++]=end;
    if(counted){
        if(!counter.countdown){
            unsigned enter=++cg.label;
            Expr entry=*s->expression,zero={0};
            counter.starts_zero=!affine&&dp_counter_starts_zero(s,&counter,previous);
            if(counter.starts_zero){
                zero.kind=EX_INT;zero.type=counter.index->type;zero.location=entry.location;
                entry.left=&zero;
                if(counter.bound->kind==EX_INT){
                    entry.value=initializer_constant(&entry,1);
                    entry.kind=EX_INT;
                }
            }
            if(counter.starts_zero&&counter.bound->kind!=EX_INT&&!body_effect(counter.bound)&&!counter.wide){
                /* The successful entry test already leaves the trip count in A */
                Type compare=common_type(entry.left->type,counter.bound->type);
                truth(counter.bound);
                flag_branch("beq","bne",done,0,0);
                if(!compare.is_unsigned)flag_branch("bmi","bpl",done,0,0);
                counter.bound_loaded=1;
            }else branch(&entry,enter,done,enter);
            label(enter);
        }else if(counter.entry_test){
            unsigned enter=++cg.label;
            branch(s->expression,enter,done,enter);
            label(enter);
        }
        if(affine)affine_initialize(affine);
        dp_counter_enter(&counter);bound_enter();
        if(!counter.countdown||counter.entry_test)jump(body);
    }else if(affine){
        unsigned enter=++cg.label;
        branch(s->expression,enter,end,enter);label(enter);affine_initialize(affine);bound_enter();jump(body);
    }
    if(!counted&&!affine)bound_enter();
    cg.divmod_available=0;
    if(rotated_while){
        if(!while_entry_true(previous,s->expression)){
            if(while_peel_entry(s->expression)){
                branch(s->expression,body,end,body);
                cg.divmod_available=0;
            }else jump(start);
        }
    }else{
        label(start);
        if(!counted){
            if(s->kind!=ST_DO&&s->expression&&s->expression->kind!=EX_INT)branch(s->expression,body,end,body);
            else if(s->kind!=ST_DO&&s->expression&&!s->expression->value)jump(end);
        }
    }
    label(body);
    saved_affine=cg.affine_active;
    if(affine)cg.affine_active=affine;
    a=emit_statements(s->body);
    if(s->kind!=ST_WHILE){cg.divmod_available=0;label(step);}
    if(s->step){
        if(counted&&!counter.update_index){
            strength_update_cursors_only(s->step);
        }else if(!strength_update(s->step,0)){
            if(scalar_home_update(s->step,0)||(!volatile_expression(s->step)&&discarded_far_update(s->step)))divmod_written(s->step->left);else emit_discarded(s->step);
        }
    }
    if(affine)affine_advance(affine);
    cg.affine_active=saved_affine;
    if(counted){
        if(!affine&&!counter.countdown&&!counter.descending&&!counter.wide&&
           !counter.recover_index&&s->expression->left->type.is_unsigned&&
           !cg.parser->no_line_passes&&!cg.parser->no_index_elimination&&
           !cg.function->jump_label_count&&dp_counter_word_prefix(s->body,counter.index))
            code("; word-array loop distance fits 32768\n");
        dp_counter_step(&counter,body);
    }
    else if(s->kind==ST_DO)branch(s->expression,start,end,end);
    else if(rotated_while){
        cg.divmod_available=0;label(start);branch(s->expression,body,end,end);
    }else if(a||s->kind==ST_FOR)jump(start);
    --cg.loop_count;cg.divmod_available=0;label(end);bound_exit();
    if(counted){dp_counter_exit(&counter);label(done);}
    infinite=s->kind!=ST_DO&&(!s->expression||(s->expression->kind==EX_INT&&s->expression->value));
    if(infinite&&!contains_break(s->body)&&!cg.switch_depth)return 0;
    return 1;
}
#include "bound_cursors.inc"
#include "region_homes.inc"
/* A leading scalar guard can return without ever allocating a frame. Limit
 * inputs to one word parameter in X and a constant so the continuation keeps
 * all incoming arguments intact and no local initializer is bypassed. */
static void entry_guard(Function *f,Statement **body)
{
    Statement *s=*body,*ret;Expr *e,*value;Symbol *parameter;unsigned yes,no;
    if(f->symbol->param_count!=1||f->symbol->params[0].base!=TY_INT||
       f->symbol->params[0].pointers||f->symbol->type.base!=TY_INT||f->symbol->type.pointers)return;
    while(s&&(s->kind==ST_EMPTY||(s->kind==ST_BLOCK&&!s->body)))s=s->next;
    if(!s||s->kind!=ST_IF||s->alternate||!word_comparison(s->expression))return;
    e=s->expression;parameter=leaf_parameter(f,0);
    if(e->left->kind!=EX_OBJECT||e->left->symbol!=parameter||e->right->kind!=EX_INT)return;
    ret=s->body;
    if(ret&&ret->kind==ST_BLOCK)ret=ret->body;
    if(!ret||ret->next||ret->kind!=ST_RETURN||!ret->expression)return;
    value=ret->expression;
    if(value->kind!=EX_INT&&(value->kind!=EX_OBJECT||value->symbol!=parameter))return;
    if(reg_width(value->type)!=2)return;
    yes=++cg.label;no=++cg.label;
    code("; entry guard before frame allocation\n    txa\n");
    word_compare_loaded(e,yes,no,yes);label(yes);
    if(value->kind==EX_INT)emit_value(value);else code("    txa\n");
    code("    rts\n");label(no);*body=s->next;
}
#include "counted_reductions.inc"
#include "bank_calls.inc"
#include "guarded_updates.inc"
#include "range_scans.inc"
/* Inspect complete emitted instructions, including operands assembled through
 * multiple code() calls. This covers selected inline paths and frame cleanup,
 * rather than predicting scratch use from the unselected expression tree. */
static unsigned interrupt_scratch_writes(size_t start)
{
    const char *line=cg.assembly+start;unsigned mask=cg.interrupt_scratch;
    while(*line){
        char op[16],operand[192];const char *end=strchr(line,'\n');
        if(sscanf(line," %15s %191[^\r\n]",op,operand)==2&&
           (!strcmp(op,"sta")||!strcmp(op,"stx")||!strcmp(op,"sty")||!strcmp(op,"stz")||
            !strcmp(op,"inc")||!strcmp(op,"dec")||!strcmp(op,"asl")||!strcmp(op,"lsr")||
            !strcmp(op,"rol")||!strcmp(op,"ror")||!strcmp(op,"trb")||!strcmp(op,"tsb"))){
            char *comment=strchr(operand,';'),*symbol;
            if(comment)*comment=0;
            symbol=operand;
            if(!strncmp(symbol,"z:",2)||!strncmp(symbol,"a:",2)||!strncmp(symbol,"f:",2))symbol+=2;
            if(strncmp(symbol,"__arith_",8))symbol=NULL;
            if(symbol){
                char *suffix;unsigned base,offset=0;
                if(!strncmp(symbol,"__arith_lhs",11))base=0;
                else if(!strncmp(symbol,"__arith_rhs",11))base=4;
                else error_at(here(cg.parser),"unknown interrupt scratch operand '%s'",operand);
                suffix=symbol+11;
                if(*suffix=='+'){
                    char *next;unsigned long n;int radix=10;
                    ++suffix;if(*suffix=='$'){++suffix;radix=16;}
                    n=strtoul(suffix,&next,radix);
                    if(next==suffix||n>30)error_at(here(cg.parser),"invalid interrupt scratch offset");
                    offset=(unsigned)n;suffix=next;
                }
                while(isspace((unsigned char)*suffix))++suffix;
                if((*suffix&&*suffix!=';')||base+offset>30)
                    error_at(here(cg.parser),"unsupported interrupt scratch addressing '%s'",operand);
                /* Scratch instructions use 16-bit A/X/Y. Include both words
                 * if a future unaligned access straddles a word boundary. */
                mask|=(1u<<((base+offset)/2))|(1u<<((base+offset+1)/2));
            }
        }
        if(!end)break;line=end+1;
    }
    return mask;
}
static void insert_interrupt_scratch(size_t start,size_t save,size_t restore)
{
    unsigned mask=interrupt_scratch_writes(start);int word;
    size_t size=cg.length-save,middle=restore-save;char *tail;
    if(!mask)return;
    tail=allocate(size+1);memcpy(tail,cg.assembly+save,size+1);
    cg.length=save;cg.assembly[save]=0;
    for(word=0;word<16;++word)if(mask&(1u<<word))code("    pei ($%02X)\n",DP_SCRATCH_BASE+word*2);
    code("%.*s",(int)middle,tail);
    for(word=15;word>=0;--word)if(mask&(1u<<word))code("    pla\n    sta z:$%02X\n",DP_SCRATCH_BASE+word*2);
    code("%s",tail+middle);free(tail);
}
static unsigned stack_reservation_offset(unsigned offset,unsigned *holes,unsigned *bytes,unsigned count)
{
    unsigned i,result=offset;
    for(i=0;i<count;++i)if(holes[i]<offset)result-=bytes[i];
    return result;
}
/* Specialized leaves have already selected their independent ABI lowering.
 * Ordinary entry-cursor dependencies must be included before omitting an
 * incoming register value, even if the body overwrites it before any C read. */
static int parameter_entry_cursor(Symbol *v)
{
    unsigned i;
    for(i=0;i<cg.cursor_count;++i){
        InductionCursor *c=&cg.cursors[i];
        if(!c->index->scope&&parameter_incoming_live(c->index)&&(c->base==v||c->index==v))return 1;
    }
    return 0;
}
/* Backward may-liveness of a scalar value. A full plain write kills it;
 * reads and address formation generate it. Expression sequencing beyond such
 * writes remains conservative. Escapes after a definite write need a home,
 * but do not require the old incoming contents in that home. */
static int scalar_live_expr(Expr *e,Symbol *v,int after)
{
    if(!e)return after;
    if(e->kind==EX_ASSIGN&&!e->op&&e->left->kind==EX_OBJECT&&e->left->symbol==v)
        return loop_mentions(e->right,v);
    return after||loop_mentions(e,v);
}
static unsigned scalar_live_budget;
static Statement *scalar_live_target;
static int scalar_live_captured,scalar_live_after;
static int body_private(Symbol *v);
static int body_address_pure(Expr *e);
static int body_has_deref(Expr *e);
static void body_drop_expr(Expr **at,Symbol *v);
static int scalar_live_statements(Statement *s,Symbol *v,int after,int breaking,int continuing,int rewrite)
{
    int next,head,body,step,again;
    if(!s)return after;
    if(!scalar_live_budget)return 1;
    --scalar_live_budget;
    next=scalar_live_statements(s->next,v,after,breaking,continuing,rewrite);
    if(s==scalar_live_target){scalar_live_captured=1;scalar_live_after|=next;}
    switch(s->kind){
    case ST_SWITCH:case ST_CASE:return 1; /* Multiple entry labels: keep the input */
    case ST_EMPTY:return next;
    case ST_EXPR:
        if(rewrite&&!next){
            body_drop_expr(&s->expression,v);
            if(!s->expression)s->kind=ST_EMPTY;
        }
        return scalar_live_expr(s->expression,v,next);
    case ST_RETURN:return scalar_live_expr(s->expression,v,0);
    case ST_BREAK:return breaking;
    case ST_CONTINUE:return continuing;
    case ST_BLOCK:return scalar_live_statements(s->body,v,next,breaking,continuing,rewrite);
    case ST_IF:
        body=scalar_live_statements(s->body,v,next,breaking,continuing,rewrite);
        step=scalar_live_statements(s->alternate,v,next,breaking,continuing,rewrite);
        return scalar_live_expr(s->expression,v,body||step);
    case ST_WHILE:case ST_FOR:case ST_DO:
        head=0;
        do{
            again=head;
            if(s->kind==ST_DO){
                step=scalar_live_expr(s->expression,v,next||head);
                body=scalar_live_statements(s->body,v,step,next,step,0);
                head=body;
            }else{
                step=scalar_live_expr(s->step,v,head);
                body=scalar_live_statements(s->body,v,step,next,step,0);
                head=scalar_live_expr(s->expression,v,next||body);
            }
        }while(head!=again);
        if(rewrite&&scalar_live_budget){
            if(s->kind==ST_DO)step=scalar_live_expr(s->expression,v,next||head);
            else{
                if(!head)body_drop_expr(&s->step,v);
                step=scalar_live_expr(s->step,v,head);
            }
            scalar_live_statements(s->body,v,step,next,step,1);
        }
        return scalar_live_statements(s->initial,v,head,breaking,continuing,rewrite);
    }
    return 1;
}

/* Capture a private scalar's loop continuation during backward may-liveness,
 * including enclosing loop backedges and break/continue paths. */
static int dot_reserved_symbol(const Symbol *v);
static void region_home_liveness(Function *f,Statement *s,unsigned offset,int *in,int *out)
{
    unsigned i;Symbol *v=NULL;Statement single=*s;
    *in=*out=1;
    if(cg.parser->no_private_regions||cg.parser->no_body_optimizations)return;
    for(i=0;i<cg.parser->symbol_count;++i){Symbol *candidate=&cg.parser->symbols[i];
        if(candidate->owner==f->id&&loop_private(candidate)&&!object_volatile(candidate->type)&&
           !structure_object(candidate->type)&&!candidate->type.array&&width(candidate->type)<=4&&
           (candidate->offset==offset||(reg_width(candidate->type)==4&&candidate->offset+2==offset))){v=candidate;break;}
    }
    if(!v||dot_reserved_symbol(v))return;
    scalar_live_target=s;scalar_live_after=scalar_live_captured=0;scalar_live_budget=100000;
    scalar_live_statements(f->body,v,0,1,1,0);
    scalar_live_target=NULL;
    if(!scalar_live_captured||!scalar_live_budget)return;
    *out=scalar_live_after;
    single.next=NULL;scalar_live_budget=100000;
    *in=scalar_live_statements(&single,v,*out,1,1,0);
}
static int parameter_incoming_live(Symbol *v)
{
    scalar_live_budget=4096;
    return scalar_live_statements(cg.function->body,v,0,1,1,0);
}
static unsigned plan_register_homes(Function *f)
{
    unsigned i,possible=0;cg.register_homes=cg.register_spills=0;
    for(i=0;i<(unsigned)(f->symbol->param_count<0?0:f->symbol->param_count);++i){
        Symbol *v=leaf_parameter(f,i);int cursor;
        if(!v)error_at(here(cg.parser),"internal parameter layout failure");
        if(!register_parameter(i,v->type))continue;
        possible|=1u<<i;cursor=parameter_entry_cursor(v);
        if(f->jump_label_count||object_volatile(v->type)){cg.register_homes|=1u<<i;cg.register_spills|=1u<<i;continue;}
        if(!statement_references(f->body,v)&&!cursor)continue;
        cg.register_homes|=1u<<i;
        if(cursor||parameter_incoming_live(v))
            cg.register_spills|=1u<<i;
    }
    return possible;
}
static unsigned compact_parameter_reservations(Function *f)
{
    /* Stack arguments retain their incoming homes. Unreferenced register
     * parameters need no storage; written/read parameters retain their homes. */
    Symbol *parameters[MAX_PARAMETERS];unsigned holes[MAX_PARAMETERS],bytes[MAX_PARAMETERS],count=0,total=0,stacked=0,i,j;
    for(i=0;i<(unsigned)(f->symbol->param_count<0?0:f->symbol->param_count);++i){
        Symbol *v=leaf_parameter(f,i);
        if(!v)error_at(here(cg.parser),"internal parameter layout failure");
        if(register_parameter(i,v->type)){
            if(cg.register_homes&(1u<<i))continue;
            cg.omitted_parameters[cg.omitted_parameter_count++]=v;
        }else ++stacked;
        parameters[count]=v;holes[count]=v->offset;bytes[count]=(width(v->type)+1)&~1u;
        total+=bytes[count++];
    }
    if(!count)return 0;
    for(i=0;i<cg.parser->symbol_count;++i){
        Symbol *v=&cg.parser->symbols[i];
        if(v->owner!=f->id)continue;
        for(j=0;j<count;++j)if(parameters[j]==v)break;
        v->offset=j<count?0:stack_reservation_offset(v->offset,holes,bytes,count);
    }
    for(i=0;i<cg.cursor_count;++i)
        cg.cursors[i].offset=stack_reservation_offset(cg.cursors[i].offset,holes,bytes,count);
    for(i=0;i<cg.affine_count;++i)for(j=0;j<cg.affine[i].count;++j)
        cg.affine[i].accesses[j].offset=stack_reservation_offset(cg.affine[i].accesses[j].offset,holes,bytes,count);
    for(i=0;i<cg.divmod_count;++i)
        cg.divmod[i].offset=stack_reservation_offset(cg.divmod[i].offset,holes,bytes,count);
    f->slots-=total;return stacked;
}
#include "scalar_values.inc"
#include "body_opt.inc"
#include "value_reuse.inc"
#include "known_values.inc"
#include "loop_fusion.inc"
static int function_uses_wide(Function *f);
#include "inline.inc"
#include "static_ipa.inc"
#include "value_recurrence.inc"
#include "dot_products.inc"
#include "dp_homes.inc"
#include "frame_packing.inc"
#include "byte_loop_regions.inc"
/* Recycle a consumed private DP home for an accumulated word value. A scalar
 * read here must be completely consumed on the left and dead afterward; a
 * previously consumed scalar must be dead on entry and exit. Continuations
 * include loop backedges. Pure operands cannot observe its replacement. */
static int dp_home_shared(unsigned word)
{
    unsigned i;
    unsigned char mapped;
    if(word>=cg.dp_words||!cg.dp_map[word])return 0;
    mapped=cg.dp_map[word];
    for(i=0;i<cg.dp_words;++i)if(i!=word&&cg.dp_map[i]==mapped)return 1;
    return 0;
}
static Symbol *last_use_home_at(Expr *e,unsigned depth)
{
    Symbol *v,*found;int in,out;
    if(!e)return NULL;
    if(!depth&&e->kind==EX_OBJECT){
        v=e->symbol;
        if(!body_private(v)||dot_reserved_symbol(v)||v->owner!=cg.function->id||!v->offset||width(v->type)!=2||
           !cg.dp_map[(v->offset-1)/2]||dp_home_shared((v->offset-1)/2)||
           expression_references(loop_current->expression,v)!=1||
           !direct_operand(e,v->type,0,0))return NULL;
        region_home_liveness(cg.function,loop_current,v->offset,&in,&out);
        return out?NULL:v;
    }
    if(!depth)return NULL;
    if((found=last_use_home_at(e->left,depth-1)))return found;
    if((found=last_use_home_at(e->right,depth-1)))return found;
    return last_use_home_at(e->third,depth-1);
}
static Symbol *recent_dead_home(void)
{
    Symbol *best=NULL;size_t latest=0,begin=cg.length>4096?cg.length-4096:0;unsigned i;
    for(i=0;i<cg.parser->symbol_count;++i){
        Symbol *v=&cg.parser->symbols[i];char name[32];const char *p;size_t read=0;int in,out;
        if(!body_private(v)||dot_reserved_symbol(v)||v->owner!=cg.function->id||!v->offset||width(v->type)!=2||
           !cg.dp_map[(v->offset-1)/2]||dp_home_shared((v->offset-1)/2)||
           expression_references(loop_current->expression,v))continue;
        snprintf(name,sizeof name,"__dp_home_%02u",cg.dp_map[(v->offset-1)/2]-1u);
        for(p=cg.assembly+begin;(p=strstr(p,name))!=NULL;++p){
            const char *line=p;while(line>cg.assembly&&line[-1]!='\n')--line;
            if(!strncmp(line,"    lda ",8)||!strncmp(line,"    ora ",8)||!strncmp(line,"    and ",8)||
               !strncmp(line,"    eor ",8)||!strncmp(line,"    adc ",8)||!strncmp(line,"    sbc ",8))read=(size_t)(p-cg.assembly);
        }
        if(read<=latest)continue;
        region_home_liveness(cg.function,loop_current,v->offset,&in,&out);
        if(!in&&!out){best=v;latest=read;}
    }
    return best;
}
static int last_use_binary_home(Expr *left,Expr *right,int op,Type t)
{
    Symbol *home=NULL;Expr operand={0};unsigned depth;
    if(cg.parser->no_body_optimizations||!cg.dp_homes||!loop_current||
       !loop_current->expression||t.pointers||t.base==TY_FLOAT||reg_width(t)!=2||
       (op!='+'&&op!='&'&&op!='|'&&op!='^')||!indexed_pure(left)||!indexed_pure(right))return 0;
    /* Prefer an already consumed home from the preceding expression. Its
     * last emitted read ranks candidates; IR liveness establishes safety. */
    home=recent_dead_home();
    for(depth=0;depth<16&&!home;++depth)home=last_use_home_at(left,depth);
    if(!home)return 0;
    operand.kind=EX_OBJECT;operand.symbol=home;operand.type=home->type;
    if(!direct_operand(&operand,t,0,0))return 0;
    code("; last-use home accumulation: %s\n",home->name);
    convert_registers(value_type(left->type),t);store_symbol(home);
    emit_value(right);convert_registers(value_type(right->type),t);
    register_binary(op,t,&operand);return 1;
}
static void forward_rebuilt_record(Function *f)
{
    Type t=f->symbol->type;
    Statement *first,*s,*ret;
    Expr *result;
    Symbol *destination,*source=NULL;
    if(cg.parser->no_copy_selection||cg.parser->no_body_optimizations||
       !structure_object(t)||t.structure->is_union||volatile_type(t)||f->jump_label_count)return;
    first=body_single(f->body);
    for(ret=first;ret&&ret->kind!=ST_RETURN;ret=ret->next){}
    if(!ret||ret->next||!(result=ret->expression)||result->kind!=EX_ASSIGN||
       result->right->kind!=EX_OBJECT)return;
    destination=result->right->symbol;
    if(destination->owner!=f->id||!destination->scope||!destination->offset)return;
    s=first;
    for(Member *m=t.structure->members;m;m=m->next,s=s->next){
        Expr *copy,*to,*from;
        while(s!=ret&&(s->kind==ST_EMPTY||(s->kind==ST_BLOCK&&!s->body)))s=s->next;
        if(s==ret||s->kind!=ST_EXPR||s->inline_callee||
           !(copy=s->expression)||copy->kind!=EX_ASSIGN||copy->op||
           m->bit_width||m->type.array)return;
        to=copy->left;from=copy->right;
        if(to->kind!=EX_MEMBER||from->kind!=EX_MEMBER||to->op!='.'||from->op!='.'||
           to->value!=m->offset||from->value!=m->offset||
           to->left->kind!=EX_OBJECT||to->left->symbol!=destination||
           from->left->kind!=EX_OBJECT||(source&&source!=from->left->symbol)||
           !same_type(unqualified_value(from->left->type),unqualified_value(t))||
           volatile_expression(copy))return;
        source=from->left->symbol;
    }
    while(s!=ret&&(s->kind==ST_EMPTY||(s->kind==ST_BLOCK&&!s->body)))s=s->next;
    if(s!=ret||!source||source->owner!=f->id||source->scope)return;
    /* Every field came from the same by-value argument. Return it directly */
    for(s=first;s!=ret;s=s->next){
        free_expression(s->expression);s->expression=NULL;s->kind=ST_EMPTY;
    }
    result->right->symbol=source;
    result->right->type=source->type;
    body_remove_local(f,destination);
}
static int literal_record_return(Function *f)
{
    Symbol *fn=f->symbol,*record;
    Type t=fn->type;
    Statement *parts[9];
    Expr *result;
    unsigned base,n=0,size=width(t),expected=0,written=0;
    uint64_t packed=0;
    if(cg.parser->no_copy_selection||!structure_object(t)||t.banked||t.structure->is_union||
       volatile_type(t)||size<2||size>8||(size&1)||statement_inline_markers(f->body)||
       !reduction_statements(f->body,parts,&n,9)||n<2||parts[n-1]->kind!=ST_RETURN)return 0;
    result=parts[n-1]->expression;
    if(!result||result->kind!=EX_ASSIGN||volatile_expression(result->right))return 0;
    record=direct_memory_object(result->right,&base);
    if(!record||record->owner!=f->id||!record->scope||!record->offset||
       base>width(record->type)||size>width(record->type)-base)return 0;
    for(Member *m=t.structure->members;m;m=m->next){
        unsigned bytes=width(m->type);
        if(m->bit_width||m->type.array||!bytes||m->offset+bytes>size)return 0;
        expected|=((1u<<bytes)-1)<<m->offset;
    }
    for(unsigned i=0;i+1<n;++i){
        Expr *store=parts[i]->expression;
        unsigned offset,bytes,mask;
        uint32_t value;
        uint64_t bits;
        if(parts[i]->kind!=ST_EXPR||!store||store->kind!=EX_ASSIGN||store->op||
           store->left->kind!=EX_MEMBER||volatile_expression(store)||
           fixed_memory_object(store->left,&offset)!=record||offset<base||
           !integer_constant(store->right,&value))return 0;
        offset-=base;
        bytes=width(store->left->type);
        if(!bytes||bytes>4||offset+bytes>size)return 0;
        mask=((1u<<bytes)-1)<<offset;
        if((expected&mask)!=mask)return 0;
        bits=(UINT64_C(1)<<(8*bytes))-1;
        packed=(packed&~(bits<<(8*offset)))|((initializer_cast(value,store->left->type)&bits)<<(8*offset));
        written|=mask;
    }
    if(written!=expected)return 0;
    /* The hidden result pointer is the first stack argument */
    code(".segment \"%s\"\n.export _%s\n_%s:\n; literal aggregate return\n",
         code_segment(),fn->asm_name,fn->asm_name);
    code("    lda %u,s\n    tax\n",3u+cg.parser->long_return);
    for(unsigned offset=0;offset<size;offset+=2){
        unsigned word=(unsigned)(packed>>(8*offset))&65535;
        if(word)code("    lda #$%04X\n    sta a:$%04X,x\n",word,offset);
        else code("    stz a:$%04X,x\n",offset);
    }
    code("    txa\n    rts\n__size_%s = * - _%s\n",fn->asm_name,fn->asm_name);
    f->frame=0;
    return 1;
}
static void emit_function(Function *f)
{
    Symbol *s=f->symbol;cg.function=f;cg.loop_count=0;cg.switch_depth=0;
    int frame_base,stacked;unsigned possible_registers;
    size_t start=cg.length;cg.interrupt_scratch=0;cg.dead_index_count=0;cg.omitted_parameter_count=0;
    memset(cg.frame_map,0,sizeof cg.frame_map);cg.frame_saved=0;
    forward_rebuilt_record(f);
    if(!cg.parser->no_body_optimizations&&!cg.parser->no_strength_reduction&&
       !f->jump_label_count&&!s->interrupt&&!body_asm_statements(f->body)&&
       !find_symbol(cg.parser,"$basic_asm")&&f->body->kind==ST_BLOCK)
        body_project_switch_strings(f->body->body);
    body_drop_unused_homes(f);
    if(!cg.parser->no_body_optimizations&&!cg.parser->no_strength_reduction&&!cg.parser->no_loop_unroll&&
       !f->jump_label_count&&!body_asm_statements(f->body))body_drop_empty_loops(f->body);
    if(f->uses_wide&&!s->interrupt&&!cg.parser->no_body_optimizations&&!cg.parser->no_strength_reduction&&
       !f->jump_label_count&&!statement_has_case(f->body)&&!body_asm_statements(f->body)){
        BodyFacts *facts=allocate(sizeof *facts);
        unsigned slots=f->slots;
        body_entry_values(f);
        scalar_refold(f->body);
        body_flow(f->body,facts);body_clear(facts);
        body_dead_locals(f);
        if(body_terminal_return_stores(f->body)){
            body_flow(f->body,facts);body_clear(facts);
            body_dead_locals(f);
        }
        if(f->slots!=slots){
            body_flow(f->body,facts);body_clear(facts);
            body_drop_unused_homes(f);
        }
        free(facts);
        if(narrow_statements(f->body,1))f->uses_wide=function_uses_wide(f);
    }
    if(!cg.parser->no_body_optimizations&&!f->symbol->interrupt)
        body_simplify_branches(f->body,f->symbol->type);
    /* Unstructured entries prevent path-dependent liveness, but a private
     * scalar that is never read on any path still needs no frame slot. */
    if(f->jump_label_count&&!f->uses_wide&&!f->uses_varargs&&!f->aggregate_abi&&!f->uses_bitfields&&
       !s->interrupt&&!cg.parser->no_body_optimizations&&!cg.parser->no_strength_reduction&&
       !body_asm_statements(f->body)&&!find_symbol(cg.parser,"$basic_asm"))body_dead_locals(f);
    copy_prepare(f,f->body);
    if(f->uses_wide){
        unsigned i;possible_registers=0;cg.register_homes=cg.register_spills=0;
        cg.cursor_count=cg.affine_count=cg.divmod_count=cg.divmod_available=cg.lftr_count=0;
        if(!f->jump_label_count&&!f->uses_varargs&&!f->aggregate_abi&&!f->uses_bitfields)strength_prepare(f);
        for(i=0;i<(unsigned)(s->param_count<0?0:s->param_count);++i)
            if(register_parameter(i,s->params[i]))possible_registers|=1u<<i;
        cg.register_homes=cg.register_spills=possible_registers;
        stacked=compact_parameter_reservations(f)!=0;
        f->frame=f->slots;
        emit_function_frame(f,stacked||f->slots!=0||f->uses_varargs||f->aggregate_abi,possible_registers,start);
        return;
    }
    if(f->jump_label_count||f->uses_varargs||f->aggregate_abi||f->uses_bitfields){
        /* Labels can enter structured regions from outside. Variadic access
         * also needs a stable frame so the incoming cursor remains valid. */
        cg.cursor_count=cg.affine_count=cg.divmod_count=cg.divmod_available=cg.lftr_count=0;
        if(!f->jump_label_count&&!s->interrupt&&
           !cg.parser->no_body_optimizations&&!cg.parser->no_strength_reduction&&
           !statement_has_case(f->body)&&!body_asm_statements(f->body)&&
           (f->aggregate_abi||f->uses_bitfields||(f->uses_varargs&&body_discarded_loads(f->body)))){
            BodyFacts *facts=allocate(sizeof *facts);
            if(f->aggregate_abi)body_dead_locals(f);
            if(f->uses_bitfields)body_narrow_far_locals(f);
            body_flow(f->body,facts);body_clear(facts);free(facts);
            body_dead_locals(f);
            if(f->aggregate_abi){
                body_drop_unused_homes(f);
                if(!cg.parser->no_loop_unroll&&body_drop_empty_loops(f->body))body_dead_locals(f);
            }
            if(literal_record_return(f))return;
        }
        possible_registers=plan_register_homes(f);
        stacked=compact_parameter_reservations(f)!=0;
        f->frame=f->slots+(reg_width(s->type)==4&&f->slots>4?2:0);
        emit_function_frame(f,stacked||f->slots||f->uses_varargs||f->aggregate_abi,possible_registers,start);
        return;
    }
    if(!s->interrupt&&!volatile_statements(f->body)&&!statement_inline_markers(f->body)&&
       (word_shift_scan_leaf(f)||range_scan_leaf(f)||guarded_update_leaf(f)||guarded_byte_lookup_leaf(f)||counted_reduction(f)))return;
    scalar_propagate(f);
    body_optimize(f);
    if(!cg.parser->no_body_optimizations&&!cg.parser->no_strength_reduction&&
       !cg.parser->no_value_reuse&&!s->interrupt&&!body_asm_statements(f->body))
        body_keep_clamps(f->body);
    if(!cg.parser->no_body_optimizations&&!cg.parser->no_strength_reduction&&
       !cg.parser->no_loop_unroll&&!s->interrupt&&!body_asm_statements(f->body))
        body_split_xor_loops(f->body);
    loop_fusion_prepare(f);
    body_shared_selections(f);
    value_reuse_prepare(f);
    body_reuse_addresses(f);
    body_order_homes(f);
    value_recurrences_prepare(f);
    body_byte_ranges(f);
    if(!volatile_statements(f->body))forward_return(f,f->body);f->frame=f->slots?f->slots+4:0;
    strength_prepare(f);
    affine_prepare(f);
    affine_prune_function_cursors(f);
    affine_compact_indices(f);
    lftr_prepare(f);
    divmod_prepare(f);
    known_prepare(f);
    dot_products_prepare(f);
    if(!s->interrupt&&!volatile_statements(f->body)&&(statement_inline_markers(f->body)?word_expression_leaf(f):
        (far_loop_leaf(f)||predicate_loop_leaf(f)||indexed_loop_leaf(f)||register_loop_leaf(f)||word_leaf(f)||word_expression_leaf(f)||wide_leaf(f)||entry_cursor_leaf(f)||entry_cursor_nested_leaf(f))))return;
    if(scalar_leaf(f))return;
    /* Word results can survive stack restoration in caller-clobbered X.
     * Wide results keep X untouched and need only one saved word for A. */
    possible_registers=plan_register_homes(f);
    stacked=compact_parameter_reservations(f)!=0;frame_base=stacked||f->slots!=0;
    pack_private_frame(f);
    f->frame=f->slots-cg.frame_saved+(reg_width(s->type)==4&&f->slots>4?2:0);
    if(cg.lftr_count){
        /* Speculative index elimination: any read or write of an eliminated
         * home re-emits the function with every index kept. */
        Codegen *saved=malloc(sizeof *saved);unsigned frame=f->frame;
        if(!saved){fputs("out of memory emitting assembly\n",stderr);exit(EXIT_FAILURE);}
        *saved=cg;cg.lftr_active=1;cg.lftr_failed=0;
        if(!(frame_base&&dp_homes_function(f,possible_registers)))emit_function_frame(f,frame_base,possible_registers,start);
#ifdef LFTR_DRYRUN
        cg.lftr_failed=1;
#endif
        if(!cg.lftr_failed){cg.lftr_active=0;free(saved);return;}
        {char *assembly=cg.assembly;size_t capacity=cg.capacity;
         cg=*saved;cg.assembly=assembly;cg.capacity=capacity;cg.length=start;cg.assembly[start]=0;}
        free(saved);f->frame=frame;cg.lftr_active=0;
    }
    if(frame_base&&dp_homes_function(f,possible_registers))return;
    emit_function_frame(f,frame_base,possible_registers,start);
}
static void emit_function_frame(Function *f,int frame_base,unsigned possible_registers,size_t start)
{
    Symbol *s=f->symbol;Statement *body=f->body;unsigned i,stack_offset=structure_object(s->type)?2:0;size_t save=0,restore=0;
    cg.loop_count=0;cg.switch_depth=f->jump_label_count!=0;cg.interrupt_scratch=0;
    cg.jump_base=cg.label;cg.label+=f->jump_label_count;
    code(".segment \"%s\"\n.export _%s\n_%s:\n",code_segment(),s->asm_name,s->asm_name);
    if(s->interrupt){
        static const char *const names[]={"","nmi","irq","brk","cop"};
        code(".export __vector_%s := _%s\n",names[s->interrupt],s->asm_name);
        if(s->interrupt==INT_NMI)code(".export __nmi_entry := _%s\n",s->asm_name);
        code("    jml interrupt_body_%s\ninterrupt_body_%s:\n",s->asm_name,s->asm_name);
        code("    rep #$30\n    pha\n    phx\n    phy\n    phd\n    pea $0000\n    pld\n    phb\n    sep #$20\n.a8\n    lda #$7E\n    pha\n    plb\n    rep #$20\n.a16\n");
        if(f->uses_wide)code("    cld\n");
        save=cg.length;
    }
    if(body->kind==ST_BLOCK)body=body->body;
    if(!f->uses_wide&&!f->jump_label_count&&!f->uses_varargs&&!f->aggregate_abi&&!f->uses_bitfields&&
       !s->interrupt&&!volatile_statements(f->body)){
        entry_guard(f,&body);
        zero_argument_entry(f);
        zero_mask_entry(f);
    }
    dp_home_parameters(f);
    if(frame_base){
        if(f->frame<=4){
            unsigned offset;Symbol *first=s->param_count>0?leaf_parameter(f,0):NULL;
            code("    phy\n");
            /* Push high homes first. A holds parameter 1, X parameter 0;
             * unused homes may contain arbitrary values until initialized. */
            for(offset=f->frame;offset;offset-=2)
                code("    %s\n",first&&(cg.register_spills&1)&&first->offset==offset-1?"phx":"pha");
            code("    tsc\n    tay\n");
        }else{
            if((cg.register_spills&2)&&!dp_parameter_home(f,1)){cg.arithmetic=1;code("    sta z:__arith_rhs\n");}
            code("    phy\n    tsc\n    sec\n    sbc #$%04X\n    tcs\n    tay\n",f->frame);
        }
        for(i=0;i<(unsigned)(s->param_count<0?0:s->param_count);++i){
            Symbol *v=NULL;unsigned j;
            for(j=0;j<cg.parser->symbol_count;++j)if(cg.parser->symbols[j].owner==f->id&&cg.parser->symbols[j].scope==0&&
                !strcmp(cg.parser->symbols[j].name,s->param_names[i])){v=&cg.parser->symbols[j];break;}
            if(!v)error_at(here(cg.parser),"internal parameter layout failure");
            if(register_parameter(i,v->type)){
                if(f->frame>4&&(cg.register_spills&(1u<<i))&&!dp_parameter_home(f,i)){
                    if(!i)code("    txa\n");else code("    lda z:__arith_rhs\n");code("    sta %s\n",frame_operand(v->offset));
                }
            }else{
                /* Incoming stack arguments already are private writable homes.
                 * Address them in place instead of copying every word. */
                v->offset=cg.dp_zero_stack?cg.dp_incoming_base+stack_offset:f->frame+cg.frame_saved+5+stack_offset+cg.parser->long_return;
                stack_offset+=argument_width(v->type);
            }
        }
    }
    if(cg.register_homes!=possible_registers||cg.register_spills!=possible_registers)
        code("; register entry: homes $%02X, spills $%02X\n",cg.register_homes,cg.register_spills);
    strength_parameters();
    if(emit_statements(body)&&(s->type.base!=TY_VOID||s->type.pointers||!strcmp(s->name,"main")))
        code("    lda #0\n    ldx #0\n");
    code("return_%s = *\n",s->asm_name);
    if(frame_base){
        if(f->frame<=4){
            unsigned offset;
            for(offset=0;offset<f->frame;offset+=2)code("    %s\n",reg_width(s->type)==4?"ply":"plx");
            code("    ply\n");
        }else if(reg_width(s->type)==4)
            code("    sta %s\n    tya\n    clc\n    adc #$%04X\n    tcs\n    pla\n    ply\n",frame_operand(f->frame-1),f->frame-2);
        else
            code("    tax\n    tya\n    clc\n    adc #$%04X\n    tcs\n    txa\n    ply\n",f->frame);
    }
    if(s->interrupt){
        if(s->interrupt==INT_NMI){
            code("__size_%s = * - _%s\n.segment \"NMI_END\"\n",s->asm_name,s->asm_name);
        }
        restore=cg.length;
        code("    plb\n    pld\n    ply\n    plx\n    pla\n    rti\n");
        if(s->interrupt!=INT_NMI)code("__size_%s = * - _%s\n",s->asm_name,s->asm_name);
        insert_interrupt_scratch(start,save,restore);
    }else{
        if(!strcmp(s->name,"main"))code("    rtl\n");else code("    rts\n");
        code("__size_%s = * - _%s\n",s->asm_name,s->asm_name);
    }
}
/* A near call whose next instruction, past label-only lines, is RTS. With
 * nothing between them the callee takes no stack arguments and sees the same
 * registers, flags and workspace; its return then reaches our caller. */
static int tail_call(const char *p)
{
    int adjacent=1;
    p=strchr(p,'\n');
    while(p&&*++p){
        const char *eol=strchr(p,'\n');size_t n=eol?(size_t)(eol-p):strlen(p);
        if(n==7&&!strncmp(p,"    rts",7))return adjacent&&eol?2:1;
        adjacent=0;
        if(!eol||!n||*p==' '||*p==';'||*p=='.')return 0;
        /* Labels: "name:" or "name = *" */
        if(!((p[n-1]==':'&&!memchr(p,' ',n))||(n>4&&!strncmp(p+n-4," = *",4))))return 0;
        p=eol;
    }
    return 0;
}
/* Materialize copy data after the function's return, in its code segment.
 * Until then the assembly passes only see the copy instructions. */
static void emit_block_copy_payloads(size_t at)
{
    static const char marker[]="; block copy payload ";
    const char *start=cg.assembly+at,*p=strstr(start,marker);
    char *payloads;
    if(!p)return;
    payloads=allocate(strlen(p)+1);
    strcpy(payloads,p);
    for(p=payloads;p;p=strstr(p,marker)){
        char *bytes;
        unsigned id=(unsigned)strtoul(p+sizeof marker-1,&bytes,10);
        code("cg_%s_%u_data:\n",cg.parser->unit,id);
        for(++bytes;*bytes!='\n';bytes+=2)code("    .byte $%.2s\n",bytes);
        p=bytes;
    }
    free(payloads);
}

static void near_relocations(void)
{
    char *original=cg.assembly;const char *p=original;int tail,frame_visible=0;
    cg.assembly=NULL;cg.length=cg.capacity=0;
    while(*p){
        if(p==original||p[-1]=='\n'){
            if(!strncmp(p,"; allocation function ",sizeof "; allocation function "-1))frame_visible=0;
            if(!strncmp(p,frame_address_marker,sizeof frame_address_marker-1))frame_visible=1;
        }
        if(!frame_visible&&!cg.parser->long_return&&(p==original||p[-1]=='\n')&&!strncmp(p,"    jsr ",8)&&p[8]!='('&&(tail=tail_call(p))!=0){
            /* The callee's RTS returns straight to our caller. An adjacent RTS
             * is unreachable afterwards; one behind a label stays a target. */
            const char *eol=strchr(p,'\n');
            code("    jmp%.*s\n",(int)(eol-p-7),p+7);p=eol+1;
            if(tail==2)p+=8;
        }
        else if(cg.parser->long_return&&!strncmp(p,"    rts\n",8)){code("    rtl\n");p+=8;}
        else if(!strncmp(p,"a:_",3)){
            const char *end=p+2;
            while(*end&&*end!=','&&*end!='\n'&&!isspace((unsigned char)*end))++end;
            code("a:.loword(%.*s)",(int)(end-p-2),p+2);p=end;
        }else{code("%c",*p);++p;}
    }
    free(original);
}
/* Instruction mnemonic of an assembly line, or NULL for a comment, label or
 * directive. */
static const char *reload_op(const char *line,const char *eol)
{
    if(eol-line<5||strncmp(line,"    ",4)||line[4]==';'||line[4]==' ')return NULL;
    return line+4;
}
/* N/Z after a removed reload: 1 if they are written before being read, 0 if
 * something may read them (branches, calls, returns, labels, flag pushes). */
static int reload_flags_dead(const char *p)
{
    static const char *const writers[]={"lda","ldx","ldy","cmp","cpx","cpy","and","ora","eor","adc","sbc",
        "tax","tay","txa","tya","tsx","tdc","tcd","xba","inc","dec","inx","dex","iny","dey","asl","lsr","rol","ror","pla","plx","ply"};
    static const char *const neutral[]={"sta","stx","sty","stz","pha","phx","phy","phb","phd","clc","sec","nop","tcs","txs"};
    while(*p){
        const char *eol=strchr(p,'\n'),*op;unsigned i;
        if(!eol)return 0;
        if(*p==';'){p=eol+1;continue;}
        if(*p=='.'&&(!strncmp(p,".a8\n",4)||!strncmp(p,".a16\n",5)||!strncmp(p,".i8\n",4)||!strncmp(p,".i16\n",5))){p=eol+1;continue;}
        if(!(op=reload_op(p,eol)))return 0;
        for(i=0;i<sizeof writers/sizeof *writers;++i)if(!strncmp(op,writers[i],3)&&(op[3]==' '||op[3]=='\n'))return 1;
        for(i=0;i<sizeof neutral/sizeof *neutral;++i)if(!strncmp(op,neutral[i],3)&&(op[3]==' '||op[3]=='\n'))break;
        if(i==sizeof neutral/sizeof *neutral){
            /* REP/SEP leave N/Z alone unless they name those status bits */
            if((!strncmp(op,"rep #$",6)||!strncmp(op,"sep #$",6))&&!(strtoul(op+6,NULL,16)&0x82u)){p=eol+1;continue;}
            return 0;
        }
        p=eol+1;
    }
    return 0;
}
/* Drop "lda X" after "sta X" with only comments between: A still holds the
 * stored value. X is restricted to private, non-volatile storage (frame and
 * stack slots, arithmetic scratch) and the load's N/Z must be dead. */
static void drop_reloads(size_t at)
{
    char *p=cg.assembly+at,*w=p;
    while(*p){
        char *eol=strchr(p,'\n'),*next,*q;size_t n;
        if(!eol)break;
        n=(size_t)(eol-p);
        if(n>8&&!strncmp(p,"    sta ",8)&&
           ((n>10&&!strncmp(p+n-2,",y",2)&&!strncmp(p+8,"a:$",3))||!strncmp(p+n-2,",s",2)||!strncmp(p+8,"z:__arith_",10))){
            q=eol+1;
            while(*q==';'&&(next=strchr(q,'\n')))q=next+1;
            next=strchr(q,'\n');
            if(next&&(size_t)(next-q)==n&&!strncmp(q,"    lda ",8)&&!strncmp(q+8,p+8,n-8)&&reload_flags_dead(next+1)){
                /* Keep the store and the comments; skip the load */
                size_t keep=(size_t)(q-p);memmove(w,p,keep);w+=keep;p=next+1;continue;
            }
        }
        memmove(w,p,n+1);w+=n+1;p=eol+1;
    }
    {size_t rest=strlen(p);memmove(w,p,rest+1);w+=rest;}
    cg.length=(size_t)(w-cg.assembly);
}
static int op_is(const char *op,const char *name){return !strncmp(op,name,3)&&(op[3]==' '||op[3]=='\n');}
/* Accumulator effect of one instruction inside a PHA/PLA window: 0 leaves A
 * alone, 1 overwrites A, -1 is not allowed in a window (stack, control,
 * width or block-move effects). */
static int window_effect(const char *op,const char *end)
{
    static const char *const keep[]={"ldx","ldy","stx","sty","sta","stz","tax","tay","txy","tyx","inx","dex","iny","dey","cpx","cpy","cmp","clc","sec","bit"};
    static const char *const write[]={"lda","txa","tya","adc","sbc","and","ora","eor","xba"};
    static const char *const shifts[]={"asl","lsr","rol","ror","inc","dec"};
    const char *comma;unsigned i;
    for(comma=op;comma<end;){
        comma=memchr(comma,',',(size_t)(end-comma));
        if(!comma)break;
        if(++comma<end&&*comma=='s')return -1;
    }
    for(i=0;i<sizeof keep/sizeof *keep;++i)if(op_is(op,keep[i]))return 0;
    for(i=0;i<sizeof write/sizeof *write;++i)if(op_is(op,write[i]))return 1;
    for(i=0;i<sizeof shifts/sizeof *shifts;++i)if(op_is(op,shifts[i]))return op[3]=='\n'||!strncmp(op+3," a\n",3);
    return -1;
}
/* Remove PHA ... PLA when the window cannot observe the stack and either
 * preserves A or A is overwritten (without being read) right after PLA. The
 * PLA's N/Z must be dead too; calls count as overwriting them because no
 * callee reads its entry flags. */
static void drop_push_pairs(size_t at)
{
    char *p=cg.assembly+at,*w=p;
    while(*p){
        char *eol=strchr(p,'\n');
        if(!eol)break;
        if(!strncmp(p,"    pha\n",8)){
            char *q=eol+1,*pull=NULL,*after;int writes=0,ok=1;
            while(*q&&ok){
                char *end=strchr(q,'\n');const char *op;int effect;
                if(!end){ok=0;break;}
                if(*q==';'){q=end+1;continue;}
                if(!(op=reload_op(q,end))){ok=0;break;}
                if(!strncmp(q,"    pla\n",8)){pull=q;break;}
                effect=window_effect(op,end);
                if(effect<0)ok=0;else writes|=effect;
                q=end+1;
            }
            if(ok&&pull){
                const char *next=pull+8,*op=NULL;
                while(*next==';'){const char *end=strchr(next,'\n');if(!end)break;next=end+1;}
                {const char *end=strchr(next,'\n');if(end)op=reload_op(next,end);}
                after=(char*)next;
                if(op&&(op_is(op,"jsr")||op_is(op,"jsl"))&&!writes)ok=1;
                else if(op&&(op_is(op,"lda")||op_is(op,"txa")||op_is(op,"tya")||op_is(op,"tdc")||op_is(op,"tsc")||op_is(op,"pla")))
                    ok=1;
                else ok=!writes&&reload_flags_dead(after);
                if(ok){
                    size_t keep=(size_t)(pull-(eol+1));
                    memmove(w,eol+1,keep);w+=keep;p=pull+8;continue;
                }
            }
        }
        {size_t n=(size_t)(eol-p)+1;memmove(w,p,n);w+=n;p=eol+1;}
    }
    {size_t rest=strlen(p);memmove(w,p,rest+1);w+=rest;}
    cg.length=(size_t)(w-cg.assembly);
}
static const char *skip_comments(const char *p)
{
    while(*p==';'){const char *end=strchr(p,'\n');if(!end)break;p=end+1;}
    return p;
}
/* After "rep #$20\n.a16\n" at p: the end of "lda #imm / sep #$20 / .a8 /
 * byte stores / rep #$20 / .a16" (the next 16-bit point), or NULL. */
static const char *byte_store_group(const char *p)
{
    const char *q=skip_comments(p);int stores=0;
    if(strncmp(q,"    lda #$",10)||!isxdigit((unsigned char)q[10]))return NULL;
    q=strchr(q,'\n');if(!q)return NULL;++q;
    if(strncmp(q,"    sep #$20\n.a8\n",17))return NULL;q+=17;
    for(;;){
        q=skip_comments(q);
        if(!strncmp(q,"    sta ",8)||!strncmp(q,"    stz ",8)){q=strchr(q,'\n');if(!q)return NULL;++q;++stores;continue;}
        break;
    }
    if(!stores||strncmp(q,"    rep #$20\n.a16\n",18))return NULL;
    return q+18;
}
/* A merge leaves A's high byte and N/Z different, so each group must end at a
 * full overwrite of A or at another mergeable group. */
static int byte_group_mergeable(const char *p)
{
    const char *end=byte_store_group(p),*op,*eol;
    if(!end)return 0;
    /* A following group starts with a word LDA. Its own merge is checked
     * separately, so an unsafe final group can still stay in word mode. */
    if(byte_store_group(end))return 1;
    do{
        end=skip_comments(end);eol=strchr(end,'\n');
        if(!eol||!(op=reload_op(end,eol)))return 0;
        end=eol+1;
    }while(op_is(op,"pea")||op_is(op,"pei"));
    return op_is(op,"pla")||op_is(op,"txa")||op_is(op,"tya")||op_is(op,"tdc")||op_is(op,"tsc")||op_is(op,"lda");
}
/* Keep consecutive constant byte stores in one 8-bit region */
static void merge_byte_stores(size_t at)
{
    char *p=cg.assembly+at,*w=p;int store=0;
    while(*p){
        char *eol=strchr(p,'\n');
        if(!eol)break;
        if(store&&!strncmp(p,"    rep #$20\n.a16\n",18)&&byte_group_mergeable(p+18)){
            char *q=p+18,*imm;size_t n;
            /* Comments, then the immediate narrowed to its stored byte */
            imm=(char*)skip_comments(q);n=(size_t)(imm-q);memmove(w,q,n);w+=n;
            {char *line=strchr(imm,'\n');unsigned long v=strtoul(imm+10,NULL,16);
             char buffer[24];int k=snprintf(buffer,sizeof buffer,"    lda #$%02lX\n",v&0xFFu);
             memcpy(w,buffer,(size_t)k);w+=k;p=line+1+17;}
            continue;
        }
        /* Set at .a8; kept by stores and comments; cleared by anything else */
        if(!strncmp(p,".a8\n",4))store=1;
        else if(strncmp(p,"    sta ",8)&&strncmp(p,"    stz ",8)&&*p!=';')store=0;
        {size_t n=(size_t)(eol-p)+1;memmove(w,p,n);w+=n;p=eol+1;}
    }
    {size_t rest=strlen(p);memmove(w,p,rest+1);w+=rest;}
    cg.length=(size_t)(w-cg.assembly);
}
#include "assembly_lines.inc"
/* Y-frame to stack-relative conversion of one finished function */
/* edit: 1 delete, 2 TYA->TSC, 3 adjusted N,s, 4 LDX via A before a load,
 * 5 LDX moved to its carry line (1 + its index), the start of the A run. */
typedef struct { const char *text; size_t length; const char *op; int label, depth, edit, offset, m8, x8, carry; } FrameLine;
/* Instructions that only compute A from A and non-X operands */
static int frame_a_only(const FrameLine *l)
{
    static const char *const ops[]={"and","ora","eor","adc","sbc","clc","sec","cmp"};
    static const char *const shifts[]={"asl","lsr","rol","ror","inc","dec"};
    const char *comma=strstr(l->op,",x");unsigned i;
    if(l->m8||(comma&&comma<l->text+l->length))return 0;
    for(i=0;i<sizeof ops/sizeof *ops;++i)if(op_is(l->op,ops[i]))return 1;
    for(i=0;i<sizeof shifts/sizeof *shifts;++i)if(op_is(l->op,shifts[i]))return l->op[3]=='\n'||l->length==9;
    return 0;
}
static int frame_line_is(const FrameLine *l,const char *text){size_t n=strlen(text);return l->op&&l->length==n+4&&!strncmp(l->op,text,n);}
/* Byte change of S, or 99 when the instruction's stack effect is unknown */
static int frame_stack_delta(const FrameLine *l)
{
    const char *op=l->op;
    if(op_is(op,"tcs")||op_is(op,"txs")||op_is(op,"mvn")||op_is(op,"mvp")||op_is(op,"rti"))return 99;
    return assembly_stack_bytes(op,l->m8,l->x8);
}
static int frame_y_use(const FrameLine *l)
{
    static const char *const users[]={"ldy","sty","cpy","iny","dey","tay","tya","tyx","txy","phy","ply","tsx","mvn","mvp"};
    unsigned i;const char *comma;
    for(i=0;i<sizeof users/sizeof *users;++i)if(op_is(l->op,users[i]))return 1;
    comma=strstr(l->op,",y");
    return comma&&comma<l->text+l->length;
}
static int frame_operand_at(const FrameLine *l,unsigned *n,size_t *at,size_t *span)
{
    const char *p=strstr(l->op,"a:$"),*end=l->text+l->length;char *stop;
    if(!p||p>end)return 0;
    *n=(unsigned)strtoul(p+3,&stop,16);
    if(stop+2!=end||stop[0]!=','||stop[1]!='y'||stop-p!=7)return 0;
    *at=(size_t)(p-l->text);*span=9;return 1;
}
/* The neighbouring instruction past comments, or -1 at a label, directive or
 * the edge of the function. */
static int frame_instruction(const FrameLine *lines,unsigned count,unsigned k,int direction)
{
    unsigned i=k;
    for(;;){
        if(direction<0){if(!i)return -1;--i;}else if(++i>=count)return -1;
        if(!lines[i].length)return -1;
        if(lines[i].text[0]==';')continue;
        return lines[i].op?(int)i:-1;
    }
}
static int stack_frames(Function *f,size_t at)
{
    char *text;FrameLine *lines;unsigned count=0,i,frame=0,start=0,base_line=0,*work,top=0;size_t length=cg.length-at;
    const char *p;int m8=0,x8=0,ok=1,prologue=-1,large=0,base=0,keep_y=0,unreachable=0;
    AssemblyLabels labels={0};unsigned label_count=0;
    if(f->symbol->interrupt||cg.parser->no_stack_frames)return 0;
    text=malloc(length+1);lines=malloc((length/2+2)*sizeof *lines);work=malloc((length/2+2)*sizeof *work);
    if(!text||!lines||!work){fputs("out of memory emitting assembly\n",stderr);exit(EXIT_FAILURE);}
    memcpy(text,cg.assembly+at,length+1);
    for(p=text;*p;){
        const char *eol=strchr(p,'\n');FrameLine *l=&lines[count++];
        if(!eol)eol=p+strlen(p);
        memset(l,0,sizeof *l);l->text=p;l->length=(size_t)(eol-p);l->depth=-1;l->offset=-1;
        l->label=assembly_decode(p,l->length,&m8,&x8,&l->op);
        l->m8=m8;l->x8=x8;if(l->label)++label_count;
        p=*eol?eol+1:eol;
    }
    /* Exactly one prologue: PHY, then pushes and TSC/TAY, or a TCS frame */
    for(i=0;i<count&&ok;++i)if(lines[i].op&&frame_line_is(&lines[i],"phy")){
        unsigned j=i+1,pushes=0;
        /* Later PHYs are Y windows, checked while walking */
        if(prologue>=0)continue;
        while(j<count&&(frame_line_is(&lines[j],"pha")||frame_line_is(&lines[j],"phx"))){++pushes;++j;}
        if(j+1<count&&frame_line_is(&lines[j],"tsc")&&frame_line_is(&lines[j+1],"tay")){
            prologue=(int)i;frame=pushes*2;lines[i].edit=1;lines[j].edit=1;lines[j+1].edit=1;base_line=j+1;
        }else if(!pushes&&j+4<count&&frame_line_is(&lines[j],"tsc")&&frame_line_is(&lines[j+1],"sec")&&
                 lines[j+2].op&&!strncmp(lines[j+2].op,"sbc #$",6)&&frame_line_is(&lines[j+3],"tcs")&&frame_line_is(&lines[j+4],"tay")){
            prologue=(int)i;frame=(unsigned)strtoul(lines[j+2].op+6,NULL,16);large=1;
            lines[i].edit=1;lines[j+4].edit=1;base_line=j+4;
        }else{
            /* Pushes interleaved with straight-line parameter setup: every
             * word pushed before TSC/TAY is a frame word. */
            for(j=i+1,pushes=0;j+1<count;++j){
                const FrameLine *l=&lines[j];
                if(!l->op){if(l->label||(l->length&&l->text[0]=='.'))break;continue;}
                if(frame_line_is(l,"tsc")&&frame_line_is(&lines[j+1],"tay"))break;
                if(l->m8||l->x8||frame_y_use(l))break;
                if(frame_line_is(l,"pha")||frame_line_is(l,"phx")||!strncmp(l->op,"pea ",4)){pushes+=2;continue;}
                if(frame_stack_delta(l)||op_is(l->op,"jsr")||op_is(l->op,"jsl")||op_is(l->op,"jmp")||op_is(l->op,"rts")||
                   l->op[0]=='b'&&!op_is(l->op,"bit"))break;
            }
            if(j+1<count&&frame_line_is(&lines[j],"tsc")&&frame_line_is(&lines[j+1],"tay")&&pushes){
                prologue=(int)i;frame=pushes;lines[i].edit=1;lines[j].edit=1;lines[j+1].edit=1;base_line=j+1;
            }else ok=0;
        }
    }
    if(prologue<0)ok=0;
    if(ok&&lines[prologue].x8)ok=0;
    /* Y windows: "phy / ldy #k ... [ptr],y ... ply" around far accesses. A
     * converted frame leaves Y free, so the windows go and the caller's Y is
     * saved once by the prologue's PHY and restored by the final PLY. */
    for(i=0;ok&&i<count;++i)if(i!=(unsigned)prologue&&frame_line_is(&lines[i],"phy"))keep_y=1;
    if(keep_y)lines[prologue].edit=6;
    /* Walk every path from entry. A state is the push depth from entry times
     * two, plus one while the saved Y (removed below) is on the stack. */
    if(ok){
        assembly_labels_init(&labels,label_count);
        for(i=0;i<count;++i)if(lines[i].label)assembly_label_add(&labels,lines[i].text,lines[i].length,i);
        lines[0].depth=0;work[top++]=0;
    }
    while(ok&&top){
        unsigned k=work[--top],first=k;int state=lines[k].depth,d=state>>2,win=(state>>1)&1,active=state&1;
        for(;k<count&&ok;++k){
            FrameLine *l=&lines[k];int delta,target=-1,ends=0,conditional=0;
            if(k!=first&&l->depth>=0){if(l->depth!=((d<<2)|(win<<1)|active))ok=0;break;}
            l->depth=((d<<2)|(win<<1)|active);
            if(!l->op)continue;
            if(k==(unsigned)prologue){d+=2;active=1;continue;}
            if(win){
                /* Inside a window Y is an index: only these uses, and no
                 * frame or stack-relative operand. */
                const char *end=l->text+l->length;
                if(frame_line_is(l,"ply")){l->edit=1;d-=2;win=0;continue;}
                if(frame_y_use(l)){
                    if(op_is(l->op,"ldy")||op_is(l->op,"iny")||op_is(l->op,"dey")||op_is(l->op,"txy")||
                       (l->length>3&&(!strncmp(end-3,"],y",3)||!strncmp(end-3,"),y",3)))){l->edit=6;continue;}
                    ok=0;break;
                }
                if(l->length>2&&end[-2]==','&&end[-1]=='s'){ok=0;break;}
                if(op_is(l->op,"rts")||op_is(l->op,"rtl")){ok=0;break;}
            }else if(keep_y&&frame_line_is(l,"phy")){
                if(!active){ok=0;break;}
                l->edit=1;d+=2;win=1;continue;
            }
            if(l->edit&&k!=base_line){d+=frame_stack_delta(l);continue;}
            if(k==base_line){
                if(large)d+=(int)frame;
                base=d;continue;
            }
            if(large&&frame_line_is(l,"tcs")&&k==base_line-1)continue;
            if(frame_line_is(l,"tya")){
                /* Large-frame teardown: TYA is S at the frame base, then
                 * CLC/ADC/TCS releases the frame. */
                if(d!=base||!active||k+3>=count||!frame_line_is(&lines[k+1],"clc")||!lines[k+2].op||
                   strncmp(lines[k+2].op,"adc #$",6)||!frame_line_is(&lines[k+3],"tcs")){ok=0;break;}
                l->edit=2;lines[k+1].depth=lines[k+2].depth=((d<<2)|(win<<1)|active);
                d-=(int)strtoul(lines[k+2].op+6,NULL,16);k+=3;lines[k].depth=((d<<2)|(win<<1)|active);continue;
            }
            if(frame_line_is(l,"ply")){
                if(!active||d!=2){ok=0;break;}
                l->edit=keep_y?6:1;
                d=0;active=0;continue;
            }
            if(frame_y_use(l)){
                unsigned n;size_t pos,span;
                /* Only these instructions have a stack-relative mode. LDX
                 * has none; it goes through A where A and N/Z are dead. */
                if(op_is(l->op,"ldx")&&!l->m8&&!l->x8){
                    int before=frame_instruction(lines,count,k,-1),after=frame_instruction(lines,count,k,1);
                    while(after>=0&&(frame_line_is(&lines[after],"inx")||frame_line_is(&lines[after],"dex")))
                        after=frame_instruction(lines,count,(unsigned)after,1);
                    if(after>=0&&lines[after].op&&op_is(lines[after].op,"lda")&&!lines[after].m8)l->edit=4;
                    else if(after>=0&&(op_is(lines[after].op,"jsr")||op_is(lines[after].op,"jsl"))){
                        /* Before a call (which reads no flags), load X ahead of
                         * the run of A-only instructions that produced A. */
                        while(before>=0&&frame_a_only(&lines[before]))before=frame_instruction(lines,count,(unsigned)before,-1);
                        if(before<0||!op_is(lines[before].op,"lda")||lines[before].m8||lines[before].carry||
                           (strstr(lines[before].op,",x")&&strstr(lines[before].op,",x")<lines[before].text+lines[before].length)){ok=0;break;}
                        l->edit=5;lines[before].carry=(int)k+1;
                    }else{ok=0;break;}
                }else if(!(op_is(l->op,"lda")||op_is(l->op,"sta")||op_is(l->op,"adc")||op_is(l->op,"sbc")||op_is(l->op,"and")||
                     op_is(l->op,"ora")||op_is(l->op,"eor")||op_is(l->op,"cmp"))){ok=0;break;}
                if(!active||!frame_operand_at(l,&n,&pos,&span)||d<base||!base){ok=0;break;}
                if(n>frame&&n<=frame+2){ok=0;break;}
                l->offset=(int)(keep_y||n<=frame?n:n-2)+(d-base);
                if(l->offset>255){ok=0;break;}
                continue;
            }
            if(active){
                /* An existing N,s operand above the removed slot moves down */
                const char *end=l->text+l->length;
                if(l->length>2&&end[-2]==','&&end[-1]=='s'){
                    const char *q=end-2;unsigned n;
                    while(q>l->op&&isdigit((unsigned char)q[-1]))--q;
                    if(q==end-2||q[-1]!=' '){ok=0;break;}
                    n=(unsigned)strtoul(q,NULL,10);
                    if(keep_y)l->offset=(int)n;
                    else if((int)n>d)l->offset=(int)n-2;
                    else if((int)n>d-2){ok=0;break;}
                    else l->offset=(int)n;
                    l->edit=3;
                }
            }
            if(frame_line_is(l,"tsc")&&k+3<count&&frame_line_is(&lines[k+1],"clc")&&lines[k+2].op&&
               !strncmp(lines[k+2].op,"adc #$",6)&&frame_line_is(&lines[k+3],"tcs")){
                lines[k+1].depth=lines[k+2].depth=d;
                d-=(int)strtoul(lines[k+2].op+6,NULL,16);k+=3;lines[k].depth=d;continue;
            }
            delta=frame_stack_delta(l);
            if(delta==99){ok=0;break;}
            d+=delta;
            if(d<0){ok=0;break;}
            if(op_is(l->op,"rts")||op_is(l->op,"rtl")){if(d){ok=0;}ends=1;}
            else if(op_is(l->op,"jml")||op_is(l->op,"brk")||op_is(l->op,"cop")||op_is(l->op,"stp"))ends=1;
            else if(op_is(l->op,"jmp")||op_is(l->op,"bra")||op_is(l->op,"brl")||
                    (l->op[0]=='b'&&(op_is(l->op,"bcc")||op_is(l->op,"bcs")||op_is(l->op,"beq")||op_is(l->op,"bne")||
                     op_is(l->op,"bmi")||op_is(l->op,"bpl")||op_is(l->op,"bvc")||op_is(l->op,"bvs")))){
                const char *name=l->op+4;size_t n=(size_t)(l->text+l->length-name);
                conditional=l->op[0]=='b'&&!op_is(l->op,"bra")&&!op_is(l->op,"brl");
                if(*name=='('||*name=='['){ok=0;break;}
                target=assembly_label_target(&labels,k,name,n);
                if(target<0){
                    /* A transfer out of the function is a tail call: frame gone */
                    if(conditional||d){ok=0;break;}
                    ends=1;
                }
            }
            if(target>=0){
                if(lines[target].depth<0){lines[target].depth=((d<<2)|(win<<1)|active);work[top++]=(unsigned)target;}
                else if(lines[target].depth!=((d<<2)|(win<<1)|active)){ok=0;break;}
                if(!conditional)break;
            }
            if(ends)break;
        }
    }
    /* Unreachable frame references must be pruned before removing Y */
    for(i=0;ok&&i<count;++i)if(lines[i].op&&frame_y_use(&lines[i])&&!lines[i].edit&&lines[i].offset<0&&lines[i].depth>=0)ok=0;
    for(i=0;ok&&i<count;++i)if(lines[i].op&&frame_y_use(&lines[i])&&lines[i].depth<0){ok=0;unreachable=1;}
    if(ok){
        const FrameLine *previous=NULL;
        cg.length=at;cg.assembly[at]=0;
        for(i=0;i<count;++i){
            FrameLine *l=&lines[i];
            if(l->edit==1||l->edit==5)continue;
            if(l->edit==4){code("    lda %u,s\n    tax\n",(unsigned)l->offset);previous=NULL;continue;}
            /* An LDX before a call moves ahead of the run that produced A */
            if(l->carry){code("    lda %u,s\n    tax\n",(unsigned)lines[l->carry-1].offset);previous=NULL;}
            if(l->edit==2){code("    tsc\n");previous=l;continue;}
            if(l->edit==3){
                const char *q=l->text+l->length-2;
                while(isdigit((unsigned char)q[-1]))--q;
                code("%.*s%u,s\n",(int)(q-l->text),l->text,(unsigned)l->offset);previous=l;continue;
            }
            if(l->offset>=0){unsigned n;size_t pos,span;frame_operand_at(l,&n,&pos,&span);
                /* Just after a 16-bit PHX, 1,s is X itself: TXA gives the same
                 * A and N/Z without the stack read. */
                if(l->offset==1&&pos==4&&!strncmp(l->op,"lda ",4)&&!l->m8&&!l->x8&&previous&&frame_line_is(previous,"phx")){
                    code("    txa\n");previous=l;continue;
                }
                code("%.*s%u,s\n",(int)pos,l->text,(unsigned)l->offset);previous=l;continue;}
            if(l->length||l->text[0])code("%.*s\n",(int)l->length,l->text);
            if(l->op)previous=l;else if(l->label)previous=NULL;
        }
    }
    (void)start;assembly_labels_free(&labels);free(text);free(lines);free(work);
    return unreachable;
}
#include "line_passes.inc"
static int lto_provided_function(Parser *p,Symbol *s)
{
    Function *f;if(!p->source_lto||!s->function)return 0;
    for(f=p->functions;f;f=f->next)if(!strcmp(f->symbol->asm_name,s->asm_name)&&!f->symbol->inline_omit&&
        (!f->symbol->inline_hint||f->symbol->internal||f->symbol->inline_external))return 1;
    return 0;
}
/* Some near lvalues use an immediate object address followed by an indexed
 * memory instruction. Distinguish those from addresses passed to hardware. */
static Symbol *interrupt_address_base(Expr *e)
{
    unsigned offset;
    if(!e||far_pointer(value_type(e->type)))return NULL;
    if(e->kind==EX_CAST)return interrupt_address_base(e->left);
    if(e->kind==EX_BINARY&&(e->op=='+'||e->op=='-'))
        return interrupt_address_base(value_type(e->left->type).pointers?e->left:e->right);
    return near_object_address(e,&offset);
}

static void interrupt_lvalues(Expr *e,int access)
{
    Symbol *s=NULL;unsigned i,offset;
    if(!e)return;
    if(access){
        if(e->kind==EX_OBJECT&&!e->type.array)s=e->symbol;
        if(e->kind==EX_DEREF)s=interrupt_address_base(e->left);
        if(e->kind==EX_MEMBER&&!e->type.array){
            int pointer;Expr *root=member_root(e,&offset,&pointer);
            if(pointer)s=interrupt_address_base(root);
            else if(root->kind==EX_DEREF)s=interrupt_address_base(root->left);
            else if(root->kind==EX_OBJECT)s=root->symbol;
        }
        if(s&&!s->owner&&!s->function&&!s->dpage&&!s->type.banked)
            code("; interrupt lvalue _%s\n",s->asm_name);
    }
    interrupt_lvalues(e->left,e->kind!=EX_ADDRESS&&(e->kind!=EX_MEMBER||e->op==TOK_ARROW));
    interrupt_lvalues(e->right,1);
    interrupt_lvalues(e->third,1);
    for(i=0;i<e->arg_count;++i)interrupt_lvalues(e->args[i],1);
}

static void interrupt_statement_lvalues(Statement *s)
{
    for(;s;s=s->next){
        interrupt_lvalues(s->expression,1);
        interrupt_lvalues(s->step,1);
        interrupt_statement_lvalues(s->initial);
        interrupt_statement_lvalues(s->body);
        interrupt_statement_lvalues(s->alternate);
    }
}

/* Keep unsupported wide value uses out of 32-bit optimizers until the full
 * eight-byte ABI and general expression lowering are implemented. */
static int validate_wide_expression(Expr *e)
{
    unsigned i;int used=0;if(!e)return 0;
    if(e->kind==EX_ADDRESS&&e->left){
        if(e->left->kind==EX_OBJECT)return 0;
        if(e->left->kind==EX_DEREF||e->left->kind==EX_MEMBER)
            return validate_wide_expression(e->left->left);
    }
    if(wide_compare_supported(e)||wide_narrow_supported(e)||wide_pointer_supported(e)||wide_call_used(e)||
       narrow_wide_compound_supported(e))return 1;
    if(!wide_address_safe(e)&&wide_mixed_narrow_supported(e))return 1;
    if(!e->type.pointers&&!e->type.array&&e->type.base==TY_DOUBLE)
        error_at(e->location,"binary64 runtime values are not implemented yet");
    if(!e->type.pointers&&!e->type.array&&e->type.base==TY_LONGLONG)
        error_at(e->location,"64-bit runtime values are not implemented yet");
    used|=validate_wide_expression(e->left);used|=validate_wide_expression(e->right);used|=validate_wide_expression(e->third);
    for(i=0;i<e->arg_count;++i)used|=validate_wide_expression(e->args[i]);
    if(used&&(((e->type.pointers||e->type.array)&&!wide_pointer_supported(e)&&
       !(e->type.array&&e->kind==EX_DEREF&&wide_lvalue_address_supported(e))&&
       !(e->kind==EX_ASSIGN&&e->left->kind==EX_OBJECT&&
         ((!e->op&&(wide_pointer_supported(e->right)||wide_narrow_supported(e->right)||
                    wide_address_expression_supported(e->right)))||
          ((e->op=='+'||e->op=='-')&&wide_narrow_supported(e->right)))))||
       (e->kind!=EX_BINARY&&e->kind!=EX_UNARY&&e->kind!=EX_CAST&&e->kind!=EX_CHOOSE&&
        e->kind!=EX_COMMA&&e->kind!=EX_CALL&&e->kind!=EX_ASSIGN&&
        !(e->kind==EX_DEREF&&(wide_pointer_supported(e->left)||wide_narrow_supported(e->left)))&&
        !((e->kind==EX_MEMBER||e->kind==EX_BITFIELD)&&wide_lvalue_address_supported(e)))))
        error_at(e->location,"64-bit runtime values in this expression are not implemented yet");
    if(used&&e->kind==EX_ASSIGN&&(!e->left||(e->left->kind!=EX_OBJECT&&
       ((!wide_lvalue_address_supported(e->left))||
        (e->op&&!wide_mixed_narrow_supported(e->right))))))
        error_at(e->location,"64-bit runtime values in this assignment are not implemented yet");
    return used;
}
static int validate_wide_condition(Expr *e)
{
    if(!e)return 0;
    if(wide_compare_supported(e)||(wide_scalar(value_type(e->type))&&wide_value_supported(e)))return 1;
    if(e->kind==EX_BINARY&&(e->op==TOK_LAND||e->op==TOK_LOR)){
        int a=validate_wide_condition(e->left),b=validate_wide_condition(e->right);return a||b;
    }
    if(e->kind==EX_UNARY&&e->op=='!')return validate_wide_condition(e->left);
    if(e->kind==EX_CAST&&e->type.is_bool&&!e->type.pointers)return validate_wide_condition(e->left);
    return validate_wide_expression(e);
}
static int wide_discard_supported(Expr *e)
{
    if(!e)return 0;
    if(e->kind==EX_CAST&&!e->type.pointers&&e->type.base==TY_VOID)
        return wide_discard_supported(e->left);
    if(e->kind==EX_COMMA&&!e->type.pointers&&e->type.base==TY_VOID&&!wide_address_safe(e))
        return (wide_address_safe(e->left)||wide_discard_supported(e->left))&&
            (wide_address_safe(e->right)||wide_discard_supported(e->right));
    if(wide_scalar(value_type(e->type)))return wide_value_supported(e);
    return !wide_address_safe(e)&&wide_mixed_narrow_supported(e);
}
static int validate_wide_statements(Statement *s,int wide_result)
{
    int used=0;
    for(;s;s=s->next){
        if(s->kind==ST_EXPR&&(wide_assignment_supported(s->expression)||wide_update_supported(s->expression)||wide_narrow_assignment(s->expression)||wide_discard_supported(s->expression)))used=1;
        else if(s->kind==ST_SWITCH&&wide_scalar(value_type(s->expression->type))&&wide_value_supported(s->expression))used=1;
        else if(s->kind==ST_IF||s->kind==ST_WHILE||s->kind==ST_FOR||s->kind==ST_DO)
            used|=validate_wide_condition(s->expression);
        else if(s->kind==ST_RETURN&&wide_result&&wide_value_supported(s->expression))used=1;
        else if((s->kind==ST_EXPR||s->kind==ST_RETURN)&&wide_call_used(s->expression))used=1;
        else if(s->kind==ST_RETURN&&(wide_compare_supported(s->expression)||wide_narrow_supported(s->expression)))used=1;
        else used|=validate_wide_expression(s->expression);
        if(wide_assignment_supported(s->step)||wide_update_supported(s->step)||wide_narrow_assignment(s->step)||wide_discard_supported(s->step))used=1;
        else used|=validate_wide_expression(s->step);
        used|=validate_wide_statements(s->body,wide_result);
        used|=validate_wide_statements(s->alternate,wide_result);
        used|=validate_wide_statements(s->initial,wide_result);
    }
    return used;
}
static int function_uses_wide(Function *f)
{
    Symbol *s=f->symbol;
    int signature=wide_scalar(value_type(s->type));
    for(int i=0;i<s->param_count;++i)
        if(wide_scalar(value_type(s->params[i])))signature=1;
    return validate_wide_statements(f->body,wide_scalar(value_type(s->type)))|signature;
}
static void resolve_near_memcpy(Parser *p)
{
    for(unsigned i=0;i<p->symbol_count;++i){
        Symbol *s=&p->symbols[i];
        Type result,source,count;
        if(!s->function||s->defined||s->internal||s->old_style||s->variadic||s->param_count!=3||
           strcmp(s->asm_name,"memcpy"))continue;
        result=value_type(s->type);source=value_type(s->params[1]);count=value_type(s->params[2]);
        if(result.base==TY_VOID&&result.pointers==1&&!far_pointer(result)&&
           same_type(result,value_type(s->params[0]))&&source.base==TY_VOID&&source.pointers==1&&
           !far_pointer(source)&&object_constant(pointed_type(source))&&
           count.base==TY_INT&&!count.pointers&&count.is_unsigned)
            strcpy(s->asm_name,"_zicc_memcpy_near");
    }
}
#include "narrow_rodata.inc"
static void wram_object_segment(Symbol *s,unsigned part)
{
    const char *kind=s->wram==WRAM_HIRAM?"H":"X";
    if(s->initializer)code(".segment \"ZWRAM_D_%s_%u_%s\"\n",kind,part,s->asm_name);
    else code(".segment \"ZWRAM_B_%s_0_%s\"\n",kind,s->asm_name);
}
static void emit_sram_object(Symbol *s)
{
    unsigned size=width(s->type),bank=(unsigned)(s->wram-WRAM_SRAM_FIRST);
    unsigned remaining=size;
    for(unsigned part=0;remaining;part++){
        unsigned bytes=remaining<sram_window_size?remaining:sram_window_size;
        code(".segment \"ZSRAM_%u_%u_%u_%u_%u_%s\"\n",
             sram_first_bank,sram_window_size,sram_capacity,bank,part,s->asm_name);
        if(alignment(s->type)==2)code(".align 2\n");
        if(!part)code("_%s:\n",s->asm_name);
        code("    .res %u\n",bytes);
        remaining-=bytes;
    }
    if(!s->internal){
        code(".export _%s\n",s->asm_name);
        code("__zicc_sram_window_%s = %u\n.export __zicc_sram_window_%s: absolute\n",s->asm_name,bank,s->asm_name);
        code("__zicc_sram_bound_%s = %u\n.export __zicc_sram_bound_%s: far\n",s->asm_name,s->type.array,s->asm_name);
        code("__zicc_object_size_%s = %u\n.export __zicc_object_size_%s: far\n",s->asm_name,size,s->asm_name);
    }
}
static int wram_placement_known(Parser *p,Symbol *s)
{
    const char *item=p->near_wram_objects;
    size_t length=strlen(s->asm_name);
    while(item&&*item){
        const char *end=strchr(item,',');
        if((end?(size_t)(end-item):strlen(item))==length&&!memcmp(item,s->asm_name,length))return 1;
        item=end?end+1:NULL;
    }
    return 0;
}
static void emit_program(FILE *out,Parser *p)
{
    Function *f;String *string;unsigned i,runtime_size=0;
    memset(&cg,0,sizeof cg);cg.parser=p;
    for(f=p->functions;f;f=f->next)f->uses_wide=function_uses_wide(f);
    inline_translation_unit(p);
    narrow_rodata_struct_arrays(p);
    resolve_near_memcpy(p);
    for(i=0;i<p->symbol_count;++i){
        Symbol *s=&p->symbols[i];
        if(s->wram&&s->wram<WRAM_SRAM_FIRST&&!s->owner)s->wram_near=wram_placement_known(p,s);
    }
    code("; ABI: near7e-far24pad32\n");
    /* Debugger names describe source objects, never linker bookkeeping */
    for(i=0;i<p->symbol_count;++i){Symbol *s=&p->symbols[i];
        if(s->owner||!s->defined)continue;
        code("; debug symbol _%s %s\n",s->asm_name,
             s->internal&&!strncmp(s->asm_name,"__lto_",6)?s->asm_name+2:s->asm_name);
    }
    code(".setcpu \"65816\"\n.a16\n.i16\n.import main_exit\n");
    for(i=0;i<p->symbol_count;++i){Symbol *s=&p->symbols[i];if(s->owner||s->function||!s->defined)continue;
        unsigned size=width(s->type);
        if(s->wram>=WRAM_SRAM_FIRST){emit_sram_object(s);continue;}
        if(s->wram)wram_object_segment(s,0);
        else code(".segment \"%s\"%s\n",s->runtime_ram?"RUNTIME_BSS":s->loram?(s->initializer?"LORAM_DATA":"LORAM_BSS"):s->initializer?(s->type.banked?(s->embedded?"EMBED":"RODATA"):"DATA"):s->dpage?"ZEROPAGE":"BSS",s->dpage?": zeropage":"");
        if(!s->runtime_ram&&!s->loram&&!s->dpage&&!s->type.banked)
            code("; allocation object _%s %s\n",s->asm_name,s->internal?"local":"global");
        if(s->runtime_ram){unsigned a=alignment(s->type);runtime_size=(runtime_size+a-1)&~(a-1);runtime_size+=size;}
        if(!s->internal)code(".%s _%s\n",s->dpage?"exportzp":"export",s->asm_name);
        code("__zicc_object_size_%s = %u\n",s->asm_name,size);
        if(!s->internal)code(".export __zicc_object_size_%s: %s\n",s->asm_name,
                             size>65536||(s->wram&&size>65535)?"far":"absolute");
        if(s->wram&&!s->internal){
            const char *kind=s->wram==WRAM_HIRAM?"H":"X";
            code("__zicc_wram_%s_%s = %u\n.export __zicc_wram_%s_%s: far\n",
                 kind,s->asm_name,size,kind,s->asm_name);
        }
        if(structure_object(s->type)||((s->initializer||s->runtime_ram||s->wram)&&alignment(s->type)==2))code(".align 2\n");
        if(s->initializer){
            unsigned j,part=0,boundary=s->wram?0x4000:size;
            Relocation *r=s->relocations;code("_%s:\n",s->asm_name);
            for(j=0;j<size;){
                /* Keep relocations intact so a manual LoROM link can place
                 * each copy span in a single physical source window. */
                if(r&&r->offset==j&&j<boundary&&j+r->size>boundary)boundary=j;
                if(j==boundary){
                    wram_object_segment(s,++part);
                    boundary=j+0x4000;
                }
                if(r&&r->offset==j){
                    char target[160];
                    if(r->symbol){
                        snprintf(target,sizeof target,r->symbol->function?(wide_scalar(value_type(r->symbol->type))?"__fnptr64_%s":"__fnptr_%s"):"_%s",r->symbol->asm_name);
                        r->symbol->used=1;if(r->symbol->function)r->symbol->adapter_used=1;
                    }
                    else{snprintf(target,sizeof target,"str_%s_%u",p->unit,r->string->id);r->string->used=1;}
                    code("    .word .loword(%s%+ld)\n",target,(long)r->addend);
                    if(r->far_value){
                        if(r->symbol&&!r->symbol->function&&!r->symbol->type.banked)code("    .byte $7E, $00\n");
                        else code("    .byte .bankbyte(%s%+ld), $00\n",target,(long)r->addend);
                    }
                    if(r->symbol&&!r->symbol->function&&!r->symbol->type.banked&&!r->symbol->dpage)
                        code(".assert %s%+ld >= $7E0001 .and %s%+ld <= $7EFFFF, lderror, \"near address initializer exceeds bank $7E\"\n",target,(long)r->addend,target,(long)r->addend);
                    j+=r->size;r=r->next;
                }else{
                    unsigned end=boundary<size?boundary:size;
                    if(r&&end>r->offset)end=r->offset;
                    if(!s->wram&&size>65536&&s->initializer[j]==0){
                        unsigned limit=end<j+65535?end:j+65535;
                        unsigned zero=j+1;
                        while(zero<limit&&s->initializer[zero]==0)++zero;
                        if(zero-j>=16){
                            code("    .res %u, 0\n",zero-j);
                            j=zero;continue;
                        }
                    }
                    if(end>j+16)end=j+16;
                    code("    .byte ");for(;j<end;++j){code("$%02X",s->initializer[j]);if(j+1<end)code(",");}code("\n");
                }
            }
        }else if(s->wram&&size>65535){
            unsigned remaining=size;
            code("_%s:\n",s->asm_name);
            while(remaining>65535){code("    .res 65535\n");remaining-=65535;}
            code("    .res %u\n",remaining);
        }else code("_%s: .res %u\n",s->asm_name,size);
        if(s->runtime_ram)code(".assert _%s >= $7F0000 .and _%s + %u <= $800000, lderror, \"runtime object exceeds bank $7F\"\n",s->asm_name,s->asm_name,size);
    }
    if(runtime_size)code(".export __runtime_runtime_bss_size := %u\n",runtime_size);
    static_ipa_prepare(p);
    bank_prepare();
    for(f=p->functions;f;f=f->next){
        size_t at;
        if(f->symbol->inline_omit||(f->symbol->inline_hint&&!f->symbol->internal&&!f->symbol->inline_external))continue;
        code("; allocation function %u begin\n",f->id);
        if(frame_address_visible(f->body))code("%s",frame_address_marker);
        at=cg.length;emit_function(f);
        /* These passes currently treat arithmetic scratch as dead at a C
         * return; an eight-byte result deliberately lives there across it. */
        if(!f->uses_wide){
            if(!volatile_statements(f->body))drop_reloads(at);
            drop_push_pairs(at);merge_byte_stores(at);
            if(stack_frames(f,at)&&lp_prune_before_frames(f,at))stack_frames(f,at);
            line_passes(f,at);
        }else lp_wide_runtime_exit(f,at);
        /* Summarized last: line passes may give the function workspace words */
        dp_summarize(f,at);
        emit_block_copy_payloads(at);
        if(f->symbol->interrupt)interrupt_statement_lvalues(f->body);
        code("; allocation function %u end\n",f->id);
    }
    bank_emit();
    emit_near_library();
    for(i=0;i<p->symbol_count;++i)if(p->symbols[i].adapter_used)
        code(".import %s%s\n",wide_scalar(value_type(p->symbols[i].type))?"__fnptr64_":"__fnptr_",p->symbols[i].asm_name);
    for(i=0;i<p->symbol_count;++i){Symbol *s=&p->symbols[i];if(!s->owner&&s->used&&(!s->defined||
        (s->function&&s->inline_hint&&!s->internal&&!s->inline_external))&&!lto_provided_function(p,s))
        code(".import%s _%s\n",s->dpage?"zp":"",s->asm_name);}
    /* A zero-byte segment records an unqualified object reference in the
     * ca65 object. Manual links can check selected prebuilt members too. */
    for(i=0;i<p->symbol_count;++i){
        Symbol *s=&p->symbols[i];
        if(!s->owner&&!s->function&&!s->defined&&s->used&&!s->wram)
            code(".segment \"ZICC_WRAM_UNQUAL_%s\"\n",s->asm_name);
    }
    for(i=0;i<p->symbol_count;++i){
        Symbol *s=&p->symbols[i];
        const char *kind;
        if(!s->wram||s->wram>=WRAM_SRAM_FIRST||s->owner||(!s->defined&&!s->used))continue;
        kind=s->wram==WRAM_HIRAM?"H":"X";
        if(!s->defined){
            code(".import __zicc_wram_%s_%s: far\n",kind,s->asm_name);
            if(width(s->type))
                code(".assert __zicc_wram_%s_%s = %u, lderror, \"conflicting WRAM object extent\"\n",
                     kind,s->asm_name,width(s->type));
        }
        if(s->wram_near){
            if(!s->defined)
                code(".assert _%s >= $7E0000 .and _%s + __zicc_wram_%s_%s <= $7F0000, lderror, \"invalid near WRAM placement\"\n",
                     s->asm_name,s->asm_name,kind,s->asm_name);
            else
                code(".assert _%s >= $7E0000 .and _%s + %u <= $7F0000, lderror, \"invalid near WRAM placement\"\n",
                     s->asm_name,s->asm_name,width(s->type));
        }
    }
    int sram_bounds=0;
    for(i=0;i<p->symbol_count;++i){
        Symbol *s=&p->symbols[i];
        if(s->wram<WRAM_SRAM_FIRST||s->owner||(!s->defined&&!s->used&&!s->placement_used))continue;
        if(!sram_bounds){
            code(".import __sram_first_bank, __sram_window_size, __sram_capacity: far\n");
            code(".assert __sram_first_bank = %u .and __sram_window_size = %u .and __sram_capacity = %u, "
                 "lderror, \"SRAM declaration was compiled with a different cartridge layout\"\n",
                 sram_first_bank,sram_window_size,sram_capacity);
            sram_bounds=1;
        }
        if(!s->defined){
            code(".import __zicc_sram_window_%s: absolute, __zicc_sram_bound_%s: far, __zicc_object_size_%s: far\n",
                 s->asm_name,s->asm_name,s->asm_name);
            code(".assert __zicc_sram_window_%s = %u .and __zicc_sram_bound_%s = %u .and __zicc_object_size_%s = %u, "
                 "lderror, \"conflicting SRAM declaration for %s\"\n",
                 s->asm_name,(unsigned)(s->wram-WRAM_SRAM_FIRST),s->asm_name,s->type.array,s->asm_name,width(s->type),s->name);
        }
    }
    int dp_bounds=0;
    for(i=0;i<p->symbol_count;++i){Symbol *s=&p->symbols[i];
        if(s->owner||!s->dpage||!s->type.pointers||s->type.array||(!s->defined&&!s->used))continue;
        if(!dp_bounds){code(".import __DP_START__, __DP_SIZE__\n");dp_bounds=1;}
        code(".assert _%s >= __DP_START__ .and _%s + %u <= __DP_START__ + __DP_SIZE__, lderror, \"__dpage pointer exceeds allocated direct page\"\n",s->asm_name,s->asm_name,width(s->type));
    }
    int loram_bounds=0;
    for(i=0;i<p->symbol_count;++i){Symbol *s=&p->symbols[i];
        if(s->owner||s->function||!s->loram||(!s->defined&&!s->used))continue;
        if(!loram_bounds){code(".import __NEAR_START__\n");loram_bounds=1;}
        if(!s->defined)code(".import __zicc_object_size_%s\n",s->asm_name);
        code(".assert _%s >= __NEAR_START__ .and _%s + __zicc_object_size_%s <= $7E2000, lderror, \"__loram object %s exceeds available LoRAM\"\n",s->asm_name,s->asm_name,s->asm_name,s->name);
    }
    /* Speculative emission and later line passes may remove every workspace
     * reference. Do not keep an otherwise unused runtime archive member. */
    if(cg.arithmetic&&(strstr(cg.assembly,"__arith_lhs")||strstr(cg.assembly,"__arith_rhs")))
        code(".importzp __arith_lhs, __arith_rhs\n");
    if(strstr(cg.assembly,"__fp_round_mode"))code(".import __fp_round_mode\n");
    if(strstr(cg.assembly,"a:.loword(__fp_exceptions)"))code(".import __fp_exceptions\n");
    for(i=0;i<cg.helper_count;++i)code(".import %s\n",cg.helpers[i]);
    if(cg.require_float_format)
        code(".import __require_float_format\n.assert __require_float_format <> 0, lderror, \"float formatter is unavailable\"\n");
    if(cg.require_int64_format)
        code(".import __require_int64_format\n.assert __require_int64_format <> 0, lderror, \"64-bit integer formatter is unavailable\"\n");
    code(".segment \"RODATA\"\n");
    for(string=p->strings;string;string=string->next)if(string->used){
        /* Literals are read-only and C leaves their sharing unspecified. A
         * literal that ends another (including an identical one) aliases the
         * longest such literal, lowest id first; owners emit the bytes. */
        String *owner=string,*other;size_t j;
        for(other=p->strings;other;other=other->next)
            if(other->used&&other!=string&&other->size>=string->size&&
               !memcmp(other->bytes+other->size-string->size,string->bytes,string->size)&&
               (other->size>owner->size||(other->size==owner->size&&other->id<owner->id)))owner=other;
        if(owner!=string){
            code("str_%s_%u = str_%s_%u+$%04X\n",p->unit,string->id,p->unit,owner->id,(unsigned)(owner->size-string->size));
            continue;
        }
        code("str_%s_%u:\n",p->unit,string->id);
        for(j=0;j<string->size;++j){if(!(j%16))code("    .byte ");else code(",");code("$%02X",string->bytes[j]);if(j%16==15||j+1==string->size)code("\n");}
    }
    near_relocations();
    if(!relax_assembly(out,cg.assembly,p->unit,!p->no_branch_relaxation))exit(EXIT_FAILURE);
    free(cg.assembly);
}
