// Read C declarations, statements, and expressions into the compiler's internal form
static Expr *expression(Parser *p);
static Expr *expression_allow_sram_array(Parser *p);
static Expr *assignment_expression(Parser *p);
static Statement *object_initializer(Parser *p,Symbol *s,int automatic);
static Symbol *new_symbol(Parser *p,const char *name,Type t,Location at);
static Statement *statement(Parser *p);;
static Type named_declarator(Parser *p,Type t,char *name,int optional);
static Symbol *linked_symbol(Parser *p,const char *name);
static void merge_function(Symbol *s,Symbol *candidate,Location at);
static void check_default_promotions(const Symbol *prototype,Location at);

static void enter_nested_parse(Parser *p)
{
    if(++p->parse_depth>256)
        error_at(p->token.location,"expression or declarator nesting exceeds compiler limit");
}
static uint32_t initializer_constant(Expr *e,int active);
static uint32_t initializer_cast(uint32_t v,Type t);
static uint64_t initializer_wide_constant(Expr *e,int active);
static uint64_t initializer_cast64(uint64_t v,Type t);
static const char *integer_binary_constant(int op,Type operands,uint64_t a,uint64_t b,uint64_t *result);
static float initializer_float(uint32_t bits,Type t);
static const char *binary32_constant_operation(int op,float x,float y,uint32_t *result);
static void integer_constant_operands(Expr *e,const char *context);
static int basic_asm_name(Parser *p)
{
    return p->token.kind==TOK_NAME&&(!strcmp(p->token.name,"__asm")||!strcmp(p->token.name,"__asm__"));
}
static int type_start(Parser *p)
{
    int k=p->token.kind;
    if(k==TOK_INT||k==TOK_CHAR||k==TOK_BOOL||k==TOK_VOID||k==TOK_FLOAT||k==TOK_DOUBLE||k==TOK_LONG||k==TOK_SHORT||
       k==TOK_UNSIGNED||k==TOK_SIGNED||k==TOK_CONST||k==TOK_VOLATILE||k==TOK_STRUCT||k==TOK_UNION||k==TOK_ENUM||k==TOK_TYPEDEF||k==TOK_REGISTER||k==TOK_AUTO||k==TOK_STATIC||k==TOK_EXTERN||k==TOK_LORAM||k==TOK_HIRAM||k==TOK_XBANKRAM||k==TOK_SRAM)return 1;
    if(k==TOK_NAME&&find_alias(p,p->token.name))return 1;
    return 0;
}
static Expr *new_expr(ExprKind kind,Location at,Type t)
{
    Expr *e=allocate(sizeof *e);e->kind=kind;e->location=at;e->type=t;return e;
}
static int spanning_sram_array(const Expr *e)
{
    return e->kind==EX_OBJECT&&e->symbol->wram>=WRAM_SRAM_FIRST&&
           e->type.array&&width(e->type)>sram_window_size;
}
static void reject_spanning_sram_array(const Expr *e)
{
    if(spanning_sram_array(e))
        error_at(e->location,"spanning SRAM array '%s' requires direct indexing",e->symbol->name);
}
static Type promoted(Type t)
{
    t=unqualified_value(t);
    if(t.bit_field_width&&t.bit_field_width<16)t.is_unsigned=0;
    t.bit_field_width=0;
    if(!t.pointers&&t.base==TY_CHAR)return type(TY_INT,0);
    /* Both short variants have the same range as their int counterparts */
    if(!t.pointers)t.is_short=0;
    return t;
}
/* Default argument promotions apply to unprototyped and variadic arguments,
   not to ordinary arithmetic or parameters with a prototype. */
static Type default_argument_promoted(Type t)
{
    t=promoted(t);
    if(binary64_enabled&&!t.pointers&&t.base==TY_FLOAT)return type(TY_DOUBLE,0);
    return t;
}
/* Scalar casts between integer types of the same representation preserve all bits */
static int same_value_representation(Type a,Type b)
{
    a=unqualified_value(a);b=unqualified_value(b);
    if(!a.pointers&&!b.pointers){
        a.is_short=b.is_short=0;
        a.is_plain_char=b.is_plain_char=0;
    }
    return same_type(a,b);
}
static int numeric(Type t)
{
    return !t.pointers&&!t.array&&(t.base==TY_CHAR||t.base==TY_INT||t.base==TY_LONG||t.base==TY_LONGLONG||t.base==TY_FLOAT||t.base==TY_DOUBLE);
}
static Type common_type(Type a,Type b)
{
    a=promoted(a);b=promoted(b);
    if(a.base==TY_VOID&&b.base==TY_VOID&&!a.pointers&&!b.pointers)return a;
    if(function_pointer(a))return a;
    if(function_pointer(b))return b;
    if(a.pointers&&b.pointers){if(far_pointer(b))a=far_type(a);a.constant|=b.constant;a.pointer_constants|=b.pointer_constants;a.is_volatile|=b.is_volatile;a.pointer_volatiles|=b.pointer_volatiles;return a;}
    if(a.pointers)return a;if(b.pointers)return b;
    if(a.base==TY_DOUBLE||b.base==TY_DOUBLE)return type(TY_DOUBLE,0);
    if(a.base==TY_FLOAT||b.base==TY_FLOAT)return type(TY_FLOAT,0);
    if(a.base==TY_LONGLONG||b.base==TY_LONGLONG){
        Type t=type(TY_LONGLONG,0);t.is_unsigned=(a.base==TY_LONGLONG&&a.is_unsigned)||(b.base==TY_LONGLONG&&b.is_unsigned);return t;
    }
    if(a.base==TY_LONG||b.base==TY_LONG){
        Type t=type(TY_LONG,0);t.is_unsigned=(a.base==TY_LONG&&a.is_unsigned)||(b.base==TY_LONG&&b.is_unsigned);return t;
    }
    {int u=a.is_unsigned||b.is_unsigned;a=type(TY_INT,0);a.is_unsigned=u;return a;}
}
static uint32_t literal_integer(Expr *e,Type t);
static int spillable_address(Expr *e,int object)
{
    if(!e)return 0;
    switch(e->kind){
    case EX_OBJECT:return (object||e->type.array)&&e->symbol->wram;
    case EX_MEMBER:return (object||e->type.array)&&spillable_address(e->left,e->op=='.');
    case EX_DEREF:return (object||e->type.array)&&spillable_address(e->left,0);
    case EX_ADDRESS:return spillable_address(e->left,1);
    case EX_CAST:return value_type(e->left->type).pointers&&spillable_address(e->left,0);
    case EX_BINARY:return (e->op=='+'||e->op=='-')&&
        (spillable_address(e->left,0)||spillable_address(e->right,0));
    case EX_COMMA:return spillable_address(e->right,object);
    case EX_CHOOSE:return spillable_address(e->right,object)||spillable_address(e->third,object);
    default:return 0;
    }
}
static int rom_address(Expr *e,int object)
{
    if(!e)return 0;
    switch(e->kind){
    case EX_STRING:return 1;
    case EX_OBJECT:return (object||e->type.array)&&e->symbol->type.banked&&!e->symbol->wram;
    case EX_MEMBER:return (object||e->type.array)&&rom_address(e->left,e->op=='.');
    case EX_DEREF:return (object||e->type.array)&&rom_address(e->left,0);
    case EX_ADDRESS:return rom_address(e->left,1);
    case EX_CAST:return value_type(e->left->type).pointers&&rom_address(e->left,0);
    case EX_BINARY:return (e->op=='+'||e->op=='-')&&value_type(e->type).pointers&&
        ((value_type(e->left->type).pointers&&rom_address(e->left,0))||
         (e->op=='+'&&value_type(e->right->type).pointers&&rom_address(e->right,0)));
    case EX_COMMA:return rom_address(e->right,object);
    case EX_CHOOSE:
        if(e->left->kind==EX_INT&&e->left->type.base!=TY_FLOAT&&e->left->type.base!=TY_DOUBLE)
            return (e->left->value||e->left->value_high)?rom_address(e->right,object):rom_address(e->third,object);
        return rom_address(e->right,object)||rom_address(e->third,object);
    default:return 0;
    }
}
static Expr *bad_convert(Expr *e,Type target)
{
    Expr *cast=new_expr(EX_CAST,e->location,unqualified_value(target));
    cast->left=e;cast->error_reported=1;return cast;
}
static Expr *convert(Expr *e,Type target)
{
    Type source=unqualified_value(e->type);Expr *cast;
    reject_spanning_sram_array(e);
    target=unqualified_value(target);
    if((function_pointer(source)&&target.pointers&&!function_pointer(target))||
       (function_pointer(target)&&source.pointers&&!function_pointer(source)&&
        !(source.pointers==1&&source.base==TY_VOID&&e->kind==EX_INT&&!e->value))){
        report_error(e->location,"function and object pointers cannot be converted");
        return bad_convert(e,target);
    }
    if(structure_object(source)&&target.base==TY_VOID&&!target.pointers){
        cast=new_expr(EX_CAST,e->location,target);cast->left=e;return cast;
    }
    if(structure_object(source)||structure_object(target))error_at(e->location,"struct values are not implemented yet");
    if(!target.pointers)target.constant=0;
    if(!source.pointers)source.constant=0;
    if(same_type(source,target)&&source.bit_field_width==target.bit_field_width)return e;
    if(target.is_bool&&!target.pointers){
        if(e->kind==EX_INT){e->value=source.base==TY_FLOAT?(e->value&0x7fffffff)!=0:source.base==TY_DOUBLE?(e->value|(e->value_high&0x7fffffff))!=0:(e->value|e->value_high)!=0;e->value_high=0;e->type=target;return e;}
        cast=new_expr(EX_UNARY,e->location,type(TY_INT,0));cast->op='!';cast->left=e;
        e=new_expr(EX_UNARY,e->location,target);e->op='!';e->left=cast;return e;
    }
    if((source.pointers&&!target.pointers&&(target.base==TY_FLOAT||target.base==TY_DOUBLE))||
       (target.pointers&&!source.pointers&&(source.base==TY_FLOAT||source.base==TY_DOUBLE))){
        report_error(e->location,"pointer/float conversion is not supported");
        return bad_convert(e,target);
    }
    if(far_pointer(source)&&target.pointers&&!far_pointer(target)&&spillable_address(e,0)){
        report_error(e->location,"spillable WRAM address is not representable as a near pointer");
        return bad_convert(e,target);
    }
    if(e->kind==EX_INT&&target.pointers){
        if(source.base==TY_LONGLONG&&e->value_high){
            report_error(e->location,"64-bit pointer constant is out of range");
            e->error_reported=1;
        }
        if(far_pointer(target)&&!source.pointers&&!source.is_unsigned&&value_width(source)==2&&(e->value&32768u))e->value|=0xffff0000u;
        if(far_pointer(target)){if(source.pointers&&!far_pointer(source)&&e->value)e->value=(e->value&65535u)|0x7e0000u;e->value&=0xffffffu;e->type=target;return e;}
        if((source.pointers&&far_pointer(source)&&e->value&&(e->value>>16)!=0x7e)||
           (e->value>65535u&&((e->value>>16)!=0x7e||!(e->value&65535u)))){
            report_error(e->location,"far address is not representable as a near pointer");
            e->error_reported=1;
        }
        e->value&=65535;e->type=target;return e;
    }
    if(far_pointer(source)&&target.pointers&&!far_pointer(target)&&rom_address(e,0)){
        report_error(e->location,"ROM address is not representable as a near pointer");
        return bad_convert(e,target);
    }
    if(e->kind==EX_INT&&numeric(source)&&numeric(target)&&source.base!=TY_DOUBLE&&target.base!=TY_DOUBLE){
        if(target.base==TY_LONGLONG&&source.base!=TY_FLOAT){
            if(source.base!=TY_LONGLONG){uint32_t v=literal_integer(e,source);e->value=v;e->value_high=!source.is_unsigned&&(v&UINT32_C(0x80000000))?UINT32_MAX:0;}
            e->type=target;return e;
        }
        if(source.base==TY_LONGLONG&&target.base!=TY_FLOAT){
            e->value=initializer_cast(e->value,target);if(width(target)<=2)e->value&=0xffffu;
            e->value_high=0;e->type=target;return e;
        }
        if(target.base==TY_FLOAT&&source.base!=TY_FLOAT&&source.base!=TY_LONGLONG){
            float f=source.is_unsigned?(float)e->value:(float)(source.base==TY_LONG?(int32_t)e->value:(int16_t)e->value);
            memcpy(&e->value,&f,4);e->type=target;return e;
        }
        /* Byte literals hold their promoted word value, like registers do */
        if(source.base!=TY_FLOAT&&target.base!=TY_FLOAT&&(target.base==TY_INT||target.base==TY_LONG||target.base==TY_CHAR)){
            uint32_t v=literal_integer(e,target);e->type=target;e->value=width(target)<=2?v&0xFFFFu:v;return e;
        }
    }
    cast=new_expr(EX_CAST,e->location,target);cast->left=e;return cast;
}
static Expr *assignment_convert(Expr *e,Type target)
{
    Type source=unqualified_value(e->type),destination=unqualified_value(target);
    if((function_pointer(source)||function_pointer(destination))&&
       !compatible_argument(destination,e)){report_error(e->location,"incompatible function pointer assignment");return bad_convert(e,target);}
    if(source.pointers&&destination.pointers&&far_pointer(source)&&!far_pointer(destination))
        {report_error(e->location,"implicit far-to-near pointer conversion (use __far)");return bad_convert(e,target);}
    if(source.pointers&&destination.pointers&&(void_pointer(source)||void_pointer(destination))){
        Type from=pointed_type(source),to=pointed_type(destination);
        if(object_constant(from)&&!object_constant(to)){report_error(e->location,"conversion discards const qualification");return bad_convert(e,target);}
        if(object_volatile(from)&&!object_volatile(to)){report_error(e->location,"conversion discards volatile qualification");return bad_convert(e,target);}
        return convert(e,target);
    }
    if((source.element||destination.element)&&source.pointers&&destination.pointers&&!compatible_argument(destination,e)){
        report_error(e->location,nested_far_mismatch(destination,e)?
                     "incompatible pointer-to-array assignment: nested near/far pointer mismatch":
                     "incompatible pointer-to-array assignment");
        return bad_convert(e,target);
    }
    if(source.pointers&&source.pointers==destination.pointers&&
       ((source.constant&&!destination.constant)||(source.pointer_constants&~destination.pointer_constants)))
        {report_error(e->location,"conversion discards const qualification");return bad_convert(e,target);}
    if(source.pointers&&destination.pointers&&
       (source.base==TY_STRUCT||destination.base==TY_STRUCT)&&
       source.base!=TY_VOID&&destination.base!=TY_VOID&&
       !compatible_argument(destination,e))
        {report_error(e->location,"incompatible aggregate pointer assignment");return bad_convert(e,target);}
    if(source.pointers&&source.pointers==destination.pointers&&
       ((source.is_volatile&&!destination.is_volatile)||(source.pointer_volatiles&~destination.pointer_volatiles)))
        {report_error(e->location,"conversion discards volatile qualification");return bad_convert(e,target);}
    if(source.pointers&&destination.pointers&&(source.pointers>1||destination.pointers>1)&&
       !compatible_argument(destination,e)){
        report_error(e->location,nested_far_mismatch(destination,e)?
                     "incompatible nested pointer assignment: nested near/far pointer mismatch":
                     "incompatible nested pointer assignment");
        return bad_convert(e,target);
    }
    return convert(e,target);
}
static int lvalue(Expr *e)
{
    if(e->kind==EX_BITFIELD)return lvalue(e->left);
    return e->kind==EX_OBJECT||e->kind==EX_DEREF||
        (e->kind==EX_MEMBER&&(e->op==TOK_ARROW||lvalue(e->left)));
}
/* Const applies recursively to embedded objects, but not pointer pointees */
static int aggregate_const_member(Type t)
{
    Member *m;
    if(object_constant(t))return 1;
    if(t.array)return aggregate_const_member(array_element(t));
    if(structure_object(t)&&t.structure)
        for(m=t.structure->members;m;m=m->next)if(aggregate_const_member(m->type))return 1;
    return 0;
}
static int aggregate_has_array(Type t)
{
    Member *m;
    if(t.array)return 1;
    if(structure_object(t)&&t.structure)
        for(m=t.structure->members;m;m=m->next)if(aggregate_has_array(m->type))return 1;
    return 0;
}
/* A non-lvalue aggregate containing an array has temporary lifetime. Preserve
 * the value before a later subscript expression can modify the destination.
 * Homes are assigned only to temporaries remaining in the executable AST. */
static Expr *aggregate_snapshot(Parser *p,Expr *e)
{
    char name[64];Symbol *home;Expr *lhs,*copy;Type t=e->type;t.banked=0;
    snprintf(name,sizeof name,"$copy_value_%u",p->symbol_count);
    home=new_symbol(p,name,t,e->location);home->owner=p->current?p->current->id:~0u;home->copy_temporary=1;
    lhs=new_expr(EX_OBJECT,e->location,t);lhs->symbol=home;
    copy=new_expr(EX_ASSIGN,e->location,t);copy->left=lhs;copy->right=e;return copy;
}
static int writable(Expr *e){return lvalue(e)&&!e->type.array&&!function_type(e->type)&&!object_constant(e->type);}
static Expr *bitfield_expression(Parser *p,Expr *storage,const Member *member)
{
    Expr *field=new_expr(EX_BITFIELD,storage->location,storage->type);
    field->type.bit_field_width=member->bit_width;
    field->value=member->bit_shift;
    field->op=!member->type.is_unsigned;
    field->left=storage;
    storage->type.is_unsigned=1;
    if(p->current)p->current->uses_bitfields=1;
    return field;
}
static unsigned expression_size(Expr *e)
{
    if(e->kind==EX_BITFIELD)error_at(e->location,"sizeof cannot be applied to a bit-field");
    return e->kind==EX_STRING?(unsigned)e->string->size:width(e->type);
}
static void pointer_element(Type t,Location at)
{
    t=value_type(t);
    if(function_pointer(t))error_at(at,"function pointer arithmetic is invalid");
    if(t.pointers){t=pointed_type(t);if(structure_object(t)&&!width(t))error_at(at,"pointer arithmetic requires a complete struct type");}
}
static Expr *pointer_offset(Expr *index)
{
    uint64_t bits=((uint64_t)index->value_high<<32)|index->value;
    /* Valid offsets fit in the signed 32-bit arithmetic of either pointer ABI.
     * Keep out-of-range constants intact for the existing diagnostics. */
    if(!index->type.pointers&&index->type.base==TY_LONGLONG&&
       (index->kind!=EX_INT||
        (index->type.is_unsigned?bits<=INT32_MAX:
         (int64_t)bits>=INT32_MIN&&(int64_t)bits<=INT32_MAX)))
        return convert(index,type(TY_LONG,0));
    return index;
}
static Expr *sram_subscript(Expr *array,Expr *index,Type element)
{
    Location at=array->location;
    Type ulong=type(TY_LONG,0),bytes=far_type(type(TY_CHAR,1));
    Expr *offset,*base,*add,*cast,*result;
    unsigned element_size=width(element);
    ulong.is_unsigned=1;
    index=convert(index,ulong);
    if(index->kind==EX_INT){
        uint32_t logical=index->value*element_size;
        index->value=(logical/sram_window_size)*65536u+logical%sram_window_size;
        offset=index;
    }else{
        Expr *scale=new_expr(EX_BINARY,at,ulong);
        scale->op='*';scale->left=index;
        scale->right=new_expr(EX_INT,at,ulong);scale->right->value=element_size;
        offset=new_expr(EX_UNARY,at,ulong);
        offset->op=TOK_SRAM;offset->left=scale;
    }
    /* Use byte arithmetic relative to the linked symbol at the first window */
    array->type=element;
    base=new_expr(EX_ADDRESS,at,pointer_to(element));base->left=array;
    cast=new_expr(EX_CAST,at,bytes);cast->left=base;
    add=new_expr(EX_BINARY,at,bytes);add->op='+';add->left=cast;add->right=offset;
    cast=new_expr(EX_CAST,at,pointer_to(element));cast->left=add;
    result=new_expr(EX_DEREF,at,element);result->left=cast;
    return result;
}
static Type call_arguments(Parser *p,Expr *e,const char *name,int count,int variadic,int old_style,const Type *parameters)
{
    unsigned i,stack_bytes=e->left?13:MAX_RETURN_ADDRESS_BYTES;
    Location at=e->location;
    if(!accept(p,')')){
        do{
            if(e->arg_count==MAX_ARGUMENTS)error_at(at,"too many function arguments (limit %u)",MAX_ARGUMENTS);
            Expr *argument=assignment_expression(p);
            reject_spanning_sram_array(argument);
            e->args[e->arg_count++]=argument;
        }while(accept(p,','));
        expect(p,')',"')'");
    }
    Type first_argument=e->arg_count?value_type(e->args[0]->type):type(TY_VOID,0);
    if(count>=0){
        unsigned checked=(unsigned)count<e->arg_count?(unsigned)count:e->arg_count;
        if(e->arg_count<(unsigned)count||(!variadic&&e->arg_count!=(unsigned)count))
            report_error(at,"wrong argument count for '%s'",name);
        for(i=0;i<checked;++i){
            if(old_style){
                Type actual=default_argument_promoted(e->args[i]->type),expected=default_argument_promoted(parameters[i]);
                if(numeric(actual)&&numeric(expected)&&actual.base!=expected.base)
                    report_error(e->args[i]->location,"argument %u does not match promoted K&R parameter",i+1);
            }
            if(!compatible_argument(parameters[i],e->args[i])){
                if(far_to_near_mismatch(parameters[i],e->args[i]))
                    report_error(e->args[i]->location,"incompatible argument %u for '%s': far pointer passed to near pointer parameter (declare parameter with __far)",i+1,name);
                else if(nested_far_mismatch(parameters[i],e->args[i]))
                    report_error(e->args[i]->location,"incompatible argument %u for '%s': nested near/far pointer mismatch",i+1,name);
                else
                    report_error(e->args[i]->location,"incompatible argument %u for '%s'",i+1,name);
            }else if(!old_style&&!structure_object(parameters[i]))e->args[i]=convert(e->args[i],parameters[i]);
        }
    }
    for(i=old_style||count<0?0:(unsigned)count;i<e->arg_count;++i)
        if(!structure_object(value_type(e->args[i]->type)))e->args[i]=convert(e->args[i],default_argument_promoted(e->args[i]->type));
    for(i=0;i<e->arg_count;++i){
        Type t=value_type(e->args[i]->type);
        if(structure_object(t)){
            if(!width(t))error_at(at,"aggregate argument requires a complete type");
            if(p->current)p->current->aggregate_abi=1;
        }
        if((variadic&&i>=(unsigned)count)||!register_parameter(i,t))stack_bytes+=argument_width(t);
    }
    if(structure_object(e->type)){
        char home[64];Symbol *result;
        if(!p->current||!width(e->type))error_at(at,"aggregate call requires a complete result type and function scope");
        snprintf(home,sizeof home,"$call_result_%u",p->symbol_count);
        result=new_symbol(p,home,e->type,at);
        result->owner=p->current->id;result->copy_temporary=1;
        e->third=new_expr(EX_OBJECT,at,e->type);e->third->symbol=result;
        p->current->aggregate_abi=1;
        stack_bytes+=2;
    }
    if(stack_bytes>STACK_BYTES)
        error_at(at,"function call exceeds stack byte budget (%u bytes including return address, limit %u)",stack_bytes,STACK_BYTES);
    return first_argument;
}
static Type variadic_cursor_type(void){return pointer_to(type(TY_CHAR,0));}
enum { BIT_FFS=1, BIT_CLZ, BIT_POPCOUNT, BIT_PARITY };
/* Library builtins use the target header ABI even without an include.
 * Bind the external symbol independently of an ordinary block-local name. */
static Symbol *library_builtin(Parser *p,const char *name,Symbol *declared,Location at)
{
    enum { NONE, INT, SIZE, VOID_PTR, FAR_VOID_PTR, CONST_FAR_VOID_PTR, CHAR_PTR, CONST_FAR_CHAR_PTR };
    static const struct { const char *name; unsigned result,params[3]; int variadic; } builtins[]={
        {"memset",VOID_PTR,{VOID_PTR,INT,SIZE}},
        {"memcpy",VOID_PTR,{VOID_PTR,CONST_FAR_VOID_PTR,SIZE}},
        {"memmove",VOID_PTR,{VOID_PTR,CONST_FAR_VOID_PTR,SIZE}},
        {"memcmp",INT,{CONST_FAR_VOID_PTR,CONST_FAR_VOID_PTR,SIZE}},
        {"memchr",FAR_VOID_PTR,{CONST_FAR_VOID_PTR,INT,SIZE}},
        {"strcmp",INT,{CONST_FAR_CHAR_PTR,CONST_FAR_CHAR_PTR}},
        {"strncmp",INT,{CONST_FAR_CHAR_PTR,CONST_FAR_CHAR_PTR,SIZE}},
        {"strlen",SIZE,{CONST_FAR_CHAR_PTR}},
        {"strcpy",CHAR_PTR,{CHAR_PTR,CONST_FAR_CHAR_PTR}},
        {"strncpy",CHAR_PTR,{CHAR_PTR,CONST_FAR_CHAR_PTR,SIZE}},
        {"strcat",CHAR_PTR,{CHAR_PTR,CONST_FAR_CHAR_PTR}},
        {"strncat",CHAR_PTR,{CHAR_PTR,CONST_FAR_CHAR_PTR,SIZE}},
        {"strspn",SIZE,{CONST_FAR_CHAR_PTR,CONST_FAR_CHAR_PTR}},
        {"strcspn",SIZE,{CONST_FAR_CHAR_PTR,CONST_FAR_CHAR_PTR}},
        {"printf",INT,{CONST_FAR_CHAR_PTR},1}
    };
    unsigned i,j;
    Type types[CONST_FAR_CHAR_PTR+1];
    Symbol candidate={0},*target=NULL;
    if(declared&&(!declared->function||declared->internal||declared->defined))return declared;
    for(i=0;i<sizeof builtins/sizeof *builtins;++i)if(!strcmp(name+10,builtins[i].name))break;
    if(i==sizeof builtins/sizeof *builtins)return declared;
    types[INT]=types[SIZE]=type(TY_INT,0);types[SIZE].is_unsigned=1;
    types[VOID_PTR]=type(TY_VOID,1);types[FAR_VOID_PTR]=far_type(types[VOID_PTR]);
    types[CONST_FAR_VOID_PTR]=types[FAR_VOID_PTR];types[CONST_FAR_VOID_PTR].constant=1;
    types[CHAR_PTR]=type(TY_CHAR,1);types[CHAR_PTR].is_plain_char=1;
    types[CONST_FAR_CHAR_PTR]=far_type(types[CHAR_PTR]);types[CONST_FAR_CHAR_PTR].constant=1;
    strcpy(candidate.name,name+10);candidate.type=types[builtins[i].result];
    candidate.function=1;candidate.external=1;candidate.variadic=builtins[i].variadic;
    for(j=0;j<3&&builtins[i].params[j];++j)candidate.params[j]=types[builtins[i].params[j]];
    candidate.param_count=(int)j;
    if(declared){
        if(!same_type(declared->type,candidate.type))error_at(at,"conflicting builtin declaration '%s'",name);
        merge_function(declared,&candidate,at);
    }
    for(j=0;j<p->symbol_count;++j){
        Symbol *s=&p->symbols[j];
        if(!s->owner&&!s->internal&&!strcmp(s->name,candidate.name)){target=s;break;}
    }
    if(target){
        if(!target->function||!same_type(target->type,candidate.type))error_at(at,"conflicting library declaration for '%s'",name);
        merge_function(target,&candidate,at);
    }else{
        target=new_symbol(p,candidate.name,candidate.type,at);
        strcpy(candidate.asm_name,candidate.name);*target=candidate;
        target->block_linkage=1;target->implicit_library=1;
    }
    return target;
}

static int bit_builtin(const char *name,Type *operand)
{
    static const char *operations[]={"ffs","clz","popcount","parity"};
    unsigned i;
    if(strncmp(name,"__builtin_",10))return 0;
    name+=10;
    for(i=0;i<sizeof operations/sizeof operations[0];++i){
        size_t length=strlen(operations[i]);
        const char *suffix;
        if(strncmp(name,operations[i],length))continue;
        suffix=name+length;
        if(!*suffix)*operand=type(TY_INT,0);
        else if(!strcmp(suffix,"l"))*operand=type(TY_LONG,0);
        else if(!strcmp(suffix,"ll"))*operand=type(TY_LONGLONG,0);
        else continue;
        operand->is_unsigned=i!=0;
        return i+1;
    }
    return 0;
}
/* Recognize folded integers and bit-mask trees, including wide shifts which
 * the ordinary word folder leaves intact. Do not evaluate side effects. */
static int bit_constant_tree(Expr *e)
{
    if(!numeric(e->type)||e->type.base==TY_FLOAT||e->type.base==TY_DOUBLE)return 0;
    if(e->kind==EX_INT)return 1;
    if(e->kind==EX_CAST||(e->kind==EX_UNARY&&
       (e->op=='+'||e->op=='~'||e->op=='!'||(e->op=='-'&&e->type.is_unsigned))))
        return bit_constant_tree(e->left);
    if(e->kind==EX_CHOOSE)
        return bit_constant_tree(e->left)&&bit_constant_tree(e->right)&&bit_constant_tree(e->third);
    if(e->kind!=EX_BINARY||!bit_constant_tree(e->left)||!bit_constant_tree(e->right))return 0;
    if(e->op==TOK_SHL||e->op==TOK_SHR){
        Type lhs=promoted(e->left->type);
        unsigned bits=8*width(lhs);
        uint64_t count=initializer_wide_constant(e->right,1);
        if(count>=bits)return 0;
        if(e->op==TOK_SHR||lhs.is_unsigned)return 1;
        return initializer_wide_constant(e->left,1)<(UINT64_C(1)<<(bits-1-count));
    }
    if(e->op=='+'||e->op=='-'||e->op=='*')
        return common_type(e->left->type,e->right->type).is_unsigned;
    return e->op=='|'||e->op=='&'||e->op=='^'||e->op==TOK_EQ||e->op==TOK_NE||
        e->op=='<'||e->op=='>'||e->op==TOK_LE||e->op==TOK_GE||e->op==TOK_LAND||e->op==TOK_LOR;
}
static Expr *fold_bit_builtin(Expr *call,Type operand,int operation)
{
    uint64_t bits;unsigned width_bits=width(operand)*8,result=0;
    Expr *value;
    if(!bit_constant_tree(call->args[0]))return call;
    bits=initializer_wide_constant(call->args[0],1);
    if(width_bits<64)bits&=(UINT64_C(1)<<width_bits)-1;
    if(operation==BIT_FFS){
        if(bits){result=1;while(!(bits&1)){++result;bits>>=1;}}
    }else if(operation==BIT_CLZ){
        uint64_t mask=UINT64_C(1)<<(width_bits-1);
        while(mask&&!(bits&mask)){++result;mask>>=1;}
    }else{
        while(bits){++result;bits&=bits-1;}
        if(operation==BIT_PARITY)result&=1;
    }
    value=new_expr(EX_INT,call->location,type(TY_INT,0));
    value->value=result;
    free_expression(call);return value;
}

static Expr *variadic_builtin(Parser *p,int start,Location at)
{
    Type cursor=variadic_cursor_type(),t;
    Expr *ap,*advance,*offset,*element;
    char name[64]="";
    lex(p);expect(p,'(',"'(' after variadic builtin");
    if(start){
        Function *f=p->current;
        Symbol *last;
        if(!f||!f->symbol->variadic||f->symbol->param_count<1)
            error_at(at,"va_start requires a variadic function");
        if(p->token.kind!=TOK_NAME||
           strcmp(p->token.name,f->symbol->param_names[f->symbol->param_count-1]))
            error_at(p->token.location,"va_start requires the last named parameter");
        last=find_symbol(p,p->token.name);
        if(!last||last->owner!=f->id||last->scope)
            error_at(p->token.location,"va_start parameter is shadowed");
        lex(p);expect(p,')',"')' after va_start");
        f->uses_varargs=1;
        return new_expr(EX_VA_START,at,cursor);
    }
    ap=assignment_expression(p);
    if(!writable(ap)||!same_type(unqualified_value(ap->type),cursor))
        error_at(ap->location,"va_arg requires a writable va_list");
    expect(p,',',"',' before va_arg type");
    t=named_declarator(p,declaration_base(p),name,1);
    expect(p,')',"')' after va_arg type");
    if(*name||t.array||(!t.pointers&&!numeric(t)&&!(structure_object(t)&&width(t)))||
       !same_type(unqualified_value(t),default_argument_promoted(t)))
        error_at(at,"va_arg requires a promoted scalar or pointer type");
    /* The assignment yields the advanced cursor and evaluates its lvalue once */
    advance=new_expr(EX_ASSIGN,at,cursor);
    advance->op='+';advance->left=ap;
    advance->right=new_expr(EX_INT,at,type(TY_INT,0));
    advance->right->value=argument_width(t);
    offset=new_expr(EX_BINARY,at,cursor);
    offset->op='-';offset->left=advance;
    offset->right=new_expr(EX_INT,at,type(TY_INT,0));
    offset->right->value=argument_width(t);
    element=new_expr(EX_DEREF,at,t);
    element->left=convert(offset,pointer_to(t));
    return element;
}
static Expr *unary_expression(Parser *p);
static Expr *unary(Parser *p)
{
    Expr *result;
    enter_nested_parse(p);
    result=unary_expression(p);
    --p->parse_depth;
    return result;
}

static Expr *unary_expression(Parser *p)
{
    Location at=p->token.location;Expr *e,*result;int op=p->token.kind;
    if(op==TOK_NAME&&!strcmp(p->token.name,"__builtin_va_start"))return variadic_builtin(p,1,at);
    if(op==TOK_NAME&&!strcmp(p->token.name,"__builtin_va_arg"))return variadic_builtin(p,0,at);
    if(op==TOK_NAME&&!strcmp(p->token.name,"__builtin_offsetof")){
        Type t;unsigned offset=0;char name[64]="";
        lex(p);expect(p,'(',"'('");t=named_declarator(p,declaration_base(p),name,1);expect(p,',',"','");
        for(;;){
            Member *m;
            if(!structure_object(t)||!t.structure||!t.structure->complete)error_at(at,"offsetof requires a complete aggregate");
            if(p->token.kind!=TOK_NAME)error_at(at,"expected offsetof member");
            for(m=t.structure->members;m&&strcmp(m->name,p->token.name);m=m->next){}
            if(!m)error_at(at,"unknown offsetof member");
            if(m->bit_width)error_at(at,"offsetof cannot be applied to a bit-field");
            offset+=m->offset;t=m->type;lex(p);
            while(accept(p,'[')){
                Expr *index=expression(p);unsigned n=initializer_constant(index,1);free_expression(index);
                if(!t.array)error_at(at,"offsetof subscript requires array member");
                t=array_element(t);offset+=n*width(t);expect(p,']',"']'");
            }
            if(!accept(p,'.'))break;
        }
        expect(p,')',"')'");result=new_expr(EX_INT,at,type(TY_INT,0));result->type.is_unsigned=1;result->value=offset;return result;
    }
    if(op==TOK_NAME&&(!strcmp(p->token.name,"__builtin_inff")||!strcmp(p->token.name,"__builtin_nanf"))){
        unsigned bits=!strcmp(p->token.name,"__builtin_inff")?0x7f800000u:0x7fc00000u;
        lex(p);expect(p,'(',"'('");expect(p,')',"')'");result=new_expr(EX_INT,at,type(TY_FLOAT,0));result->value=bits;return result;
    }
    if(accept(p,TOK_SIZEOF)){
        unsigned size;
        if(accept(p,'(')){
            if(type_start(p)){char name[64]="";Type t=named_declarator(p,declaration_base(p),name,1);size=width(t);}
            else {e=expression_allow_sram_array(p);size=expression_size(e);}
            expect(p,')',"')'");
        }else{e=unary(p);size=expression_size(e);}
        if(!size)error_at(at,"sizeof requires a complete object type");
        unsigned limit=object_extent_limit();
        if(size>limit)error_at(at,"sizeof operand exceeds %u bytes",limit);
        result=new_expr(EX_INT,at,type(size>65535?TY_LONG:TY_INT,0));result->type.is_unsigned=1;result->value=size;return result;
    }
    if(op=='+'||op=='-'||op=='!'||op=='~'||op=='&'||op=='*'||op==TOK_INC||op==TOK_DEC){
        lex(p);e=unary(p);
        reject_spanning_sram_array(e);
        if(op=='&'){
            if(e->kind==EX_BITFIELD)error_at(at,"cannot take the address of a bit-field");
            if(!function_type(e->type)&&!lvalue(e))error_at(at,"address-of requires an lvalue");
            if(e->kind==EX_OBJECT)e->symbol->address_taken=1;
            result=new_expr(EX_ADDRESS,at,pointer_to(e->type));result->left=e;return result;
        }
        if(op=='*'){
            Type t=value_type(e->type);if(!t.pointers)error_at(at,"dereference requires a pointer");
            t=pointed_type(t);result=new_expr(EX_DEREF,at,t);result->left=e;return result;
        }
        if(structure_object(value_type(e->type)))error_at(at,"struct values are not implemented yet");
        if(op==TOK_INC||op==TOK_DEC){
            pointer_element(e->type,at);
            if(!writable(e))error_at(at,"increment requires a writable scalar");
            result=new_expr(EX_PRE,at,e->type);result->op=op;result->left=e;return result;
        }
        if(op!='!'&&(!numeric(e->type)||(op=='~'&&(e->type.base==TY_FLOAT||e->type.base==TY_DOUBLE))))
            error_at(at,"invalid operand to unary arithmetic");
        if(e->kind==EX_INT&&e->type.base==TY_LONGLONG){
            uint64_t v=((uint64_t)e->value_high<<32)|e->value;
            if(op!='-'||e->type.is_unsigned||v!=(UINT64_C(1)<<63)){
                if(op=='-')v=0-v;else if(op=='~')v=~v;else if(op=='!'){v=!v;e->type=type(TY_INT,0);}
                e->value=(uint32_t)v;e->value_high=(uint32_t)(v>>32);return e;
            }
        }
        if(e->kind==EX_INT&&e->type.base!=TY_FLOAT&&e->type.base!=TY_DOUBLE&&e->type.base!=TY_LONGLONG){
            if(op!='!')e=convert(e,promoted(e->type));
            int64_t v=e->type.is_unsigned?(int64_t)e->value:
                (value_width(e->type)==4?(int32_t)e->value:(int16_t)e->value);
            if(op=='-')v=-v;else if(op=='!')v=!v;else if(op=='~')v=~v;
            if(!e->type.is_unsigned&&((value_width(e->type)==2&&(v < -32768||v>32767))||
                (value_width(e->type)==4&&(v<INT32_MIN||v>INT32_MAX))))error_at(at,"signed constant expression overflows");
            e->value=(uint32_t)v;if(value_width(e->type)==2)e->value&=0xFFFF;
            if(op=='!')e->type=type(TY_INT,0);return e;
        }
        result=new_expr(EX_UNARY,at,op=='!'?type(TY_INT,0):promoted(e->type));result->op=op;result->left=e;return result;
    }
    if(accept(p,'(')){
        if(type_start(p)){char name[64]="";Type t=named_declarator(p,declaration_base(p),name,1);expect(p,')',"')'");e=convert(unary(p),t);}
        else{e=expression_allow_sram_array(p);expect(p,')',"')'");}
    }else if(p->token.kind==TOK_NUMBER){
        e=new_expr(EX_INT,at,p->token.number_type);e->value=p->token.number;e->value_high=p->token.number_high;lex(p);
    }else if(p->token.kind==TOK_STRING){
        String *string=allocate(sizeof *string);string->bytes=allocate(4096);string->id=++p->string_count;
        do{
            if(string->size+p->token.length+1>4096)error_at(at,"concatenated string too long");
            memcpy(string->bytes+string->size,p->token.bytes,p->token.length);string->size+=p->token.length;lex(p);
        }while(p->token.kind==TOK_STRING);
        ++string->size;*p->string_tail=string;p->string_tail=&string->next;
        e=new_expr(EX_STRING,at,far_type(type(TY_CHAR,1)));e->type.is_plain_char=1;e->string=string;
    }else{
        Symbol *symbol,*target;char name[64];Type bit_operand;int implicit_old_style=0,bit_operation;
        if(p->token.kind!=TOK_NAME)error_at(at,"expected expression");
        strcpy(name,p->token.name);symbol=find_symbol(p,name);lex(p);
        if(!strncmp(name,"__builtin_",10))symbol=library_builtin(p,name,symbol,at);
        bit_operation=bit_builtin(name,&bit_operand);
        if(!symbol&&!strcmp(name,"__builtin_abort")){
            symbol=new_symbol(p,name,type(TY_VOID,0),at);
            symbol->function=1;symbol->external=1;
        }
        if(bit_operation&&!symbol){
            symbol=new_symbol(p,name,type(TY_INT,0),at);
            symbol->function=1;symbol->external=1;symbol->param_count=1;
            symbol->params[0]=bit_operand;
        }
        if(!symbol){
            Symbol *linked;
            if(p->token.kind!='(')error_at(at,"undeclared identifier '%s'",name);
            warning_at(at,"implicit declaration of function '%s' returning int",name);
            linked=linked_symbol(p,name);
            if(linked){
                if(!linked->function||!same_type(linked->type,type(TY_INT,0)))
                    error_at(at,"conflicting declaration '%s'",name);
                if(!linked->old_style)check_default_promotions(linked,at);
                symbol=linked;implicit_old_style=1;
            }else{
                symbol=new_symbol(p,name,type(TY_INT,0),at);
                symbol->function=1;symbol->param_count=-1;symbol->old_style=1;symbol->external=1;
            }
        }
        target=symbol->storage?symbol->storage:symbol;
        if(symbol->enumerator){e=new_expr(EX_INT,at,type(TY_INT,0));e->value=symbol->enum_value;}
        else{e=new_expr(EX_OBJECT,at,symbol->type);e->symbol=target;target->placement_used=1;}
        if(symbol->function&&p->token.kind=='('){
            if(target->interrupt)error_at(at,"interrupt handler '%s' cannot be called",symbol->name);
            if(p->current&&p->current->symbol->interrupt)error_at(at,"ordinary calls are not allowed in interrupt handlers");
            if(!strcmp(symbol->name,"main"))error_at(at,"main has a startup-only entry ABI and cannot be called");
            e->kind=EX_CALL;expect(p,'(',"'(' after function name");
            Type first_argument=call_arguments(p,e,symbol->name,implicit_old_style?-1:symbol->param_count,symbol->variadic,symbol->old_style,symbol->params);
            if(bit_operation&&e->arg_count==1&&symbol->param_count==1&&
               !symbol->defined&&!symbol->variadic&&same_type(symbol->type,type(TY_INT,0))&&
               same_type(symbol->params[0],bit_operand))
                e=fold_bit_builtin(e,bit_operand,bit_operation);
            if(e->kind==EX_CALL)target->called=1;
            /* A match within a valid near object is near. Keep the runtime
             * call's far ABI and narrow only the builtin expression result. */
            if(!strcmp(name,"__builtin_memchr")&&!strcmp(symbol->name,"memchr")&&
               first_argument.pointers&&!far_pointer(first_argument))
                e=convert(e,type(TY_VOID,1));
        }else if(symbol->function){
            if(target->interrupt||!strcmp(target->name,"main"))
                error_at(at,"function has a special entry ABI and cannot be used as a callback");
            target->address_taken=1;
            e->type=function_signature(symbol->type,symbol->old_style?-1:symbol->param_count,symbol->variadic,symbol->params);
        }
    }
    for(;;){
        if(accept(p,'(')){
            Type t=value_type(e->type);
            FunctionType *signature=t.signature;
            if(!function_pointer(t))error_at(e->location,"called expression must be a function pointer");
            if(p->current&&p->current->symbol->interrupt)error_at(at,"ordinary calls are not allowed in interrupt handlers");
            result=new_expr(EX_CALL,e->location,signature->result);result->left=e;
            call_arguments(p,result,"function pointer",signature->count,signature->variadic,signature->count<0,signature->parameters);
            e=result;
        }else if(accept(p,'[')){
            Expr *index=expression(p),*add;Type t=value_type(e->type);
            expect(p,']',"']'");if(!t.pointers)error_at(at,"indexing requires a pointer/array");
            reject_spanning_sram_array(index);
            if(!numeric(index->type)||index->type.base==TY_FLOAT||index->type.base==TY_DOUBLE)error_at(at,"array index requires an integer");
            index=pointer_offset(index);
            if(spanning_sram_array(e)){
                e=sram_subscript(e,index,pointed_type(t));
                continue;
            }
            add=new_expr(EX_BINARY,at,t);add->op='+';add->left=e;add->right=index;
            pointer_element(t,at);t=pointed_type(t);result=new_expr(EX_DEREF,at,t);result->left=add;e=result;
        }else if(p->token.kind=='.'||p->token.kind==TOK_ARROW){
            int access=p->token.kind;Location member_at=p->token.location;Type container=e->type,member_type;Member *member;
            lex(p);
            if(access==TOK_ARROW){
                container=value_type(container);
                if(container.base!=TY_STRUCT||container.pointers!=1||pointed_type(container).array)
                    error_at(member_at,"'->' requires a pointer to a struct");
                container=pointed_type(container);
            }else if(container.base!=TY_STRUCT||container.pointers||container.array||(!lvalue(e)&&e->kind!=EX_ASSIGN&&e->kind!=EX_MEMBER&&e->kind!=EX_CALL&&e->kind!=EX_COMMA))
                error_at(member_at,"'.' requires a struct object");
            if(!container.structure||!container.structure->complete)
                error_at(member_at,"member access requires a complete struct type");
            if(p->token.kind!=TOK_NAME)error_at(p->token.location,"expected member name");
            for(member=container.structure->members;member;member=member->next)
                if(!strcmp(member->name,p->token.name))break;
            if(!member)error_at(p->token.location,"%s '%s' has no member '%s'",container.structure->is_union?"union":"struct",container.structure->name,p->token.name);
            if(access=='.'&&(e->kind==EX_ASSIGN||e->kind==EX_COMMA)&&aggregate_has_array(container))e=aggregate_snapshot(p,e);
            member_type=member->type;member_type.banked=access=='.'?e->type.banked:container.banked;
            if(object_constant(container)){
                if(member_type.array)member_type=const_object(member_type);
                else if(member_type.pointers){
                    if(!pointer_bit(member_type.pointers))error_at(member_at,"too many pointer levels for const member");
                    member_type.pointer_constants|=pointer_bit(member_type.pointers);
                }else member_type.constant=1;
            }
            if(object_volatile(container))member_type=volatile_object(member_type);
            result=new_expr(EX_MEMBER,member_at,member_type);result->left=e;result->op=access;
            result->value=member->offset;e=member->bit_width?bitfield_expression(p,result,member):result;lex(p);
        }else if(p->token.kind==TOK_INC||p->token.kind==TOK_DEC){
            if(structure_object(value_type(e->type)))error_at(at,"struct values are not implemented yet");
            pointer_element(e->type,at);
            if(!writable(e))error_at(at,"increment requires a writable scalar");
            result=new_expr(EX_POST,at,e->type);result->op=p->token.kind;result->left=e;lex(p);e=result;
        }else break;
    }
    return e;
}
static int precedence(int op)
{
    switch(op){
    case '=':case TOK_ADDEQ:case TOK_SUBEQ:case TOK_MULEQ:case TOK_DIVEQ:case TOK_MODEQ:
    case TOK_ANDEQ:case TOK_OREQ:case TOK_XOREQ:case TOK_SHLEQ:case TOK_SHREQ:return 1;
    case '?':return 2;case TOK_LOR:return 3;case TOK_LAND:return 4;case '|':return 5;case '^':return 6;
    case '&':return 7;case TOK_EQ:case TOK_NE:return 8;case '<':case '>':case TOK_LE:case TOK_GE:return 9;
    case TOK_SHL:case TOK_SHR:return 10;case '+':case '-':return 11;case '*':case '/':case '%':return 12;
    default:return 0;
    }
}
static int assignment_op(int op)
{
    switch(op){case TOK_ADDEQ:return '+';case TOK_SUBEQ:return '-';case TOK_MULEQ:return '*';case TOK_DIVEQ:return '/';
    case TOK_MODEQ:return '%';case TOK_ANDEQ:return '&';case TOK_OREQ:return '|';case TOK_XOREQ:return '^';
    case TOK_SHLEQ:return TOK_SHL;case TOK_SHREQ:return TOK_SHR;default:return 0;}
}
static int comparison(int op){return op==TOK_EQ||op==TOK_NE||op=='<'||op=='>'||op==TOK_LE||op==TOK_GE;}
static uint32_t initializer_cast(uint32_t v,Type t);
static uint32_t literal_integer(Expr *e,Type t){return initializer_cast(initializer_cast(e->value,e->type),t);}
static int literal_operand(Expr *e){return e->kind==EX_INT&&numeric(e->type)&&e->type.base!=TY_FLOAT&&e->type.base!=TY_DOUBLE&&e->type.base!=TY_LONGLONG;}
static Expr *fold_literal(Expr *e,uint64_t v)
{
    unsigned size=width(e->type);
    e->kind=EX_INT;e->value=size==2?(uint32_t)v&0xFFFFu:(uint32_t)v;
    e->value_high=size==8?(uint32_t)(v>>32):0;
    e->left=e->right=NULL;e->op=0;return e;
}
static int fold_binary32_unary(Expr *e)
{
    Expr *input=e->left;
    uint32_t bits;
    if(e->kind!=EX_UNARY||!input||input->kind!=EX_INT||input->type.pointers||input->type.base!=TY_FLOAT)return 0;
    bits=input->value;
    if(e->op=='-')bits^=UINT32_C(0x80000000);
    else if(e->op=='!')bits=!(bits&UINT32_C(0x7fffffff));
    else if(e->op!='+')return 0;
    free_expression(input);fold_literal(e,bits);return 1;
}
/* Fold integer operators on literal operands, with initializer_constant's
 * target semantics. Division by zero, signed overflow and invalid shifts
 * stay run-time operations, so ordinary code is diagnosed exactly as before. */
static Expr *fold_integer(Expr *e)
{
    Type operands;uint32_t a,b;int64_t x,y,z;unsigned bits;int u,op=e->op;
    if(e->kind==EX_BINARY&&e->left->kind==EX_INT&&e->right->kind==EX_INT&&
       numeric(e->left->type)&&numeric(e->right->type)&&
       (e->left->type.base==TY_LONGLONG||e->right->type.base==TY_LONGLONG)&&
       e->left->type.base!=TY_DOUBLE&&e->left->type.base!=TY_FLOAT&&
       e->right->type.base!=TY_DOUBLE&&e->right->type.base!=TY_FLOAT){
        uint64_t lhs=initializer_cast64(((uint64_t)e->left->value_high<<32)|e->left->value,e->left->type);
        uint64_t rhs=initializer_cast64(((uint64_t)e->right->value_high<<32)|e->right->value,e->right->type);
        uint64_t result;
        if(op==TOK_LAND||op==TOK_LOR)result=op==TOK_LAND?lhs&&rhs:lhs||rhs;
        else{
            operands=op==TOK_SHL||op==TOK_SHR?promoted(e->left->type):common_type(e->left->type,e->right->type);
            if(integer_binary_constant(op,operands,lhs,rhs,&result))return e;
        }
        free_expression(e->left);free_expression(e->right);
        return fold_literal(e,initializer_cast64(result,e->type));
    }
    if(e->kind!=EX_BINARY||!literal_operand(e->left)||!literal_operand(e->right)||
       !numeric(e->type)||e->type.base==TY_FLOAT)return e;
    if(op==TOK_LAND||op==TOK_LOR){
        a=literal_integer(e->left,e->left->type)!=0;b=literal_integer(e->right,e->right->type)!=0;
        return fold_literal(e,op==TOK_LAND?a&&b:a||b);
    }
    operands=(op==TOK_SHL||op==TOK_SHR)?promoted(e->left->type):common_type(e->left->type,e->right->type);
    if(operands.pointers||operands.base==TY_FLOAT||operands.base==TY_LONGLONG)return e;
    bits=width(operands)*8;u=operands.is_unsigned;
    a=literal_integer(e->left,operands);
    b=literal_integer(e->right,(op==TOK_SHL||op==TOK_SHR)?promoted(e->right->type):operands);
    x=u?(int64_t)a:(int64_t)(int32_t)a;y=u?(int64_t)b:(int64_t)(int32_t)b;
    switch(op){
    case '+':z=x+y;break;case '-':z=x-y;break;
    case '*':if(u)return fold_literal(e,initializer_cast((uint32_t)((uint64_t)a*b),e->type));z=x*y;break;
    case '/':case '%':
        if(!y||(!u&&x==-(INT64_C(1)<<(bits-1))&&y==-1))return e;
        z=op=='/'?x/y:x%y;break;
    case '&':return fold_literal(e,initializer_cast(a&b,e->type));
    case '|':return fold_literal(e,initializer_cast(a|b,e->type));
    case '^':return fold_literal(e,initializer_cast(a^b,e->type));
    case TOK_EQ:return fold_literal(e,x==y);case TOK_NE:return fold_literal(e,x!=y);
    case '<':return fold_literal(e,x<y);case '>':return fold_literal(e,x>y);
    case TOK_LE:return fold_literal(e,x<=y);case TOK_GE:return fold_literal(e,x>=y);
    case TOK_SHL:case TOK_SHR:
        if((int32_t)b<0||b>=bits)return e;
        if(op==TOK_SHR)return fold_literal(e,initializer_cast((uint32_t)(u?(int64_t)(a>>b):x>>b),e->type));
        if(!u&&x<0)return e;
        z=x*(INT64_C(1)<<b);break;
    default:return e;
    }
    if(!u&&(z<-(INT64_C(1)<<(bits-1))||z>((INT64_C(1)<<(bits-1))-1)))return e;
    return fold_literal(e,initializer_cast((uint32_t)z,e->type));
}
static int binary32_literal(Expr *e,float *result,int finite)
{
    if(e->kind!=EX_INT||!numeric(e->type))return 0;
    if(e->type.base==TY_FLOAT){
        if(finite&&(e->value&UINT32_C(0x7f800000))==UINT32_C(0x7f800000))return 0;
        *result=initializer_float(e->value,e->type);return 1;
    }
    if(!literal_operand(e))return 0;
    *result=initializer_float(literal_integer(e,e->type),e->type);return 1;
}
static Expr *fold_runtime_binary(Expr *e)
{
    float left,right;uint32_t result;int finite=!comparison(e->op);
    if(e->kind==EX_BINARY&&numeric(e->type)&&
       (e->left->type.base==TY_FLOAT||e->right->type.base==TY_FLOAT)&&
       binary32_literal(e->left,&left,finite)&&binary32_literal(e->right,&right,finite)&&
       !binary32_constant_operation(e->op,left,right,&result)){
        free_expression(e->left);free_expression(e->right);
        return fold_literal(e,result);
    }
    return fold_integer(e);
}
static void check_arithmetic_operands(int op, Type a, Type b, int compound, Location at)
{
    a=value_type(a);b=value_type(b);
    if(op=='+'||op=='-'){
        if(a.pointers||b.pointers){
            int ai=numeric(a)&&a.base!=TY_FLOAT&&a.base!=TY_DOUBLE;
            int bi=numeric(b)&&b.base!=TY_FLOAT&&b.base!=TY_DOUBLE;
            if((a.pointers&&bi)||(!compound&&op=='+'&&ai&&b.pointers)||
               (!compound&&op=='-'&&a.pointers&&b.pointers))return;
            error_at(at,"invalid operands to pointer arithmetic");
        }
    }else if(op!='*'&&op!='/'&&op!='%'&&op!='&'&&op!='|'&&op!='^'&&
             op!=TOK_SHL&&op!=TOK_SHR)return;
    if(!numeric(a)||!numeric(b))error_at(at,"arithmetic requires numeric operands");
    if(op!='+'&&op!='-'&&op!='*'&&op!='/'&&(a.base==TY_FLOAT||b.base==TY_FLOAT||a.base==TY_DOUBLE||b.base==TY_DOUBLE))
        error_at(at,"operator requires integer operands");
}
static Expr *binary_expression(Parser *p,int minimum);
static int expression_calls(Expr *e)
{
    unsigned i;
    if(!e)return 0;
    if(e->kind==EX_CALL||expression_calls(e->left)||expression_calls(e->right)||expression_calls(e->third))return 1;
    for(i=0;i<e->arg_count;++i)if(expression_calls(e->args[i]))return 1;
    return 0;
}
static Expr *binary(Parser *p,int minimum)
{
    Expr *result;
    enter_nested_parse(p);
    result=binary_expression(p,minimum);
    --p->parse_depth;
    return result;
}

static Expr *binary_expression(Parser *p,int minimum)
{
    Expr *left=unary(p);
    while(precedence(p->token.kind)>=minimum){
        int op=p->token.kind,rank=precedence(op);Location at=p->token.location;Expr *node,*right;
        reject_spanning_sram_array(left);
        lex(p);
        if(op=='?'){
            Expr *yes=expression(p);expect(p,':',"':'");right=binary(p,2);
            if((function_pointer(value_type(yes->type))||function_pointer(value_type(right->type)))&&
               !compatible_argument(value_type(yes->type),right)&&
               !compatible_argument(value_type(right->type),yes))
                error_at(at,"incompatible function pointer conditional operands");
            node=new_expr(EX_CHOOSE,at,common_type(yes->type,right->type));node->left=left;
            node->right=convert(yes,node->type);node->third=convert(right,node->type);left=node;continue;
        }
        right=binary(p,rank+(rank==1?0:1));
        reject_spanning_sram_array(right);
        if(function_pointer(value_type(left->type))||function_pointer(value_type(right->type))){
            if(op=='<'||op=='>'||op==TOK_LE||op==TOK_GE)
                error_at(at,"function pointers support equality comparisons only");
            if((op==TOK_EQ||op==TOK_NE)&&
               !compatible_argument(value_type(left->type),right)&&
               !compatible_argument(value_type(right->type),left))
                error_at(at,"incompatible function pointer comparison");
        }
        if(op=='='&&!left->type.array&&!right->type.array&&
           structure_object(left->type)&&structure_object(right->type)){
            if(!lvalue(left)||aggregate_const_member(left->type))error_at(at,"aggregate assignment requires a modifiable lvalue");
            if(!width(left->type)||!width(right->type))error_at(at,"aggregate assignment requires complete types");
            if(!same_type(unqualified_value(left->type),unqualified_value(right->type)))
                error_at(at,"aggregate assignment requires the same type");
            node=new_expr(EX_ASSIGN,at,unqualified_value(left->type));node->left=left;node->right=right;
            left=node;continue;
        }
        if(structure_object(value_type(left->type))||structure_object(value_type(right->type)))
            error_at(at,"struct values are not implemented yet");
        check_arithmetic_operands(rank==1?assignment_op(op):op,left->type,right->type,rank==1,at);
        if((op==TOK_SHL||op==TOK_SHR||op==TOK_SHLEQ||op==TOK_SHREQ)&&
           !left->type.pointers&&left->type.base!=TY_LONGLONG&&
           !right->type.pointers&&right->type.base==TY_LONGLONG&&
           (right->kind!=EX_INT||(!right->value_high&&right->value<=65535u))){
            Type count=type(TY_INT,0);count.is_unsigned=1;
            right=convert(right,count);
        }
        if(numeric(value_type(left->type))&&numeric(value_type(right->type))&&
           !value_type(left->type).pointers&&!value_type(right->type).pointers&&
           common_type(left->type,right->type).base==TY_FLOAT&&
           (op=='+'||op=='-'||op=='*'||op=='/'||op==TOK_EQ||op==TOK_NE||
            op=='<'||op=='>'||op==TOK_LE||op==TOK_GE||
            op==TOK_ADDEQ||op==TOK_SUBEQ||op==TOK_MULEQ||op==TOK_DIVEQ)){
            if(rank!=1&&left->type.base==TY_LONGLONG)left=convert(left,type(TY_FLOAT,0));
            if(right->type.base==TY_LONGLONG)right=convert(right,type(TY_FLOAT,0));
        }
        if(op=='+'||op=='-'||op==TOK_ADDEQ||op==TOK_SUBEQ){
            pointer_element(left->type,at);pointer_element(right->type,at);
            if(op=='+'&&!value_type(left->type).pointers&&left->type.base==TY_LONGLONG&&
               value_type(right->type).pointers){
                Expr *swap=left;left=right;right=swap;
            }
            if(value_type(left->type).pointers&&!value_type(right->type).pointers)
                right=pointer_offset(right);
        }
        if(rank==1){
            Expr *save=NULL;
            if(!writable(left))error_at(at,"assignment requires a writable scalar");
            node=new_expr(EX_ASSIGN,at,left->type);node->left=left;node->op=assignment_op(op);
            /* A call on the RHS must finish before the compound read and write */
            if(node->op&&(left->kind==EX_BITFIELD||(p->current&&expression_calls(right)))){
                Type t=value_type(right->type);
                char name[64];Symbol *temporary;
                if(!p->current)error_at(at,"bit-field update requires function scope");
                snprintf(name,sizeof name,"$update_operand_%u",p->symbol_count);
                temporary=new_symbol(p,name,t,at);
                temporary->owner=p->current->id;temporary->copy_temporary=1;
                save=new_expr(EX_ASSIGN,at,t);
                save->left=new_expr(EX_OBJECT,at,t);save->left->symbol=temporary;
                save->right=right;
                right=new_expr(EX_OBJECT,at,t);right->symbol=temporary;
            }
            if(!node->op)right=assignment_convert(right,left->type);
            else if(left->kind==EX_OBJECT&&!left->type.pointers&&!left->type.is_bool&&
                    numeric(left->type)&&left->type.base!=TY_FLOAT&&left->type.base!=TY_DOUBLE&&
                    left->type.base!=TY_LONGLONG&&!right->type.pointers&&
                    (right->type.base==TY_LONGLONG||right->type.base==TY_DOUBLE)&&
                    node->op!=TOK_SHL&&node->op!=TOK_SHR){
                Type common=common_type(left->type,right->type);
                Expr *read=new_expr(EX_OBJECT,left->location,left->type);
                Expr *calculation=new_expr(EX_BINARY,at,common);
                read->symbol=left->symbol;
                calculation->op=node->op;calculation->left=read;calculation->right=right;
                right=assignment_convert(calculation,left->type);node->op=0;
            }
            node->right=right;
            if(save){
                Expr *sequence=new_expr(EX_COMMA,at,node->type);
                sequence->left=save;sequence->right=node;
                node=sequence;
            }
        }else{
            Type result=common_type(left->type,right->type);
            if(op==TOK_EQ||op==TOK_NE||op=='<'||op=='>'||op==TOK_LE||op==TOK_GE||op==TOK_LAND||op==TOK_LOR)result=type(TY_INT,0);
            if(op==TOK_SHL||op==TOK_SHR)result=promoted(left->type);
            if(op=='-'&&value_type(left->type).pointers&&value_type(right->type).pointers)result=type(far_pointer(common_type(left->type,right->type))?TY_LONG:TY_INT,0);
            node=new_expr(EX_BINARY,at,result);node->op=op;node->left=left;node->right=right;
            if(op=='-'&&value_type(left->type).pointers&&value_type(right->type).pointers){
                unsigned scale=width(pointed_type(value_type(left->type)));
                if(!same_type(unqualified_value(pointed_type(value_type(left->type))),unqualified_value(pointed_type(value_type(right->type)))))
                    error_at(at,"pointer subtraction requires compatible element types");
                if(scale>1){
                    Expr *difference=node,*divisor=new_expr(EX_INT,at,type(scale>32767&&node->type.base==TY_LONG?TY_LONG:TY_INT,0));divisor->value=scale;
                    node=new_expr(EX_BINARY,at,difference->type);node->op='/';node->left=difference;node->right=divisor;
                }
            }
        }
        left=fold_integer(node);
    }
    return left;
}
/* Unaddressed automatic scalars cannot be modified by a call. Recover the
 * normal compound form so private-local optimization can handle the update. */
static void restore_private_compound_expression(Expr **at)
{
    Expr *e=*at,*save,*update;
    Expr **right;
    unsigned i;
    if(!e)return;
    restore_private_compound_expression(&e->left);
    restore_private_compound_expression(&e->right);
    restore_private_compound_expression(&e->third);
    for(i=0;i<e->arg_count;++i)restore_private_compound_expression(&e->args[i]);
    if(e->kind!=EX_COMMA||!e->left||!e->right)return;
    save=e->left;update=e->right;
    if(save->kind!=EX_ASSIGN||save->left->kind!=EX_OBJECT||
       strncmp(save->left->symbol->name,"$update_operand_",16)||
       update->kind!=EX_ASSIGN||update->left->kind!=EX_OBJECT||
       !update->left->symbol->owner||update->left->symbol->address_taken)return;
    right=&update->right;
    if(!update->op){
        while((*right)->kind==EX_CAST)right=&(*right)->left;
        if((*right)->kind!=EX_BINARY)return;
        right=&(*right)->right;
    }
    if((*right)->kind!=EX_OBJECT||(*right)->symbol!=save->left->symbol)return;
    free_expression(*right);*right=save->right;save->right=NULL;
    e->right=NULL;free_expression(e);*at=update;
}
static void restore_private_compound_operands(Statement *s)
{
    for(;s;s=s->next){
        restore_private_compound_expression(&s->expression);
        restore_private_compound_expression(&s->step);
        restore_private_compound_operands(s->body);
        restore_private_compound_operands(s->alternate);
        restore_private_compound_operands(s->initial);
    }
}
static Expr *assignment_expression(Parser *p){return binary(p,1);}
static Expr *expression_allow_sram_array(Parser *p)
{
    Expr *e=assignment_expression(p);
    while(accept(p,',')){
        Expr *right=assignment_expression(p),*next=new_expr(EX_COMMA,e->location,unqualified_value(right->type));
        reject_spanning_sram_array(e);
        reject_spanning_sram_array(right);
        /* The aggregate is copied from the right operand's storage */
        if(structure_object(next->type))next->type.is_volatile=right->type.is_volatile;
        next->left=e;next->right=right;e=next;
    }
    return e;
}
static Expr *expression(Parser *p)
{
    Expr *e=expression_allow_sram_array(p);
    reject_spanning_sram_array(e);
    return e;
}

static Symbol *new_symbol(Parser *p,const char *name,Type t,Location at)
{
    Symbol *s;if(p->symbol_count==1024)error_at(at,"too many symbols");
    s=&p->symbols[p->symbol_count++];strcpy(s->name,name);strcpy(s->asm_name,name);s->type=t;return s;
}
static void ordinary_name_available(Parser *p,const char *name,Location at)
{
    unsigned owner=p->current?p->current->id:0;
    Symbol *s=find_symbol(p,name);Alias *a=find_alias(p,name);
    if((s&&s->owner==owner&&(s->scope==p->scope||(owner&&p->scope==1&&!s->scope)))||
       (a&&a->owner==owner&&a->scope==p->scope))
        error_at(at,"duplicate ordinary identifier '%s'",name);
}
static void add_alias(Parser *p,const char *name,Type t,Location at)
{
    unsigned owner=p->current?p->current->id:0;Alias *a=find_alias(p,name);
    if(a&&a->owner==owner&&a->scope==p->scope){
        if(!same_type(a->type,t))error_at(at,"conflicting typedef '%s'",name);
        return;
    }
    ordinary_name_available(p,name,at);
    if(p->alias_count==64)error_at(at,"too many typedefs");
    a=&p->aliases[p->alias_count++];strcpy(a->name,name);a->type=t;
    a->owner=p->current?p->current->id:0;a->scope=p->scope;a->active=1;
}
typedef struct DeclaratorPart {
    struct DeclaratorPart *next;
    Location location;
    unsigned size;
    FunctionType *signature;
    int pointer, far, constant, vol;
} DeclaratorPart;

/* Collect constructors from the base type outward. Suffixes outside a
 * parenthesized declarator apply before the constructors inside it. */
static void function_parameters(Parser *p,Symbol *candidate,Type *declared,int *old_definition,Location at);
static FunctionType *declarator_signature(Parser *p,Location at)
{
    Symbol *candidate=allocate(sizeof *candidate);
    Type *declared=allocate(sizeof candidate->params);
    FunctionType *signature;
    int definition=0;
    function_parameters(p,candidate,declared,&definition,at);
    if(definition)error_at(at,"invalid nested function parameter list");
    signature=function_signature(type(TY_VOID,0),candidate->param_count,candidate->variadic,candidate->params).signature;
    if(candidate->param_count>0){
        size_t bytes=(size_t)candidate->param_count*sizeof *candidate->param_names;
        signature->names=allocate(bytes);
        memcpy(signature->names,candidate->param_names,bytes);
    }
    free(declared);
    free(candidate);
    return signature;
}

typedef struct { int hint, force, never, noclone; } FunctionAttributes;
static int function_attributes(Parser *p,FunctionAttributes *attributes);

static DeclaratorPart *declarator_parts(Parser *p,char *name,int optional,int suffix,FunctionAttributes *attributes)
{
    DeclaratorPart *parts=NULL;
    Location at=p->token.location;
    enter_nested_parse(p);
    while(attributes&&p->token.kind==TOK_ATTRIBUTE)function_attributes(p,attributes);
    if(accept(p,'*')){
        DeclaratorPart *part=allocate(sizeof *part);
        part->pointer=1;
        for(;;){
            if(accept(p,TOK_FAR))part->far=1;
            else if(accept(p,TOK_CONST))part->constant=1;
            else if(accept(p,TOK_VOLATILE))part->vol=1;
            else if(attributes&&p->token.kind==TOK_ATTRIBUTE)function_attributes(p,attributes);
            else break;
        }
        part->next=declarator_parts(p,name,optional,suffix,attributes);
        --p->parse_depth;
        return part;
    }
    if(accept(p,'(')){
        parts=declarator_parts(p,name,optional,1,attributes);
        expect(p,')',"')'");
    }else if(p->token.kind==TOK_NAME){
        strcpy(name,p->token.name);lex(p);
    }else if(!optional)error_at(p->token.location,"expected declaration name");
    if((suffix||parts)&&accept(p,'(')){
        DeclaratorPart *part=allocate(sizeof *part);
        part->signature=declarator_signature(p,at);
        part->next=parts;parts=part;
    }
    while(accept(p,'[')){
        DeclaratorPart *part=allocate(sizeof *part);
        part->location=p->token.location;
        part->size=~0u;
        if(p->token.kind!=']'){
            Expr *n=expression(p);
            integer_constant_operands(n,"array size");
            part->size=initializer_constant(n,1);
            if(!numeric(n->type)||n->type.base==TY_FLOAT||n->type.base==TY_DOUBLE||!part->size||part->size>object_extent_limit())
                error_at(n->location,"array size must be a small positive integer constant");
            free_expression(n);
        }
        expect(p,']',"']'");
        part->next=parts;
        parts=part;
    }
    --p->parse_depth;
    return parts;
}
static Type named_declarator_mode(Parser *p,Type t,char *name,int optional,int suffix,FunctionAttributes *attributes)
{
    DeclaratorPart *part=declarator_parts(p,name,optional,suffix,attributes);
    while(part){
        DeclaratorPart *next=part->next;
        if(part->signature){
            if(t.array||function_type(t))error_at(p->token.location,"unsupported function return type");
            part->signature->result=t;
            t=type(TY_FUNCTION,0);t.signature=part->signature;
        }else if(part->pointer){
            t=pointer_to(t);
            if(!pointer_bit(t.pointers))error_at(part->location,"too many pointer levels");
            if(part->far)t=far_type(t);
            if(part->constant)t=const_object(t);
            if(part->vol)t=volatile_object(t);
        }else{
            if(t.array==~0u)error_at(part->location,"only the outer parameter dimension may be omitted");
            if(!width(t))error_at(part->location,"array element requires a complete object type");
            t.element=type_copy(t);
            t.array=part->size;
        }
        free(part);
        part=next;
    }
    return t;
}
static Type named_declarator(Parser *p,Type t,char *name,int optional)
{
    return named_declarator_mode(p,t,name,optional,0,NULL);
}
static void complete_array(Parser *p,Type t)
{
    if(t.array==~0u)error_at(p->token.location,"only the outer parameter dimension may be omitted");
}
static void structure_definition(Parser *p,Structure *record)
{
    Member **tail=&record->members;unsigned offset=0,count=0,bits_used=0;
    const char *kind=record->is_union?"union":"struct";
    if(record->complete||record->defining)error_at(p->token.location,"redefinition of %s '%s'",kind,record->name);
    record->defining=1;expect(p,'{',"'{'");
    while(p->token.kind!='}'){
        Type base;
        if(p->token.kind==TOK_EOF)error_at(p->token.location,"expected '}' in %s definition",kind);
        base=declaration_base(p);
        if(base.enum_tag&&accept(p,';'))continue;
        do{
            Type t=base;Member *member,*previous;unsigned size,align;Location at=p->token.location;
            member=allocate(sizeof *member);
            if(p->token.kind!=':')t=named_declarator(p,t,member->name,0);
            complete_array(p,t);
            for(previous=record->members;previous;previous=previous->next)
                if(!strcmp(previous->name,member->name))error_at(at,"duplicate member '%s'",member->name);
            if(accept(p,':')){
                Expr *length=assignment_expression(p);
                unsigned bits;
                if(t.base!=TY_INT||t.pointers||t.array||t.is_short||t.enum_tag)
                    error_at(at,"bit-field requires plain, signed, or unsigned int");
                integer_constant_operands(length,"bit-field width");
                bits=initializer_constant(length,1);free_expression(length);
                if(bits>16||(!bits&&*member->name))error_at(at,"invalid bit-field width");
                if(!bits){
                    bits_used=0;
                    if(!record->is_union)offset=(offset+1)&~1u;
                }else if(record->is_union){
                    if(offset<2)offset=2;
                }else{
                    if(!bits_used||bits_used+bits>16){
                        offset=(offset+1)&~1u;
                        if(offset>MAX_WRAM_OBJECT-2)error_at(at,"%s layout exceeds %u bytes",kind,MAX_WRAM_OBJECT);
                        offset+=2;bits_used=0;
                    }
                    member->offset=offset-2;
                    member->bit_shift=bits_used;
                    bits_used=(bits_used+bits)%16;
                }
                if(*member->name){
                    member->type=t;member->bit_width=bits;
                    *tail=member;tail=&member->next;++count;
                }else free(member);
                continue;
            }
            bits_used=0;
            size=width(t);if(!size)error_at(at,"member '%s' requires a complete object type",member->name);
            align=alignment(t);
            if(!record->is_union)offset=(offset+align-1)&~(align-1);
            if(size>MAX_WRAM_OBJECT-(record->is_union?0:offset))
                error_at(at,"%s layout exceeds %u bytes",kind,MAX_WRAM_OBJECT);
            member->type=t;member->offset=record->is_union?0:offset;
            if(record->is_union){if(size>offset)offset=size;}else offset+=size;
            *tail=member;tail=&member->next;++count;
        }while(accept(p,','));
        expect(p,';',record->is_union?"';' after union member":"';' after struct member");
    }
    if(!count)error_at(p->token.location,"empty %ss are not supported",kind);
    lex(p);record->size=(offset+1)&~1u;record->complete=1;record->defining=0;
}
#include "legacy_functions.inc"
static Symbol *linked_symbol(Parser *p,const char *name)
{
    unsigned i;Symbol *hidden=NULL;
    for(i=0;i<p->symbol_count;++i){
        Symbol *s=&p->symbols[i];
        if(!s->owner&&!strcmp(s->name,name)){
            if(!s->implicit_library)return s;
            hidden=s;
        }
    }
    return hidden;
}
static void merge_object_type(Symbol *s,Type *candidate,Location at)
{
    Type composite=s->type,other=*candidate;
    if(composite.array&&other.array&&(composite.array==~0u||other.array==~0u)){
        if(composite.array==~0u)composite.array=other.array;
        other.array=composite.array;
    }
    if(!same_type(composite,other)){
        report_error(at,pointer_far_mismatch(composite,other)?
                     "conflicting declaration '%s': near/far pointer mismatch":
                     "conflicting declaration '%s'",s->name);
        return;
    }
    s->type=composite;
    *candidate=composite;
}
static void block_function_declaration(Parser *p,Type t,const char *name,int storage_class,Location at)
{
    Symbol candidate={0},*storage=linked_symbol(p,name),*visible=find_symbol(p,name),*binding;
    Type declared[MAX_PARAMETERS];FunctionAttributes attributes={0};
    int old_definition=0;
    if(storage_class&&storage_class!=TOK_EXTERN)error_at(at,"invalid storage class for block function declaration");
    if(t.array)error_at(at,"unsupported function return type");
    strcpy(candidate.name,name);
    candidate.type=t;candidate.function=1;candidate.external=1;
    if(function_type(t)){
        FunctionType *signature=t.signature;
        candidate.type=t=signature->result;candidate.param_count=signature->count;
        candidate.variadic=signature->variadic;candidate.old_style=signature->count<0;
        if(signature->count>0)memcpy(candidate.params,signature->parameters,(size_t)signature->count*sizeof *candidate.params);
    }else function_parameters(p,&candidate,declared,&old_definition,at);
    while(p->token.kind==TOK_ATTRIBUTE)function_attributes(p,&attributes);
    candidate.noclone=attributes.noclone;candidate.noinline=attributes.never;candidate.always_inline=attributes.force;
    if(old_definition||p->token.kind=='{'||p->token.kind=='=')error_at(at,"block function declaration cannot define a function");
    if(storage){
        Symbol composite=*storage;
        if(!storage->function||!same_type(storage->type,t)||
           (storage->internal&&visible!=storage&&(!visible||visible->storage!=storage)))
            error_at(at,"conflicting declaration '%s'",name);
        merge_function(&composite,&candidate,at);
        if(storage->block_linkage)merge_function(storage,&candidate,at);
        storage->implicit_library=0;
        storage->noclone|=candidate.noclone;storage->noinline|=candidate.noinline;storage->always_inline|=candidate.always_inline;
    }else{
        storage=new_symbol(p,name,t,at);
        strcpy(candidate.asm_name,name);
        *storage=candidate;
        storage->block_linkage=1;
    }
    if(storage->noinline&&storage->always_inline)error_at(at,"always_inline conflicts with noinline for '%s'",name);
    if(visible&&(visible==storage||visible->storage==storage)){
        Symbol prior=*visible;
        merge_function(&prior,&candidate,at);
        candidate=prior;
        if(visible->owner==p->current->id&&visible->scope==p->scope){
            merge_function(visible,&candidate,at);
            return;
        }
    }
    ordinary_name_available(p,name,at);
    binding=new_symbol(p,name,t,at);
    *binding=candidate;
    binding->owner=p->current->id;binding->scope=p->scope;binding->active=1;
    binding->block_linkage=0;binding->storage=storage;
}
static void check_static_storage_size(Symbol *s,const char *name,unsigned limit,Location at)
{
    unsigned size=width(s->type);
    if(size<=limit)return;
    if(!s->type.banked&&!s->dpage&&!s->loram){
        if(size<=MAX_WRAM_OBJECT)
            error_at(at,"object size exceeds %u bytes for '%s' in ordinary 16-bit WRAM (bank $7E). "
                        "Use %s if the object can use far pointers.",
                     limit,name,size<=65536?"__hiram":"__xbankram");
        error_at(at,"object size exceeds %u bytes for '%s' in ordinary 16-bit WRAM (bank $7E) "
                    "and also exceeds expanded WRAM capacity.",limit,name);
    }
    error_at(at,"object size exceeds %u bytes",limit);
}
static void check_sram_object(Symbol *s,int initializer,Location at)
{
    unsigned bank=(unsigned)(s->wram-WRAM_SRAM_FIRST),size=width(s->type);
    unsigned available=sram_capacity-bank*sram_window_size;
    unsigned usable=available<sram_window_size?available:sram_window_size;
    if(initializer)error_at(at,"SRAM object '%s' cannot have an explicit initializer",s->name);
    if(!size||object_constant(s->type)||aggregate_const_member(s->type))
        error_at(at,"SRAM object '%s' requires a complete writable type",s->name);
    if(size<=usable)return;
    if(!s->type.array||size>available)
        error_at(at,"SRAM object '%s' does not fit starting at window %u (%u usable bytes in that window)",
                 s->name,bank,usable);
    if(sram_window_size%width(array_element(s->type)))
        error_at(at,"SRAM array '%s' would split an element across windows",s->name);
}
static Statement *local_declaration(Parser *p)
{
    int storage_class=0,is_typedef,is_static,loram,wram=WRAM_NONE;
    Type base;Statement *block=allocate(sizeof *block),**tail=&block->body;
    base=declaration_base_with_storage(p,&storage_class,1,&wram);
    if(wram>=WRAM_SRAM_FIRST)error_at(p->token.location,"__sram declarations require file scope");
    is_typedef=storage_class==TOK_TYPEDEF;
    is_static=storage_class==TOK_STATIC;
    if(wram&&!is_static&&storage_class!=TOK_EXTERN)
        error_at(p->token.location,"WRAM placement requires a static-storage object");
    loram=wram==WRAM_LORAM;
    if(loram)wram=WRAM_NONE;
    block->kind=ST_BLOCK;block->location=p->token.location;
    if(!wram&&!loram&&!is_typedef&&(base.base==TY_STRUCT||base.enum_tag)&&accept(p,';'))return block;
    do{
        Type t=base;Symbol *s;char name[64];Location at=p->token.location;
        t=named_declarator_mode(p,t,name,0,is_typedef,NULL);
        if(!is_typedef&&(function_type(t)||accept(p,'('))){
            if(wram||loram)error_at(at,"WRAM placement cannot qualify a function");
            block_function_declaration(p,t,name,storage_class,at);continue;
        }
        if(is_typedef){add_alias(p,name,t,at);continue;}
        {Alias *a=find_alias(p,name);if(a&&a->owner==p->current->id&&a->scope==p->scope)error_at(at,"duplicate local '%s'",name);}
        if(storage_class==TOK_EXTERN){
            Symbol *storage=linked_symbol(p,name);
            Symbol *visible=find_symbol(p,name);
            if(p->token.kind=='=')error_at(at,"block extern cannot have an initializer");
            if(storage){
                Symbol composite=*storage;
                Type declared=t;
                if(storage->function||storage->enumerator||
                   (storage->internal&&visible!=storage&&(!visible||visible->storage!=storage)))
                    error_at(at,"conflicting declaration '%s'",name);
                if(storage->wram!=wram)error_at(at,"conflicting WRAM placement for '%s'",name);
                if(loram&&!storage->loram)error_at(at,"conflicting WRAM placement for '%s'",name);
                merge_object_type(&composite,&declared,at);
                if(storage->block_linkage)storage->type=composite.type;
                if(visible&&(visible==storage||visible->storage==storage)){
                    Symbol visible_type=*visible;
                    merge_object_type(&visible_type,&t,at);
                }
            }else{
                storage=new_symbol(p,name,t,at);
                storage->external=1;
                storage->block_linkage=1;
                storage->wram=wram;storage->loram=loram;
                storage->type.banked=wram||(!loram&&object_constant(t)&&!object_volatile(t));
            }
            t.banked=storage->type.banked;
            if(visible&&visible->owner==p->current->id&&visible->scope==p->scope&&visible->storage==storage){
                visible->type=t;
                continue;
            }
            ordinary_name_available(p,name,at);
            s=new_symbol(p,name,t,at);
            s->owner=p->current->id;s->scope=p->scope;s->active=1;s->storage=storage;
            continue;
        }
        s=find_symbol(p,name);if(s&&p->current&&s->owner==p->current->id&&(s->scope==p->scope||(p->scope==1&&!s->scope)))error_at(at,"duplicate local '%s'",name);
        s=new_symbol(p,name,t,at);s->owner=p->current->id;s->scope=p->scope;s->active=1;
        if(is_static){
            Symbol *storage;char hidden[64];
            snprintf(hidden,sizeof hidden,"$static_%u",p->symbol_count);
            storage=new_symbol(p,hidden,t,at);storage->internal=1;storage->defined=1;s->storage=storage;
            snprintf(storage->asm_name,sizeof storage->asm_name,"%s__static_%u_%.40s",p->unit,p->symbol_count,name);
            storage->wram=wram;storage->loram=loram;
            storage->type.banked=wram||(!loram&&object_constant(t)&&!object_volatile(t)&&p->token.kind=='=');
            if(accept(p,'='))object_initializer(p,storage,0);
            if(!width(storage->type))error_at(at,"static local requires a complete type");
            check_static_storage_size(storage,name,object_size_limit(storage),at);
            s->type=storage->type;continue;
        }
        if(!width(t)&&!(t.array==~0u&&p->token.kind=='='))error_at(at,"local requires a complete type");
        if(width(t)>65534)error_at(at,"object size exceeds 65534 bytes");
        /* Y and frame sizes are even in the near-call ABI. Struct homes need
         * an even offset; reserve the skipped byte and retain an even frame. */
        s->offset=p->current->slots+(structure_object(t)?2:1);
        if(accept(p,'=')){
            Statement *init=object_initializer(p,s,1);*tail=init;while(*tail)tail=&(*tail)->next;
        }
        p->current->slots+=((width(s->type)+1)&~1u)+(structure_object(s->type)?2:0);
    }while(accept(p,','));
    expect(p,';',"';'");return block;
}
static void leave_scope(Parser *p)
{
    unsigned i;
    for(i=0;i<p->symbol_count;++i)if(p->symbols[i].owner==p->current->id&&p->symbols[i].scope==p->scope)p->symbols[i].active=0;
    for(i=0;i<p->tag_count;++i)if(p->tags[i].owner==p->current->id&&p->tags[i].scope==p->scope)p->tags[i].active=0;
    for(i=0;i<p->alias_count;++i)if(p->aliases[i].owner==p->current->id&&p->aliases[i].scope==p->scope)p->aliases[i].active=0;
    --p->scope;
}
static int label_start(Parser *p)
{
    Token saved=p->token;
    size_t position=p->position;
    Location at=here(p);
    int label;
    if(saved.kind!=TOK_NAME)return 0;
    lex(p);
    label=p->token.kind==':';
    p->token=saved;p->position=position;p->path=at.path;p->line=at.line;p->column=at.column;
    return label;
}
static unsigned jump_label(Parser *p,int defining)
{
    JumpLabel *label;
    Function *f=p->current;
    if(p->token.kind!=TOK_NAME)error_at(p->token.location,"expected label name");
    for(label=f->jump_labels;label;label=label->next)
        if(!strcmp(label->name,p->token.name))break;
    if(!label){
        label=allocate(sizeof *label);
        strcpy(label->name,p->token.name);
        label->location=p->token.location;label->id=++f->jump_label_count;
        label->next=f->jump_labels;f->jump_labels=label;
    }
    if(defining){
        if(label->defined)error_at(p->token.location,"duplicate label '%s'",label->name);
        label->defined=1;
    }
    lex(p);
    return label->id;
}
static void finish_jump_labels(Function *f)
{
    while(f->jump_labels){
        JumpLabel *label=f->jump_labels;
        if(!label->defined)report_error(label->location,"undefined label '%s'",label->name);
        f->jump_labels=label->next;
        free(label);
    }
}
static void unwind_scopes(Parser *p,unsigned target_scope)
{
    while(p->scope>target_scope)leave_scope(p);
}
static void skip_to_statement_sync(Parser *p,size_t start_position,int start_kind)
{
    unsigned braces=0;
    Recovery *saved=active_recovery;
    active_recovery=NULL;
    if(p->token.kind!=TOK_EOF&&p->position==start_position&&p->token.kind==start_kind&&p->token.kind!='}')
        lex(p);
    while(p->token.kind!=TOK_EOF){
        if(p->token.kind=='{'){++braces;lex(p);continue;}
        if(p->token.kind=='}'){
            if(!braces)break;
            --braces;lex(p);
            if(!braces)break;
            continue;
        }
        if(p->token.kind==';'&&!braces){lex(p);break;}
        lex(p);
    }
    active_recovery=saved;
}
static Statement *statement(Parser *p);
static void parse_block_item(Parser *p,Statement ***tail)
{
    Statement *item=type_start(p)&&!label_start(p)?local_declaration(p):statement(p);
    **tail=item;
    *tail=&item->next;
}
static Statement *statement(Parser *p)
{
    Statement *s=allocate(sizeof *s);s->location=p->token.location;s->id=++p->next_id;
    if(accept(p,TOK_GOTO)){
        s->kind=ST_GOTO;s->jump_label=jump_label(p,0);expect(p,';',"';'");
    }else if(label_start(p)){
        s->kind=ST_LABEL;s->jump_label=jump_label(p,1);expect(p,':',"':'");s->body=statement(p);
    }else if(accept(p,'{')){
        Statement **volatile tail=&s->body;
        unsigned volatile saved_scope;
        unsigned volatile saved_loop=p->loop_depth;
        unsigned volatile saved_parse=p->parse_depth;
        Statement *volatile saved_switch=p->current_switch;
        ++p->scope;saved_scope=p->scope;s->kind=ST_BLOCK;
        while(p->token.kind!='}'){
            Recovery frame;
            size_t volatile start_pos=p->position;
            int volatile start_kind=p->token.kind;
            if(p->token.kind==TOK_EOF){
                report_error(p->token.location,"expected '}'");
                break;
            }
            frame.previous=active_recovery;
            active_recovery=&frame;
            if(setjmp(frame.env)==0){
                Statement **current_tail=(Statement **)tail;
                parse_block_item(p,&current_tail);
                tail=current_tail;
                active_recovery=frame.previous;
            }else{
                active_recovery=frame.previous;
                unwind_scopes(p,saved_scope);
                p->loop_depth=saved_loop;
                p->parse_depth=saved_parse;
                p->current_switch=(Statement *)saved_switch;
                skip_to_statement_sync(p,start_pos,start_kind);
            }
        }
        leave_scope(p);
        if(p->token.kind=='}')lex(p);
    }else if(accept(p,TOK_SWITCH)){
        Statement *outer=p->current_switch;Expr *control;
        s->kind=ST_SWITCH;expect(p,'(',"'(' after switch");control=expression(p);expect(p,')',"')'");
        if(!numeric(control->type)||control->type.base==TY_FLOAT||control->type.base==TY_DOUBLE)
            error_at(control->location,"switch requires an integer expression");
        s->expression=convert(control,promoted(control->type));
        p->current_switch=s;s->body=statement(p);p->current_switch=outer;
    }else if(p->token.kind==TOK_CASE||p->token.kind==TOK_DEFAULT){
        Statement *previous,**tail;Expr *constant;
        if(!p->current_switch)error_at(s->location,"case/default outside switch");
        s->kind=ST_CASE;s->is_default=accept(p,TOK_DEFAULT);
        if(!s->is_default){
            lex(p);constant=expression(p);integer_constant_operands(constant,"case label");
            {Type control=p->current_switch->expression->type;
             uint64_t value=initializer_cast64(initializer_wide_constant(constant,1),control);
             s->case_value=(uint32_t)value;
             s->case_value_high=reg_width(control)==8?(uint32_t)(value>>32):0;}
            free_expression(constant);
        }
        expect(p,':',"':' after case/default");tail=&p->current_switch->cases;
        for(previous=*tail;previous;previous=previous->case_next){
            if(s->is_default&&previous->is_default)error_at(s->location,"duplicate default label");
            if(!s->is_default&&!previous->is_default&&s->case_value==previous->case_value&&
               s->case_value_high==previous->case_value_high)
                error_at(s->location,"duplicate case value after conversion");
            tail=&previous->case_next;
        }
        *tail=s;s->body=statement(p);
    }else if(accept(p,';'))s->kind=ST_EMPTY;
    else if(accept(p,TOK_IF)){
        s->kind=ST_IF;expect(p,'(',"'('");s->expression=expression(p);expect(p,')',"')'");s->body=statement(p);
        if(accept(p,TOK_ELSE))s->alternate=statement(p);
    }else if(accept(p,TOK_WHILE)){
        s->kind=ST_WHILE;expect(p,'(',"'('");s->expression=expression(p);expect(p,')',"')'");++p->loop_depth;s->body=statement(p);--p->loop_depth;
    }else if(accept(p,TOK_FOR)){
        s->kind=ST_FOR;expect(p,'(',"'('");++p->scope;
        if(type_start(p))s->initial=local_declaration(p);
        else if(!accept(p,';')){s->initial=allocate(sizeof *s->initial);s->initial->kind=ST_EXPR;s->initial->expression=expression(p);expect(p,';',"';'");}
        if(!accept(p,';')){s->expression=expression(p);expect(p,';',"';'");}
        if(!accept(p,')')){s->step=expression(p);expect(p,')',"')'");}++p->loop_depth;s->body=statement(p);--p->loop_depth;
        leave_scope(p);
    }else if(accept(p,TOK_DO)){
        s->kind=ST_DO;++p->loop_depth;s->body=statement(p);--p->loop_depth;expect(p,TOK_WHILE,"while");expect(p,'(',"'('");s->expression=expression(p);expect(p,')',"')'");expect(p,';',"';'");
    }else if(accept(p,TOK_RETURN)){
        s->kind=ST_RETURN;
        if(p->current->symbol->interrupt&&p->token.kind!=';')error_at(s->location,"interrupt handler cannot return a value");
        if(!accept(p,';')){
            Type t=p->current->symbol->type;
            Expr *value=expression(p);
            if(structure_object(t)){
                Expr *destination,*copy;
                if(!same_type(unqualified_value(t),unqualified_value(value->type)))
                    report_error(s->location,"incompatible aggregate return");
                destination=new_expr(EX_DEREF,s->location,t);
                destination->left=new_expr(EX_RESULT_ADDR,s->location,pointer_to(t));
                copy=new_expr(EX_ASSIGN,s->location,t);copy->left=destination;copy->right=value;
                s->expression=copy;
            }else s->expression=assignment_convert(value,t);
            expect(p,';',"';'");
        }
        else if(p->current->symbol->type.base!=TY_VOID)report_error(s->location,"non-void return needs a value");
    }else if(accept(p,TOK_BREAK)){
        if(!p->loop_depth&&!p->current_switch)report_error(s->location,"break outside loop or switch");
        s->kind=ST_BREAK;expect(p,';',"';'");}
    else if(accept(p,TOK_CONTINUE)){
        if(!p->loop_depth)report_error(s->location,"continue outside loop");
        s->kind=ST_CONTINUE;expect(p,';',"';'");}
    else if(basic_asm_name(p)){
        Expr *literal;Symbol *barrier;const char *instruction;
        lex(p);
        accept(p,TOK_VOLATILE);
        expect(p,'(',"'(' after __asm");
        if(p->token.kind!=TOK_STRING)error_at(p->token.location,"basic __asm requires a string literal");
        literal=unary(p);expect(p,')',"')' after basic __asm string");expect(p,';',"';'");
        if(literal->kind!=EX_STRING||strlen((char *)literal->string->bytes)+1!=literal->string->size)
            error_at(s->location,"basic __asm requires an instruction string without embedded NULs");
        /* Restrict basic asm to instructions that leave the C machine state
         * intact. Keep a call-shaped barrier in the optimizer, but emit no call. */
        for(instruction=(char *)literal->string->bytes;*instruction;){
            while(isspace((unsigned char)*instruction))++instruction;
            if(!*instruction)break;
            if((strncmp(instruction,"wai",3)&&strncmp(instruction,"nop",3))||
               (instruction[3]&&!isspace((unsigned char)instruction[3])))
                error_at(s->location,"basic __asm supports only wai and nop");
            instruction+=3;
        }
        if(p->current->symbol->interrupt)error_at(s->location,"basic __asm is not supported in interrupt handlers");
        barrier=find_symbol(p,"$basic_asm");
        if(!barrier){barrier=new_symbol(p,"$basic_asm",type(TY_VOID,0),s->location);barrier->function=1;barrier->noinline=1;}
        literal->kind=EX_CALL;literal->type=barrier->type;literal->symbol=barrier;
        s->kind=ST_EXPR;s->expression=literal;
    }
    else{s->kind=ST_EXPR;s->expression=expression(p);expect(p,';',"';'");}
    return s;
}
#include "initializer.inc"
static void integer_constant_operands(Expr *e,const char *context)
{
    if(!numeric(e->type)||e->type.base==TY_FLOAT||e->type.base==TY_DOUBLE)
        error_at(e->location,"%s requires an integer constant expression",context);
    if(e->kind==EX_INT)return;
    if(e->kind!=EX_UNARY&&e->kind!=EX_CAST&&e->kind!=EX_BINARY&&e->kind!=EX_CHOOSE)
        error_at(e->location,"%s requires an integer constant expression",context);
    if(e->kind==EX_CAST&&e->left->kind==EX_INT&&e->left->type.base==TY_FLOAT)return;
    if(e->left)integer_constant_operands(e->left,context);
    if(e->right)integer_constant_operands(e->right,context);
    if(e->third)integer_constant_operands(e->third,context);
}
static Type enum_specifier(Parser *p)
{
    Type t=type(TY_INT,0);Structure *record=NULL;char name[64]="";
    unsigned i,owner=p->current?p->current->id:0;Location at=p->token.location;
    if(p->token.kind==TOK_NAME){strcpy(name,p->token.name);lex(p);}
    if(*name)for(i=p->tag_count;i;--i)if(p->tags[i-1].active&&!strcmp(p->tags[i-1].name,name)){
        record=&p->tags[i-1];break;
    }
    if(p->token.kind=='{'){
        int32_t next=0;
        if(record&&(record->owner!=owner||record->scope!=p->scope))record=NULL;
        if(record)error_at(at,"duplicate or conflicting enum tag '%s'",name);
        if(p->tag_count==64)error_at(at,"too many tags");
        record=&p->tags[p->tag_count++];strcpy(record->name,name);
        record->owner=owner;record->scope=p->scope;record->active=1;record->is_enum=1;record->defining=1;
        lex(p);if(p->token.kind=='}')error_at(at,"enum requires at least one enumerator");
        for(;;){
            Symbol *constant;int64_t value=next;char identifier[64];Location item=p->token.location;
            if(p->token.kind!=TOK_NAME)error_at(item,"expected enumerator name");
            strcpy(identifier,p->token.name);ordinary_name_available(p,identifier,item);lex(p);
            if(accept(p,'=')){
                Expr *e=assignment_expression(p);uint32_t bits;
                integer_constant_operands(e,"enumerator");
                bits=initializer_constant(e,1);
                value=e->type.is_unsigned?(int64_t)bits:(int64_t)(int32_t)bits;
                free_expression(e);
            }
            if(value < -32768||value>32767)error_at(item,"enumerator value is outside signed 16-bit int range");
            constant=new_symbol(p,identifier,type(TY_INT,0),item);constant->enumerator=1;
            constant->enum_value=(uint32_t)(int32_t)value;constant->owner=owner;
            constant->scope=p->scope;constant->active=1;next=(int32_t)value+1;
            if(!accept(p,','))break;
            if(p->token.kind=='}')break;
        }
        expect(p,'}',"'}' after enumerators");record->defining=0;record->complete=1;record->size=2;
    }else if(!*name||!record||!record->is_enum||!record->complete){
        error_at(at,"enum tag requires a prior complete definition");
    }
    /* Lower enum objects and expressions to the existing signed int ABI */
    t.enum_tag=(unsigned)(record-p->tags)+1;return t;
}

static int function_attributes(Parser *p,FunctionAttributes *attributes)
{
    if(accept(p,TOK_INLINE)){attributes->hint=1;return 1;}
    if(accept(p,TOK_FORCEINLINE)){attributes->force=1;return 1;}
    if(accept(p,TOK_NOINLINE)){attributes->never=1;return 1;}
    if(!accept(p,TOK_ATTRIBUTE))return 0;
    expect(p,'(',"'(' after __attribute__");expect(p,'(',"second '(' after __attribute__");
    if(accept(p,')')){expect(p,')',"second ')' after function attributes");return 1;}
    do{
        if(p->token.kind!=TOK_NAME)error_at(p->token.location,"expected function attribute name");
        if(!strcmp(p->token.name,"always_inline")||!strcmp(p->token.name,"__always_inline__"))attributes->force=1;
        else if(!strcmp(p->token.name,"noinline")||!strcmp(p->token.name,"__noinline__"))attributes->never=1;
        else if(!strcmp(p->token.name,"noclone")||!strcmp(p->token.name,"__noclone__"))attributes->noclone=1;
        else error_at(p->token.location,"unsupported function attribute '%s'",p->token.name);
        lex(p);
    }while(accept(p,','));
    expect(p,')',"')' after function attributes");expect(p,')',"second ')' after function attributes");return 1;
}

static void parse_top_level(Parser *p,int *has_main)
{
    int storage_class=0,is_typedef,is_extern,is_static,dpage=0,loram=0,definition=0,interrupt=INT_NONE;
    int constant=0,vol=0,wram=WRAM_NONE;Type base;FunctionAttributes shared={0};
    for(;;){if(storage_specifier(p,&storage_class,0)){}
        else if(accept(p,TOK_DPAGE))dpage=1;
        else if(accept(p,TOK_LORAM))loram=1;
        else if(wram_specifier(p,&wram)){}
        else if(accept(p,TOK_CONST))constant=1;
        else if(accept(p,TOK_VOLATILE))vol=1;
        else if(function_attributes(p,&shared)){}
        else if(accept(p,TOK_INTERRUPT)){
            if(interrupt)error_at(p->token.location,"duplicate interrupt attribute");
            expect(p,'(',"'(' after __interrupt");
            if(p->token.kind!=TOK_NAME)error_at(p->token.location,"expected nmi, irq, brk or cop");
            if(!strcmp(p->token.name,"nmi"))interrupt=INT_NMI;
            else if(!strcmp(p->token.name,"irq"))interrupt=INT_IRQ;
            else if(!strcmp(p->token.name,"brk"))interrupt=INT_BRK;
            else if(!strcmp(p->token.name,"cop"))interrupt=INT_COP;
            else error_at(p->token.location,"unknown interrupt kind '%s'",p->token.name);
            lex(p);expect(p,')',"')' after interrupt kind");
        }else break;}
    base=declaration_base_with_storage(p,&storage_class,0,&wram);
    if(wram==WRAM_LORAM){loram=1;wram=WRAM_NONE;}
    is_typedef=storage_class==TOK_TYPEDEF;
    is_extern=storage_class==TOK_EXTERN;
    is_static=storage_class==TOK_STATIC;
    if(loram&&(is_typedef||dpage||interrupt))error_at(p->token.location,"__loram requires an ordinary static-storage object");
    if(wram&&(is_typedef||dpage||loram||interrupt||
              (wram>=WRAM_SRAM_FIRST&&storage_class&&!is_extern&&!is_static)))
        error_at(p->token.location,"conflicting %s placement or storage class",wram>=WRAM_SRAM_FIRST?"SRAM":"WRAM");
    if(interrupt&&(is_typedef||is_static||dpage))error_at(p->token.location,"interrupt handler must have external function linkage");
    if(constant)base=const_object(base);if(vol)base=volatile_object(base);
    while(function_attributes(p,&shared)){}
    if((base.base==TY_STRUCT||base.enum_tag)&&!is_typedef&&!is_extern&&!is_static&&!dpage&&!loram&&!wram&&!interrupt&&accept(p,';')){
        if(shared.noclone)error_at(p->token.location,"noclone requires a function");
        return;
    }
    do{
        Type t=base,declared_params[MAX_PARAMETERS];int old_definition=0;char name[64];Location at=p->token.location;Symbol candidate={0},*s;
        FunctionAttributes attributes=shared;
        t=named_declarator_mode(p,t,name,0,is_typedef,&attributes);
        if(is_typedef){
            if(attributes.noclone)error_at(at,"noclone requires a function");
            if(attributes.hint||attributes.force||attributes.never)error_at(at,"inlining specifiers require a function");
            add_alias(p,name,t,at);continue;
        }
        strcpy(candidate.name,name);candidate.type=t;candidate.external=is_extern;candidate.dpage=dpage;candidate.loram=loram;candidate.wram=wram;candidate.internal=is_static;candidate.interrupt=interrupt;
        if(function_type(t)||accept(p,'(')){
            if(loram)error_at(at,"__loram cannot qualify a function");
            if(wram)error_at(at,"%s placement cannot qualify a function",wram>=WRAM_SRAM_FIRST?"SRAM":"WRAM");
            if(t.array)error_at(at,"function cannot return an array");
            candidate.function=1;
            if(function_type(t)){
                FunctionType *signature=t.signature;
                candidate.type=t=signature->result;
                candidate.param_count=signature->count;
                candidate.variadic=signature->variadic;
                candidate.old_style=signature->count<0;
                if(signature->count<0&&p->token.kind=='{')candidate.param_count=0;
                if(signature->count>0){
                    size_t count=(size_t)signature->count;
                    memcpy(candidate.params,signature->parameters,count*sizeof *candidate.params);
                    memcpy(declared_params,signature->parameters,count*sizeof *declared_params);
                    memcpy(candidate.param_names,signature->names,count*sizeof *candidate.param_names);
                }
            }else function_parameters(p,&candidate,declared_params,&old_definition,at);
        }else{
            candidate.defined=!is_extern;
            candidate.type.banked=wram||(!loram&&object_constant(t)&&!object_volatile(t)&&(is_extern||p->token.kind=='='));
            if(p->runtime_objects){
                const char *item=p->runtime_objects;size_t length=strlen(name);
                while(item&&*item){
                    const char *end=strchr(item,',');size_t n=end?(size_t)(end-item):strlen(item);
                    if(n==length&&!strncmp(item,name,n)){
                        if(dpage||loram||wram||object_constant(t)||p->token.kind=='=')
                            error_at(at,"runtime object requires uninitialized mutable banked storage");
                        candidate.runtime_ram=1;candidate.type.banked=1;break;
                    }
                    item=end?end+1:NULL;
                }
            }
            if(wram>=WRAM_SRAM_FIRST)check_sram_object(&candidate,p->token.kind=='=',at);
            else check_static_storage_size(&candidate,name,object_size_limit(&candidate),at);
        }
        {
         while(function_attributes(p,&attributes)){}
         if(attributes.noclone&&!candidate.function)error_at(at,"noclone requires a function");
         candidate.noclone=attributes.noclone;
         if((attributes.hint||attributes.force||attributes.never)&&!candidate.function)error_at(at,"inlining specifiers require a function");
         candidate.inline_hint=attributes.hint;candidate.always_inline=attributes.force;candidate.noinline=attributes.never;
         /* ISO C: any extern or non-inline file-scope declaration supplies
          * the external definition; otherwise an external inline body is
          * available for substitution only. */
         candidate.inline_external=candidate.function&&(is_extern||!attributes.hint);
        }
        s=linked_symbol(p,name);
        if(s&&s->implicit_library&&is_static)s=NULL;
        if(s)s->implicit_library=0;
        if(s&&s->enumerator)error_at(at,"enumerator '%s' cannot be redeclared as an object/function",name);
        if(find_alias(p,name))error_at(at,"identifier '%s' was declared as a typedef",name);
        if(interrupt&&(!candidate.function||t.base!=TY_VOID||t.pointers||candidate.param_count!=0||candidate.variadic||candidate.old_style))
            error_at(at,"interrupt handler must be void name(void)");
        if(s){
            int block_linkage=s->block_linkage;
            if(s->wram!=wram)
                error_at(at,"conflicting %s placement for '%s'",
                         wram>=WRAM_SRAM_FIRST||s->wram>=WRAM_SRAM_FIRST?"SRAM":"WRAM",name);
            if((loram&&s->dpage)||(dpage&&s->loram))error_at(at,"__loram conflicts with __dpage");
            if(loram&&!s->loram&&(s->defined||s->placement_used))error_at(at,"__loram must precede the definition and uses of '%s'",name);
            if(loram){s->loram=1;s->type.banked=0;}
            if((interrupt||s->interrupt)&&(is_static||s->internal||dpage))error_at(at,"interrupt handler must have external function linkage");
            if(interrupt&&s->interrupt&&interrupt!=s->interrupt)error_at(at,"conflicting interrupt attribute");
            if(interrupt&&s->called)error_at(at,"interrupt handler was previously called");
            if(interrupt&&s->defined&&!s->interrupt)error_at(at,"interrupt attribute must precede the definition");
            if(interrupt)s->interrupt=interrupt;
            if(s->block_linkage&&is_static)error_at(at,"conflicting linkage for '%s'",name);
            s->block_linkage=0;
            if(!candidate.function&&!s->function)merge_object_type(s,&candidate.type,at);
            if(s->function!=candidate.function)error_at(at,"conflicting declaration '%s'",name);
            if(!same_type(s->type,candidate.type))
                report_error(at,pointer_far_mismatch(s->type,candidate.type)?
                             "conflicting declaration '%s': near/far pointer mismatch":
                             "conflicting declaration '%s'",name);
            if(candidate.function){
                merge_function(s,&candidate,at);
                if(block_linkage&&candidate.old_style&&candidate.param_count<0){
                    s->old_style=1;s->param_count=-1;
                }
            }
            s->inline_hint|=candidate.inline_hint;s->always_inline|=candidate.always_inline;
            s->noclone|=candidate.noclone;s->noinline|=candidate.noinline;s->inline_external|=candidate.inline_external;
            if(!candidate.function&&candidate.defined)s->defined=1;
        }else{s=new_symbol(p,name,t,at);*s=candidate;}
        if(!s->function&&!is_extern&&!width(s->type)&&
           !(s->type.array==~0u&&(p->token.kind=='='||!s->internal))&&
           !(structure_object(s->type)&&!s->type.array&&!s->internal&&p->token.kind!='='))
            error_at(at,"global requires a complete object type");
        if(s->always_inline&&s->noinline)error_at(at,"always_inline conflicts with noinline for '%s'",name);
        if(s->internal)snprintf(s->asm_name,sizeof s->asm_name,"%s__%s",p->unit,name);else strcpy(s->asm_name,name);
        if(p->token.kind=='{'){
            Function *f;int i;
            if(!s->function||s->defined)error_at(at,"invalid/duplicate function definition");
            if(s->interrupt){
                Function *previous;
                if(candidate.param_count!=0||candidate.variadic||candidate.old_style)error_at(at,"interrupt handler must be void name(void)");
                for(previous=p->functions;previous;previous=previous->next)
                    if(previous->symbol->interrupt==s->interrupt)error_at(at,"duplicate interrupt handler for this vector");
            }
            if(!strcmp(name,"main")){if((!same_type(t,type(TY_INT,0))&&!same_type(t,type(TY_VOID,0)))||candidate.param_count>0||candidate.variadic)error_at(at,"main must be int main(void) or void main(void)");*has_main=1;}
            s->defined=1;f=allocate(sizeof *f);f->symbol=s;f->id=++p->function_count;*p->function_tail=f;p->function_tail=&f->next;p->current=f;
            if(structure_object(t)){
                if(!width(t))error_at(at,"aggregate return requires a complete type");
                f->aggregate_abi=1;
            }
            {
                Statement *initial=NULL,**tail=&initial;
                for(i=0;i<s->param_count;++i){
                    Symbol *param;Type declared=declared_params[i];char incoming[64];
                    if(structure_object(declared)){
                        if(!width(declared))error_at(at,"aggregate parameter requires a complete type");
                        f->aggregate_abi=1;
                    }
                    int narrow=old_definition&&!same_type(unqualified_value(declared),unqualified_value(s->params[i]));
                    if(!candidate.param_names[i][0])error_at(at,"function definition needs parameter names");
                    strcpy(incoming,candidate.param_names[i]);
                    if(narrow)snprintf(incoming,sizeof incoming,"$knr_%d",i);
                    strcpy(s->param_names[i],incoming);
                    param=new_symbol(p,incoming,narrow?s->params[i]:declared,at);param->owner=f->id;param->active=1;
                    param->offset=f->slots+1;f->slots+=(width(param->type)+1)&~1u;
                    if(narrow){
                        Symbol *local=new_symbol(p,candidate.param_names[i],declared,at);
                        Expr *lhs=new_expr(EX_OBJECT,at,declared),*rhs=new_expr(EX_OBJECT,at,param->type);
                        Expr *assignment=new_expr(EX_ASSIGN,at,declared);Statement *init=allocate(sizeof *init);
                        local->owner=f->id;local->active=1;local->offset=f->slots+1;f->slots+=(width(declared)+1)&~1u;
                        lhs->symbol=local;rhs->symbol=param;assignment->left=lhs;assignment->right=convert(rhs,declared);
                        init->kind=ST_EXPR;init->location=at;init->expression=assignment;*tail=init;tail=&init->next;
                    }
                }
                f->body=statement(p);
                if(!diagnostic_errors)restore_private_compound_operands(f->body);
                finish_jump_labels(f);
                if(initial){*tail=f->body->body;f->body->body=initial;}
            }
            f->frame=f->slots?f->slots+4:0;p->current=NULL;
            if(f->frame>768)error_at(at,"function frame exceeds initial stack budget");
            definition=1;break;
        }
        if(p->token.kind=='='){
            size_t begin=p->position;EmbeddedRange *range;lex(p);
            if(s->function)error_at(at,"function cannot have an initializer");
            if(s->initializer)error_at(at,"duplicate initializer for '%s'",name);
            if(s->dpage)error_at(at,"ROM initializer cannot use __dpage");
            if(!width(s->type)&&s->type.array!=~0u)
                error_at(at,"global requires a complete object type");
            s->type.banked=s->wram||(!s->loram&&object_constant(s->type)&&!object_volatile(s->type));
            object_initializer(p,s,0);
            for(range=p->embeds;range;range=range->next)
                if(range->begin<p->position&&range->end>begin)s->embedded=1;
            s->defined=1;
        }
    }while(accept(p,','));
    if(!definition)expect(p,';',"';'");
}
static void skip_to_top_level_sync(Parser *p,size_t start_position,int start_kind)
{
    unsigned braces=0;
    Recovery *saved=active_recovery;
    active_recovery=NULL;
    if(p->token.kind!=TOK_EOF&&p->position==start_position&&p->token.kind==start_kind)
        lex(p);
    while(p->token.kind!=TOK_EOF){
        if(p->token.kind=='{'){++braces;lex(p);continue;}
        if(p->token.kind=='}'){
            lex(p);
            if(!braces){accept(p,';');break;}
            if(!--braces){accept(p,';');break;}
            continue;
        }
        if(p->token.kind==';'&&!braces){lex(p);break;}
        lex(p);
    }
    active_recovery=saved;
}
static Statement *translation_unit(Parser *p)
{
    int has_main=0;
    while(p->token.kind!=TOK_EOF){
        Recovery frame;
        size_t volatile start_pos=p->position;
        int volatile start_kind=p->token.kind;
        frame.previous=active_recovery;
        active_recovery=&frame;
        if(setjmp(frame.env)==0){
            parse_top_level(p,&has_main);
            active_recovery=frame.previous;
        }else{
            unsigned i;
            active_recovery=frame.previous;
            if(p->current){
                unwind_scopes(p,0);
                p->current=NULL;
            }
            p->scope=0;p->loop_depth=0;p->parse_depth=0;p->current_switch=NULL;
            for(i=0;i<p->tag_count;++i)p->tags[i].defining=0;
            skip_to_top_level_sync(p,start_pos,start_kind);
        }
    }
    if(!diagnostic_errors){
        for(unsigned i=0;i<p->symbol_count;++i){
            Symbol *s=&p->symbols[i];
            if(s->owner||s->function||!s->defined||s->enumerator)continue;
            if(s->type.array==~0u)s->type.array=1;
            if(!width(s->type)){report_error(p->token.location,"global '%s' requires a complete object type",s->name);continue;}
            if(s->wram>=WRAM_SRAM_FIRST)continue;
            unsigned limit=s->initializer||s->wram?object_size_limit(s):65534u;
            check_static_storage_size(s,s->name,limit,p->token.location);
        }
    }
    // Library translation units need no main; the linker selects the entry unit
    (void)has_main;return NULL;
}
