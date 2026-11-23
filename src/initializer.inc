/* Static numeric images use the target layout, not the host C representation */
static uint32_t initializer_cast(uint32_t v,Type t)
{
    unsigned bits=width(t)*8;
    if(t.is_bool&&!t.pointers)return v!=0;
    if(bits<32){uint32_t mask=(1u<<bits)-1;v&=mask;if(!t.is_unsigned&&(v&(1u<<(bits-1))))v|=~mask;}
    return v;
}
static int initializer_truth(uint32_t bits,Type t)
{
    return t.base==TY_FLOAT?(bits&UINT32_C(0x7fffffff))!=0:bits!=0;
}
static float initializer_float(uint32_t bits,Type t)
{
    float value;
    if(t.base!=TY_FLOAT)return t.is_unsigned?(float)bits:(float)(int32_t)bits;
    memcpy(&value,&bits,sizeof value);
    return value;
}
static uint32_t initializer_float_bits(float value,Location at)
{
    uint32_t bits;
    memcpy(&bits,&value,sizeof bits);
    if((bits&UINT32_C(0x7f800000))==UINT32_C(0x7f800000))
        error_at(at,"floating constant expression overflows");
    return bits;
}
static int binary32_integer_bits(uint32_t bits,Type target,uint32_t *result)
{
    double value=initializer_float(bits,type(TY_FLOAT,0));
    unsigned n=8*width(target);
    double limit=(double)(UINT64_C(1)<<(n-!target.is_unsigned));
    double lower=target.is_unsigned?-1.0:-limit-1.0;
    if(!(value>lower&&value<limit))return 0;
    *result=initializer_cast((uint32_t)(int64_t)value,target);
    return 1;
}
static uint32_t initializer_conversion(uint32_t bits,Type source,Type target,Location at)
{
    if(target.is_bool)return initializer_truth(bits,source);
    if(source.base==TY_FLOAT&&target.base==TY_FLOAT)return bits;
    if(target.base==TY_FLOAT)return initializer_float_bits(initializer_float(bits,source),at);
    if(source.base==TY_FLOAT){
        if(!binary32_integer_bits(bits,target,&bits))error_at(at,"floating initializer conversion is out of range");
        return bits;
    }
    return initializer_cast(bits,target);
}
static const char *binary32_constant_operation(int op,float x,float y,uint32_t *result)
{
    float value;
    switch(op){
    case TOK_EQ:*result=x==y;return NULL;case TOK_NE:*result=x!=y;return NULL;
    case '<':*result=x<y;return NULL;case '>':*result=x>y;return NULL;
    case TOK_LE:*result=x<=y;return NULL;case TOK_GE:*result=x>=y;return NULL;
    case '+':value=x+y;break;
    case '-':value=x-y;break;
    case '*':value=x*y;break;
    case '/':
        if(y==0)return "division by zero in initializer";
        value=x/y;break;
    default:return "unsupported floating initializer operator";
    }
    memcpy(result,&value,sizeof value);
    return (*result&UINT32_C(0x7f800000))==UINT32_C(0x7f800000)?
        "floating constant expression overflows":NULL;
}
static uint32_t initializer_float_binary(Expr *e,uint32_t a,uint32_t b,int active)
{
    float x=initializer_float(a,e->left->type),y=initializer_float(b,e->right->type);
    uint32_t result;const char *error;
    if(!active)return 0;
    error=binary32_constant_operation(e->op,x,y,&result);
    if(error)error_at(e->location,"%s",error);
    return result;
}
/* Wide integer constant expressions are evaluated as bit patterns, avoiding
 * host signed overflow and preserving the target's 16/32/64-bit promotions. */
static int initializer_has_wide(Expr *e)
{
    unsigned i;if(!e)return 0;
    if(!e->type.pointers&&!e->type.array&&e->type.base==TY_LONGLONG)return 1;
    if(initializer_has_wide(e->left)||initializer_has_wide(e->right)||initializer_has_wide(e->third))return 1;
    for(i=0;i<e->arg_count;++i)if(initializer_has_wide(e->args[i]))return 1;
    return 0;
}
static uint64_t initializer_mask(unsigned bits)
{
    return bits==64?UINT64_MAX:(UINT64_C(1)<<bits)-1;
}
static uint64_t initializer_cast64(uint64_t v,Type t)
{
    unsigned bits=width(t)*8;uint64_t mask;
    if(t.is_bool&&!t.pointers)return v!=0;
    if(!bits||bits>64)error_at((Location){"<initializer>",0,0},"invalid integer constant width");
    mask=initializer_mask(bits);v&=mask;
    if(!t.is_unsigned&&!t.pointers&&(v&(UINT64_C(1)<<(bits-1))))v|=~mask;
    return v;
}
static int initializer_has_binary64(Expr *e);
static double initializer_binary64_constant(Expr *e,int active);
static uint64_t initializer_mixed_integer(Expr *e,int active);
static uint64_t initializer_binary64_integer(double value,Type target,Location at,int active)
{
    unsigned bits=width(target)*8;double limit,lower;uint64_t magnitude;
    if(target.is_bool)return value!=0.0;
    if(!active)return 0;
    limit=1.0;{unsigned i;for(i=0;i<bits-(target.is_unsigned?0u:1u);++i)limit*=2.0;}
    lower=target.is_unsigned?-1.0:bits==64?-limit:-limit-1.0;
    if(!(value<limit&&(bits==64&&!target.is_unsigned?value>=lower:value>lower)))
        error_at(at,"floating initializer conversion is out of range");
    magnitude=target.is_unsigned?(uint64_t)(value<0.0?0.0:value):(uint64_t)(int64_t)value;
    return initializer_cast64(magnitude,target);
}
static const char *integer_binary_constant(int op,Type operands,uint64_t a,uint64_t b,uint64_t *result)
{
    uint64_t r,mask,sign,aa,bb,limit;unsigned bits;int u,negative;
    bits=width(operands)*8;mask=initializer_mask(bits);sign=UINT64_C(1)<<(bits-1);u=operands.is_unsigned;
    a=initializer_cast64(a,operands)&mask;
    if(op!=TOK_SHL&&op!=TOK_SHR)b=initializer_cast64(b,operands)&mask;
    switch(op){
    case '+':
        r=(a+b)&mask;
        if (!u && ((a ^ r) & (b ^ r) & sign)) {
            return "signed constant expression overflows";
        }
        break;
    case '-':
        r=(a-b)&mask;
        if (!u && ((a ^ b) & (a ^ r) & sign)) {
            return "signed constant expression overflows";
        }
        break;
    case '*':
        if(!u){
            negative=((a&sign)!=0)!=((b&sign)!=0);
            aa=(a&sign)?(0-a)&mask:a;bb=(b&sign)?(0-b)&mask:b;
            limit=negative?sign:sign-1;
            if(bb&&aa>limit/bb)return "signed constant expression overflows";
        }
        r=(a*b)&mask;break;
    case '/':case '%':
        if(!b)return "division by zero in initializer";
        if(u){r=op=='/'?a/b:a%b;break;}
        if(a==sign&&b==mask)return "signed constant expression overflows";
        aa=(a&sign)?(0-a)&mask:a;bb=(b&sign)?(0-b)&mask:b;
        r=op=='/'?aa/bb:aa%bb;
        negative=op=='/'?((a&sign)!=0)!=((b&sign)!=0):(a&sign)!=0;
        if (negative) {
            r = (0 - r) & mask;
        }
        break;
    case '&':r=a&b;break;case '|':r=a|b;break;case '^':r=a^b;break;
    case TOK_EQ:r=a==b;break;case TOK_NE:r=a!=b;break;
    case '<':r=u?a<b:(a^sign)<(b^sign);break;
    case '>':r=u?a>b:(a^sign)>(b^sign);break;
    case TOK_LE:r=u?a<=b:(a^sign)<=(b^sign);break;
    case TOK_GE:r=u?a>=b:(a^sign)>=(b^sign);break;
    case TOK_SHL:case TOK_SHR:
        if(b>=bits)return "invalid shift count in initializer";
        if(op==TOK_SHL){
            if(!u&&((a&sign)||a>((sign-1)>>b)))return "signed constant expression overflows";
            r=(a<<b)&mask;
        }else{
            r=a>>b;
            if(!u&&(a&sign)&&b)r|=mask^(mask>>b);
        }
        break;
    default:return "unsupported constant initializer operator";
    }
    *result=initializer_cast64(r,operands);return NULL;
}
static uint64_t initializer_wide_constant(Expr *e,int active)
{
    uint64_t a,b,r,mask,sign;unsigned bits;Type operands;const char *error;
    if(!e||!numeric(e->type)||e->type.base==TY_FLOAT||e->type.base==TY_DOUBLE)
        error_at(e?e->location:(Location){"<initializer>",0,0},"wide initializer requires an integer constant expression");
    if(e->kind==EX_BINARY&&(e->op==TOK_LAND||e->op==TOK_LOR))
        return initializer_cast64(initializer_constant(e,active),e->type);
    if(initializer_has_binary64(e))
        return initializer_mixed_integer(e,active);
    if(!initializer_has_wide(e))return initializer_cast64(initializer_constant(e,active),e->type);
    if(e->kind==EX_INT)return initializer_cast64(((uint64_t)e->value_high<<32)|e->value,e->type);
    if(e->kind==EX_CAST)return initializer_cast64(initializer_wide_constant(e->left,active),e->type);
    if(e->kind==EX_CHOOSE){
        a=initializer_wide_constant(e->left,active);
        b=initializer_wide_constant(e->right,active&&a!=0);
        r=initializer_wide_constant(e->third,active&&a==0);
        return initializer_cast64(a?b:r,e->type);
    }
    if(e->kind==EX_UNARY){
        a=initializer_wide_constant(e->left,active);
        if(e->op=='!')return !a;
        bits=width(e->type)*8;mask=initializer_mask(bits);sign=UINT64_C(1)<<(bits-1);a&=mask;
        if(e->op=='+')return initializer_cast64(a,e->type);
        if(e->op=='~')return initializer_cast64(~a,e->type);
        if(e->op=='-'){
            if(active&&!e->type.is_unsigned&&a==sign)error_at(e->location,"signed constant expression overflows");
            return initializer_cast64(0-a,e->type);
        }
        error_at(e->location,"unsupported constant initializer operator");
    }
    if(e->kind!=EX_BINARY)error_at(e->location,"initializer requires an integer constant expression");
    a=initializer_wide_constant(e->left,active);
    if(e->op==TOK_LAND||e->op==TOK_LOR){
        int conjunction=e->op==TOK_LAND;
        b=initializer_wide_constant(e->right,active&&(conjunction?a!=0:a==0));
        return conjunction?(a!=0&&b!=0):(a!=0||b!=0);
    }
    b=initializer_wide_constant(e->right,active);
    operands=(e->op==TOK_SHL||e->op==TOK_SHR)?promoted(e->left->type):common_type(e->left->type,e->right->type);
    if(!numeric(operands)||operands.base==TY_FLOAT)error_at(e->location,"wide initializer requires integer operands");
    if(!active)return 0;
    error=integer_binary_constant(e->op,operands,a,b,&r);
    if(error)error_at(e->location,"%s",error);
    return initializer_cast64(r,e->type);
}
/* Evaluate binary64 constants using the host's IEEE double operations.  Integer
 * subtrees remain in the integer evaluator until their conversion to double. */
static double initializer_binary64_constant(Expr *e,int active)
{
    double a,b;
    if(!e||!numeric(e->type))error_at(e?e->location:(Location){"<initializer>",0,0},"binary64 initializer requires numeric operands");
    if(e->type.base!=TY_DOUBLE&&e->type.base!=TY_FLOAT&&initializer_has_binary64(e)){
        uint64_t bits=initializer_mixed_integer(e,active);
        return e->type.is_unsigned?(double)bits:(double)(int64_t)bits;
    }
    if(!initializer_has_binary64(e)){
        if(e->type.base==TY_FLOAT)return initializer_float(initializer_constant(e,active),e->type);
        {uint64_t bits=initializer_wide_constant(e,active);
         return e->type.is_unsigned?(double)bits:(double)(int64_t)bits;}
    }
    if(e->kind==EX_UNARY&&(e->op=='+'||e->op=='-')){
        double value=initializer_binary64_constant(e->left,active);
        return e->op=='-'?-value:value;
    }
    if(e->kind==EX_UNARY&&e->op=='!')return !initializer_binary64_constant(e->left,active);
    if(e->kind==EX_CAST){
        a=initializer_binary64_constant(e->left,active);
        if(e->type.base==TY_DOUBLE)return a;
        if(e->type.base==TY_FLOAT)return (double)(float)a;
        {uint64_t bits=initializer_binary64_integer(a,e->type,e->location,active);
         return e->type.is_unsigned?(double)bits:(double)(int64_t)bits;}
    }
    if(e->kind==EX_INT&&e->type.base==TY_DOUBLE){
        uint64_t bits=((uint64_t)e->value_high<<32)|e->value;double value;
        memcpy(&value,&bits,sizeof value);return value;
    }
    if(e->kind==EX_CHOOSE){
        a=initializer_binary64_constant(e->left,active);
        b=initializer_binary64_constant(e->right,active&&a!=0.0);
        {double other=initializer_binary64_constant(e->third,active&&a==0.0);return a!=0.0?b:other;}
    }
    if(e->kind==EX_BINARY){
        a=initializer_binary64_constant(e->left,active);
        if(e->op==TOK_LAND||e->op==TOK_LOR){
            int conjunction=e->op==TOK_LAND;
            b=initializer_binary64_constant(e->right,active&&(conjunction?a!=0.0:a==0.0));
            return conjunction?(a!=0.0&&b!=0.0):(a!=0.0||b!=0.0);
        }
        b=initializer_binary64_constant(e->right,active);
        if(!active)return 0;
        switch(e->op){
        case TOK_EQ:return a==b;case TOK_NE:return a!=b;
        case '<':return a<b;case '>':return a>b;case TOK_LE:return a<=b;case TOK_GE:return a>=b;
        default:break;
        }
        if(e->type.base==TY_FLOAT){
            float x=(float)a,y=(float)b,value=0;
            switch(e->op){
            case '+':value=x+y;break;case '-':value=x-y;break;case '*':value=x*y;break;
            case '/':if(y==0.0f)error_at(e->location,"division by zero in initializer");value=x/y;break;
            default:error_at(e->location,"unsupported binary32 constant expression");
            }
            (void)initializer_float_bits(value,e->location);return value;
        }
        if(e->type.base!=TY_DOUBLE)error_at(e->location,"unsupported binary64 integer constant expression");
        switch(e->op){
        case '+':return a+b;case '-':return a-b;case '*':return a*b;
        case '/':if(b==0.0)error_at(e->location,"division by zero in initializer");return a/b;
        }
    }
    error_at(e->location,"unsupported binary64 constant expression");
}
static int initializer_has_binary64(Expr *e)
{
    unsigned i;if(!e)return 0;
    if(!e->type.pointers&&!e->type.array&&e->type.base==TY_DOUBLE)return 1;
    if(initializer_has_binary64(e->left)||initializer_has_binary64(e->right)||initializer_has_binary64(e->third))return 1;
    for(i=0;i<e->arg_count;++i)if(initializer_has_binary64(e->args[i]))return 1;
    return 0;
}
static int initializer_mixed_truth(Expr *e,int active)
{
    if(e->type.base==TY_DOUBLE||e->type.base==TY_FLOAT)
        return initializer_binary64_constant(e,active)!=0.0;
    return initializer_mixed_integer(e,active)!=0;
}
/* Reduce integer nodes around binary64 comparisons/casts to integer literals,
 * then reuse the existing width-aware integer evaluator without rounding them
 * through host double. */
static uint64_t initializer_mixed_integer(Expr *e,int active)
{
    Expr node,left,right;uint64_t a,b;Type operands;
    if(!e||!numeric(e->type)||e->type.base==TY_FLOAT||e->type.base==TY_DOUBLE)
        error_at(e?e->location:(Location){"<initializer>",0,0},"mixed initializer requires an integer expression");
    if(!initializer_has_binary64(e))return initializer_wide_constant(e,active);
    if(e->kind==EX_CAST){
        if(e->left->type.base==TY_DOUBLE||e->left->type.base==TY_FLOAT)
            return initializer_binary64_integer(initializer_binary64_constant(e->left,active),e->type,e->location,active);
        return initializer_cast64(initializer_mixed_integer(e->left,active),e->type);
    }
    if(e->kind==EX_UNARY&&e->op=='!')return !initializer_mixed_truth(e->left,active);
    if(e->kind==EX_CHOOSE){
        int truth=initializer_mixed_truth(e->left,active);
        a=initializer_mixed_integer(e->right,active&&truth);
        b=initializer_mixed_integer(e->third,active&&!truth);
        return initializer_cast64(truth?a:b,e->type);
    }
    if(e->kind==EX_BINARY&&(e->op==TOK_LAND||e->op==TOK_LOR)){
        int x=initializer_mixed_truth(e->left,active),conjunction=e->op==TOK_LAND;
        int y=initializer_mixed_truth(e->right,active&&(conjunction?x:!x));
        return conjunction?(x&&y):(x||y);
    }
    if(e->kind==EX_BINARY&&(e->op==TOK_EQ||e->op==TOK_NE||e->op=='<'||
       e->op=='>'||e->op==TOK_LE||e->op==TOK_GE)){
        operands=common_type(e->left->type,e->right->type);
        if(operands.base==TY_DOUBLE||operands.base==TY_FLOAT){
            double x=initializer_binary64_constant(e->left,active),y=initializer_binary64_constant(e->right,active);
            if(!active)return 0;
            if(operands.base==TY_FLOAT){x=(float)x;y=(float)y;}
            switch(e->op){case TOK_EQ:return x==y;case TOK_NE:return x!=y;
            case '<':return x<y;case '>':return x>y;case TOK_LE:return x<=y;case TOK_GE:return x>=y;}
        }
    }
    if(e->kind!=EX_UNARY&&e->kind!=EX_BINARY)
        error_at(e->location,"unsupported mixed binary64 integer constant expression");
    a=initializer_mixed_integer(e->left,active);
    memset(&left,0,sizeof left);left.kind=EX_INT;left.type=e->left->type;left.location=e->left->location;
    left.value=(uint32_t)a;left.value_high=(uint32_t)(a>>32);
    node=*e;node.left=&left;node.third=NULL;
    if(e->kind==EX_BINARY){
        b=initializer_mixed_integer(e->right,active);
        memset(&right,0,sizeof right);right.kind=EX_INT;right.type=e->right->type;right.location=e->right->location;
        right.value=(uint32_t)b;right.value_high=(uint32_t)(b>>32);node.right=&right;
    }else node.right=NULL;
    return initializer_wide_constant(&node,active);
}
static int initializer_expression_truth(Expr *e,int active)
{
    Type t=value_type(e->type);
    if(!t.pointers&&t.base==TY_LONGLONG)return initializer_wide_constant(e,active)!=0;
    if(!t.pointers&&t.base==TY_DOUBLE)return initializer_binary64_constant(e,active)!=0.0;
    return initializer_truth(initializer_constant(e,active),t);
}
static uint32_t initializer_constant(Expr *e,int active)
{
    uint32_t a,b,result=0;int64_t x,y,z=0;Type operands;unsigned bits;int unsigned_op;
    if(!numeric(e->type))error_at(e->location,"initializer requires a numeric constant expression");
    if(e->kind==EX_BINARY&&(e->op==TOK_LAND||e->op==TOK_LOR)&&initializer_has_wide(e)){
        int conjunction=e->op==TOK_LAND;
        int first=initializer_expression_truth(e->left,active);
        int second=initializer_expression_truth(e->right,active&&(conjunction?first:!first));
        return conjunction?(first&&second):(first||second);
    }
    if(initializer_has_binary64(e)){
        if(e->type.base==TY_FLOAT)return initializer_float_bits((float)initializer_binary64_constant(e,active),e->location);
        return (uint32_t)initializer_mixed_integer(e,active);
    }
    if(initializer_has_wide(e)&&e->kind==EX_CAST&&e->type.base==TY_FLOAT&&
       e->left->type.base==TY_LONGLONG){
        uint64_t wide=initializer_wide_constant(e->left,active);float single;
        if(!active)return 0;
        single=e->left->type.is_unsigned?(float)wide:(float)(int64_t)wide;
        return initializer_float_bits(single,e->location);
    }
    if(initializer_has_wide(e)&&e->type.base!=TY_FLOAT&&
       !(e->kind==EX_BINARY&&common_type(e->left->type,e->right->type).base==TY_FLOAT)){
        uint64_t v=initializer_wide_constant(e,active);
        if(active&&(v>>32)!=0&&((v>>32)!=UINT32_MAX||(uint32_t)v<UINT32_C(0x80000000)||e->type.is_unsigned))
            error_at(e->location,"constant expression exceeds supported 32-bit context");
        return (uint32_t)v;
    }
    if(e->kind==EX_INT)return e->type.base==TY_FLOAT?e->value:initializer_cast(e->value,e->type);
    if(e->type.base==TY_FLOAT&&e->kind==EX_UNARY&&(e->op=='-'||e->op=='+')){
        a=initializer_constant(e->left,active);return e->op=='-'?a^UINT32_C(0x80000000):a;
    }
    if(e->kind==EX_CAST){
        a=initializer_constant(e->left,active);
        return active?initializer_conversion(a,e->left->type,e->type,e->location):0;
    }
    if(e->kind==EX_CHOOSE){
        a=initializer_expression_truth(e->left,active);
        b=initializer_constant(e->right,active&&a!=0);result=initializer_constant(e->third,active&&a==0);
        return a?b:result;
    }
    if(e->kind==EX_UNARY){
        a=initializer_constant(e->left,active);
        if(e->op=='!')return !initializer_truth(a,e->left->type);
        if(e->op=='+')return initializer_cast(a,e->type);
        if(e->op=='~')return initializer_cast(~a,e->type);
        if(e->op=='-'){
            bits=width(e->type)*8;
            if(active&&!e->type.is_unsigned&&(int32_t)a==-(INT64_C(1)<<(bits-1)))
                error_at(e->location,"signed constant expression overflows");
            return initializer_cast(0u-a,e->type);
        }
    }
    if(e->kind!=EX_BINARY)error_at(e->location,"initializer requires a numeric constant expression");
    a=initializer_constant(e->left,active);
    if(e->op==TOK_LAND||e->op==TOK_LOR){
        int truth=initializer_truth(a,e->left->type), conjunction=e->op==TOK_LAND;
        b=initializer_constant(e->right,active&&(conjunction?truth:!truth));
        return conjunction?(truth&&initializer_truth(b,e->right->type)):(truth||initializer_truth(b,e->right->type));
    }
    b=initializer_constant(e->right,active);
    operands=(e->op==TOK_SHL||e->op==TOK_SHR)?promoted(e->left->type):common_type(e->left->type,e->right->type);
    if(operands.pointers)error_at(e->location,"initializer requires an arithmetic constant expression");
    if(operands.base==TY_FLOAT)return initializer_float_binary(e,a,b,active);
    bits=width(operands)*8;unsigned_op=operands.is_unsigned;
    a=initializer_cast(a,operands);b=initializer_cast(b,(e->op==TOK_SHL||e->op==TOK_SHR)?promoted(e->right->type):operands);
    x=unsigned_op?(int64_t)a:(int64_t)(int32_t)a;y=unsigned_op?(int64_t)b:(int64_t)(int32_t)b;
    if(!active)return 0;
    switch(e->op){
    case '+':z=x+y;break;case '-':z=x-y;break;case '*':
        if(unsigned_op)return initializer_cast((uint32_t)((uint64_t)a*b),e->type);
        z=x*y;break;
    case '/':case '%':
        if(!y)error_at(e->location,"division by zero in initializer");
        if(!unsigned_op&&x==-(INT64_C(1)<<(bits-1))&&y==-1)error_at(e->location,"signed constant expression overflows");
        z=e->op=='/'?x/y:x%y;break;
    case '&':return initializer_cast(a&b,e->type);case '|':return initializer_cast(a|b,e->type);case '^':return initializer_cast(a^b,e->type);
    case TOK_EQ:return x==y;case TOK_NE:return x!=y;case '<':return x<y;case '>':return x>y;case TOK_LE:return x<=y;case TOK_GE:return x>=y;
    case TOK_SHL:case TOK_SHR:
        if((int32_t)b<0||b>=bits)error_at(e->location,"invalid shift count in initializer");
        if(e->op==TOK_SHR)return initializer_cast((uint32_t)(unsigned_op?(int64_t)(a>>b):x>>b),e->type);
        if(!unsigned_op&&x<0)error_at(e->location,"negative signed left shift in initializer");
        z=x*(INT64_C(1)<<b);break;
    default:error_at(e->location,"unsupported constant initializer operator");
    }
    if(!unsigned_op&&(z<-(INT64_C(1)<<(bits-1))||z>((INT64_C(1)<<(bits-1))-1)))
        error_at(e->location,"signed constant expression overflows");
    return initializer_cast((uint32_t)z,e->type);
}
/* Resolve addresses without baking linker placement into the frontend */
static int initializer_address(Expr *e,Relocation *r,uint32_t *absolute,int address)
{
    if(e->kind==EX_INT&&e->type.pointers){*absolute=e->value;return 1;}
    if(e->kind==EX_CAST&&e->type.pointers){
        Expr literal={0};
        Type source=value_type(e->left->type);
        if(source.pointers){
            if(!initializer_address(e->left,r,absolute,address))return 0;
        }else{
            integer_constant_operands(e->left,"address initializer");
            *absolute=initializer_constant(e->left,1);
        }
        if(r->symbol||r->string){
            if(!e->error_reported&&!far_pointer(e->type)&&(r->string||r->symbol->type.banked))
                report_error(e->location,"ROM address is not representable as a near pointer");
        }else{
            literal.kind=EX_INT;literal.type=source;literal.location=e->location;literal.value=*absolute;
            *absolute=convert(&literal,e->type)->value;
        }
        return 1;
    }
    if(e->kind==EX_CHOOSE&&e->type.pointers){
        Relocation ignored={0};uint32_t unused=0;
        Expr *selected,*other;
        integer_constant_operands(e->left,"address initializer condition");
        if(initializer_constant(e->left,1)){selected=e->right;other=e->third;}
        else{selected=e->third;other=e->right;}
        return initializer_address(selected,r,absolute,address)&&initializer_address(other,&ignored,&unused,address);
    }
    if(e->kind==EX_STRING){r->string=e->string;return 1;}
    if(e->kind==EX_OBJECT&&function_type(e->type)){r->symbol=e->symbol;return 1;}
    if(e->kind==EX_OBJECT&&(address||e->type.array)&&!e->symbol->owner&&!e->symbol->function){r->symbol=e->symbol;return 1;}
    if(e->kind==EX_ADDRESS)return initializer_address(e->left,r,absolute,1);
    if(e->kind==EX_DEREF&&(address||e->type.array))return initializer_address(e->left,r,absolute,0);
    if(e->kind==EX_MEMBER&&(address||e->type.array)){
        int64_t addend;
        if(!initializer_address(e->left,r,absolute,e->op=='.'))return 0;
        if(r->symbol||r->string){
            addend=(int64_t)r->addend+e->value;
            if(addend>INT32_MAX)error_at(e->location,"address initializer offset overflows");
            r->addend=(int32_t)addend;
        }else{
            addend=(int64_t)*absolute+e->value;
            if(addend>(e->left->type.banked||far_pointer(value_type(e->left->type))?0xffffff:0xffff))
                error_at(e->location,"address initializer offset overflows");
            *absolute=(uint32_t)addend;
        }
        return 1;
    }
    if(e->kind==EX_BINARY&&(e->op=='+'||e->op=='-')){
        Expr *base=e->left,*index=e->right;int64_t n;uint32_t bits;
        if(e->op=='+'&&!value_type(base->type).pointers&&value_type(index->type).pointers){base=e->right;index=e->left;}
        if(!value_type(base->type).pointers||!initializer_address(base,r,absolute,0))return 0;
        integer_constant_operands(index,"address initializer offset");bits=initializer_constant(index,1);
        n=index->type.is_unsigned?(int64_t)bits:(int64_t)(int32_t)bits;
        n*=width(pointed_type(value_type(base->type)));
        if(e->op=='-')n=-n;
        if(r->symbol||r->string){
            n+=r->addend;
            if(n<INT32_MIN||n>INT32_MAX)error_at(e->location,"address initializer offset overflows");
            r->addend=(int32_t)n;
        }else{
            n+=*absolute;
            if(n<0||n>(far_pointer(value_type(base->type))?0xffffff:0xffff))
                error_at(e->location,"address initializer offset overflows");
            *absolute=(uint32_t)n;
        }
        return 1;
    }
    return 0;
}
typedef struct { Parser *p;Symbol *symbol;int automatic;Statement *body,**tail;const Member *bitfield; } Initializer;
static void initializer_store(Initializer *init,Type t,unsigned offset,Expr *e)
{
    Location at=e->location;unsigned i;uint32_t value=0;
    if(init->automatic){
        Expr *root=new_expr(EX_OBJECT,at,init->symbol->type),*lhs=root,*assignment;
        Statement *s=allocate(sizeof *s);root->symbol=init->symbol;
        if(t.array||structure_object(t)||offset||init->symbol->type.array||structure_object(init->symbol->type)){
            lhs=new_expr(EX_MEMBER,at,t);lhs->op='.';lhs->left=root;lhs->value=offset;
        }
        if(init->bitfield)lhs=bitfield_expression(init->p,lhs,init->bitfield);
        assignment=new_expr(EX_ASSIGN,at,t);assignment->left=lhs;
        if(structure_object(t)){
            if(!same_type(unqualified_value(t),unqualified_value(e->type)))error_at(at,"incompatible aggregate initializer");
            assignment->right=e;
        }else assignment->right=assignment_convert(e,t);
        s->kind=ST_EXPR;s->location=at;s->expression=assignment;
        *init->tail=s;init->tail=&s->next;return;
    }
    if(!t.pointers&&t.base==TY_DOUBLE){
        double real=initializer_binary64_constant(e,1);uint64_t bits;
        memcpy(&bits,&real,sizeof bits);
        for(i=0;i<8;++i)init->symbol->initializer[offset+i]=(unsigned char)(bits>>(8*i));
        free_expression(e);return;
    }
    if(!t.pointers&&initializer_has_binary64(e)){
        uint64_t bits;
        if(e->type.base!=TY_FLOAT&&e->type.base!=TY_DOUBLE){
            uint64_t integer=initializer_mixed_integer(e,1);
            if(t.base==TY_FLOAT){float single=e->type.is_unsigned?(float)integer:(float)(int64_t)integer;bits=initializer_float_bits(single,at);}
            else bits=initializer_cast64(integer,t);
        }else{
            double real=initializer_binary64_constant(e,1);
            if(t.base==TY_FLOAT){float single=(float)real;bits=initializer_float_bits(single,at);}
            else bits=initializer_binary64_integer(real,t,at,1);
        }
        for(i=0;i<width(t);++i)init->symbol->initializer[offset+i]=(unsigned char)(bits>>(8*i));
        free_expression(e);return;
    }
    if(!t.pointers&&t.base==TY_LONGLONG){
        uint64_t wide;
        Expr *floating=e;
        if(!numeric(e->type))
            error_at(at,"64-bit initializer requires an integer constant expression");
        if(e->kind==EX_CAST&&e->left->type.base==TY_FLOAT)floating=e->left;
        if(floating->type.base==TY_FLOAT){
            uint32_t bits=initializer_constant(floating,1);float single;
            memcpy(&single,&bits,sizeof single);
            Type target=e->type.base==TY_LONGLONG?e->type:t;
            wide=initializer_cast64(initializer_binary64_integer((double)single,target,at,1),t);
        }else wide=initializer_cast64(initializer_wide_constant(e,1),t);
        for(i=0;i<8;++i)init->symbol->initializer[offset+i]=(unsigned char)(wide>>(8*i));
        free_expression(e);return;
    }
    if(t.pointers){
        Relocation *r=allocate(sizeof *r);
        if(numeric(e->type)&&e->type.base!=TY_FLOAT&&e->kind!=EX_INT){
            integer_constant_operands(e,"pointer initializer");
            value=initializer_constant(e,1);
            if(value){report_error(at,"incompatible pointer initializer");free(r);free_expression(e);return;}
            free_expression(e);
            e=new_expr(EX_INT,at,type(TY_INT,0));
        }
        if(!compatible_argument(t,e)){
            if(far_to_near_mismatch(t,e))
                report_error(at,"incompatible pointer initializer: far pointer cannot initialize near pointer (declare target with __far)");
            else if(nested_far_mismatch(t,e))
                report_error(at,"incompatible pointer initializer: nested near/far pointer mismatch");
            else
                report_error(at,"incompatible pointer initializer");
            free(r);free_expression(e);return;
        }
        e=assignment_convert(e,t);
        if(!initializer_address(e,r,&value,0)){report_error(at,"pointer initializer requires a constant address");free(r);free_expression(e);return;}
        if(r->symbol||r->string){
            r->offset=offset;r->size=width(t);r->far_value=far_pointer(t);
            if (r->symbol) r->symbol->used = 1;
            if (r->string) r->string->used = 1;
            {Relocation **tail=&init->symbol->relocations;while(*tail)tail=&(*tail)->next;*tail=r;}
            free_expression(e);return;
        }
        free(r);
    }else if(initializer_has_wide(e)){
        if(t.base==TY_FLOAT){
            Expr *integer=e;
            uint64_t wide;float single;
            if(e->type.base==TY_FLOAT)value=initializer_constant(e,1);
            else{
                if(!numeric(integer->type)||integer->type.base==TY_DOUBLE)
                    error_at(at,"wide-to-float initializer requires an integer constant expression");
                wide=initializer_wide_constant(integer,1);
                single=integer->type.is_unsigned?(float)wide:(float)(int64_t)wide;
                value=initializer_float_bits(single,at);
            }
        }else{
            if(!numeric(t))error_at(at,"wide constant conversion requires an integer target");
            if(e->kind==EX_BINARY&&common_type(e->left->type,e->right->type).base==TY_FLOAT)
                value=initializer_conversion(initializer_constant(e,1),e->type,t,at);
            else value=(uint32_t)initializer_cast64(initializer_wide_constant(e,1),t);
        }
    }else{
        value=initializer_constant(e,1);
        value=initializer_conversion(value,e->type,t,at);
    }
    if(init->bitfield){
        unsigned char *bytes=init->symbol->initializer+offset;
        unsigned shift=init->bitfield->bit_shift;
        unsigned mask=((1u<<init->bitfield->bit_width)-1)<<shift;
        unsigned previous=bytes[0]|((unsigned)bytes[1]<<8);
        value=(previous&~mask)|((value<<shift)&mask);
    }
    for(i=0;i<width(t);++i)init->symbol->initializer[offset+i]=(unsigned char)(value>>(8*i));
    free_expression(e);
}
static void initializer_zero(Initializer *init,Type t,unsigned offset)
{
    unsigned i;Member *m;Expr *zero;
    if(!init->automatic)return;
    if(t.array){for(i=0;i<t.array;++i)initializer_zero(init,array_element(t),offset+i*width(array_element(t)));return;}
    if(structure_object(t)){
        for(m=t.structure->members;m;m=t.structure->is_union?NULL:m->next){
            init->bitfield=m->bit_width?m:NULL;
            initializer_zero(init,m->type,offset+m->offset);
            init->bitfield=NULL;
        }
        return;
    }
    zero=new_expr(EX_INT,init->p->token.location,type(TY_INT,0));initializer_store(init,t,offset,zero);
}
static int character_array(Type t){return t.array&&!array_element(t).pointers&&array_element(t).base==TY_CHAR;}
static void initializer_string(Initializer *init,Type *t,unsigned offset)
{
    Parser *p=init->p;unsigned count=0,i;unsigned char bytes[4096];Location at=p->token.location;
    if(!init->automatic&&init->symbol->wram){
        unsigned limit=t->array==~0u?object_size_limit(init->symbol)-offset:t->array;
        do{
            if(p->token.length>limit-count)error_at(at,"string initializer is too long for character array");
            memcpy(init->symbol->initializer+offset+count,p->token.bytes,p->token.length);
            count+=(unsigned)p->token.length;lex(p);
        }while(p->token.kind==TOK_STRING);
        if(t->array==~0u){
            if(count==limit)error_at(at,"object size exceeds %u bytes",object_size_limit(init->symbol));
            t->array=count+1;
        }
        return;
    }
    do{
        if(count+p->token.length>=sizeof bytes)error_at(at,"character initializer string too long");
        memcpy(bytes+count,p->token.bytes,p->token.length);count+=(unsigned)p->token.length;lex(p);
    }while(p->token.kind==TOK_STRING);
    if(t->array==~0u)t->array=count+1;
    if(t->array<count)error_at(at,"string initializer is too long for character array");
    for(i=0;i<t->array;++i){Expr *e=new_expr(EX_INT,at,type(TY_CHAR,0));e->value=i<count?bytes[i]:0;initializer_store(init,array_element(*t),offset+i,e);}
}
/* Only an explicit brace list owns its closing brace. An unbraced
 * subaggregate consumes entries up to its capacity, leaving the next
 * separator to its parent. */
static void parse_initializer(Initializer *init,Type *t,unsigned offset,int nested,Expr *first)
{
    Parser *p=init->p;Location at=p->token.location;unsigned count=0;Member *m;
    if(!first&&(p->token.kind=='.'||p->token.kind=='['))error_at(at,"designated initializers are not implemented yet");
    if(!first&&character_array(*t)&&p->token.kind==TOK_STRING){initializer_string(init,t,offset);return;}
    if(t->array||structure_object(*t)){
        int braced=!first&&accept(p,'{');Type element=t->array?array_element(*t):*t;
        if(!braced){
            if(!t->array&&init->automatic){
                if(!first&&(!nested||p->token.kind!=TOK_STRING))first=assignment_expression(p);
                if(!nested||(first&&same_type(unqualified_value(*t),unqualified_value(first->type)))){
                    initializer_store(init,*t,offset,first);return;
                }
            }
            if(!nested)error_at(at,"expected '{' for aggregate initializer");
        }
        if(braced&&character_array(*t)&&p->token.kind==TOK_STRING){
            initializer_string(init,t,offset);accept(p,',');expect(p,'}',"'}' after string initializer");return;
        }
        if(braced&&p->token.kind=='}')error_at(at,"empty initializer is not supported");
        m=t->array?NULL:t->structure->members;
        for(;;){
            if(t->array){
                if(count==t->array)error_at(p->token.location,"excess array initializer");
                unsigned limit=init->automatic?65534u:object_size_limit(init->symbol);
                unsigned stride=width(element);
                if(!stride||count>=(limit-offset)/stride)
                    error_at(at,"object size exceeds %u bytes",limit);
                parse_initializer(init,&element,offset+count*width(element),1,first);++count;
            }else{
                Type field;
                if(!m)error_at(p->token.location,"excess %s initializer",t->structure->is_union?"union":"struct");
                field=m->type;
                init->bitfield=m->bit_width?m:NULL;
                parse_initializer(init,&field,offset+m->offset,1,first);
                init->bitfield=NULL;
                m=t->structure->is_union?NULL:m->next;
            }
            first=NULL;
            if(!braced&&(t->array?count==t->array:!m))break;
            if (!accept(p, ',')) break;
            if (p->token.kind == '}') break;
        }
        if(braced)expect(p,'}',"'}' after initializer");
        if(t->array){
            if(t->array==~0u)t->array=count;
            for(;count<t->array;++count)initializer_zero(init,element,offset+count*width(element));
        }else for(;m;m=m->next){
            init->bitfield=m->bit_width?m:NULL;
            initializer_zero(init,m->type,offset+m->offset);
            init->bitfield=NULL;
        }
        return;
    }
    if(!first&&accept(p,'{')){
        parse_initializer(init,t,offset,0,NULL);
        if(accept(p,',')&&p->token.kind!='}')error_at(p->token.location,"excess scalar initializer");
        expect(p,'}',"'}' after scalar initializer");return;
    }
    initializer_store(init,*t,offset,first?first:assignment_expression(p));
}
static Statement *object_initializer(Parser *p,Symbol *s,int automatic)
{
    Initializer init={0};Statement *statement;
    unsigned limit=automatic?65534u:object_size_limit(s);
    init.p=p;init.symbol=s;init.automatic=automatic;init.tail=&init.body;
    if(width(s->type)>limit)error_at(p->token.location,"object size exceeds %u bytes",limit);
    if(!automatic)s->initializer=allocate(s->type.array==~0u?limit:width(s->type));
    parse_initializer(&init,&s->type,0,0,NULL);
    if(!width(s->type)||width(s->type)>limit)error_at(p->token.location,"initializer requires a complete target-sized object");
    if(!automatic&&s->type.array){
        unsigned char *image=realloc(s->initializer,width(s->type));
        if (!image) {
            error_at(p->token.location, "out of memory");
        }
        s->initializer = image;
    }
    /* Inferred automatic arrays acquire their extent after the final element */
    for(statement=init.body;statement;statement=statement->next){
        Expr *lhs=statement->expression->left;
        if(lhs->kind==EX_BITFIELD)lhs=lhs->left;
        if(lhs->kind==EX_MEMBER)lhs->left->type=s->type;else lhs->type=s->type;
    }
    return init.body;
}
