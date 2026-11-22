/* Legacy syntax uses promoted incoming homes and converts them to each
 * parameter's declared type at function entry. */
static void function_parameters(Parser *p,Symbol *candidate,Type *declared,int *old_definition,Location at)
{
    unsigned i,j;unsigned char seen[MAX_PARAMETERS]={0};
    if(accept(p,')')){
        candidate->old_style=1;candidate->param_count=-1;
        if(p->token.kind=='{'){
            candidate->param_count=0;*old_definition=1;
            warning_at(at,"old-style function definition without a prototype");
        }else warning_at(at,"function declaration without a prototype");
        return;
    }
    if(p->token.kind==TOK_NAME&&!find_alias(p,p->token.name)){
        candidate->old_style=1;*old_definition=1;
        warning_at(at,"K&R identifier-list function definition");
        do{
            if(p->token.kind!=TOK_NAME)error_at(p->token.location,"expected K&R parameter name");
            if(candidate->param_count==MAX_PARAMETERS)error_at(at,"too many parameters");
            for(i=0;i<(unsigned)candidate->param_count;++i)
                if(!strcmp(candidate->param_names[i],p->token.name))error_at(p->token.location,"duplicate parameter '%s'",p->token.name);
            strcpy(candidate->param_names[candidate->param_count],p->token.name);
            declared[candidate->param_count++]=type(TY_INT,0);lex(p);
        }while(accept(p,','));
        expect(p,')',"')' after K&R parameter names");
        while(p->token.kind!='{'){
            Type base;
            if(p->token.kind==';'||p->token.kind==TOK_EOF)
                error_at(p->token.location,"identifier-list parameters require a function definition");
            accept(p,TOK_REGISTER);base=declaration_base(p);
            do{
                char name[64];Type t=named_declarator(p,base,name,0);Location item=p->token.location;
                for(i=0;i<(unsigned)candidate->param_count;++i)if(!strcmp(candidate->param_names[i],name))break;
                if(i==(unsigned)candidate->param_count)error_at(item,"declaration for non-parameter '%s'",name);
                if(seen[i])error_at(item,"duplicate declaration for parameter '%s'",name);
                t=value_type(t);
                if(!width(t))error_at(item,"K&R parameter requires a scalar or pointer type, or a complete aggregate");
                if(p->token.kind=='=')error_at(item,"parameter cannot have an initializer");
                declared[i]=t;seen[i]=1;
            }while(accept(p,','));
            expect(p,';',"';' after K&R parameter declaration");
        }
        for(i=0;i<(unsigned)candidate->param_count;++i){
            if(!(seen[i]))warning_at(at,"implicit int for parameter '%s'",candidate->param_names[i]);
            candidate->params[i]=default_argument_promoted(declared[i]);
        }
        return;
    }
    do{
        Type param;
        if(accept(p,TOK_ELLIPSIS)){
            if(!candidate->param_count)error_at(at,"variadic prototype needs a named parameter");
            candidate->variadic=1;break;
        }
        accept(p,TOK_REGISTER);param=declaration_base(p);
        if(candidate->param_count==MAX_PARAMETERS)error_at(at,"too many parameters");
        param=named_declarator_mode(p,param,candidate->param_names[candidate->param_count],1,1,NULL);
        param=value_type(param);
        if(param.base==TY_VOID&&!param.pointers){
            if(candidate->param_count||p->token.kind!=')'||candidate->param_names[0][0])error_at(at,"invalid void parameter");
            break;
        }
        for(j=0;j<(unsigned)candidate->param_count;++j)
            if(candidate->param_names[candidate->param_count][0]&&!strcmp(candidate->param_names[j],candidate->param_names[candidate->param_count]))
                error_at(at,"duplicate parameter '%s'",candidate->param_names[j]);
        declared[candidate->param_count]=candidate->params[candidate->param_count]=param;
        ++candidate->param_count;
    }while(accept(p,','));
    expect(p,')',"')'");
}
static void check_default_promotions(const Symbol *prototype,Location at)
{
    int i;
    if(prototype->variadic)error_at(at,"variadic prototype conflicts with old-style declaration");
    for(i=0;i<prototype->param_count;++i)
        if(!same_type(unqualified_value(prototype->params[i]),default_argument_promoted(prototype->params[i])))
            error_at(at,"prototype parameter is incompatible with default argument promotions");
}

static void merge_function(Symbol *s,Symbol *candidate,Location at)
{
    int i;
    if(s->param_count>=0&&candidate->param_count>=0){
        if(s->param_count!=candidate->param_count||s->variadic!=candidate->variadic)
            error_at(at,"conflicting prototype '%s'",candidate->name);
        for(i=0;i<s->param_count;++i){
            Type existing=unqualified_value(s->params[i]),incoming=unqualified_value(candidate->params[i]);
            if(!same_type(existing,incoming))
                error_at(at,pointer_far_mismatch(existing,incoming)?
                         "conflicting parameter type: near/far pointer mismatch":
                         "conflicting parameter type");
        }
    }
    if(s->old_style!=candidate->old_style)
        check_default_promotions(s->old_style?candidate:s,at);
    if(candidate->param_count>=0){
        s->param_count=candidate->param_count;s->variadic=candidate->variadic;
        memcpy(s->params,candidate->params,sizeof s->params);
    }
    /* A later non-prototype declaration must not erase a visible prototype or
     * rename the parameter homes of a definition already parsed. */
    s->old_style=s->old_style&&candidate->old_style;
    if(!s->defined)memcpy(s->param_names,candidate->param_names,sizeof s->param_names);
}
