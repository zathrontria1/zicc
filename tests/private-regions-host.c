/* White-box checks for byte liveness and frame provenance after emission */
#include <assert.h>
#define main compiler_entry
#include "../src/main.c"
#undef main
static Parser parser;
static Function function;
static Statement escape;
static Expr address,object;
static const char *prefix="_probe:\n    phy\n    tsc\n    sec\n    sbc #$0008\n    tcs\n    tay\n";
static void setup(void)
{
    unsigned i;

    memset(&parser, 0, sizeof parser);
    memset(&function, 0, sizeof function);
    cg_reset_program(&parser);
    cg.function = &function;
    lp_bind_from_codegen(1, 0, 1, 1); // volatile, no escaping frame address, word value result

    function.id = 1;
    function.slots = function.frame = 8;
    parser.symbol_count = 6;

    for (i = 0; i < 4; ++i) {
        parser.symbols[i].owner = 1;
        parser.symbols[i].offset = i * 2 + 1;
        parser.symbols[i].type = type(TY_INT, 0);
    }

    parser.symbols[1].type.is_volatile = 1;
    object.kind = EX_OBJECT;
    object.symbol = &parser.symbols[2];
    object.type = object.symbol->type;
    address.kind = EX_ADDRESS;
    address.left = &object;
    escape.kind = ST_EXPR;
    escape.expression = &address;
    function.body = &escape;

    strcpy(parser.symbols[4].asm_name, "outside");
    parser.symbols[4].type = type(TY_INT, 0);
    strcpy(parser.symbols[5].asm_name, "volatile_io");
    parser.symbols[5].type = volatile_object(type(TY_INT, 0));
}
static void parse(LpUnit *u,const char *body)
{
    char *text=malloc(strlen(prefix)+strlen(body)+32);strcpy(text,prefix);strcat(text,body);strcat(text,"    rts\n");lp_parse(u,text,strlen(text));free(text);
}
static void lp_free(LpUnit *u)
{
    lp_free_edits(u);
    free(u->text);
    free(u->lines);
}
static LpLine *find(LpUnit *u,const char *text,unsigned occurrence)
{
    unsigned i;for(i=0;i<u->count;++i)if(lp_line_is(&u->lines[i],text)&&!occurrence--)return &u->lines[i];abort();
}
static void dead_stores(void)
{
    LpUnit u;
    parse(&u,"    lda #1\n    sta a:$0001,y\n    lda #2\n    sta a:$0001,y\n    lda a:$0001,y\n");
    assert(lp_region_dead_stores(&u,&function,0));assert(find(&u,"sta a:$0001,y",0)->deleted);assert(!find(&u,"sta a:$0001,y",1)->deleted);lp_free(&u);
    parse(&u,"    sta a:$0003,y\n    sta a:$0003,y\n    sta a:$0005,y\n    sta a:$0005,y\n");
    lp_region_dead_stores(&u,&function,0);assert(!find(&u,"sta a:$0003,y",0)->deleted&&!find(&u,"sta a:$0005,y",0)->deleted);lp_free(&u);
    parse(&u,"    sta a:$0001,y\n    lda a:$0000,x\n");lp_region_dead_stores(&u,&function,0);assert(!find(&u,"sta a:$0001,y",0)->deleted);lp_free(&u);
    parse(&u,"    sta a:$0001,y\n    lda f:$004212\n    sta f:$002100\n    lda #0\n");lp_region_dead_stores(&u,&function,0);
    assert(find(&u,"sta a:$0001,y",0)->deleted&&!find(&u,"sta f:$002100",0)->deleted);lp_free(&u);
    parse(&u,"    sta z:__arith_lhs\n    sep #$20\n.a8\n    sta z:__arith_lhs+1\n    rep #$20\n.a16\n    lda z:__arith_lhs\n");lp_region_dead_stores(&u,&function,0);
    assert(!find(&u,"sta z:__arith_lhs",0)->deleted&&!find(&u,"sta z:__arith_lhs+1",0)->deleted);lp_free(&u);
    parse(&u,"    sep #$20\n.a8\n    sta z:__arith_lhs\n    rep #$20\n.a16\n    sta z:__arith_lhs\n    lda z:__arith_lhs\n");lp_region_dead_stores(&u,&function,0);
    assert(find(&u,"sta z:__arith_lhs",0)->deleted&&!find(&u,"sta z:__arith_lhs",1)->deleted);lp_free(&u);
    parse(&u,"    sta a:$0001,y\n    jsr .loword(_unresolved)\n    lda #0\n");lp_region_dead_stores(&u,&function,0);assert(find(&u,"sta a:$0001,y",0)->deleted);lp_free(&u);
    parse(&u,"    sta z:__arith_lhs\n    jsr .loword(_unresolved)\n    lda #0\n");lp_region_dead_stores(&u,&function,0);assert(!find(&u,"sta z:__arith_lhs",0)->deleted);lp_free(&u);
}
static void provenance(void)
{
    LpUnit u;PrState *states;LpLine *cursor,*home;
    parse(&u,"    beq :+\n    phy\n    lda #0\n    tay\n    sta a:$0001,y\n    iny\n    ply\n:\n    sta a:$0001,y\n");
    states=pr_states(&u);cursor=find(&u,"sta a:$0001,y",0);home=find(&u,"sta a:$0001,y",1);
    assert(!states[cursor-u.lines].frame&&states[home-u.lines].frame);free(states);lp_region_dead_stores(&u,&function,0);
    assert(!cursor->deleted&&home->deleted);lp_free(&u);
    parse(&u,"    beq :+\n    lda #0\n    tay\n:\n    sta a:$0001,y\n");states=pr_states(&u);home=find(&u,"sta a:$0001,y",0);
    assert(!states[home-u.lines].frame);free(states);lp_region_dead_stores(&u,&function,0);assert(!home->deleted);lp_free(&u);
    parse(&u,"    phy\n    mvp #$7E, #$7E\n    sta a:$0001,y\n    ply\n    sta a:$0001,y\n");
    states=pr_states(&u);cursor=find(&u,"sta a:$0001,y",0);home=find(&u,"sta a:$0001,y",1);
    assert(!states[cursor-u.lines].frame&&states[home-u.lines].frame);free(states);lp_free(&u);
    parse(&u,"    phy\n    sep #$10\n.i8\n    ply\n    rep #$10\n.i16\n    sta a:$0001,y\n");states=pr_states(&u);home=find(&u,"sta a:$0001,y",0);assert(!states[home-u.lines].frame);free(states);lp_free(&u);
    parse(&u,"    sta a:$0001,y\n    jmp (table,x)\n.word 0\n");assert(!lp_region_dead_stores(&u,&function,0));lp_free(&u);
}
static void copies(void)
{
    LpUnit u;LpLine *load;unsigned i;const char *ops[]={"asl","lsr","rol","ror","inc","dec"};char text[256];
    for(i=0;i<sizeof ops/sizeof *ops;++i){
        snprintf(text,sizeof text,"    lda a:$0001,y\n    %s a\n    sta a:.loword(_outside)\n    lda a:$0001,y\n",ops[i]);
        parse(&u,text);lp_region_private_copies(&u,&function,0);assert(!find(&u,"lda a:$0001,y",1)->deleted);lp_free(&u);
    }
    parse(&u,"    lda a:$0001,y\n    sta z:__arith_lhs\n    lda #5\n    sta a:.loword(_outside)\n    lda z:__arith_lhs\n");lp_region_private_copies(&u,&function,0);
    load=find(&u,"lda z:__arith_lhs",0);assert(load->replace&&strstr(load->replace,"a:$0001,y"));lp_free(&u);
    parse(&u,"    lda a:$0001,y\n    sta z:__arith_lhs\n    lda f:$004212\n    lda z:__arith_lhs\n");lp_region_private_copies(&u,&function,0);assert(!find(&u,"lda z:__arith_lhs",0)->replace);lp_free(&u);
    parse(&u,"    lda a:$0001,y\n    sta z:__arith_lhs\n    sta a:$0001,y\n    inc a:$0001,y\n    lda z:__arith_lhs\n");lp_region_private_copies(&u,&function,0);assert(!find(&u,"lda z:__arith_lhs",0)->replace);lp_free(&u);
    parse(&u,"    lda a:$0001,y\n    sta z:__arith_lhs\n    sep #$10\n.i8\n    lda z:__arith_lhs\n");lp_region_private_copies(&u,&function,0);assert(!find(&u,"lda z:__arith_lhs",0)->replace);lp_free(&u);
    parser.no_private_regions=1;parse(&u,"    sta a:$0001,y\n");assert(!lp_region_dead_stores(&u,&function,0));lp_free(&u);
}
static void demanded_masks(void)
{
    LpUnit u;
    parse(&u,"    and #$00FF\n    clc\n    adc #$002A\n    and #$003F\n");
    lp_demanded_masks(&u,&function,0);assert(find(&u,"and #$00FF",0)->deleted);lp_free(&u);
    parse(&u,"    and #$00F0\n    clc\n    adc #$0011\n    and #$00F0\n");
    lp_demanded_masks(&u,&function,0);assert(!find(&u,"and #$00F0",0)->deleted);lp_free(&u);
    parse(&u,"    and #$00FF\n    clc\n    adc #$002A\n    bcs :+\n    and #$003F\n:\n");
    lp_demanded_masks(&u,&function,0);assert(!find(&u,"and #$00FF",0)->deleted);lp_free(&u);
    parse(&u,"    ora #$0000\n    beq :+\n:\n");
    lp_demanded_masks(&u,&function,0);assert(!find(&u,"ora #$0000",0)->deleted);lp_free(&u);
    parse(&u,"    ora #$0000\n    xba\n    and #$00FF\n");
    lp_demanded_masks(&u,&function,0);assert(find(&u,"ora #$0000",0)->deleted);lp_free(&u);
}
static void private_steps(void)
{
    LpUnit u;
    parse(&u,"    lda z:__arith_lhs+8\n    inc a\n    sta z:__arith_lhs+8\n    lda #7\n");
    assert(lp_memory_word_steps(&u,&function,0));assert(find(&u,"lda z:__arith_lhs+8",0)->replace);lp_free(&u);
    parse(&u,"    lda z:__arith_lhs+8\n    dec a\n    sta z:__arith_lhs+8\n    sta a:.loword(_outside)\n");
    assert(!lp_memory_word_steps(&u,&function,0));lp_free(&u);
    parse(&u,"    sep #$20\n.a8\n    lda z:__arith_lhs+8\n    inc a\n    sta z:__arith_lhs+8\n    lda #7\n");
    assert(!lp_memory_word_steps(&u,&function,0));lp_free(&u);
}
static void cfg_accumulator(void)
{
    LpUnit u;setup();
    parse(&u,"    lda a:.loword(_outside),x\n    bpl cg_join\n    nop\ncg_join = *\n    lda a:.loword(_outside),x\n    cmp #12\n");
    assert(lp_cfg_accumulator(&u,&function,0));assert(find(&u,"lda a:.loword(_outside),x",1)->deleted);lp_free(&u);
    parse(&u,"    beq cg_left\n    lda #1\n    sta z:__arith_lhs\n    bra cg_join\ncg_left = *\n    lda #2\n    sta z:__arith_lhs\ncg_join = *\n    lda z:__arith_lhs\n");
    assert(lp_cfg_accumulator(&u,&function,0));assert(find(&u,"lda z:__arith_lhs",0)->deleted);lp_free(&u);
    parse(&u,"    beq cg_left\n    lda z:__arith_lhs\n    bra cg_join\ncg_left = *\n    lda z:__arith_rhs\ncg_join = *\n    lda z:__arith_lhs\n");
    assert(!lp_cfg_accumulator(&u,&function,0));lp_free(&u);
    parse(&u,"    lda z:__arith_rhs\ncg_loop = *\n    lda z:__arith_lhs\n    inx\n    bne cg_loop\n");
    assert(!lp_cfg_accumulator(&u,&function,0));lp_free(&u);
    parse(&u,"    lda z:__arith_lhs\ncg_loop = *\n    lda z:__arith_lhs\n    inx\n    bne cg_loop\n");
    assert(lp_cfg_accumulator(&u,&function,0));assert(find(&u,"lda z:__arith_lhs",1)->deleted);lp_free(&u);
    parse(&u,"    lda a:.loword(_outside),x\n    inx\ncg_join = *\n    lda a:.loword(_outside),x\n");
    assert(!lp_cfg_accumulator(&u,&function,0));lp_free(&u);
    parse(&u,"    lda a:.loword(_outside),x\n    sta a:.loword(_outside+1),x\ncg_join = *\n    lda a:.loword(_outside),x\n");
    assert(!lp_cfg_accumulator(&u,&function,0));lp_free(&u);
    parse(&u,"    lda a:.loword(_outside),x\n    sta ($10)\ncg_join = *\n    lda a:.loword(_outside),x\n");
    assert(!lp_cfg_accumulator(&u,&function,0));lp_free(&u);
    parse(&u,"    lda z:__arith_lhs\n    jsr .loword(_unresolved)\ncg_join = *\n    lda z:__arith_lhs\n");
    assert(!lp_cfg_accumulator(&u,&function,0));lp_free(&u);
    parse(&u,"    lda a:.loword(_volatile_io)\ncg_join = *\n    lda a:.loword(_volatile_io)\n");
    assert(!lp_cfg_accumulator(&u,&function,0));lp_free(&u);
    parse(&u,"    lda z:__arith_lhs\n    sep #$20\n.a8\n    sta z:__arith_lhs+1\n    rep #$20\n.a16\ncg_join = *\n    lda z:__arith_lhs\n");
    assert(!lp_cfg_accumulator(&u,&function,0));lp_free(&u);
    parse(&u,"    lda a:$0001,y\n    iny\ncg_join = *\n    lda a:$0001,y\n");
    assert(!lp_cfg_accumulator(&u,&function,0));lp_free(&u);
    parse(&u,"    lda z:__arith_lhs\n    xba\ncg_join = *\n    lda z:__arith_lhs\n");
    assert(!lp_cfg_accumulator(&u,&function,0));lp_free(&u);
    parse(&u,"    lda z:__arith_lhs\nexternal_entry:\n    lda z:__arith_lhs\n");
    assert(!lp_cfg_accumulator(&u,&function,0));lp_free(&u);
    parse(&u,"    lda z:__arith_lhs\n    cmp #1\ncg_join = *\n    lda z:__arith_lhs\n    beq cg_end\ncg_end = *\n");
    assert(!lp_cfg_accumulator(&u,&function,0));lp_free(&u);
    parse(&u,"    lda z:__arith_lhs\n    cmp #0\ncg_join = *\n    lda z:__arith_lhs\n    beq cg_end\ncg_end = *\n");
    assert(lp_cfg_accumulator(&u,&function,0));assert(find(&u,"lda z:__arith_lhs",1)->deleted);lp_free(&u);
    parse(&u,"    lda z:__arith_lhs\n    bpl cg_join\n    nop\ncg_join = *\n    lda z:__arith_lhs\n    beq cg_end\ncg_end = *\n");
    assert(lp_cfg_accumulator(&u,&function,0));assert(find(&u,"lda z:__arith_lhs",1)->deleted);lp_free(&u);
    /* The first deleted load cannot supply phantom flags to delete the second */
    parse(&u,"    lda z:__arith_lhs\n    cmp #1\ncg_join = *\n    lda z:__arith_lhs\n    lda z:__arith_lhs\n    beq cg_end\ncg_end = *\n");
    assert(lp_cfg_accumulator(&u,&function,0));assert(find(&u,"lda z:__arith_lhs",1)->deleted&&!find(&u,"lda z:__arith_lhs",2)->deleted);
    code("; reanalyse\n");lp_emit(&u,0);lp_free(&u);lp_parse(&u,cg.assembly,cg.length);assert(!lp_cfg_accumulator(&u,&function,0));lp_free(&u);
}
static void cfg_index(void)
{
    LpUnit u;
    parse(&u,"    ldx z:__arith_lhs\n    bpl cg_join\n    nop\ncg_join = *\n    ldx z:__arith_lhs\n    beq cg_end\ncg_end = *\n");
    assert(lp_cfg_index(&u,&function,0));
    assert(find(&u,"ldx z:__arith_lhs",1)->deleted);lp_free(&u);
    parse(&u,"    ldx z:__arith_lhs\n    sep #$20\n.a8\n    sta z:__arith_lhs+1\n    rep #$20\n.a16\ncg_join = *\n    ldx z:__arith_lhs\n");
    assert(!lp_cfg_index(&u,&function,0));lp_free(&u);
}
static int reject_edit(LpUnit *u,Function *f,size_t at)
{
    LpLine *jump=find(u,"jmp .loword(cg_end)",0);
    assert(jump->target==1);
    jump->target=-1;
    lp_set(jump,"    nop");
    return 0;
}
static int check_then_edit(LpUnit *u,Function *f,size_t at)
{
    if(lp_line_is(&u->lines[0],"nop")){
        assert(u->lines[1].target==2);
        return 0;
    }
    LpLine *jump=find(u,"jmp .loword(cg_end)",0);
    assert(jump->target==1&&!jump->replace);
    lp_insert(jump,"    nop\n");
    return 1;
}
static void runner_reparse(void)
{
    LpRunner runner={0};
    code("    jmp .loword(cg_end)\ncg_end = *\ncg_end:\n    rts\n");
    /* Both label spellings resolve to the first definition (line 1) */
    assert(!lp_run(&runner,&function,0,reject_edit));
    assert(lp_run(&runner,&function,0,check_then_edit));
    lp_invalidate(&runner);free(runner.work);free(cg.assembly);
}
static void assembly_facts(void)
{
    LpUnit u;PrState *states;LpLine *home;unsigned i,m,x;
    static const char *const pushes[]={"pha\n","phx\n","phy\n","php\n","phb\n","phk\n","phd\n","pea\n","pei\n","per\n"};
    static const char *const pulls[]={"pla\n","plx\n","ply\n","plp\n","plb\n","pld\n"};
    const char *source="start:\n.a8\n    pha\n.a16\n.i8\n    phx\n.i16\n    pei ($20)\n"
        "    bne :++\n:\n    bne :--\nalias = *\n    jmp .loword(alias)\n:\n    bne :--\n"
        "alias:\n    jmp absent\n    jmp (table,x)\n.word 0\n.byte 1";
    lp_parse(&u,source,strlen(source));
    assert(u.lines[2].m8&&!u.lines[2].x8&&u.lines[5].x8&&!u.lines[5].m8);
    assert(!u.lines[7].m8&&!u.lines[7].x8);
    assert(u.lines[8].target==13&&u.lines[10].target==-1&&u.lines[14].target==9);
    assert(u.lines[12].target==11&&u.lines[16].target==-1&&u.lines[16].call);
    assert(u.lines[17].indirect&&u.indirect);lp_free(&u);
    {AssemblyLabels labels;const char *op;int m8=0,x8=0;
     assembly_labels_init(&labels,0);
     assert(assembly_label_target(&labels,0,":+-",3)==-1);
     assert(assembly_label_target(&labels,0,":+",2)==-1);
     assert(assembly_label_target(&labels,0,"missing",7)==-1);
     assembly_labels_free(&labels);
     assert(!assembly_decode("    ; comment",13,&m8,&x8,&op)&&!op);
     assert(!assembly_decode("     lda #0",11,&m8,&x8,&op)&&!op);}
    for(m=0;m<2;++m)for(x=0;x<2;++x){
        for(i=0;i<sizeof pushes/sizeof *pushes;++i){
            int expected=i==0?(m?1:2):i<3?(x?1:2):i<6?1:2;
            assert(assembly_stack_bytes(pushes[i],m,x)==expected);
        }
        for(i=0;i<sizeof pulls/sizeof *pulls;++i){
            int expected=i==0?(m?-1:-2):i<3?(x?-1:-2):i<5?-1:-2;
            assert(assembly_stack_bytes(pulls[i],m,x)==expected);
        }
    }
    {FrameLine line={0};line.op="tcs\n";
     assert(!assembly_stack_bytes(line.op,0,0)&&frame_stack_delta(&line)==99);}
    parse(&u,"    phy\n    pei ($20)\n    pla\n.a8\n    pha\n    pla\n.a16\n    ply\n    sta a:$0001,y\n");
    states=pr_states(&u);home=find(&u,"sta a:$0001,y",0);
    assert(states[home-u.lines].frame);free(states);lp_free(&u);
}
int main(void){setup();assembly_facts();dead_stores();provenance();copies();demanded_masks();private_steps();cfg_accumulator();cfg_index();free(cg.assembly);setup();runner_reparse();puts("PASS shared assembly facts, private region memory effects, byte liveness, CFG/Y-stack joins and guards");return 0;}
