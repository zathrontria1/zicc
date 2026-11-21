// Read C source, check its types, and write 65816 assembly
// POSIX 2008 with X/Open, so glibc declares realpath under -std=c17
#if !defined(_WIN32) && !defined(_XOPEN_SOURCE)
#define _XOPEN_SOURCE 700
#endif
#include <ctype.h>
#include <errno.h>
#include <stdarg.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#ifndef _WIN32
#include <unistd.h>
#endif
#include "headers/preprocess.h"

static int binary64_enabled;
static int large_rom_objects;
static unsigned sram_first_bank, sram_window_size, sram_capacity;
#include "headers/relax.h"

enum { TOK_EOF = 256, TOK_NAME, TOK_NUMBER, TOK_STRING, TOK_INT, TOK_VOID,
       TOK_CHAR, TOK_BOOL, TOK_CONST, TOK_STRUCT, TOK_TYPEDEF, TOK_EXTERN, TOK_WHILE,
       TOK_RETURN, TOK_ELLIPSIS, TOK_FLOAT, TOK_DOUBLE, TOK_LONG, TOK_UNSIGNED, TOK_SIGNED,
       TOK_SHORT, TOK_STATIC, TOK_DPAGE, TOK_IF, TOK_ELSE, TOK_SIZEOF, TOK_INC,
       TOK_DEC, TOK_EQ, TOK_NE, TOK_LE, TOK_GE, TOK_LAND, TOK_LOR, TOK_SHL,
       TOK_SHR, TOK_ADDEQ, TOK_SUBEQ, TOK_MULEQ, TOK_DIVEQ, TOK_MODEQ,
       TOK_ANDEQ, TOK_OREQ, TOK_XOREQ, TOK_SHLEQ, TOK_SHREQ, TOK_BREAK,
       TOK_CONTINUE, TOK_FOR, TOK_DO, TOK_ARROW, TOK_INTERRUPT, TOK_ENUM, TOK_UNION, TOK_REGISTER, TOK_AUTO, TOK_GOTO, TOK_SWITCH, TOK_CASE, TOK_DEFAULT, TOK_FAR, TOK_VOLATILE, TOK_LORAM,
       TOK_INLINE, TOK_FORCEINLINE, TOK_NOINLINE, TOK_ATTRIBUTE, TOK_HIRAM, TOK_XBANKRAM, TOK_SRAM };
enum { INT_NONE, INT_NMI, INT_IRQ, INT_BRK, INT_COP };
enum { WRAM_NONE, WRAM_HIRAM, WRAM_XBANK, WRAM_LORAM, WRAM_SRAM_FIRST };
enum { MAX_WRAM_OBJECT = 0x1fe00, MAX_ROM_OBJECT = 0x400000 };
/* The compiler uses TY_STRUCT for both structs and unions. The parser checks
 * Structure.is_union to lay out and initialize their members. */
typedef enum { TY_INT, TY_VOID, TY_CHAR, TY_STRUCT, TY_LONG, TY_FLOAT, TY_FUNCTION, TY_LONGLONG, TY_DOUBLE } BaseType;
typedef struct Structure Structure;
typedef struct Type Type;
typedef struct FunctionType FunctionType;
/* far_pointers tracks which pointers can reach other banks. The banked flag
 * tells us where the object lives without changing its C type. */
struct Type { BaseType base; unsigned pointers, tag, array; int constant, is_unsigned, is_volatile; unsigned pointer_constants, pointer_volatiles, far_pointers; int banked; Structure *structure; unsigned enum_tag; Type *element; int is_bool, is_short, is_plain_char; unsigned bit_field_width; FunctionType *signature; };
struct FunctionType { Type result; int count, variadic; char (*names)[64]; Type parameters[]; };
typedef struct Member Member;
struct Member { char name[64]; Type type; unsigned offset, bit_width, bit_shift; Member *next; };
struct Structure {
    char name[64]; unsigned size, complete, defining, owner, scope, active, is_enum, is_union;
    Member *members;
};
typedef struct { const char *path; int line, column; } Location;
typedef struct {
    int kind; Location location; uint32_t number, number_high; Type number_type;
    char name[64]; unsigned char bytes[1024]; size_t length;
} Token;
typedef struct Symbol Symbol;
typedef struct Relocation Relocation;
struct Relocation { unsigned offset, size; int32_t addend; Symbol *symbol; struct String *string; int far_value; Relocation *next; };
enum { MAX_PARAMETERS=127, MAX_ARGUMENTS=256, STACK_BYTES=1024, MAX_RETURN_ADDRESS_BYTES=3 };
struct Symbol {
    char name[64], asm_name[128]; Type type;
    int function, param_count, variadic, defined, used, external, dpage, internal, loram;
    int old_style, copy_temporary, placement_used, runtime_ram, block_linkage, implicit_library;
    int interrupt, called, zero_arguments_inert, address_taken, adapter_used;
    int inline_hint, always_inline, noinline, noclone, inline_external;
    int inline_instances, inline_omit;
    int enumerator; uint32_t enum_value;
    unsigned owner, scope, offset; int active;
    unsigned char *initializer;
    Relocation *relocations;
    Symbol *storage;
    int embedded, near_nowrap, wram, wram_near;
    Type params[MAX_PARAMETERS];
    char param_names[MAX_PARAMETERS][64];
};
typedef struct { char name[64]; Type type; unsigned owner, scope, active; } Alias;
typedef struct String String;
struct String { unsigned id; size_t size; unsigned char *bytes; int used; String *next; };
typedef enum { EX_INT, EX_STRING, EX_OBJECT, EX_ADDRESS, EX_CALL, EX_DEREF,
               EX_CAST, EX_UNARY, EX_BINARY, EX_ASSIGN, EX_POST, EX_PRE, EX_CHOOSE, EX_MEMBER, EX_COMMA, EX_VA_START, EX_RESULT_ADDR, EX_BITFIELD } ExprKind;
typedef struct Expr Expr;
typedef struct { unsigned zero,one;int32_t min,max;int valid; } KnownValue;
struct Expr {
    ExprKind kind; Type type; Location location; uint32_t value, value_high; int op;
    Symbol *symbol; String *string; Expr *args[MAX_ARGUMENTS]; unsigned arg_count;
    Expr *left, *right, *third;
    KnownValue known,range;
    int known_no_conversion, known_nonnull;
};
typedef enum { ST_BLOCK, ST_EMPTY, ST_WHILE, ST_RETURN, ST_EXPR, ST_IF,
               ST_BREAK, ST_CONTINUE, ST_FOR, ST_DO, ST_SWITCH, ST_CASE, ST_GOTO, ST_LABEL } StatementKind;
typedef struct Statement Statement;
struct Statement {
    StatementKind kind; Location location; unsigned id;
    Expr *expression, *step; Statement *body, *next, *alternate, *initial;
    Statement *cases, *case_next; /* non-owning switch label index */
    Symbol *inline_callee; /* zero-byte execution marker */
    uint32_t case_value, case_value_high; unsigned case_label; int is_default;
    unsigned jump_label;
};
typedef struct JumpLabel JumpLabel;
struct JumpLabel { char name[64]; Location location; unsigned id; int defined; JumpLabel *next; };
typedef struct Function Function;
struct Function { Symbol *symbol; Statement *body; unsigned id, slots, frame, jump_label_count; int uses_varargs, aggregate_abi, uses_bitfields, uses_wide, ipa_internal; KnownValue ipa_known[16]; unsigned char ipa_known_valid[16]; JumpLabel *jump_labels; Function *next; };
typedef struct {
    EmbeddedRange *embeds;
    const char *path; char *source; size_t position; int line, column;
    unsigned next_id; Token token;
    Symbol symbols[1024]; unsigned symbol_count;
    Alias aliases[64]; unsigned alias_count;
    Structure tags[64]; unsigned tag_count;
    char *paths[128]; unsigned path_count;
    String *strings, **string_tail; unsigned string_count;
    Function *functions, **function_tail, *current;
    unsigned function_count, scope, loop_depth, parse_depth;
    Statement *current_switch;
    char unit[64];
    int no_strength_reduction;
    int no_indexed_dpage;
    int no_direct_dpage;
    int no_indexed_operands;
    int no_loop_index_retention;
    int no_known_values;
    int no_byte_shuffles,no_store_fusion;
    int no_private_regions;
    int no_value_reuse;
    int no_branch_relaxation;
    int no_divmod_reuse;
    int no_register_loops;
    int no_dp_counters;
    int no_dp_homes;
    int no_stack_frames;
    int no_line_passes;
    int rom_default_rounding;
    int no_register_cursors;
    int no_dp_summaries;
    int no_index_elimination;
    int no_region_homes;
    int no_loop_unroll;
    int no_body_optimizations;
    int no_inline,c89_keywords;
    int source_lto;
    int no_copy_selection;
    int no_bank_specialization;
    int long_return;
    const char *long_calls;
    const char *runtime_objects;
    const char *near_wram_objects;
} Parser;

static Type type(BaseType base, unsigned pointers)
{
    Type t = {0}; t.base = base; t.pointers = pointers; t.is_unsigned = base == TY_CHAR; return t;
}
static void *allocate(size_t size);
/* Derived types keep their immediate element when arrays occur inside the
 * declarator. Plain scalar pointers retain the compact depth representation. */
static Type *type_copy(Type t)
{
    Type *copy=allocate(sizeof *copy);*copy=t;return copy;
}
static Type array_element(Type t)
{
    if(t.element)t=*t.element;else t.array=0;
    return t;
}
static unsigned pointer_bit(unsigned depth) { return depth<32?1u<<depth:0; }
static int far_pointer(Type t) { return t.pointers&&(t.far_pointers&pointer_bit(t.pointers))!=0; }
static Type far_type(Type t) { t.far_pointers|=pointer_bit(t.pointers);return t; }
static int function_type(Type t){return t.base==TY_FUNCTION&&!t.pointers&&!t.array;}
static int function_pointer(Type t){return t.base==TY_FUNCTION&&t.pointers==1&&!t.element&&!t.array;}
static Type function_signature(Type result,int count,int variadic,const Type *parameters)
{
    Type t=type(TY_FUNCTION,0);
    unsigned n=count<0?0:(unsigned)count;
    t.signature=allocate(sizeof *t.signature+n*sizeof *parameters);
    t.signature->result=result;t.signature->count=count;t.signature->variadic=variadic;
    if(n)memcpy(t.signature->parameters,parameters,n*sizeof *parameters);
    return t;
}
static Type pointer_to(Type t)
{
    int banked=t.banked||function_type(t);
    if(t.array||t.element){Type result=t;result.element=type_copy(t);result.array=0;result.pointers=1;result.pointer_constants=0;result.pointer_volatiles=0;result.far_pointers=banked?2:0;result.banked=0;return result;}
    ++t.pointers;t.banked=0;if(banked)t=far_type(t);return t;
}
static Type value_type(Type t) { if(t.array){Type element=array_element(t);element.banked=t.banked;t=pointer_to(element);}else if(function_type(t))t=pointer_to(t);return t; }
/* Bit n qualifies the pointer at depth n; bit zero is represented by constant.
 * Member qualification can therefore make a pointer field read-only without
 * accidentally qualifying the object to which that field points. */
static int object_constant(Type t) { return t.pointers?(t.pointer_constants&pointer_bit(t.pointers))!=0:t.constant; }
static Type const_object(Type t)
{
    if(t.array){
        Type element=const_object(array_element(t));t.element=type_copy(element);
        t.constant|=element.constant;
    }else if(t.pointers)t.pointer_constants|=pointer_bit(t.pointers);
    else t.constant=1;
    return t;
}
static int object_volatile(Type t) { return t.pointers?(t.pointer_volatiles&pointer_bit(t.pointers))!=0:t.is_volatile; }
static Type volatile_object(Type t)
{
    if(t.array){Type element=volatile_object(array_element(t));t.element=type_copy(element);t.is_volatile|=element.is_volatile;}
    else if(t.pointers)t.pointer_volatiles|=pointer_bit(t.pointers);
    else t.is_volatile=1;
    return t;
}
static Type unqualified_value(Type t)
{
    t=value_type(t);if(t.pointers){t.pointer_constants&=~pointer_bit(t.pointers);t.pointer_volatiles&=~pointer_bit(t.pointers);}else{t.constant=0;t.is_volatile=0;}return t;
}
static Type pointed_type(Type t)
{
    int banked=far_pointer(t);
    if(t.element){t=*t.element;t.banked=banked;return t;}
    t.pointer_constants&=~pointer_bit(t.pointers);t.pointer_volatiles&=~pointer_bit(t.pointers);t.far_pointers&=~pointer_bit(t.pointers);--t.pointers;t.banked=banked;return t;
}
static unsigned object_extent_limit(void)
{
    if(large_rom_objects)return MAX_ROM_OBJECT;
    return sram_capacity>MAX_WRAM_OBJECT?sram_capacity:MAX_WRAM_OBJECT;
}
static unsigned width(Type t)
{
    unsigned count=t.array?t.array:1, bytes;
    unsigned limit=object_extent_limit();
    if(t.array==~0u)return 0;
    if(t.array&&t.element)bytes=width(*t.element);
    else{
        t.array=0;
        if(t.pointers)bytes=far_pointer(t)?4:2;
        else if(t.base==TY_STRUCT)bytes=t.structure&&t.structure->complete?t.structure->size:0;
        else bytes=t.base==TY_CHAR?1:t.base==TY_INT?2:(t.base==TY_LONG||t.base==TY_FLOAT)?4:(t.base==TY_LONGLONG||t.base==TY_DOUBLE)?8:0;
    }
    return bytes&&count>limit/bytes?limit+1u:count*bytes;
}
static unsigned object_size_limit(const Symbol *s)
{
    if(s->wram==WRAM_XBANK)return MAX_WRAM_OBJECT;
    if(large_rom_objects&&s->type.banked&&!s->wram&&!s->runtime_ram)return MAX_ROM_OBJECT;
    return s->type.banked&&!s->runtime_ram?65536u:65534u;
}
static unsigned value_width(Type t) { return width(value_type(t)); }
static int structure_object(Type t) { return t.base==TY_STRUCT&&!t.pointers; }
static unsigned alignment(Type t) { return t.array&&t.element?alignment(*t.element):!t.pointers&&t.base==TY_CHAR?1:2; }
static Type declaration_base(Parser *p);
static Type enum_specifier(Parser *p);
static void structure_definition(Parser *p,Structure *record);
static void free_expression(Expr *e);
static void free_statements(Statement *s);
static void error_at(Location at, const char *format, ...)
{
    va_list args;
    fprintf(stderr, "%s:%d:%d: error: ", at.path, at.line, at.column);
    va_start(args, format); vfprintf(stderr, format, args); va_end(args);
    fputc('\n', stderr); exit(EXIT_FAILURE);
}
static void warning_at(Location at,const char *format,...)
{
    va_list args;
    fprintf(stderr,"%s:%d:%d: warning: ",at.path,at.line,at.column);
    va_start(args,format);vfprintf(stderr,format,args);va_end(args);fputc('\n',stderr);
}
static Location here(Parser *p)
{
    Location at = {p->path, p->line, p->column}; return at;
}
static void *allocate(size_t size)
{
    void *memory = calloc(1, size);
    if (!memory) { fputs("zicc: out of memory\n", stderr); exit(EXIT_FAILURE); }
    return memory;
}
static const char *intern_path(Parser *p, const char *path)
{
    unsigned i;
    for (i = 0; i < p->path_count; ++i) if (!strcmp(p->paths[i], path)) return p->paths[i];
    if (p->path_count == 128) error_at(here(p), "too many source files");
    p->paths[p->path_count] = allocate(strlen(path) + 1);
    strcpy(p->paths[p->path_count], path);
    return p->paths[p->path_count++];
}
static int peek(Parser *p) { return (unsigned char)p->source[p->position]; }
static void advance(Parser *p)
{
    int c = peek(p);
    if (!c) return;
    ++p->position;
    if (c == '\n') { ++p->line; p->column = 1; } else ++p->column;
}
static unsigned escaped_byte(Parser *p)
{
    unsigned value; int c = peek(p);
    if (!c || c == '\n' || c == '\r') error_at(here(p), "unterminated string/character literal");
    advance(p);
    if (c != '\\') return (unsigned)c;
    c = peek(p); advance(p);
    switch (c) {
    case 'a': return 7; case 'b': return 8; case 't': return 9; case 'n': return 10;
    case 'v': return 11; case 'f': return 12; case 'r': return 13;
    case '\\': case '\'': case '"': case '?': return (unsigned)c;
    default:
        if (c >= '0' && c <= '7') {
            int i; value = (unsigned)(c - '0');
            for (i = 0; i < 2 && peek(p) >= '0' && peek(p) <= '7'; ++i) {
                value = value * 8 + (unsigned)(peek(p) - '0'); advance(p);
            }
        } else if (c == 'x') {
            value = 0;
            if (!isxdigit(peek(p))) error_at(here(p), "hex escape needs digits");
            while (isxdigit(peek(p))) {
                int d = peek(p);
                value = value * 16 + (unsigned)(isdigit(d) ? d - '0' : tolower(d) - 'a' + 10);
                if (value > 255) error_at(here(p), "escape exceeds one byte");
                advance(p);
            }
        } else error_at(here(p), "unsupported escape sequence");
        if (value > 255) error_at(here(p), "escape exceeds one byte");
        return value;
    }
}
static void lex(Parser *p)
{
    Token *t = &p->token;
    for (;;) {
        while (isspace(peek(p))) advance(p);
        if (peek(p) == '#') {
            char path[2048]; int line, consumed=0; size_t length=0;
            if (sscanf(p->source + p->position, "#line %d \"%n", &line, &consumed) != 1 || !consumed)
                error_at(here(p), "invalid source location marker");
            p->position+=(size_t)consumed;
            while (peek(p)!='"') {
                unsigned byte=escaped_byte(p);
                if (!byte || length+1>=sizeof path) error_at(here(p),"invalid source path");
                path[length++]=(char)byte;
            }
            path[length]=0;
            while (peek(p) && peek(p) != '\n') advance(p);
            advance(p); p->path = intern_path(p, path); p->line = line; p->column = 1;
            continue;
        }
        if (peek(p) != '/') break;
        if (p->source[p->position + 1] == '/') {
            while (peek(p) && peek(p) != '\n') advance(p);
        } else if (p->source[p->position + 1] == '*') {
            Location at = here(p); advance(p); advance(p);
            while (peek(p) && !(peek(p) == '*' && p->source[p->position + 1] == '/')) advance(p);
            if (!peek(p)) error_at(at, "unterminated comment");
            advance(p); advance(p);
        } else break;
    }
    memset(t, 0, sizeof *t); t->location = here(p);
    if (!peek(p)) { t->kind = TOK_EOF; return; }
    if (isalpha(peek(p)) || peek(p) == '_') {
        static const struct { const char *name; int kind; } keywords[] = {
            {"int",TOK_INT},{"void",TOK_VOID},{"char",TOK_CHAR},{"_Bool",TOK_BOOL},{"const",TOK_CONST},{"volatile",TOK_VOLATILE},
            {"__const",TOK_CONST},{"__const__",TOK_CONST},{"__volatile",TOK_VOLATILE},{"__volatile__",TOK_VOLATILE},
            {"union",TOK_UNION},{"struct",TOK_STRUCT},{"typedef",TOK_TYPEDEF},{"extern",TOK_EXTERN},
            {"while",TOK_WHILE},{"return",TOK_RETURN},{"float",TOK_FLOAT},{"double",TOK_DOUBLE},
            {"long",TOK_LONG},{"unsigned",TOK_UNSIGNED},{"signed",TOK_SIGNED},{"short",TOK_SHORT},
            {"__signed",TOK_SIGNED},{"__signed__",TOK_SIGNED},
            {"static",TOK_STATIC},{"__dpage",TOK_DPAGE},{"__loram",TOK_LORAM},
            {"__hiram",TOK_HIRAM},{"__farram",TOK_HIRAM},{"__xbankram",TOK_XBANKRAM},{"__sram",TOK_SRAM},{"if",TOK_IF},{"else",TOK_ELSE},
            {"inline",TOK_INLINE},{"__inline",TOK_INLINE},{"__inline__",TOK_INLINE},
            {"__forceinline",TOK_FORCEINLINE},{"__noinline",TOK_NOINLINE},{"__attribute",TOK_ATTRIBUTE},{"__attribute__",TOK_ATTRIBUTE},
            {"sizeof",TOK_SIZEOF},{"break",TOK_BREAK},{"continue",TOK_CONTINUE},{"for",TOK_FOR},{"do",TOK_DO},
            {"__far",TOK_FAR},{"case",TOK_CASE},{"default",TOK_DEFAULT},{"switch",TOK_SWITCH},{"register",TOK_REGISTER},{"auto",TOK_AUTO},{"goto",TOK_GOTO},{"__interrupt",TOK_INTERRUPT},{"enum",TOK_ENUM}
        };
        size_t n = 0, i;
        while (isalnum(peek(p)) || peek(p) == '_') {
            if (n + 1 >= sizeof t->name) error_at(t->location, "identifier too long");
            t->name[n++] = (char)peek(p); advance(p);
        }
        t->kind = TOK_NAME;
        for (i = 0; i < sizeof keywords / sizeof keywords[0]; ++i)
            if (!strcmp(t->name, keywords[i].name) &&
                !(p->c89_keywords && keywords[i].kind==TOK_INLINE && t->name[0]!='_'))
                t->kind = keywords[i].kind;
        return;
    }
    if (peek(p) == '"') {
        advance(p); t->kind = TOK_STRING;
        while (peek(p) != '"') {
            if (t->length + 1 >= sizeof t->bytes) error_at(t->location, "string literal too long");
            t->bytes[t->length++] = (unsigned char)escaped_byte(p);
        }
        advance(p); return;
    }
    if (peek(p) == '\'') {
        advance(p); t->kind = TOK_NUMBER; t->number = escaped_byte(p); t->number_type=type(TY_INT,0);
        if (peek(p) != '\'') error_at(t->location, "expected one character");
        advance(p); return;
    }
    if (isdigit(peek(p)) || (peek(p)=='.' && isdigit((unsigned char)p->source[p->position+1]))) {
        char literal[128], *end; size_t n = 0; unsigned long long value;
        int floating=0, is_unsigned=0, is_long=0, decimal;
        while (isalnum(peek(p)) || peek(p)=='.' || peek(p)=='_' ||
               ((peek(p)=='+'||peek(p)=='-') && n && (literal[n-1]=='e'||literal[n-1]=='E'||literal[n-1]=='p'||literal[n-1]=='P'))) {
            if (n + 1 >= sizeof literal) error_at(t->location, "integer literal too long");
            literal[n++] = (char)peek(p); advance(p);
        }
        literal[n]=0;
        if (strchr(literal,'.') || ((literal[1]!='x'&&literal[1]!='X') && (strchr(literal,'e')||strchr(literal,'E'))) || strchr(literal,'p')||strchr(literal,'P')) floating=1;
        t->kind=TOK_NUMBER;
        if (floating) {
            float f; double d; uint64_t bits; size_t len=strlen(literal);
            if(binary64_enabled&&!(len&&(literal[len-1]=='f'||literal[len-1]=='F'))){
                errno=0;d=strtod(literal,&end);
                if((*end=='l'||*end=='L')&&!end[1])++end;
                if(*end)error_at(t->location,"invalid floating literal");
                memcpy(&bits,&d,sizeof bits);t->number=(uint32_t)bits;t->number_high=(uint32_t)(bits>>32);
                t->number_type=type(TY_DOUBLE,0);return;
            }
            errno=0; f=strtof(literal,&end);
            if ((*end=='f'||*end=='F'||*end=='l'||*end=='L') && !end[1]) ++end;
            if (*end) error_at(t->location,"invalid floating literal");
            memcpy(&t->number,&f,4); t->number_type=type(TY_FLOAT,0); return;
        }
        errno=0; value=strtoull(literal,&end,0);decimal=literal[0]!='0';
        if(*end=='u'||*end=='U'){is_unsigned=1;++end;}
        if(*end=='l'||*end=='L'){
            char first=*end++;is_long=1;
            if(*end==first){is_long=2;++end;}
        }
        if(*end=='u'||*end=='U'){if(is_unsigned)error_at(t->location,"invalid integer suffix");is_unsigned=1;++end;}
        if(errno||*end)error_at(t->location,"invalid/out-of-range integer literal");
        if(is_long==2){
            if(!is_unsigned&&value>INT64_MAX){if(decimal)error_at(t->location,"invalid/out-of-range integer literal");is_unsigned=1;}
        }else if(is_unsigned){
            if(value>UINT32_MAX)is_long=2;else if(is_long||value>65535u)is_long=1;
        }else if(decimal){
            if(value>INT64_MAX)error_at(t->location,"invalid/out-of-range integer literal");
            if(value>INT32_MAX)is_long=2;else if(is_long||value>32767u)is_long=1;
        }else if(!is_long&&value<=32767u){
            /* signed int */
        }else if(!is_long&&value<=65535u){is_unsigned=1;
        }else if(value<=INT32_MAX){is_long=1;
        }else if(value<=UINT32_MAX){is_long=1;is_unsigned=1;
        }else{is_long=2;if(value>INT64_MAX)is_unsigned=1;}
        t->number=(uint32_t)value;t->number_high=(uint32_t)(value>>32);
        t->number_type=type(is_long==2?TY_LONGLONG:is_long?TY_LONG:TY_INT,0);t->number_type.is_unsigned=is_unsigned;return;
    }
    if (peek(p) == '.' && !strncmp(p->source + p->position, "...", 3)) {
        advance(p); advance(p); advance(p); t->kind = TOK_ELLIPSIS; return;
    }
    {
        static const struct { const char *text; int kind; } operators[]={
            {"<<=",TOK_SHLEQ},{">>=",TOK_SHREQ},{"++",TOK_INC},{"--",TOK_DEC},{"->",TOK_ARROW},
            {"==",TOK_EQ},{"!=",TOK_NE},{"<=",TOK_LE},{">=",TOK_GE},{"&&",TOK_LAND},
            {"||",TOK_LOR},{"<<",TOK_SHL},{">>",TOK_SHR},{"+=",TOK_ADDEQ},{"-=",TOK_SUBEQ},
            {"*=",TOK_MULEQ},{"/=",TOK_DIVEQ},{"%=",TOK_MODEQ},{"&=",TOK_ANDEQ},{"|=",TOK_OREQ},{"^=",TOK_XOREQ}
        };
        size_t i;
        for(i=0;i<sizeof operators/sizeof operators[0];++i) if(!strncmp(p->source+p->position,operators[i].text,strlen(operators[i].text))) {
            size_t j; t->kind=operators[i].kind;for(j=0;j<strlen(operators[i].text);++j)advance(p);return;
        }
    }
    t->kind = peek(p); advance(p);
}
static int accept(Parser *p, int kind)
{
    if (p->token.kind != kind) return 0;
    lex(p); return 1;
}
static void expect(Parser *p, int kind, const char *description)
{
    if (!accept(p, kind)) error_at(p->token.location, "expected %s", description);
}
static Symbol *find_symbol(Parser *p, const char *name)
{
    unsigned i;
    for (i = p->symbol_count; i; --i) if (!strcmp(p->symbols[i-1].name,name) &&
        !p->symbols[i-1].block_linkage &&
        (!p->symbols[i-1].owner || (p->current && p->symbols[i-1].owner==p->current->id && p->symbols[i-1].active))) return &p->symbols[i-1];
    return NULL;
}
static Alias *find_alias(Parser *p,const char *name)
{
    unsigned i;Symbol *s=find_symbol(p,name);
    for(i=p->alias_count;i;--i){
        Alias *a=&p->aliases[i-1];
        if(strcmp(a->name,name)||!a->active||(a->owner&&(!p->current||a->owner!=p->current->id)))continue;
        if(s&&((s->owner&&!a->owner)||(s->owner==a->owner&&s->scope>=a->scope)))return NULL;
        return a;
    }
    return NULL;
}
static Type promoted(Type t);
static Type default_argument_promoted(Type t);
static int same_type(Type a, Type b)
{
    if(a.signature!=b.signature){
        int i;
        if(!a.signature||!b.signature||a.signature->variadic!=b.signature->variadic||
           !same_type(a.signature->result,b.signature->result))return 0;
        if(a.signature->count<0||b.signature->count<0){
            FunctionType *prototype=a.signature->count<0?b.signature:a.signature;
            for(i=0;i<prototype->count;++i){
                Type parameter=unqualified_value(prototype->parameters[i]);
                if(!same_type(parameter,default_argument_promoted(parameter)))return 0;
            }
        }else{
            if(a.signature->count!=b.signature->count)return 0;
            for(i=0;i<a.signature->count;++i)
                if(!same_type(unqualified_value(a.signature->parameters[i]),unqualified_value(b.signature->parameters[i])))return 0;
        }
    }
    return a.base == b.base && a.is_bool == b.is_bool && a.is_short == b.is_short && a.is_plain_char == b.is_plain_char && a.pointers == b.pointers && a.tag == b.tag && a.constant == b.constant && a.is_volatile == b.is_volatile && a.pointer_volatiles == b.pointer_volatiles && a.is_unsigned==b.is_unsigned && a.array==b.array && a.pointer_constants==b.pointer_constants && a.far_pointers==b.far_pointers && ((!a.element&&!b.element)||(a.element&&b.element&&same_type(*a.element,*b.element)));
}
/* Widen only the pointer value being converted, never pointers stored in its referent */
static int compatible_array_referent(Type parameter,Type value)
{
    if(value.constant&&!parameter.constant)return 0;
    if(value.is_volatile&&!parameter.is_volatile)return 0;
    if(value.pointer_volatiles&~parameter.pointer_volatiles)return 0;
    if(value.pointer_constants&~parameter.pointer_constants)return 0;
    parameter.constant=value.constant=0;parameter.pointer_constants=value.pointer_constants=0;
    parameter.is_volatile=value.is_volatile=0;parameter.pointer_volatiles=value.pointer_volatiles=0;
    if(parameter.array&&value.array&&(parameter.array==~0u||value.array==~0u))
        parameter.array=value.array=~0u;
    if(parameter.element&&value.element){
        Type a=*parameter.element,b=*value.element;
        parameter.element=value.element=NULL;
        return same_type(parameter,value)&&compatible_array_referent(a,b);
    }
    return same_type(parameter,value);
}
static int void_pointer(Type t)
{
    return t.base==TY_VOID&&t.pointers==1&&!t.element;
}
static int compatible_argument(Type parameter, const Expr *arg)
{
    Type value = unqualified_value(arg->type); parameter=unqualified_value(parameter);
    if(function_pointer(parameter)||function_pointer(value)){
        if(function_pointer(parameter)&&arg->kind==EX_INT&&!arg->value&&!arg->value_high&&
           ((!value.pointers&&(value.base==TY_INT||value.base==TY_CHAR||value.base==TY_LONG))||
            (value.pointers==1&&value.base==TY_VOID)))return 1;
        return same_type(parameter,value);
    }
    if (!parameter.pointers && !value.pointers && parameter.base!=TY_STRUCT && value.base!=TY_STRUCT && parameter.base!=TY_VOID && value.base!=TY_VOID) return 1;
    if (!parameter.pointers && parameter.base == TY_INT && !value.pointers && value.base == TY_CHAR) return 1;
    if (parameter.pointers && arg->kind == EX_INT && !arg->value&&!arg->value_high) return 1;
    if(parameter.pointers&&value.pointers){
        if(far_pointer(value)&&!far_pointer(parameter))return 0;
        if(far_pointer(parameter))value=far_type(value);
        if(void_pointer(parameter)||void_pointer(value)){
            Type to=pointed_type(parameter),from=pointed_type(value);
            return (!object_constant(from)||object_constant(to))&&
                   (!object_volatile(from)||object_volatile(to));
        }
    }
    if(parameter.element||value.element)return compatible_array_referent(parameter,value);
    if (parameter.pointers == 1 && parameter.constant && !value.constant) value.constant = 1;
    if(parameter.pointers==1&&parameter.is_volatile&&!value.is_volatile)value.is_volatile=1;
    if(parameter.pointers>1&&parameter.pointers==value.pointers){
        unsigned pointee=pointer_bit(parameter.pointers-1);
        value.pointer_constants|=parameter.pointer_constants&pointee;
        value.pointer_volatiles|=parameter.pointer_volatiles&pointee;
    }
    return same_type(parameter, value);
}
static void declaration_qualifiers(Parser *p,int *constant,int *vol)
{
    while(p->token.kind==TOK_CONST||p->token.kind==TOK_VOLATILE){
        if(accept(p,TOK_CONST))*constant=1;else{lex(p);*vol=1;}
    }
}
static int storage_specifier(Parser *p,int *storage,int local)
{
    int kind=p->token.kind;
    if(!storage)return 0;
    if(kind!=TOK_TYPEDEF&&kind!=TOK_STATIC&&
       kind!=TOK_EXTERN&&(!local||(kind!=TOK_AUTO&&kind!=TOK_REGISTER)))return 0;
    if(*storage)error_at(p->token.location,"conflicting storage classes");
    *storage=kind;
    lex(p);
    return 1;
}
static Expr *assignment_expression(Parser *p);
static void integer_constant_operands(Expr *e,const char *context);
static uint64_t initializer_wide_constant(Expr *e,int active);

static int wram_specifier(Parser *p,int *wram)
{
    Location at=p->token.location;
    int kind=p->token.kind==TOK_HIRAM?WRAM_HIRAM:p->token.kind==TOK_XBANKRAM?WRAM_XBANK:
             p->token.kind==TOK_LORAM?WRAM_LORAM:p->token.kind==TOK_SRAM?WRAM_SRAM_FIRST:WRAM_NONE;
    if(!kind)return 0;
    if(!wram)error_at(at,"%s placement requires a static-storage object",kind==WRAM_SRAM_FIRST?"SRAM":"WRAM");
    lex(p);
    if(kind==WRAM_SRAM_FIRST){
        Expr *expr;
        uint64_t bank;
        if(!sram_capacity)error_at(at,"__sram requires a build with --sram-size");
        expect(p,'(',"'(' after __sram");
        expr=assignment_expression(p);
        integer_constant_operands(expr,"__sram window");
        bank=initializer_wide_constant(expr,1);
        free_expression(expr);
        expect(p,')',"')' after __sram window");
        if(bank>(sram_capacity-1)/sram_window_size)
            error_at(at,"__sram window index is outside installed cartridge SRAM");
        kind+=(int)bank;
    }
    if(*wram&&*wram!=kind)
        error_at(at,"conflicting %s placement attributes",
                 kind>=WRAM_SRAM_FIRST||*wram>=WRAM_SRAM_FIRST?"SRAM":"WRAM");
    *wram=kind;return 1;
}
static Type declaration_base_with_storage(Parser *p,int *storage,int local,int *wram)
{
    Type result = type(TY_INT, 0); unsigned i; int found = 0, sign=-1, used_alias=0;
    int constant=0,vol=0;
    int rank=0,has_int=0,long_count=0,has_double=0;
    for(;;){
        int token;
        declaration_qualifiers(p,&constant,&vol);
        if(storage_specifier(p,storage,local)||wram_specifier(p,wram))continue;
        token=p->token.kind;
        if(token==TOK_SIGNED||token==TOK_UNSIGNED){
            if(sign>=0)error_at(p->token.location,"conflicting signed/unsigned specifiers");
            sign=token==TOK_UNSIGNED;
        }else if(token==TOK_SHORT||token==TOK_LONG||token==TOK_CHAR){
            if(rank&&!(rank==TOK_LONG&&token==TOK_LONG&&long_count==1))error_at(p->token.location,"conflicting integer type specifiers");
            if(token==TOK_LONG)++long_count;
            rank=token;
        }else if(token==TOK_DOUBLE){
            if(has_double)error_at(p->token.location,"duplicate double specifier");
            has_double=1;
        }else if(token==TOK_INT){
            if(has_int)error_at(p->token.location,"duplicate int specifier");
            has_int=1;
        }else break;
        lex(p);
    }
    if(has_double){
        if(sign>=0||has_int||(rank&&rank!=TOK_LONG)||long_count>1)
            error_at(p->token.location,"invalid double type specifiers");
        found=1;result.base=binary64_enabled?TY_DOUBLE:TY_FLOAT;
    }else if(rank||has_int){
        found=1;
        if(rank==TOK_CHAR){
            if(has_int)error_at(p->token.location,"char cannot be combined with int");
            result.base=TY_CHAR;
            result.is_plain_char=sign<0;
        }else if(rank==TOK_LONG)result.base=long_count==2?TY_LONGLONG:TY_LONG;
        else if(rank==TOK_SHORT)result.is_short=1;
    }
    else if (accept(p, TOK_BOOL)) { found = 1; result.base = TY_CHAR; result.is_bool=1; if(sign>=0)error_at(p->token.location,"_Bool cannot have a sign modifier"); }
    else if (accept(p, TOK_VOID)) { found = 1; result.base = TY_VOID; }
    else if (accept(p,TOK_FLOAT)) {found=1;result.base=TY_FLOAT;}
    else if (accept(p,TOK_ENUM)) {
        if(sign>=0)error_at(p->token.location,"enum cannot have a signed/unsigned modifier");
        result=enum_specifier(p);found=1;
    }
    else if (p->token.kind==TOK_STRUCT||p->token.kind==TOK_UNION) {
        int is_union=p->token.kind==TOK_UNION;lex(p);
        result.base = TY_STRUCT; found = 1;
        {
            char name[64]="";unsigned owner=p->current?p->current->id:0;Structure *record=NULL;
            if(p->token.kind==TOK_NAME){strcpy(name,p->token.name);lex(p);}
            else if(p->token.kind!='{')error_at(p->token.location,"expected %s tag or definition",is_union?"union":"struct");
            if(*name)for(i=p->tag_count;i;--i)if(p->tags[i-1].active&&!strcmp(p->tags[i-1].name,name)){
                record=&p->tags[i-1];break;
            }
            /* A definition or standalone forward declaration introduces a tag
             * in this scope; an ordinary reference can use an enclosing tag. */
            if(record&&(p->token.kind=='{'||p->token.kind==';')&&
               (record->owner!=owner||record->scope!=p->scope))record=NULL;
            if(record&&record->is_enum)error_at(p->token.location,"tag '%s' was declared as enum",name);
            if(record&&record->is_union!=(unsigned)is_union)
                error_at(p->token.location,"tag '%s' was declared as %s",name,record->is_union?"union":"struct");
            if(!record){
                if(p->tag_count==64)error_at(p->token.location,"too many aggregate tags");
                record=&p->tags[p->tag_count++];strcpy(record->name,name);
                record->owner=owner;record->scope=p->scope;record->active=1;record->is_union=is_union;
            }
            result.tag=(unsigned)(record-p->tags)+1;result.structure=record;
            if(p->token.kind=='{')structure_definition(p,record);
        }
    } else if (p->token.kind == TOK_NAME) {
        Alias *a=find_alias(p,p->token.name);
        if(a&&sign<0){result=a->type;found=1;used_alias=1;lex(p);}
    }
    if(!found&&sign<0){
        if(p->token.kind!=TOK_NAME&&p->token.kind!='*'&&p->token.kind!='(')
            error_at(p->token.location,"expected a supported type declaration");
        warning_at(p->token.location,"implicit int type specifier");
    }
    if(result.enum_tag&&sign>=0)error_at(p->token.location,"enum cannot have a signed/unsigned modifier");
    if(sign>=0&&(result.base==TY_VOID||result.base==TY_FLOAT||result.base==TY_STRUCT))
        error_at(p->token.location,"signed/unsigned requires an integer type specifier");
    if(result.base==TY_CHAR&&!used_alias)result.is_unsigned=1;
    if(sign>=0)result.is_unsigned=sign;
    do{declaration_qualifiers(p,&constant,&vol);}while(storage_specifier(p,storage,local)||wram_specifier(p,wram));
    if(vol)result=volatile_object(result);
    if(constant)result=const_object(result);
    return result;
}
static Type declaration_base(Parser *p){return declaration_base_with_storage(p,NULL,0,NULL);}
static unsigned reg_width(Type t){t=value_type(t);return !t.pointers&&(t.base==TY_LONGLONG||t.base==TY_DOUBLE)?8:width(t)>2?4:2;}
static unsigned argument_width(Type t){t=value_type(t);return structure_object(t)?width(t):reg_width(t);}
static int register_parameter(unsigned index,Type t)
{
    return index<2&&!structure_object(value_type(t))&&reg_width(t)==2;
}
static int register_argument(Symbol *s,unsigned index,Expr *value)
{
    if(s->variadic&&index>=(unsigned)s->param_count)return 0;
    return register_parameter(index,value->type);
}
#include "parser.inc"

/* Volatile accesses are observable even when their result is discarded.
 * Address formation alone does not read the object being addressed. */
static int volatile_type(Type t)
{
    Member *m;
    if(object_volatile(t))return 1;
    if(t.array)return volatile_type(array_element(t));
    if(structure_object(t)&&t.structure)
        for(m=t.structure->members;m;m=m->next)if(volatile_type(m->type))return 1;
    return 0;
}
static int volatile_expression(Expr *e);
static int volatile_address(Expr *e)
{
    if(e->kind==EX_OBJECT)return 0;
    if(e->kind==EX_DEREF)return volatile_expression(e->left);
    if(e->kind==EX_MEMBER)return e->op==TOK_ARROW?volatile_expression(e->left):volatile_address(e->left);
    return volatile_expression(e);
}
static int volatile_expression(Expr *e)
{
    unsigned i;if(!e)return 0;
    if(e->kind==EX_ADDRESS)return volatile_address(e->left);
    if(lvalue(e)&&!e->type.array&&volatile_type(e->type))return 1;
    if(volatile_expression(e->left)||volatile_expression(e->right)||volatile_expression(e->third))return 1;
    for(i=0;i<e->arg_count;++i)if(volatile_expression(e->args[i]))return 1;
    return 0;
}
static int volatile_statements(Statement *s);
static int volatile_statement(Statement *s)
{
    return s&&(volatile_expression(s->expression)||volatile_expression(s->step)||
        volatile_statements(s->initial)||volatile_statements(s->body)||volatile_statements(s->alternate));
}
static int volatile_statements(Statement *s)
{
    for(;s;s=s->next)if(volatile_statement(s))return 1;
    return 0;
}

#include "codegen/codegen.inc"

static void free_expression(Expr *e)
{
    unsigned i; if (!e) return;
    for (i = 0; i < e->arg_count; ++i) free_expression(e->args[i]);
    free_expression(e->left);free_expression(e->right);free_expression(e->third);
    free(e);
}
static void free_statements(Statement *s)
{
    while (s) { Statement *next = s->next; free_statements(s->body);free_statements(s->alternate);free_statements(s->initial);free_expression(s->step); free_expression(s->expression); free(s); s = next; }
}
#include "source_lto.inc"

/* Packaged headers sit in include/ beside the compiler, else in include/ in
 * the current directory. POSIX has no call that names the running program,
 * so Windows asks its C runtime and other systems resolve argv[0] directly
 * or through PATH. */
static const char *default_include_directory(const char *argv0, char *directory, size_t capacity)
{
    const char *result = "include", *slash;
    char *program = NULL;
#ifdef _WIN32
    char *found = NULL;
    struct _stat attributes;
    (void)argv0;
    if (_get_pgmptr(&found) == 0 && found) program = _strdup(found);
#else
    struct stat attributes;
    if (argv0 && strchr(argv0, '/')) program = realpath(argv0, NULL);
    else if (argv0 && *argv0) {
        const char *search = getenv("PATH");
        char candidate[4096];
        while (search && !program) {
            const char *end = strchr(search, ':');
            size_t length = end ? (size_t)(end - search) : strlen(search);
            /* An empty PATH entry names the current directory */
            int n = snprintf(candidate, sizeof candidate, "%.*s/%s",
                             length ? (int)length : 1, length ? search : ".", argv0);
            /* Like the shell, take only a regular file: a directory passes X_OK too */
            if (n > 0 && (size_t)n < sizeof candidate &&
                stat(candidate, &attributes) == 0 && S_ISREG(attributes.st_mode) &&
                access(candidate, X_OK) == 0)
                program = realpath(candidate, NULL);
            search = end ? end + 1 : NULL;
        }
    }
#endif
    if (!program) return result;
    slash = strrchr(program, '/');
#ifdef _WIN32
    {
        const char *backslash = strrchr(program, '\\');
        if (!slash || (backslash && backslash > slash)) slash = backslash;
    }
#endif
    if (slash && (size_t)(slash - program) + sizeof "/include" <= capacity) {
        size_t length = (size_t)(slash - program);
        memcpy(directory, program, length);
        memcpy(directory + length, "/include", sizeof "/include");
#ifdef _WIN32
        if (_stat(directory, &attributes) == 0 && (attributes.st_mode & _S_IFDIR)) result = directory;
#else
        if (stat(directory, &attributes) == 0 && S_ISDIR(attributes.st_mode)) result = directory;
#endif
    }
    free(program);
    return result;
}

int main(int argc, char **argv)
{
    Parser *p = allocate(sizeof *p); FILE *out; unsigned i; int failed;
    const char *lto_sources[32];unsigned lto_count=1;lto_sources[0]=argc>1?argv[1]:NULL;
    Parser *lto_units[32];unsigned lto_units_count=0;
    char packaged_include[2048];
    const char *include_directory=NULL, *dependency_path=NULL;
    FILE *dependencies=NULL;
    if (argc < 4 || strcmp(argv[2],"-o")) {
        fputs("usage: zicc input.c -o output.s [-I include-directory] [--dependencies file] [--binary64] [--large-rom-objects] [--c89-keywords] [--no-strength-reduction] [--no-indexed-dpage] [--no-direct-dpage] [--no-indexed-operands] [--no-loop-index-retention] [--no-known-values] [--no-byte-shuffles] [--no-store-fusion] [--no-private-regions] [--no-value-reuse] [--no-branch-relaxation] [--no-divmod-reuse] [--no-register-loops] [--no-dp-counters] [--no-dp-homes] [--no-stack-frames] [--no-line-passes] [--no-register-cursors] [--no-dp-summaries] [--no-index-elimination] [--no-region-homes] [--no-loop-unroll] [--no-body-optimizations] [--no-inline] [--lto] [--lto-source input.c] [--no-copy-selection] [--no-bank-specialization] [--long-return] [--long-calls symbols]\n",stderr); return EXIT_FAILURE;
    }
    for(i=4;i<(unsigned)argc;++i){
        if(!strcmp(argv[i],"-I")&&i+1<(unsigned)argc)include_directory=argv[++i];
        else if(!strcmp(argv[i],"--dependencies")&&i+1<(unsigned)argc)dependency_path=argv[++i];
        else if(!strcmp(argv[i],"--long-calls")&&i+1<(unsigned)argc)p->long_calls=argv[++i];
        else if(!strcmp(argv[i],"--binary64"))binary64_enabled=1;
        else if(!strcmp(argv[i],"--large-rom-objects"))large_rom_objects=1;
        else if(!strcmp(argv[i],"--sram-layout")&&i+1<(unsigned)argc){
            char extra;
            if(sscanf(argv[++i],"%u,%u,%u%c",&sram_first_bank,&sram_window_size,&sram_capacity,&extra)!=3||
               sram_first_bank>255||(sram_window_size!=8192&&sram_window_size!=32768)||
               sram_capacity<2048||sram_capacity>524288||(sram_capacity&(sram_capacity-1))||
               sram_first_bank+(sram_capacity-1)/sram_window_size>255){
                fputs("invalid --sram-layout, expected BANK,WINDOW_BYTES,CAPACITY_BYTES\n",stderr);return EXIT_FAILURE;
            }
        }
        else if(!strcmp(argv[i],"--long-return"))p->long_return=1;
        else if(!strcmp(argv[i],"--rom-default-rounding"))p->rom_default_rounding=1;
        else if(!strcmp(argv[i],"--runtime-objects")&&i+1<(unsigned)argc)p->runtime_objects=argv[++i];
        else if(!strcmp(argv[i],"--near-wram-objects")&&i+1<(unsigned)argc)p->near_wram_objects=argv[++i];
        else if(!strcmp(argv[i],"--no-strength-reduction"))p->no_strength_reduction=1;
        else if(!strcmp(argv[i],"--no-indexed-dpage"))p->no_indexed_dpage=1;
        else if(!strcmp(argv[i],"--no-direct-dpage"))p->no_direct_dpage=1;
        else if(!strcmp(argv[i],"--no-indexed-operands"))p->no_indexed_operands=1;
        else if(!strcmp(argv[i],"--no-loop-index-retention"))p->no_loop_index_retention=1;
        else if(!strcmp(argv[i],"--no-branch-relaxation"))p->no_branch_relaxation=1;
        else if(!strcmp(argv[i],"--no-divmod-reuse"))p->no_divmod_reuse=1;
        else if(!strcmp(argv[i],"--no-register-loops"))p->no_register_loops=1;
        else if(!strcmp(argv[i],"--no-dp-counters"))p->no_dp_counters=1;
        else if(!strcmp(argv[i],"--no-dp-homes"))p->no_dp_homes=1;
        else if(!strcmp(argv[i],"--no-stack-frames"))p->no_stack_frames=1;
        else if(!strcmp(argv[i],"--no-line-passes"))p->no_line_passes=1;
        else if(!strcmp(argv[i],"--no-register-cursors"))p->no_register_cursors=1;
        else if(!strcmp(argv[i],"--no-dp-summaries"))p->no_dp_summaries=1;
        else if(!strcmp(argv[i],"--no-index-elimination"))p->no_index_elimination=1;
        else if(!strcmp(argv[i],"--no-region-homes"))p->no_region_homes=1;
        else if(!strcmp(argv[i],"--no-loop-unroll"))p->no_loop_unroll=1;
        else if(!strcmp(argv[i],"--no-body-optimizations"))p->no_body_optimizations=1;
        else if(!strcmp(argv[i],"--no-known-values"))p->no_known_values=1;
        else if(!strcmp(argv[i],"--no-byte-shuffles"))p->no_byte_shuffles=1;
        else if(!strcmp(argv[i],"--no-store-fusion"))p->no_store_fusion=1;
        else if(!strcmp(argv[i],"--no-private-regions"))p->no_private_regions=1;
        else if(!strcmp(argv[i],"--no-value-reuse"))p->no_value_reuse=1;
        else if(!strcmp(argv[i],"--no-inline"))p->no_inline=1;
        else if(!strcmp(argv[i],"--c89-keywords"))p->c89_keywords=1;
        else if(!strcmp(argv[i],"--lto"))p->source_lto=1;
        else if(!strcmp(argv[i],"--lto-source")&&i+1<(unsigned)argc){
            if(lto_count==32)error_at((Location){argv[1],1,1},"source LTO supports at most 32 translation units");
            lto_sources[lto_count++]=argv[++i];p->source_lto=1;
        }
        else if(!strcmp(argv[i],"--no-copy-selection"))p->no_copy_selection=1;
        else if(!strcmp(argv[i],"--no-bank-specialization"))p->no_bank_specialization=1;
        else{fprintf(stderr,"unknown or incomplete option: %s\n",argv[i]);return EXIT_FAILURE;}
    }
    if (!include_directory)
        include_directory = default_include_directory(argv[0], packaged_include, sizeof packaged_include);
    if (dependency_path) {
        dependencies = fopen(dependency_path, "wb");
        if (!dependencies) { perror(dependency_path); return EXIT_FAILURE; }
    }
    if(p->source_lto){
        Parser *options=p;
        for(i=0;i<lto_count;++i){Parser *unit=allocate(sizeof *unit);*unit=*options;
            lto_parse(unit,lto_sources[i],include_directory,dependencies);lto_units[lto_units_count++]=unit;}
        p=lto_merge(options,lto_units,lto_units_count);free(options);
    }else lto_parse(p,argv[1],include_directory,dependencies);
    if (dependencies) {
        failed = ferror(dependencies);
        if (fclose(dependencies)) failed = 1;
        if (failed) { fprintf(stderr,"%s: dependency write failed\n",dependency_path); return EXIT_FAILURE; }
    }
    out = fopen(argv[3],"wb");
    if (!out) { perror(argv[3]); return EXIT_FAILURE; }
    fprintf(out,"; Generated by zicc\n; Source: %s\n",argv[1]);
    if(p->source_lto)for(i=0;i<lto_units_count;++i){unsigned j;fprintf(out,"; Source LTO unit: %s\n",lto_sources[i]);
        for(j=0;j<lto_units[i]->path_count;++j)fprintf(out,"; Source LTO dependency: %s\n",lto_units[i]->paths[j]);}
    {
        EmbeddedRange *range;
        for(range=p->embeds;range;range=range->next)fprintf(out,"; Embedded resource: %s\n",range->resource);
    }
    /* The ROM builder proves the initial mode and runtime closure. A unit
     * with an interrupt entry or inline assembly cannot use that assumption. */
    if(p->rom_default_rounding){
        Function *f;
        if(find_symbol(p,"$basic_asm"))p->rom_default_rounding=0;
        for(f=p->functions;f&&p->rom_default_rounding;f=f->next)
            if(f->symbol->interrupt||body_asm_statements(f->body))p->rom_default_rounding=0;
    }
    emit_program(out,p);
    failed = ferror(out); if (fclose(out)) failed = 1;
    lto_free(p);for(i=0;i<lto_units_count;++i)lto_free(lto_units[i]);
    if (failed) { fprintf(stderr,"%s: output write failed\n",argv[3]); return EXIT_FAILURE; }
    return EXIT_SUCCESS;
}
