// Expand macros and handle directives such as #if before parsing C
#include <ctype.h>
#include <errno.h>
#include <limits.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "headers/preprocess.h"

/* Reserve six slots for the predefined macros */
enum { PP_MACROS = 4092 + 6, PP_HIDE_WORDS = (PP_MACROS + 63) / 64, PP_PARAMS = 127, PP_DEPTH = 64 };
typedef struct { char *data; size_t size, capacity; } Text;
typedef struct { char *text; uint64_t hide[PP_HIDE_WORDS]; int line, column, gap; } Token;
typedef struct { Token *items; size_t count, capacity; } Tokens;
typedef struct { Tokens raw, expanded; int ready; } MacroArgument;
typedef struct {
    char name[64];
    char (*params)[64];
    int defined, function, arity;
    Tokens body;
} Macro;
typedef struct {
    Macro macros[PP_MACROS];
    int macro_count;
    const char *include_dir, *path, *logical_file;
    int line;
    Text output;
    EmbeddedRange *embeds;
    FILE *dependencies;
    int conditional, embed_depth;
} Preprocessor;

static _Noreturn void pp_error(const char *path, int line, const char *message)
{
    fprintf(stderr, "%s:%d:1: error: %s\n", path, line, message);
    exit(EXIT_FAILURE);
}
static _Noreturn void fail(Preprocessor *pp, const char *message)
{
    if (pp->logical_file) {
        fprintf(stderr, "%.*s:%d:1: error: %s\n", (int)strlen(pp->logical_file)-2,
                pp->logical_file+1, pp->line, message);
        exit(EXIT_FAILURE);
    }
    pp_error(pp->path, pp->line, message);
}
static void *allocate(size_t n)
{
    void *p = malloc(n);
    if (!p) pp_error("<preprocessor>", 1, "out of memory");
    return p;
}
static void append(Text *text, const char *data, size_t size)
{
    if (size > 8 * 1024 * 1024 - text->size)
        pp_error("<preprocessor>", 1, "expanded source exceeds 8 MiB");
    if (text->size + size + 1 > text->capacity) {
        char *p;
        text->capacity = (text->size + size + 1) * 2;
        p = realloc(text->data, text->capacity);
        if (!p) pp_error("<preprocessor>", 1, "out of memory");
        text->data = p;
    }
    memcpy(text->data + text->size, data, size);
    text->size += size; text->data[text->size] = 0;
}
static void quoted_path(Text *text, const char *path, int normalize)
{
    append(text, "\"", 1);
    for (; *path; ++path) {
        char c = normalize && *path == '\\' ? '/' : *path;
        if (c == '"' || c == '\\') append(text, "\\", 1);
        append(text, &c, 1);
    }
    append(text, "\"", 1);
}
static int is_identifier(const char *s)
{
    if (!isalpha((unsigned char)*s) && *s != '_') return 0;
    while (*++s) if (!isalnum((unsigned char)*s) && *s != '_') return 0;
    return 1;
}
static int equal(const Token *t, const char *s) { return !strcmp(t->text, s); }
static Token token(const char *s, size_t n, int line, int gap)
{
    Token t = {0};
    t.text = allocate(n + 1); memcpy(t.text, s, n); t.text[n] = 0;
    t.line = line; t.gap = gap; return t;
}
static void reserve(Tokens *ts, size_t count)
{
    if (count > 262144) pp_error("<macro>", 1, "macro expansion exceeds token limit");
    if (count > ts->capacity) {
        Token *p;
        ts->capacity = count * 2 + 16;
        p = realloc(ts->items, ts->capacity * sizeof *p);
        if (!p) pp_error("<macro>", 1, "out of memory");
        ts->items = p;
    }
}
static void push(Tokens *ts, Token t) { reserve(ts, ts->count + 1); ts->items[ts->count++] = t; }
static void copy_tokens(Tokens *to, const Tokens *from, size_t begin, size_t end)
{
    size_t i;
    for (i = begin; i < end; ++i) {
        Token t = from->items[i], c = token(t.text, strlen(t.text), t.line, t.gap);
        c.column = t.column;
        memcpy(c.hide,t.hide,sizeof c.hide); push(to, c);
    }
}
static void clear_tokens(Tokens *ts)
{
    size_t i;
    for (i = 0; i < ts->count; ++i) free(ts->items[i].text);
    free(ts->items); memset(ts, 0, sizeof *ts);
}
static void clear_macro(Macro *macro)
{
    free(macro->params);
    clear_tokens(&macro->body);
    memset(macro, 0, sizeof *macro);
}
static void lex(Preprocessor *pp, Tokens *ts, const char *s, int *comment)
{
    const char *origin = s;
    int gap = 1;
    while (*s) {
        const char *start = s;
        if (*comment) {
            if (s[0] == '*' && s[1] == '/') { *comment = 0; s += 2; }
            else ++s;
            gap = 1; continue;
        }
        if (isspace((unsigned char)*s)) { gap = 1; ++s; continue; }
        if (s[0] == '/' && s[1] == '/') break;
        if (s[0] == '/' && s[1] == '*') { *comment = 1; s += 2; gap = 1; continue; }
        if (*s == '\'' || *s == '"') {
            char quote = *s++;
            while (*s && *s != quote && *s != '\n' && *s != '\r') {
                if (*s == '\\' && s[1]) ++s;
                ++s;
            }
            if (*s != quote) fail(pp, "unterminated string/character literal");
            ++s;
        } else if (isalpha((unsigned char)*s) || *s == '_') {
            do { ++s; } while (isalnum((unsigned char)*s) || *s == '_');
        } else if (isdigit((unsigned char)*s) || (*s == '.' && isdigit((unsigned char)s[1]))) {
            do {
                char previous = *s++;
                if ((previous == 'e' || previous == 'E' || previous == 'p' || previous == 'P') &&
                    (*s == '+' || *s == '-')) ++s;
            } while (isalnum((unsigned char)*s) || *s == '_' || *s == '.');
        } else {
            static const char *const pairs[] = {
                "&&", "||", "<<", ">>", "<=", ">=", "==", "!=", "##", "->",
                "++", "--", "+=", "-=", "*=", "/=", "%=", "&=", "|=", "^="
            };
            size_t i;
            if (!strncmp(s, "...", 3)) s += 3;
            else if (!strncmp(s, "<<=", 3) || !strncmp(s, ">>=", 3)) s += 3;
            else {
                for (i = 0; i < sizeof pairs / sizeof *pairs; ++i)
                    if (!strncmp(s, pairs[i], 2)) break;
                s += i < sizeof pairs / sizeof *pairs ? 2 : 1;
            }
        }
        {
            Token t = token(start, (size_t)(s - start), pp->line, gap);
            t.column = (int)(start - origin) + 1;
            push(ts, t); gap = 0;
        }
    }
}
static int macro_index(Preprocessor *pp, const char *name)
{
    int i;
    for (i = 0; i < pp->macro_count; ++i)
        if (pp->macros[i].defined && !strcmp(pp->macros[i].name, name)) return i;
    return -1;
}
static int macro_defined(Preprocessor *pp, const char *name)
{
    return macro_index(pp, name) >= 0 || !strcmp(name, "__has_embed") ||
           !strcmp(name, "__FILE__") || !strcmp(name, "__LINE__");
}
static int has_embed(Preprocessor *pp, Tokens *ts, size_t at, size_t *end);
static int macro_parameter(const Macro *m, const Token *t)
{
    int param;
    for (param = 0; param < m->arity; ++param)
        if (equal(t, m->params[param])) break;
    return param;
}
static Token stringify(const Tokens *arg, int line)
{
    Text spelling = {0};
    Token result;
    size_t i;
    append(&spelling, "\"", 1);
    for (i = 0; i < arg->count; ++i) {
        const char *s = arg->items[i].text;
        int literal = *s == '"' || *s == '\'';
        if (i && arg->items[i].gap) append(&spelling, " ", 1);
        for (; *s; ++s) {
            if (literal && (*s == '"' || *s == '\\')) append(&spelling, "\\", 1);
            append(&spelling, s, 1);
        }
    }
    append(&spelling, "\"", 1);
    result = token(spelling.data, spelling.size, line, 0);
    free(spelling.data);
    return result;
}
static void expand(Preprocessor *pp, Tokens *ts, unsigned depth)
{
    size_t i = 0, steps = 0;
    if (depth > PP_DEPTH) fail(pp, "macro argument nesting exceeds 64");
    while (i < ts->count) {
        int index;
        if (equal(&ts->items[i], "__FILE__") || equal(&ts->items[i], "__LINE__")) {
            Token *t = &ts->items[i]; Text replacement = {0};
            if (equal(t, "__FILE__")) {
                if (pp->logical_file)
                    append(&replacement, pp->logical_file, strlen(pp->logical_file));
                else quoted_path(&replacement, pp->path, 1);
            } else {
                char number[24]; int n = snprintf(number, sizeof number, "%d", t->line);
                append(&replacement, number, (size_t)n);
            }
            free(t->text); t->text = replacement.data; ++i; continue;
        }
        if (equal(&ts->items[i], "__has_embed")) {
            size_t end, j; int found;
            if (!pp->conditional) fail(pp, "__has_embed is only allowed in conditional expressions");
            found = has_embed(pp, ts, i + 1, &end);
            for (j = i; j < end; ++j) free(ts->items[j].text);
            ts->items[i] = token(found == 2 ? "2" : found ? "1" : "0", 1, pp->line, 1);
            memmove(ts->items + i + 1, ts->items + end, (ts->count - end) * sizeof *ts->items);
            ts->count -= end - i - 1; ++i; continue;
        }
        index = macro_index(pp, ts->items[i].text);
        Token invocation = ts->items[i];
        Macro *m;
        Tokens replacement = {0};
        MacroArgument *arguments = NULL;
        size_t end = i + 1, j;
        uint64_t hide[PP_HIDE_WORDS];
        memcpy(hide,invocation.hide,sizeof hide);
        if (index < 0 || (hide[index / 64] & (UINT64_C(1) << (index % 64)))) { ++i; continue; }
        m = &pp->macros[index]; pp->line = invocation.line;
        if (++steps > 262144) fail(pp, "macro expansion exceeds operation limit");
        if (m->function) {
            int nesting = 0, count = 0;
            size_t begin;
            if (end == ts->count || !equal(&ts->items[end], "(")) { ++i; continue; }
            if (m->arity) {
                arguments = calloc((size_t)m->arity, sizeof *arguments);
                if (!arguments) fail(pp, "out of memory");
            }
            begin = ++end;
            for (; end < ts->count; ++end) {
                Token *t = &ts->items[end];
                if (equal(t, "(")) ++nesting;
                else if (equal(t, ")") && nesting) --nesting;
                else if ((!nesting && equal(t, ",")) || (!nesting && equal(t, ")"))) {
                    if (end != begin || count || m->arity || equal(t, ",")) {
                        if (count == m->arity) fail(pp, "wrong number of macro arguments");
                        copy_tokens(&arguments[count++].raw, ts, begin, end);
                    }
                    begin = end + 1;
                    if (equal(t, ")")) break;
                }
            }
            if (end == ts->count) fail(pp, "unterminated macro invocation");
            if (count != m->arity) fail(pp, "wrong number of macro arguments");
            // A function replacement inherits only macros disabled at both ends
            for(j=0;j<PP_HIDE_WORDS;++j)hide[j]&=ts->items[end].hide[j];
            ++end;
        }
        for (j = 0; j < m->body.count; ++j) {
            int param;
            if (m->function && equal(&m->body.items[j], "#")) {
                int gap=m->body.items[j].gap;
                Token string;
                param = macro_parameter(m, &m->body.items[++j]);
                string=stringify(&arguments[param].raw, invocation.line);
                string.gap=gap;
                push(&replacement, string);
                continue;
            }
            param = macro_parameter(m, &m->body.items[j]);
            if (param < m->arity) {
                int pasted=(j&&equal(&m->body.items[j-1],"##"))||(j+1<m->body.count&&equal(&m->body.items[j+1],"##"));
                MacroArgument *argument=&arguments[param];
                Tokens *arg=pasted?&argument->raw:&argument->expanded;
                if (!pasted && !argument->ready) {
                    copy_tokens(arg, &argument->raw, 0, argument->raw.count);
                    expand(pp, arg, depth + 1);
                    argument->ready = 1;
                }
                if(pasted&&!arg->count)push(&replacement,token("",0,invocation.line,m->body.items[j].gap));
                else if(arg->count){
                    size_t first=replacement.count;
                    copy_tokens(&replacement,arg,0,arg->count);
                    replacement.items[first].gap=m->body.items[j].gap;
                }
            }
            else copy_tokens(&replacement, &m->body, j, j + 1);
        }
        for(j=0;j<replacement.count;++j)if(equal(&replacement.items[j],"##")){
            Token *left,*right;Tokens joined={0};Text spelling={0};int comment=0;size_t word;
            if(!j||j+1==replacement.count)fail(pp,"token paste requires two operands");
            left=&replacement.items[j-1];right=&replacement.items[j+1];
            append(&spelling,left->text,strlen(left->text));append(&spelling,right->text,strlen(right->text));
            if(spelling.size){
                lex(pp,&joined,spelling.data,&comment);
                if(joined.count!=1||comment||strlen(joined.items[0].text)!=spelling.size)fail(pp,"token paste does not form one preprocessing token");
            }else push(&joined,token("",0,invocation.line,0));
            joined.items[0].gap=left->text[0]?left->gap:(left->gap||right->gap);
            for(word=0;word<PP_HIDE_WORDS;++word)joined.items[0].hide[word]=left->hide[word]&right->hide[word];
            free(left->text);free(replacement.items[j].text);free(right->text);
            *left=joined.items[0];free(joined.items);free(spelling.data);
            memmove(replacement.items+j,replacement.items+j+2,(replacement.count-j-2)*sizeof *replacement.items);
            replacement.count-=2;--j;
        }
        for(j=0;j<replacement.count;)if(!replacement.items[j].text[0]){
            free(replacement.items[j].text);memmove(replacement.items+j,replacement.items+j+1,(replacement.count-j-1)*sizeof *replacement.items);--replacement.count;
        }else ++j;
        if(replacement.count)replacement.items[0].gap=invocation.gap;
        for (j = 0; j < replacement.count; ++j) {
            Token *t = &replacement.items[j];
            size_t word;
            for(word=0;word<PP_HIDE_WORDS;++word)t->hide[word]|=hide[word];
            t->hide[index / 64] |= UINT64_C(1) << (index % 64);
            t->line = invocation.line;
            t->column = invocation.column;
        }
        for (j = 0; j < (size_t)m->arity; ++j) {
            clear_tokens(&arguments[j].raw);
            clear_tokens(&arguments[j].expanded);
        }
        free(arguments);
        for (j = i; j < end; ++j) free(ts->items[j].text);
        reserve(ts, ts->count - (end - i) + replacement.count);
        memmove(ts->items + i + replacement.count, ts->items + end, (ts->count - end) * sizeof *ts->items);
        if (replacement.count) memcpy(ts->items + i, replacement.items, replacement.count * sizeof *ts->items);
        ts->count = ts->count - (end - i) + replacement.count;
        free(replacement.items);
        // Rescan the boundary: an object macro can name a function macro
    }
}

// #if arithmetic uses signed/unsigned 64-bit values, independently of target int
typedef struct { uint64_t bits; int uns; } Value;
typedef struct { Preprocessor *pp; Tokens *ts; size_t at; unsigned depth; } Expression;
static Value value(uint64_t bits, int uns) { Value v = {bits, uns}; return v; }
static int take(Expression *e, const char *s)
{
    if (e->at < e->ts->count && equal(&e->ts->items[e->at], s)) { ++e->at; return 1; }
    return 0;
}
static Value expression(Expression *e, int minimum, int evaluate);
static uint64_t character(Preprocessor *pp, const char *s)
{
    unsigned result;
    ++s;
    if (*s != '\\') result = (unsigned char)*s++;
    else {
        ++s;
        if (*s >= '0' && *s <= '7') {
            int n = 0; result = 0;
            while (n++ < 3 && *s >= '0' && *s <= '7') result = result * 8 + (unsigned)(*s++ - '0');
        } else if (*s == 'x') {
            result = 0; ++s;
            if (!isxdigit((unsigned char)*s)) fail(pp, "invalid hexadecimal character escape");
            while (isxdigit((unsigned char)*s)) {
                result = result * 16 + (unsigned)(isdigit((unsigned char)*s) ? *s - '0' : tolower((unsigned char)*s) - 'a' + 10);
                ++s;
            }
        } else {
            switch (*s++) {
            case 'a': result = 7; break; case 'b': result = 8; break;
            case 't': result = 9; break; case 'n': result = 10; break;
            case 'v': result = 11; break; case 'f': result = 12; break;
            case 'r': result = 13; break; case '\\': result = '\\'; break;
            case '\'': result = '\''; break; case '"': result = '"'; break;
            case '?': result = '?'; break;
            default: fail(pp, "unsupported character escape");
            }
        }
    }
    if (*s != '\'' || s[1] || result > 255) fail(pp, "expected a single-byte character constant");
    return result;
}
static Value primary(Expression *e, int evaluate)
{
    Value v;
    Token *t;
    if (++e->depth > PP_DEPTH) fail(e->pp, "conditional expression nesting exceeds 64");
    if (take(e, "!")) { v = primary(e, evaluate); v = value(!v.bits, 0); }
    else if (take(e, "~")) { v = primary(e, evaluate); v.bits = ~v.bits; }
    else if (take(e, "+")) v = primary(e, evaluate);
    else if (take(e, "-")) { v = primary(e, evaluate); v.bits = 0 - v.bits; }
    else if (take(e, "(")) {
        v = expression(e, 1, evaluate);
        if (!take(e, ")")) fail(e->pp, "expected ')' in conditional expression");
    } else {
        char *end;
        int uns = 0;
        if (e->at == e->ts->count) fail(e->pp, "expected operand in conditional expression");
        t = &e->ts->items[e->at++];
        if (is_identifier(t->text)) v = value(0, 0);
        else if (t->text[0] == '\'') v = value(character(e->pp, t->text), 0);
        else {
            if (!isdigit((unsigned char)t->text[0])) fail(e->pp, "expected integer in conditional expression");
            errno = 0; v = value(strtoull(t->text, &end, 0), 0);
            if (errno == ERANGE) fail(e->pp, "conditional integer exceeds 64 bits");
            if (*end == 'u' || *end == 'U') { uns = 1; ++end; }
            if (*end == 'l' || *end == 'L') {
                char c = *end++;
                if (*end == c) ++end;
            }
            if (!uns && (*end == 'u' || *end == 'U')) { uns = 1; ++end; }
            if (*end) fail(e->pp, "invalid integer constant in conditional expression");
            if (v.bits > INT64_MAX) {
                if (!uns && t->text[0] != '0') fail(e->pp, "decimal conditional integer exceeds signed range");
                uns = 1;
            }
            v.uns = uns;
        }
    }
    --e->depth; return v;
}
static int precedence(const char *op)
{
    static const char *const ops[] = {"||", "&&", "|", "^", "&", "==", "!=", "<", "<=", ">", ">=", "<<", ">>", "+", "-", "*", "/", "%"};
    static const int ranks[] = {2,3,4,5,6,7,7,8,8,8,8,9,9,10,10,11,11,11};
    size_t i;
    for (i = 0; i < sizeof ops / sizeof *ops; ++i) if (!strcmp(op, ops[i])) return ranks[i];
    return 0;
}
static Value binary(Preprocessor *pp, const char *op, Value a, Value b, int evaluate)
{
    uint64_t x = a.bits, y = b.bits;
    int uns = a.uns || b.uns, less = uns ? x < y : (x ^ (UINT64_C(1) << 63)) < (y ^ (UINT64_C(1) << 63));
    if (!strcmp(op, "||")) return value(!!x || !!y, 0);
    if (!strcmp(op, "&&")) return value(!!x && !!y, 0);
    if (!strcmp(op, "==")) return value(x == y, 0);
    if (!strcmp(op, "!=")) return value(x != y, 0);
    if (!strcmp(op, "<")) return value(less, 0);
    if (!strcmp(op, "<=")) return value(less || x == y, 0);
    if (!strcmp(op, ">")) return value(!less && x != y, 0);
    if (!strcmp(op, ">=")) return value(!less, 0);
    if (!strcmp(op, "+")) return value(x + y, uns);
    if (!strcmp(op, "-")) return value(x - y, uns);
    if (!strcmp(op, "*")) return value(x * y, uns);
    if (!strcmp(op, "&")) return value(x & y, uns);
    if (!strcmp(op, "|")) return value(x | y, uns);
    if (!strcmp(op, "^")) return value(x ^ y, uns);
    if (!strcmp(op, "<<") || !strcmp(op, ">>")) {
        if (y >= 64) { if (evaluate) fail(pp, "invalid shift in conditional expression"); return value(0, a.uns); }
        if (*op == '<') return value(x << y, a.uns);
        if (!a.uns && (x >> 63) && y) return value((x >> y) | (~UINT64_C(0) << (64 - y)), 0);
        return value(x >> y, a.uns);
    }
    if (!y) { if (evaluate) fail(pp, "division by zero in conditional expression"); return value(0, uns); }
    if (uns) return value(*op == '/' ? x / y : x % y, 1);
    {
        int negative_x = (int)(x >> 63), negative_y = (int)(y >> 63);
        uint64_t ax = negative_x ? 0 - x : x, ay = negative_y ? 0 - y : y;
        uint64_t result = *op == '/' ? ax / ay : ax % ay;
        if (*op == '/' ? negative_x != negative_y : negative_x) result = 0 - result;
        return value(result, 0);
    }
}
static Value expression(Expression *e, int minimum, int evaluate)
{
    Value a = primary(e, evaluate);
    if (++e->depth > PP_DEPTH) fail(e->pp, "conditional expression nesting exceeds 64");
    while (e->at < e->ts->count) {
        const char *op = e->ts->items[e->at].text;
        int rank = precedence(op), rhs_evaluate = evaluate;
        Value b;
        if (!strcmp(op, "?") && minimum <= 1) {
            Value yes, no;
            ++e->at; yes = expression(e, 1, evaluate && a.bits != 0);
            if (!take(e, ":")) fail(e->pp, "expected ':' in conditional expression");
            no = expression(e, 1, evaluate && a.bits == 0);
            a = value(a.bits ? yes.bits : no.bits, yes.uns || no.uns); continue;
        }
        if (!rank || rank < minimum) break;
        ++e->at;
        if (!strcmp(op, "&&") && !a.bits) rhs_evaluate = 0;
        if (!strcmp(op, "||") && a.bits) rhs_evaluate = 0;
        b = expression(e, rank + 1, rhs_evaluate);
        a = binary(e->pp, op, a, b, evaluate);
    }
    --e->depth; return a;
}
static int condition(Preprocessor *pp, Tokens *line, size_t begin)
{
    Tokens ts = {0}; size_t i;
    Expression e; Value result;
    for (i = begin; i < line->count; ++i) {
        if (equal(&line->items[i], "defined")) {
            int paren = ++i < line->count && equal(&line->items[i], "(");
            int found;
            if (paren) ++i;
            if (i == line->count || !is_identifier(line->items[i].text)) fail(pp, "expected identifier after defined");
            found = macro_defined(pp, line->items[i].text);
            if (paren && (++i == line->count || !equal(&line->items[i], ")"))) fail(pp, "expected ')' after defined");
            push(&ts, token(found ? "1" : "0", 1, pp->line, 1));
        } else copy_tokens(&ts, line, i, i + 1);
    }
    pp->conditional = 1; expand(pp, &ts, 0); pp->conditional = 0; e.pp = pp; e.ts = &ts; e.at = 0; e.depth = 0;
    result = expression(&e, 1, 1);
    if (e.at != ts.count) fail(pp, "unexpected token in conditional expression");
    clear_tokens(&ts); return result.bits != 0;
}
static void define(Preprocessor *pp, Tokens *ts)
{
    size_t at = 2, i;
    char params[PP_PARAMS][64];
    int index;
    Macro *m;
    if (at == ts->count || !is_identifier(ts->items[at].text) || strlen(ts->items[at].text) >= 64)
        fail(pp, "expected macro identifier (at most 63 characters)");
    index = macro_index(pp, ts->items[at].text);
    if (index < 0) {
        for (index = 0; index < PP_MACROS && pp->macros[index].defined; ++index) {}
        if (index == PP_MACROS) fail(pp, "too many macros");
        if (index >= pp->macro_count) pp->macro_count = index + 1;
    }
    m = &pp->macros[index]; clear_macro(m);
    strcpy(m->name, ts->items[at++].text); m->defined = 1;
    if (at < ts->count && equal(&ts->items[at], "(") && !ts->items[at].gap) {
        m->function = 1; ++at;
        if (at < ts->count && !equal(&ts->items[at], ")")) {
            for (;;) {
                if (at == ts->count || !is_identifier(ts->items[at].text) || strlen(ts->items[at].text) >= 64)
                    fail(pp, "expected macro parameter identifier; variadic macros are unsupported");
                if (m->arity == PP_PARAMS) fail(pp, "too many macro parameters (limit 127)");
                for (i = 0; i < (size_t)m->arity; ++i)
                    if (!strcmp(params[i], ts->items[at].text)) fail(pp, "duplicate macro parameter");
                strcpy(params[m->arity++], ts->items[at++].text);
                if (at == ts->count || !equal(&ts->items[at], ",")) break;
                ++at;
            }
        }
        if (at == ts->count || !equal(&ts->items[at++], ")")) fail(pp, "expected ')' after macro parameters");
        if (m->arity) {
            size_t bytes = (size_t)m->arity * sizeof *m->params;
            m->params = allocate(bytes);
            memcpy(m->params, params, bytes);
        }
    }
    for (i = at; i < ts->count; ++i)
        if (m->function && equal(&ts->items[i], "#") &&
            (i+1==ts->count || macro_parameter(m, &ts->items[i+1])==m->arity))
            fail(pp, "macro stringification requires a parameter");
        else if(equal(&ts->items[i],"##")&&(i==at||i+1==ts->count))fail(pp,"token paste requires two operands");
    copy_tokens(&m->body, ts, at, ts->count);
}
static void emit(Preprocessor *pp, Tokens *ts)
{
    size_t i; int line = -1, column = 1, have_token = 0, previous_macro = 0;
    expand(pp, ts, 0);
    for (i = 0; i < ts->count; ++i) {
        Token *t = &ts->items[i];
        size_t word; int expanded=0;
        for(word=0;word<PP_HIDE_WORDS;++word)expanded|=t->hide[word]!=0;
        if (t->line != line) {
            char marker[32];
            int n = snprintf(marker, sizeof marker, "\n#line %d ", t->line);
            append(&pp->output, marker, (size_t)n);
            if (pp->logical_file) append(&pp->output, pp->logical_file, strlen(pp->logical_file));
            else quoted_path(&pp->output, pp->path, 0);
            append(&pp->output, "\n", 1);
            line = t->line;
            column = 1; have_token = 0; previous_macro = 0;
        }
        // Expanding X to '+' in X+1 must not manufacture the token '++'
        if (have_token && (t->column < column ||
            (t->column == column && (previous_macro || expanded)))) {
            append(&pp->output, " ", 1); ++column;
        }
        while (column < t->column) { append(&pp->output, " ", 1); ++column; }
        append(&pp->output, t->text, strlen(t->text));
        column += (int)strlen(t->text); have_token = 1;
        previous_macro = expanded;
    }
    append(&pp->output, "\n", 1); clear_tokens(ts);
}

/* Binary resources are not source files: no text decoding, NUL rejection or
 * source-line limits. The same parser and lookup serve #embed and its probe. */
typedef struct { Text name; char *resolved; Tokens clause[4]; uint64_t limit; int angled, unsupported; } Embed;
static size_t balanced_end_at(Preprocessor *pp, Tokens *ts, size_t at, unsigned depth)
{
    const char *close; size_t i = at + 1;
    if (depth > PP_DEPTH) fail(pp, "embed delimiter nesting exceeds 64");
    if (equal(&ts->items[at], "(")) close = ")";
    else if (equal(&ts->items[at], "[")) close = "]";
    else close = "}";
    while (i < ts->count) {
        Token *t = &ts->items[i];
        if (equal(t, close)) return i;
        if (equal(t, "(") || equal(t, "[") || equal(t, "{")) i = balanced_end_at(pp, ts, i, depth + 1);
        else if (equal(t, ")") || equal(t, "]") || equal(t, "}")) fail(pp, "mismatched embed delimiter");
        ++i;
    }
    fail(pp, "unterminated embed parameter");
}
static size_t balanced_end(Preprocessor *pp, Tokens *ts, size_t at)
{
    return balanced_end_at(pp, ts, at, 0);
}
static void parse_embed(Preprocessor *pp, Tokens *ts, Embed *e)
{
    size_t at = 0, i; unsigned seen = 0;
    static const char *const names[] = {"limit", "prefix", "suffix", "if_empty"};
    memset(e, 0, sizeof *e); e->limit = UINT64_MAX;
    if (!ts->count) fail(pp, "expected embed resource name");
    if (ts->items[0].text[0] != '"' && !equal(&ts->items[0], "<")) expand(pp, ts, 0);
    if (ts->count && ts->items[0].text[0] == '"') {
        const char *s = ts->items[at++].text;
        append(&e->name, s + 1, strlen(s) - 2);
    } else if (ts->count && equal(&ts->items[0], "<")) {
        e->angled = 1; ++at;
        while (at < ts->count && !equal(&ts->items[at], ">")) {
            append(&e->name, ts->items[at].text, strlen(ts->items[at].text)); ++at;
        }
        if (at == ts->count) fail(pp, "expected '>' after embed resource");
        ++at;
    } else fail(pp, "expected embed resource name");
    if (!e->name.size) fail(pp, "empty embed resource name");
    while (at < ts->count) {
        char name[80]; size_t n, end; int kind = -1, vendor = 0;
        const char *raw = ts->items[at++].text;
        if (!is_identifier(raw)) fail(pp, "expected embed parameter name");
        n = strlen(raw);
        if (n > 4 && !strncmp(raw, "__", 2) && !strcmp(raw + n - 2, "__")) { raw += 2; n -= 4; }
        if (n >= sizeof name) fail(pp, "embed parameter name too long");
        memcpy(name, raw, n); name[n] = 0;
        if (at + 2 < ts->count && equal(&ts->items[at], ":") && equal(&ts->items[at + 1], ":")) {
            at += 2; vendor = 1;
            if (!is_identifier(ts->items[at++].text)) fail(pp, "expected vendor embed parameter name");
        }
        if (!vendor) for (i = 0; i < 4; ++i) if (!strcmp(name, names[i])) kind = (int)i;
        if (kind < 0) e->unsupported = 1;
        if (at == ts->count || !equal(&ts->items[at], "(")) {
            if (kind >= 0) fail(pp, "expected '(' after embed parameter");
            continue;
        }
        end = balanced_end(pp, ts, at);
        if (kind >= 0) {
            if (seen & (1u << kind)) fail(pp, "duplicate embed parameter");
            seen |= 1u << kind;
            copy_tokens(&e->clause[kind], ts, at + 1, end);
            if (!kind) {
                Expression expr; Value v;
                for (i = 0; i < e->clause[0].count; ++i)
                    if (equal(&e->clause[0].items[i], "defined")) fail(pp, "defined is forbidden in embed limit");
                expand(pp, &e->clause[0], 0);
                for (i = 0; i < e->clause[0].count; ++i)
                    if (equal(&e->clause[0].items[i], "defined")) fail(pp, "defined is forbidden in embed limit");
                expr.pp = pp; expr.ts = &e->clause[0]; expr.at = 0; expr.depth = 0;
                v = expression(&expr, 1, 1);
                if (expr.at != expr.ts->count) fail(pp, "unexpected token in embed limit");
                if (!v.uns && (v.bits >> 63)) fail(pp, "negative embed limit");
                e->limit = v.bits;
            }
        }
        at = end + 1;
    }
}
static void record_dependency(Preprocessor *pp, const char *path, int found)
{
    if (pp->dependencies) fprintf(pp->dependencies, "%c %s\n", found ? '+' : '-', path);
}
static FILE *resource_file(Preprocessor *pp, Embed *e, const char *path)
{
    FILE *f = fopen(path, "rb");
    record_dependency(pp, path, f != NULL);
    if (f) { e->resolved = allocate(strlen(path) + 1); strcpy(e->resolved, path); }
    return f;
}
static FILE *open_embed(Preprocessor *pp, Embed *e)
{
    char joined[4096]; int n; FILE *f;
    const char *name = e->name.data;
    if (name[0] == '/' || name[0] == '\\' || (strlen(name) > 1 && name[1] == ':')) return resource_file(pp, e, name);
    if (!e->angled) {
        const char *slash = strrchr(pp->path, '/'), *back = strrchr(pp->path, '\\');
        if (!slash || (back && back > slash)) slash = back;
        n = slash ? snprintf(joined, sizeof joined, "%.*s/%s", (int)(slash - pp->path), pp->path, name) : snprintf(joined, sizeof joined, "%s", name);
        if (n < 0 || (size_t)n >= sizeof joined) fail(pp, "embed path too long");
        f = resource_file(pp, e, joined); if (f) return f;
    }
    n = snprintf(joined, sizeof joined, "%s/%s", pp->include_dir, name);
    if (n < 0 || (size_t)n >= sizeof joined) fail(pp, "embed path too long");
    return resource_file(pp, e, joined);
}
static void free_embed(Embed *e)
{
    size_t i; free(e->name.data); free(e->resolved); for (i = 0; i < 4; ++i) clear_tokens(&e->clause[i]);
}
static int has_embed(Preprocessor *pp, Tokens *ts, size_t at, size_t *end)
{
    Tokens args = {0}; Embed e; FILE *f; int result = 0;
    if (++pp->embed_depth > PP_DEPTH) fail(pp, "__has_embed nesting exceeds 64");
    if (at == ts->count || !equal(&ts->items[at], "(")) fail(pp, "expected '(' after __has_embed");
    *end = balanced_end(pp, ts, at) + 1;
    copy_tokens(&args, ts, at + 1, *end - 1); parse_embed(pp, &args, &e);
    if (!e.unsupported && (f = open_embed(pp, &e)) != NULL) {
        int c = e.limit ? fgetc(f) : EOF;
        if (!ferror(f)) result = c == EOF ? 2 : 1;
        fclose(f);
    }
    clear_tokens(&args); free_embed(&e); --pp->embed_depth; return result;
}
static void embed(Preprocessor *pp, Tokens *line)
{
    Tokens args = {0}, output = {0}; Embed e; FILE *f; uint64_t count = 0; int c;
    copy_tokens(&args, line, 2, line->count); parse_embed(pp, &args, &e);
    if (e.unsupported) fail(pp, "unsupported embed parameter");
    f = open_embed(pp, &e); if (!f) fail(pp, "cannot open embed resource");
    while (count < e.limit && (c = fgetc(f)) != EOF) {
        char number[4]; int n;
        if (!count) copy_tokens(&output, &e.clause[1], 0, e.clause[1].count);
        else push(&output, token(",", 1, pp->line, 1));
        n = snprintf(number, sizeof number, "%u", (unsigned)(unsigned char)c);
        push(&output, token(number, (size_t)n, pp->line, 1)); ++count;
    }
    if (ferror(f)) fail(pp, "embed resource read failed");
    fclose(f);
    copy_tokens(&output, &e.clause[count ? 2 : 3], 0, e.clause[count ? 2 : 3].count);
    {
        EmbeddedRange *r = allocate(sizeof *r);
        r->resource = allocate(strlen(e.resolved) + 1); strcpy(r->resource, e.resolved);
        r->begin = pp->output.size; emit(pp, &output); r->end = pp->output.size;
        r->next = pp->embeds; pp->embeds = r;
    }
    clear_tokens(&args); free_embed(&e);
}

static void file(Preprocessor *pp, const char *path, unsigned depth)
{
    FILE *input;
    const char *saved_path = pp->path;
    const char *saved_logical_file = pp->logical_file;
    char *logical_file = NULL;
    int saved_line = pp->line, line = 0, comment = 0, active = 1, level = 0;
    int parent[32], taken[32], had_else[32];
    size_t total = 0;
    Tokens pending = {0}; char physical[4096];
    pp->path = path; pp->logical_file = NULL; pp->line = 1;
    if (depth > 16) fail(pp, "include nesting exceeds 16");
    input = fopen(path, "rb");
    if (!input) fail(pp, "cannot open source/header");
    if (depth) record_dependency(pp, path, 1);
    {
        unsigned char block[4096]; size_t count;
        while ((count = fread(block, 1, sizeof block, input)) != 0) {
            total += count;
            if (total > 1048576) fail(pp, "source/header exceeds 1 MiB");
            if (memchr(block, 0, count)) fail(pp, "embedded NUL in source/header");
        }
        if (ferror(input) || fseek(input, 0, SEEK_SET)) fail(pp, "source read failed");
    }
    while (fgets(physical, sizeof physical, input)) {
        Text logical = {0}; Tokens ts = {0}; int continued;
        int start;
        if (line == INT_MAX) fail(pp, "source line number overflows");
        start = line + 1;
        do {
            size_t length = strlen(physical), end = length;
            if (line == INT_MAX) fail(pp, "source line number overflows");
            ++line; pp->line = line;
            if (!strchr(physical, '\n') && !feof(input)) fail(pp, "source line exceeds 4095 bytes");
            if (end && physical[end - 1] == '\n') --end;
            if (end && physical[end - 1] == '\r') --end;
            continued = end < length && end && physical[end - 1] == '\\';
            append(&logical, physical, continued ? end - 1 : length);
            if (continued && !fgets(physical, sizeof physical, input)) fail(pp, "unterminated line continuation");
        } while (continued);
        pp->line = start; lex(pp, &ts, logical.data, &comment); free(logical.data);
        if (ts.count && equal(&ts.items[0], "#")) {
            const char *directive;
            if (pending.count) emit(pp, &pending);
            pp->line = start;
            if (ts.count == 1) { clear_tokens(&ts); continue; }
            directive = ts.items[1].text;
            if (!strcmp(directive, "if") || !strcmp(directive, "ifdef") || !strcmp(directive, "ifndef")) {
                int test = 0;
                if (level == 32) fail(pp, "conditional nesting exceeds 32");
                if (!strcmp(directive, "if")) { if (active) test = condition(pp, &ts, 2); }
                else {
                    if (ts.count != 3 || !is_identifier(ts.items[2].text)) fail(pp, "expected one conditional identifier");
                    test = (macro_defined(pp, ts.items[2].text)) == !strcmp(directive, "ifdef");
                }
                parent[level] = active; taken[level] = test; had_else[level++] = 0; active = active && test;
            } else if (!strcmp(directive, "elif") || !strcmp(directive, "elifdef") || !strcmp(directive, "elifndef")) {
                int test;
                if (!level || had_else[level - 1]) fail(pp, "unmatched #elif or #elif after #else");
                test = 0;
                if (parent[level - 1] && !taken[level - 1]) {
                    if (!strcmp(directive, "elif")) test = condition(pp, &ts, 2);
                    else {
                        if (ts.count != 3 || !is_identifier(ts.items[2].text)) fail(pp, "expected one conditional identifier");
                        test = macro_defined(pp, ts.items[2].text) == !strcmp(directive, "elifdef");
                    }
                }
                active = parent[level - 1] && !taken[level - 1] && test; taken[level - 1] |= test;
            } else if (!strcmp(directive, "else")) {
                if (!level || had_else[level - 1]) fail(pp, "unmatched/duplicate #else");
                if (ts.count != 2) fail(pp, "unexpected token after #else");
                had_else[level - 1] = 1; active = parent[level - 1] && !taken[level - 1]; taken[level - 1] = 1;
            } else if (!strcmp(directive, "endif")) {
                if (!level) fail(pp, "unmatched #endif");
                if (ts.count != 2) fail(pp, "unexpected token after #endif");
                active = parent[--level];
            } else if (active && !strcmp(directive, "define")) define(pp, &ts);
            else if (active && !strcmp(directive, "undef")) {
                int index;
                if (ts.count != 3 || !is_identifier(ts.items[2].text)) fail(pp, "expected one macro identifier");
                index = macro_index(pp, ts.items[2].text);
                if (index >= 0) clear_macro(&pp->macros[index]);
            } else if (active && !strcmp(directive, "line")) {
                Tokens args = {0};
                char *end;
                long next;
                copy_tokens(&args, &ts, 2, ts.count);
                expand(pp, &args, 0);
                if (!args.count || args.count > 2 || !isdigit((unsigned char)args.items[0].text[0]))
                    fail(pp, "expected line number and optional filename");
                errno = 0;
                next = strtol(args.items[0].text, &end, 10);
                if (*end || errno || next <= 0 || next >= INT_MAX) fail(pp, "invalid line number");
                if (args.count == 2) {
                    const char *name = args.items[1].text;
                    if (*name != '"' || strlen(name) >= 2048) fail(pp, "invalid line filename");
                    free(logical_file);
                    logical_file = allocate(strlen(name) + 1);
                    strcpy(logical_file, name);
                    pp->logical_file = logical_file;
                }
                line = (int)next - 1;
                clear_tokens(&args);
            } else if (active && !strcmp(directive, "embed")) embed(pp, &ts);
            else if (active && !strcmp(directive, "include")) {
                Text target = {0}; char joined[2048]; size_t i, first = 2; int n;
                if (ts.count > 2 && ts.items[2].text[0] != '"' && !equal(&ts.items[2], "<")) {
                    Tokens operand = {0};
                    copy_tokens(&operand, &ts, 2, ts.count);
                    expand(pp, &operand, 0);
                    clear_tokens(&ts);
                    ts = operand;
                    first = 0;
                }
                if (ts.count == first + 1 && ts.items[first].text[0] == '"')
                    append(&target, ts.items[first].text + 1, strlen(ts.items[first].text) - 2);
                else if (ts.count >= first + 2 && equal(&ts.items[first], "<") && equal(&ts.items[ts.count - 1], ">")) {
                    for (i = first + 1; i + 1 < ts.count; ++i) {
                        if (equal(&ts.items[i], ">")) fail(pp, "extra tokens after header name");
                        append(&target, ts.items[i].text, strlen(ts.items[i].text));
                    }
                } else fail(pp, "expected a literal header name");
                if (!target.size) fail(pp, "empty header name");
                if (equal(&ts.items[first], "<")) n = snprintf(joined, sizeof joined, "%s/%s", pp->include_dir, target.data);
                else {
                    const char *slash = strrchr(path, '/'), *backslash = strrchr(path, '\\');
                    if (!slash || (backslash && backslash > slash)) slash = backslash;
                    if (slash) n = snprintf(joined, sizeof joined, "%.*s/%s", (int)(slash - path), path, target.data);
                    else n = snprintf(joined, sizeof joined, "%s", target.data);
                }
                if (n < 0 || (size_t)n >= sizeof joined) fail(pp, "include path too long");
                free(target.data); file(pp, joined, depth + 1);
            } else if (active) fail(pp, "unsupported preprocessor directive");
        } else if (active) copy_tokens(&pending, &ts, 0, ts.count);
        clear_tokens(&ts);
    }
    if (ferror(input)) fail(pp, "source read failed");
    fclose(input); pp->line = line;
    if (level) fail(pp, "unterminated conditional directive");
    if (comment) fail(pp, "unterminated comment");
    if (pending.count) emit(pp, &pending);
    free(logical_file);
    pp->path = saved_path; pp->logical_file = saved_logical_file; pp->line = saved_line;
}
char *preprocess_with_embeds(const char *path, const char *include_dir, EmbeddedRange **ranges,
                             int binary64, FILE *dependencies)
{
    Preprocessor *pp = calloc(1, sizeof *pp); char *result; int i;
    if (!pp) pp_error(path, 1, "out of memory");
    pp->include_dir = include_dir;
    pp->dependencies = dependencies;
    pp->macro_count = 6;
    strcpy(pp->macros[5].name, "__SIZE_TYPE__"); pp->macros[5].defined = 1;
    push(&pp->macros[5].body, token("unsigned", 8, 1, 1));
    push(&pp->macros[5].body, token("int", 3, 1, 1));
    strcpy(pp->macros[4].name, "__ZICC_BINARY64__"); pp->macros[4].defined = 1;
    push(&pp->macros[4].body, token(binary64 ? "1" : "0", 1, 1, 1));
    strcpy(pp->macros[0].name, "__ZICC__"); pp->macros[0].defined = 1;
    push(&pp->macros[0].body, token("1", 1, 1, 1));
    {
        static const char *const names[] = {"__STDC_EMBED_NOT_FOUND__", "__STDC_EMBED_FOUND__", "__STDC_EMBED_EMPTY__"};
        for (i = 0; i < 3; ++i) {
            char digit = (char)('0' + i);
            strcpy(pp->macros[i + 1].name, names[i]); pp->macros[i + 1].defined = 1;
            push(&pp->macros[i + 1].body, token(&digit, 1, 1, 1));
        }
    }
    file(pp, path, 0);
    if (!pp->output.data) append(&pp->output, "", 0);
    result = pp->output.data;
    for (i = 0; i < PP_MACROS; ++i) clear_macro(&pp->macros[i]);
    *ranges = pp->embeds;
    free(pp); return result;
}

char *preprocess(const char *path, const char *include_dir)
{
    EmbeddedRange *ranges; char *result = preprocess_with_embeds(path, include_dir, &ranges, 0, NULL);
    while(ranges){EmbeddedRange *next = ranges->next; free(ranges->resource); free(ranges); ranges = next;}
    return result;
}
