"""Exercise native long arithmetic, all shift counts, comparison flags and ABI."""
import os
import importlib.util
import json
import random
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
OUT = Path(os.environ.get('ZICC_LOGS_DIR', 'logs')).resolve() / 'long-codegen-check'
sys.path.insert(0, str(ROOT / 'tools'))
from mesen_core import Core

spec = importlib.util.spec_from_file_location('support', ROOT / 'tests/check-compiler.py')
support = importlib.util.module_from_spec(spec)
spec.loader.exec_module(support)


def mask(a, b):
    return int(a == b) | (int(a != b) << 1) | (int(a < b) << 2) | (int(a <= b) << 3) | (int(a > b) << 4) | (int(a >= b) << 5)


def main():
    OUT.mkdir(parents=True, exist_ok=True)
    support.OUT = OUT
    values = (0, 1, 0x7fff, 0xffff, 0x10000, 0x12345678, 0x7fffffff, 0x80000000, 0xffff0000, 0xffffffff)
    cases = [(a, b, n) for a in values for b in values for n in range(32)]
    rng = random.Random(65816)
    cases += [(rng.getrandbits(32), rng.getrandbits(32), rng.randrange(32)) for _ in range(512)]
    rows = []
    for a, b, n in cases:
        sa = a if a < 0x80000000 else a - (1 << 32)
        sb = b if b < 0x80000000 else b - (1 << 32)
        wa, wb = a & 65535, b & 65535
        swa = wa if wa < 32768 else wa - 65536
        swb = wb if wb < 32768 else wb - 65536
        valid_long = int(-0x80000000 <= sa + sb <= 0x7fffffff) | (int(-0x80000000 <= sa - sb <= 0x7fffffff) << 1)
        valid_word = int(-32768 <= swa + swb <= 32767) | (int(-32768 <= swa - swb <= 32767) << 1)
        rows.append((a, b, n, (a + b) & 0xffffffff, (a - b) & 0xffffffff, a & b, a | b, a ^ b,
                     (a << n) & 0xffffffff, a >> n, (sa >> n) & 0xffffffff,
                     ((a << n) ^ (a >> n)) & 0xffffffff, mask(a, b), mask(sa, sb),
                     valid_long, valid_word, (wb - wa) & 65535))
    source = '''unsigned long a,b,ea,es,eb,eo,ex,el,er,ear,em;
unsigned int n,eu,ess,vl,vw,evr;
unsigned long add(unsigned long a,unsigned long b){return a+b;}
unsigned long sub(unsigned long a,unsigned long b){return a-b;}
long sadd(long a,long b){return a+b;}
long ssub(long a,long b){return a-b;}
unsigned int wadd(unsigned int a,unsigned int b){return a+b;}
unsigned int wsub(unsigned int a,unsigned int b){return a-b;}
unsigned int wrev(unsigned int a,unsigned int b){return b-a;}
int wsadd(short a,short b){return a+b;}
int wssub(short a,short b){return a-b;}
unsigned int wand(unsigned int a,unsigned int b){return a&b;}
unsigned int wor(unsigned int a,unsigned int b){return a|b;}
unsigned int wxor(unsigned int a,unsigned int b){return a^b;}
unsigned long band(unsigned long a,unsigned long b){return a&b;}
unsigned long bor(unsigned long a,unsigned long b){return a|b;}
unsigned long bxor(unsigned long a,unsigned long b){return a^b;}
unsigned long shl(unsigned long a,unsigned int n){return a<<n;}
unsigned long shr(unsigned long a,unsigned int n){return a>>n;}
long sar(long a,unsigned int n){return a>>n;}
unsigned long mix(unsigned long a,unsigned int n){return (a>>n)^(a<<n);}
unsigned int ucmp(unsigned long a,unsigned long b){unsigned int r=0;
 if(a==b)r|=1;if(a!=b)r|=2;if(a<b)r|=4;if(a<=b)r|=8;if(a>b)r|=16;if(a>=b)r|=32;return r;}
unsigned int scmp(long a,long b){unsigned int r=0;
 if(a==b)r|=1;if(a!=b)r|=2;if(a<b)r|=4;if(a<=b)r|=8;if(a>b)r|=16;if(a>=b)r|=32;return r;}
unsigned int uvalue(unsigned long a,unsigned long b){return (a==b)|((a!=b)<<1)|((a<b)<<2)|((a<=b)<<3)|((a>b)<<4)|((a>=b)<<5);}
unsigned int svalue(long a,long b){return (a==b)|((a!=b)<<1)|((a<b)<<2)|((a<=b)<<3)|((a>b)<<4)|((a>=b)<<5);}
'''
    for n in range(32):
        source += f'unsigned long cl{n}(unsigned long a){{return a<<{n};}}\n'
        source += f'unsigned long cr{n}(unsigned long a){{return a>>{n};}}\n'
        source += f'long ca{n}(long a){{return a>>{n};}}\n'
    source += '''int check(void){
 if(add(a,b)!=ea)return 1;if(sub(a,b)!=es)return 2;
 if(band(a,b)!=eb)return 3;if(bor(a,b)!=eo)return 4;if(bxor(a,b)!=ex)return 5;
 if(shl(a,n)!=el)return 6;if(shr(a,n)!=er)return 7;if(sar((long)a,n)!=(long)ear)return 8;
 if(mix(a,n)!=em)return 9;if(ucmp(a,b)!=eu||scmp((long)a,(long)b)!=ess)return 10;
 if(uvalue(a,b)!=eu||svalue((long)a,(long)b)!=ess)return 11;
 if(vl&1U){if(sadd((long)a,(long)b)!=(long)ea)return 13;}
 if(vl&2U){if(ssub((long)a,(long)b)!=(long)es)return 14;}
 if(wadd((unsigned int)a,(unsigned int)b)!=(unsigned int)ea)return 15;
 if(wsub((unsigned int)a,(unsigned int)b)!=(unsigned int)es)return 16;
 if(wrev((unsigned int)a,(unsigned int)b)!=evr)return 17;
 if(vw&1U){if(wsadd((short)a,(short)b)!=(short)ea)return 18;}
 if(vw&2U){if(wssub((short)a,(short)b)!=(short)es)return 19;}
 if(wand((unsigned int)a,(unsigned int)b)!=(unsigned int)eb)return 20;
 if(wor((unsigned int)a,(unsigned int)b)!=(unsigned int)eo)return 21;
 if(wxor((unsigned int)a,(unsigned int)b)!=(unsigned int)ex)return 22;
'''
    for n in range(32):
        source += f'if(n=={n}){{if(cl{n}(a)!=el||cr{n}(a)!=er||ca{n}((long)a)!=(long)ear)return 12;}}\n'
    source += 'return 0;}\nint main(void){int i;for(i=0;i<' + str(len(rows)) + ';i++){if(check())return i+1;}return 0;}\n'
    workspace = OUT / 'workspace.s'
    workspace.write_text('.exportzp __arith_lhs,__arith_rhs\n.segment "DP_SCRATCH": zeropage\n'
                         '__arith_lhs: .res 4\n__arith_rhs: .res 28\n', encoding='ascii')
    support.run([support.CC65 / 'ca65.exe', '-o', OUT / 'workspace.o', workspace])
    _, rom, labels = support.compile_case('wide', source, extra_objects=(OUT / 'workspace.o', ROOT / 'build/integers.o'))
    assembly = (OUT / 'wide.s').read_text()
    shift17 = assembly.split('_cr17:', 1)[1].split('__size_cr17', 1)[0]
    assert 'lda 5,s\n    ldx #0\n    lsr a' in shift17 and 'pha' not in shift17 and 'tax' not in shift17, shift17
    for n in range(7, 16):
        shift = assembly.split(f'_cr{n}:', 1)[1].split(f'__size_cr{n}', 1)[0]
        assert 'lda z:__arith_lhs+1' in shift and shift.count('ror z:__arith_lhs') == max(0, n-8), shift
    def function_body(name):
        return assembly.split('_' + name + ':', 1)[1].split('__size_' + name, 1)[0]
    def function_ops(name):
        return [line for line in function_body(name).splitlines() if line.startswith('    ')]
    for name in ('add', 'sub', 'sadd', 'ssub', 'band', 'bor', 'bxor', 'shl', 'shr', 'sar', 'mix'):
        body = function_body(name)
        assert 'tcs' not in body and 'tay' not in body and 'phy' not in body, (name, body)
    assert function_ops('add') == function_ops('sadd')
    assert function_ops('sub') == function_ops('ssub')
    for name in ('wadd', 'wsub', 'wrev', 'wsadd', 'wssub', 'wand', 'wor', 'wxor'):
        body = function_body(name)
        assert 'native word expression leaf' in body and 'tcs' not in body and 'tay' not in body, name
    assert function_ops('wadd') == function_ops('wsadd')
    assert function_ops('wsub') == function_ops('wssub')
    table = ',\n'.join('{' + ','.join(map(str, row)) + '}' for row in rows)
    names = ('a', 'b', 'ea', 'es', 'eb', 'eo', 'ex', 'el', 'er', 'ear', 'em')
    assignments = ''.join(f'long({labels[name]},c[{column}]);' for name, column in zip(names, (1, 2, 4, 5, 6, 7, 8, 9, 10, 11, 12)))
    script = f'''local cases={{{table}}}
local index=0
local function word(p,v) emu.write(((p)&0x1ffff),v&255,emu.memType.snesWorkRam);emu.write(((p+1)&0x1ffff),(v>>8)&255,emu.memType.snesWorkRam) end
local function long(p,v) word(p,v);word(p+2,v>>16) end
emu.addMemoryCallback(function()
 index=index+1;local c=cases[index];if not c then error('extra case') end
 {assignments}
 word({labels['n']},c[3]);word({labels['eu']},c[13]);word({labels['ess']},c[14])
 word({labels['vl']},c[15]);word({labels['vw']},c[16]);word({labels['evr']},c[17])
end,emu.callbackType.exec,{labels['check']},{labels['check']})
emu.addMemoryCallback(function()
 local s=emu.getState()
 if s['cpu.a']~=0 then error('case '..index..' returned '..s['cpu.a']) end
 if index~=#cases or s['cpu.sp']~=0x04ff or s['cpu.y']~=0 or s['cpu.d']~=0 or s['cpu.dbr']~=0x7e or (s['cpu.ps']&0x38)~=0 then error('count/ABI') end
 emu.log('PASS '..index..' wide cases');emu.log('DONE');emu.breakExecution()
end,emu.callbackType.exec,{labels['main_exit']},{labels['main_exit']})
'''
    lua = OUT / 'wide.lua'
    lua.write_text(script, encoding='ascii')
    core = Core(OUT / 'emulator')
    try:
        core.load(rom, lua, script)
        core.start()
        log = core.wait_for('DONE', 45)
        assert 'PASS' in log, log
    finally:
        core.close_with_log(OUT / 'wide.log')
    extra = [ROOT / ('build/' + name + '.o') for name in ('arithmetic', 'integers', 'ieee_engine')]
    abi_cases = {
        'signed_cast_widening': '''long mulcast(unsigned int a){return (int)a*3L;}
            long addcast(unsigned int a){return (int)a+3L;}
            long unsignedcast(int a){return (unsigned int)a*3L;}
            int main(void){unsigned int a=32769U,b=65535U;
            if(mulcast(a)!=-98301L||addcast(a)!=-32764L)return 1;
            if(unsignedcast(-32767)!=98307L)return 2;
            if(!((int)a < -1L)||!((int)b == -1L))return 3;
            if((int)a/(int)b!=32767)return 4;return 0;}''',
        'parameter_homes': '''long adjust(long a,long b){long *p=&a;*p+=b;a-=b;return a;}
            long mixed(int a,long b,int c,long d){b+=a;d-=c;return b+d;}
            long recurse(long a,int depth){long q=a+1L;if(depth)return q+recurse(a+2L,depth-1);return q;}
            int main(void){if(adjust(0x1234ffffL,3L)!=0x1234ffffL)return 1;
            if(mixed(5,100000L,7,200000L)!=299998L)return 2;
            if(recurse(10L,3)!=56L)return 3;return 0;}''',
        'widened_constants': '''unsigned long scale(int a){return a*2UL;}
            int main(void){unsigned long a=0x1234ffffUL,b=3UL;
            if(a+(-1)!=0x1234fffeUL||a-(-1)!=0x12350000UL)return 1;
            if(scale(-1)!=0xfffffffeUL||scale(32767)!=65534UL)return 2;
            if(a+(b*543UL)!=0x1235065cUL)return 3;
            if(a-(b*543UL)!=0x1234f9a2UL)return 4;return 0;}''',
        'float_conditions': '''int main(void){float a=1.0,b=2.0,n=0.0/0.0;
            if(a==b||!(a!=b)||!(a<b)||!(a<=b)||a>b||a>=b)return 1;
            if(n==n||!(n!=n)||n<a||n<=a||n>a||n>=a)return 2;
            if(-0.0||0.0)return 3;return 0;}''',
        'wide_truth': '''__noinline int word_truth(unsigned long value){if(value)return 7;return 11;}
            __noinline int float_truth(float value){if(value)return 13;return 17;}
            int main(void){
                if(word_truth(0)!=11||word_truth(1)!=7||word_truth(0x80000000UL)!=7)return 1;
                if(float_truth(-0.0f)!=17||float_truth(1.0f)!=13||float_truth(-1.0f)!=13)return 2;
                return 0;
            }''',
        'long_predicates': '''long lower;
            __noinline int relative(long delta){return lower<=(delta>>4);}
            __noinline int nonzero(void){return lower!=0L;}
            __noinline long assign_lower(void){lower=7L;return 6L;}
            __noinline int with_call(void){return lower<=(assign_lower()>>1);}
            int main(void){
                lower=-2L;
                if(!nonzero()||!relative(-32L)||relative(-33L))return 1;
                lower=0L;
                if(nonzero()||!relative(1L)||relative(-1L))return 2;
                lower=65536L;
                if(!nonzero()||relative(65536L)||!relative(1048576L))return 3;
                lower=-2147483647L-1L;
                if(!relative(2147483647L)||!relative(lower))return 4;
                lower=7L;
                if(with_call()||lower!=7L)return 5;
                return 0;
            }''',
        'constant_conditions': '''int main(void){if(0)return 1;if(1){}else return 2;return 0;}''',
        'known_high': '''int main(void){unsigned long a=0xfedcba98UL;
            if((a>>17)!=0x7f6eUL)return 1;if((a>>17)==0x00017f6eUL)return 2;
            if((a&0xffffUL)!=0xba98UL)return 3;if((a&0xffffUL)==0x0001ba98UL)return 4;
            return 0;}''',
        'indirect_shift': '''unsigned long *cursor;
            __noinline unsigned long fetch_next(void){return *cursor++ >> 24;}
            __noinline long signed_byte(long *p){return *p >> 26;}
            __noinline unsigned long low_byte(unsigned long *p,int i){return p[i]<<24;}
            __noinline long volatile_byte(volatile long *p){return *p >> 24;}
            __noinline unsigned long *advance(unsigned long *p,long n){return p+n;}
            int main(void){unsigned long a[2]={0xa1234567UL,0x12456789UL};
            long negative=-2147483647L;volatile long observed=-268435455L;
            cursor=a;
            if(fetch_next()!=0xa1UL||cursor!=a+1)return 1;
            if(fetch_next()!=0x12UL||cursor!=a+2)return 2;
            if(signed_byte(&negative)!=-32L||volatile_byte(&observed)!=-16L)return 3;
            if(low_byte(a,1)!=0x89000000UL||advance(a+1,-1L)!=a)return 4;
            return 0;}''',
        'signed_and_indirect': '''typedef struct { long x,y; } Point;
            __noinline int signs(long a){
                return (a<0) | ((a>=0)<<1) | ((0>a)<<2) | ((0<=a)<<3);
            }
            __noinline long delta(const Point *p,const Point *q){return p->y-q->x;}
            __noinline unsigned long combine(const unsigned long *p,const unsigned long *q){return *p^*q;}
            __noinline long reflect(const Point *p,const Point *q,int invert){
                long d=p->y-q->x;
                if(invert)d=-d;
                return d;
            }
            int main(void){
                Point p={0x1270L,0x10000L},q={1L,0x1270L};
                unsigned long a=0x87654321UL,b=0x11223344UL;
                if(signs(-2147483647L-1L)!=5||signs(-1L)!=5||signs(0L)!=10||signs(65535L)!=10)return 1;
                if(delta(&p,&q)!=65535L||delta(&q,&p)!=0L||delta(&q,&q)!=4719L)return 2;
                if(combine(&a,&b)!=0x96477065UL||combine(&a,&a)!=0)return 3;
                if(reflect(&p,&q,1)!=-65535L||reflect(&p,&q,0)!=65535L)return 4;
                return 0;}''',
        'fixed_long_shifts': '''unsigned long bits;
            long signed_bits;
            volatile unsigned long device;
            unsigned char chunks[5];
            __noinline void shift7(void){bits>>=7;}
            __noinline void shift8(void){signed_bits=signed_bits>>8;}
            __noinline void shift_device(void){device>>=7;}
            __noinline long verify(long *p){return p[1]==0x12345678L?p[0]:0;}
            __noinline long shift_stack(long seed){
                long pair[2]={seed,0x12345678L};
                pair[0]>>=7;
                return verify(pair);
            }
            __noinline void split(long seed){
                unsigned long value=(unsigned long)((seed-516L)>>2);
                int i=0;
                while(value){
                    chunks[i]=(unsigned char)(value&127U);
                    value>>=7;
                    if(value)chunks[i]|=128U;
                    ++i;
                }
            }
            int main(void){
                bits=0x89abcdefUL;shift7();if(bits!=0x0113579bUL)return 1;
                signed_bits=(long)0x89abcdefUL;shift8();if((unsigned long)signed_bits!=0xff89abcdUL)return 2;
                signed_bits=0x76543210L;shift8();if(signed_bits!=0x765432L)return 3;
                if((unsigned long)shift_stack((long)0x89abcdefUL)!=0xff13579bUL)return 4;
                if(shift_stack(-2147483647L-1L)!=-16777216L)return 5;
                device=0x89abcdefUL;shift_device();if(device!=0x0113579bUL)return 6;
                split(4132L);if(chunks[0]!=136||chunks[1]!=7||chunks[2]!=0)return 7;
                return 0;
            }''',
        'word_operands': '''int wa(int a,int b){return a+5;}
            int wb(int a,int b){return 5+b;}int wc(int a,int b){return 5-b;}
            int wd(int a,int b){return a+a;}int we(int a,int b){return b+b;}
            unsigned int mask(unsigned int a,unsigned int b){return b&65535U;}
            int main(void){if(wa(-12,77)!=-7||wb(77,-12)!=-7)return 1;
            if(wc(77,-12)!=17||wd(-12,77)!=-24||we(77,-12)!=-24)return 2;
            if(mask(123U,65535U)!=65535U)return 3;return 0;}''',
    }
    for name, text in abi_cases.items():
        _, image, syms = support.compile_case(name, text, extra_objects=extra)
        support.emulate(image, syms, 0)
        if name == 'constant_conditions':
            assert 'cmp #0' not in (OUT / (name + '.s')).read_text()
        if name == 'indirect_shift':
            text = (OUT / (name + '.s')).read_text()
            fetch = text.split('_fetch_next:\n', 1)[1].split('__size_fetch_next', 1)[0]
            assert 'lda a:$0002,x' in fetch and 'lda a:$0000,x' not in fetch, fetch
            assert 'xba' in fetch and 'lsr a' not in fetch, fetch
        if name == 'signed_and_indirect':
            text = (OUT / (name + '.s')).read_text()
            signs = text.split('_signs:\n', 1)[1].split('__size_signs', 1)[0]
            delta = text.split('_delta:\n', 1)[1].split('__size_delta', 1)[0]
            assert 'bmi' in signs or 'bpl' in signs, signs
            assert 'sbc' not in signs, signs
            assert 'sbc z:__arith_rhs+2' in delta and 'plx' not in delta, delta
        if name == 'wide_truth':
            text = (OUT / (name + '.s')).read_text()
            for function in ('word_truth', 'float_truth'):
                test = text.split(f'_{function}:\n', 1)[1].split(f'__size_{function}', 1)[0]
                assert '    ora ' in test and '__arith_lhs' not in test, test
        if name == 'long_predicates':
            text = (OUT / (name + '.s')).read_text()
            relative = text.split('_relative:\n', 1)[1].split('__size_relative', 1)[0]
            nonzero = text.split('_nonzero:\n', 1)[1].split('__size_nonzero', 1)[0]
            with_call = text.split('_with_call:\n', 1)[1].split('__size_with_call', 1)[0]
            assert 'sbc a:.loword(_lower)' in relative and '    pha\n' not in relative, relative
            assert '    ora a:.loword(_lower)' in nonzero, nonzero
            assert 'sbc z:__arith_rhs' in with_call and '    pha\n' in with_call, with_call
        if name == 'fixed_long_shifts':
            text = (OUT / (name + '.s')).read_text()
            for function in ('shift7', 'shift8', 'shift_stack', 'shift_device'):
                block = text.split(f'_{function}:\n', 1)[1].split(f'__size_{function}', 1)[0]
                assert ('; shift long in its fixed home' in block)==(function!='shift_device'), block
            block = text.split('_split:\n', 1)[1].split('__size_split', 1)[0]
            shift = block.split('; shift long in its fixed home\n', 1)[1]
            assert re.search(r'lda z:__arith_lhs\+\d+\n    xba\n    asl a\n    lda z:__arith_lhs\+\d+', shift), shift
        print('PASS ' + name, flush=True)
    (OUT / 'results.json').write_text(json.dumps(dict(vectors=len(rows), shifts=list(range(32)), seed=65816,
                                                     abi_cases=list(abi_cases)), indent=2), encoding='utf-8')
    print(re.search(r'PASS[^\r\n]*', log)[0])


if __name__ == '__main__':
    main()
