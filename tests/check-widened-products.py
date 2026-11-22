"""Check full word products, cast provenance, deferred loads and ALU latency."""
import os
import importlib.util
import json
import re
from pathlib import Path
import random
import sys

ROOT = Path(__file__).resolve().parents[1]
OUT = Path(os.environ.get('ZICC_LOGS_DIR', 'logs')).resolve() / 'widened-product-check'
sys.path.insert(0, str(ROOT / 'tools'))
from mesen_core import Core
spec = importlib.util.spec_from_file_location('support', ROOT / 'tests/check-compiler.py')
support = importlib.util.module_from_spec(spec)
spec.loader.exec_module(support)


def main():
    OUT.mkdir(parents=True, exist_ok=True)
    support.OUT = OUT
    boundary = (0,1,127,128,255,256,257,32767,32768,32769,65535)
    pairs = [(a,b) for a in boundary for b in boundary]
    rng = random.Random(160032)
    pairs += [(rng.randrange(65536),rng.randrange(65536)) for _ in range(4096)]
    rows = []
    def row(a,b,base):
        sa = a if a<32768 else a-65536
        sb = b if b<32768 else b-65536
        return (a,b,base,*[v&0xffffffff for v in
            (sa*sb,a*b,sa*b,a*sb,base+sa*sb,base^(sa*sb),
             base+(sa*sb)*3,(a&255)*(b&255),sa*base,a*base,sa*base*3,base*65535,a*31337)])
    for a,b in pairs:
        rows.append(row(a,b,rng.getrandbits(32)))
    long_boundary=(0,1,255,256,65535,65536,65537,0x7fffffff,0x80000000,0x80000001,0xfffffffe,0xffffffff)
    rows += [row(a,65535,value) for a in boundary for value in long_boundary]
    source = '''unsigned int a,b;unsigned long base,expected[13];
unsigned long ss(int x,int y){return (unsigned long)x*(unsigned long)y;}
unsigned long uu(unsigned int x,unsigned int y){return (unsigned long)x*(unsigned long)y;}
unsigned long su(int x,unsigned int y){return (long)x*(unsigned long)y;}
unsigned long us(unsigned int x,int y){return (unsigned long)x*(long)y;}
unsigned long scaled(unsigned long z,int x,int y){return z+(unsigned long)x*(unsigned long)y;}
unsigned long bits(unsigned long z,int x,int y){return z^((unsigned long)x*(unsigned long)y);}
unsigned long nested(unsigned long z,int x,int y){return z+((unsigned long)x*(unsigned long)y)*3UL;}
unsigned long bytes(unsigned int x,unsigned int y){return (unsigned long)(unsigned char)x*(unsigned long)(unsigned char)y;}
struct Record{unsigned int guard;unsigned long value;};struct Record record;
unsigned long array[2];
unsigned long member_sum(int x,int y){return record.value+(long)x*y;}
unsigned long array_sum(int x,int y){return array[1]+(long)x*y;}
unsigned long band(unsigned long z,int x,int y){return z&((long)x*y);}
unsigned long bor(unsigned long z,int x,int y){return z|((long)x*y);}
unsigned long changed;unsigned int calls;
int observe(int x){calls+=1;return x;}
#ifdef __ZICC__
__noinline
#endif
unsigned long mutate(void){changed=99UL;return 7UL;}
unsigned long effects(int x,int y){return (unsigned long)observe(x)*(unsigned long)observe(y);}
unsigned long across_call(void){return changed+mutate();}
unsigned long truncation(unsigned long x,unsigned long y){return (unsigned long)(int)x*(unsigned long)(unsigned int)y;}
#ifdef __ZICC__
__noinline
#endif
unsigned long full(unsigned long x,unsigned long y){return x*y;}
volatile unsigned long product_left,product_right;
unsigned long word_long(int x,unsigned long y){return (unsigned long)x*y;}
unsigned long long_word(unsigned long x,int y){return x*(unsigned long)y;}
unsigned long uword_long(unsigned int x,unsigned long y){return (unsigned long)x*y;}
unsigned long long_uword(unsigned long x,unsigned int y){return x*(unsigned long)y;}
unsigned long long_literal(unsigned long x){return x*65535UL;}
unsigned long word_literal(unsigned int x){return 31337UL*x;}
long signed_word_long(int x,long y){return (long)x*y;}
long signed_long_word(long x,int y){return x*(long)y;}
unsigned long mixed_truncation(unsigned long x,unsigned long y){return (unsigned long)(int)x*y;}
unsigned long changed_sign(int x,unsigned long y){return (unsigned long)(unsigned int)x*y;}
unsigned long observe_long(unsigned long x){calls+=1;return x*3UL;}
unsigned long mixed_effects(int x,unsigned long y){return (unsigned long)observe(x)*observe_long(y);}
unsigned long reversed_effects(unsigned long x,int y){return observe_long(x)*(unsigned long)observe(y);}
struct Record mixed;
unsigned long mixed_member(struct Record *p){return (unsigned long)p->guard*p->value;}
unsigned long reversed_member(struct Record *p){return p->value*(unsigned long)p->guard;}
int check(void){
if(ss((int)a,(int)b)!=expected[0])return 1;
if(uu(a,b)!=expected[1])return 2;
if(su((int)a,b)!=expected[2])return 3;
if(us(a,(int)b)!=expected[3])return 4;
if(scaled(base,(int)a,(int)b)!=expected[4])return 5;
if(bits(base,(int)a,(int)b)!=expected[5])return 6;
if(nested(base,(int)a,(int)b)!=expected[6])return 7;
if(bytes(a,b)!=expected[7])return 8;
calls=0;if(effects((int)a,(int)b)!=expected[0]||calls!=2)return 9;
if(truncation((unsigned long)a+65536UL,(unsigned long)b+65536UL)!=expected[2])return 10;
record.guard=77;record.value=base;array[1]=base;
if(member_sum((int)a,(int)b)!=expected[4]||array_sum((int)a,(int)b)!=expected[4]||record.guard!=77)return 13;
if(band(base,(int)a,(int)b)!=(base&expected[0]))return 14;
if(bor(base,(int)a,(int)b)!=(base|expected[0]))return 15;
if(word_long((int)a,base)!=expected[8]||long_word(base,(int)a)!=expected[8])return 16;
if(uword_long(a,base)!=expected[9]||long_uword(base,a)!=expected[9])return 17;
if((unsigned long)signed_word_long((int)a,(long)base)!=expected[8]||
   (unsigned long)signed_long_word((long)base,(int)a)!=expected[8])return 18;
if(mixed_truncation((unsigned long)a+65536UL,base)!=expected[8]||changed_sign((int)a,base)!=expected[9])return 19;
calls=0;if(mixed_effects((int)a,base)!=expected[10]||calls!=2)return 20;
calls=0;if(reversed_effects(base,(int)a)!=expected[10]||calls!=2)return 21;
mixed.guard=a;mixed.value=base;
if(mixed_member(&mixed)!=expected[9]||reversed_member(&mixed)!=expected[9])return 22;
if(long_literal(base)!=expected[11]||word_literal(a)!=expected[12])return 24;
return 0;}
int main(void){int i;changed=11UL;if(across_call()!=18UL||changed!=99UL)return 11;
product_left=0x12345678UL;product_right=0xfedcba98UL;
if(full(product_left,product_right)!=0x35068740UL)return 12;
product_right=255UL;if(full(product_left,product_right)!=0x22222188UL)return 23;
for(i=0;i<COUNT;i++){if(check())return i+1;}return 0;}
'''.replace('COUNT',str(len(rows)))
    extra = [ROOT / ('build/'+n+'.o') for n in ('arithmetic','integers','ieee_engine')]
    _,rom,labels = support.compile_case('products',source,extra_objects=extra)
    assembly = (OUT/'products.s').read_text()
    def body(name):
        return assembly.split('_'+name+':',1)[1].split('__size_'+name,1)[0]
    for name in ('ss','uu','su','us','scaled','bits','effects','truncation','bytes','member_sum','array_sum','band','bor'):
        assert '__mul16wide' in body(name), name
    assert '__mul32' in body('full')
    assert '__mul16x32' in body('long_literal')
    assert '__mul16wide' in body('word_literal')
    for name in ('word_long','long_word','uword_long','long_uword','signed_word_long','signed_long_word',
                 'mixed_truncation','changed_sign','mixed_effects','reversed_effects','mixed_member','reversed_member'):
        assert '__mul16x32' in body(name),name
    assert body('scaled').index('__mul16wide') < re.search(r'    adc (?:a:|z:|\d+,s)',body('scaled')).start()
    assert body('across_call').index('lda a:.loword(_changed)') < body('across_call').index('_mutate')
    def code_size(name):
        dump = support.run([support.CC65 / 'od65.exe', '--dump-segments', ROOT / f'build/integers-{name}.o']).stdout
        return int(re.search(r'Name:\s*"CODE"\s+Flags:\s+\d+\s+Size:\s+(\d+)', dump)[1])
    table = ',\n'.join('{'+','.join(map(str,row))+'}' for row in rows)
    script = f'''local cases={{{table}}}
local index=0
local trigger=0
local minimum=1000000
local active=nil
local products=0
local verified={{}}
local word_word_counts={{}}
local word_long_counts={{}}
local function word(p,v) emu.write(((p)&0x1ffff),v&255,emu.memType.snesWorkRam);emu.write(((p+1)&0x1ffff),(v>>8)&255,emu.memType.snesWorkRam) end
local function long(p,v) word(p,v);word(p+2,v>>16) end
local function sampling() return index<=1 or index>#cases-{len(boundary)*len(long_boundary)} end
emu.addMemoryCallback(function() if sampling() then trigger=emu.getState().masterClock;if active then products=products+1 end end end,emu.callbackType.write,0x004203,0x004203)
local function hardware_count(name,first,last,count)
 local expected=nil
 emu.addMemoryCallback(function()
  if sampling() then
   active=name;products=0;expected=type(count)=='function' and count() or count
  end
 end,emu.callbackType.exec,first,first)
 emu.addMemoryCallback(function()
  if not sampling() then return end
  if active~=name or products~=expected then error(name..' hardware products '..products) end
  if name=='word_word' then word_word_counts[products]=true end
  if name=='word_long' then word_long_counts[products]=true end
  verified[name]=true;active=nil
 end,emu.callbackType.exec,last,last)
end
local function word_word_products()
 local wram=emu.memType.snesWorkRam
 local left=emu.read({labels['_arith_lhs']+1},wram,false)==0 and 1 or 2
 local right=emu.read({labels['_arith_rhs']+1},wram,false)==0 and 1 or 2
 return left*right
end
local function word_long_products()
 local wram=emu.memType.snesWorkRam
 local high_byte=emu.read({labels['_arith_lhs']+1},wram,false)
 local high_word=emu.read16({labels['_arith_rhs']+2},wram,false)
 if high_byte==0 then return high_word==0 and 2 or 4 end
 return high_word==0 and 4 or 7
end
hardware_count('word_word',{labels['_mul16wide']},{labels['_mul16wide']+code_size('mul16wide')-1},word_word_products)
hardware_count('word_long',{labels['_mul16x32']},{labels['_mul16x32']+code_size('mul16x32')-1},word_long_products)
hardware_count('long_long',{labels['_mul32']},{labels['mul32_byte']-1},10)
hardware_count('long_byte',{labels['mul32_byte']},{labels['_mul32']+code_size('mul32')-1},4)
emu.addMemoryCallback(function()
 if not sampling() then return end
 local delta=emu.getState().masterClock-trigger
 if delta<48 then error('early multiply read '..delta) end
 minimum=math.min(minimum,delta)
end,emu.callbackType.read,0x004216,0x004217)
emu.addMemoryCallback(function()
 index=index+1;local c=cases[index];if not c then error('extra case') end
 word({labels['a']},c[1]);word({labels['b']},c[2]);long({labels['base']},c[3])
 for i=1,13 do long({labels['expected']}+(i-1)*4,c[i+3]) end
end,emu.callbackType.exec,{labels['check']},{labels['check']})
emu.addMemoryCallback(function()
 local s=emu.getState()
 if s['cpu.a']~=0 then error('case '..index..' returned '..s['cpu.a']) end
 if index~=#cases or s['cpu.sp']~=0x04ff or s['cpu.y']~=0 or s['cpu.d']~=0 or s['cpu.dbr']~=0x7e or (s['cpu.ps']&0x38)~=0 then error('count/ABI') end
 if minimum==1000000 then error('no hardware reads') end
 if not verified.word_word or not verified.word_long or not verified.long_long or not verified.long_byte then error('missing hardware count') end
 if not word_word_counts[1] or not word_word_counts[2] or not word_word_counts[4] then error('missing adaptive word multiply path') end
 if not word_long_counts[2] or not word_long_counts[4] or not word_long_counts[7] then error('missing adaptive multiply path') end
 emu.log('PASS '..index..' vectors; minimum multiply delay '..minimum);emu.log('DONE');emu.breakExecution()
end,emu.callbackType.exec,{labels['main_exit']},{labels['main_exit']})
'''
    lua = OUT/'products.lua'
    lua.write_text(script,encoding='ascii')
    core = Core(OUT/'emulator')
    try:
        core.load(rom,lua,script)
        core.start()
        log = core.wait_for('DONE',60)
        assert 'PASS' in log,log
    finally:
        core.close_with_log(OUT/'products.log')
    (OUT/'results.json').write_text(json.dumps(dict(vectors=len(rows),products=len(rows)*28,seed=160032,hardware_products=dict(word_word=[1,2,4],word_long=[2,4,7],long_long=10,long_byte=4)),indent=2))
    print(log)


if __name__=='__main__':
    main()
