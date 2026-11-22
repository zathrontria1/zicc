"""Check general word plans, input lifetimes, stack arguments and safe fallbacks."""
import os
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import random
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'tools'))
from mesen_core import Core
SPEC = importlib.util.spec_from_file_location('support', ROOT / 'tests/check-compiler.py')
support = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(support)
COEFFICIENTS = (0,1,2,3,4,5,7,9,10,15,17,31,255,257,-1,-3,-7,32768,65535,4095,12345)


def word(value):
    return value & 65535


def signed(value):
    return value if value < 32768 else value - 65536


def fixture():
    source = 'unsigned int a,b,c,d,e,f,g,h,expected[128];\n'
    functions = []
    for i,k in enumerate(COEFFICIENTS):
        literal = f'({k})' if k < 0 else f'{k}U'
        for side in ('right','left'):
            name = f'scale_{side}_{i}'
            expression = f'x*{literal}' if side == 'right' else f'{literal}*x'
            source += f'unsigned int {name}(unsigned int x){{return {expression};}}\n'
            functions.append((name, 'a', lambda v,k=k: word(v[0]*k)))
    expressions = [
        ('mix4', 'a+b*2U+c*3U+d*4U', lambda v: word(v[0]+2*v[1]+3*v[2]+4*v[3])),
        ('late', '(c*3U+d*5U)+(a*7U+b*9U)', lambda v: word(3*v[2]+5*v[3]+7*v[0]+9*v[1])),
        ('repeat', '(a+b*2U)+(a*3U+b*5U)', lambda v: word(4*v[0]+7*v[1])),
        ('reverse', 'a-(b*3U+c)', lambda v: word(v[0]-3*v[1]-v[2])),
        ('difference', '(a-b)-(c-d)', lambda v: word((v[0]-v[1])-(v[2]-v[3]))),
        ('bits', '(a*3U^b*5U)|((c+7U)&(d*9U))', lambda v: word((3*v[0]^5*v[1])|((v[2]+7)&(9*v[3])))),
        ('shifts', '((a<<3)^(b>>2))+((c<<7)|(d>>1))', lambda v: word((word(v[0]<<3)^(v[1]>>2))+(word(v[2]<<7)|(v[3]>>1)))),
        ('wrapped_shift', '(a*3U)>>2', lambda v: word(v[0]*3)>>2),
        ('signed_shift_cast', '(unsigned int)((int)a>>3)+(b>>2)', lambda v: word((signed(v[0])>>3)+(v[1]>>2))),
        ('unsigned_shift_cast', '((unsigned int)(int)a)>>3', lambda v: v[0]>>3),
        ('unary', '(-(+a))^(~b)', lambda v: word((-v[0])^(~v[1]))),
        ('byte_dup', '(a&255U)*257U', lambda v: word((v[0]&255)*257)),
        ('byte_shift', '(a&255U)*256U', lambda v: word((v[0]&255)*256)),
        ('bounded_lut', '0x0101U*(0xFFU>>(a&7U))', lambda v: word(0x0101*(0xff>>(v[0]&7)))),
        ('bounded_lut_sub', '0x0101U*(0xFFU>>(8U-(a&7U)))', lambda v: word(0x0101*(0xff>>(8-(v[0]&7))))),
        ('var_shift_peel', 'a<<((b&3U)+4U)', lambda v: word(v[0]<<((v[1]&3)+4))),
    ]
    for name,expr,expected in expressions:
        source += f'unsigned int {name}(unsigned int a,unsigned int b,unsigned int c,unsigned int d){{return {expr};}}\n'
        functions.append((name, 'a,b,c,d', expected))
    source += 'unsigned int eight(unsigned int a,unsigned int b,unsigned int c,unsigned int d,unsigned int e,unsigned int f,unsigned int g,unsigned int h){return a+3U*b+5U*c+7U*d+9U*e+11U*f+13U*g+15U*h;}\n'
    functions.append(('eight', 'a,b,c,d,e,f,g,h', lambda v: word(sum(x*k for x,k in zip(v,(1,3,5,7,9,11,13,15))))))
    source += 'int sar(int a,int b){return (a>>3)+(b>>2);}\n'
    functions.append(('sar', '(int)a,(int)b', lambda v: word((signed(v[0])>>3)+(signed(v[1])>>2))))
    source += 'int signed_scale(int a){return a*7;}\nint signed_neg_scale(int a){return a*(-7);}\n'
    functions.append(('signed_scale', '(int)(a&4095U)-2048', lambda v: word(((v[0]&4095)-2048)*7)))
    functions.append(('signed_neg_scale', '(int)(a&4095U)-2048', lambda v: word(((v[0]&4095)-2048)*(-7))))
    source += 'unsigned int variable(unsigned int a,unsigned int b){return a*b;}\n'
    functions.append(('variable', 'a,b', lambda v: word(v[0]*v[1])))
    terms = ['a','c','d','a','c','d','a','c','d','a','c','d','a','c','d','b']
    def balanced(items):
        if len(items)==1:
            return f'({items[0]}*2U)'
        middle=len(items)//2
        return '('+balanced(items[:middle])+'+'+balanced(items[middle:])+')'
    source += 'unsigned int deep(unsigned int a,unsigned int b,unsigned int c,unsigned int d){return '+balanced(terms)+';}\n'
    functions.append(('deep', 'a,b,c,d', lambda v: word(2*sum(v['abcd'.index(t)] for t in terms))))
    source += 'struct Fields{unsigned int x,y;unsigned char guard;};struct Fields fields;\nunsigned int members(void){return fields.x+fields.y*3U;}\n'
    functions.append(('members', '', lambda v: word(v[0]+3*v[1])))
    source += 'int check(void){fields.x=a;fields.y=b;fields.guard=77;\n'
    for i,(name,args,_) in enumerate(functions):
        source += f'if((unsigned int){name}({args})!=expected[{i}])return {i+1};\n'
    source += 'if(fields.guard!=77)return 63;return 0;}\n'
    return source,functions


EFFECTS = '''unsigned int calls,index;
struct Box{unsigned int value;unsigned char guard;};struct Box boxes[2];
unsigned int observe(unsigned int n){calls+=1;return n+1U;}
unsigned int zero(unsigned int n){return observe(n)*0U;}
unsigned int left(unsigned int n){return 3U*observe(n);}
unsigned int twice(unsigned int n){return observe(n)*3U+observe(n)*5U;}
struct Box *get(void){calls+=1;return &boxes[index];}
unsigned int flip(void){index^=1;return 6;}
unsigned long wide(unsigned long x){return x*3UL;}
int main(void){unsigned int n;
 for(n=0;n<256U;n++){
  calls=0;if(zero(n)!=0||calls!=1)return 1;
  calls=0;if(left(n)!=(n+1U)*3U||calls!=1)return 2;
  calls=0;if(twice(n)!=(n+1U)*8U||calls!=2)return 3;
 }
 boxes[0].value=10;boxes[1].value=20;boxes[0].guard=11;boxes[1].guard=22;
 calls=0;index=0;get()->value*=3U;if(calls!=1||boxes[0].value!=30)return 4;
 calls=0;index=0;get()->value=flip()*3U;
 if(calls!=1||boxes[0].value!=18||boxes[1].value!=20||index!=1)return 5;
 calls=0;if(get()->value*5U!=100||calls!=1)return 6;
 if(boxes[0].guard!=11||boxes[1].guard!=22)return 7;
 if(wide(0x12345678UL)!=0x369d0368UL)return 8;
 return 0;}
'''


def vectors():
    edges=(0,1,2,127,128,255,256,32767,32768,32769,65534,65535)
    result=[(a,word(a*40503+1),word(a^0x55aa),word(65535-a),word(a+5),word(a*7),word(a^0xaa55),word(a-7)) for a in edges]
    rng=random.Random(65816)
    result += [tuple(rng.randrange(65536) for _ in range(8)) for _ in range(2048)]
    return result


def worker(args):
    out=args.output.resolve()/str(args.batch);out.mkdir(parents=True,exist_ok=True);support.OUT=out
    original_run=support.run
    def run(command,**kw):
        command=list(command)
        if Path(command[0])==ROOT/'build/zicc.exe':command[0]=args.compiler.resolve()
        return original_run(command,**kw)
    support.run=run
    source,functions=fixture();rows=vectors()[args.batch*256:(args.batch+1)*256]
    if args.effects:source=EFFECTS
    else:source+=f'int main(void){{unsigned int i;for(i=0;i<{len(rows)}U;i++)if(check())return 1;return 0;}}\n'
    workspace=out/'workspace.s';workspace.write_text('.exportzp __arith_lhs,__arith_rhs\n.segment "DP_SCRATCH": zeropage\n__arith_lhs: .res 4\n__arith_rhs: .res 28\n')
    run([support.CC65/'ca65.exe','-o',out/'workspace.o',workspace])
    name='effects' if args.effects else 'expressions'
    _,rom,labels=support.compile_case(name,source,extra_objects=(out/'workspace.o',ROOT/'build/integers.o'))
    assembly=(out/(name+'.s')).read_text()
    def body(name):return assembly.split('_'+name+':',1)[1].split('__size_'+name,1)[0]
    if args.expect_planner:
        if not args.effects:
            for selected in ('mix4','late','repeat','reverse','difference','bits','shifts','wrapped_shift','signed_shift_cast','unsigned_shift_cast','unary','byte_dup','byte_shift','eight','sar','signed_scale','signed_neg_scale','members'):
                text=body(selected);assert '; native word expression leaf' in text,selected
                assert not re.search(r'^    (?:jsr|phy|ply|pha|pla|phx|plx|tcs|tsc)\b',text,re.M),(selected,text)
            assert '    xba\n' in body('byte_dup') and '    ora ' in body('byte_dup'),body('byte_dup')
            assert '    xba\n' in body('byte_shift') and '    and #$FF00' in body('byte_shift'),body('byte_shift')
            assert '; bounded expression lookup' in body('bounded_lut'),body('bounded_lut')
            assert '; bounded expression lookup' in body('bounded_lut_sub'),body('bounded_lut_sub')
            assert '    asl a\n    asl a\n    asl a\n    asl a\n' in body('var_shift_peel'),body('var_shift_peel')
            assert len(re.findall(r'^    \w+',body('mix4'),re.M))==18,body('mix4')
            assert '; native word expression leaf' not in body('deep'),body('deep')
            assert '__mul16' in body('variable') and '__mul16' in body('scale_right_20')
        else:
            assert '__mul16' not in body('left') and '__mul16' not in body('zero')
            assert '__mul16x32' in body('wide') and '__mul32' not in body('wide'),body('wide')
    table=[]
    for values in rows:
        table.append('{'+','.join(map(str,list(values)+[fn(values) for _,_,fn in functions]))+'}')
    script='local cases={'+','.join(table)+'}\nlocal index=0\nlocal start,sp,y=0,0,0\n'
    script+='local function word(p,v) emu.write(((p)&0x1ffff),v&255,emu.memType.snesWorkRam);emu.write(((p+1)&0x1ffff),(v>>8)&255,emu.memType.snesWorkRam) end\n'
    if not args.effects:
        script+='emu.addMemoryCallback(function() index=index+1;local c=cases[index];if not c then error("extra case") end\n'
        for i,label in enumerate('abcdefgh',1):script+=f'word({labels[label]},c[{i}])\n'
        script+=f'for i=1,{len(functions)} do word({labels["expected"]}+(i-1)*2,c[i+8]) end\n'
        script+=f'end,emu.callbackType.exec,{labels["check"]},{labels["check"]})\n'
    script+=f'''emu.addMemoryCallback(function() local s=emu.getState();start=s.masterClock;sp=s['cpu.sp'];y=s['cpu.y'] end,emu.callbackType.exec,{labels['main']},{labels['main']})
emu.addMemoryCallback(function()
 local s=emu.getState()
 if s['cpu.a']~=0 then error('result '..s['cpu.a']..' case '..index) end
 if s['cpu.sp']~=sp+3 or s['cpu.y']~=y or s['cpu.d']~=0 or s['cpu.dbr']~=126 then error('ABI') end
 emu.log('PASS '..index..' '..(s.masterClock-start));emu.log('DONE');emu.breakExecution()
end,emu.callbackType.exec,{labels['main_exit']},{labels['main_exit']})
'''
    scriptfile=out/'measure.lua';scriptfile.write_text(script);core=Core(out/'home')
    try:
        core.load(rom,scriptfile,script);core.start();log=core.wait_for('DONE',60)
        match=re.search(r'PASS (\d+) (\d+)',log);assert match,log
        if not args.effects:assert int(match[1])==len(rows)
        result=dict(vectors=len(rows) if not args.effects else 0,functions=len(functions) if not args.effects else 0,master_clocks=int(match[2]),
                    compiler_sha256=hashlib.sha256(args.compiler.read_bytes()).hexdigest(),source_sha256=hashlib.sha256(source.encode()).hexdigest(),
                    vectors_sha256=hashlib.sha256(','.join(table).encode()).hexdigest(),runtime_sha256=hashlib.sha256((ROOT/'build/integers.o').read_bytes()).hexdigest(),rom_sha256=hashlib.sha256(rom.read_bytes()).hexdigest(),emulator=core.version)
        (out/'results.json').write_text(json.dumps(result,indent=2)+'\n');print(name,args.batch,result['vectors'],result['master_clocks'],flush=True)
    finally:core.close_with_log(out/'measure.log')


def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--compiler',type=Path,default=ROOT/'build/zicc.exe')
    parser.add_argument('--output',type=Path,default=Path(os.environ.get('ZICC_LOGS_DIR', 'logs')).resolve() / 'word-expression-check');parser.add_argument('--batch',type=int)
    parser.add_argument('--effects',action='store_true');parser.add_argument('--expect-planner',action='store_true');args=parser.parse_args()
    if args.batch is not None:worker(args);return
    args.output.mkdir(parents=True,exist_ok=True)
    support.run([ROOT/'tools/msvc.cmd','/nologo','/std:c17','/W4','/WX','/O2','/D_CRT_SECURE_NO_WARNINGS',
                 '/Fo'+str(args.output.resolve())+'/', '/Fe'+str(args.output.resolve()/'plans.exe'),
                 ROOT/'tests/word-plan-driver.c',ROOT/'src/preprocess.c',ROOT/'src/relax.c'])
    result=support.run([args.output.resolve()/'plans.exe']);print(result.stdout.strip(),flush=True)
    results=[]
    for batch in range((len(vectors())+255)//256+1):
        command=[sys.executable,__file__,'--compiler',str(args.compiler),'--output',str(args.output),'--batch',str(batch)]
        if batch==(len(vectors())+255)//256:command.append('--effects')
        if args.expect_planner:command.append('--expect-planner')
        subprocess.run(command,check=True)
        results.append(json.loads((args.output/str(batch)/'results.json').read_text()))
    (args.output/'results.json').write_text(json.dumps(dict(batches=results,vectors=sum(r['vectors'] for r in results),
        function_results=sum(r['vectors']*r['functions'] for r in results)),indent=2)+'\n')


if __name__=='__main__':main()
