"""Check compound assignments at each integer width, including carries, shared addresses and function calls."""
import os
import argparse,importlib.util,json,subprocess,hashlib,re
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1];OUT=Path(os.environ.get('ZICC_LOGS_DIR', 'logs')).resolve() / 'scalar-home-check'
spec=importlib.util.spec_from_file_location('support',ROOT/'tests/check-compiler.py');support=importlib.util.module_from_spec(spec);spec.loader.exec_module(support)
CASES={}
for bits,ctype,suffix in [(16,'unsigned short','U'),(32,'unsigned long','UL')]:
 mask=(1<<bits)-1;body=[]
 for a,b in [(0,0),(mask,1),(0,1),(0xffff,1),(0x8000,0x8001),(0x1234,0x4321)]:
  for op,val in [('+',(a+b)&mask),('-',(a-b)&mask),('&',a&b),('|',a|b),('^',a^b)]:
   body.append(f'x={a}{suffix};y={b}{suffix};x{op}=y;if(x!={val}{suffix})return 1;')
   body.append(f'x={a}{suffix};if((x{op}=y)!={val}{suffix}||x!={val}{suffix})return 2;')
 CASES['width'+str(bits)]=f'{ctype} global;int main(void){{{ctype} x,y;'+''.join(body)+f'global={mask}{suffix};global+=1{suffix};if(global)return 3;return 0;}}'
CASES['aliases']='''unsigned long global;unsigned long change(unsigned long *p){*p=99UL;return 2UL;}
int main(void){unsigned long local=5UL;global=5UL;local+=change(&local);
if(local!=101UL)return 1;
global+=change(&global);
if(global!=101UL)return 2;
local=0x1234ffffUL;local+=local;if(local!=0x2469fffeUL)return 3;
local+=*(unsigned long *)&local;if(local!=0x48d3fffcUL)return 4;return 0;}
'''
CASES['mixed']='''short g;float f;unsigned char head,middle,tail;
unsigned long recurse(short n){unsigned long x=0xffffUL;if(n)x+=recurse((short)(n-1));return x;}
int main(void){signed char b=-128;unsigned char u=255;short x=-3;unsigned long wide=65537UL;short a[3];short *p=a;int i;
b+=1;u+=2;if(b!=-127||u!=1)return 1;head=77;middle=255;tail=88;middle+=2;if(middle!=1||head!=77||tail!=88)return 8;if((middle+=254)!=255||tail!=88)return 9;x+=wide;if(x!=-2)return 2;
f=1.5f;f+=2.0f;if(f!=3.5f)return 3;g=12;g*=3;g/=7;g%=4;g<<=2;g>>=1;if(g!=2)return 4;
p+=2;if(p!=a+2)return 5;
wide=0;for(i=0;i<3;wide+=1UL)++i;if(wide!=3UL)return 6;
if(recurse(5)!=393210UL)return 7;return 0;}
'''
CASES['shape']='''unsigned long g;
void discarded(unsigned long r){unsigned long x=0xffffUL;x+=r;g=x;}
unsigned long used(unsigned long r){unsigned long x=0xffffUL;return x+=r;}
int main(void){discarded(1UL);if(g!=0x10000UL||used(1UL)!=0x10000UL)return 1;return 0;}
'''

# Whole-function guarded updates: arbitrary names/offsets, both addition orders,
# and patterns which must keep ordinary lowering. Values straddle zero and the
# signed-word limits; the last two pairs also preserve existing target wrapping
# behavior when ADC's V is set, rather than mistaking V for the sign of next
GUARDED_PAIRS=[(-32768,0),(-32768,32767),(-32767,32767),(-1,1),(0,0),(0,-1),
               (0,32767),(1,-2),(1,32766),(32767,-32768),(32767,-32767),
               (32767,0),(200,-2),(-200,201),(32767,1),(-32768,-1)]
GUARDED_SELECTED={}
for variant in ('basic','commuted','dot','nested','unsigned_delta','unsigned_field',
                'narrow_cast','changed_field','guard_le','extra_call','escaped_temp',
                'extra_local','subtract','different_return'):
 declaration='struct Cell {unsigned short head;short value;unsigned short tail;};'
 field='p->value';cell='cell.value';destination=field
 delta_type='short';operator='+';transform=lambda v:v
 before='';prefix='';guard='<';failure=0;extra=''
 if variant=='commuted':expression='delta+p->value'
 else:expression='p->value+delta'
 if variant=='dot':field='(*p).value';expression='(*p).value+delta'
 if variant=='nested':
  declaration='struct Inner {short value;};struct Cell {unsigned long head;struct Inner inner;unsigned short tail;};'
  field='p->inner.value';cell='cell.inner.value';expression=field+'+delta'
 if variant=='unsigned_delta':delta_type='unsigned short'
 if variant=='unsigned_field':declaration=declaration.replace('short value','unsigned short value')
 if variant=='narrow_cast':expression='(signed char)(p->value+delta)';transform=lambda v:((v+128)&255)-128
 if variant=='changed_field':destination='p->tail'
 elif variant in ('dot','nested'):destination=field
 if variant=='guard_le':guard='<='
 if variant=='extra_call':prefix='int calls;void observe(void){calls++;}';before='observe();'
 if variant=='escaped_temp':prefix='void bump(short *p){*p=(short)(*p+1);}';before='bump(&next);';transform=lambda v:((v+1+32768)&65535)-32768
 if variant=='extra_local':extra='short unused;'
 if variant=='subtract':expression='p->value-delta';operator='-'
 if variant=='different_return':failure=2
 function=f'int update(struct Cell *p,{delta_type} delta){{{extra}short next=(short)({expression});{before}if(next{guard}0)return {failure};{destination}=next;return 1;}}'
 checks=[]
 for a,b in GUARDED_PAIRS:
  value=((a+(b if operator=='+' else -b)+32768)&65535)-32768;value=transform(value)
  accepted=value>0 if guard=='<=' else value>=0
  stored=value if accepted and variant!='changed_field' else a
  tail=value if accepted and variant=='changed_field' else 0xbeef
  if variant=='extra_call':checks.append('calls=0;')
  checks.append(f'cell.head=0xCAFEU;cell.tail=0xBEEFU;{cell}=(short)({a});if(update(&cell,(short)({b}))!={1 if accepted else failure})return 1;if((short){cell}!=(short)({stored})||cell.head!=0xCAFEU||cell.tail!=(unsigned short)({tail}))return 2;')
  if variant=='extra_call':checks.append('if(calls!=1)return 3;')
 name='guarded_'+variant
 CASES[name]=declaration+prefix+function+'int main(void){struct Cell cell;'+''.join(checks)+'return 0;}'
 GUARDED_SELECTED[name]=variant in ('basic','commuted','dot','nested')
def main():
 parser=argparse.ArgumentParser();parser.add_argument('--baseline',type=Path);args=parser.parse_args()
 OUT.mkdir(parents=True, exist_ok=True);support.OUT=OUT;result={};original=support.run
 extra=[ROOT/'build/arithmetic.o',ROOT/'build/integers.o',ROOT/'build/ieee_engine.o']
 for name,source in CASES.items():
  cfile,rom,labels=support.compile_case(name,source,extra_objects=extra)
  exe=OUT/(name+'-host.exe');support.run([ROOT/'tools/msvc.cmd','/nologo','/std:c17','/O2','/Fo'+str(OUT/(name+'-host.obj')),'/Fe'+str(exe),cfile]);assert subprocess.run([str(exe)]).returncode==0,name
  result[name]=support.emulate(rom,labels,0)
  if name in GUARDED_SELECTED:
   assembly=(OUT/(name+'.s')).read_text();part=assembly.split('_update:\n',1)[1].split('__size_update',1)[0]
   if GUARDED_SELECTED[name]:
    offset=4 if name=='guarded_nested' else 2
    ops=[line for line in part.splitlines() if line.startswith('    ')]
    add_idx=ops.index(f'    adc a:${offset:04X},x')
    branch_op=ops[add_idx+1]
    assert branch_op.startswith('    bmi ') or branch_op.startswith('    bpl '),part
    assert f'    sta a:${offset:04X},x' in ops[add_idx+2:],part
    assert '    phy\n' not in part and '    tsc\n' not in part and '__arith_' not in part,part
  def baseline(cmd,*a,**kw):
   if Path(cmd[0]).name=='zicc.exe':cmd=[args.baseline,*cmd[1:]]
   return original(cmd,*a,**kw)
  if args.baseline:
   try:
    support.run=baseline
    _,br,bl=support.compile_case(name+'-baseline',source,extra_objects=extra);support.emulate(br,bl,0)
   finally:support.run=original
 _,rom,labels=support.compile_case('mixed-conversion','int main(void){long x=1L;x+=1.0f;return x==2L?0:1;}',extra_objects=[*extra,ROOT/'build/libc.a'])
 result['mixed-conversion']=support.emulate(rom,labels,0)
 assembly=(OUT/'shape.s').read_text();part=assembly.split('_discarded:\n')[1].split('__size_discarded')[0]
 # Frame homes may be Y-relative or, without a Y frame, stack-relative
 home=r'(?:a:\$[0-9A-F]+,y|\d+,s|z:__arith_lhs(?:\+\d+)?)'
 # Either half's constant can be forwarded while preserving the carry between ADCs
 low=r'(?:'+home+r'|#\$[0-9A-F]{4})'
 high=r'(?:'+home+r'|#\$0000)'
 assert re.search(r'adc '+low+r'\n    sta '+home+r'\n    txa\n    adc '+high,part),part
 (OUT/'results.json').write_text(json.dumps(dict(cases=result,baseline_sha256=hashlib.sha256(args.baseline.read_bytes()).hexdigest() if args.baseline else None,compiler_sha256=hashlib.sha256((ROOT/'build/zicc.exe').read_bytes()).hexdigest()),indent=2))
 print(f'PASS: {len(CASES)} MSVC/Mesen cases; optional baseline; scalar homes and {len(GUARDED_SELECTED)} guarded-update shape/boundary/fallback cases')
if __name__=='__main__':main()
