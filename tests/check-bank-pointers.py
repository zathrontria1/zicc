"""Store, convert and pass near and far pointers, then check which bytes they reach in working RAM."""
import os
import importlib.util,json,sys
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'tools'))
from mesen_core import Core,SnesConfig
ROOT=Path(__file__).resolve().parents[1]
spec=importlib.util.spec_from_file_location('compiler',ROOT/'tests/check-compiler.py')
c=importlib.util.module_from_spec(spec);spec.loader.exec_module(c)
c.OUT=Path(os.environ.get('ZICC_LOGS_DIR', 'logs')).resolve() / 'bank-pointer-check';c.OUT.mkdir(parents=True,exist_ok=True)
SOURCE=r"""
const unsigned words[3]={17,29,43};
unsigned data[12000];
struct Pair { unsigned a,b; };
struct Pair pair,other;
const struct Pair rompair={123,456};
typedef unsigned * __far Far;
unsigned matrix[2][3];
struct Row {unsigned values[3];};struct Row row,otherrow;
struct Forty {unsigned values[20];};struct Forty ramforty;
const struct Forty romforty={{11,22,33}};
int mutate_row(void){row.values[1]=99;return 1;}
unsigned read(const unsigned * __far p){return *p;}
unsigned * __far advance(unsigned * __far p,int n){return p+n;}
unsigned indexed_signed(const unsigned char * __far p,int n){return p[n];}
unsigned indexed_unsigned(const unsigned char * __far p,unsigned n){return p[n];}
int indexed_signed_byte(const signed char * __far p,int n){return p[n];}
unsigned indexed_long(const unsigned char * __far p,unsigned long n){return p[n];}
unsigned indexed_constant(const unsigned char * __far p){return p[1];}
unsigned indexed_word(const unsigned * __far p,unsigned i){return p[i];}
int compare_offset(const char * __far p,const char * __far q){return p==q+2 ? 1 : 0;}
unsigned updated_cursor(const unsigned char * __far p){
 unsigned x=*p++;
 return (x<<8)|*--p;
}
unsigned long short_sum(const unsigned * __far p){
 unsigned i;unsigned long sum=0x8000ffffUL;
 for(i=3;i>0;)sum=sum*2UL+p[--i];
 return sum+i;
}
unsigned byte_sentinel(const unsigned char * __far p,int reverse){
 unsigned sum=0;
 if(reverse){
  while(*p)sum=sum*2u+*p--;
 }else{
  while(*p)sum=sum*2u+*p++;
 }
 return sum+(unsigned)((unsigned long)p>>16);
}
unsigned long word_sentinel(const unsigned * __far p){
 unsigned long sum=0;
scan:
 if(*p!=0xbeefu){
  sum=sum*2UL+*p;
  ++p;
  goto scan;
 }
 return sum+(unsigned long)p;
}
unsigned long fixed_cursor_sum(const unsigned * __far source){
 const unsigned * __far p;
 unsigned long sum=0;
 p=source+3;
 do {sum=sum*2UL+*--p;} while(p!=source+1);
 return sum+(unsigned long)p;
}
unsigned indexed_calls;
const unsigned char * __far indexed_base(const unsigned char * __far p){indexed_calls++;return p;}
int indexed_offset(int n){indexed_calls+=10;return n;}
unsigned indexed_effects(const unsigned char * __far p,int n){return indexed_base(p)[indexed_offset(n)];}
unsigned indexed_nested(const unsigned char * __far p,const unsigned char * __far q,int n){return p[(int)q[n]];}
int main(void){
 unsigned old;int minus_one=-1;
 struct Row * __far rowptr=&row;
 unsigned *near=data+10000;
 unsigned * __far far=near;
 unsigned * __far zero=(unsigned *)0;
 unsigned * __far *slot=&far;
 Far * __far home=&far;
 unsigned (* __far rows)[3]=matrix;
 struct Pair * __far dest=&pair;
 const struct Pair * __far source=&rompair;
 if(sizeof(near)!=2||sizeof(far)!=4||sizeof(slot)!=2)return 1;
 if((unsigned long)far!=0x7e0500UL+10000UL*sizeof(data[0]))return 2;
 if((unsigned long)near!=0x0500UL+10000UL*sizeof(data[0]))return 35;
 if((unsigned long)(char * __far)minus_one!=0xffffffUL||(unsigned long)(char * __far)-1!=0xffffffUL)return 19;
 if(zero!=0||(unsigned long)(unsigned * __far)(unsigned *)0x1234!=0x7e1234UL)return 3;
 *far=301;(*far)++;if(*near!=302)return 4;
 if(read(words+1)!=29)return 5;
 if((unsigned *)far!=near)return 6;
 if(advance(far,-2)!=far-2)return 7;
 if((advance(far,5)-far)!=5L)return 8;
 *slot=near;if(read(*slot)!=302)return 9;
 *dest=*source;if(pair.a!=123||pair.b!=456)return 10;
 other=pair;if(other.b!=456)return 11;
 if((unsigned long)((char * __far)0x7effffUL+1)!=0x7f0000UL)return 12;
 *home=near;if(**home!=302||sizeof(home)!=4)return 13;
 rows[1][2]=77;if(matrix[1][2]!=77)return 14;
 *(unsigned * __far)0x7effffUL=0x1234;
 if(*(unsigned char * __far)0x7effffUL!=0x34||*(unsigned char * __far)0x7f0000UL!=0x12)return 15;
 otherrow.values[1]=41;
 if((*rowptr=otherrow).values[mutate_row()]!=41||row.values[1]!=99)return 16;
 ramforty=romforty;if(ramforty.values[2]!=33||ramforty.values[19]!=0)return 17;
 *far=read(words+2);*far+=read(words);old=(*far)++;
 if(old!=60||++(*far)!=62||*near!=62)return 18;
 *(unsigned char * __far)0x7effffUL=0xe1;
 *(unsigned char * __far)0x7f0000UL=0x80;
 *(unsigned char * __far)0x7e9000UL=0x34;
 *(unsigned char * __far)0x7f8fffUL=0x55;
 *(unsigned char * __far)0x7f3fffUL=0x66;
 *(unsigned char * __far)0x7f9000UL=0x77;
 *(unsigned char * __far)0x7e9080UL=0x4c;
 if(indexed_signed((unsigned char * __far)0x7f0000UL,-1)!=0xe1||
    indexed_signed((unsigned char * __far)0x7effffUL,1)!=0x80)return 20;
 if(indexed_signed((unsigned char * __far)0x7f1000UL,-32768)!=0x34||
    indexed_signed((unsigned char * __far)0x7f1000UL,32767)!=0x55)return 21;
 if(indexed_unsigned((unsigned char * __far)0x7e4000UL,65535U)!=0x66||
    indexed_signed_byte((signed char * __far)0x7effffUL,1)!=-128)return 22;
 if(indexed_long((unsigned char * __far)0x7e9000UL,65536UL)!=0x77||
    indexed_constant((unsigned char * __far)0x7effffUL)!=0x80)return 23;
 if(indexed_effects((unsigned char * __far)0x7f0000UL,-1)!=0xe1||indexed_calls!=11)return 24;
 if(indexed_nested((unsigned char * __far)0x7e9000UL,(unsigned char * __far)0x7efff0UL,16)!=0x4c)return 25;
 if(indexed_signed((unsigned char * __far)0x004000UL,-32768)!=*(unsigned char * __far)0xffc000UL)return 26;
 *(unsigned char * __far)0x000080UL=0xab;
 if(indexed_unsigned((unsigned char * __far)0xffff00UL,0x180U)!=0xab)return 27;
 *(unsigned * __far)0x7efffeUL=0x1234;
 *(unsigned * __far)0x7f0000UL=0xabcd;
 *(unsigned * __far)0x7f0002UL=0x6000;
 if(indexed_word((unsigned * __far)0x7e0000UL,0x8000u)!=0xabcd||
    indexed_word((unsigned * __far)0x7efffeUL,1)!=0xabcd)return 28;
 if(!compare_offset((char * __far)0x7f0001UL,(char * __far)0x7effffUL)||
    compare_offset((char * __far)0x7e0001UL,(char * __far)0x7effffUL)||
    !compare_offset((char * __far)1UL,(char * __far)0xffffffUL))return 29;
 if(updated_cursor((unsigned char * __far)0x7effffUL)!=0x1212)return 30;
 if(short_sum((unsigned * __far)0x7efffeUL)!=0x000ae9c6UL)return 31;
 *(unsigned char * __far)0x7efffeUL=0;
 *(unsigned char * __far)0x7effffUL=7;
 *(unsigned char * __far)0x7f0000UL=3;
 *(unsigned char * __far)0x7f0001UL=0;
 if(byte_sentinel((unsigned char * __far)0x7effffUL,0)!=17+0x7f||
    byte_sentinel((unsigned char * __far)0x7f0000UL,1)!=13+0x7e||
    byte_sentinel((unsigned char * __far)0x7f0001UL,0)!=0x7f)return 32;
 *(unsigned * __far)0x7efffeUL=0x00ef;
 *(unsigned * __far)0x7f0000UL=0xbe00;
 *(unsigned * __far)0x7f0002UL=0xbeef;
 if(word_sentinel((unsigned * __far)0x7efffeUL)!=0x7fbfe0UL||
    word_sentinel((unsigned * __far)0x7f0002UL)!=0x7f0002UL)return 33;
 if(fixed_cursor_sum((unsigned * __far)0x7efffeUL)!=0x813bdeUL)return 34;
 return 0;
}
"""
if len(sys.argv)==1:
 for region in ('ntsc','pal'):
  result=c.run([sys.executable,__file__,region],timeout=45)
  print(result.stdout)
 sys.exit(0)
_,rom,labels=c.compile_case('pointers',SOURCE,extra_objects=[ROOT/'build/arithmetic.o',ROOT/'build/integers.o',ROOT/'build/ieee_engine.o'])
assembly=rom.with_suffix('.s').read_text()
for name in ('indexed_signed','indexed_unsigned','indexed_signed_byte','indexed_effects','indexed_nested'):
 body=assembly.split('_'+name+':\n',1)[1].split('__size_'+name,1)[0]
 assert '; indexed far byte load:' in body,name
for name in ('indexed_long','indexed_constant'):
 body=assembly.split('_'+name+':\n',1)[1].split('__size_'+name,1)[0]
 assert '; indexed far byte load:' not in body,name
print(c.emulate(rom,labels,0))
results={}
for region in (sys.argv[1],):
 home=c.OUT/region;home.mkdir(exist_ok=True)
 script=(c.OUT/'pointers.lua').read_text().replace("print('PASS')","emu.log('PASS')").replace('emu.stop(bad and 1 or 0)','emu.breakExecution()')
 core=Core(home)
 try:
  config=SnesConfig();config.Region=1 if region=='ntsc' else 2
  config.Port1.Type=1;config.DisableFrameSkipping=True;config.RamPowerOnState=1
  config.GsuClockSpeed=100;config.BsxCustomDate=-1
  for i in range(8):config.ChannelVolumes[i]=100
  core.bind('SetSnesConfig',None,SnesConfig)(config)
  core.load(rom,home/'check.lua',script);core.start();core.wait_for('PASS',20)
  results[region]='PASS';print('PASS bank pointers '+region)
 finally:
  core.close_with_log(home/'check.log')
diagnostics=(
 ('implicit','int main(void){int * __far f;int *n;n=f;return 0;}','implicit far-to-near pointer conversion (use __far)'),
 ('rom','int main(void){char *p;p="rom";return 0;}','implicit far-to-near pointer conversion (use __far)'),
 ('constant','int main(void){int *p=(int *)0x804200UL;return 0;}','not representable'),
 ('bank_zero','int main(void){int *p=(int *)(int * __far)0x4200UL;return 0;}','not representable'),
 ('reserved_zero','int main(void){int *p=(int *)(int * __far)0x7e0000UL;return 0;}','not representable'),
 ('float_pointer','int main(void){char * __far p=(char * __far)1.0f;return 0;}','pointer/float'),
 ('identity','void f(int *p);void f(int * __far p){}','conflicting parameter type: near/far pointer mismatch'),
 ('rom_table_init','const unsigned char rom_table[4]={1,2,3,4};const unsigned char *table[1]={rom_table};','incompatible pointer initializer: far pointer cannot initialize near pointer (declare target with __far)'),
 ('rom_near_param','const unsigned char rom_table[4]={1,2,3,4};void f(const unsigned char *p);void g(void){f(rom_table);}','incompatible argument 1 for \'f\': far pointer passed to near pointer parameter (declare parameter with __far)'),
 ('nested_init_far','const char * __far table[1]={"a"};const char ** __far p=table;','incompatible pointer initializer: nested near/far pointer mismatch'),
 ('nested_arg_far','int *p;void take(int * __far *q);void g(void){take(&p);}','incompatible argument 1 for \'take\': nested near/far pointer mismatch'),
 ('decl_far_conflict','extern const char *p;const char * __far p;','conflicting declaration \'p\': near/far pointer mismatch'),
 ('return_far_conflict','const char *f(void);const char * __far f(void){return 0;}','conflicting declaration \'f\': near/far pointer mismatch'),
 ('rom_array_arg','const unsigned char rom_table[4]={1,2,3,4};extern void sink(const unsigned char * __far p);void a(void){sink((unsigned char *)rom_table);}','ROM address is not representable as a near pointer'),
 ('rom_array_return','const unsigned char rom_table[4]={1,2,3,4};unsigned char *f(void){return (unsigned char *)rom_table;}','ROM address is not representable as a near pointer'),
 ('rom_array_offset','const unsigned char rom_table[4]={1,2,3,4};unsigned char *f(void){return (unsigned char *)(rom_table+2);}','ROM address is not representable as a near pointer'),
 ('rom_array_elem_addr','const unsigned char rom_table[4]={1,2,3,4};unsigned char *f(void){return (unsigned char *)&rom_table[2];}','ROM address is not representable as a near pointer'),
 ('rom_2d_row','const unsigned char rom_2d[2][4]={{1,2,3,4},{5,6,7,8}};unsigned char *f(void){return (unsigned char *)rom_2d[1];}','ROM address is not representable as a near pointer'),
 ('rom_member_array','struct S{unsigned char a[4];};const struct S rs={{1,2,3,4}};unsigned char *f(void){return (unsigned char *)rs.a;}','ROM address is not representable as a near pointer'),
 ('rom_member_addr','struct S{int x;};const struct S rs={1};int *f(void){return (int *)&rs.x;}','ROM address is not representable as a near pointer'),
 ('rom_cast_chain','const unsigned char rom_table[4]={1,2,3,4};unsigned char *f(void){return (unsigned char *)(const void * __far)rom_table;}','ROM address is not representable as a near pointer'),
 ('rom_comma','const unsigned char rom_table[4]={1,2,3,4};unsigned char *f(void){return (unsigned char *)(0,rom_table);}','ROM address is not representable as a near pointer'),
 ('rom_choose','const unsigned char rom_table[4]={1,2,3,4};unsigned char near_buf[4];unsigned char *f(int c){return (unsigned char *)(c?rom_table:near_buf);}','ROM address is not representable as a near pointer'),
 ('rom_string_offset','char *f(void){return (char *)("abc"+1);}','ROM address is not representable as a near pointer'),
 ('rom_local_static','unsigned char *f(void){static const unsigned char t[4]={1,2,3,4};return (unsigned char *)t;}','ROM address is not representable as a near pointer'),
 ('rom_extern_array','extern const unsigned char t[4];unsigned char *f(void){return (unsigned char *)t;}','ROM address is not representable as a near pointer'))
for name,source,message in diagnostics:
 path=c.OUT/(name+'.c');path.write_text(source)
 result=c.run([ROOT/'build/zicc.exe',path,'-o',path.with_suffix('.s')],expected=1)
 assert message in result.stderr,(name,result.stderr)
non_far_path=c.OUT/'non_far_mismatch.c'
non_far_path.write_text('unsigned a;char *p=&a;')
non_far_result=c.run([ROOT/'build/zicc.exe',non_far_path,'-o',non_far_path.with_suffix('.s')],expected=1)
assert 'incompatible pointer initializer' in non_far_result.stderr,non_far_result.stderr
assert '__far' not in non_far_result.stderr and 'near/far' not in non_far_result.stderr,non_far_result.stderr
for name,source in (
 ('rom_ptr_value','unsigned char near_buf[4];unsigned char * __far const rom_ptr=near_buf;unsigned char *f(void){return (unsigned char *)rom_ptr;}'),
 ('rom_ptr_array_elem','unsigned char near_buf[4];unsigned char * __far const rom_ptrs[1]={near_buf};unsigned char *g(void){return (unsigned char *)rom_ptrs[0];}'),
 ('rom_ptr_member','unsigned char near_buf[4];struct P{unsigned char * __far p;};const struct P rp={near_buf};unsigned char *h(void){return (unsigned char *)rp.p;}'),
 ('rom_choose_false','const unsigned char rom_table[4]={1,2,3,4};unsigned char near_buf[4];unsigned char *f(void){return (unsigned char *)(0?rom_table:near_buf);}'),
 ('rom_diff_offset','const unsigned char rom_table[4]={1,2,3,4};unsigned char near_buf[4];unsigned char *f(void){return (unsigned char *)((unsigned char * __far)near_buf+(rom_table-rom_table));}')):
 path=c.OUT/(name+'.c');path.write_text(source)
 c.run([ROOT/'build/zicc.exe',path,'-o',path.with_suffix('.s')],expected=0)
(c.OUT/(sys.argv[1]+'-results.json')).write_text(json.dumps(dict(regions=results,diagnostics=len(diagnostics)),indent=2)+'\n')
