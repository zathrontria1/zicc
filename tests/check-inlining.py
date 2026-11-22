"""Same-TU policy, sequencing, storage, control-flow and linkage checks."""
import os
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import subprocess
import sys

ROOT=Path(__file__).resolve().parents[1]
OUT=Path(os.environ.get('ZICC_LOGS_DIR', 'logs')).resolve() / 'inlining-check'
spec=importlib.util.spec_from_file_location('body',ROOT/'tests/check-body-codegen.py')
b=importlib.util.module_from_spec(spec);spec.loader.exec_module(b)
c=b.c

KERNEL=r'''
#ifdef __ZICC__
#define FORCE __forceinline
#define NEVER __attribute__((noinline))
#define HINT inline
#define GCCFORCE __attribute__((always_inline))
#define ALIASNEVER __noinline
#else
#define FORCE
#define NEVER
#define HINT __inline
#define GCCFORCE
#define ALIASNEVER
#endif
volatile int events;
int plain(int a,int b){return a+b;}
static HINT int hinted(int x){x+=1;x+=2;x+=3;x+=4;x+=5;x+=6;x+=7;x+=8;x+=9;return x;}
static int larger(int x){x+=1;x+=2;x+=3;x+=4;x+=5;x+=6;x+=7;x+=8;x+=9;return x;}
NEVER int blocked(int x);
int blocked(int x){return x+7;}
NEVER int next(void){events++;return events;}
unsigned checked_byte_total;
void guarded_byte_update(unsigned char a,unsigned char b){
    if(a!=b&&b!=(unsigned char)(a+1))next();
    else if(a==b&&(unsigned char)(a+2)!=0)next();
    checked_byte_total+=a;
}
NEVER unsigned loop_guarded_update(unsigned char start,unsigned times){
    unsigned i;
    checked_byte_total=0;
    for(i=0;i<times;++i){
        unsigned char a=(unsigned char)(start+i);
        guarded_byte_update(a,(unsigned char)(a+(i!=1)));
    }
    return checked_byte_total;
}
FORCE int pair(int a,int z){return a*10+z;}
FORCE int tick(int n){events++;return n;}
FORCE int early(int n){int i,j,total=0;if(n<0)return -7;
 for(i=0;i<n;i++){if(i==2)continue;for(j=0;j<3;j++){if(j==1)break;total++;if(total==5)return total+10;}}
 return total;}
FORCE int local_array(int n){int a[3];a[0]=n;a[1]=n+1;a[2]=n+2;return a[0]+a[1]+a[2];}
FORCE unsigned long wide(unsigned long n,unsigned k){return (n<<k)+3ul;}
FORCE int aliased(int *p,int n){*p+=n;return *p;}
FORCE int via(int *p){return (*p)++;}
FORCE void bump(int *p){(*p)++;if(*p==3)return;(*p)++;}
FORCE int return_step(int n){int i;for(i=0;i<4;events++){if(i==n)return events;i++;}return 19;}
FORCE int far_read(const char * __far p){return p[1];}
int left_array[2],right_array[2],*destination_pointer;
FORCE int change_destination(void){destination_pointer=right_array;return 42;}
FORCE unsigned long change_wide(unsigned long *p){*p=99ul;return 2ul;}
struct Copy{int x,y;};struct Copy copy_a,copy_b,copy_c,*copy_target;
union Overlay {struct Copy low;struct {int skip;struct Copy value;} high;} overlay;
void copy_parameter(struct Copy value){copy_a=value;}
void copy_into_overlay(struct Copy value){overlay.high.value=value;}
NEVER void forward_parameter(int seed){struct Copy local={seed,seed+11};copy_parameter(local);}
NEVER void copy_overlap(void){copy_into_overlay(overlay.low);}
struct Projection {unsigned char tag,values[32];};
int project(struct Projection a,struct Projection b){
    if(a.tag!=b.tag)return -7;
    return a.values[0]+b.values[31];
}
int project_mutating(struct Projection a,struct Projection b){
    a.values[0]+=3;
    return a.values[0]+b.values[0];
}
int project_identity(struct Projection a,struct Projection b){return a.values==b.values;}
NEVER int project_same(unsigned char first,unsigned char last){
    struct Projection a={0};
    a.values[0]=first;a.values[31]=last;
    return project(a,a);
}
NEVER int project_distinct(unsigned char first,unsigned char last,int different){
    struct Projection a={0},b={0};
    a.values[0]=first;b.values[31]=last;b.tag=different;
    return project(a,b);
}
NEVER int project_copy_observed(unsigned char first){
    struct Projection a={0};
    a.values[0]=first;
    return project_mutating(a,a)+project_identity(a,a)+a.values[0];
}
unsigned projected_words[2];
volatile unsigned observed_word;
int fixed_load(void){
    unsigned word,count;
    word=projected_words[1];
    count=word>>8;
    return count;
}
int changed_after_load(unsigned changed){
    unsigned word;
    word=projected_words[1];
    projected_words[1]=changed;
    return word>>8;
}
int observe_load(void){unsigned word;word=observed_word;return word>>8;}
NEVER int check_fixed_load(void){return fixed_load()==0x93;}
NEVER int check_changed_load(void){return changed_after_load(0xcd00)==0x93;}
NEVER int check_observe_load(void){return observe_load()==0xab;}
struct InlineField {unsigned preserved:12;unsigned updated:4;};
struct InlineField inline_field;
unsigned old_field;
int field_guard(unsigned value){
    old_field=inline_field.updated;
    inline_field.updated=value;
    if(value)return 1;
    return 2;
}
NEVER int fixed_field_guard(void){return field_guard(3U);}
NEVER int runtime_field_guard(unsigned value){return field_guard(value);}
struct LocalFields {unsigned low:1;unsigned middle:2;unsigned high:3;};
unsigned local_field_result;
NEVER void record_local_field(unsigned value){local_field_result=value;}
void local_field_update(int a,int b,int c){
    struct LocalFields fields={a,b,c},*ptr=&fields;
    ptr->high+=fields.middle-fields.low;
    record_local_field(ptr->high);
}
NEVER void fixed_local_fields(void){local_field_update(1,2,3);}
NEVER void runtime_local_fields(int value){local_field_update(1,2,value);}
int indexed_inline_slots[4];
int indexed_inline_pos,indexed_inline_value;
int inline_store_value(int value){return indexed_inline_value+=value;}
NEVER int check_inline_index(int value){
    indexed_inline_pos=1;
    indexed_inline_value=4;
    indexed_inline_slots[0]=8;
    indexed_inline_slots[1]=9;
    indexed_inline_slots[indexed_inline_pos++]=inline_store_value(value);
    return indexed_inline_pos==2&&indexed_inline_value==4+value&&
        indexed_inline_slots[0]==8&&indexed_inline_slots[1]==4+value;
}
int unused_guard,discarded_guard_store;
volatile int volatile_guard;
volatile int literal_guard_state;
int literal_guard(void){
    if(++literal_guard_state>1)return -3;
    return 7;
}
NEVER int conditional_literal_guard(int enabled){return enabled?literal_guard():19;}
FORCE int discarded_pure_guard(void){
    discarded_guard_store=1;
    if(unused_guard<=0)return 1;
    else return 0;
}
FORCE int discarded_effectful_guard(void){
    if(volatile_guard&&next())return 1;
    else return 0;
}
NEVER int check_discarded_guards(int value){
    discarded_guard_store=0;events=0;volatile_guard=value;
    discarded_pure_guard();
    discarded_effectful_guard();
    return discarded_guard_store==1&&events==(value!=0);
}
NEVER int check_field_guard(int n){
    fixed_local_fields();
    if(local_field_result!=4)return 0;
    runtime_local_fields(n);
    if(local_field_result!=n+1)return 0;
    inline_field.preserved=0xaceU;inline_field.updated=12;
    if(fixed_field_guard()!=1||old_field!=12||inline_field.updated!=3||
       inline_field.preserved!=0xaceU)return 0;
    return runtime_field_guard(n)==(n?1:2)&&old_field==3&&
        inline_field.updated==n&&inline_field.preserved==0xaceU;
}
unsigned char wrapper_log[8];
unsigned wrapper_count;
NEVER void record_wrapper_pair(unsigned a,unsigned b){
    wrapper_log[wrapper_count++]=a;
    wrapper_log[wrapper_count++]=b;
}
int two_calls(int value){
    unsigned char a=value,b=value+1;
    record_wrapper_pair(a,b);
    a^=b;b^=a;a^=b;
    record_wrapper_pair(a,b);
    return 0;
}
NEVER int check_loop_wrapper(int start,unsigned times){
    unsigned i;
    wrapper_count=0;
    for(i=0;i<times;++i)two_calls(start+i);
    return wrapper_count==8&&wrapper_log[0]==255&&wrapper_log[1]==0&&
        wrapper_log[2]==0&&wrapper_log[3]==255&&wrapper_log[4]==0&&
        wrapper_log[5]==1&&wrapper_log[6]==1&&wrapper_log[7]==0;
}
FORCE struct Copy *copy_destination(void){events++;return copy_target;}
FORCE struct Copy *copy_source(void){events++;copy_target=&copy_b;return &copy_a;}
FORCE int copy_value(struct Copy *a,struct Copy *b){return (*a=*b).y;}
FORCE int local_struct(int n){struct Copy a,b;a.x=n;a.y=n+1;b=a;return b.x+b.y;}
FORCE int recursive_leaf(int x){return x+1;}
GCCFORCE int forced_attribute(int x){return x+9;}
ALIASNEVER int blocked_alias(int x){return x+11;}
NEVER int pressure_case(int x){volatile int a=x,b=x,c=x,d=x,e=x,f=x,g=x,h=x,i=x,j=x,k=x,l=x,m=x,n=x,o=x,p=x;
 return plain(x,3)+a+b+c+d+e+f+g+h+i+j+k+l+m+n+o+p;}
NEVER int recursive(int n){if(n==0)return 1;return recursive(n-1)+recursive_leaf(n);}
NEVER int automatic_case(int x){return plain(x,3);}
NEVER int hinted_case(int x){return hinted(x);}
static HINT int shared_leaf(int x){return x+6;}
static int retained_wide_caller(long long x){return shared_leaf((int)x);}
NEVER int shared_leaf_case(int x){return shared_leaf(x);}
NEVER int larger_case(int x){return larger(x);}
NEVER int blocked_case(int x){return blocked(x);}
NEVER void action_true(void){events=17;}
NEVER void action_false(void){events=-19;}
void choose_action(int value,int expected){
 if(value==expected)action_true();else action_false();}
NEVER void check_action(int value){choose_action(value,5);}
int guard_state;
volatile int guard_checks;
int next_guard(void){++guard_checks;guard_state=!guard_state;return guard_state;}
void guarded_loop(int enabled,int after){
 if(enabled){action_true();action_true();}
 while(next_guard()){
  if(enabled){enabled=after;break;}
 }
 if(enabled)action_false();
}
NEVER void fixed_guard_loop(void){guarded_loop(0,1);}
NEVER void runtime_guard_loop(int enabled){guarded_loop(enabled,1);}
int read_selected_word(const long *raw){
 const int *word=(const int *)raw;
 return word[3];
}
int selected_word(const int *src){
 const int *selected;
 int fallback[32];
 if(src!=0) selected=src;
 else {fallback[3]=events;selected=fallback;}
 return read_selected_word((const long *)selected);
}
NEVER int fixed_null_guard(void){return selected_word((const int *)(void *)0);}
volatile long observed_long;
FORCE void save_long_low(long value){events=(int)value;}
FORCE void save_long_full(long value){observed_long=value;}
NEVER void call_long_low(int value){save_long_low((long)(value+events));}
NEVER void call_long_full(int value){save_long_full((long)(value+events));}
int early_auto(int x){if(x<0)return 0;events=x;return 1;}
NEVER int early_auto_case(int x){return early_auto(x);}
int later(int);
NEVER int forward_case(int x){return later(x);}
int later(int x){return x+13;}
FORCE unsigned char narrow(unsigned char x){x++;return x;}
static int state;
static FORCE unsigned char matches_state(int value){if(value==state)return 1;return 0;}
NEVER int state_guard(int value){if(matches_state(value)&&next())return 1;return 0;}
unsigned short state_left,state_right;
static unsigned short read_left(void){return state_left;}
static unsigned short read_right(void){return state_right;}
static char same_state(void){if(read_left()==read_right())return 1;else return 0;}
NEVER int state_branch(void){if(!same_state()&&next())return 7;return 2;}
int bins[4]={2,3,5,7},totals[2];
int add_elements(int *a,int *b){return *a+*b;}
int selected_bin;
int sum_from(int start){
 int i,j=start,k=selected_bin;
 totals[k]=bins[j];++j;
 for(i=j;i<4;++i){totals[k]=add_elements(&totals[k],&bins[j]);++j;}
 return totals[k];}
NEVER int fixed_sum(void){return sum_from(0);}
NEVER int runtime_sum(int start){return sum_from(start);}
NEVER int indexed_sum(int start,int end,int k){
 int j;for(j=start;j<end;++j)totals[k]=add_elements(&totals[k],&bins[j]);
 return totals[k];}
NEVER int indexed_step(int j){int sum=add_elements(&bins[j++],&bins[0]);return sum+j;}
NEVER int indexed_volatile(volatile int j){return add_elements(&bins[j],&bins[0]);}
int public_arith_leaf(int a,int b){return ((a^b)+5)-(a>>2);}
NEVER int pressure_loop_leaf(int n){
 int i,a=1,b=2,c=3,d=4,e=5,f=6,g=7,h=8,k=9,m=10,p=11,q=12,acc=0;
 for(i=0;i<n;++i){acc+=public_arith_leaf(a+i,b-i);a+=3;b+=5;c^=a;d^=b;e+=c;f+=d;g^=e;h+=f;k^=g;m+=h;p^=k;q+=m;}
 return acc+c+d+e+f+g+h+k+m+p+q;}
static signed char scale_signed_leaf(int x,int z){return (signed char)((x+z*4)>>4);}
static int scale_signed_int_leaf(int x,int z){return (x+z*4)>>4;}
static int take_schar_leaf(signed char x,int k){return (int)x*3+k;}
unsigned char leaf_bytes[4];
NEVER int signed_leaf_cases(const int *in){
 int i,sum=0;
 for(i=0;i<4;++i){
  int s=(int)scale_signed_leaf(in[i],i-2);
  leaf_bytes[i]=(unsigned char)(124+scale_signed_int_leaf(in[i],i-2));
  sum+=s+take_schar_leaf(in[i],i);
 }
 return sum;}
NEVER unsigned char signed_byte_store_leaf(const int *in){
 int i;
 for(i=0;i<4;++i)leaf_bytes[i]=(unsigned char)(124+scale_signed_int_leaf(in[i],i-2));
 return leaf_bytes[0];}
static int leaf_once(int a){return (a<<1)+3;}
static int leaf_twice(int a){return a*a+a;}
static int leaf_pair(int a,int b){return (a<<2)-b;}
NEVER int effectful_leaf_cases(volatile int *vp,int x,int y){
 int r=0;
 r+=leaf_once(next());
 r+=leaf_once(x++);
 r+=leaf_twice(next());
 r+=leaf_twice(*vp);
 r+=leaf_pair(x++,y++);
 leaf_bytes[x&3]=(unsigned char)leaf_once(y++);
 return r+x+y+leaf_bytes[0]+leaf_bytes[1]+leaf_bytes[2]+leaf_bytes[3];}
struct Transfer;
struct TransferLink {struct TransferLink *next;struct Transfer *owner;};
struct Transfer {struct TransferLink *head;long low,high;};
struct Transfer left_transfer,right_transfer;
struct TransferLink transfer_links[2];
void transfer_fields(struct Transfer *to,struct Transfer *from){
 if(!to->head){
  struct TransferLink *link=to->head=from->head;
  from->head=0;
  for(;link;link=link->next)link->owner=to;
 }
 if(to->low==-1){
  to->low=from->low;to->high=from->high;
  from->low=-1;from->high=0;
 }
}
NEVER int fixed_structure_transfer(int n){
 transfer_links[0].next=&transfer_links[1];transfer_links[1].next=0;
 transfer_links[0].owner=0;transfer_links[1].owner=0;
 left_transfer.head=0;right_transfer.head=transfer_links;
 left_transfer.low=-1;right_transfer.low=n;right_transfer.high=n+8192L;
 transfer_fields(&left_transfer,&right_transfer);
 return left_transfer.head==transfer_links&&right_transfer.head==0&&
  transfer_links[0].owner==&left_transfer&&transfer_links[1].owner==&left_transfer&&
  left_transfer.low==n&&left_transfer.high==n+8192L&&right_transfer.low==-1&&right_transfer.high==0;
}
NEVER int test_suite(int n){int i,j,sum,x,got;
 if(automatic_case(n)!=n+3||hinted_case(n)!=n+45||larger_case(n)!=n+45||blocked_case(n)!=n+7)return 1;
 if(early(-1)!=-7||early(4)!=3||early(10)!=15||local_array(n)!=n*3+3)return 2;
 if(wide(0x12345678ul,4)!=0x23456783ul)return 3;
 events=0;got=pair(next(),next());if(events!=2||(got!=12&&got!=21))return 4;
 events=0;if(0&&tick(1))return 5;if(!(1||tick(0)))return 6;if(events!=0)return 7;
 events=0;got=n?tick(11):tick(17);if(got!=(n?11:17)||events!=1)return 8;
 events=0;i=0;while(tick(i<4)){i++;if(i==2)continue;}if(i!=4||events!=5)return 9;
 events=0;sum=0;for(i=0;tick(i<4);i=tick(i+1)){if(i==1)continue;sum+=i;if(i==3)break;}
 if(sum!=5||events!=7)return 10;
 events=0;i=0;do{i++;if(i==2)continue;}while(tick(i<4));if(i!=4||events!=4)return 11;
 x=5;if(aliased(&x,x)!=10||x!=10)return 12;
 x=5;got=aliased(&x,2)+x;if((got!=12&&got!=14)||x!=7)return 13;
 x=0;j=1;(&x)[via(&x)]=pair(1,j);if(x!=11)return 14;
 if(recursive(3)!=10)return 15;
 if(shared_leaf_case(n)!=n+6)return 30;
 if(forced_attribute(n)!=n+9||blocked_alias(n)!=n+11||pressure_case(n)!=17*n+3)return 16;
 x=0;bump(&x);if(x!=2)return 17;bump(&x);if(x!=3)return 18;
 events=0;if(return_step(1)!=1||events!=1||far_read("AZ")!=90)return 19;
 destination_pointer=left_array;left_array[0]=10;right_array[0]=20;destination_pointer[0]=change_destination();
#ifdef __ZICC__
 if(left_array[0]!=42||right_array[0]!=20)return 20;
#else
 if(!((left_array[0]==42&&right_array[0]==20)||(left_array[0]==10&&right_array[0]==42)))return 20;
#endif
 {unsigned long value=5;value+=change_wide(&value);
  if(value!=101)return 21;
 }
 copy_a.x=7;copy_a.y=11;copy_b.x=19;copy_b.y=23;copy_c.x=0;copy_target=&copy_c;events=0;
 *copy_destination()=*copy_source();if(events!=2)return 22;
#ifdef __ZICC__
 if(copy_c.x!=7||copy_c.y!=11||copy_b.x!=19)return 23;
#endif
 copy_b.x=19;copy_b.y=23;
 if(copy_value(&copy_c,&copy_b)!=23||copy_c.x!=19||local_struct(n)!=2*n+1)return 24;
 if(forward_case(n)!=n+13||narrow((unsigned char)(n+253))!=((n+254)&255))return 25;
 events=0;if(early_auto_case(n)!=1||events!=n||early_auto_case(-1)!=0)return 26;
 state=5;events=0;if(state_guard(4)||events||!state_guard(5)||events!=1)return 27;
 state=4;if(state_guard(5)||events!=1||!state_guard(4)||events!=2)return 28;
 totals[1]=11;if(indexed_sum(1,4,1)!=26||indexed_sum(3,2,1)!=26||totals[0]!=0)return 31;
 if(indexed_step(1)!=7||indexed_volatile(2)!=7)return 32;
 selected_bin=n!=0;bins[0]=n+1;
 if(fixed_sum()!=n+16||totals[selected_bin]!=n+16)return 33;
 if(runtime_sum(n?2:1)!=(n?12:15))return 34;
 bins[0]=2;
 forward_parameter(n);
 if(copy_a.x!=n||copy_a.y!=n+11)return 35;
 overlay.low.x=n+9;overlay.low.y=n-13;copy_overlap();
 if(overlay.high.value.x!=n+9||overlay.high.value.y!=n-13)return 36;
 if(project_same(n,11)!=n+11||project_distinct(n,19,0)!=n+19||
    project_distinct(n,19,1)!=-7||project_copy_observed(n)!=3*n+3)return 43;
 projected_words[1]=0x9321;observed_word=0xab12;
 if(!check_fixed_load()||!check_changed_load()||projected_words[1]!=0xcd00||
    check_fixed_load()||!check_observe_load())return 44;
 if(!check_field_guard(n))return 45;
 if(!check_inline_index(n))return 46;
 if(!check_loop_wrapper(255,2))return 46;
 check_action(n);if(events!=-19)return 37;
 check_action(5);if(events!=17)return 38;
 state_left=n;state_right=n;events=0;
 if(state_branch()!=2||events!=0)return 39;
 state_right=n+1;
 if(state_branch()!=7||events!=1)return 40;
 guard_state=guard_checks=events=0;
 fixed_guard_loop();if(guard_state||guard_checks!=2||events)return 41;
 guard_checks=0;
 runtime_guard_loop(n);if(guard_state!=(n!=0)||guard_checks!=(n?1:2)||events!=(n?-19:0))return 42;
 events=1234;
 if(fixed_null_guard()!=1234)return 47;
 events=23;call_long_low(-724);if(events!=-701)return 48;
 events=23;call_long_full(-724);if(observed_long!=-701L)return 49;
 if(!check_discarded_guards(n))return 50;
 if(!fixed_structure_transfer(n))return 51;
 events=0;if(loop_guarded_update(255,3)!=256||events!=1)return 52;
 {
  const int signed_inputs[4]={200,-200,327,-195};
  volatile int vseed=5;
  int r1=pressure_loop_leaf(n+1);
  int r2=signed_leaf_cases(signed_inputs);
  int r3;
  events=4;
  r3=effectful_leaf_cases(&vseed,3,7);
  if(r2!=409)return 53;
  if(r3!=528||events!=6)return 54;
  if(signed_byte_store_leaf(signed_inputs)!=136)return 55;
  events^=r1^r2^r3;
 }
 return 0;}
'''

# Each source call has two local initializers, but its substituted value is
# one XOR expression. Repeated calls exercise the caller's growth budget
KERNEL += '''
unsigned mask_word(unsigned x){
 unsigned sign=0x8000, tag=0x1234;
 return (x^sign)^tag;
}
unsigned repeat_mask(unsigned x){
''' + ' x=mask_word(x);\n'*11 + ' return x;\n}\n'

SEMANTICS_DRIVER='''int test_suite(int);
unsigned repeat_mask(unsigned);
int selected_word(const int *);
int literal_guard(void), conditional_literal_guard(int);
extern volatile int literal_guard_state;
int main(void){
 int input[4]={3,5,7,42};
 if(test_suite(3)||test_suite(0))return 1;
 if(repeat_mask(0x4321)!=0xd115)return 5;
    if(conditional_literal_guard(0)!=19||literal_guard_state!=0)return 2;
    if(conditional_literal_guard(1)!=7||literal_guard_state!=1)return 3;
    if(literal_guard()!=-3||literal_guard_state!=2)return 4;
 return selected_word(input)!=42;
}'''

def transfers_to(assembly,callee):
    return re.search(r'^    (?:jsr|jmp) \.loword\(' + re.escape(callee) + r'\)$',
                     assembly,re.M) is not None


def build(name,kernel,driver,flags=()):
    directory=OUT/name;directory.mkdir(parents=True,exist_ok=True);c.OUT=directory
    path=directory/'kernels.c';path.write_text(kernel)
    asm=path.with_suffix('.s');obj=path.with_suffix('.o')
    c.run([ROOT/'build/zicc.exe',path,'-o',asm,*flags])
    c.run([c.CC65/'ca65.exe','--cpu','65816','-g','-o',obj,asm])
    workspace=directory/'workspace.s';workspace.write_text('.exportzp __arith_lhs,__arith_rhs\n.segment "DP_SCRATCH": zeropage\n__arith_lhs:.res 4\n__arith_rhs:.res 28\n')
    c.run([c.CC65/'ca65.exe','-o',workspace.with_suffix('.o'),workspace])
    _,rom,sy=c.compile_case('driver',driver,extra_objects=[obj,workspace.with_suffix('.o'),ROOT/'build/integers.o',ROOT/'build/libc.a'],flags=list(flags))
    digest=b.run(directory,rom,sy)
    return asm.read_text(),digest


def main():
    ap=argparse.ArgumentParser();ap.add_argument('--case',choices=['semantics','diagnostics','linkage','long-call','forward-void']);args=ap.parse_args()
    OUT.mkdir(parents=True,exist_ok=True);report={}
    if not args.case or args.case=='semantics':
        for mode,flags in [('automatic',()),('disabled',('--no-inline',))]:
            assembly,digest=build(mode,KERNEL,SEMANTICS_DRIVER,flags)
            def body(name):return re.search(r'^_'+name+r':\n(.*?)^__size_'+name+r' =',assembly,re.M|re.S)[1]
            assert ('; inlined call: automatic_case plain' in body('automatic_case'))==(mode=='automatic')
            assert ('.loword(_mask_word)' in body('repeat_mask'))==(mode=='disabled')
            assert ('; inlined call: hinted_case ' in body('hinted_case'))==(mode=='automatic')
            assert 'jsr .loword(_kernels__shared_leaf)' in body('kernels__retained_wide_caller')
            assert ('; inlined call: shared_leaf_case ' in body('shared_leaf_case'))==(mode=='automatic')
            blocked=body('blocked_case')
            assert '; inlined call: blocked_case ' not in blocked,blocked
            assert transfers_to(blocked,'_blocked'),blocked
            assert '; inlined call: larger_case' not in body('larger_case')
            assert transfers_to(body('larger_case'),'_kernels__larger')
            assert 'jsr .loword(_pair)' not in body('test_suite')
            assert 'jsr .loword(_early)' not in body('test_suite')
            assert 'jsr .loword(_recursive)' in body('recursive')
            assert '; inlined call: pressure_case plain' not in body('pressure_case')
            assert 'jsr .loword(_plain)' in body('pressure_case')
            discarded=body('check_discarded_guards')
            assert 'inlined call: check_discarded_guards discarded_pure_guard' in discarded
            assert 'lda a:.loword(_unused_guard)' not in discarded
            assert 'lda a:.loword(_volatile_guard)' in discarded
            literal=body('conditional_literal_guard')
            assert ('inlined call: conditional_literal_guard literal_guard' in literal)==(mode=='automatic'),literal
            assert (('jsr .loword(_literal_guard)' in literal) or ('jmp .loword(_literal_guard)' in literal))==(mode=='disabled'),literal
            assert '.export _literal_guard' in assembly
            assert 'jsr .loword(_forced_attribute)' not in body('test_suite')
            assert 'jsr .loword(_blocked_alias)' in body('test_suite')
            assert ('; inlined call: forward_case later' in body('forward_case'))==(mode=='automatic')
            assert transfers_to(body('early_auto_case'),'_early_auto')
            guard=body('state_guard')
            assert 'jsr .loword(_next)' in guard and 'matches_state' in guard
            assert re.search(r'\b(?:cmp|cpx) a:\.loword\(_kernels__state\)',guard),guard
            assert 'cmp #0' not in guard.split('jsr .loword(_next)',1)[0],guard
            state_branch=body('state_branch')
            if mode=='automatic':
                assert re.search(r'cmp a:\.loword\(_state_right\)\n    beq ',state_branch),state_branch
            indexed=body('indexed_sum')
            if mode=='automatic':
                assert 'inlined call: indexed_sum add_elements' in indexed,indexed
                assert re.search(r'\b(?:lda|adc) a:\.loword\(_bins\+\$0000\),[xy]',indexed),indexed
                fixed=body('fixed_sum')
                assert 'inlined call: fixed_sum sum_from' in fixed,fixed
                markers=re.findall(r'^(__inlined_\w+_add_elements):$',fixed,re.M)
                assert len(set(markers))==len(markers)==3,fixed
                assert 'loop lowering:' not in fixed,fixed
            else:
                assert 'jsr .loword(_add_elements)' in indexed,indexed
                assert transfers_to(body('fixed_sum'),'_sum_from')
            assert transfers_to(body('runtime_sum'),'_sum_from')
            forwarded=body('forward_parameter')
            assert ('inlined call: forward_parameter copy_parameter' in forwarded)==(mode=='automatic'),forwarded
            assert ('jsr .loword(_copy_parameter)' in forwarded)==(mode=='disabled'),forwarded
            assert 'jsr .loword(_copy_into_overlay)' in body('copy_overlap')
            for name in ('project_same','project_distinct'):
                projection=body(name)
                assert ('; inlined call: '+name+' project' in projection)==(mode=='automatic'),projection
                assert ('jsr .loword(_project)' in projection)==(mode=='disabled'),projection
            observed=body('project_copy_observed')
            for callee in ('project_mutating','project_identity'):
                assert f'jsr .loword(_{callee})' in observed,observed
            projected=body('check_fixed_load')
            if mode=='automatic':
                assert 'lda a:.loword(_projected_words+$0003)' in projected and 'cmp #$93' in projected,projected
                assert '    sta ' not in projected and '    pha\n' not in projected,projected
            else:
                assert 'jsr .loword(_fixed_load)' in projected,projected
            fixed_field=body('fixed_field_guard')
            assert ('; inlined call: fixed_field_guard field_guard' in fixed_field)==(mode=='automatic'),fixed_field
            assert transfers_to(fixed_field,'_field_guard')==(mode=='disabled'),fixed_field
            if mode=='automatic':
                assert 'ora #$3000' in fixed_field,fixed_field
            assert transfers_to(body('runtime_field_guard'),'_field_guard')
            fixed_local=body('fixed_local_fields')
            assert ('; inlined call: fixed_local_fields local_field_update' in fixed_local)==(mode=='automatic'),fixed_local
            assert '.loword(_local_field_update)' in body('runtime_local_fields')
            captured_index=body('check_inline_index')
            if mode=='automatic':
                assert '; inlined call: check_inline_index inline_store_value' in captured_index,captured_index
                assert captured_index.count('inc a:.loword(_indexed_inline_pos)')==1,captured_index
                # The pre-increment index 1 can also load directly as a two-byte offset
                assert re.search(
                    r'(?:tax|ldx #\$0002)\n    lda .+\n    sta a:\.loword\(_indexed_inline_slots\+\$0000\),x',
                    captured_index),captured_index
            loop_wrapper=body('check_loop_wrapper')
            assert ('; inlined call: check_loop_wrapper two_calls' in loop_wrapper)==(mode=='automatic'),loop_wrapper
            assert ('jsr .loword(_two_calls)' in loop_wrapper)==(mode=='disabled'),loop_wrapper
            if mode=='automatic':
                assert loop_wrapper.count('jsr .loword(_record_wrapper_pair)')==2 and 'eor ' not in loop_wrapper,loop_wrapper
            guarded_update=body('loop_guarded_update')
            assert ('inlined call: loop_guarded_update guarded_byte_update' in guarded_update)==(mode=='automatic'),guarded_update
            dispatch=body('check_action')
            assert ('inlined call: check_action choose_action' in dispatch)==(mode=='automatic'),dispatch
            guard=body('fixed_guard_loop')
            assert ('inlined call: fixed_guard_loop guarded_loop' in guard)==(mode=='automatic'),guard
            transfer=body('fixed_structure_transfer')
            assert ('inlined call: fixed_structure_transfer transfer_fields' in transfer)==(mode=='automatic'),transfer
            assert '.loword(_guarded_loop)' in body('runtime_guard_loop')
            null_guard=body('fixed_null_guard')
            assert ('inlined call: fixed_null_guard selected_word' in null_guard)==(mode=='automatic'),null_guard
            assert ('.loword(_selected_word)' in null_guard)==(mode=='disabled'),null_guard
            if mode=='automatic':
                assert 'lda 7,s' in null_guard and not re.search(r'\b(?:beq|bne) ',null_guard),null_guard
                assert 'inlined call: pressure_loop_leaf public_arith_leaf' in body('pressure_loop_leaf')
                assert 'inlined call: signed_leaf_cases kernels__scale_signed_leaf' in body('signed_leaf_cases')
                assert 'inlined call: signed_leaf_cases kernels__take_schar_leaf' in body('signed_leaf_cases')
                assert 'inlined call: effectful_leaf_cases kernels__leaf_twice' in body('effectful_leaf_cases')
                assert 'inlined call: signed_byte_store_leaf kernels__scale_signed_int_leaf' in body('signed_byte_store_leaf')
                assert not re.search(r'eor #\$[0-9A-F]{2}00',body('signed_byte_store_leaf')),body('signed_byte_store_leaf')
            assert '#$8000' not in body('call_long_low') and '#$8000' in body('call_long_full')
            report[mode]=digest;print('PASS inline policies and semantics',mode,flush=True)
        host=OUT/'host.c';host.write_text(KERNEL+'\n'+SEMANTICS_DRIVER+'\n')
        exe=host.with_suffix('.exe');c.run([ROOT/'tools/msvc.cmd','/nologo','/std:c17','/O2','/Fo'+str(host.with_suffix('.obj')),'/Fe'+str(exe),host]);c.run([exe])
        print('PASS MSVC semantic reference',flush=True)
    if not args.case or args.case=='diagnostics':
        fixtures=[('conflict','__forceinline __noinline int f(int x){return x;}','conflicts'),
          ('missing','__forceinline int f(int);int main(void){return f(1);}','not available'),
          ('recursive','__forceinline int f(int x){return x?f(x-1):0;}','recursive'),
          ('mutual','__forceinline int f(int);int g(int x){return f(x);}int f(int x){return g(x);}','recursive'),
          ('switch','__forceinline int f(int x){switch(x){case 1:return 3;default:return 4;}}int main(void){return f(0);}','switch bodies'),
          ('object','inline int x;','require a function'),
          ('pointer_object','int * __attribute__((noinline)) x;','require a function'),
          ('pointer_conflict','__forceinline int * __attribute__((noinline)) f(void);','conflicts')]
        for name,source,message in fixtures:
            path=OUT/(name+'.c');path.write_text(source)
            r=c.run([ROOT/'build/zicc.exe',path,'-o',path.with_suffix('.s')],expected=1)
            assert message in r.stderr,(name,r.stderr);report[name]=r.stderr
            print('PASS inline diagnostic',name,flush=True)
    if not args.case or args.case=='linkage':
        kernel='''static int value;
int * __attribute__((noinline)) first(int n){value=n;return &value;}
int * (__attribute__((noinline)) second(int n)){return first(n+1);}
int * __attribute__((noinline)) third(void), *plain_pointer;
int * third(void){return second(41);}
int read(void){return *third();}'''
        assembly,report['pointer-attributes']=build('pointer-attributes',kernel,
            'int read(void);int main(void){return read()!=42;}')
        for name in ('first','second','third'):
            assert transfers_to(assembly,'_'+name),name
        kernel='inline int local(int x){return x+1;} __noinline int use(int x){return local(x);}'
        for mode,flags,expected in [('substitute',(),4),('external',('--no-inline',),10)]:
            assembly,digest=build('link-'+mode,kernel,f'int local(int x){{return x+7;}}int use(int);int main(void){{return use(3)!={expected};}}',flags)
            assert '\n_local:' not in assembly
            assert ('.import _local' in assembly)==(mode=='external')
            report['link-'+mode]=digest
        for name,prefix,suffix in [('extern','extern inline',''),('prior','inline','extern int local(int);')]:
            assembly,digest=build('link-'+name,prefix+' int local(int x){return x+1;}'+suffix,'int local(int);int main(void){return local(3)!=4;}',('--no-inline',))
            assert '.export _local' in assembly;report['link-'+name]=digest
        print('PASS ISO external-inline/linkage and fallback definitions',flush=True)
    if not args.case or args.case=='long-call':
        directory=OUT/'long-call';directory.mkdir(exist_ok=True)
        kernel=directory/'kernels.c';kernel.write_text(KERNEL)
        driver=directory/'driver.c';driver.write_text(SEMANTICS_DRIVER)
        stem=directory/'program'
        c.run([sys.executable,ROOT/'tools/build-rom.py',kernel,driver,'--stage','4','-o',stem.with_suffix('.raw')])
        c.run([ROOT/'build/romtool.exe',stem.with_suffix('.raw'),stem.with_suffix('.sfc'),ROOT/'tests/title.txt'])
        sy={n.removeprefix('_'):int(a,16) for a,n in re.findall(r'^al (\w+) \.(\S+)$',stem.with_suffix('.labels').read_text(),re.M)}
        report['long-call']=b.run(directory,stem.with_suffix('.sfc'),sy)
        print('PASS inline expansion with stage-4 JSL/RTL ABI',flush=True)
    if not args.case or args.case=='forward-void':
        kernel='''int count;__forceinline void step(void);__forceinline int loop(int);
__noinline int forward_entry(int n){return loop(n);}
__forceinline int loop(int n){int i;for(i=0;i<4;step()){if(i==n)return i;i++;}return 9;}
__forceinline void step(void){count++;}
static unsigned bounded_loop(unsigned n){
    unsigned result=0;while(n){for(unsigned i=1;i<=3;++i)result+=i;--n;}
    return result;
}
unsigned short_literal_loop(void){return bounded_loop(3);}
unsigned long_literal_loop(void){return bounded_loop(80);}'''
        driver='''int forward_entry(int);extern int count;
unsigned short_literal_loop(void),long_literal_loop(void);
int main(void){
    if(forward_entry(2)!=2||count!=2)return 1;
    count=0;if(forward_entry(0)!=0||count!=0)return 2;
    return short_literal_loop()!=18||long_literal_loop()!=480;
}'''
        assembly,report['forward-void']=build('forward-void',kernel,driver)
        short=assembly.split('_short_literal_loop:\n',1)[1].split('__size_short_literal_loop',1)[0]
        long=assembly.split('_long_literal_loop:\n',1)[1].split('__size_long_literal_loop',1)[0]
        assert 'lda #$0012\n' in short and not transfers_to(short,'_kernels__bounded_loop'),short
        assert transfers_to(long,'_kernels__bounded_loop'),long
        print('PASS forward definitions, void loop steps and early exits',flush=True)
    report['inputs']={str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in [ROOT/'build/zicc.exe',ROOT/'src/codegen/inline.inc',Path(__file__)]}
    (OUT/('results-'+(args.case or 'all')+'.json')).write_text(json.dumps(report,indent=2)+'\n')


if __name__=='__main__':main()
