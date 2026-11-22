"""Check address reuse, argument passing and wraparound with inputs the compiler learns only at run time."""
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
OUT=Path(os.environ.get('ZICC_LOGS_DIR', 'logs')).resolve() / 'body-codegen-check'
sys.path.insert(0,str(ROOT/'tools'))
from mesen_core import Core
spec=importlib.util.spec_from_file_location('support',ROOT/'tests/check-compiler.py')
c=importlib.util.module_from_spec(spec);spec.loader.exec_module(c)

KERNELS=r'''
#include <string.h>
#include <stdbool.h>
int side_effect;
unsigned opaque(unsigned);
unsigned narrowed_step(unsigned a,unsigned b){unsigned char x=a,y=b;x-=((unsigned char)(x-y)>>5)+1;opaque(x);return x;}
unsigned narrowed_step0(unsigned a,unsigned b){unsigned char x=a,y=b;x-=((unsigned char)(x-y)>>0)+255;opaque(x);return x;}
unsigned boolean_difference(unsigned a,unsigned b){unsigned char x=a,y=b;x-=((_Bool)(x-y)>>0)+1;opaque(x);return x;}
unsigned boolean_target(unsigned a,unsigned b){_Bool x=a;unsigned char y=b;x-=((unsigned char)(x-y)>>0)+1;opaque(x);return x;}
unsigned sum_dest[4];
void stack_sums(unsigned input){
 unsigned first,second;
 input=opaque(input);
 first=(input&31u)<<5;second=first+1024u;
 sum_dest[0]=0x4c00u+first;sum_dest[1]=0x4c00u+second;
 sum_dest[2]=0x5400u+first;sum_dest[3]=0x5400u+second;
}
int relative(int *p,int origin,int value,int unused){
 int i,start=origin+3;
 p[start]=value;p[start+1]=p[start];p[start+5]=start;
 for(i=start;i<=start+1;++i)p[i]=start;
 p[start-1]+=1;return i;
}
int rectangular(int *p,int q[][13],int first,int value){
 int i,base=first+2;
 p[base]=value;p[base+1]=p[base];p[base+9]=base;
 for(i=base;i<=base+1;i++)q[base][i]=base;
 q[base][base-1]+=1;q[base+7][base]=p[base];return 0;
}
int mutate(int *p,int n){int *saved=p;p[n]=3;p=p+1;p[n]=5;return saved[n]+p[n];}
int copy_snapshot(int a){int b=a;a=19;return b+a;}
int short_if_loop(int flag){int i,total=0;for(i=0;i<3;++i){if(flag)total+=i;else total-=i;}return total+i;}
int conditional_bound(int flag){int i,total=0;for(i=0;i<3;++i){++total;if(flag)++i;}return total;}
int single_trip_exit(volatile int *out){
 int once=0,keep=1;
 while(!once){++*out;if(!keep)break;++*out;once=1;}
 return once;
}
int runtime_trip_exit(volatile int *out,int stop){
 int once=0;
 while(!once){++*out;if(stop)break;++*out;once=1;}
 return once;
}
unsigned long copy_bytes(const unsigned char *source){
 unsigned long i,j,value=0;unsigned char *bytes=(unsigned char *)&value;
 for(i=0;i<1;++i)for(j=0;j<sizeof(value);++j)bytes[j]=source[j];
 return value+j;
}
unsigned alias_change(int flag){
 unsigned first=0,second=0;unsigned char *p=(unsigned char *)&first;
 for(long i=0;i<2;++i){if(i==flag)p=(unsigned char *)&second;p[i]=(unsigned char)(i+1);}
 return first+second*2;
}
int sum_rows(int rows[][2]){
 int sum=0.0f;
 for(int i=0;i<2;++i)sum+=rows[i][0]+rows[i][1];
 return sum;
}
int update_rows(int rows[][2],int *result){
 int i;
 for(i=0;i<2;++i){*result+=rows[i][0];rows[i][1]+=*result;}
 return i;
}
int cast_bound(int *p,int origin){int i,n=0;for(i=(int)((unsigned)origin+1u);i<=(int)((unsigned)origin+2u);i++){*p+=i;n++;}return n;}
int unsigned_step(int *p,int start){int i;for(i=start;i<=start;i+=1u)*p=i;return i;}
int wrap_fact(void){int n=32767;n+=1u;return n;}
int signed_bounds(int *p,int base){int i,n=0;for(i=base+32767;i<=base-32767;i++){*p=19;n++;}return n;}
int progress(int *state){int n=4;char ch;
 while(n<=4)if((*state)--==0){ch='G';n+=1;}
 if(ch>='J'&&ch<'Z')n=17;
 if(ch=='R')return 0;
 return n+ch;
}
int retry(int *state){int n=4;char ch;
 while(n<=4)if(predicate(state)){ch='G';n+=1;}
 if(ch>='J'&&ch<'Z')n=17;
 if(ch=='R')return 0;
 return n+ch;
}
int byte_update(unsigned char *out,unsigned char first){unsigned char x=first;x++;*out=x;x--;return x;}
unsigned char byte_global;
unsigned global_byte_steps(void){byte_global=255;byte_global++;if(byte_global)return 1;byte_global--;return byte_global;}
#ifndef ITEM_DEFINED
#define ITEM_DEFINED
struct item { unsigned char tag, value; unsigned marker; };
#endif
struct item items[12];
unsigned item_compare(void){return items[0].value<64;}
const unsigned char windows[5]={0,3,3,4,0};
unsigned window_start(unsigned i){if(windows[i]!=0&&windows[i]!=windows[i-1])return 1;return 0;}
unsigned signed_window_start(int i){if(windows[i]!=0&&windows[i]!=windows[i-1])return 1;return 0;}
void item_updates(unsigned char *p) {
 p[0]=(unsigned char)(p[0]+1);p[1]=(unsigned char)(p[1]-1);
}
void item_alias_loop(void) {
 unsigned char i;
 for(i=0;i<12;i++){struct item *p=&items[i];if(p->tag)p->value=(unsigned char)(p->value+1);}
}
unsigned item_alias_observed(void) {
 unsigned char i;struct item *p=items;
 for(i=0;i<3;i++){p=&items[i];p->value=(unsigned char)(p->value+1);}
 return p==&items[2];
}
void item_alias_changed_index(void) {
 unsigned char i;
 for(i=0;i<4;i++){struct item *p=&items[i];if(i==1)i++;p->value=9;}
}
void item_alias_escaped(void) {
 unsigned char i;
 for(i=0;i<2;i++){struct item *p=&items[i];item_repoint(&p);p->value=33;}
}
void item_alias_jump(int enter) {
 unsigned char i=0;struct item *p=&items[5];
 if(enter)goto inside;
 for(i=0;i<2;i++){p=&items[i];inside:p->value=41;}
}
void item_distinct(unsigned char *p) {p[0]=(unsigned char)(p[1]+1);}
int post_value(int n){int x=7;return x++;}
int entry_x,entry_y;
int post_global(int seed){
 int old;
 entry_x=3;entry_y=2;
 if((entry_x<entry_y?entry_x++:entry_y++)!=2)return -1;
 old=entry_x>entry_y?entry_x--:entry_y++;
 return seed+entry_x+10*old+100*entry_y;
}
int post_global_alias(int *target){
 entry_x=4;
 *target=9;
 return entry_x;
}
void change_entry(void);
int post_global_call(void){
 entry_x=5;
 change_entry();
 return entry_x;
}
int post_branch(int seed){
 int x=3,y=2,z;
 if((x<y?x++:y++)!=2)return -1;
 z=x>y?x--:y++;
 return seed+x+10*z+100*y;
}
int branch_facts(int n){int x=3;if(n)x=9;return x;}
int conversions(int n){unsigned char x=255;signed char y=-1;x++;return x+((int)y)+n;}
unsigned wrapping(unsigned *p){return *(p+1);}
unsigned memory_updates(unsigned *p){unsigned a=(*p)++;unsigned b=++*p;*p-=1;return a+b+*p;}
unsigned break_loop(unsigned *p,unsigned start){unsigned i;for(i=start;i<=start+1u;i++){p[i&3]=i;if(i==65535u)break;}return i;}
int escaped(int *p,int start){int i=start;while(i<start+2){*p+=i;modify(&i);}return i;}
int compare_near(const char *a,const char *b){return strcmp(a,b);}
int compare_far(const char * __far a,const char * __far b){return strcmp(a,b);}
int compare_effects(void){return strcmp(right_source(),left_source());}
'''
# Explicit prototypes keep argument/result ABI opaque across the two units
KERNELS='struct item;void item_repoint(struct item **);int predicate(int *);void modify(int *);char *right_source(void);char *left_source(void);\n'+KERNELS
DRIVER=r'''
int relative(int *,int,int,int);int rectangular(int *,int [][13],int,int);
int mutate(int *,int);int copy_snapshot(int);int progress(int *);int retry(int *);
int short_if_loop(int);int conditional_bound(int);
int single_trip_exit(volatile int *);int runtime_trip_exit(volatile int *,int);
unsigned long copy_bytes(const unsigned char *);unsigned alias_change(int);
int sum_rows(int [][2]);int update_rows(int [][2],int *);
int cast_bound(int *,int);int unsigned_step(int *,int);int wrap_fact(void);
int signed_bounds(int *,int);
int byte_update(unsigned char *,unsigned char);int post_value(int);int branch_facts(int);int conversions(int);
int post_branch(int);
extern int entry_x,entry_y;
int post_global(int);int post_global_alias(int *);int post_global_call(void);
void change_entry(void){entry_x=11;}
unsigned global_byte_steps(void);
unsigned narrowed_step(unsigned,unsigned);unsigned narrowed_step0(unsigned,unsigned);
unsigned boolean_difference(unsigned,unsigned);unsigned boolean_target(unsigned,unsigned);
void stack_sums(unsigned);extern unsigned sum_dest[4];
void item_updates(unsigned char *);void item_alias_loop(void);unsigned item_alias_observed(void);void item_alias_changed_index(void);
void item_alias_escaped(void);void item_alias_jump(int);void item_distinct(unsigned char *);
unsigned item_compare(void);
unsigned window_start(unsigned);
unsigned signed_window_start(int);
#ifndef ITEM_DEFINED
#define ITEM_DEFINED
struct item { unsigned char tag, value; unsigned marker; };
#endif
extern struct item items[12];
void item_repoint(struct item **p){*p=&items[7];}
unsigned wrapping(unsigned *);unsigned memory_updates(unsigned *);unsigned break_loop(unsigned *,unsigned);
int escaped(int *,int);int compare_near(const char *,const char *);int compare_far(const char * __far,const char * __far);
int compare_effects(void);
char left[5]={'A','B','C',0,0},right[5]={'A','B','C',0,0};
int sequence;
unsigned opaque(unsigned n){return n-1;}
int predicate(int *state){return (*state)--==0;}
void modify(int *n){++*n;}
char *right_source(void){sequence=sequence*10+2;return right;}
char *left_source(void){sequence=sequence*10+1;return left;}
int main(void){int a[52],b[22][13],i,j,n;unsigned char byte;
 for(i=0;i<52;i++)a[i]=0;
 for(i=0;i<22;i++)for(j=0;j<13;j++)b[i][j]=0;
 if(relative(a,2,23,41)!=7||a[4]!=1||a[5]!=5||a[6]!=5||a[10]!=5)return 1;
 if(rectangular(a,b,3,23)||a[5]!=23||a[6]!=23||a[14]!=5||b[5][5]!=5||b[5][6]!=5||b[5][4]!=1||b[12][5]!=23)return 2;
 /* Partial overlap and identical array bases must preserve every reload */
 if(rectangular((int *)b,b,2,67)||b[0][4]!=67||b[4][4]!=4||b[4][5]!=4||b[11][4]!=67)return 3;
 if(mutate(a,1)!=8||copy_snapshot(8)!=27)return 4;
 if(short_if_loop(1)!=6||short_if_loop(0)!=0||conditional_bound(1)!=2||conditional_bound(0)!=3)return 45;
 {volatile int seen=0;
  if(single_trip_exit(&seen)!=1||seen!=2||runtime_trip_exit(&seen,1)!=0||seen!=3||
     runtime_trip_exit(&seen,0)!=1||seen!=5)return 48;}
 {unsigned char bytes[4]={0x13,0x26,0x8b,0x42};
  if(copy_bytes(bytes)!=0x428b2617UL||alias_change(0)!=1026||alias_change(1)!=1025)return 46;}
 {int rows[2][2]={{1,2},{4,8}};
  if(sum_rows(rows)!=15||update_rows(rows,&rows[1][0])!=2||
     rows[0][1]!=7||rows[1][0]!=10||rows[1][1]!=18)return 47;}
 n=2;if(progress(&n)!=76||n!=-1)return 5;
 n=3;if(retry(&n)!=76||n!=-1)return 6;
 if(byte_update(&byte,255)!=255||byte!=0||post_value(0)!=7||branch_facts(0)!=3||branch_facts(1)!=9||conversions(11)!=10)return 7;
 if(post_branch(17)!=450)return 28;
 if(post_global(17)!=450||entry_x!=3||entry_y!=4)return 29;
 if(post_global_alias(&entry_x)!=9||post_global_call()!=11)return 30;
 if(global_byte_steps()!=255)return 25;
 for(i=0;i<256;i++)for(j=0;j<256;j+=17){
  if(narrowed_step(i,j)!=(unsigned char)(i+255-((unsigned char)(i-j)>>5)))return 33;
  if(narrowed_step0(i,j)!=(unsigned char)(i-((unsigned char)(i-j))-255))return 34;
 }
 if(boolean_difference(4,4)!=3||boolean_difference(4,3)!=2||boolean_target(1,0)!=1)return 35;
 stack_sums(32);if(sum_dest[0]!=0x4fe0u||sum_dest[1]!=0x53e0u||sum_dest[2]!=0x57e0u||sum_dest[3]!=0x5be0u)return 32;
 {unsigned char values[2]={255,0};item_updates(values);if(values[0]!=0||values[1]!=255)return 18;}
 for(i=0;i<12;i++){items[i].tag=i&1;items[i].value=255;items[i].marker=0x3456;}
 item_alias_loop();for(i=0;i<12;i++)if(items[i].value!=(i&1?0:255)||items[i].marker!=0x3456)return 19;
 if(!item_alias_observed()||items[0].value!=0||items[1].value!=1||items[2].value!=0)return 20;
 item_alias_changed_index();if(items[0].value!=9||items[1].value!=9||items[2].value!=0||items[3].value!=9)return 21;
 item_alias_escaped();if(items[7].value!=33||items[0].value!=9||items[1].value!=9)return 22;
 item_alias_jump(1);if(items[5].value!=41||items[1].value!=41)return 23;
 {unsigned char values[2]={2,19};item_distinct(values);if(values[0]!=20||values[1]!=19)return 24;}
 items[0].value=0;if(!item_compare())return 26;items[0].value=63;if(!item_compare())return 27;
 items[0].value=64;if(item_compare())return 28;items[0].value=255;if(item_compare())return 29;
 if(window_start(0)||!window_start(1)||window_start(2)||!window_start(3)||window_start(4))return 30;
 if(!signed_window_start(1)||signed_window_start(2))return 31;
 {unsigned v=10;if(memory_updates(&v)!=33||v!=11)return 8;}
 {unsigned p[4];if(break_loop(p,65534u)!=65535u)return 9;}
 n=0;if(escaped(&n,3)!=5||n!=7)return 10;
 if(compare_near(left,right)!=0||compare_far(left,right)!=0)return 11;
 right[2]='D';if(compare_near(left,right)>=0||compare_near(right,left)<=0)return 12;
 right[2]='C';sequence=0;if(compare_effects()!=0||sequence!=12)return 13;
#ifdef __ZICC__
 n=0;if(cast_bound(&n,32766)!=0||n!=0)return 14;
#else
 n=0;if(cast_bound(&n,32766)!=2||n!=65535)return 14;
#endif
 n=0;if(cast_bound(&n,-4)!=2||n!=-5||unsigned_step(&n,-3)!=-2||n!=-3)return 15;
#ifdef __ZICC__
 if(wrap_fact()!=-32768)return 16;
#endif
 n=0;if(signed_bounds(&n,0)!=0||n!=0)return 17;
 return 0;}
'''

GENERAL_KERNELS=r'''
int note(int);
int tick(void);
int fixed_grid[6][9];
static void set_value(int a,int b,int *out){*out=a+b;}
static int fill_pair(int a[][9],int row,int value,int bias){
 a[row][row]=value;
 a[row][row+1]=value;
 return a[row][row+1]+bias;
}
int fixed_exit(int bias){
 int row=2, value;
 while(row<4){note(row);++row;}
 set_value(row,7,&value);
 return fill_pair(fixed_grid,row,value,bias);
}
int zero_and_do(void){
 int i=4;
 while(i<4)note(9);
 do{note(i);--i;}while(i>3);
 return i;
}
int dead_late(int seed){
 int v=seed+2, result=note(v);
 v=note(seed);
 v=200/v;
 return result;
}
int live_paths(int stop){
 int i, v=2, result=0;
 for(i=0;i<4;++i){
  v=note(i+1);
  if(i==stop)break;
  if(i==1)continue;
  result+=v;
  v=note(i+5);
 }
 return result+v;
}
void wide_unsigned(unsigned long begin,unsigned long end){
 unsigned long i;
 for(i=begin;i<end;++i)if(tick())break;
}
void wide_signed(unsigned long begin,int end){
 unsigned long i;
 for(i=begin;i<end;++i){if(tick())break;continue;}
}
unsigned long wide_observed(unsigned long begin,unsigned long end){
 unsigned long i;
 for(i=begin;i<end;++i)if(tick())break;
 return i;
}
struct NarrowPair { int x; int y; };
static const struct NarrowPair ro_pairs[8]={
 {-120,30},{50,-90},{-1,127},{80,-40},{15,60},{-70,-20},{110,-5},{-45,95}
};
static const int dot_coeffs[4]={45,-35,19,-51};
unsigned char packed_out[32];
int pack_scaled_dot(int c0,int c1){
 int i, total=0, k0=dot_coeffs[c0&3], k1=dot_coeffs[c1&3];
 for(i=0;i<8;++i){
  int dot=(ro_pairs[i].x*k0+ro_pairs[i].y*k1)/128;
  total+=dot;
  packed_out[i*4+0]=(unsigned char)dot;
  packed_out[i*4+1]=(unsigned char)(dot>>8);
  packed_out[i*4+2]=(unsigned char)i;
  packed_out[i*4+3]=0x80u;
 }
 return total;
}
int narrow_long_add(long a,long b){
 return (int)((a+b)-(a^b));
}
int bounded_smul8(int a,int b){
 if(a<-128||a>127||b<-128||b>127)return 0;
 return a*b;
}
int widened_flag(unsigned value,int key){
 unsigned char flag=value&1;
 if(flag)return flag>key;
 return flag<key;
}
static const signed char dot_a[3]={3,4,5},dot_b[3]={3,2,1};
int mixed_sign_dot(int n){
 int b=dot_coeffs[(n+1)&3],a=dot_coeffs[n&3],i,total=note(1);
 for(i=0;i<3;++i)
  total+=dot_a[i]*a+dot_b[i]*b-dot_a[i]*b-dot_b[i]*a;
 return total;
}
struct TripletByte { signed char x, y, z; };
static const struct TripletByte tri_verts[6]={
 {10,-20,30},{-40,50,-60},{70,-80,90},{-100,110,-120},{127,-128,15},{-1,2,-3}
};
int dot_y_scratch(int step,int packed_c){
 int i,k0=dot_coeffs[packed_c&3],k1=dot_coeffs[(packed_c>>2)&3],k2=dot_coeffs[(packed_c>>4)&3],sum=0;
 if(step<1||step>6)return 0;
 for(i=0;i<6;i+=step)sum+=tri_verts[i].x*k0+tri_verts[i].y*k1+tri_verts[i].z*k2;
 return sum;
}
int dot_stride_wrap(unsigned stop,int a,int b){
 int sum=0,ca=dot_coeffs[a&3],cb=dot_coeffs[b&3];
 unsigned i;
 for(i=0;i<21845u;++i){
  if(i==stop)break;
  sum+=tri_verts[i+1].x*ca+tri_verts[i+1].y*cb;
 }
 return sum;
}
unsigned char tri_sx[6],tri_sy[6];
int tri_depth[6];
static int tri_div16(int v){return (v+128)>>4;}
void tri_project_loop(int c0,int c1,int c2){
 int i,k0=dot_coeffs[c0&3],k1=dot_coeffs[c1&3],k2=dot_coeffs[c2&3];
 for(i=0;i<6;++i){
  int px=tri_verts[i].x*k0+tri_verts[i].y*k1+tri_verts[i].z*k2;
  int py=tri_verts[i].x*k1-tri_verts[i].y*k2;
  tri_sx[i]=(unsigned char)(120+tri_div16(px));
  tri_sy[i]=(unsigned char)(96+tri_div16(py));
  tri_depth[i]=tri_verts[i].x*k2+tri_verts[i].z*k0;
 }
}
signed char ram_vec[6]={3,-5,7,-9,11,-13};
signed char ram_scalar=-6;
int quad_ram_dot(int c0,int c1,int c2,int c3){
 int i,k0=dot_coeffs[c0&3],k1=dot_coeffs[c1&3],k2=dot_coeffs[c2&3],k3=dot_coeffs[c3&3],sum=0;
 signed char local_b=(signed char)(c0-4);
 for(i=0;i<6;++i){
  sum+=tri_verts[i].x*k0+tri_verts[i].y*k1+tri_verts[i].z*k2+ram_vec[i]*k3;
  sum+=local_b*k0+ram_scalar*k1;
 }
 return sum;
}
unsigned switch_loop_carry(int mode,unsigned *dst,unsigned n){
 unsigned i,sum=0;
 switch(mode){
  case 0:{
   unsigned a0=n&7u,a1=dst[0]&7u;
   sum=(a0+a1)+1u;
   for(i=0;i<8u;++i){dst[i+8u]=i+a0;dst[i]|=(i+a0);sum+=dst[i+8u];}
   break;
  }
  case 1:{
   unsigned b0=(n&7u)+5u;
   for(i=0;i<4u;++i){dst[i]=i*2u+b0;sum+=dst[i];}
   break;
  }
 }
 return sum;
}
void pointer_chained_offsets(unsigned *out,unsigned n){
 out[n*2u+10u]=11u;
 out[n*2u+10u+1u]=22u;
 out[n*2u+10u+32u+1u]=33u;
}
int byte_cmp_nomask(const unsigned char *p,unsigned char limit){
 unsigned char a=p[0];
 return a<limit&&a==p[1];
}
unsigned ipa_out[16];
static __noinline void ipa_cell(const unsigned char * __far p,unsigned *out,unsigned idx,unsigned shift){
 unsigned v=(unsigned)p[idx]^(0x0101u*(0xffu>>(shift&7u)));
 out[idx*2u]=v;
 out[idx*2u+1u]=v^1u;
 out[idx*2u+8u]=v+2u;
 out[idx*2u+9u]=v+3u;
}
static __noinline unsigned ipa_far_spill(const unsigned * __far src,unsigned n,unsigned shift){
 unsigned row=src[n];
 if(shift<4u)return (row&(0xffu>>shift))<<(8u-shift);
 return (row>>shift)&(0xffu>>(shift-4u));
}
unsigned ipa_run(const unsigned char *p,const unsigned * __far fsrc,unsigned n,unsigned s){
 unsigned *dst=ipa_out;
 unsigned shift=s&3u;
 ipa_cell((const unsigned char * __far)p,dst,n&3u,shift);
 return ipa_far_spill(fsrc,n&3u,shift);
}
unsigned char mul_a[16],mul_b[16];
unsigned u8_dot_retained(void){
 unsigned i,s=0;
 for(i=0;i<16u;++i)s+=(unsigned)mul_a[i]*mul_b[i];
 return s;
}
unsigned u8_dot_dynamic(unsigned n){
 unsigned i,s=0;
 for(i=0;i<n;++i)s+=(unsigned)mul_a[i]*mul_b[i];
 return s;
}
unsigned u8_mul_compound(unsigned char x,unsigned char y,unsigned i){
 unsigned p=mul_b[i]*(unsigned char)(mul_a[i]*y);
 unsigned v=x;
 v*=(unsigned)y;
 return p+v;
}
static const unsigned char rom_bit_masks[8]={1u,2u,4u,8u,16u,32u,64u,128u};
__noinline void byte_bit_clear(unsigned idx){
 mul_a[idx>>3u]&=~rom_bit_masks[idx&7u];
}
__noinline unsigned byte_bit_check(unsigned idx){
 return mul_b[idx>>3u]&rom_bit_masks[idx&7u];
}
unsigned byte_bit_ops(unsigned n){
 unsigned i,sum=0;
 for(i=0;i<n;++i){
  byte_bit_clear(i);
  mul_b[i>>3u]|=rom_bit_masks[i&7u];
  if(byte_bit_check(i)){
   unsigned char v=mul_a[i>>3u]^mul_b[i>>3u];
   while(v){sum+=v&1u;v>>=1u;}
  }
 }
 return sum;
}
unsigned word_sign_branch(unsigned v,unsigned n){
 unsigned char j;
 for(j=0;j<n;++j){
  if(v&0x8000u)v=(v<<1u)^0x1021u;
  else v<<=1u;
 }
 if((v+0x1234u)&0x8000u)v^=0x0001u;
 return v;
}
unsigned long long_shift_xor(unsigned long v,unsigned char hi,unsigned n){
 unsigned i;
 for(i=0;i<n;++i){
  unsigned char j;
  v^=(unsigned long)hi<<24u;
  for(j=8;j;--j){
   if(v&0x80000000UL)v=(v<<1u)^0x04C11DB7UL;
   else v<<=1u;
  }
  v=(v>>1u)^0xEDB88320UL;
 }
 v^=0xFFFFFFFFUL;
 v+=0x00020000UL;
 v&=0xFFFF00FFUL;
 return v;
}
unsigned red_words[32];
unsigned sum_words_unrolled(void){
 unsigned i,s=0;
 for(i=0;i<32u;++i)s+=red_words[i];
 return s;
}
unsigned xor_words_rolled(unsigned *p,unsigned n){
 unsigned i,x=0;
 for(i=0;i<n;++i)x^=p[i];
 return x;
}
'''

GENERAL_DRIVER=r'''
extern int fixed_grid[6][9];
extern unsigned char packed_out[32];
int fixed_exit(int);int zero_and_do(void);int dead_late(int);int live_paths(int);
void wide_unsigned(unsigned long,unsigned long);void wide_signed(unsigned long,int);
unsigned long wide_observed(unsigned long,unsigned long);
int pack_scaled_dot(int,int);int bounded_smul8(int,int);int narrow_long_add(long,long);
int widened_flag(unsigned,int);int mixed_sign_dot(int);
int dot_y_scratch(int,int);void tri_project_loop(int,int,int);
int dot_stride_wrap(unsigned,int,int);int quad_ram_dot(int,int,int,int);
unsigned switch_loop_carry(int,unsigned *,unsigned);
void pointer_chained_offsets(unsigned *,unsigned);
int byte_cmp_nomask(const unsigned char *,unsigned char);
extern unsigned ipa_out[16];
unsigned ipa_run(const unsigned char *,const unsigned * __far,unsigned,unsigned);
extern unsigned char mul_a[16],mul_b[16];
unsigned u8_dot_retained(void);unsigned u8_dot_dynamic(unsigned);unsigned u8_mul_compound(unsigned char,unsigned char,unsigned);
unsigned byte_bit_ops(unsigned);
unsigned word_sign_branch(unsigned,unsigned);
unsigned long long_shift_xor(unsigned long,unsigned char,unsigned);
extern unsigned red_words[32];
unsigned sum_words_unrolled(void);
unsigned xor_words_rolled(unsigned *,unsigned);
extern unsigned char tri_sx[6],tri_sy[6];extern int tri_depth[6];
unsigned notes;
unsigned long seen, stop_at;
int note(int v){notes=notes*10u+v;return v;}
int tick(void){++seen;return seen==stop_at;}
int main(void){
 notes=0;if(fixed_exit(6)!=17||notes!=23||fixed_grid[4][4]!=11||fixed_grid[4][5]!=11||fixed_grid[4][6]!=0)return 1;
 notes=0;if(zero_and_do()!=3||notes!=4)return 2;
 notes=0;if(dead_late(5)!=7||notes!=75)return 3;
 notes=0;if(live_paths(2)!=4||notes!=1523)return 4;
 seen=0;stop_at=0;wide_unsigned(0,0x10002UL);if(seen!=65538UL)return 5;
 seen=0;wide_unsigned(13,9);if(seen!=0)return 6;
 seen=0;wide_signed(0xfffeffffUL,-1);if(seen!=65536UL)return 7;
 seen=0;stop_at=3;wide_signed(0,-32768);if(seen!=3)return 8;
 seen=0;stop_at=2;if(wide_observed(65535UL,65539UL)!=65536UL||seen!=2)return 9;
 if(pack_scaled_dot(0,1)!=-35||
    packed_out[0]!=(unsigned char)-50||packed_out[1]!=0xffu||packed_out[2]!=0||packed_out[3]!=0x80u||
    packed_out[4]!=42||packed_out[5]!=0||packed_out[6]!=1||packed_out[7]!=0x80u||
    packed_out[28]!=(unsigned char)-41||packed_out[29]!=0xffu||packed_out[30]!=7||packed_out[31]!=0x80u)return 10;
 if(bounded_smul8(-128,127)!=-16256||bounded_smul8(-128,-128)!=16384||bounded_smul8(127,-1)!=-127)return 11;
 if(narrow_long_add(0x100023L,0x200005L)!=((0x23+0x05)-(0x23^0x05)))return 12;
 if(widened_flag(1,-1)!=1||widened_flag(0,-1)!=0||
    widened_flag(1,2)!=0||widened_flag(0,2)!=1)return 13;
 notes=0;if(mixed_sign_dot(0)!=481||mixed_sign_dot(3)!=-575||notes!=11)return 14;
 if(dot_y_scratch(1,0x24)!=4368||dot_y_scratch(2,0x0B)!=-8814)return 15;
 tri_project_loop(0,1,2);
 if(tri_sx[0]!=235||tri_sy[0]!=105||tri_depth[0]!=1540)return 16;
 if(tri_sx[4]!=15||tri_sy[4]!=234||tri_depth[4]!=3088)return 17;
 if(dot_stride_wrap(1,0,1)!=-3550||dot_stride_wrap(2,0,1)!=2400)return 18;
 if(quad_ram_dot(0,1,2,3)!=4854||quad_ram_dot(3,2,1,0)!=-3588)return 19;
 {
  unsigned buf[48], i;
  unsigned char bytes2[2];
  for(i=0;i<48;++i)buf[i]=(i<8u?0x8001u:0u);
  if(switch_loop_carry(0,buf,5u)!=75u||buf[8]!=5u||buf[15]!=12u||buf[0]!=0x8005u||buf[7]!=0x800Du)return 20;
  if(switch_loop_carry(1,buf,3u)!=44u||buf[0]!=8u||buf[3]!=14u)return 21;
  pointer_chained_offsets(buf,1u);
  if(buf[12]!=11u||buf[13]!=22u||buf[45]!=33u)return 22;
  bytes2[0]=4u;bytes2[1]=4u;
  if(byte_cmp_nomask(bytes2,5u)!=1||byte_cmp_nomask(bytes2,4u)!=0)return 23;
  {
   unsigned char pbytes[4]={0x12u,0x34u,0x56u,0x78u};
   unsigned fwords[4]={0xABCDu,0x1234u,0x5678u,0x00FFu};
   unsigned res=ipa_run(pbytes,(const unsigned * __far)fwords,2u,2u);
   if(res!=((0x5678u&0x3fu)<<6u))return 24;
   if(ipa_out[4]!=0x3f69u||ipa_out[5]!=0x3f68u||ipa_out[12]!=0x3f6bu||ipa_out[13]!=0x3f6cu)return 25;
  }
  {
   unsigned k,want=0;
   for(k=0;k<16u;++k){mul_a[k]=(unsigned char)(k*13u+7u);mul_b[k]=(unsigned char)(k*9u+3u);want+=(unsigned)mul_a[k]*mul_b[k];}
   if(u8_dot_retained()!=want||u8_dot_dynamic(16u)!=want||u8_dot_dynamic(0u)!=0u)return 26;
   if(u8_mul_compound(11u,13u,5u)!=((unsigned)mul_b[5]*(unsigned char)(mul_a[5]*13u)+11u*13u))return 27;
   for(k=0;k<16u;++k){mul_a[k]=0xffu;mul_b[k]=0u;}
   if(byte_bit_ops(32u)!=256u||mul_a[0]!=0u||mul_a[3]!=0u||mul_b[0]!=0xffu||mul_b[3]!=0xffu)return 28;
   if(word_sign_branch(0xABCDu,4u)!=0x1D9Au||word_sign_branch(0x1234u,4u)!=0x3361u)return 29;
   if(long_shift_xor(0x12345678UL,0xA5u,3u)!=0x6789005BUL)return 30;
   for(k=0;k<32u;++k)red_words[k]=k*37u+1u;
   if(sum_words_unrolled()!=18384u||xor_words_rolled(red_words,32u)!=32u)return 31;
  }
 }
 return 0;
}
'''

FIXED_KERNELS=r'''
struct ByteFields { unsigned char bytes[9]; _Bool flag; };
struct ByteFields fields;
extern volatile unsigned port_word;
extern unsigned source_word;
int side_once(void);
void projected(unsigned word, unsigned long wide){
 fields.bytes[0]&=0xf7;
 fields.bytes[0]|=(word&0x0800u)>>8;
 fields.bytes[1]^=(unsigned char)(wide>>16);
 fields.bytes[2]=(unsigned char)source_word;
 fields.bytes[7]=(unsigned char)word;
}
void byte_fallbacks(unsigned word,signed char small){
 fields.bytes[3]=0x10;
 fields.bytes[3]|=(unsigned)(int)small>>8;
 fields.bytes[4]=(unsigned char)word>>8;
 fields.bytes[5]|=side_once();
 fields.bytes[6]|=port_word>>8;
 fields.flag|=2u;
}
struct Stream { unsigned char bytes[12]; } stream;
int guarded_pair(int first,int second,int cap){
 int values[3], bounds[3];
 unsigned char i;
 values[1]=first; values[2]=second;
 bounds[1]=first+2; bounds[2]=second-1;
 for(i=1;i<3;i++){
  if(values[i]<0||bounds[i]>cap){stream.bytes[i*3]=0xfe;stream.bytes[i*3+1]=0;}
  else{stream.bytes[i*3]=(unsigned char)values[i];stream.bytes[i*3+1]=(unsigned char)bounds[i];}
  stream.bytes[i*3+2]=(unsigned char)(values[i]+bounds[i]);
 }
 return i;
}
int descending_pair(int a,int b){
 int u[3],v[3];
 unsigned char i;
 u[1]=a;u[2]=b;v[1]=b;v[2]=a;
 for(i=2;i>0;--i){
  stream.bytes[i*2]=(unsigned char)u[i];
  stream.bytes[i*2+1]=(unsigned char)v[i];
 }
 return i;
}
int early_exit(int a,int b){
 int u[3],v[3];
 unsigned char i;
 u[1]=a;u[2]=b;v[1]=b;v[2]=a;
 for(i=1;i<3;++i){
  if(u[i]<0)break;
  stream.bytes[i*2]=(unsigned char)u[i];
  stream.bytes[i*2+1]=(unsigned char)v[i];
 }
 return i;
}
int local_rows(int first,int second){
 int rows[2][2],(*p)[2]=rows,i,total=0;
 rows[0][1]=first;rows[1][1]=second;
 for(i=0;i<2;++i)total+=p[i][1];
 return total;
}
int successive_values(int start){
 int values[3],i;
 for(i=0;i<3;++i)values[i]=start++;
 return values[0]-values[1]+values[2]+start;
}
void check_miss(void);
int descending_checks(int first,int middle,int last){
 int values[3],i;
 values[0]=first;values[1]=middle;values[2]=last;
 for(i=2;i>=0;--i)if(values[i]!=i)check_miss();
 return i;
}
'''

FIXED_DRIVER=r'''
struct ByteFields { unsigned char bytes[9]; _Bool flag; };
extern struct ByteFields fields;
struct Stream { unsigned char bytes[12]; };
extern struct Stream stream;
volatile unsigned port_word;
unsigned source_word;
int calls;
int side_once(void){++calls;return 2;}
unsigned compound_array[1]={2};
long compound_wide=5;
unsigned compound_rhs(void){compound_array[0]|=128;return 1;}
long compound_wide_rhs(void){compound_wide=100;return 19;}
void compound_indirect(unsigned *p){*p|=compound_rhs();}
int misses;
void check_miss(void){++misses;}
void projected(unsigned,unsigned long);void byte_fallbacks(unsigned,signed char);
int guarded_pair(int,int,int);int descending_pair(int,int);int early_exit(int,int);
int local_rows(int,int);
int successive_values(int);
int descending_checks(int,int,int);
int main(void){
 fields.bytes[0]=0xb3;fields.bytes[1]=0xa7;source_word=0x7311u;
 projected(0x0853u,0x005a4321UL);
 if(fields.bytes[0]!=0xbb||fields.bytes[1]!=0xfd||fields.bytes[2]!=0x11||fields.bytes[7]!=0x53)return 1;
 source_word=0x2223u;
 projected(0x125au,0x00ff0000UL);
 if(fields.bytes[0]!=0xb3||fields.bytes[1]!=2||fields.bytes[2]!=0x23||fields.bytes[7]!=0x5a)return 2;
 fields.bytes[4]=0xff;fields.bytes[5]=0x40;fields.bytes[6]=3;port_word=0x8000u;
 byte_fallbacks(0xab12u,-1);
 if(fields.bytes[3]!=255||fields.bytes[4]!=0||fields.bytes[5]!=0x42||
    fields.bytes[6]!=0x83||!fields.flag||calls!=1)return 3;
 if(guarded_pair(4,9,7)!=3||stream.bytes[3]!=4||stream.bytes[4]!=6||stream.bytes[5]!=10||
    stream.bytes[6]!=0xfe||stream.bytes[7]!=0||stream.bytes[8]!=17)return 4;
 if(descending_pair(5,8)!=0||stream.bytes[2]!=5||stream.bytes[3]!=8||
    stream.bytes[4]!=8||stream.bytes[5]!=5)return 5;
 if(early_exit(3,-7)!=2||stream.bytes[2]!=3||stream.bytes[3]!=249||
    stream.bytes[4]!=8||stream.bytes[5]!=5)return 6;
 if(local_rows(7,-12)!=-5||local_rows(3,17)!=20)return 7;
 if(successive_values(10)!=24||successive_values(-5)!=-6)return 8;
 if(descending_checks(0,-1,2)!=-1||misses!=1)return 9;
 if(descending_checks(7,1,9)!=-1||misses!=3)return 10;
 compound_array[0]|=compound_rhs();
 if(compound_array[0]!=131)return 11;
 compound_array[0]=2;compound_indirect(compound_array);
 if(compound_array[0]!=131)return 12;
 compound_wide-=compound_wide_rhs();
 if(compound_wide!=81)return 13;
 return 0;
}
'''


def build(mode,kernels,driver):
    directory=OUT/mode;directory.mkdir(parents=True,exist_ok=True);c.OUT=directory
    flags=['--no-body-optimizations','--no-strength-reduction','--no-dp-homes','--no-line-passes'] if mode.endswith('fallback') else []
    path=directory/'kernels.c';path.write_text(kernels)
    c.run([ROOT/'build/zicc.exe',path,'-o',path.with_suffix('.s'),*flags])
    c.run([c.CC65/'ca65.exe','--cpu','65816','-g','-o',path.with_suffix('.o'),path.with_suffix('.s')])
    workspace=directory/'workspace.s';workspace.write_text('.exportzp __arith_lhs,__arith_rhs\n.segment "DP_SCRATCH": zeropage\n__arith_lhs:.res 4\n__arith_rhs:.res 28\n')
    c.run([c.CC65/'ca65.exe','-o',workspace.with_suffix('.o'),workspace])
    _,rom,sy=c.compile_case('driver',driver,extra_objects=[path.with_suffix('.o'),workspace.with_suffix('.o'),ROOT/'build/integers.o',ROOT/'build/libc.a'],flags=flags)
    return directory,rom,sy,path.with_suffix('.s').read_text()


def run(directory,rom,sy,seed='',expect_calls=None,custom=None,start_flag=None):
    script='''local function check(ok,msg)if not ok then emu.breakExecution();error(msg or 'check')end end
local calls={}
'''
    if expect_calls:
        for name,count in expect_calls.items():
            script+=f"calls['{name}']=0;\n"
            entries=[sy[name]]+[a for label,a in sy.items() if label.startswith('_inlined_') and label.endswith('_'+name)]
            for address in entries:script+=f"emu.addMemoryCallback(function()calls['{name}']=calls['{name}']+1 end,emu.callbackType.exec,{address},{address})\n"
    if start_flag:
        address=sy[start_flag]
        script+=f"""local started=false
emu.addMemoryCallback(function()
 if not started then
  started=true
  emu.write({address & 0x1ffff},1,emu.memType.snesWorkRam)
 end
end,emu.callbackType.read,{address},{address})
"""
    script+=f'''emu.addMemoryCallback(function()
{seed}
end,emu.callbackType.exec,{sy['main']},{sy['main']})
emu.addMemoryCallback(function()
 local s=emu.getState();check(s['cpu.a']==0,'return '..s['cpu.a'])
 check(s['cpu.sp']==0x4ff and s['cpu.d']==0 and s['cpu.dbr']==0x7e and s['cpu.y']==0,'ABI')
'''
    if expect_calls:
        for name,count in expect_calls.items():script+=f"check(calls['{name}']=={count},'{name} count '..calls['{name}'])\n"
    script+=f"emu.log('PASS body codegen');emu.breakExecution()end,emu.callbackType.exec,{sy['main_exit']},{sy['main_exit']})\n"
    if custom:script=custom
    home=directory/'run';home.mkdir(exist_ok=True);lua=home/'check.lua';lua.write_text(script)
    subprocess.run([sys.executable,__file__,'--worker',str(rom),str(home)],check=True)
    return hashlib.sha256(rom.read_bytes()).hexdigest()


def main():
    all_cases=['shapes','general','fixed-addresses','boundaries','span','long-call','bytes','overrides','divergence']
    parser=argparse.ArgumentParser();parser.add_argument('--worker',nargs=2);parser.add_argument('--case',action='append',choices=all_cases);parser.add_argument('--mode',action='append',choices=['optimized','fallback']);args=parser.parse_args()
    if args.worker:
        rom,home=map(Path,args.worker);lua=home/'check.lua';core=Core(home,cache=False)
        try:core.load(rom,lua,lua.read_text());core.start();log=core.wait_for('PASS body codegen',60)
        finally:core.close_with_log(home/'check.log')
        assert 'FAIL' not in log;return
    modes=args.mode or ['optimized','fallback'];cases=args.case or all_cases
    OUT.mkdir(parents=True,exist_ok=True);report={}
    if 'shapes' in cases:
        host=OUT/'reference.c';host.write_text((KERNELS+'\n'+DRIVER).replace(' __far','').replace('sequence!=12','(sequence!=12&&sequence!=21)'))
        exe=host.with_suffix('.exe')
        c.run([ROOT/'tools/msvc.cmd','/nologo','/std:c17','/O2','/Fo'+str(host.with_suffix('.obj')),'/Fe'+str(exe),host])
        assert subprocess.run([str(exe)]).returncode==0,'independent host reference'
    for mode in modes if 'shapes' in cases else []:
        directory,rom,sy,assembly=build(mode,KERNELS,DRIVER)
        report[mode]=run(directory,rom,sy,expect_calls={'relative':1,'rectangular':2,'retry':1,'progress':1,'compare_near':3,'compare_far':1,'compare_effects':1,'predicate':4})
        if mode=='optimized':
            post_branch=assembly.split('_post_branch:',1)[1].split('__size_post_branch',1)[0]
            assert not re.search(r'^    b(?:cc|cs|eq|mi|ne|pl|vc|vs) ',post_branch,re.M),post_branch
            post_global=assembly.split('_post_global:',1)[1].split('__size_post_global',1)[0]
            assert not re.search(r'^    b(?:cc|cs|eq|mi|ne|pl|vc|vs) ',post_global,re.M),post_global
            sums=assembly.split('_stack_sums:',1)[1].split('__size_stack_sums',1)[0]
            assert 'adc #$4C00' in sums and sums.count('adc #$0400')==3
            assert '; discarded byte narrowed difference' in assembly.split('_narrowed_step:',1)[1].split('__size_narrowed_step',1)[0]
            assert '; discarded byte narrowed difference' not in assembly.split('_boolean_difference:',1)[1].split('__size_boolean_difference',1)[0]
            assert '; discarded byte narrowed difference' not in assembly.split('_boolean_target:',1)[1].split('__size_boolean_target',1)[0]
            relative=assembly.split('_relative:',1)[1].split('__size_relative',1)[0]
            retry=assembly.split('_retry:',1)[1].split('__size_retry',1)[0]
            assert 'affine loop:' not in relative and 'saved DP counter:' not in relative
            assert 'cg_' not in relative
            short_loop=assembly.split('_short_if_loop:',1)[1].split('__size_short_if_loop',1)[0]
            assert 'loop lowering:' not in short_loop,short_loop
            single=assembly.split('_single_trip_exit:',1)[1].split('__size_single_trip_exit',1)[0]
            assert 'loop lowering:' not in single,single
            conditional=assembly.split('_conditional_bound:',1)[1].split('__size_conditional_bound',1)[0]
            assert 'loop lowering:' in conditional,conditional
            copied=assembly.split('_copy_bytes:',1)[1].split('__size_copy_bytes',1)[0]
            assert 'loop lowering:' not in copied and 'lda a:$0003,x' in copied,copied
            rows=assembly.split('_sum_rows:',1)[1].split('__size_sum_rows',1)[0]
            assert 'loop lowering:' not in rows and '__fix32' not in rows,rows
            assert '__near_strcmp_' in assembly and '#$004A' not in retry and '#$0052' not in retry
            assert '__near_strcmp_' not in assembly.split('_compare_far:',1)[1].split('__size_compare_far',1)[0]
            assert 'cg_' in assembly.split('_unsigned_step:',1)[1].split('__size_unsigned_step',1)[0]
            assert 'direct discarded byte update' in assembly
            assert '; short-circuit immutable ROM bytes' in assembly.split('_window_start:',1)[1].split('__size_window_start',1)[0]
            assert '; short-circuit immutable ROM bytes' not in assembly.split('_signed_window_start:',1)[1].split('__size_signed_window_start',1)[0]
            item_loop=assembly.split('_item_alias_loop:',1)[1].split('__size_item_alias_loop',1)[0]
            assert 'retained loop indices:' in item_loop
            assert 'retained loop indices:' not in assembly.split('_item_alias_changed_index:',1)[1].split('__size_item_alias_changed_index',1)[0]
        else:assert '__near_strcmp_' not in assembly
        print('PASS body shapes',mode,flush=True)
    for mode in modes if 'general' in cases else []:
        directory,rom,sy,assembly=build('general-'+mode,GENERAL_KERNELS,GENERAL_DRIVER)
        report['general-'+mode]=run(directory,rom,sy)
        if mode=='optimized':
            def function(name):
                return assembly.split(f'_{name}:',1)[1].split(f'__size_{name}',1)[0]
            fixed=function('fixed_exit')
            assert 'inlined call: fixed_exit kernels__set_value' in fixed and 'inlined call: fixed_exit kernels__fill_pair' in fixed
            assert 'a:.loword(_fixed_grid+$0050)' in fixed and '__mul16' not in fixed
            assert '__sdiv16' not in function('dead_late')
            assert all('saved wide DP counter:' in function(name) for name in ('wide_unsigned','wide_signed'))
            assert 'saved wide DP counter:' not in function('wide_observed')
            pack=function('pack_scaled_dot')
            assert '__zicc_pack_coeff_' in pack and '__mul32' not in pack and '__sdiv32' not in pack and 'adc #$007E' in pack
            assert '; retained loop indices: X=stride 4' in pack and '; fused adjacent RAM byte stores' in pack
            assert all(f'_packed_out+${off:04X})' in pack for off in (0,2,3))
            dot_y=function('dot_y_scratch')
            assert '    tay\n' in dot_y and '    tya\n' in dot_y and '    sep #$20\n' not in dot_y,dot_y
            assert '    xba\n' not in dot_y.split('; loop lowering:',1)[1],dot_y
            tri_proj=function('tri_project_loop')
            assert '; retained loop indices: X=stride 3, Y=counter' in tri_proj,tri_proj
            assert '; retained y-cursor: _tri_depth+$0000 -> __arith_lhs+' in tri_proj,tri_proj
            assert '(__arith_lhs+' in tri_proj and tri_proj.count('    sep #$20\n')==2,tri_proj
            assert '    sty z:__arith_lhs+' in tri_proj and '    ldy z:__arith_lhs+' in tri_proj,tri_proj
            assert 'inlined call: tri_project_loop kernels__tri_div16' in tri_proj,tri_proj
            assert 'eor #$1000' not in tri_proj,tri_proj
            quad_dot=function('quad_ram_dot')
            assert '    sta f:$004202\n' in quad_dot and '    sta f:$004203\n' in quad_dot,quad_dot
            assert '__zicc_smul8_' in function('bounded_smul8')
            assert '__zicc_object_size_kernels__ro_pairs = 16' in assembly
            sw=function('switch_loop_carry')
            assert '; ADC cannot carry' in sw and '    phx\n' not in sw and '    tsc\n' not in sw,sw
            pc=function('pointer_chained_offsets')
            assert pc.count('    asl a\n')==2,pc
            bc=function('byte_cmp_nomask')
            assert '    sep #$20\n.a8\n    lda a:$0000,x\n    cmp ' in bc,bc
            ic=function('kernels__ipa_cell')
            assert '; bounded expression lookup' in ic,ic
            assert 'a:.loword(_ipa_out+$0010),x' in ic,ic
            assert '    sta [__arith_lhs]' not in ic and '[__arith_lhs],y' not in ic,ic
            fs=function('kernels__ipa_far_spill')
            assert '    tsc\n    tay\n' not in fs and ',s\n' in fs,fs
            for name in ('u8_dot_retained','u8_dot_dynamic','u8_mul_compound'):
                fn=function(name)
                read_op='adc' if name=='u8_dot_retained' else 'lda'
                assert all(op in fn for op in ('sta f:$004202','sta f:$004203',f'{read_op} f:$004216'))
                assert '__mul8' not in fn,fn
            retained_dot=function('u8_dot_retained')
            assert all(op in retained_dot for op in ('; register unsigned byte product sum',
                'ldx #$000F','dex','bpl','tay')),retained_dot
            bcl=function('byte_bit_clear')
            assert '    phx\n' not in bcl and '    pha\n' not in bcl and 'a:.loword(_mul_a+$0000),y' in bcl,bcl
            bck=function('byte_bit_check')
            assert '    phx\n' not in bck and '    pha\n' not in bck and 'a:.loword(_mul_b+$0000),y' in bck,bck
            bbo=function('byte_bit_ops')
            assert '    lsr a\n' in bbo and '    cmp #$8000\n' not in bbo,bbo
            wsb=function('word_sign_branch')
            assert '    and #$8000\n' not in wsb and ('    bpl ' in wsb or '    bmi ' in wsb),wsb
            lsx=function('long_shift_xor')
            assert all(op in lsx for op in ('; carry-tested shift recurrence',
                'asl a','rol z:__arith_lhs','eor #$1DB7','eor #$04C1')),lsx
            swu=function('sum_words_unrolled')
            assert '; unrolled retained loop: 8x' in swu and swu.count('    adc a:.loword(_red_words')==8,swu
        else:
            assert 'saved wide DP counter:' not in assembly
        print('PASS short-loop facts, call bindings, dead definitions and wide counters',mode,flush=True)
    for mode in modes if 'fixed-addresses' in cases else []:
        directory,rom,sy,assembly=build('fixed-addresses-'+mode,FIXED_KERNELS,FIXED_DRIVER)
        report['fixed-addresses-'+mode]=run(directory,rom,sy,expect_calls={'side_once':1})
        def function(name):
            return assembly.split(f'_{name}:',1)[1].split(f'__size_{name}',1)[0]
        if mode=='optimized':
            assert function('projected').count('; fixed byte assignment')==4
            fallbacks=function('byte_fallbacks')
            before_call,after_call=fallbacks.split('jsr .loword(_side_once)',1)
            assert '; fixed byte assignment' not in before_call
            assert after_call.count('; fixed byte assignment')==1
            for name,slots in [('guarded_pair',(3,6)),('descending_pair',(2,4))]:
                text=function(name)
                assert all(f'a:.loword(_stream+${slot:04X})' in text for slot in slots), name
                assert not re.search(r'_stream[^\n]*,x',text),name
            assert re.search(r'_stream[^\n]*,x',function('early_exit'))
            assert 'loop lowering:' not in function('local_rows')
            assert 'loop lowering:' not in function('successive_values')
            assert 'loop lowering:' not in function('descending_checks')
            assert function('descending_checks').count('jsr .loword(_check_miss)')==3
        else:
            assert '; fixed byte assignment' not in assembly
        print('PASS fixed byte projections and short indexed loops',mode,flush=True)
    boundary_driver='''unsigned wrapping(unsigned *);int compare_near(const char *,const char *);int compare_far(const char * __far,const char * __far);
int main(void){if(wrapping((unsigned *)65535u)!=0x4321u)return 1;
if(compare_near((char *)65534u,(char *)0x7000)!=0)return 2;
if(compare_far((const char * __far)0x7f6000UL,(const char * __far)0x7f6010UL)>=0)return 3;return 0;}'''
    seed='''emu.write(1,0x21,emu.memType.snesWorkRam);emu.write(2,0x43,emu.memType.snesWorkRam)
emu.write(0xfffe,65,emu.memType.snesWorkRam);emu.write(0xffff,66,emu.memType.snesWorkRam)
emu.write(0x10000,67,emu.memType.snesWorkRam);emu.write(0x10001,0,emu.memType.snesWorkRam)
for i,b in ipairs({65,66,67,0})do emu.write(0x6fff+i,b,emu.memType.snesWorkRam)end
emu.write(0x16000,65,emu.memType.snesWorkRam);emu.write(0x16001,0,emu.memType.snesWorkRam)
emu.write(0x16010,66,emu.memType.snesWorkRam);emu.write(0x16011,0,emu.memType.snesWorkRam)
'''
    boundary_kernels='''#include <string.h>
unsigned wrapping(unsigned *p){return *(p+1);}
int compare_near(const char *a,const char *b){return strcmp(a,b);}
int compare_far(const char * __far a,const char * __far b){return strcmp(a,b);}
'''
    for mode in modes if 'boundaries' in cases else []:
        directory,rom,sy,_=build('boundary-'+mode,boundary_kernels,boundary_driver)
        report['boundary-'+mode]=run(directory,rom,sy,seed)
        print('PASS near pointer and string bank crossings',mode,flush=True)
    long_driver='int compare_near(const char *,const char *);int main(void){return compare_near((char *)0x500,(char *)0x500)!=0;}'
    for mode in modes if 'span' in cases else []:
        directory,rom,sy,_=build('long-'+mode,boundary_kernels,long_driver)
        seed='for i=0x500,0x104ff do emu.write(i,65,emu.memType.snesWorkRam)end;emu.write(0x10500,66,emu.memType.snesWorkRam);emu.write(0x10501,0,emu.memType.snesWorkRam)'
        report['span-'+mode]=run(directory,rom,sy,seed)
        print('PASS 65536-byte strcmp progression',mode,flush=True)
    if 'long-call' in cases:
        directory=OUT/'long-call';directory.mkdir(exist_ok=True)
        kernels=directory/'kernels.c';kernels.write_text(boundary_kernels)
        driver=directory/'driver.c';driver.write_text(long_driver)
        stem=directory/'program'
        c.run([sys.executable,ROOT/'tools/build-rom.py',kernels,driver,'--stage','4','-o',stem.with_suffix('.raw')])
        c.run([ROOT/'build/romtool.exe',stem.with_suffix('.raw'),stem.with_suffix('.sfc'),ROOT/'tests/title.txt'])
        sy={n.removeprefix('_'):int(a,16) for a,n in re.findall(r'^al (\w+) \.(\S+)$',stem.with_suffix('.labels').read_text(),re.M)}
        report['long-call']=run(directory,stem.with_suffix('.sfc'),sy,seed='for i=0x500,0x104ff do emu.write(i,65,emu.memType.snesWorkRam)end;emu.write(0x10500,66,emu.memType.snesWorkRam);emu.write(0x10501,0,emu.memType.snesWorkRam)')
        print('PASS long-call/long-return library adapter',flush=True)
    for mode in modes if 'bytes' in cases else []:
        kernels='int byte_rel(unsigned char a,unsigned char b){return (a<b)|((a<=b)<<1)|((a>b)<<2)|((a>=b)<<3)|((a==b)<<4)|((a!=b)<<5);}'
        # The core can advance during ROM loading. Gate the loop on a bus
        # read that can be released only after the call counter is installed
        driver='''volatile unsigned char byte_ready;
int byte_rel(unsigned char,unsigned char);int main(void){unsigned a,b;int want;while(!byte_ready){}for(a=0;a<256u;a++)for(b=0;b<256u;b++){
want=(a<b)|((a<=b)<<1)|((a>b)<<2)|((a>=b)<<3)|((a==b)<<4)|((a!=b)<<5);if(byte_rel((unsigned char)a,(unsigned char)b)!=want)return 1;}return 0;}'''
        directory,rom,sy,assembly=build('bytes-'+mode,kernels,driver)
        if mode=='optimized':assert 'unsigned byte relation' in assembly
        report['bytes-'+mode]=run(directory,rom,sy,expect_calls={'byte_rel':65536},start_flag='byte_ready')
        print('PASS all six byte relations, 65536 opaque pairs',mode,flush=True)
    if 'overrides' in cases:
        fixtures=[
            ('definition','''#include <string.h>
int calls;int strcmp(const char * __far a,const char * __far b){calls++;return 23;}
int compare_custom(char *a,char *b){return strcmp(a,b);}''',
             'extern int calls;int compare_custom(char *,char *);char a[2],b[2];int main(void){return compare_custom(a,b)!=23||calls!=1;}'),
            ('signature','''int strcmp(char ** __far,char ** __far);
int compare_custom(char **a,char **b){return strcmp(a,b);}''',
             'int calls;int compare_custom(char **,char **);int strcmp(char ** __far a,char ** __far b){calls++;return 37;}int main(void){return compare_custom((char **)0x7000,(char **)0x7100)!=37||calls!=1;}')]
        for name,kernels,driver in fixtures:
            driver='volatile unsigned char override_ready;\n'+driver.replace(
                'int main(void){','int main(void){while(!override_ready){}')
            directory,rom,sy,assembly=build('override-'+name,kernels,driver)
            assert '__near_strcmp_' not in assembly
            report['override-'+name]=run(directory,rom,sy,expect_calls={'strcmp':1,'compare_custom':1},start_flag='override_ready')
            print('PASS standard-library selection fallback',name,flush=True)
    for mode in modes if 'divergence' in cases else []:
        fixtures=[('unsigned',
          'int spin(volatile unsigned *out,int base){int i;for(i=base;i<=base;i+=1u)*out=(unsigned)i;return i;}',
          'int spin(volatile unsigned *,int);volatile unsigned output;int main(void){return spin(&output,32767);}') ,
          ('wide','int predicate(volatile int *);int output;int spin(volatile int *state){int i=4;while(i<=65540L)if(predicate(state)){output=i;i+=1;}return i;}',
          'int spin(volatile int *);int predicate(volatile int *state){return (*state)--==0;}int main(void){volatile int state=0;return spin(&state);}')]
        for name,kernels,driver in fixtures:
            directory,rom,sy,_=build('divergence-'+name+'-'+mode,kernels,driver)
            common=f'''local function check(ok,msg)if not ok then emu.breakExecution();error(msg)end end
emu.addMemoryCallback(function()check(false,'nonterminating loop was removed')end,emu.callbackType.exec,{sy['main_exit']},{sy['main_exit']})
local count=0;local first_sp=nil
local armed=false
emu.addMemoryCallback(function()armed=true end,emu.callbackType.exec,{sy['spin']},{sy['spin']})
'''
            if name=='unsigned':
                address=0x7e0000|(sy['output']&65535)
                custom=common+f'''emu.addMemoryCallback(function(a,v)
 if not armed then return end
 count=count+1;local s=emu.getState();first_sp=first_sp or s['cpu.sp']
 local word=(v<<8)|emu.read({address},emu.memType.snesMemory,false)
 check(word==32766+count,'unsigned step wrap '..word);check(s['cpu.sp']==first_sp,'loop stack')
 if count==3 then emu.log('PASS body codegen');emu.breakExecution()end
end,emu.callbackType.write,{address+1},{address+1})
'''
            else:
                custom=common+f'''emu.addMemoryCallback(function()
 count=count+1;local s=emu.getState();first_sp=first_sp or s['cpu.sp']
 check(s['cpu.sp']==first_sp,'retry stack')
 if count==3 then
  check(emu.read16(s['cpu.x']|0x7e0000,emu.memType.snesMemory,false)==65534,'retry state')
  check(emu.read16({sy['output']},emu.memType.snesMemory,false)==4,'retry output')
  emu.log('PASS body codegen');emu.breakExecution()
 end
end,emu.callbackType.exec,{sy['predicate']},{sy['predicate']})
'''
            report['divergence-'+name+'-'+mode]=run(directory,rom,sy,custom=custom)
            print('PASS bounded nontermination witness',name,mode,flush=True)
    report['inputs']={str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in [ROOT/'build/zicc.exe',Path(__file__),ROOT/'src/codegen/body_opt.inc',ROOT/'src/codegen/near_libcalls.inc']}
    (OUT/'results.json').write_text(json.dumps(report,indent=2)+'\n')


if __name__=='__main__':main()
