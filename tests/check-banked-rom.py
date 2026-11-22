"""Verify HiROM placement stages and explicit ExHiROM images."""
import os
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import sys
import subprocess
import tempfile

ROOT=Path(__file__).resolve().parents[1]
OUT=Path(os.environ.get('ZICC_LOGS_DIR', 'logs')).resolve() / 'banked-rom-check'
spec=importlib.util.spec_from_file_location('support',ROOT/'tests/check-compiler.py')
support=importlib.util.module_from_spec(spec);spec.loader.exec_module(support)
spec=importlib.util.spec_from_file_location('build_rom',ROOT/'tools/build-rom.py')
builder=importlib.util.module_from_spec(spec);sys.modules[spec.name]=builder;spec.loader.exec_module(builder)

SOURCE=r'''
#include <string.h>
#include <stdlib.h>
char * __far dec_format(unsigned long);
char * __far dec_format_spec(unsigned long,int,int);
const unsigned char asset[]={
#embed "resource.bin"
};
unsigned char initialized[]={1,127,128,255};
volatile unsigned calls;
__noinline int sum(int a,int b,int c,int d){calls++;return a+b+c+d;}
long wide(long a,long b){return a+b;}
int recursive(int n){if(n<=1)return n;return recursive(n-1)+recursive(n-2);}
struct R {short quantity;unsigned long price;};
const struct R products[2]={{-3,10},{4,20}};
unsigned long reduce(const struct R * __far p,int n){unsigned long total=0;while(n>0){total+=p->quantity*p->price;p++;n--;}return total;}
int scalar_condition(int a,int b,int *p){if(a<0)*p=b+(a&7);else *p=a-b;return b;}
int alias_store(int a,int b,int *p){*p=(*p+a)^b;return *p;}
void pointer_last(int a,int b,int c,int d,int e,int f,int g,int *p){int t=(a+b)^(c-d);*p=t+e+f+g;}
unsigned destination[2];
__noinline void read_pair(unsigned i) {
 unsigned *out=destination;
 out[0]=*(const unsigned * __far)(asset+2+i);
 out[1]=*(const unsigned * __far)(asset+4+i);
}
__noinline unsigned read_signed(int i) {
 return *(const unsigned * __far)(asset+4+i);
}
struct Words { unsigned a,b; };
__noinline unsigned cross_field(const struct Words * __far p) {
 return p->b;
}
__noinline unsigned far_record(const struct Words * __far p,unsigned i) {
 return p[i].b;
}
const struct Words words[2]={{2,3},{5,7}};
__noinline const struct Words * __far record_address(unsigned i) {
 return words+i;
}
__noinline int nonnull(const struct Words * __far p) {
 if(p!=0)return 1;
 return 0;
}
__noinline const struct Words * __far advance_record(const struct Words * __far p) {
 p++;
 return p;
}
__noinline int shifted_position(int x) { return (x>>4)-3; }
unsigned long projection_source;
__noinline unsigned char projection_byte(void) {
 return (projection_source>>24)&255UL;
}
__noinline unsigned projection_sub(void) {
 return (unsigned)((projection_source>>16)-1UL);
}
struct Entry { unsigned x,y; };
struct Entry entries[3];
__noinline int same_y(struct Entry *p,unsigned y) {
 if(y==p->y)return 1;
 return 0;
}
struct Entry *entries_end;
__noinline void tail_a(struct Entry *p) { p->y=123; }
__noinline void tail_b(struct Entry *p) { p->y=456; }
__noinline void clear_entry(struct Entry *p) {
 p->y=0;
 if(p->x!=1)tail_a(p);
}
struct Counter { unsigned state; unsigned char ticks; };
__noinline void reset_counter(struct Counter *p,unsigned state) {
 p->state=state;
 p->ticks=5;
}
__noinline void count_counter(struct Counter *p,unsigned state) {
 if(state!=p->state||(p->ticks!=0&&--p->ticks==0))reset_counter(p,state);
 p->state++;
}
struct Counter counter;
__noinline void record_move(void) { calls++; }
__noinline void move_entry(struct Entry *p,int dx,int dy) {
 unsigned x=p->x+dx, y=p->y+dy;
 if(dx!=0)record_move();
 if(dy!=0)record_move();
 p->x=x;
 p->y=y;
}
__noinline void observe_zero_move(struct Entry *p,int dx,int dy) {
 unsigned x=p->x+dx, y=p->y+dy;
 if(dx==0)record_move();
 p->x=x;
 p->y=y;
}
__noinline unsigned check_extent(const struct Entry *p,unsigned limit) {
 unsigned end=p->y+1;
 if(p->x>=limit||end>=limit)return 99;
 return end;
}
__noinline void tail_wrapper(unsigned offset) {
 struct Entry *p=(struct Entry*)((unsigned char*)entries+offset);
 switch(p->x) {
 case 30: tail_a(p); break;
 case 33: tail_b(p); break;
 }
}
__noinline void switch_pointer(unsigned offset) {
 struct Entry *p=(struct Entry*)((unsigned char*)entries+offset);
 switch(offset) {
 case 0: tail_a(p); break;
 case sizeof(struct Entry): tail_b(p); break;
 }
}
extern unsigned tail_observed;
extern unsigned *tail_published;
void tail_read_byte(const unsigned char *p);
unsigned tail_read_word(const unsigned *p);
void tail_read_published(void);
__noinline void tail_local_array(unsigned char value) {
 unsigned char buffer[12];
 buffer[10]=value;
 tail_read_byte(buffer+10);
}
__noinline void tail_local_member(unsigned char value) {
 struct TailBuffer { unsigned prefix; unsigned char bytes[4]; } buffer;
 buffer.bytes[3]=value;
 tail_read_byte(buffer.bytes+3);
}
__noinline unsigned tail_local_scalar(unsigned value) {
 unsigned local=value;
 unsigned *alias=&local;
 return tail_read_word(alias);
}
__noinline void tail_publish_local(unsigned value) {
 unsigned local=value;
 tail_published=&local;
 tail_read_published();
}
__noinline void tail_forward_pointer(const unsigned char *p) {
 tail_read_byte(p);
}
struct Entry * const fixed_end=entries+3;
__noinline unsigned take(struct Entry *p) { p->x++; return p->y; }
__noinline unsigned scan(unsigned left,unsigned top,unsigned width,unsigned height) {
 struct Entry *p=entries;
 while(p!=entries_end) {
  if((unsigned)(p->x-left)<width&&(unsigned)(p->y-top)<height) {
   return take(p);
  }
  p++;
 }
 return p==entries+3?0:99;
}
__noinline unsigned scan_fixed(unsigned x) {
 struct Entry *p=entries;
 while(p!=fixed_end) {
  if(p->x==x)return p->y;
  p++;
 }
 return 0;
}
static struct RenderState { unsigned bits,count; unsigned char *output,tag; } render;
static unsigned char pixels[4];
__noinline void finish_bits(void) {
 do { render.bits >>= 2; } while (++render.count != 4);
 *render.output++ = render.tag;
}
__noinline unsigned count_rises(const int *p,const int *end) {
 int previous=*p++; unsigned count=0;
 while(p!=end) {
  int key=*p++;
  if(key>previous)count++;
  if(key<previous)count+=2;
  previous=key;
 }
 return count;
}
static unsigned read_entry(const struct Entry * __far p) { return p->y; }
__noinline unsigned near_entry(const struct Entry *p) { return read_entry(p)+1; }
static struct ByteFlags { unsigned char bits,remaining; } masks[3];
__noinline int masked_flag(unsigned index) { if(masks[index].bits&4)return 7;return 9; }
__noinline int step_byte(struct ByteFlags *p) { if(p->remaining && --p->remaining==0)return 1;return 0; }
static int depths[]={-32768,32767,32767,-1,0,-32768};
static struct ScanPoint { unsigned x,y; } scan_points[16], short_points[4];
static struct ScanPoint *scan_end, *short_end;
static unsigned scan_result;
__noinline void record_point(struct ScanPoint *p) { scan_result=p->y; }
__noinline int scan_range(unsigned x,unsigned y,unsigned w,unsigned h) {
 struct ScanPoint *p=scan_points;
 while(p!=scan_end) {
  if((unsigned)(p->x-x)<w && (unsigned)(p->y-y)<h) {record_point(p);return 1;}
  p++;
 }
 return 0;
}
__noinline int short_range(unsigned x,unsigned w) {
 struct ScanPoint *p=short_points;
 while(p!=short_end) {
  if((unsigned)(p->x-x)<w)return 1;
  p++;
 }
 return 0;
}
__noinline int checked_extent(unsigned a,unsigned b,unsigned x,unsigned y) {
 if(a<=(unsigned)(65535u-b) && (unsigned)(x-y)>(unsigned)(a+b))return 1;
 return 0;
}
static struct FramePoint { unsigned x,y; unsigned char count; } frame_point;
static unsigned frame_x,frame_y,frame_width,frame_height;
static unsigned guard_keys[2];
static const unsigned char guard_direction[4]={255,1,2,3};
static __noinline void guard_delta(struct FramePoint *p,int dx,int dy) {
 unsigned x=p->x+dx,y=p->y+dy;
 if(dx && x==12)x=p->x;
 if(dy && y==13)y=p->y;
 p->x=x;p->y=y;
}
__noinline _Bool guarded_input(struct FramePoint *p,_Bool running) {
 unsigned char facing=guard_direction[(guard_keys[0]>>8)&3];
 int dx=0,dy=0;
 if(facing!=255)p->count=facing;
 if((guard_keys[0]&256)==256)dx=running?3:2;
 if((guard_keys[0]&512)==512)dy=running?3:2;
 guard_delta(p,dx,dy);
 return dx!=0 || dy!=0;
}
__noinline unsigned collision_flags(unsigned x,unsigned y,_Bool flight) {
 unsigned mask=0;
 if((x&255)>=48)mask=1;
 if((y&255)>=48)mask|=2;
 if(flight)mask|=4;
 return mask+((x>>8)^(y>>8))*8;
}
__noinline int selected_velocity(int gap,_Bool fast) {
 int speed=fast?16:8;
 if(gap>=speed)return speed;
 if(gap<=-speed)return -speed;
 return 0;
}
extern unsigned frame_calls;
unsigned frame_probe(unsigned x,unsigned y,unsigned w,unsigned h);
_Bool frame_bool_probe(unsigned x,unsigned y,unsigned w,unsigned h);
__noinline _Bool frame_candidate(struct FramePoint *p,unsigned dx,unsigned dy,unsigned w,unsigned h) {
 unsigned x=p->x+dx,y=p->y+dy,wm=w-1,hm=h-1;
 unsigned bw=frame_width,bh=frame_height;
 _Bool hit;
 if(bw<=(unsigned)(65535u-wm) && (unsigned)(x+wm-frame_x)>(unsigned)(bw+wm))return 0;
 if(bh<=(unsigned)(65535u-hm) && (unsigned)(y+hm-frame_y)>(unsigned)(bh+hm))return 0;
 hit=frame_bool_probe(x,y,w,h);
 if(hit && p->count)p->count--;
 return hit;
}
__noinline unsigned frame_two_live(struct FramePoint *p,unsigned dx,unsigned dy,unsigned w,unsigned h) {
 unsigned x=p->x+dx,y=p->y+dy,wm=w-1,hm=h-1;
 unsigned bw=frame_width,bh=frame_height;
 unsigned char hit;
 if(bw<=(unsigned)(65535u-wm) && (unsigned)(x+wm-frame_x)>(unsigned)(bw+wm))return 0;
 if(bh<=(unsigned)(65535u-hm) && (unsigned)(y+hm-frame_y)>(unsigned)(bh+hm))return 0;
 hit=frame_probe(x,y,w,h);
 if(hit && p->count)p->count--;
 return hit+x;
}
static unsigned char lookup_bytes[4]={0,2,127,255};
__dpage unsigned char *lookup_ready;
static unsigned char generation;
__noinline unsigned byte_lookup(unsigned i) {
 unsigned char *p=lookup_ready;
 if(!p)return 65535u;
 unsigned char value=p[i];
 if(value<2)return 65535u;
 return value-2;
}
__noinline void byte_guard_store(unsigned i,unsigned char value) {
 unsigned char *p=lookup_ready;
 if(p[i]==0) {
  p[i]=value;
  calls++;
 }
}
__noinline void next_generation(void) { generation=(generation+1)&31; }
#define PROBE_LOW (*(volatile unsigned char * __far)0x7fff10ul)
#define PROBE_HIGH (*(volatile unsigned char * __far)0x7fff11ul)
__noinline int packed_guard(void) {
 unsigned value=PROBE_LOW;
 value|=(PROBE_HIGH&1)<<8;
 if(value<208)return 1;
 return 0;
}
static unsigned ring_words[8];
static unsigned char ring_bytes[20];
static unsigned ring_out_head,ring_out_tail,ring_sum;
__noinline void ring_walk(unsigned start,unsigned end) {
 unsigned head=start,tail=end,budget=6,sum=0;
 do {
  if(head==tail)break;
  unsigned item=ring_words[head];
  head=(head+1)&7;
  unsigned char *p=ring_bytes+item+4;
  unsigned char stamp=*p+1;
  if(stamp>254)continue;
  if(p[-1]==0) {
   p[-1]=stamp;
   ring_words[tail]=item-1;
   tail=(tail+1)&7;
  }
  if(p[2]==0) {
   p[2]=stamp;
   ring_words[tail]=item+2;
   tail=(tail+1)&7;
  }
  if(p[-3]==0) {
   p[-3]=stamp;
   ring_words[tail]=item-3;
   tail=(tail+1)&7;
  }
  if(p[6]==0) {
   p[6]=stamp;
   ring_words[tail]=item+6;
   tail=(tail+1)&7;
  }
  sum+=item;
 } while(--budget);
 ring_out_head=head;ring_out_tail=tail;ring_sum=sum;
}
static unsigned char search_field[8],search_taken[8];
__dpage unsigned char *search_ready;
#define BYTE_SEARCH(name, forward, reverse) \
__noinline unsigned name(unsigned index) { \
 unsigned char *field=search_ready; \
 if(!field)return 65535u; \
 unsigned char *c=field+index; \
 unsigned char here=*c; \
 if(here<4)return 65535u; \
 unsigned char closer=here-1; \
 int side=(index&1)?-1:1; \
 unsigned char *taken=search_taken+index; \
 if(c[side]==closer&&taken[side]==0)return forward; \
 if(c[-side]==closer&&taken[-side]==0)return reverse; \
 return 65535u; \
}
BYTE_SEARCH(search_index, index+side, index-side)
BYTE_SEARCH(search_code, 11u, 12u)
__noinline unsigned masked_relations(unsigned a,unsigned b) {
 unsigned result=0;
 if(a<(b&31))result|=1;
 if(a<=(b&31))result|=2;
 if(a>(b&31))result|=4;
 if(a>=(b&31))result|=8;
 if((a&31)<(b&31))result|=16;
 return result;
}
int main(void){
 char local[96];char *p;char * __far end;unsigned i;int out;
 char * __far edge=(char * __far)0x7efffeUL;
 if(sizeof(asset)!=256||initialized[2]!=128||initialized[3]!=255)return 1;
 for(i=0;i<256;i++)if(asset[i]!=(unsigned char)i)return 2;
 if(sum(11,22,33,44)!=110||calls!=1||wide(0x12345678L,0x11223344L)!=0x235689bcL)return 3;
 if(recursive(9)!=34||reduce(products,2)!=50UL)return 4;
 if(scalar_condition(-7,20,&out)!=20||out!=21)return 11;
 if(alias_store(3,7,&out)!=31||out!=31)return 12;
 pointer_last(1,2,3,4,5,6,7,&out);if(out!=14)return 13;
 strcpy(local,"0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz");
 if(local[0]!=48||local[61]!=122||local[62]!=0)return 14;
 strcpy(local,"hello");if(strcmp(local,"hello"))return 5;
 memset(local,65,12);memcpy(local+12,asset,8);memmove(local+1,local,16);
 if(local[1]!=65||local[13]!=0||local[16]!=3)return 6;
 edge[0]=21;edge[1]=22;edge[2]=23;edge[3]=24;memcpy(local,edge,4);
 if(local[0]!=21||local[1]!=22||local[2]!=23||local[3]!=24)return 10;
 p=malloc(8);if(!p)return 7;*p=23;if(*p!=23)return 8;free(p);
 if(strtod("12.5x",&end)!=12.5||*end!=120)return 9;
 if(strtod("-0x1.8p2",&end)!=-6.0||*end)return 15;
 if(strcmp(dec_format(0x7f800000UL),"inf"))return 16;
 if(strcmp(dec_format_spec(0x3fa00000UL,'e',8),"1.25000000e+00"))return 17;
 if(strcmp(dec_format_spec(0x3fa00000UL,'f',32),"1.25000000000000000000000000000000"))return 18;
 read_pair(initialized[0]+1);
 if(destination[0]!=0x0504||destination[1]!=0x0706||read_signed(-2)!=0x0302)return 19;
 entries[0].x=30;entries[0].y=50;entries[1].x=32;entries[1].y=17;
 entries_end=entries;
 if(scan(31,16,2,2)!=99)return 20;
 entries_end=entries+3;
 if(scan(31,16,2,2)!=17||entries[0].x!=30||entries[1].x!=33||scan(31,16,2,2)!=0)return 21;
 if(scan_fixed(33)!=17||scan_fixed(123)!=0)return 22;
 if(cross_field((const struct Words * __far)edge)!=0x1817)return 23;
 if(far_record((const struct Words * __far)0x7dfffeUL,0x4000)!=0x1817)return 24;
 projection_source=0xab010203UL;
 if(projection_byte()!=0xab||projection_sub()!=0xab00)return 25;
 tail_wrapper(0);tail_wrapper(sizeof(struct Entry));
 if(entries[0].y!=123||entries[1].y!=456)return 26;
 if(record_address(initialized[0])->b!=7||record_address(initialized[0]+1)!=words+2)return 27;
 if(nonnull(0)||!nonnull((const struct Words * __far)0x7e0000UL)||
    !nonnull((const struct Words * __far)1UL))return 28;
 if(advance_record((const struct Words * __far)edge)!=(const struct Words * __far)0x7f0002UL)return 29;
 if(shifted_position(-32767)!=-2051||shifted_position(32767)!=2044||
    shifted_position(-1)!=-4||shifted_position(0)!=-3)return 30;
 if(!same_y(entries,123)||same_y(entries,456))return 31;
 entries[0].x=1;clear_entry(entries);clear_entry(entries+1);
 if(entries[0].y!=0||entries[1].y!=123)return 32;
 counter.state=40;counter.ticks=2;count_counter(&counter,40);
 if(counter.state!=41||counter.ticks!=1)return 33;
 count_counter(&counter,41);
 if(counter.state!=42||counter.ticks!=5)return 34;
 count_counter(&counter,40);
 if(counter.state!=41||counter.ticks!=5)return 35;
 calls=0;
 move_entry(entries,0,0);
 if(entries[0].x!=1||entries[0].y!=0||calls!=0)return 36;
 move_entry(entries,0,3);
 move_entry(entries,-1,0);
 if(entries[0].x!=0||entries[0].y!=3||calls!=2)return 37;
 observe_zero_move(entries,0,0);
 if(calls!=3)return 38;
 switch_pointer(0);
 switch_pointer(sizeof(struct Entry));
 if(entries[0].y!=123||entries[1].y!=456)return 39;
 if(check_extent(entries,124)!=99||check_extent(entries,125)!=124||
    check_extent(entries+1,0)!=99)return 40;
 render.bits=0xf080;render.count=1;render.output=pixels;render.tag=0x92;
 finish_bits();
 if(render.bits!=0x03c2||render.count!=4||render.output!=pixels+1||pixels[0]!=0x92)return 41;
 if(count_rises(depths,depths+6)!=6||near_entry(entries)!=124)return 42;
 masks[1].bits=4;masks[1].remaining=2;
 if(masked_flag(1)!=7||masked_flag(0)!=9||step_byte(masks+1)||!step_byte(masks+1)||
    step_byte(masks+1)||masks[1].remaining)return 43;
 scan_points[0].x=100;scan_points[0].y=3;
 scan_points[1].x=2;scan_points[1].y=12;
 scan_points[2].x=4;scan_points[2].y=13;
 scan_end=scan_points;
 if(scan_range(65530u,10,16,8))return 44;
 scan_end=scan_points+1;
 if(scan_range(65530u,10,16,8))return 45;
 scan_end=scan_points+2;
 if(!scan_range(65530u,10,16,8)||scan_result!=12)return 46;
 scan_end=scan_points+3;
 if(!scan_range(65530u,13,16,1)||scan_result!=13||scan_range(65530u,10,0,8))return 47;
 short_points[0].x=4;short_end=short_points+1;
 if(!short_range(4,1)||short_range(5,1))return 48;
 if(!checked_extent(2,3,9,2)||checked_extent(2,3,7,2)||checked_extent(65535u,1,9,2)||
    checked_extent(65530u,5,0,1))return 49;
 frame_point.x=100;frame_point.y=200;frame_point.count=2;
 frame_x=103;frame_y=204;frame_width=8;frame_height=8;
 if(frame_candidate(&frame_point,70,4,6,9)||frame_candidate(&frame_point,3,70,6,9)||frame_calls)return 50;
 if(!frame_candidate(&frame_point,3,4,6,9)||frame_point.count!=1||frame_calls!=1)return 51;
 if(frame_two_live(&frame_point,3,4,6,9)!=103+(103^204^6^9)||frame_point.count||frame_calls!=2)return 52;
 if(!frame_candidate(&frame_point,3,4,6,9)||frame_point.count||frame_calls!=3)return 53;
 frame_point.x=356;frame_point.y=100;frame_point.count=1;frame_x=356;frame_y=100;
 if(frame_candidate(&frame_point,0,0,6,6)||frame_point.count!=1||frame_calls!=4)return 54;
 guard_keys[0]=0x8000;frame_point.x=10;frame_point.y=10;frame_point.count=4;
 if(guarded_input(&frame_point,1)||frame_point.x!=10||frame_point.y!=10||frame_point.count!=4)return 55;
 guard_keys[0]=0x8300;
 if(!guarded_input(&frame_point,1)||frame_point.x!=13||frame_point.y!=10||frame_point.count!=3)return 56;
 if(collision_flags(0x012f,0x0130,1)!=6||collision_flags(0x0130,0x012f,0)!=1||
    collision_flags(0x0230,0x0230,1)!=7||collision_flags(0x012f,0x012f,0)!=0)return 57;
 if(selected_velocity(-32768,0)!=-8||selected_velocity(32767,1)!=16||
    selected_velocity(-16,1)!=-16||selected_velocity(-15,1)||selected_velocity(7,0)||
    selected_velocity(8,0)!=8)return 58;
 if(byte_lookup(0)!=65535u)return 100;
 lookup_ready=lookup_bytes;
 if(byte_lookup(0)!=65535u||byte_lookup(1)!=0||byte_lookup(2)!=125||byte_lookup(3)!=253)return 101;
 calls=0;
 byte_guard_store(1,99);
 byte_guard_store(0,129);
 if(calls!=1||lookup_bytes[0]!=129||lookup_bytes[1]!=2)return 102;
 generation=31;
 next_generation();
 if(generation!=0)return 103;
 next_generation();
 if(generation!=1)return 104;

 PROBE_LOW=207;PROBE_HIGH=2;
 if(!packed_guard())return 105;
 PROBE_LOW=208;
 if(packed_guard())return 106;
 PROBE_LOW=0;PROBE_HIGH=3;
 if(packed_guard())return 107;

 ring_walk(0x8001u,0x8001u);
 if(ring_out_head!=0x8001u||ring_out_tail!=0x8001u||ring_sum)return 108;
 for(unsigned i=0;i<20;i++)ring_bytes[i]=1;
 ring_bytes[7]=0;ring_bytes[10]=0;ring_bytes[8]=128;
 ring_words[7]=4;
 ring_walk(7,0);
 if(ring_out_head!=2||ring_out_tail!=2||ring_sum!=13||
    ring_words[0]!=3||ring_words[1]!=6||ring_bytes[7]!=129||
    ring_bytes[10]!=129||ring_bytes[14]!=1)return 109;
 ring_bytes[7]=0;ring_bytes[8]=254;
 ring_walk(7,0);
 if(ring_out_head||ring_out_tail||ring_sum||ring_bytes[7]!=0)return 116;

 if(search_index(4)!=65535u||search_code(4)!=65535u)return 110;
 search_ready=search_field;
 if(search_index(4)!=65535u||search_code(4)!=65535u)return 111;
 search_field[4]=5;search_field[5]=4;search_field[3]=4;
 if(search_index(4)!=5||search_code(4)!=11)return 112;
 search_taken[5]=1;
 if(search_index(4)!=3||search_code(4)!=12)return 113;
 search_taken[3]=1;
 if(search_index(4)!=65535u||search_code(4)!=65535u)return 114;

 if(masked_relations(16,48)!=10||masked_relations(15,48)!=19||
    masked_relations(17,48)!=12||masked_relations(32,48)!=28||
    masked_relations(65535u,0)!=12)return 115;

 tail_local_array(0xa5);
 if(tail_observed!=0xa5)return 117;
 tail_local_member(0xb6);
 if(tail_observed!=0xb6)return 118;
 if(tail_local_scalar(0xc7d8)!=0xc7d8)return 119;
 tail_publish_local(0xe9fa);
 if(tail_observed!=0xe9fa)return 120;
 tail_forward_pointer(initialized+2);
 if(tail_observed!=128)return 121;

 return 0;
}
'''

FRAME_CALLEE = '''
unsigned frame_calls;
unsigned frame_probe(unsigned x,unsigned y,unsigned w,unsigned h) {
 frame_calls++;
 return x^y^w^h;
}
_Bool frame_bool_probe(unsigned x,unsigned y,unsigned w,unsigned h) {
 return (unsigned char)frame_probe(x,y,w,h);
}
unsigned tail_observed;
unsigned *tail_published;
static __noinline void tail_stack_noise(void) {
 volatile unsigned scratch[12];
 for(unsigned i=0;i<12;++i)scratch[i]=0x1234;
}
void tail_read_byte(const unsigned char *p) {
 tail_stack_noise();
 tail_observed=*p;
}
unsigned tail_read_word(const unsigned *p) {
 tail_stack_noise();
 return *p;
}
void tail_read_published(void) {
 tail_stack_noise();
 tail_observed=*tail_published;
 tail_published=0;
}

'''


def labels(path):
    return {n.removeprefix('_'):int(a,16) for a,n in re.findall(r'^al (\w+) \.(\S+)$',path.read_text(),re.M)}


def compile_rom(name,source,*flags):
    path=OUT/(name+'.c');path.write_text(source)
    raw=OUT/(name+'.raw')
    support.run([sys.executable,ROOT/'tools/build-rom.py',path,*flags,'-o',raw],timeout=120)
    rom=raw.with_suffix('.sfc')
    support.run([ROOT/'build/romtool.exe',raw,rom,ROOT/'tests/title.txt'])
    data=rom.read_bytes();m=json.loads(raw.with_suffix('.allocation.json').read_text())
    assert len(data)==m['capacity'] and data[0xffd5]==0x31
    assert 1<<data[0xffd7]==len(data)//1024
    assert sum(data)&65535==int.from_bytes(data[0xffde:0xffe0],'little')
    assert int.from_bytes(data[0xffdc:0xffde],'little')^int.from_bytes(data[0xffde:0xffe0],'little')==65535
    sy=labels(raw.with_suffix('.labels'))
    for offset in range(0xffe0,0x10000,2):
        target=int.from_bytes(data[offset:offset+2],'little')
        assert 0xffa0<=target<0xffc0 and data[target] in [0x40,0x5c]
    # Prove linker symbols agree with each manifest placement/size
    maptext=raw.with_suffix('.map').read_text()
    for unit in m['units']:
        if unit['name']=='INTERRUPT':continue
        found=re.search(r'^'+re.escape(unit['name'])+r'\s+([0-9A-F]+)\s+([0-9A-F]+)\s+([0-9A-F]+)',maptext,re.M)
        assert found,(name,unit['name'])
        address=int(found[1],16)
        if unit['name'] in {'DATA','LORAM_DATA'} or unit['name'].startswith('NEAR_DATA_'):
            address=sy[f"_{unit['name']}_LOAD__"]
        assert address==unit['address'],(name,unit,found[0])
        assert int(found[3],16)==unit['size']
        assert (unit['address']&65535)+unit['size']<=65536
    return rom,sy,m


def check_intermediate_retention():
    with tempfile.TemporaryDirectory(dir=OUT) as temporary:
        folder = Path(temporary)
        source = folder / 'retention.c'
        cache = folder / 'cache'
        environment = dict(os.environ, ZICC_RUNTIME_OBJECT_CACHE='1',
                           ZICC_RUNTIME_OBJECT_CACHE_DIR=str(cache))

        def build(name, code, *options):
            source.write_text(code)
            raw = folder / (name + '.raw')
            command = [sys.executable, ROOT/'tools/build-rom.py', source, '-o', raw, *options]
            subprocess.run(list(map(str, command)), env=environment, check=True, timeout=120)
            manifest = json.loads(raw.with_suffix('.allocation.json').read_text())
            return raw, Path(manifest['evidence'])

        _, cold = build('cold', 'int main(void) { return 0; }')
        assert not list(cold.rglob('*.o')) and not list(cold.rglob('*_abs.s'))
        code = 'int abs(int); volatile int value = -7; int main(void) { return abs(value) != 7; }'
        warm_raw, warm = build('warm', code)
        chosen, = warm.rglob('*_abs.s')
        assert not list(warm.rglob('*.o'))
        debug = warm_raw.with_suffix('.dbg').read_text()
        assert str(chosen) in debug and str(cold) not in debug
        assert re.search(r'Runtime object cache hit: .*_abs\.o <- .*_abs\.s', (warm/'build.log').read_text())
        full_raw, full = build('full', code, '--keep-intermediates')
        assert warm_raw.read_bytes() == full_raw.read_bytes()
        manifest = json.loads(warm_raw.with_suffix('.allocation.json').read_text())
        object_name = chosen.with_suffix('.o').relative_to(warm).as_posix()
        assert manifest['linked_objects'][object_name] == hashlib.sha256((full/object_name).read_bytes()).hexdigest()
        assert len(list(full.rglob('*.s'))) > len(list(warm.rglob('*.s')))
        assert list(full.rglob('*.o'))

        _, r1 = build('history', 'int main(void) { return 0; }')
        _, r2 = build('history', 'int main(void) { return 1; }')
        custom = r1.parent / 'saved-baseline'
        custom.mkdir()
        runs = sorted(p for p in r1.parent.iterdir() if p != custom)
        assert runs == [r1, r2] and custom.is_dir(), runs
        _, r3 = build('history', 'int main(void) { return 2; }')
        runs = sorted(p for p in r1.parent.iterdir() if p != custom)
        assert runs == [r2, r3] and not r1.exists() and custom.is_dir(), runs
        source.write_text('int main(void) { return ; }')
        failed = subprocess.run([sys.executable, ROOT/'tools/build-rom.py', source, '-o', folder/'history.raw'],
                                env=environment, capture_output=True, text=True, timeout=120)
        assert failed.returncode != 0
        runs = sorted(p for p in r1.parent.iterdir() if p != custom)
        assert len(runs) == 2 and runs[0] == r3 and not r2.exists() and custom.is_dir(), runs


def check_exhirom():
    # A file-contiguous run from the end of $FF into $40 is not CPU-contiguous
    units = [builder.Unit('code', 96, 1, 'code', 'application'),
             builder.Unit('asset', 0x400000, 1, 'asset', 'application')]
    try:
        builder.pack(units, 128, 1)
    except builder.PackingError as error:
        assert 'contiguous ROM extents' in str(error)
    else:
        raise AssertionError('An asset crossed from $FF into $40')

    support.mesen_executable()
    with tempfile.TemporaryDirectory(dir=OUT) as temporary:
        folder = Path(temporary)
        source = folder / 'exhirom.c'
        raw = folder / 'game.raw'
        rom = raw.with_suffix('.sfc')
        unsupported = support.run([sys.executable, ROOT/'tools/build-rom.py', source, '--mapping',
                                   'exhirom', '--rom-size', 12288, '-o', raw], expected=2)
        assert 'invalid choice' in unsupported.stderr and not raw.exists()
        cases = {
            6144: '''
const unsigned char small[32] = {91, 92};
const unsigned char crossed[0x10002] = {124, 125};
volatile unsigned long offset = 0x10001;
volatile unsigned nmis;
__interrupt(nmi) void vblank(void) { ++nmis; }
int main(void) {
    *(volatile unsigned char * __far)0x004200UL = 0x80;
    while (!nmis) {}
    if (crossed[0] != 124 || crossed[offset] != 0) return 1;
    offset = 1;
    return small[offset] != 92 || crossed[offset] != 125;
}
''',
            8192: '''
const unsigned char fast[0x400000] = {17};
const unsigned char slow[0x3D0000] = {51};
const unsigned char tail_e[0x8000] = {71};
const unsigned char tail_f[0x8000] = {93};
volatile unsigned long offset = 0x10000;
int main(void) {
    if (sizeof(fast) != 0x400000UL || sizeof(slow) != 0x3D0000UL) return 4;
    if (fast[0] != 17 || slow[0] != 51 || fast[offset] != 0 || slow[offset] != 0)
        return 1;
    offset = 0x3FFFFF;
    if (fast[offset] != 0) return 2;
    offset = 0x3CFFFF;
    if (slow[offset] != 0) return 3;
    *(volatile unsigned char * __far)0x7E8000UL = 0xA6;
    *(volatile unsigned char * __far)0x7F8000UL = 0xA7;
    return tail_e[0] != 71 || tail_f[0] != 93 ||
           *(volatile unsigned char * __far)0x7E8000UL != 0xA6 ||
           *(volatile unsigned char * __far)0x7F8000UL != 0xA7;
}
''',
        }
        for kib, code in cases.items():
            source.write_text(code)
            result = support.run([sys.executable, ROOT/'tools/build-rom.py', source, '--mapping',
                                  'exhirom', '--rom-size', kib, '-o', raw], timeout=180)
            assert ('fits in HiROM' in result.stderr) == (kib == 6144), result.stderr
            support.run([ROOT/'build/romtool.exe', raw, rom, ROOT/'tests/title.txt'])
            data = rom.read_bytes()
            assert len(data) == kib * 1024 and data[0x40FFD5] == 0x35 and data[0x40FFD7] == 13
            checksum = int.from_bytes(data[0x40FFDE:0x40FFE0], 'little')
            complement = int.from_bytes(data[0x40FFDC:0x40FFDE], 'little')
            assert checksum ^ complement == 0xFFFF
            assert checksum == (sum(data) + (sum(data[0x400000:]) if kib == 6144 else 0)) & 0xFFFF
            sy = labels(raw.with_suffix('.labels'))
            reset = int.from_bytes(data[0x40FFFC:0x40FFFE], 'little')
            assert reset == sy['reset_vector'] == 0xFFA0
            assert data[0x40FFA0:0x40FFA4] == b'\x5C' + sy['reset_entry'].to_bytes(3, 'little')
            manifest = json.loads(raw.with_suffix('.allocation.json').read_text())
            assert manifest['mapping'] == 'exhirom' and manifest['capacity'] == len(data)
            placements = {unit['address']: unit for unit in manifest['units']}

            def check_object(name, size, prefix):
                address = sy[name]
                unit = placements[address]
                start = unit['file_offset']
                assert unit['size'] == size
                assert data[start:start+size] == bytes(prefix) + bytes(size-len(prefix))
                return address, start

            if kib == 6144:
                small, _ = check_object('small', 32, (91, 92))
                crossed, _ = check_object('crossed', 0x10002, (124, 125))
                assert small >> 16 == (small + 31) >> 16
                assert (crossed + 0x10001) >> 16 == (crossed >> 16) + 1
            else:
                assert check_object('fast', 0x400000, (17,)) == (0xC00000, 0)
                assert check_object('slow', 0x3D0000, (51,)) == (0x410000, 0x410000)
                assert manifest['order'] == 'large-data-first'
                tails = {check_object('tail_e', 0x8000, (71,)), check_object('tail_f', 0x8000, (93,))}
                assert tails == {(0x3E8000, 0x7E8000), (0x3F8000, 0x7F8000)}
                for hole in (0x7E0000, 0x7F0000):
                    assert data[hole:hole+0x8000] == b'\xFF' * 0x8000
            support.run([sys.executable, ROOT/'tools/debug_symbols.py', raw.with_suffix('.labels'),
                         rom.with_suffix('.sym')])
            mlb = rom.with_suffix('.mlb').read_text()
            if kib == 8192:
                for name in ('fast', 'slow', 'tail_e', 'tail_f'):
                    offset = placements[sy[name]]['file_offset']
                    assert f'SnesPrgRom:{offset:06x}:{name}\n' in mlb
            support.emulate(rom, sy, 0)

        overflow = folder/'overflow.s'
        overflow.write_text('.segment "CODE"\n.export unused_interrupt\nunused_interrupt: rti\n'
                            '.segment "RODATA"\n.res $8000, 0\n')
        obj = overflow.with_suffix('.o')
        support.run([support.CC65/'ca65.exe', '--cpu', '65816', '-o', obj, overflow])
        failure = support.run([support.CC65/'ld65.exe', '-C', ROOT/'linker/lorom32.cfg',
                               '-o', folder/'too-big.raw', obj], expected=1)
        assert 'overflows memory area' in failure.stderr and '--mapping exhirom' in failure.stderr, failure.stderr


def check_rom_byte_copies():
    source=OUT/'rom-copy.c'
    source.write_text('''
extern const unsigned char contained[32],crossed[32];
unsigned char output[32];
__noinline unsigned copy_contained(unsigned to,unsigned from,unsigned count) {
    for(;count;--count) output[to++]=contained[from++];
    return to+from+count;
}
__noinline unsigned copy_crossed(unsigned to,unsigned from,unsigned count) {
    while(count) {output[to++]=crossed[from++];count--;}
    return to+from+count;
}
int main(void) {
    unsigned i;
    if(copy_contained(2,1,0)!=3||output[2]!=0)return 1;
    if(copy_contained(4,1,3)!=11||output[4]!=18||output[6]!=20)return 2;
    if(copy_contained(7,3,12)!=34)return 3;
    for(i=0;i<12;++i)if(output[7+i]!=i+20)return 4;
    if(copy_crossed(0,0,32)!=64)return 5;
    for(i=0;i<32;++i)if(output[i]!=i+117)return 6;
    return 0;
}
''')
    table=OUT/'rom-copy-table.s'
    table.write_text('.segment "EMBED"\n.export _contained,_crossed\n'
                     '_contained: .byte '+','.join(str(i+17) for i in range(32))+'\n'
                     '.res $FFD0, 0\n'
                     '_crossed: .byte '+','.join(str(i+117) for i in range(32))+'\n')
    raw=source.with_suffix('.raw')
    support.run([sys.executable,ROOT/'tools/build-rom.py',source,'--assembly',table,
                 '--keep-intermediates','-o',raw],timeout=120)
    m=json.loads(raw.with_suffix('.allocation.json').read_text())
    generated='\n'.join(p.read_text() for p in (Path(m['evidence'])/f"stage{m['stage']}").glob('*rom_copy.s'))
    assert generated.count('; counted byte copy: forward mvn')==2,generated
    sy=labels(raw.with_suffix('.labels'))
    assert sy['contained']>>16==(sy['contained']+31)>>16
    assert sy['crossed']>>16!=(sy['crossed']+31)>>16
    rom=raw.with_suffix('.sfc')
    support.run([ROOT/'build/romtool.exe',raw,rom,ROOT/'tests/title.txt'])
    return support.emulate(rom,sy,0)


def main():
    global OUT
    parts=['packing','abi-1','abi-2','abi-3','abi-4','assets','ordinary','code','console-3','console-4','source-names','near-startup','exhirom','byte-copies']
    parser=argparse.ArgumentParser();parser.add_argument('--list-parts',action='store_true');parser.add_argument('--part',choices=parts);args=parser.parse_args()
    if args.list_parts:print(json.dumps(parts));return
    if args.part:OUT=OUT/args.part
    OUT.mkdir(parents=True,exist_ok=True);support.OUT=OUT
    (OUT/'resource.bin').write_bytes(bytes(range(256)))
    report={}
    if args.part is None or args.part=='byte-copies':
        report['byte-copies']=check_rom_byte_copies()
    if args.part is None or args.part=='exhirom':
        check_exhirom()
        report['exhirom'] = 'passed'
    if args.part is None or args.part=='near-startup':
        support.run([sys.executable, ROOT/'tests/check-near-startup.py', OUT/'near-startup'], timeout=120)
        report['near-startup'] = 'passed'
    if args.part is None or args.part=='source-names':
        (OUT/'worker.one.c').write_text('static int work(int x){return x+1;} int one(int x){return work(x);}')
        (OUT/'worker.two.c').write_text('static int work(int x){return x+2;} int two(int x){return work(x);}')
        source='int one(int),two(int); int main(void){return one(5)!=6 || two(5)!=7;}'
        for flags in [(), ('--lto',)]:
            rom,sy,_=compile_rom('rom_header',source,OUT/'worker.one.c',OUT/'worker.two.c',*flags)
            report['source-names'+''.join(flags)]=support.emulate(rom,sy,0)
            for left,right in [('worker.one','worker_one'), ('a'*63+'x','a'*63+'y')]:
                # These inputs need not exist: the collision must precede compilation
                result=support.run([sys.executable,ROOT/'tools/build-rom.py',OUT/(left+'.c'),OUT/(right+'.c'),
                                    *flags,'-o',OUT/'collision.raw'],expected=1)
                assert 'same sanitized name' in result.stderr and left in result.stderr and right in result.stderr
    if args.part is None or args.part=='packing':
        check_intermediate_retention()
        # Group eligibility and fallback tests independent of generated instruction sizes
        units=[builder.Unit('app',59000,1,'code','application'),builder.Unit('runtime',9000,1,'code','runtime'),builder.Unit('const',2000,2,'constant','runtime')]
        for stage,banks,expected in [(1,1,False),(2,2,False),(3,4,True),(4,4,True)]:
            try: placements,_=builder.pack(units,banks,stage);passed=True
            except builder.PackingError:passed=False
            assert passed==expected
    # Every call/return convention executes the same opaque runtime work
    for stage in ([int(args.part[-1])] if args.part and args.part.startswith("abi-") else [1,2,3,4]) if args.part is None or args.part.startswith("abi-") else []:
        callee=OUT/'frame-callee.c'
        callee.write_text(FRAME_CALLEE)
        rom,sy,m=compile_rom('abi-stage'+str(stage),SOURCE,callee,'--stage',str(stage))
        assert m['stage']==stage
        assert sy['reset_entry']>>16==sy['main_exit']>>16
        report['abi-stage'+str(stage)]=support.emulate(rom,sy,0,seed=True)
        assemblies='\n'.join(p.read_text() for p in (Path(m['evidence'])/f'stage{stage}').glob('*.s'))
        packed=assemblies.split('_packed_guard:',1)[1].split('__size_packed_guard',1)[0]
        assert 'ordered packed byte comparison' in packed
        assert re.findall(r'lda f:\$7FFF1[01]',packed)==['lda f:$7FFF10','lda f:$7FFF11']
        if stage==1:
            ring=assemblies.split('_ring_walk:',1)[1].split('__size_ring_walk',1)[0]
            assert 'scaled ring indices within loop' in ring and 'and #$000E' in ring
            assert 'retained byte step and biased guard cursor' in ring and 'cmp #$FFF7' in ring
            assert 'cpy #$FFF7' not in ring
            search=assemblies.split('_search_index:',1)[1].split('__size_search_index',1)[0]
            assert search.count('reuse field address before probing reservation')==2
            assert 'byte load, lower-bound guard and decrement' in search
            assert '    phy' not in search and '    ply' not in search
            search=assemblies.split('_search_code:',1)[1].split('__size_search_code',1)[0]
            assert search.count('    phy')==search.count('    ply')==1
            assert search.index('lda #$FFFF')<search.index('    phy')<search.index('    ply')
        for function in ('tail_wrapper','switch_pointer'):
            wrapper=assemblies.split(f'_{function}:',1)[1].split(f'__size_{function}',1)[0]
            for target in ('_tail_a','_tail_b'):
                jump=f'jml {target}' if stage==4 else f'jmp .loword({target})'
                assert jump in wrapper,(stage,function,jump,wrapper)
        for function,target in (
            ('tail_local_array','tail_read_byte'),('tail_local_member','tail_read_byte'),
            ('tail_local_scalar','tail_read_word'),('tail_publish_local','tail_read_published'),
        ):
            body=assemblies.split(f'_{function}:',1)[1].split(f'__size_{function}',1)[0]
            call=f'jsl _{target}' if stage==4 else f'jsr .loword(_{target})'
            assert call in body,(stage,function,body)
        forward=assemblies.split('_tail_forward_pointer:',1)[1].split('__size_tail_forward_pointer',1)[0]
        jump='jml _tail_read_byte' if stage==4 else 'jmp .loword(_tail_read_byte)'
        assert jump in forward,(stage,forward)
        finish=assemblies.split('_finish_bits:',1)[1].split('__size_finish_bits',1)[0]
        assert 'register-resident fixed word shift loop' in finish and 'cpx #$0004' in finish
        assert re.search(r'\binc a:\.loword\(_\w+__render\+\$0004\)',finish)
        order=assemblies.split('_count_rises:',1)[1].split('__size_count_rises',1)[0]
        assert 'eor #$8000' in order and 'bvc' not in order
        near=assemblies.split('_near_entry:',1)[1].split('__size_near_entry',1)[0]
        assert 'lda a:$0002,x' in near and 'lda [' not in near
        masked=assemblies.split('_masked_flag:',1)[1].split('__size_masked_flag',1)[0]
        assert re.search(r'lda a:\.loword\(_\w+__masks\+\$0000\),x',masked)
        step=assemblies.split('_step_byte:',1)[1].split('__size_step_byte',1)[0]
        assert step.count('sep #$20')==1 and 'dec a:$0001,x' in step
        scan=assemblies.split('_scan_range:',1)[1].split('__size_scan_range',1)[0]
        short=assemblies.split('_short_range:',1)[1].split('__size_short_range',1)[0]
        extent=assemblies.split('_checked_extent:',1)[1].split('__size_checked_extent',1)[0]
        assert 'frameless unsigned range scan, two candidates per iteration' in scan
        assert 'frameless unsigned range scan' in short and 'two candidates' not in short
        assert 'adc z:__arith_lhs+8' in scan and '    phy' not in scan
        assert 'carry-guarded word sum' in extent and 'cmp z:__arith_rhs' in extent
        candidate=assemblies.split('_frame_candidate:',1)[1].split('__size_frame_candidate',1)[0]
        two_live=assemblies.split('_frame_two_live:',1)[1].split('__size_frame_two_live',1)[0]
        assert candidate.count('    phx')==1 and '    phy' not in candidate and '    tyx' not in candidate, (stage,candidate)
        guard=candidate.rindex('carry-guarded word sum')
        call=candidate.index('jsl _frame_bool_probe' if stage==4 else 'jsr .loword(_frame_bool_probe)')
        assert guard<candidate.index('    phx')<call and candidate[call:].count('    plx')==3, (stage,candidate)
        assert 'adc a:$0000,x' in candidate and candidate.count('    dec a\n')==2, (stage,candidate)
        height_use=re.search(r'adc a:\.loword\(_\w+__frame_height\)',candidate)
        assert height_use and guard<candidate.rindex('    dec a\n')<height_use.start()<call, (stage,candidate)
        result_test=candidate[call:].split('    beq ',1)[0]
        assert 'and #$00FF' in result_test and '    lda ' not in result_test, (stage,candidate)
        assert not re.search(r'\b(?:sta|lda) z:__arith_',candidate[call:]), (stage,candidate)
        assert '    tcs' not in candidate and '    tcs' in two_live, (stage,candidate,two_live)
        if stage==1:
            guarded=assemblies.split('_guarded_input:',1)[1].split('__size_guarded_input',1)[0]
            flags=assemblies.split('_collision_flags:',1)[1].split('__size_collision_flags',1)[0]
            velocity=assemblies.split('_selected_velocity:',1)[1].split('__size_selected_velocity',1)[0]
            assert 'masked input has a zero return before frame allocation' in guarded
            assert flags.count('    rol z:')==3 and 'lda 3,s' in flags
            assert flags.count('    cmp #$30')==2 and flags.count('    sep #$20')==1
            assert '    bmi ' in velocity and '    bpl ' in velocity and '    bvc ' not in velocity
            assert '    txy' in two_live and '    adc 1,s' in two_live
        if stage==1:
            compact=OUT/'compact-scan.s'
            support.run([ROOT/'build/zicc.exe',OUT/'abi-stage1.c','-o',compact,'-I',ROOT/'include','--no-loop-unroll'])
            disabled=compact.read_text().split('_scan_range:',1)[1].split('__size_scan_range',1)[0]
            assert 'frameless unsigned range scan' in disabled and 'two candidates' not in disabled
        if stage==3:
            assert all((u['address']>>16)==(0xc1 if u['owner']=='application' else 0xc2) for u in m['units'] if u['kind']=='code')
        if stage==4:
            assert not re.search(r'^\s*(?:rts|jsr)\b',assemblies,re.M)
            assert 'jsl _strcpy' in assemblies
            assert 'jsl _sum' in assemblies
            pair=assemblies.split('_read_pair:',1)[1].split('__size_read_pair',1)[0]
            assert 'lda f:_asset+$0002,x' in pair and 'lda f:_asset+$0004,x' in pair
            assert 'sta a:.loword(_destination+$0002)' in pair
            assert '; register pointer scan' in assemblies.split('_scan:',1)[1].split('__size_scan',1)[0]
            assert 'cmp f:_fixed_end' in assemblies.split('_scan_fixed:',1)[1].split('__size_scan_fixed',1)[0]
            address=assemblies.split('_record_address:',1)[1].split('__size_record_address',1)[0]
            assert 'indexed ROM address with bank carry' in address and '__shl32' not in address
            nonnull=assemblies.split('_nonnull:',1)[1].split('__size_nonnull',1)[0]
            assert '__ucmp32' not in nonnull
            assert 'zero arguments leave fields unchanged' in assemblies.split('_move_entry:',1)[1].split('__size_move_entry',1)[0]
            assert 'zero arguments leave fields unchanged' not in assemblies.split('_observe_zero_move:',1)[1].split('__size_observe_zero_move',1)[0]
            dispatch=assemblies.split('_switch_pointer:',1)[1].split('__size_switch_pointer',1)[0]
            assert not re.search(r'^    ph[axy]\b',dispatch,re.M)
    if args.part is None or args.part=='assets':
        # Flexible assets force 64 -> 128 -> 256 KiB without forcing long code calls
        payload=bytes((i*37+11)&255 for i in range(60000));(OUT/'large.bin').write_bytes(payload)
        source='\n'.join('const unsigned char asset'+str(i)+'[]={\n#embed "large.bin"\n};' for i in range(3))
        source+='\nint main(void){return asset0[59999]!=198||asset1[59999]!=198||asset2[59999]!=198;}\n'
        assert payload[-1]==198
        rom,sy,m=compile_rom('assets',source)
        assert m['capacity']==262144 and m['stage']==1
        data=rom.read_bytes()
        for i in range(3):
            offset=sy['asset'+str(i)]-0xc00000
            assert data[offset:offset+len(payload)]==payload
        report['assets']=support.emulate(rom,sy,0)
        failed=OUT/'limited.raw'
        result=subprocess.run([sys.executable,ROOT/'tools/build-rom.py',OUT/'assets.c','-o',failed,'--max-rom','131072'],capture_output=True,text=True)
        assert result.returncode and 'maximum HiROM capacity' in result.stderr and not failed.exists()
        assert '--mapping exhirom' in result.stderr
        assert not failed.with_suffix('.allocation.json').exists()
        # Rebuilding reads the resource again; no stale generated initializer
        (OUT/'large.bin').write_bytes(bytes([77])*60000)
        rom,sy,m=compile_rom('assets-rebuilt',source.replace('!=198','!=77'))
        report['assets-rebuilt']=support.emulate(rom,sy,0)

        payload=bytes((i*37+11)&255 for i in range(65536))
        (OUT/'full-bank.bin').write_bytes(payload)
        for bound in ('', '65536'):
            form='explicit' if bound else 'inferred'
            source=(
                f'const unsigned char full_bank[{bound}]={{\n'
                '#embed "full-bank.bin"\n};\n'
                'typedef char size_check[sizeof(full_bank)==65536UL && '
                'sizeof(sizeof(full_bank))==4 && sizeof(sizeof(char))==2 ? 1 : -1];\n'
                'volatile unsigned index=65535;\n'
                f'int main(void){{return full_bank[0]!=11 || full_bank[index]!={payload[-1]};}}\n'
            )
            rom,sy,m=compile_rom(f'full-bank-{form}',source)
            address=sy['full_bank']
            assert address>=0xc10000 and address%65536==0
            assert any(u['address']==address and u['size']==65536 for u in m['units'])
            offset=address-0xc00000
            assert rom.read_bytes()[offset:offset+65536]==payload
            report[f'full-bank-{form}']=support.emulate(rom,sy,0)

        (OUT/'oversized.bin').write_bytes(payload+b'\0')
        for name, declaration, limit in (
            ('oversized-inferred', 'const unsigned char a[]={\n#embed "oversized.bin"\n};', 65536),
            ('oversized-multidimensional', 'const unsigned char a[257][256]={0};', 65536),
            ('oversized-wram', 'unsigned char a[65536]={0};', 65534),
        ):
            path=OUT/f'{name}.c'
            path.write_text(declaration)
            result=subprocess.run([ROOT/'build/zicc.exe',path,'-o',path.with_suffix('.s')],
                                  capture_output=True,text=True,timeout=30)
            assert result.returncode and f'object size exceeds {limit} bytes' in result.stderr, result.stderr
    if args.part is None or args.part=='ordinary':
        # Ordinary constants also use remaining space, with no upper-half restriction
        ordinary='const unsigned char table[65534]={7};\nint main(void){return table[0]!=7||table[65533]!=0;}\n'
        rom,sy,m=compile_rom('ordinary-growth',ordinary)
        assert m['capacity']==131072 and sy['table']>>16==0xc1
        report['ordinary-growth']=support.emulate(rom,sy,0)

        definition=OUT/'full-bank-words.c'
        definition.write_text('const unsigned int words[32768]={0x1234};\n')
        reader=(
            'extern const unsigned int words[32768];\n'
            'volatile unsigned index=32767;\n'
            'int main(void){return sizeof(words)!=65536UL || words[0]!=0x1234 || words[index]!=0;}\n'
        )
        rom,sy,m=compile_rom('full-bank-words-reader',reader,definition)
        address=sy['words']
        assert address>=0xc10000 and address%65536==0
        offset=address-0xc00000
        assert rom.read_bytes()[offset:offset+65536]==bytes([0x34,0x12])+bytes(65534)
        report['full-bank-words']=support.emulate(rom,sy,0)
    if args.part is None or args.part=='code':
        # Real code pressure automatically reaches per-function long-call packing
        body='\n'.join('sink+=n;' for _ in range(3400))
        source='volatile unsigned sink;\n'+''.join(f'int work{i}(int n){{\n{body}\nreturn sink;\n}}\n' for i in range(2))
        source+='int main(void){work0(1);work1(2);return sink!=10200U;}\n'
        rom,sy,m=compile_rom('code-growth',source)
        assert m['stage']==4 and m['capacity']==262144
        assert any((u['address']&65535)<0x8000<(u['address']&65535)+u['size'] for u in m['units'] if u['kind']=='code')
        report['code-growth']=support.emulate(rom,sy,0)
        # Leave room for startup in C0, but force console_init to C1:0000
        # independently of the code size produced for main
        padding=OUT/'zero-console-padding.s'
        padding.write_text('.segment "CODE"\n.res $FA00, $EA\n')
        source='#include <stdio.h>\nint main(void){printf("ZERO");fflush(stdout);return 0;}\n'
        rom,sy,m=compile_rom('zero-console',source,'--console','--stage','4','--assembly',padding)
        assert sy['console_init']&65535==0 and sy['console_init']>>16!=sy['reset_entry']>>16
        assert sy['reset_entry']>>16==sy['main_exit']>>16
        report['zero-console']=support.emulate(rom,sy,0)
        # A function cannot be made bank-contained by adding more banks
        oversize=OUT/'oversize.c';oversize.write_text('volatile unsigned sink;\nint huge(int n){\n'+body.replace('sink+=n;', 'sink+=n;\nsink+=n;')+'\nreturn sink;}\nint main(void){return 0;}\n')
        result=subprocess.run([sys.executable,ROOT/'tools/build-rom.py',oversize,'-o',OUT/'oversize.raw'],capture_output=True,text=True)
        assert result.returncode and 'indivisible allocation' in result.stderr,result.stderr
    # Actual NMI wrapper and console execute across the stage-3 bank boundary
    for stage in ([int(args.part[-1])] if args.part and args.part.startswith("console-") else [3,4]) if args.part is None or args.part.startswith("console-") else []:
        source='#include <stdio.h>\nvolatile unsigned nmis;\n__interrupt(nmi) void vblank(void){nmis++;}\nint main(void){printf("BANK %ld %g",123456L,12.5);fflush(stdout);return nmis==0;}\n'
        rom,sy,m=compile_rom('console-stage'+str(stage),source,'--console','--input',str(ROOT/'samples/input.txt'),'--stage',str(stage))
        lua=OUT/('console-stage'+str(stage)+'.lua')
        lua.write_text(f'''local done=false
emu.addMemoryCallback(function()
 if done then return end
 local text=''
 for i=0,31 do local c=emu.read(({sy['console_map']}+(i//2)*2+(i%2)*2048)&0x1ffff,emu.memType.snesWorkRam,false);text=text..(c==0 and '.' or string.char(c//2)) end
 if not string.find(text,'BANK 123456 12.5',1,true) then error(text) end
 print('PASS '..text);done=true
end,emu.callbackType.exec,{sy['console_flush_done']},{sy['console_flush_done']})
emu.addMemoryCallback(function() if not done or emu.getState()['cpu.sp']~=0x04ff or emu.getState()['cpu.a']~=0 then error('console return') end;emu.stop(0) end,emu.callbackType.exec,{sy['main_exit']},{sy['main_exit']})
''')
        result=support.run([support.mesen_executable(OUT),'--testRunner','--doNotSaveSettings','--timeout=12',rom,lua],timeout=20)
        assert 'PASS' in result.stdout,result.stdout
        report['console-stage'+str(stage)]=result.stdout
    (OUT/'results.json').write_text(json.dumps(report,indent=2)+'\n')
    print(f'PASS: {args.part or "HiROM and ExHiROM banked ROMs"}')


if __name__=='__main__':main()
