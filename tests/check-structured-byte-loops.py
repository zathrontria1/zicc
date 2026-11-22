"""Check loops that select and copy bytes, including when copies can use wider words or two loops can safely become one."""
import os
import importlib.util
import json
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[1]
OUT = Path(os.environ.get('ZICC_LOGS_DIR', 'logs')).resolve() / 'structured-byte-loop-check'
spec = importlib.util.spec_from_file_location('body_checks', ROOT / 'tests/check-body-codegen.py')
checks = importlib.util.module_from_spec(spec)
spec.loader.exec_module(checks)

KERNELS = r'''
#include <stdint.h>
uint8_t tags[256], image[1056], slots[256], backup[256], small[32], other[256], phase;
volatile uint8_t observed[16];
struct Padded { uint16_t word; uint8_t flag; };
struct Mixed { uint16_t word; uint8_t flag; volatile uint8_t adjacent; };
struct Padded padded[8];
struct Mixed mixed_flags[8];
uint16_t used, bound;
static void collect(unsigned first,unsigned end) {
    for(unsigned i=first;i<end;i++) {
        if(tags[i]==phase) {
            unsigned at=used++;
            slots[at]=i;
            backup[at]=image[i*4+1];
            image[i*4+1]=241;
        }
    }
}
void filtered(unsigned first,unsigned end) {
    collect(first,end);
    for(unsigned j=first;j<end;j++) {
        if(tags[j]==phase) image[1024+j/8]&=~(1<<(j%8));
    }
}
void scatter(void) {
    for(unsigned i=0;i<used;i++) image[slots[i]*4+1]=backup[i];
}
unsigned fixed_odd(void) {
    unsigned i;
    for(i=2;i<15;i++) small[i]=image[500+i];
    return i;
}
unsigned fixed_block(void) {
    unsigned i;
    for(i=3;i<78;++i) other[i+9]=image[37+i];
    return i;
}
void overlap_block(void) {
    for(unsigned i=0;i<74;++i) other[i+1]=other[i];
}
void fill_block(void) {
    for(unsigned i=7;i<82;++i) other[i]=0xac;
}
unsigned dynamic_forward(unsigned index,unsigned distance,unsigned count) {
    while(count) {
        other[index]=other[index-distance];
        index+=1;
        --count;
    }
    return index+count;
}
unsigned dynamic_distinct(unsigned dest,unsigned source,unsigned count) {
    for(;count!=0;--count) other[dest++]=image[source++];
    return dest+source+count;
}
void stationary_source(unsigned index,unsigned source,unsigned count) {
    while(count) {
        other[index++]=image[source];
        --count;
    }
}
uint16_t fixed_sum(uint16_t seed) {
    unsigned i;
    for(i=4;i<48;++i) seed=other[i+3]+seed;
    return i==48?seed:0U;
}
uint16_t fixed_sum_odd(uint16_t seed) {
    for(unsigned i=4;i<47;++i) seed+=other[i+3];
    return seed;
}
uint16_t fixed_products(uint16_t seed) {
    for(unsigned i=2;i<19;++i) seed+=(uint16_t)tags[i+3]*other[i+4];
    return seed;
}
uint16_t strided_store(uint16_t index,uint16_t stride) {
    for(;index<10U;index+=stride) other[index+4]=211;
    return index;
}
unsigned indexed_and(unsigned i) {
    if(tags[i+2]==3&&other[i+2]==251)return 8;
    return 9;
}
unsigned indexed_or(unsigned i) {
    if(tags[i+2]!=3||other[i+2]!=251)return 10;
    return 11;
}
unsigned indexed_independent(unsigned i,unsigned j) {
    if(tags[i]==3&&other[j]==251)return 12;
    return 13;
}
unsigned padded_guard(unsigned i) {
    if(padded[i].flag)return 31;
    return 32;
}
unsigned mixed_guard(unsigned i) {
    if(mixed_flags[i].flag)return 33;
    return 34;
}
void set_guard_values(void) {
    padded[7].flag=255;
    mixed_flags[7].adjacent=255;
}
static const uint8_t packed_masks[8]={1,2,4,8,16,32,64,128};
uint16_t packed_clear(uint16_t i,uint16_t stride) {
    for(;i<64U;i+=stride) other[i>>3]&=~packed_masks[i%8U];
    return i;
}
uint16_t packed_set(uint16_t i,uint16_t stride) {
    for(;i<64U;i+=stride) other[i/8U]=packed_masks[i&7U]|other[i/8U];
    return i;
}
void adjacent_ascending(void) {
    unsigned char saved;
    for(unsigned i=0;i<7U;++i) {
        if(small[i]>small[i+1]) {
            saved=small[i];small[i]=small[i+1];small[i+1]=saved;
        }
    }
}
void adjacent_descending(void) {
    unsigned char saved;
    for(unsigned i=0;i<7U;++i) {
        if(small[i+1]>small[i]) {
            saved=small[i+1];small[i+1]=small[i];small[i]=saved;
        }
    }
}
uint16_t saved_indices[8];
unsigned guarded_save(uint16_t base) {
    uint16_t candidate=base+3U;
    if(tags[candidate]==3&&other[candidate]==251) {
        image[candidate]=76;
        saved_indices[used]=candidate;
        ++used;
    }
    return used;
}
void overlap(void) {
    for(unsigned i=0;i<15;i++) small[i+1]=small[i];
}
unsigned changing_bound(void) {
    unsigned i;bound=20;
    for(i=0;i<bound;i++) {other[i]=i;if(i==2)bound=3;}
    return i;
}
unsigned alias_bound(uint8_t *where) {
    unsigned i;bound=7;
    for(i=0;i<bound;i++) {other[i]=i;*where=3;}
    return i;
}
void volatile_loop(void) {
    for(unsigned i=0;i<16;i++) observed[i]=i;
}
uint16_t fold_left(uint16_t x) {
    unsigned char i;
    for(i=3;i<=9;++i) {
        if(x&0x8000U) x=(uint16_t)((x<<1)^0x8d95U);
        else x<<=1;
    }
    return i==10?x:0xbeefU;
}
uint32_t fold_right(uint32_t x) {
    for(unsigned i=11;i>0;--i) {
        if((x&1UL)==0) x=x>>1;
        else x=0xa9d3d497UL^(x>>1);
    }
    return x;
}
uint16_t sum_low_bits(uint16_t x,uint16_t sum) {
    while(x!=0) {
        sum=sum+(x%2U);
        x/=2U;
    }
    return sum;
}
uint16_t signed_remainders(int16_t x,uint16_t sum) {
    while(x) {
        sum+=x%2;
        x/=2;
    }
    return sum;
}
uint16_t volatile_shift(uint16_t seed) {
    volatile uint16_t observed_word=seed;
    for(unsigned i=0;i<3;++i) {
        if(observed_word&0x8000U) observed_word=(observed_word<<1)^3U;
        else observed_word<<=1;
    }
    return observed_word;
}
void dependent_loops(void) {
    for(unsigned i=0;i<16;i++) other[i]=small[i];
    for(unsigned j=0;j<16;j++) small[j]=other[(j+1)&15];
}
void changing_predicate(void) {
    for(unsigned i=0;i<16;i++) {if(tags[i]==phase) phase^=1;}
    for(unsigned j=0;j<16;j++) {if(tags[j]==phase) other[j]=99;}
}
void independent_loops(unsigned first,unsigned end) {
    for(unsigned i=first;i<end;i++) small[i]=image[i];
    for(unsigned j=first;j<end;j++) other[j]=tags[j];
}
unsigned self_start(unsigned start,unsigned end) {
    unsigned i=start;
    for(i=i+1;i<end;i++) other[i]=i+11;
    for(i=i+1;i<end;i++) small[i]=i+37;
    return i;
}
unsigned post_result(unsigned start) {
    unsigned value=start,old=0;
    for(unsigned i=0;i<7;i++) {old=value++;if(value!=old+1)return 1;}
    return value!=start+7;
}
unsigned global_steps(unsigned first,unsigned end) {
    for(used=first;used<end;used++) other[used]=used^73;
    return used;
}
unsigned comma_steps(unsigned end) {
    phase=0;
    for(used=0;used<end;used++,phase^=1) other[used]=used;
    return used+phase;
}
unsigned mixed_steps(unsigned end) {
    unsigned i;
    uint8_t value=65;
    for(i=0;i<end;i++,value++,backup[i]=value) {
        if(value>=68)value=65;
        other[i]=value;
    }
    for(i=0;i<end;value--,i++) {
        if(value<=65)value=68;
        image[2*i]=value;
    }
    return i+value;
}
unsigned repeated_index_step(unsigned end) {
    unsigned i;
    for(i=0;i<end;i++,i++) {
        if(phase)small[i]=i;
    }
    return i;
}
unsigned while_copy(unsigned first,unsigned end) {
    unsigned i=first;
    while(end>i) {if(tags[i]==phase)other[i]=image[i*2+1];i++;}
    return i;
}
unsigned while_copy_plus(unsigned first,unsigned end) {
    unsigned i=first;
    while(end>i) {if(tags[i]==phase)other[i]=image[i*2+1];i+=1;}
    return i;
}
void sentinel(unsigned first,unsigned end) {
    for(unsigned i=first;i!=end;i+=1) {if(tags[i]==phase)other[i]=i^131;}
}
int signed_window(int first,int end) {
    int i;
    for(i=first;i<end;i++) {if(phase==2)other[i+12]=i;}
    return i;
}
void signed_predicates(unsigned n) {
    for(unsigned i=0;i<n;i++) {if((int8_t)tags[i]<1)other[i]=17;else other[i]=33;}
}
void cast_predicates(unsigned n) {
    for(unsigned i=0;i<n;i++) {if((unsigned)(int8_t)tags[i]<1U)other[i]=17;else other[i]=33;}
}
void compare_bytes(unsigned n) {
    for(unsigned i=0;i<n;i++) {
        if((int8_t)tags[i]<(int8_t)backup[i])other[i]|=1;
        if((int8_t)tags[i]<=(int8_t)backup[i])other[i]|=2;
        if((int8_t)tags[i]>(int8_t)backup[i])other[i]|=4;
        if((int8_t)tags[i]>=(int8_t)backup[i])other[i]|=8;
        if((int8_t)tags[i]==(int8_t)backup[i])other[i]|=16;
        if((int8_t)tags[i]!=(int8_t)backup[i])other[i]|=32;
    }
}
void mixed_predicate(unsigned n) {
    for(unsigned i=0;i<n;i++) {if((int8_t)tags[i]==backup[i])other[i]=17;else other[i]=33;}
}
void cmp_lt(unsigned n) {for(unsigned i=0;i<n;i++)if((int8_t)tags[i]<(int8_t)backup[i])other[i]|=1;}
void cmp_le(unsigned n) {for(unsigned i=0;i<n;i++)if((int8_t)tags[i]<=(int8_t)backup[i])other[i]|=2;}
void cmp_gt(unsigned n) {for(unsigned i=0;i<n;i++)if((int8_t)tags[i]>(int8_t)backup[i])other[i]|=4;}
void cmp_ge(unsigned n) {for(unsigned i=0;i<n;i++)if((int8_t)tags[i]>=(int8_t)backup[i])other[i]|=8;}
void cmp_eq(unsigned n) {for(unsigned i=0;i<n;i++)if((int8_t)tags[i]==(int8_t)backup[i])other[i]|=16;}
void cmp_ne(unsigned n) {for(unsigned i=0;i<n;i++)if((int8_t)tags[i]!=(int8_t)backup[i])other[i]|=32;}
void expr_bound_char(unsigned n, unsigned trim) {unsigned char i;if(n<10||n>200||trim>10)return;for(i=0;i<n-trim;i++)other[i]=tags[i]^0x55;}
'''
DRIVER = r'''
#include <stdint.h>
extern uint8_t tags[256],image[1056],slots[256],backup[256],small[32],other[256],phase;
extern volatile uint8_t observed[16];
extern uint16_t used,bound;
void filtered(unsigned,unsigned);void scatter(void);unsigned fixed_odd(void);void overlap(void);
unsigned fixed_block(void);void overlap_block(void);
void fill_block(void);
unsigned dynamic_forward(unsigned,unsigned,unsigned);unsigned dynamic_distinct(unsigned,unsigned,unsigned);
void stationary_source(unsigned,unsigned,unsigned);
uint16_t fixed_sum(uint16_t);uint16_t fixed_sum_odd(uint16_t);
uint16_t fixed_products(uint16_t);
uint16_t strided_store(uint16_t,uint16_t);
unsigned indexed_and(unsigned);unsigned indexed_or(unsigned);
unsigned indexed_independent(unsigned,unsigned);
unsigned padded_guard(unsigned);unsigned mixed_guard(unsigned);
void set_guard_values(void);
uint16_t packed_clear(uint16_t,uint16_t);
uint16_t packed_set(uint16_t,uint16_t);
void adjacent_ascending(void);void adjacent_descending(void);
extern uint16_t saved_indices[8];
unsigned guarded_save(uint16_t);
unsigned changing_bound(void);unsigned alias_bound(uint8_t *);void volatile_loop(void);
uint16_t fold_left(uint16_t);uint32_t fold_right(uint32_t);uint16_t sum_low_bits(uint16_t,uint16_t);
uint16_t signed_remainders(int16_t,uint16_t);
uint16_t volatile_shift(uint16_t);
void dependent_loops(void);void changing_predicate(void);void independent_loops(unsigned,unsigned);
unsigned post_result(unsigned);
unsigned global_steps(unsigned,unsigned);unsigned comma_steps(unsigned);
unsigned mixed_steps(unsigned);unsigned repeated_index_step(unsigned);
unsigned self_start(unsigned,unsigned);unsigned while_copy_plus(unsigned,unsigned);
unsigned while_copy(unsigned,unsigned);void sentinel(unsigned,unsigned);int signed_window(int,int);
void signed_predicates(unsigned);void cast_predicates(unsigned);
void compare_bytes(unsigned);void mixed_predicate(unsigned);
void cmp_lt(unsigned);void cmp_le(unsigned);void cmp_gt(unsigned);void cmp_ge(unsigned);void cmp_eq(unsigned);void cmp_ne(unsigned);
void expr_bound_char(unsigned,unsigned);
uint8_t expected_masks[256];
int main(void) {
    unsigned t,i,j,first,end,expected,next;uint8_t want;
    for(t=0;t<32;t++) {
        phase=t&1;used=0;first=(t*7)%257;end=(t*13)%257;
        if(t<2){first=0;end=256;}
        for(i=0;i<256;i++) tags[i]=t==1?phase:(i+t)%3;
        for(i=0;i<1056;i++) image[i]=(i*37+t*11)&255;
        filtered(first,end);expected=0;
        for(i=0;i<256;i++) {
            int hidden=i>=first&&i<end&&tags[i]==phase;
            if(hidden) {
                if(slots[expected]!=i||backup[expected]!=(uint8_t)((i*4+1)*37+t*11))return 1;
                expected++;
            }
            for(j=0;j<4;j++) {
                want=(i*4+j)*37+t*11;
                if(j==1&&hidden)want=241;
                if(image[i*4+j]!=want)return 2;
            }
        }
        if(used!=expected)return 3;
        for(i=0;i<32;i++) {
            want=(1024+i)*37+t*11;
            for(j=0;j<8;j++) {
                next=i*8+j;
                if(next>=first&&next<end&&tags[next]==phase)want&=~(1<<j);
            }
            if(image[1024+i]!=want)return 4;
        }
        scatter();
        for(i=0;i<1024;i++) if(image[i]!=(uint8_t)(i*37+t*11))return 5;
    }
    for(i=0;i<32;i++)small[i]=77;
    if(fixed_odd()!=15)return 6;
    for(i=0;i<32;i++)if(small[i]!=(i>=2&&i<15?image[500+i]:77))return 7;
    overlap();for(i=0;i<16;i++)if(small[i]!=77)return 8;
    for(i=0;i<256;i++)other[i]=77;
    if(fixed_block()!=78)return 43;
    for(i=0;i<256;i++)if(other[i]!=(i>=12&&i<87?image[28+i]:77))return 44;
    other[0]=51;overlap_block();
    for(i=0;i<75;i++)if(other[i]!=51)return 45;
    for(i=0;i<256;i++)other[i]=77;
    fill_block();for(i=0;i<256;i++)if(other[i]!=(i>=7&&i<82?0xac:77))return 50;
    other[1]=23;other[2]=87;other[3]=116;
    if(dynamic_forward(4,3,0)!=4||other[4]!=77||dynamic_forward(4,3,15)!=19)return 52;
    for(i=4;i<19;i++)if(other[i]!=other[(i-1)%3+1])return 53;
    if(dynamic_distinct(20,30,21)!=92)return 54;
    for(i=20;i<41;i++)if(other[i]!=image[i+10])return 55;
    image[123]=137;stationary_source(44,123,7);
    for(i=44;i<51;i++)if(other[i]!=137)return 56;
    expected=65512U;
    for(i=7;i<50;i++)expected+=other[i];
    if(fixed_sum_odd(65512U)!=(uint16_t)expected)return 57;
    if(fixed_sum(65512U)!=(uint16_t)(expected+other[50]))return 58;
    tags[6]=255;other[7]=255;
    expected=0xbff9U;
    for(i=2;i<19;++i)expected+=(uint16_t)tags[i+3]*other[i+4];
    if(fixed_products(0xbff9U)!=(uint16_t)expected)return 59;
    for(i=0;i<20;i++)other[i]=77;
    if(strided_store(10,3)!=10||strided_store(1,3)!=10)return 60;
    for(i=0;i<20;i++)if(other[i]!=((i==5||i==8||i==11)?211:77))return 61;
    if(strided_store(5,65535U)!=65535U)return 62;
    for(i=4;i<10;i++)if(other[i]!=211)return 63;
    tags[3]=3;other[3]=251;tags[4]=3;other[4]=250;tags[5]=2;other[5]=251;
    if(indexed_and(1)!=8||indexed_and(2)!=9||indexed_and(3)!=9)return 64;
    if(indexed_or(1)!=11||indexed_or(2)!=10||indexed_or(3)!=10)return 65;
    if(indexed_independent(4,5)!=12||indexed_independent(5,3)!=13)return 66;
    used=0;
    if(guarded_save(1)!=0||guarded_save(2)!=0||guarded_save(0)!=1||
       saved_indices[0]!=3||image[3]!=76)return 71;
    set_guard_values();
    if(padded_guard(0)!=32||padded_guard(7)!=31||mixed_guard(7)!=34)return 67;
    for(i=0;i<8;i++)other[i]=255;
    if(packed_clear(64,5)!=64||packed_clear(2,5)!=67)return 68;
    for(i=0;i<64;i++)if(((other[i/8]>>(i&7))&1U)!=(i<2||(i-2)%5!=0))return 69;
    for(i=0;i<8;i++)other[i]=255;
    if(packed_clear(9,65535U)!=65535U||other[0]!=0||other[1]!=252||other[2]!=255)return 70;
    for(i=0;i<8;i++)other[i]=0;
    if(packed_set(2,5)!=67)return 72;
    for(i=0;i<64;i++)if(((other[i/8]>>(i&7))&1U)!=(i>=2&&(i-2)%5==0))return 73;
    small[0]=3;small[1]=1;small[2]=3;small[3]=2;small[4]=2;small[5]=8;small[6]=5;small[7]=1;
    adjacent_ascending();
    if(small[0]!=1||small[1]!=3||small[2]!=2||small[3]!=2||
       small[4]!=3||small[5]!=5||small[6]!=1||small[7]!=8)return 74;
    adjacent_descending();
    if(small[0]!=3||small[1]!=2||small[2]!=2||small[3]!=3||
       small[4]!=5||small[5]!=1||small[6]!=8||small[7]!=1)return 75;
    for(i=0;i<256;i++)other[i]=77;
    if(changing_bound()!=3||bound!=3||other[2]!=2||other[3]!=77)return 9;
    for(i=0;i<256;i++)other[i]=77;
    if(alias_bound((uint8_t *)&bound)!=3||bound!=3||other[2]!=2||other[3]!=77)return 10;
    volatile_loop();for(i=0;i<16;i++)if(observed[i]!=i)return 11;
    if(fold_left(0)!=0||fold_left(1)!=0x80U||fold_left(0xa9e3U)!=0x1034U||fold_left(0xf741U)!=0x1c90U)return 46;
    if(fold_right(0)!=0||fold_right(1)!=0x430a4294UL||fold_right(0xa9e3e906UL)!=0xa7120544UL||
       fold_right(0xffffffffUL)!=0xf07b5969UL)return 47;
    if(sum_low_bits(0,234)!=234||sum_low_bits(0xffffU,65530U)!=10||sum_low_bits(0x8101U,7)!=10)return 48;
    if(signed_remainders(-3,10)!=8)return 51;
    if(volatile_shift(0xa001U)!=7)return 49;
    for(i=0;i<16;i++){small[i]=i+17;other[i]=77;tags[i]=i&1;}
    dependent_loops();for(i=0;i<16;i++)if(small[i]!=(i+1)%16+17)return 12;
    phase=0;for(i=0;i<16;i++)other[i]=77;
    changing_predicate();for(i=0;i<16;i++)if(other[i]!=(i&1?77:99))return 13;
    independent_loops(1,16);
    for(i=1;i<16;i++)if(small[i]!=image[i]||other[i]!=tags[i])return 14;
    if(post_result(65300))return 15;
    for(i=0;i<32;i++)other[i]=77;
    if(global_steps(3,19)!=19||global_steps(20,12)!=20)return 36;
    for(i=0;i<32;i++)if(other[i]!=(i>=3&&i<19?(i^73):77))return 37;
    if(comma_steps(9)!=10||used!=9||phase!=1)return 38;
    for(i=0;i<9;i++)if(other[i]!=i)return 39;
    backup[0]=99;
    if(mixed_steps(8)!=73||backup[0]!=99)return 40;
    for(i=0;i<8;i++) {
        want=65+i%3;
        if(other[i]!=want||backup[i+1]!=want+1)return 41;
        want=i<2?67-i:68-(i-2)%3;
        if(image[2*i]!=want)return 42;
    }
    if(repeated_index_step(7)!=8||small[6]!=6)return 43;
    for(i=0;i<32;i++)small[i]=77;
    if(self_start(1,8)!=9)return 33;
    for(i=0;i<32;i++)if(small[i]!=77)return 34;
    phase=1;for(i=0;i<32;i++)other[i]=77;
    if(while_copy(1,17)!=17||while_copy(19,2)!=19)return 16;
    if(while_copy_plus(1,17)!=17||while_copy_plus(19,2)!=19)return 35;
    for(i=1;i<17;i++)if(other[i]!=(tags[i]==phase?image[i*2+1]:77))return 17;
    sentinel(2,19);for(i=2;i<19;i++)if(tags[i]==phase&&other[i]!=(i^131))return 18;
    phase=2;for(i=0;i<32;i++)other[i]=77;
    if(signed_window(-6,-1)!=-1||signed_window(-1,-2)!=-1)return 19;
    for(i=0;i<32;i++)if(other[i]!=(i>=6&&i<=10?(uint8_t)(i-12):77))return 20;
    for(i=0;i<256;i++)tags[i]=i;
    signed_predicates(256);for(i=0;i<256;i++)if(other[i]!=(i==0||i>=128?17:33))return 21;
    cast_predicates(256);for(i=0;i<256;i++)if(other[i]!=(i==0?17:33))return 22;
    for(t=0;t<256;t++) {
        for(i=0;i<256;i++){tags[i]=i;backup[i]=t;other[i]=0;}
        compare_bytes(256);
        for(i=0;i<256;i++) {
            int a=(int8_t)i,b=(int8_t)t;
            expected=(a<b?1:0)|(a<=b?2:0)|(a>b?4:0)|(a>=b?8:0)|(a==b?16:0)|(a!=b?32:0);
            if(other[i]!=expected)return 23;expected_masks[i]=expected;
        }
        for(i=0;i<256;i++)other[i]=0;
        cmp_lt(256);cmp_le(256);cmp_gt(256);cmp_ge(256);cmp_eq(256);cmp_ne(256);
        for(i=0;i<256;i++)if(other[i]!=expected_masks[i])return 25;
    }
    for(i=0;i<256;i++){tags[i]=i;backup[i]=i;}
    mixed_predicate(256);for(i=0;i<256;i++)if(other[i]!=(i<128?17:33))return 24;
    for(i=0;i<32;i++)other[i]=77;
    expr_bound_char(10,10);if(other[0]!=77)return 26;
    expr_bound_char(19,5);for(i=0;i<32;i++)if(other[i]!=(i<14?(tags[i]^0x55):77))return 27;
    return 0;
}
'''


def body(assembly, name):
    return assembly.split('_' + name + ':', 1)[1].split('__size_' + name, 1)[0]


def main():
    OUT.mkdir(parents=True, exist_ok=True)
    checks.OUT = OUT
    host = OUT / 'reference.c'
    host.write_text(KERNELS + '\n' + DRIVER, encoding='ascii')
    exe = host.with_suffix('.exe')
    checks.c.run([ROOT / 'tools/msvc.cmd', '/nologo', '/std:c17', '/O2',
                  '/Fo' + str(host.with_suffix('.obj')), '/Fe' + str(exe), host])
    assert subprocess.run([str(exe)], timeout=5).returncode == 0
    reports = {}
    for mode in ('optimized', 'fallback'):
        directory, rom, sy, assembly = checks.build(mode, KERNELS, DRIVER)
        if mode == 'optimized':
            assert assembly.count('; fused independent counted loops') == 2, assembly
            filtered = body(assembly, 'filtered')
            assert '; structured byte loop:' in filtered and filtered.count('lda a:.loword(_tags') == 1
            assert '; bounded byte shift lookup' in filtered
            assert '; structured byte loop:' in body(assembly, 'scatter')
            for name in ('while_copy', 'while_copy_plus', 'sentinel', 'signed_window', 'signed_predicates', 'cast_predicates', 'compare_bytes',
                         'cmp_lt', 'cmp_le', 'cmp_gt', 'cmp_ge', 'cmp_eq', 'cmp_ne', 'expr_bound_char'):
                assert '; structured byte loop:' in body(assembly, name), name
            assert '; widened fixed byte copy: 13 bytes' in body(assembly, 'fixed_odd')
            assert '; fixed byte copy: mvn 75 bytes' in body(assembly, 'fixed_block')
            assert '    mvn ' not in body(assembly, 'overlap_block')
            fill = body(assembly, 'fill_block')
            assert '; constant indexed byte fill' in fill and '    sbc #$0010' in fill
            for name in ('dynamic_forward', 'dynamic_distinct'):
                assert '; counted byte copy: forward mvn' in body(assembly, name), name
            assert '; counted byte copy' not in body(assembly, 'stationary_source')
            for name in ('fixed_sum', 'fixed_sum_odd'):
                assert '; register unsigned byte sum' in body(assembly, name), name
            assert '; register unsigned byte product sum' in body(assembly, 'fixed_products')
            assert '; register-indexed strided byte store' in body(assembly, 'strided_store')
            for name in ('indexed_and', 'indexed_or'):
                assert '; short-circuit indexed byte pair' in body(assembly, name), name
            assert '; short-circuit indexed byte pair' not in body(assembly, 'indexed_independent')
            assert '; test byte beside struct padding' in body(assembly, 'padded_guard')
            assert '; test byte beside struct padding' not in body(assembly, 'mixed_guard')
            assert '; split packed byte index' in body(assembly, 'packed_clear')
            assert 'packed_mask_' in body(assembly, 'packed_clear')
            assert '; split packed byte index' in body(assembly, 'packed_set')
            for name in ('adjacent_ascending', 'adjacent_descending'):
                assert '; carry adjacent byte into next comparison' in body(assembly, name), name
            assert '; spill tested index on live edge' in body(assembly, 'guarded_save')
            for name in ('fold_left', 'fold_right'):
                assert '; carry-tested shift recurrence' in body(assembly, name), name
            assert '; register low-bit sum' in body(assembly, 'sum_low_bits')
            assert '; register low-bit sum' not in body(assembly, 'signed_remainders')
            assert '; carry-tested shift recurrence' not in body(assembly, 'volatile_shift')
            for name in ('overlap', 'changing_bound', 'alias_bound', 'volatile_loop'):
                part = body(assembly, name)
                assert '; widened fixed byte copy:' not in part, name
                if name != 'overlap':
                    assert '; structured byte loop:' not in part, name
            assert '; structured byte loop:' not in body(assembly, 'mixed_predicate')
            mixed = body(assembly, 'mixed_steps')
            assert mixed.count('; structured byte loop:') == 2, mixed
            assert '; structured byte loop:' not in body(assembly, 'repeated_index_step')
        sha = checks.run(directory, rom, sy, expect_calls={
            'filtered': 32, 'scatter': 32, 'fixed_odd': 1, 'overlap': 1,
            'fixed_block': 1, 'overlap_block': 1, 'fill_block': 1,
            'dynamic_forward': 2, 'dynamic_distinct': 1, 'stationary_source': 1,
            'fixed_sum': 1, 'fixed_sum_odd': 1, 'fixed_products': 1, 'strided_store': 3,
            'indexed_and': 3, 'indexed_or': 3, 'indexed_independent': 2,
            'padded_guard': 2, 'mixed_guard': 1, 'set_guard_values': 1, 'packed_clear': 3,
            'packed_set': 1, 'adjacent_ascending': 1, 'adjacent_descending': 1, 'guarded_save': 3,
            'fold_left': 4, 'fold_right': 4, 'sum_low_bits': 3, 'signed_remainders': 1, 'volatile_shift': 1,
            'changing_bound': 1, 'alias_bound': 1, 'volatile_loop': 1,
            'dependent_loops': 1, 'changing_predicate': 1, 'independent_loops': 1, 'self_start': 1, 'post_result': 1,
            'while_copy_plus': 2,
            'global_steps': 2, 'comma_steps': 1, 'mixed_steps': 1, 'repeated_index_step': 1,
            'while_copy': 2, 'sentinel': 1, 'signed_window': 2, 'signed_predicates': 1, 'cast_predicates': 1,
            'compare_bytes': 256, 'mixed_predicate': 1, 'expr_bound_char': 2,
            **{name: 256 for name in ('cmp_lt', 'cmp_le', 'cmp_gt', 'cmp_ge', 'cmp_eq', 'cmp_ne')}})
        reports[mode] = dict(rom_sha256=sha, filter_cases=32, max_backups=256, signed_byte_pairs=65536)
        print('PASS structured byte loops', mode, flush=True)
    (OUT / 'results.json').write_text(json.dumps(reports, indent=2) + '\n')


if __name__ == '__main__':
    main()
