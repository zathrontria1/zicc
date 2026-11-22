"""Check shorter code for branches, booleans, switch tables and arithmetic. Look for unnecessary stores at function exit and unused static inline functions."""
import os
import importlib.util
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
OUT = Path(os.environ.get('ZICC_LOGS_DIR', 'logs')).resolve() / 'control-stack-size-check'
SPEC = importlib.util.spec_from_file_location('support', ROOT / 'tests/check-compiler.py')
support = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(support)
support.OUT = OUT

SOURCE = r'''
#ifdef _MSC_VER
#include <stdint.h>
#include <stdbool.h>
typedef uintptr_t uaddr_t;
#else
#include <stdint.h>
#include <stdbool.h>
typedef unsigned int uaddr_t;
#endif

static uint16_t side_flag = 0;
uint32_t wide_global = 0x00150077uL;
uint8_t near_buf[32] = {3, 6, 9, 12, 15, 18, 21, 24};
uint8_t grid_flags[16];

static inline uint16_t unused_inline_a(uint16_t x) {
    return (uint16_t)(x * 7u + 13u);
}

static inline uint16_t unused_inline_b(uint16_t x, uint16_t y) {
    return (uint16_t)((x ^ y) + 99u);
}

static inline uint16_t taken_inline_cb(uint16_t x) {
    return (uint16_t)(x + 55u);
}

uint16_t (*const cb_table[1])(uint16_t) = { taken_inline_cb };

__noinline uint16_t pan_helper(uint16_t x) {
    return (uint16_t)((x + 5u) & 0xFFu);
}

__noinline uint16_t packed_helper(uint16_t packed) {
    return (uint16_t)(packed ^ 0x1234u);
}

__noinline uint16_t step_helper(uint16_t v) {
    return (uint16_t)(v * 3u + 1u);
}

__noinline uint16_t identical_ternary_const(uint16_t flag) {
    return flag ? 42u : 42u;
}

__noinline uint16_t side_effect_ternary(uint16_t flag) {
    (void)flag;
    return (++side_flag) ? 19u : 19u;
}

__noinline uint16_t identical_ternary_expr(uint16_t flag, uint16_t x) {
    return flag ? (uint16_t)(x + 3u) : (uint16_t)(x + 3u);
}

__noinline uint16_t local_bool_chain(uint16_t a, uint16_t b) {
    bool running = (a > 3u);
    bool armed = (b != 0u);
    bool blocked = running && armed;
    return (uint16_t)((uint16_t)running + ((uint16_t)armed << 1) +
                      ((uint16_t)(!!running) << 2) + ((uint16_t)blocked << 3));
}

__noinline uint16_t out_of_order_switch(uint16_t dir, uint16_t x) {
    uint16_t r = 0;
    switch (dir) {
    case 0: r = step_helper(x + 1u); break;
    case 7:
    case 6:
    case 5: r = step_helper(x + 9u); break;
    case 1: r = step_helper(x + 2u); break;
    case 2: r = step_helper(x + 3u); break;
    case 3: r = step_helper(x + 4u); break;
    case 4: r = step_helper(x + 5u); break;
    default: r = 77u; break;
    }
    return r;
}

__noinline uint16_t const_assign_switch(uint16_t s, uint16_t init) {
    uint16_t v = init;
    switch (s) {
    case 3: v = 40u; break;
    case 0: v = 10u; break;
    case 2: v = 30u; break;
    case 1: v = 20u; break;
    default: break;
    }
    return v;
}

__noinline uint16_t const_return_switch(uint16_t s) {
    switch (s) {
    case 5: return 500u;
    case 2:
    case 3: return 230u;
    case 4: return 400u;
    default: return 999u;
    }
}

__noinline uint16_t commute_imm_or_call(uint16_t x) {
    return (uint16_t)(2u | (pan_helper(x) << 8));
}

__noinline int16_t scroll_sub_high_word(int16_t a) {
    return (int16_t)(a - (int16_t)(wide_global >> 16));
}

__noinline uint16_t near_byte_addr_read(uint16_t idx) {
    const uint8_t *p = near_buf + idx;
    return *p;
}

__noinline void bounded_shift_store(uint16_t limit) {
    uint16_t i;
    for (i = 0; i < limit; ++i) {
        grid_flags[i >> 2] = (uint8_t)(1u << ((i & 3u) * 2u));
    }
}

__noinline uint16_t tail_dead_local(uint16_t x) {
    uint16_t pan = pan_helper(x);
    uint16_t packed;
    if (pan > 10u) pan = 10u;
    packed = (uint16_t)(3u | (pan << 8));
    return packed_helper(packed);
}

__noinline uint16_t dead_epilogue_region(uint16_t n) {
    const uint16_t * __far p = (const uint16_t * __far)0;
    uint16_t sum = 0, i;
    static const uint16_t vals[4] = {3, 5, 7, 11};
    p = vals;
    for (i = 0; i < n; ++i) {
        sum += p[i];
    }
    return sum;
}

int main(void) {
    if (identical_ternary_const(0u) != 42u || identical_ternary_const(9u) != 42u) return 1;
    if (side_effect_ternary(0u) != 19u || side_flag != 1u) return 2;
    if (identical_ternary_expr(0u, 7u) != 10u || identical_ternary_expr(5u, 7u) != 10u) return 3;
    if (local_bool_chain(0u, 0u) != 0u || local_bool_chain(5u, 0u) != 5u ||
        local_bool_chain(0u, 2u) != 2u || local_bool_chain(4u, 1u) != 15u) return 4;
    if (out_of_order_switch(0u, 1u) != 7u || out_of_order_switch(3u, 1u) != 16u ||
        out_of_order_switch(6u, 1u) != 31u || out_of_order_switch(8u, 1u) != 77u) return 5;
    if (const_assign_switch(0u, 99u) != 10u || const_assign_switch(3u, 99u) != 40u ||
        const_assign_switch(9u, 99u) != 99u) return 6;
    if (const_return_switch(2u) != 230u || const_return_switch(3u) != 230u ||
        const_return_switch(4u) != 400u || const_return_switch(5u) != 500u ||
        const_return_switch(1u) != 999u) return 7;
    if (commute_imm_or_call(4u) != 0x0902u) return 8;
    if (scroll_sub_high_word(30) != 9) return 9;
    if (near_byte_addr_read(3u) != 12u || near_byte_addr_read(6u) != 21u) return 10;
    bounded_shift_store(8u);
    if (grid_flags[0] != 0x40u || grid_flags[1] != 0x40u) return 11;
    if (tail_dead_local(2u) != (uint16_t)(0x0703u ^ 0x1234u)) return 12;
    if (tail_dead_local(99u) != (uint16_t)(0x0A03u ^ 0x1234u)) return 13;
    if (dead_epilogue_region(4u) != 26u) return 14;
    if (cb_table[0](10u) != 65u) return 15;
    return 0;
}
'''


def section(asm_text, name):
    return asm_text.split(f'_{name}:\n', 1)[1].split(f'__size_{name}', 1)[0]


def main():
    OUT.mkdir(parents=True, exist_ok=True)
    host_c = OUT / 'host.c'
    host_c.write_text(re.sub(r'\b(__noinline|__far)\b', '', SOURCE))
    host_exe = OUT / 'host.exe'
    support.run([ROOT / 'tools/msvc.cmd', '/nologo', '/std:c17', '/W4', '/O2',
                 '/Fo' + str(OUT / 'host.obj'), '/Fe' + str(host_exe), host_c])
    res = subprocess.run([str(host_exe)], timeout=5, creationflags=subprocess.CREATE_NO_WINDOW)
    assert res.returncode == 0, f'host exited with {res.returncode}'

    cfile = OUT / 'control_stack_size.c'
    cfile.write_text(SOURCE)
    raw = OUT / 'control_stack_size.raw'
    support.run([sys.executable, ROOT / 'tools/build-rom.py', cfile, '-o', raw])
    rom = raw.with_suffix('.sfc')
    support.run([ROOT / 'build/romtool.exe', raw, rom, ROOT / 'tests/title.txt'])
    labels = {name.removeprefix('_'): int(addr, 16)
              for addr, name in re.findall(r'^al ([0-9A-Fa-f]+) \.(\S+)$',
                                           raw.with_suffix('.labels').read_text(), re.M)}
    stage1_s = sorted((OUT / 'control_stack_size-allocation').glob('*/stage1/0_control_stack_size.s'))[-1]
    asm = stage1_s.read_text()

    # 5.5 Unreferenced static inline omitted; address-taken static inline retained
    assert 'unused_inline_a:' not in asm and 'unused_inline_b:' not in asm, asm
    assert 'taken_inline_cb:' in asm, asm

    # 5.1 Identical ternary arms folded without branching
    itc = section(asm, 'identical_ternary_const')
    assert 'beq' not in itc and 'bne' not in itc and 'bra' not in itc, itc
    assert 'lda #$002A' in itc, itc
    ite = section(asm, 'identical_ternary_expr')
    assert 'beq' not in ite and 'bne' not in ite and 'bra' not in ite, ite

    # 5.2 Local _Bool and !!bool reads avoid normalization branches
    lbc = section(asm, 'local_bool_chain')
    assert lbc.count('lda #1') == 3, lbc
    assert 'and #$00FF' not in lbc, lbc

    # 5.3 Out-of-order split switch and constant dense switch LUTs
    oos = section(asm, 'out_of_order_switch')
    assert '; split dense word switch' in oos, oos
    cas = section(asm, 'const_assign_switch')
    assert '; constant dense switch lookup table' in cas and '$000A,$0014,$001E,$0028' in cas, cas
    crs = section(asm, 'const_return_switch')
    assert '; constant dense switch lookup table' in crs and '$00E6,$00E6,$0190,$01F4' in crs, crs

    # 5.4 Commutative direct LHS, direct >> 16 word, near_buf + idx, and dead epilogue stores
    cioc = section(asm, 'commute_imm_or_call')
    assert 'pha' not in cioc and '__arith_rhs' not in cioc and 'ora #$0002' in cioc, cioc
    sshw = section(asm, 'scroll_sub_high_word')
    assert 'pha' not in sshw and '__arith_rhs' not in sshw, sshw
    nbar = section(asm, 'near_byte_addr_read')
    assert 'pha' not in nbar and '__arith_rhs' not in nbar, nbar
    tdl = section(asm, 'tail_dead_local')
    assert 'sta 1,s' not in tdl and 'sta 3,s' not in tdl, tdl
    der = section(asm, 'dead_epilogue_region')
    assert 'sta a:' not in der and 'sta 1,s' not in der and 'sta 3,s' not in der, der

    support.emulate(rom, labels, 0)
    check_nmi_switch()
    print('PASS control stack size: inline omission, ternary fold, bool norm, switch LUT/split, ALU/epilogue')


NMI_SWITCH_SOURCE = r'''
#include <stdint.h>
#define REG(a) (*(volatile unsigned char * __far)(a##UL))

unsigned nmi_idx = 0;
unsigned nmi_out = 0;
unsigned nmi_shift = 0;
unsigned nmi_after = 0;
volatile __dpage unsigned char nmi_done;

__interrupt(nmi) void user_nmi(void) {
    unsigned sel = nmi_idx;
    (void)REG(0x4210);
    switch (sel) {
        case 0: nmi_out = 10u; break;
        case 1: nmi_out = 20u; break;
        case 2: nmi_out = 30u; break;
        case 3: nmi_out = 40u; break;
    }
    nmi_shift = (uint16_t)(1u << (sel & 3u));
    nmi_after++;
    nmi_done = 1u;
}

int main(void) {
    static const unsigned expected[5] = {10u, 20u, 30u, 40u, 77u};
    static const unsigned indices[5] = {0u, 1u, 2u, 3u, 9u};
    unsigned i;
    (void)REG(0x4210);
    nmi_done = 1u;
    REG(0x4200) = 0x80u;
    for (i = 0; i < 5u; ++i) {
        *(volatile unsigned *)&nmi_out = 77u;
        *(volatile unsigned *)&nmi_idx = indices[i];
        nmi_done = 0u;
        while (!nmi_done) {}
        if (*(volatile unsigned *)&nmi_out != expected[i]) { REG(0x4200) = 0u; return (int)(i + 1u); }
        if (*(volatile unsigned *)&nmi_shift != (unsigned)(1u << (indices[i] & 3u))) {
            REG(0x4200) = 0u;
            return (int)(i + 10u);
        }
    }
    REG(0x4200) = 0u;
    return *(volatile unsigned *)&nmi_after == 5u ? 0 : 20;
}
'''


def check_nmi_switch():
    cfile = OUT / 'nmi_switch.c'
    cfile.write_text(NMI_SWITCH_SOURCE)
    raw_s = OUT / 'nmi_switch_raw.s'
    support.run([ROOT / 'build/zicc.exe', cfile, '-o', raw_s, '-I', ROOT / 'include', '--binary64'])
    raw_nmi = raw_s.read_text().split('.segment "NMI_USER"\n.export _user_nmi\n_user_nmi:\n', 1)[1].split('.segment "NMI_END"', 1)[0]
    assert '; constant dense switch lookup table' in raw_nmi, raw_nmi
    assert '; bounded word shift lookup' in raw_nmi, raw_nmi
    assert '.segment "RODATA"' in raw_nmi, raw_nmi
    assert '.segment "CODE"' not in raw_nmi, raw_nmi
    assert raw_nmi.count('.segment "NMI_USER"') >= 2, raw_nmi

    raw = OUT / 'nmi_switch.raw'
    support.run([sys.executable, ROOT / 'tools/build-rom.py', cfile, '-o', raw])
    rom = raw.with_suffix('.sfc')
    support.run([ROOT / 'build/romtool.exe', raw, rom, ROOT / 'tests/title.txt'])
    labels = {name.removeprefix('_'): int(addr, 16)
              for addr, name in re.findall(r'^al ([0-9A-Fa-f]+) \.(\S+)$',
                                           raw.with_suffix('.labels').read_text(), re.M)}
    stage1_s = sorted((OUT / 'nmi_switch-allocation').glob('*/stage1/0_nmi_switch.s'))[-1]
    asm = stage1_s.read_text()
    nmi_body = section(asm, 'user_nmi').split('.segment "NMI_END"', 1)[0]
    assert '; constant dense switch lookup table' in nmi_body, nmi_body
    assert '; bounded word shift lookup' in nmi_body, nmi_body
    assert '.segment "CODE"' not in nmi_body, nmi_body
    assert nmi_body.count('.segment "NMI_USER"') >= 2, nmi_body
    after_switch_lut = nmi_body.split('switch_lut_', 1)[1].split('.segment "NMI_USER"', 1)[1]
    assert '_nmi_out' in after_switch_lut, after_switch_lut
    tail_after_luts = nmi_body.rsplit('.segment "NMI_USER"', 1)[1]
    assert '_nmi_after' in tail_after_luts and '_nmi_done' in tail_after_luts, tail_after_luts
    support.emulate(rom, labels, 0)


if __name__ == '__main__':
    main()
