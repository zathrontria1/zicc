"""Verify general compiler codegen optimizations across equivalent C spellings."""
import importlib.util
import os
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
OUT = Path(os.environ.get('ZICC_LOGS_DIR', 'logs')).resolve() / 'codegen-optimizations-check'
spec = importlib.util.spec_from_file_location('support', ROOT / 'tests/check-compiler.py')
support = importlib.util.module_from_spec(spec)
spec.loader.exec_module(support)


SOURCE = r'''#include <stdbool.h>
#include <stdint.h>

extern uint16_t ext_words[];
uint16_t ext_words[8] = {0x1234, 0x5678, 0x9ABC, 0xDEF0, 1, 2, 3, 4};

const uint8_t far_bytes[4] = {10, 20, 30, 40};

struct Vec { int16_t x; int16_t y; int16_t vx; int16_t vy; };
struct BytePair { uint8_t hp; uint8_t timer; uint16_t flags; };

uint8_t sat8_assign(uint8_t *dst, uint8_t a, uint8_t b) {
    *dst = a > b ? a - b : 0;
    return *dst;
}
uint8_t sat8_1(uint8_t a, uint8_t b) { return a >= b ? (uint8_t)(a - b) : 0; }
uint8_t sat8_2(uint8_t a, uint8_t b) { return b < a ? (uint8_t)(a - b) : 0; }
uint8_t sat8_3(uint8_t a, uint8_t b) { return b <= a ? (uint8_t)(a - b) : 0; }
uint8_t sat8_4(uint8_t a, uint8_t b) { return a <= b ? 0 : (uint8_t)(a - b); }
uint8_t sat8_5(uint8_t a, uint8_t b) { return a < b ? 0 : (uint8_t)(a - b); }
uint8_t sat8_6(uint8_t a, uint8_t b) { return b >= a ? 0 : (uint8_t)(a - b); }
uint8_t sat8_7(uint8_t a, uint8_t b) { return b > a ? 0 : (uint8_t)(a - b); }

uint16_t sat16_0(uint16_t a, uint16_t b) { return a > b ? a - b : 0; }
uint16_t sat16_1(uint16_t a, uint16_t b) { return a <= b ? 0 : a - b; }

uint16_t range_and(uint16_t flag, uint16_t x) {
    return flag && x >= 2 && x <= 7;
}

uint16_t range_or(uint16_t flag, uint16_t x) {
    return flag || x < 2 || x > 7;
}

uint16_t choose_const_add(uint16_t c) {
    return 0x180 + (c ? 2 : 0);
}

int16_t choose_sub(int16_t ahead, uint16_t slime) {
    return ahead - (slime ? 0x200 : 0x140);
}

int16_t shared_add(const struct Vec *p) {
    return p->x + p->vx;
}

int16_t local_compound(int16_t spread) {
    struct Vec v = {10, 20, 0, 0};
    v.y += spread;
    return v.y;
}

static uint16_t ipa_leaf(uint16_t x, uint16_t k) { return x + k; }
static uint16_t ipa_mid(uint16_t x, uint16_t k) { return ipa_leaf(x, k); }
uint16_t ipa_outer(uint16_t x) { return ipa_mid(x, 7); }

uint8_t ext_cast_index(uint16_t i) {
    const uint8_t *p = (const uint8_t *)ext_words;
    return p[i];
}

uint32_t far_addr_val(void) {
    return (uint32_t)far_bytes;
}

uint16_t local_bool_test(uint16_t a, uint16_t b) {
    bool ok = a > b;
    if (ok) return 11;
    return 22;
}

void coalesce_byte_stores(struct BytePair *p, uint8_t v) {
    p->hp = v;
    p->timer = 60;
}

uint16_t tail_callee(uint16_t x) { return x + 3; }
uint16_t tail_caller(uint16_t x) { return tail_callee(x); }

uint16_t global_step_word = 10;
uint16_t rmw_step_old(void) {
    return global_step_word++;
}

int main(void) {
    struct Vec v = {100, 200, 25, -5};
    struct BytePair bp = {10, 0, 0};
    uint8_t sat_out = 0;
    if (sat8_assign(&sat_out, 5, 3) != 2 || sat8_assign(&sat_out, 3, 5) != 0 || sat8_assign(&sat_out, 0, 0) != 0 || sat8_assign(&sat_out, 255, 1) != 254) return 1;
    if (sat8_1(5, 3) != 2 || sat8_2(5, 3) != 2 || sat8_3(5, 3) != 2) return 2;
    if (sat8_4(5, 3) != 2 || sat8_5(5, 3) != 2 || sat8_6(5, 3) != 2 || sat8_7(5, 3) != 2) return 3;
    if (sat8_1(3, 5) != 0 || sat8_2(3, 5) != 0 || sat8_3(3, 5) != 0) return 4;
    if (sat8_4(3, 5) != 0 || sat8_5(3, 5) != 0 || sat8_6(3, 5) != 0 || sat8_7(3, 5) != 0) return 5;
    if (sat16_0(1000, 300) != 700 || sat16_0(300, 1000) != 0 || sat16_1(0xFFFF, 1) != 0xFFFE) return 6;
    if (!range_and(1, 2) || !range_and(1, 7) || range_and(1, 1) || range_and(1, 8) || range_and(0, 5)) return 7;
    if (range_or(0, 5) || !range_or(0, 1) || !range_or(0, 8) || !range_or(1, 5)) return 8;
    if (choose_const_add(1) != 0x182 || choose_const_add(0) != 0x180) return 9;
    if (choose_sub(0x300, 1) != 0x100 || choose_sub(0x300, 0) != 0x1C0) return 10;
    if (shared_add(&v) != 125 || local_compound(15) != 35) return 11;
    if (ipa_outer(5) != 12) return 12;
    if (ext_cast_index(0) != 0x34 || ext_cast_index(1) != 0x12) return 13;
    if (far_addr_val() == 0) return 14;
    if (local_bool_test(9, 2) != 11 || local_bool_test(2, 9) != 22) return 15;
    coalesce_byte_stores(&bp, 42);
    if (bp.hp != 42 || bp.timer != 60) return 16;
    if (tail_caller(10) != 13) return 17;
    if (rmw_step_old() != 10 || global_step_word != 11) return 18;
    return 0;
}
'''


def fn_body(asm_text, name):
    m = re.search(rf'^{re.escape(name)}:\s*\n(.*?)(?=^_[A-Za-z0-9_]+:|^\.segment|\Z)',
                  asm_text, re.M | re.S)
    assert m, f'missing function {name}'
    return m.group(1)


def main():
    OUT.mkdir(parents=True, exist_ok=True)
    support.OUT = OUT
    _, rom, labels = support.compile_case('codegen_opt', SOURCE)
    asm = (OUT / 'codegen_opt.s').read_text(encoding='ascii')

    # Saturating subtraction should use branchless/short sbc + bcs + lda #0
    for name in ('_sat8_assign', '_sat16_0', '_sat16_1'):
        body = fn_body(asm, name)
        assert 'sbc ' in body and 'bcs ' in body, f'{name} did not use saturating sbc/bcs:\n{body}'

    # Constant + choose folds to immediate loads
    choose_add = fn_body(asm, '_choose_const_add')
    assert '#$0182' in choose_add and '#$0180' in choose_add, f'choose_const_add not folded:\n{choose_add}'

    # Incomplete extern array cast uses indexed addressing
    ext = fn_body(asm, '_ext_cast_index')
    assert 'a:.loword(_ext_words+$0000),x' in ext, f'ext_cast_index not indexed:\n{ext}'

    # RMW step uses inc on memory
    rmw = fn_body(asm, '_rmw_step_old')
    assert 'inc a:.loword(_global_step_word)' in rmw, f'rmw_step_old did not use inc mem:\n{rmw}'

    # Local bool test omits and #$00FF
    lbool = fn_body(asm, '_local_bool_test')
    assert '#$00FF' not in lbool, f'local_bool_test emitted redundant mask:\n{lbool}'

    # Build and run in Mesen
    support.emulate(rom, labels, 0)
    print('PASS codegen-optimizations')


if __name__ == '__main__':
    main()
