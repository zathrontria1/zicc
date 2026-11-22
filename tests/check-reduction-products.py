"""Check variable byte reductions, guarded products and compact recursive calls."""
import json
import os
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
OUT = Path(os.environ.get('ZICC_LOGS_DIR', 'logs')).resolve() / 'reduction-products-check'
sys.path.insert(0, str(ROOT / 'tools'))
from mesen_core import Core

KERNELS = r'''
#include <stdint.h>

uint8_t data[32780];
volatile uint8_t read_once[4];
uint16_t last, factors[4], calls;
uint32_t accumulator;

uint16_t sum_indexed(uint16_t count, uint16_t seed)
{
    unsigned i;
    for (i=0; i<count; ++i) seed = data[i+3] + seed;
    last = i;
    return seed;
}

uint16_t sum_plain(uint16_t count)
{
    uint16_t sum=0;
    for (unsigned i=0; i<count; i+=1) sum += (uint16_t)data[i];
    return sum;
}

uint16_t sum_signed(uint16_t count)
{
    uint16_t sum=0;
    for (unsigned i=0; i<count; ++i) sum += (int8_t)data[i];
    return sum;
}

uint16_t sum_volatile(uint16_t count)
{
    uint16_t sum=0;
    for (unsigned i=0; i<count; ++i) sum += read_once[i];
    return sum;
}

uint32_t two_products(unsigned f, unsigned at)
{
    return accumulator*f + 10000UL*factors[at];
}

uint32_t commuted_products(unsigned a, unsigned f)
{
    return (uint32_t)a*0x1379UL + f*accumulator;
}

uint16_t read_factor(unsigned a)
{
    ++calls;
    return a;
}

uint32_t product_with_call(unsigned a, unsigned f)
{
    return 10000UL*read_factor(a) + accumulator*f;
}

uint32_t down_product(unsigned n)
{
    if (n <= 1U) return 1UL;
    return down_product(n-1U) * n;
}

uint32_t step_product(unsigned n)
{
    if (n >= 256U) {
        uint32_t child = step_product(n-2U);
        return n * child;
    } else {
        return 0x12345UL;
    }
}

uint32_t escaped_product(unsigned n)
{
    extern void modify(unsigned *);
    if (n < 2U) return 1UL;
    uint32_t child=escaped_product(n-1U);
    modify(&n);
    return n*child;
}
'''

DRIVER = r'''
#include <stdint.h>
extern uint8_t data[32780];
extern volatile uint8_t read_once[4];
extern uint16_t last, factors[4], calls;
extern uint32_t accumulator;
uint16_t sum_indexed(uint16_t,uint16_t), sum_plain(uint16_t);
uint16_t sum_signed(uint16_t), sum_volatile(uint16_t);
uint32_t two_products(unsigned,unsigned), commuted_products(unsigned,unsigned);
uint32_t product_with_call(unsigned,unsigned);
uint32_t down_product(unsigned), step_product(unsigned), escaped_product(unsigned);
void modify(unsigned *n) {++*n;}
uint32_t multiply(uint32_t a, uint32_t b) {return a*b;}

const uint16_t counts[]={0,1,2,3,7,8,255,256,1027,0x8001U};
const uint16_t words[]={0,1,134,135,136,137,217,218,255,256,4097,65535U};
const uint32_t longs[]={0,1,255,256,65535UL,65536UL,0x80000000UL,0xffffffffUL};
int main(void)
{
    unsigned i,j,k,n,f,a;
    uint16_t seed, want, plain;
    uint32_t expected;
    for (i=0;i<sizeof data;++i) data[i]=(uint8_t)(255-i*7U);
    for (k=0;k<sizeof counts/sizeof counts[0];++k) {
        n=counts[k]; seed=65520U+k; want=seed; plain=0;
        for (i=0;i<n;++i) {
            want+=data[i+3];
            plain+=data[i];
        }
        last=65535U;
        if (sum_indexed(n,seed)!=want||last!=n||sum_plain(n)!=plain) return 1;
    }
    data[0]=255; data[1]=128; data[2]=127;
    read_once[0]=255; read_once[1]=3; read_once[2]=128;
    if (sum_signed(3)!=65534U || sum_volatile(3)!=386U) return 2;
    for (k=0;k<sizeof longs/sizeof longs[0];++k) {
        accumulator=longs[k];
        for (i=0;i<sizeof words/sizeof words[0];++i) {
            f=words[i];
            for (j=0;j<sizeof words/sizeof words[0];++j) {
                a=words[j]; factors[3]=a;
                expected=multiply(accumulator,f);
                if (two_products(f,3)!=expected+multiply(10000UL,a)) return 3;
                if (commuted_products(a,f)!=expected+multiply(0x1379UL,a)) return 4;
            }
        }
    }
    calls=0; accumulator=123;
    if (product_with_call(78,34)!=784182UL||calls!=1) return 5;
    expected=1;
    for (i=0;i<22;++i) {
        if (i) expected=multiply(expected,i);
        if (down_product(i)!=expected) return 6;
    }
    if (step_product(255)!=0x12345UL || step_product(259)!=
        multiply(multiply(0x12345UL,257),259)) return 7;
    if (escaped_product(4)!=60UL) return 8;
    return 0;
}
'''


def function_body(assembly, name):
    return assembly.split(f'_{name}:', 1)[1].split(f'__size_{name} =', 1)[0]


def worker(folder):
    symbols = {name: int(address, 16) for address, name in re.findall(
        r'^al (\w+) \.(\S+)$', (folder / 'test.labels').read_text(), re.M)}
    code = f'''
emu.addMemoryCallback(function()
    local s=emu.getState()
    assert(s['cpu.a']==0, 'Fixture return code '..s['cpu.a'])
    assert(s['cpu.sp']==0x4ff and s['cpu.d']==0 and s['cpu.dbr']==0x7e and s['cpu.y']==0, 'ABI')
    emu.log('REDUCTIONS PASS')
    emu.breakExecution()
end,emu.callbackType.exec,{symbols['main_exit']},{symbols['main_exit']})
'''
    script = folder / 'check.lua'
    script.write_text(code, encoding='ascii')
    core = Core(folder / 'mesen')
    try:
        core.load(folder / 'test.sfc', script, code)
        core.start()
        log = core.wait_for('REDUCTIONS PASS', 30)
        (folder / 'emulator.log').write_text(log, encoding='utf-8')
    finally:
        core.close_with_log(folder / 'emulator.log')


def command(*args):
    subprocess.run([str(arg) for arg in args], cwd=ROOT, check=True)


def main():
    OUT.mkdir(parents=True, exist_ok=True)
    driver, kernels = OUT / 'driver.c', OUT / 'kernels.c'
    driver.write_text(DRIVER, encoding='ascii')
    kernels.write_text(KERNELS, encoding='ascii')
    checks = {
        'register unsigned byte sum with runtime bound': ('sum_indexed', 'sum_plain'),
        'guarded narrow sum of widened products': ('two_products', 'commuted_products'),
        'compact recursive word product frame': ('down_product', 'step_product'),
    }
    fallback = OUT / 'fallback.s'
    command(ROOT / 'build/zicc.exe', kernels, '-o', fallback, '-I', ROOT / 'include',
            '--no-strength-reduction', '--no-body-optimizations')
    for marker in checks:
        assert marker not in fallback.read_text(), marker
    for stage in (1, 4):
        folder = OUT / f'stage{stage}'
        folder.mkdir(exist_ok=True)
        rom = folder / 'test.sfc'
        command(sys.executable, ROOT / 'tools/build-rom.py', driver, kernels,
                '--stage', stage, '--keep-intermediates', '-o', rom)
        manifest = json.loads(rom.with_suffix('.allocation.json').read_text())
        assembly = (Path(manifest['evidence']) / f'stage{stage}' / '1_kernels.s').read_text()
        for marker, names in checks.items():
            for name in names:
                assert marker in function_body(assembly, name), (stage, name, marker)
        for name in ('sum_signed', 'sum_volatile', 'product_with_call', 'escaped_product'):
            assert all(marker not in function_body(assembly, name) for marker in checks), (stage, name)
        command(sys.executable, __file__, '--worker', folder)
        print(f'PASS reduction and product lowering, layout stage {stage}', flush=True)


if __name__ == '__main__':
    if sys.argv[1:2] == ['--worker']:
        worker(Path(sys.argv[2]))
    else:
        main()
