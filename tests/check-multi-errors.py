"""Verify multi-error reporting per translation unit and across build-rom.py inputs."""
import json
import os
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
OUT = Path(os.environ.get('ZICC_LOGS_DIR', 'logs')).resolve() / 'multi-errors-check'


def run_zicc(name, source, extra=()):
    OUT.mkdir(parents=True, exist_ok=True)
    c_path = OUT / (name + '.c')
    s_path = OUT / (name + '.s')
    s_path.unlink(missing_ok=True)
    c_path.write_text(source)
    result = subprocess.run(
        [str(ROOT / 'build/zicc.exe'), str(c_path), '-o', str(s_path), *map(str, extra)],
        cwd=ROOT, capture_output=True, text=True, timeout=30,
        creationflags=getattr(subprocess, 'CREATE_NO_WINDOW', 0),
    )
    assert result.returncode != 0, (name, result.stdout, result.stderr)
    assert not s_path.exists(), (name, 'assembly should not be written on error')
    return result.stderr


def main():
    OUT.mkdir(parents=True, exist_ok=True)
    results = {}

    # 1. Multi-entry static ROM pointer table
    stderr = run_zicc('rom_table', '''
const unsigned char a[2] = {1, 2};
const unsigned char b[2] = {3, 4};
const unsigned char c[2] = {5, 6};
const unsigned char *table[3] = {
    a,
    b,
    c
};
''')
    errors = [ln for ln in stderr.splitlines() if ': error:' in ln]
    assert len(errors) == 3, stderr
    results['rom_table'] = len(errors)

    # 2. Multiple call arguments and ROM-to-near casts in one function (no duplicates)
    stderr = run_zicc('calls_and_casts', '''
const unsigned char rom_a[4] = {1, 2, 3, 4};
const unsigned char rom_b[4] = {5, 6, 7, 8};
void take(const unsigned char *p, const unsigned char *q);
void sink(const unsigned char * __far p);
void test(void) {
    take(rom_a, rom_b);
    sink((unsigned char *)rom_a);
    sink((unsigned char *)rom_b);
}
''')
    errors = [ln for ln in stderr.splitlines() if ': error:' in ln]
    assert len(errors) == 4, stderr
    results['calls_and_casts'] = len(errors)

    # 3. Static initializer ROM cast reports once (no duplicate between convert and initializer_address)
    stderr = run_zicc('static_rom_cast', '''
const unsigned char rom_table[4] = {1, 2, 3, 4};
unsigned char *p = (unsigned char *)rom_table;
''')
    errors = [ln for ln in stderr.splitlines() if ': error:' in ln]
    assert len(errors) == 1 and 'ROM address is not representable' in errors[0], stderr
    results['static_rom_cast'] = len(errors)

    # 4. Broken local pointer initializer keeps variable declared (no undeclared identifier cascade)
    stderr = run_zicc('local_decl_keep', '''
const unsigned char rom_table[4] = {1, 2, 3, 4};
void sink(const unsigned char * __far p);
void f(void) {
    const unsigned char *p = rom_table;
    sink(p);
}
''')
    errors = [ln for ln in stderr.splitlines() if ': error:' in ln]
    assert len(errors) == 1 and 'undeclared' not in stderr, stderr
    results['local_decl_keep'] = len(errors)

    # 5. Syntax/expression recovery inside blocks and across functions + warning still emitted
    stderr = run_zicc('block_recovery', '''
void old() {}
int first(void) {
    int x = ;
    return missing_var;
}
int second(void) {
    return also_missing;
}
''')
    errors = [ln for ln in stderr.splitlines() if ': error:' in ln]
    warnings = [ln for ln in stderr.splitlines() if ': warning:' in ln]
    assert len(errors) >= 3 and 'missing_var' in stderr and 'also_missing' in stderr, stderr
    assert len(warnings) == 1 and 'old-style function definition' in warnings[0], stderr
    results['block_recovery'] = len(errors)

    # 6. Top-level recovery across broken globals and structs
    stderr = run_zicc('top_level_recovery', '''
int bad_global = ;
struct Broken { int x };
int after_broken(void) {
    return undeclared_after;
}
''')
    errors = [ln for ln in stderr.splitlines() if ': error:' in ln]
    assert len(errors) >= 3 and 'undeclared_after' in stderr, stderr
    results['top_level_recovery'] = len(errors)

    # 7. 50-error cap
    lines = ['const unsigned char r[2] = {1, 2};']
    lines += [f'const unsigned char *p{i} = r;' for i in range(70)]
    stderr = run_zicc('error_cap', '\n'.join(lines) + '\n')
    errors = [ln for ln in stderr.splitlines() if ': error:' in ln]
    assert len(errors) == 50 and 'too many errors, stopping' in stderr, (len(errors), stderr)
    results['error_cap'] = len(errors)

    # 8. --lto + --lto-source reports errors across multiple TUs
    tu2 = OUT / 'lto_tu2.c'
    tu2.write_text('int g(void) { return missing_in_tu2; }\n')
    stderr = run_zicc('lto_tu1', 'int f(void) { return missing_in_tu1; }\n',
                      extra=['--lto', '--lto-source', tu2])
    assert 'missing_in_tu1' in stderr and 'missing_in_tu2' in stderr, stderr
    results['lto_multi_tu'] = 2

    # 9. build-rom.py collects errors across multiple .c files in one build
    first = OUT / 'first.c'
    middle = OUT / 'middle.c'
    last = OUT / 'last.c'
    raw = OUT / 'multi.raw'
    raw.unlink(missing_ok=True)
    first.write_text('int f(void) { return err_first; }\n')
    middle.write_text('int main(void) { return 0; }\n')
    last.write_text('int l(void) { return err_last; }\n')
    built = subprocess.run(
        [sys.executable, str(ROOT / 'tools/build-rom.py'), str(first), str(middle), str(last), '-o', str(raw)],
        cwd=ROOT, capture_output=True, text=True, timeout=60,
        creationflags=getattr(subprocess, 'CREATE_NO_WINDOW', 0),
    )
    assert built.returncode != 0 and not raw.exists(), (built.stdout, built.stderr)
    combined = built.stdout + built.stderr
    assert 'err_first' in combined and 'err_last' in combined, combined
    results['build_rom_multi_file'] = 2

    (OUT / 'results.json').write_text(json.dumps(results, indent=2) + '\n')
    print('PASS: multi-error reporting across statements, tables, top-level, LTO, and build-rom.py')


if __name__ == '__main__':
    main()
