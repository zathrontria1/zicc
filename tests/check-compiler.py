"""Build small C programs, run them in the SNES emulator, and check their results."""
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'tools'))
import host_cache
import run_cache  # noqa: E402
from check_diagnostics import save_log
LOGS = Path(os.environ.get('ZICC_LOGS_DIR', 'logs')).resolve()
OUT = Path(os.environ.get('ZICC_COMPILER_CHECK_OUT', LOGS / 'compiler-check'))
CC65 = Path(os.environ.get('CC65_BIN', 'C:/bin/cc65/bin'))


def emulator_run_key(command):
    """Identify a Mesen run by its settings and the contents of its ROM and Lua files.

    Return the key and its label, or (None, None) when Mesen must run."""
    arguments = list(map(str, command))
    if not run_cache.enabled() or '--testRunner' not in arguments or Path(arguments[0]).name.lower() != 'mesen.exe':
        return None, None
    executable = Path(arguments[0])
    settings = executable.parent / 'settings.json'
    parts, label = [], executable.name
    for argument in arguments[1:]:
        path = Path(argument)
        if path.is_file():
            if path.suffix.lower() == '.lua' and not run_cache.cacheable_script(path.read_text(errors='replace')):
                run_cache.record('bypass', f'{path.name} (script not cacheable)')
                return None, None
            parts.append(['file', run_cache.file_sha256(path)])
            if path.suffix.lower() in ('.sfc', '.smc'):
                label = path.name
        else:
            parts.append(['arg', argument])
    return run_cache.key(kind='testrunner', mesen=run_cache.file_sha256(executable),
                         settings=settings.read_text() if settings.exists() else None, arguments=parts), label


def run(command, expected=0, cwd=ROOT, timeout=30, *, binary64=True):
    # These cases use 64-bit doubles by default. Pass binary64=False to test
    # the compiler with its usual 32-bit doubles
    if binary64 and (Path(command[0]).name.lower() == 'zicc.exe' or
                     len(command) > 1 and Path(command[1]).name == 'build-rom.py'):
        if '--binary64' not in command:
            command = [*command, '--binary64']
    if Path(command[0]).name.lower()=='ld65.exe' and '-C' in command:
        config=Path(command[command.index('-C')+1]).resolve()
        if config.parent==ROOT/'linker':
            command=[sys.executable,ROOT/'tools/link-runtime-ram.py',*command[1:]]
    host=host_cache.prepare(command,cwd) if expected==0 else None
    if host and 'hit' in host:return host['hit']
    if host:command=host['command']
    digest, label = emulator_run_key(command)
    if digest:
        entry = run_cache.get(digest, label)
        if entry is not None and entry['returncode'] == expected:
            return subprocess.CompletedProcess(list(map(str, command)), entry['returncode'], entry['stdout'], entry['stderr'])
    env = dict(os.environ, ZICC_LOGS_DIR=str(LOGS))
    result = subprocess.run(list(map(str, command)), cwd=cwd, env=env, capture_output=True, text=True,
                            timeout=timeout, creationflags=subprocess.CREATE_NO_WINDOW)
    if result.returncode != expected:
        raise AssertionError(f'{command}: exit {result.returncode}\n{result.stdout}{result.stderr}')
    if host:host_cache.store(host,result)
    if digest:
        run_cache.put(digest, dict(returncode=result.returncode, stdout=result.stdout, stderr=result.stderr, rom=label))
    return result


def symbols(path):
    return {name: int(address, 16) for address, name in (line.split() for line in path.read_text().splitlines())}


_MESEN_EXECUTABLES = {}


def mesen_executable(output=None):
    # Portable Mesen stores state beside its executable. Each suite owns this
    # directory, including callers that only use the launcher, not emulate()
    tools = (OUT if output is None else Path(output)) / 'mesen'
    if tools in _MESEN_EXECUTABLES:
        return _MESEN_EXECUTABLES[tools]
    tools.mkdir(parents=True, exist_ok=True)
    emulator = tools / 'Mesen.exe'
    original = Path('C:/bin/Mesen/Mesen.exe')
    if not emulator.exists() or hashlib.sha256(emulator.read_bytes()).digest() != hashlib.sha256(original.read_bytes()).digest():
        shutil.copyfile(original, emulator)
    (tools / 'settings.json').write_text('{}')
    _MESEN_EXECUTABLES[tools] = emulator
    return emulator


def emulate_embedded_worker(rom, lua, timeout_seconds):
    from mesen_core import Core
    checks = lua.read_text()
    core = Core(lua.parent / (rom.stem + '-core'))
    try:
        core.load(rom, lua, checks)
        core.start()
        return core.wait_for('TARGET_VERDICT', timeout_seconds)
    finally:
        core.close_with_log(lua.with_suffix('.log'))


def emulate(rom, labels, expected_return=None, seed=False, extra_checks='', timeout_seconds=8, *, embedded=False, expected_abort=False):
    stack_top = labels.get('_STACK_TOP__', 0x04ff)
    checks = '''
local done,bad,entered,cleared=false,false,false,false
local visits=0
local stamps={}
local function require_value(ok, message)
    if not ok then print('FAIL '..message);bad=true;done=true end
end
'''
    checks += extra_checks
    if seed:
        checks += '''
for i=0,0x1ffff do emu.write(((i)&0x1ffff),0xa5,emu.memType.snesWorkRam) end
'''
        checks += f'''
local imported=emu.getLabelAddress('_main') or emu.getLabelAddress('main')
require_value(imported~=nil and imported.address=={(labels['main'] - 0xc00000) if labels['main'] >= 0xc00000 else (labels['main'] & 0x7fff)},'Mesen debug-symbol import')
'''
    if seed:
        clear_spans = {'ZEROPAGE', 'LORAM_BSS', 'BSS',
                       'CONSOLE_MAP', 'RUNTIME_BSS', 'RUNTIME_CLOCK', 'RUNTIME_CONSOLE'}
        checks += 'local cleared_bytes, unchecked_bytes = {}, {}\n'
        for symbol, address in labels.items():
            if not symbol.startswith('_') or not symbol.endswith('_RUN__'):
                continue
            name = symbol[1:-6]
            if name in clear_spans or name.startswith(('NEAR_BSS_', 'NEAR_DATA_', 'ZWRAM_B_', 'ZWRAM_D_')):
                size = labels[f'_{name}_SIZE__']
                start = address & 0x1ffff
                table = 'unchecked_bytes' if name.startswith(('NEAR_DATA_', 'ZWRAM_D_')) else 'cleared_bytes'
                checks += f'for i={start},{start+size-1} do {table}[i]=true end\n'
        scratch = labels['_SCRATCH_START__']
        checks += f'for i={scratch},{scratch+labels["_SCRATCH_SIZE__"]-1} do cleared_bytes[i]=true end\n'
        checks += f'''
emu.addMemoryCallback(function()
    cleared=true
    cleared_bytes[0], cleared_bytes[1] = true, true
    -- The generated initializer can use the top three stack bytes and
    -- has already copied individually allocated initialized near objects
    for i=0,0x1ffff do
        if (i<{stack_top-2} or i>{stack_top}) and not unchecked_bytes[i] then
            local expected = cleared_bytes[i] and 0 or 0xa5
            if emu.read(i,emu.memType.snesWorkRam,false)~=expected then
                require_value(false,'WRAM startup byte '..i);break
            end
        end
    end
end,emu.callbackType.exec,{labels['ram_cleared']},{labels['ram_cleared']})
'''
    else:
        checks += f'''
emu.addMemoryCallback(function() cleared=true end,emu.callbackType.exec,{labels['ram_cleared']},{labels['ram_cleared']})
'''
    checks += f'''
emu.addMemoryCallback(function()
    if not entered then
        entered=true
        local s=emu.getState()
        require_value(cleared,'main reached before RAM-clear checkpoint')
        require_value(s['cpu.a']==0 and s['cpu.x']==0 and s['cpu.y']==0,'entry A/X/Y')
        require_value(s['cpu.d']==0 and s['cpu.dbr']==0x7e and s['cpu.k']=={labels['main'] >> 16},'entry D/DBR/PBR')
        require_value(s['cpu.sp']==0x{stack_top-3:04x} and not s['cpu.emulationMode'],'entry stack/native mode')
        require_value((s['cpu.ps'] & 0x3c)==4,'entry M/X/decimal/IRQ flags')
        print('ENTRY A=0 X=0 Y=0 D=0 DBR=7E PBR={labels['main'] >> 16:02X} S={stack_top-3:04X} native A16 X16')
    end
'''
    if expected_return is None:
        checks += '''
    visits=visits+1
    if visits<=8 then stamps[#stamps+1]=emu.getState().masterClock end
    if visits>=8 then done=true end
'''
    checks += f'end,emu.callbackType.exec,{labels["main"]},{labels["main"]})\n'
    if expected_return is not None:
        # The runtime's abort entry shares main_exit and clears A. A normal
        # return check must reject that path before checking A and the stack
        abort_entries = {labels[name] for name in ('abort', '__builtin_abort') if name in labels}
        if expected_abort:
            assert abort_entries, "Expected abort requires a runtime abort entry"
        checks += "local observed_abort=false\n"
        for address in sorted(abort_entries):
            on_abort = "observed_abort=true" if expected_abort else "require_value(false,'abort before normal return')"
            checks += f'''
    emu.addMemoryCallback(function() {on_abort} end,
                          emu.callbackType.exec,{address},{address})
    '''
        checks += f'''
emu.addMemoryCallback(function()
    if done then return end
    require_value(entered,'exit before main')
    require_value(not {str(expected_abort).lower()} or observed_abort,'expected abort was not reached')
    require_value(emu.getState()['cpu.a']=={expected_return & 0xffff},'return value')
    require_value(emu.getState()['cpu.sp']==0x{stack_top:04x},'stack balance at main exit')
    done=true
end,emu.callbackType.exec,{labels['main_exit']},{labels['main_exit']})
'''
    checks += '''
emu.addEventCallback(function()
    if done then
        if not bad then
            print('PASS')
            if #stamps>1 then
                local deltas={}
                for i=2,#stamps do deltas[#deltas+1]=stamps[i]-stamps[i-1] end
                print('LOOP_MASTER_CLOCK_DELTAS '..table.concat(deltas,','))
            end
        end
        emu.stop(bad and 1 or 0)
    end
end,emu.eventType.endFrame)
'''
    lua = OUT / (rom.stem + '.lua')
    log = OUT / (rom.stem + '.log')
    if embedded:
        checks = checks.replace('emu.stop(bad and 1 or 0)',
                                "emu.log('TARGET_VERDICT '..(bad and 'FAIL' or 'PASS')); emu.breakExecution()")
        lua.write_text(checks)
        result = run([sys.executable, __file__, '--embedded-worker', rom, lua, timeout_seconds],
                     cwd=OUT, timeout=max(30, timeout_seconds + 10))
        output = result.stdout
        assert 'TARGET_VERDICT PASS' in output and 'FAIL' not in output, output
        return output
    lua.write_text(checks)
    emulator = mesen_executable()
    result = run([emulator, '--testRunner', '--doNotSaveSettings', f'--timeout={timeout_seconds}', rom, lua], cwd=OUT,
                 timeout=max(30, timeout_seconds+10))
    failed = 'PASS' not in result.stdout or 'FAIL' in result.stdout
    save_log(log, result.stdout + result.stderr, failed=failed)
    if failed:
        raise AssertionError(result.stdout + result.stderr)
    return result.stdout


def near_fixture(source):
    """Keep near-loop optimizer fixtures in RAM under the bank-qualified ABI."""
    literals=[]
    def literal(match):
        value=json.loads(match[0]);name='near_literal_'+str(len(literals))
        literals.append('char '+name+'['+str(len(value)+1)+']={'+','.join(str(ord(c)) for c in value)+(',0' if value else '0')+'};')
        return name
    lines=[]
    for line in source.replace(' __far ',' ').splitlines():
        lines.append(line if line.lstrip().startswith('#') else re.sub(r'"(?:[^"\\]|\\.)*"',literal,line))
    return '\n'.join(literals+lines)+'\n'


def compile_case(name, source, console=False, extra_objects=(), console_object='console', flags=()):
    cfile = OUT / f'{name}.c'
    asm, obj, raw, rom = (OUT / f'{name}{suffix}' for suffix in ('.s', '.o', '.raw', '.sfc'))
    cfile.write_text(source)
    run([ROOT / 'build/zicc.exe', cfile, '-o', asm, *flags])
    run([CC65 / 'ca65.exe', '--cpu', '65816', '-g', '-o', obj, asm])
    supplied = {Path(o).name for o in extra_objects} | ({f'{console_object}.o'} if console else set())
    if '.importzp __arith_lhs' in asm.read_text() and not supplied & {'arithmetic.o', 'workspace.o', 'dp-scratch.o'}:
        workspace = OUT / 'workspace.s'
        workspace.write_text('.exportzp __arith_lhs,__arith_rhs\n.segment "DP_SCRATCH": zeropage\n'
                             '__arith_lhs: .res 4\n__arith_rhs: .res 28\n')
        run([CC65 / 'ca65.exe', '-o', OUT / 'workspace.o', workspace])
        extra_objects = [*extra_objects, OUT / 'workspace.o']
    # Resolve optional wide helpers for fixtures that explicitly provide the
    # legacy arithmetic objects. Archive members are selected only if needed
    if 'arithmetic.o' in supplied and 'libc.a' not in supplied:
        extra_objects = [*extra_objects, ROOT / 'build/libc.a']
    label_file = OUT / f'{name}.labels'
    run([CC65 / 'ld65.exe', '-C', ROOT / 'linker/lorom32.cfg', '-Ln', label_file,
         '-o', raw, ROOT / ('build/prompt_startup.o' if console else 'build/startup.o'),
         obj, *([ROOT / f'build/{console_object}.o'] if console else []), *extra_objects,
         ROOT / 'build/nmi.o', ROOT / 'build/vectors.o', ROOT / 'build/rom_header.o'])
    run([ROOT / 'build/romtool.exe', raw, rom, ROOT / 'tests/title.txt'])
    label_map = {name.removeprefix('_'): int(address, 16)
                 for address, name in re.findall(r'^al ([0-9A-Fa-f]+) \.(\S+)$', label_file.read_text(), re.M)}
    return cfile, rom, label_map


# Each entry names a check and its time limit in seconds. Use --list-parts to
# see the names or --part NAME to run one. Each job has its own output folder
# (ZICC_COMPILER_CHECK_OUT). The name 'cases' runs the checks defined in this file
PARTS = [
    ('debug-symbols', 120),
    ('math', 600),
    ('conversions', 600),
    ('main-entry', 120),
    ('typedef-char', 120),
    ('bitops', 180),
    ('indexed-operands', 120),
    ('index-retention', 120),
    ('gradient-codegen', 120),
    ('known-values', 180),
    ('range-values', 180),
    ('signed-minmax', 180),
    ('byte-shuffles', 180),
    ('store-fusion', 180),
    ('private-regions', 180),
    ('private-cleanups', 180),
    ('value-reuse', 180),
    ('value-placement', 180),
    ('source-lto', 600),
    ('arithmetic-regions', 600),
    ('integer-lowering', 300),
    ('int64-runtime', 300),
    ('int64-frontend', 120),
    ('int64-codegen', 300),
    ('int64-abi', 300),
    ('int64-aggregate', 300),
    ('int64-float', 600),
    ('wide-interrupt-live', 600),
    ('int64-strto', 300),
    ('int64-format', 300),
    ('legacy-float-abi', 300),
    ('ieee64-codegen', 300),
    ('ieee64-decimal', 300),
    ('ieee64-decimal-compare', 300),
    ('ieee64-decimal-estimate', 300),
    ('ieee64-decimal-refine', 300),
    ('ieee64-decimal-parse', 900),
    ('ieee64-hexparse', 300),
    ('ieee64-strtod', 300),
    ('ieee64-sqrt', 1200),
    ('ieee64-log', 1200),
    ('ieee64-exp', 1200),
    ('ieee64-atan', 1200),
    ('ieee64-trig', 1200),
    ('ieee64-format', 300),
    ('ieee64-runtime', 300),
    ('float-abi-mode', 300),
    ('structured-byte-loops', 300),
    ('reduction-products', 300),
    ('loop-access', 120),
    ('inlining', 300),
    ('body-codegen', 300),
    ('dpage-access', 300),
    ('runtime-ram', 600),
    ('loram', 300),
    ('application-wram', 600),
    ('preprocessor', 30),
    ('multi-errors', 30),
    ('embed', 30),
    ('banked-rom', 600),
    ('volatile', 120),
    ('scalar-values', 600),
    ('literal-copies', 600),
    ('libc', 120),
    ('libc-new', 600),
    ('printf-cursor', 120),
    ('assembly-match', 600),
    ('assembly-render', 900),
    ('assembly-rounded', 1200),
    ('decimal-assembly', 3600),
    ('far-loops', 120),
    ('far-loop-interrupts', 600),
    ('bank-pointers', 60),
    ('far-pointer-costs', 120),
    ('bank-calls', 120),
    ('bank-reductions', 120),
    ('constant-folding', 120),
    ('stack-frames', 120),
    ('enums', 60),
    ('legacy-functions', 60),
    ('switch', 60),
    ('multidimensional', 60),
    ('object-initializers', 180),
    ('callbacks', 180),
    ('priority4', 180),
    ('port-abi', 120),
    ('time', 300),
    ('interrupts', 600),
    ('interrupt-scratch', 120),
    ('dp-homes', 600),
    ('compare-constants', 600),
    ('index-elimination', 300),
    ('region-homes', 300),
    ('width-masks', 60),
    ('strength-algebra', 60),
    ('reuse-licm', 60),
    ('near7e-far', 60),
    ('control-stack-size', 60),
]


def run_part(name):
    timeout = dict(PARTS)[name]
    result = run([sys.executable, ROOT / f'tests/check-{name}.py'], timeout=timeout)
    sys.stdout.write(result.stdout)
    sys.stdout.write(result.stderr)


def main():
    if '--list-parts' in sys.argv:
        # Longest time limits first, so the slowest parts start early in the queue
        print(json.dumps([name for name, _ in sorted(PARTS, key=lambda part: -part[1])] + ['cases']))
        return
    selected = sys.argv[sys.argv.index('--part') + 1] if '--part' in sys.argv else None
    if selected is not None and selected != 'cases':
        if selected not in dict(PARTS):
            raise SystemExit(f'unknown part {selected}')
        run_part(selected)
        return
    OUT.mkdir(parents=True, exist_ok=True)
    if selected is None:
        for name, _ in PARTS:
            run_part(name)
    report = {}
    minimal = ROOT / 'build/minimal.sfc'
    debug = symbols(ROOT / 'build/minimal.sym')
    assert 'main' in debug and 'ram_cleared' in debug and 'reset_entry' in debug
    data = minimal.read_bytes()
    assert len(data) == 65536 and data[0xffd5] == 0x31
    assert data[debug['main']-0xc00000] == 0x80
    startup_labels = {name.removeprefix('_'): int(address, 16)
                      for address, name in re.findall(r'^al (\w+) \.(\S+)$',
                                                      minimal.with_suffix('.labels').read_text(), re.M)}
    report['minimal'] = emulate(minimal, debug | startup_labels, seed=True)
    cases = [
        ('false_loop', 'int main(void) { while (0) { while (1) {} } return 37; }', 37),
        ('return_in_loop', 'int main() { while (1) { return 5; } }', 5),
        ('nested_loops', 'int main(void) { while (1) { while (!1) {} return -17; } }', -17),
        ('fallthrough', '/* comment */ int main(void) { ; while (0) ; } // end\n', 0),
    ]
    for name, source, expected in cases:
        cfile, rom, label_map = compile_case(name, source)
        host = OUT / f'{name}.exe'
        run([ROOT / 'tools/msvc.cmd', '/nologo', '/std:c17', '/W4', '/O2', '/wd4127', '/wd4702',
             '/Fo' + str(OUT / f'{name}.obj'), '/Fe' + str(host), cfile])
        result = subprocess.run([str(host)], timeout=5, creationflags=subprocess.CREATE_NO_WINDOW)
        assert result.returncode & 0xffff == expected & 0xffff
        report[name] = emulate(rom, label_map, expected)
    invalid = ['int main(void) { while (1) {',
               'int main(void) { while (variable) {} }',
               'int main(void) { return -~32767; }',
               'int main(void) { break; }',
               'int main(void) { /* unterminated',
               'int main(void) { return 09; }']
    for i, source in enumerate(invalid):
        cfile = OUT / f'invalid_{i}.c'
        cfile.write_text(source)
        result = subprocess.run([str(ROOT / 'build/zicc.exe'), str(cfile), '-o', str(OUT / 'invalid.s')],
                                capture_output=True, text=True)
        assert result.returncode != 0 and re.search(r':\d+:\d+: error:', result.stderr), result.stderr
    report['negative_cases'] = len(invalid)
    (OUT / 'results.json').write_text(json.dumps(report, indent=2) + '\n')
    print('PASS: startup/seeded RAM clear; four MSVC+Mesen cases; six rejection cases')


if __name__ == '__main__':
    if sys.argv[1:2] == ['--embedded-worker']:
        print(emulate_embedded_worker(Path(sys.argv[2]), Path(sys.argv[3]), float(sys.argv[4])))
    else:
        main()
