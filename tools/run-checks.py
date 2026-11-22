"""Run the compiler tests. Use --suite to pick one group of tests.

The runner reuses saved emulator results when the inputs match. Use --no-cache
for a fresh emulator run. To skip groups whose inputs match their last passing
run, use --changed. The runner saves that record in logs/check/last-pass.json."""
import argparse
from concurrent.futures import ThreadPoolExecutor, wait, FIRST_COMPLETED
from contextlib import closing
from datetime import datetime, timezone
import hashlib
import json
import re
import os
from pathlib import Path
import subprocess
import sqlite3
import sys
import threading
import time

ROOT = Path(__file__).resolve().parents[1]
LOGS = Path('logs').resolve()
LOW_PRIORITY = getattr(subprocess, 'BELOW_NORMAL_PRIORITY_CLASS', 0x00004000)
_transcript_lock = threading.Lock()
# Keep the original make-check order and every original command-line assertion
SUITES = [
    ('rom', ['powershell', '-NoProfile', '-ExecutionPolicy', 'Bypass', '-File', 'tests/check-rom.ps1']),
    ('sram', []),
    ('compiler', []),
    ('structs', []),
    ('members', []),
    ('initializers', []),
    ('scalar-homes', []),
    ('shared-elements', []),
    ('struct-cursors', []),
    ('frames', ['--compiler', 'build/zicc.exe', '--output', str(LOGS / 'frame-check'),
                '--expect-guards', '--expect-forwarding', '--expect-reloads', '--expect-small-frames']),
    ('prompt', []),
    ('scalar-runtime', []),
    ('integer-hardware', []),
    ('small-integers', ['--expect-widths']),
    ('divmod', []),
    ('wide-codegen', []),
    ('widened-products', []),
    ('word-expressions', ['--expect-planner']),
    ('array-codegen', []),
    ('string-codegen', []),
    ('register-loops', []),
    ('indexed-byte-loops', []),
    ('byte-predicates', []),
    ('comparisons', []),
    ('strength', []),
    ('indexed-dpage', []),
    ('relax', []),
    ('decimal', []),
    ('codegen-optimizations', []),
]


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


STATE = LOGS / 'check/last-pass.json'
# Every suite uses the built tools, runtime, linker scripts, headers, samples,
# test tools, and the external assembler, linker and emulators
GLOBAL_TREES = ['runtime', 'linker', 'include', 'samples', 'tools']
GLOBAL_FILES = ['Makefile', 'build/zicc.exe', 'build/romtool.exe', 'tests/title.txt']
EXTERNAL_FILES = ['C:/bin/cc65/bin/ca65.exe', 'C:/bin/cc65/bin/ld65.exe',
                  'C:/bin/Mesen/Mesen.exe', 'D:/dev/dragon/tools/mesen/MesenCore.dll']


def global_fingerprint():
    digest = hashlib.sha256()
    paths = [ROOT / name for name in GLOBAL_FILES] + [Path(name) for name in EXTERNAL_FILES]
    for tree in GLOBAL_TREES:
        paths += sorted(p for p in (ROOT / tree).rglob('*') if p.is_file() and '__pycache__' not in p.parts)
    for path in paths:
        digest.update(str(path.relative_to(ROOT) if path.is_relative_to(ROOT) else path).encode())
        digest.update(sha256(path).encode() if path.exists() else b'missing')
    return digest.hexdigest()


def suite_inputs(script):
    # Test scripts a suite runs or imports, and the fixtures they reference
    seen, pending = set(), [script]
    while pending:
        path = pending.pop()
        if path in seen or not path.exists():
            continue
        seen.add(path)
        if path.suffix not in {'.py', '.ps1'}:
            continue
        text = path.read_text(errors='replace')
        names = set(re.findall(r"tests/([\w./-]+\.[\w-]+)", text))
        names |= {name + '.py' for name in re.findall(r'^\s*(?:import|from)\s+(\w+)', text, re.M)}
        names |= {f'check-{name}.py' for name in re.findall(r"^\s*\('([\w-]+)', \d+\),$", text, re.M)}  # PARTS
        pending += [ROOT / 'tests' / name for name in names if (ROOT / 'tests' / name).exists()]
    return sorted(seen)


def suite_fingerprint(name, command, shared):
    script = ROOT / ('tests/check-rom.ps1' if name == 'rom' else f'tests/check-{name}.py')
    digest = hashlib.sha256((shared + json.dumps(command)).encode())
    for path in suite_inputs(script):
        digest.update(str(path.relative_to(ROOT)).encode() + sha256(path).encode())
    return digest.hexdigest()


def load_state():
    try:
        return json.loads(STATE.read_text())
    except (OSError, ValueError):
        return {}


def msvc_environment():
    if os.environ.get('VSCMD_ARG_TGT_ARCH', '').lower() == 'x64':
        return os.environ.copy(), 0
    result = subprocess.run(
        [os.environ.get('COMSPEC', 'cmd.exe'), '/d', '/c',
         'call tools\\msvc-env.cmd >nul && set'], cwd=ROOT,
        capture_output=True, text=True, timeout=120,
        creationflags=subprocess.CREATE_NO_WINDOW)
    if result.returncode:
        raise RuntimeError('MSVC environment initialization failed:\n' + result.stdout + result.stderr)
    env = dict(line.split('=', 1) for line in result.stdout.splitlines()
               if '=' in line and not line.startswith('='))
    if env.get('VSCMD_ARG_TGT_ARCH', '').lower() != 'x64':
        raise RuntimeError('MSVC initialization did not select the x64 host environment')
    return env, 1


def run_suite(name, command, env, output, started, *, suite=None):
    begin = time.perf_counter()
    error = None
    try:
        result = subprocess.run(command, cwd=ROOT, env=env, stdout=subprocess.PIPE,
                                stderr=subprocess.STDOUT,
                                creationflags=subprocess.CREATE_NO_WINDOW | LOW_PRIORITY)
        code, child_output = result.returncode, result.stdout
    except OSError as exc:
        error = str(exc)
        code, child_output = 1, error.encode('utf-8')
    elapsed = time.perf_counter() - begin
    log = output / ((suite or name) + '.log')
    header = f'[{name}] exit={code}\n{subprocess.list2cmdline(command)}\n'.encode()
    with _transcript_lock, log.open('ab') as stream:
        offset = stream.tell()
        stream.write(header)
        stream.write(child_output)
        stream.write(b'\n\n')
    failure_log = None
    if code and suite and name != suite:
        failure_log = output / (name + '.failure.log')
        with failure_log.open('wb') as stream:
            stream.write(header)
            stream.write(child_output)
    return dict(name=name, command=command, exit_code=code, error=error,
                start_seconds=begin - started, seconds=elapsed,
                log_offset=offset, log_length=len(header) + len(child_output),
                failure_log=str(failure_log) if failure_log else None,
                log=str(log.relative_to(ROOT)) if log.is_relative_to(ROOT) else str(log))


STAGED_PARTS = {'time', 'interrupts', 'assembly-render', 'scalar-values', 'far-loop-interrupts', 'assembly-match', 'assembly-rounded', 'literal-copies'}


def plan_tasks(commands, env):
    tasks=[]
    def manifest(command, flag):
        result=subprocess.run(command+[flag],cwd=ROOT,env=env,capture_output=True,text=True,
                              check=True,timeout=30,creationflags=subprocess.CREATE_NO_WINDOW)
        return json.loads(result.stdout)
    for name,command in commands:
        if name in ('compiler','strength'):
            parts=manifest(command,'--list-parts')
            if not parts or len(set(parts))!=len(parts):raise RuntimeError('invalid part manifest')
            for part in parts:
                prefix=f'{name}-{part}'
                if name=='strength' and part in ('dp-counters','loop-unroll'):
                    base=[sys.executable,'tools/staged-check.py',part]
                    tasks.append(dict(name=prefix+'-setup',suite=name,part=part,command=base+['--setup'],expand=base,prefix=prefix))
                elif name=='compiler' and part=='banked-rom':
                    base=[sys.executable,'tests/check-banked-rom.py']
                    for child in manifest(base,'--list-parts'):
                        tasks.append(dict(name=prefix+'-'+child,suite=name,part=part,command=base+['--part',child]))
                elif name=='compiler' and (part in STAGED_PARTS or part=='decimal-assembly'):
                    base=([sys.executable,'tests/check-decimal-assembly.py'] if part=='decimal-assembly'
                          else [sys.executable,'tools/staged-check.py',part])
                    tasks.append(dict(name=prefix+'-setup',suite=name,part=part,
                                      command=base+['--setup'],expand=base,prefix=prefix))
                else:
                    tasks.append(dict(name=prefix,suite=name,part=part,command=command+['--part',part],
                        env={'ZICC_COMPILER_CHECK_OUT':str(LOGS/'compiler-check'/part)} if name=='compiler' else {}))
        elif name=='frames':
            parts=manifest(command,'--list-parts')
            children=[dict(name=name+'-'+part,suite=name,part=part,command=command+['--worker',part]) for part in parts]
            tasks+=children
            tasks.append(dict(name=name+'-collect',suite=name,command=command+['--collect'],
                              requires=[t['name'] for t in children],stage='collect'))
        elif name=='small-integers':
            batches=manifest(command,'--list-batches')
            if not batches:raise RuntimeError('empty arithmetic manifest')
            children=[dict(name=f"{name}-{item['kind']}-{item['batch']:02d}",suite=name,
                           command=command+['--worker',item['kind'],'--batch',str(item['batch'])],batch=item)
                      for item in batches]
            if len({t['name'] for t in children})!=len(children):raise RuntimeError('duplicate batches')
            tasks+=children
            tasks.append(dict(name=name+'-collect',suite=name,command=command+['--collect'],
                              requires=[t['name'] for t in children],stage='collect'))
        else:tasks.append(dict(name=name,suite=name,command=command))
    return tasks, {}


def expand_tasks(task, env):
    base=task['expand']
    result=subprocess.run(base+['--list-workers'],cwd=ROOT,env=env,capture_output=True,text=True,
                          check=True,timeout=30,creationflags=subprocess.CREATE_NO_WINDOW)
    workers=json.loads(result.stdout)
    if not workers:raise RuntimeError('empty worker manifest')
    children=[]
    for index,item in enumerate(workers):
        if 'mode' in item and 'name' in item:
            arguments=['--mode',item['mode'],'--region',item['region'],'--function',item['name'],'--batch',str(item['batch'])]
            suffix='-'.join(map(str,item.values()))
        else:arguments=['--worker',str(item['index'])];suffix=str(index)
        children.append(dict(name=task['prefix']+'-'+suffix,suite=task['suite'],part=task['part'],
                             command=base+arguments,requires=[task['name']],stage='worker'))
    children.append(dict(name=task['prefix']+'-collect',suite=task['suite'],part=task['part'],
                         command=base+['--collect'],requires=[t['name'] for t in children],stage='collect'))
    return children


def previous_durations():
    # Most recent completed run containing each job, including partial selections
    durations={}
    history = (LOGS / 'check').glob('*/summary.json')
    for path in sorted(history,key=lambda p:p.stat().st_mtime,reverse=True):
        try:rows=json.loads(path.read_text())['tasks']
        except (OSError,ValueError,KeyError):continue
        for row in rows:
            if row.get('exit_code')==0:durations.setdefault(row['name'],row['seconds'])
    return durations


def schedule(tasks, jobs, execute, env, completed):
    """One bounded pool; newly released dependencies precede existing ready work."""
    durations=previous_durations()
    priority=lambda t:(t['name'] in durations,-durations.get(t['name'],0))
    pending=list(tasks);ready=[];results={};active={}
    def release():
        nonlocal pending,ready
        released=[];remaining=[]
        for task in pending:
            deps=task.get('requires',[])
            if not all(dep in results for dep in deps):remaining.append(task);continue
            failed=[dep for dep in deps if results[dep]['exit_code']]
            if failed:
                row=dict(name=task['name'],command=task['command'],exit_code=1,
                         error='prerequisite failed: '+', '.join(failed),start_seconds=0,seconds=0,log=None)
                results[task['name']]=row;completed(task,row)
            else:released.append(task)
        pending=remaining
        ready=sorted(released,key=priority)+ready
    with ThreadPoolExecutor(max_workers=jobs) as pool:
        while pending or ready or active:
            release()
            while ready and len(active)<jobs:
                task=ready.pop(0);active[pool.submit(execute,task)]=task
            if not active:
                if pending:
                    if any(all(d in results for d in t.get('requires',[])) for t in pending):continue
                    raise RuntimeError('cyclic or missing prerequisites')
                break
            finished,_=wait(active,return_when=FIRST_COMPLETED)
            for future in finished:
                task=active.pop(future);row=future.result()
                if row['exit_code']==0 and 'expand' in task:
                    try:
                        children=expand_tasks(task,env)
                        if len({t['name'] for t in tasks+children})!=len(tasks)+len(children):
                            raise RuntimeError('duplicate task name')
                        tasks.extend(children);pending.extend(children)
                    except Exception as exc:
                        row.update(exit_code=1,error='planning workers: '+str(exc))
                results[task['name']]=row;completed(task,row)
    return results


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--jobs', type=int, default=max(4, (os.cpu_count() or 1) - 2),
                        help='maximum number of jobs that can run at once')
    parser.add_argument('--suite', action='append', choices=[name for name, _ in SUITES],
                        help='run this group of tests (repeat to select more groups). Build its inputs with Make first')
    parser.add_argument('--output', type=Path, help='new directory for logs and summary')
    parser.add_argument('--no-cache', action='store_true',
                        help='emulate every ROM instead of reusing cached results of identical runs')
    parser.add_argument('--cache-trace', action='store_true',
                        help='retain individual cache events in cache-events.sqlite3')
    parser.add_argument('--changed', action='store_true',
                        help='run only suites whose inputs changed since they last passed')
    args = parser.parse_args()
    if args.jobs < 1:
        parser.error('--jobs must be at least 1')
    output = (args.output or LOGS / 'check' /
              datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%S.%fZ')).resolve()
    # Refuse reuse so a failed run cannot be confused with earlier evidence
    output.mkdir(parents=True, exist_ok=False)
    started = time.perf_counter()
    env, setups = msvc_environment()
    env['ZICC_LOGS_DIR'] = str(LOGS)
    setup_seconds = time.perf_counter() - started
    env['ZICC_VERIFICATION_RUN_ID']=output.name+'-'+str(time.time_ns())
    env['ZICC_RUN_CACHE'] = '0' if args.no_cache else '1'
    commands = [(name, extra if name == 'rom' else
                 [sys.executable, 'tests/check-' + name + '.py', *extra])
                for name, extra in SUITES if not args.suite or name in args.suite]
    shared = global_fingerprint()
    fingerprints = {name: suite_fingerprint(name, command, shared) for name, command in commands}
    state = load_state()
    if args.changed:
        skipped = [name for name, _ in commands if state.get(name) == fingerprints[name]]
        commands = [(name, command) for name, command in commands if name not in skipped]
        print(f'Unchanged since their last pass, not run: {", ".join(skipped) or "none"}', flush=True)
    tasks, collectors = plan_tasks(commands, env) if commands else ([], {})
    print(f'Running {len(commands)} suites / {len(tasks)} jobs with '
          f'{min(args.jobs, max(len(tasks), 1))} workers; emulator cache '
          f'{"off" if args.no_cache else "on"}; logs: {output}', flush=True)
    cache_db = output / 'cache-events.sqlite3'

    def task_env(task):
        merged = dict(env, **task.get('env', {}))
        merged['ZICC_CACHE_EVENT_DB'] = str(cache_db)
        merged['ZICC_CACHE_EVENT_JOB'] = task['name']
        merged['ZICC_CACHE_TRACE'] = '1' if args.cache_trace else '0'
        return merged

    planning_seconds=time.perf_counter()-started-setup_seconds
    def completed(task,result):
        result['suite']=task['suite']
        for key in ('batch','part','stage','requires'):
            if key in task:result[key]=task[key]
        print(f"{'PASS' if result['exit_code']==0 else 'FAIL'} {task['name']}: {result['seconds']:.2f}s",flush=True)
    def execute(task):
        return run_suite(task['name'], task['command'], task_env(task), output, started,
                         suite=task['suite'])

    results = {}
    if tasks:
        with closing(sqlite3.connect(cache_db)) as connection:
            connection.execute('PRAGMA journal_mode=WAL')
            connection.execute('CREATE TABLE counts(job TEXT, kind TEXT, count INTEGER, PRIMARY KEY(job, kind))')
            if args.cache_trace:
                connection.execute('CREATE TABLE events(job TEXT, kind TEXT, digest TEXT, label TEXT)')
            results = schedule(tasks, args.jobs, execute, env, completed)
            for result in results.values():
                result['cache'] = {}
            for job, kind, count in connection.execute('SELECT job, kind, count FROM counts'):
                results[job]['cache'][kind] = count
    ordered=[]
    for name,command in commands:
        children=[results[t['name']] for t in tasks if t['suite']==name]
        if len(children)==1 and children[0]['name']==name:
            ordered.append(children[0]);continue
        failures=[c['name'] for c in children if c['exit_code']]
        log=next((c['log'] for c in children if c['log']), None)
        begin=min(c['start_seconds'] for c in children)
        end=max(c['start_seconds']+c['seconds'] for c in children)
        ordered.append(dict(name=name,command=command,exit_code=int(bool(failures)),
            error='child failures' if failures else None,log=log,start_seconds=begin,seconds=end-begin,
            task_seconds=sum(c['seconds'] for c in children),
            part_count=len({c['part'] for c in children if 'part' in c}),
            batch_count=sum('batch' in c for c in children)))
    for row in ordered:
        script = 'tests/check-' + row['name'] + ('.ps1' if row['name'] == 'rom' else '.py')
        row['script_sha256'] = sha256(ROOT / script)
    for row in ordered:
        row['fingerprint'] = fingerprints[row['name']]
        if row['exit_code'] == 0:
            state[row['name']] = fingerprints[row['name']]
        else:
            state.pop(row['name'], None)
    STATE.parent.mkdir(parents=True, exist_ok=True)
    STATE.write_text(json.dumps(state, indent=2, sort_keys=True) + '\n')
    totals = {kind: sum(task.get('cache', {}).get(kind, 0) for task in results.values())
              for kind in ('hit', 'miss', 'bypass', 'host-hit', 'host-miss')}
    print(f"Emulator runs: {totals['hit']} cached, {totals['miss']} emulated, "
          f"{totals['bypass']} uncacheable", flush=True)
    wall=time.perf_counter()-started
    busy=sum(r['seconds'] for r in results.values())
    last=max(results.values(),key=lambda r:r['start_seconds']+r['seconds'],default=None)
    chain=[]
    cursor=last
    while cursor:
        chain.append(cursor['name'])
        parents=[results[n] for n in cursor.get('requires',[]) if n in results]
        cursor=max(parents,key=lambda r:r['start_seconds']+r['seconds'],default=None)
    summary = dict(critical_path=dict(last_job=last['name'] if last else None,chain=list(reversed(chain)),
                       achieved_thread_seconds=busy,available_thread_seconds=wall*args.jobs,
                       idle_worker_seconds=max(0,wall*args.jobs-busy),utilization=busy/(wall*args.jobs)),
                   planning_seconds=planning_seconds,
                   prerequisite_seconds=float(env.get('ZICC_PREREQUISITE_SECONDS',0)),jobs=args.jobs, seconds=time.perf_counter() - started, cache=not args.no_cache,
                   emulator_runs=totals, changed_only=args.changed,
                   msvc_initializations=setups, msvc_setup_seconds=setup_seconds,
                   compiler_sha256=sha256(ROOT / 'build/zicc.exe'), suites=ordered,
                   tasks=[results[task['name']] for task in tasks])
    (output / 'summary.json').write_text(json.dumps(summary, indent=2) + '\n', encoding='utf-8')
    if tasks and not args.cache_trace:
        cache_db.unlink()
    failed = sum(row['exit_code'] != 0 for row in ordered)
    print(f"{len(ordered) - failed}/{len(ordered)} suites passed in {summary['seconds']:.2f}s", flush=True)
    return int(failed != 0)


if __name__ == '__main__':
    sys.exit(main())
