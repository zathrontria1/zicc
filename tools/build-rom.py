"""Build a raw SNES HiROM or ExHiROM image from C source files.

The builder compiles each C file separately by default. It places code first
and keeps assembly routines together when they use short jumps between them.
It starts with 64 KiB, doubles the space when needed, and saves each layout
it tries. A standard HiROM holds up to 4 MiB.
"""
import argparse
import base64
from dataclasses import dataclass
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile
from run_cache import file_sha256
from runtime_ram import RUNTIME_RAM, backfill
import application_wram as wram
import cartridge_sram
import interrupt_addressing
import accumulator_width

ROOT = Path(__file__).resolve().parents[1]
EXE = '.exe' if os.name == 'nt' else ''
CC65 = Path(os.environ.get('CC65_BIN') or ('C:/bin/cc65/bin' if os.name == 'nt' else
                                           Path(shutil.which('ca65') or '/usr/bin/ca65').parent))
RAM = {'BSS', 'ZEROPAGE', 'DP_SCRATCH', 'LORAM_BSS'} | set(RUNTIME_RAM)
INITIALIZED = {'DATA', 'LORAM_DATA'}
FIXED = {'VECTOR_STUBS', 'HEADER', 'VECTORS'}
DEFAULTS = {'__console_init', '__format_float_hook', '__format_int64_hook', '__vector_nmi', '__vector_irq', '__vector_brk', '__vector_cop'}
LINK_SYMBOLS = DEFAULTS | {'__DATA_LOAD__', '__DATA_RUN__', '__DATA_SIZE__', '__NEAR_LAST__', '__initialize_extra_ram',
                           '__zicc_reset_offset__',
                           '__NEAR_START__', '__NEAR_SIZE__', '__STACK_BOTTOM__', '__STACK_TOP__', '__STACK_SIZE__', '__ARITH_BASE__', '__dp_scratch',
                           '__DP_START__', '__DP_SIZE__', '__SCRATCH_START__', '__SCRATCH_SIZE__',
                           '__LORAM_BSS_RUN__', '__LORAM_BSS_SIZE__', '__LORAM_DATA_LOAD__',
                           '__LORAM_DATA_RUN__', '__LORAM_DATA_SIZE__',
                           '__RUNTIME_RAM_BOTTOM__', '__RUNTIME_RAM_TOP__'}
LINK_SYMBOLS |= {f'__{name}_{suffix}__' for name in ('ZEROPAGE', 'DP_SCRATCH', 'BSS')
                 for suffix in ('RUN', 'SIZE')}
LINK_SYMBOLS |= cartridge_sram.LINK_SYMBOLS
FAR_LIBRARY = {
    'far-memory.c': ('_far_memcpy', '_far_memmove', '_far_memset'),
    'far-heap.s': ('_far_heap_init', '_far_malloc', '_far_calloc', '_far_realloc', '_far_free'),
}


class BuildTranscript:
    def __init__(self, evidence):
        self.evidence = evidence
        self.compile_cache_hits = []
        self.keep_assembly = set()

    def write(self, text):
        with (self.evidence / 'build.log').open('a', encoding='utf-8') as stream:
            stream.write(text.rstrip('\n') + '\n\n')

    def compile_hit(self, asm, entry):
        self.compile_cache_hits.append(asm.relative_to(self.evidence).as_posix())
        self.write(f'Compile cache hit: {asm} <- {entry}')

    def prune_intermediates(self):
        for path in self.evidence.rglob('*'):
            if path.suffix == '.o' or (path.suffix == '.s' and path not in self.keep_assembly):
                path.unlink()


def run(command, log=None):
    p = subprocess.run(list(map(str, command)), cwd=ROOT, capture_output=True, text=True,
                       creationflags=getattr(subprocess, 'CREATE_NO_WINDOW', 0))
    diagnostic = subprocess.list2cmdline(list(map(str, command))) + '\n' + p.stdout + p.stderr
    if log is not None:
        log.write(diagnostic)
    if p.returncode:
        if log is not None:
            log.keep_assembly.update(Path(arg) for arg in command
                                     if Path(arg).suffix == '.s' and Path(arg).is_relative_to(log.evidence))
        raise RuntimeError(diagnostic)
    return p.stdout


def save(path, text):
    path.write_bytes(text.replace('\r\n', '\n').replace('\n', '\r\n').encode())


def dependency_hash(path):
    try:
        return file_sha256(path)
    except (FileNotFoundError, NotADirectoryError, PermissionError):
        return None


def compiler_executable():
    override = os.environ.get('ZICC_COMPILER')
    if override:
        return Path(override).resolve()
    local = ROOT / f'build/zicc{EXE}'
    return local if local.is_file() else ROOT / f'bin/zicc{EXE}'


def compile_unit(source, asm, flags, cache_dir, stage, show, log, *, track_dependencies=False):
    log.keep_assembly.add(asm)
    compiler = compiler_executable()
    command = [compiler, source, '-o', asm, '-I', ROOT / 'include', *flags]
    entry = None
    dependencies = {}
    if track_dependencies:
        primary = [compiler, source, *(flags[i + 1] for i, flag in enumerate(flags) if flag == '--lto-source')]
        dependencies.update((str(path), file_sha256(path)) for path in primary)
    if cache_dir is not None or track_dependencies:
        dependency_file = asm.with_suffix('.deps')
        command.extend(['--dependencies', dependency_file])
    if cache_dir is not None:
        key = [str(compiler), file_sha256(compiler), str(source), file_sha256(source), flags]
        digest = hashlib.sha256(json.dumps(key).encode()).hexdigest()
        entry = cache_dir / digest[:2] / (digest + '.json')
        try:
            cached = json.loads(entry.read_text(encoding='utf-8'))
        except (FileNotFoundError, ValueError):
            cached = None
        if cached is not None and all(dependency_hash(path) == digest
                                      for path, digest in cached['dependencies'].items()):
            log.compile_hit(asm, entry)
            return cached['assembly'], cached['dependencies'] | dependencies

    if show:
        display_path = source.relative_to(Path.cwd()) if source.is_relative_to(Path.cwd()) else source
        print(f'zicc [stage {stage}] {display_path.as_posix()}', flush=True)
    run(command, log)
    text = asm.read_text()
    if cache_dir is not None or track_dependencies:
        for line in dependency_file.read_text().splitlines():
            path = str(ROOT / line[2:])
            dependencies[path] = dependency_hash(path)
            if (dependencies[path] is not None) != (line[0] == '+'):
                raise RuntimeError(f'{path}: dependency changed during compilation')
    if entry is not None:
        entry.parent.mkdir(parents=True, exist_ok=True)
        with tempfile.TemporaryDirectory(dir=entry.parent) as directory:
            temporary = Path(directory) / entry.name
            with temporary.open('w', encoding='utf-8') as stream:
                json.dump(dict(assembly=text, dependencies=dependencies), stream)
            try:
                os.replace(temporary, entry)
            except PermissionError:
                # A concurrent Windows reader can hold the existing entry open
                if not entry.is_file():
                    raise
    return text, dependencies


@dataclass
class Unit:
    name: str
    size: int
    alignment: int
    kind: str
    owner: str


class PackingError(Exception):
    pass


ROM_BANK = 0x10000
EXHIROM_BANKS = (96, 128)


@dataclass(frozen=True)
class RomLayout:
    """Bank indices follow ROM file order, including the two half-bank holes."""
    banks: int

    @property
    def extended(self):
        return self.banks in EXHIROM_BANKS

    @property
    def header_bank(self):
        return 64 if self.extended else 0

    @property
    def mapping(self):
        return 'exhirom' if self.extended else 'hirom'

    def address(self, bank, offset):
        if bank < 64:
            return 0xC00000 + bank * ROM_BANK + offset
        if bank < 126:
            return bank * ROM_BANK + offset
        # The final upper halves are available only through $3E and $3F
        return (bank - 64) * ROM_BANK + offset

    def bounds(self, bank):
        return (0x8000 if bank >= 126 else 0,
                0xFFA0 if bank == self.header_bank else ROM_BANK)

    def file_offset(self, bank, offset):
        return bank * ROM_BANK + offset


def bank_crossing_data(unit):
    return unit.kind in {'asset', 'constant'}


def pack(units, banks, stage, batches=(), *, large_data_first=False):
    """Pack ROM units around reserved and unmapped bytes."""
    layout = RomLayout(banks)
    free = [[layout.bounds(b)] for b in range(banks)]
    result = {}

    def reserve(bank, start, size):
        while size:
            lo, hi = next(span for span in free[bank] if span[0] <= start < span[1])
            end = min(start + size, hi)
            free[bank].remove((lo, hi))
            free[bank].extend((a, z) for a, z in [(lo, start), (end, hi)] if a < z)
            free[bank].sort()
            size -= end - start
            # Only a verified contiguous extent can continue into another bank
            bank += 1
            start = 0

    def contiguous_extents(eligible):
        extent = None
        for bank in eligible:
            for lo, hi in free[bank]:
                address = layout.address(bank, lo)
                offset = layout.file_offset(bank, lo)
                if extent and extent[0] + extent[2] == address and extent[1] + extent[2] == offset:
                    extent = (*extent[:2], extent[2] + hi - lo)
                else:
                    if extent:
                        yield extent
                    extent = (address, offset, hi - lo)
        if extent:
            yield extent

    def place(unit, eligible, residue=0):
        candidates = []
        for b in eligible:
            for lo, hi in free[b]:
                start = lo + ((residue - lo) & (unit.alignment - 1))
                if start + unit.size <= hi:
                    priority = int(b >= 64) + int(b >= 126) if unit.kind == 'code' else 0
                    candidates.append((priority, hi - lo - unit.size, b, start))
        if not candidates and bank_crossing_data(unit):
            for address, offset, size in contiguous_extents(eligible):
                padding = (residue - address) & (unit.alignment - 1)
                if padding + unit.size <= size:
                    bank, start = divmod(offset + padding, ROM_BANK)
                    candidates.append((0, size - unit.size, bank, start))
        if not candidates:
            extent = 'contiguous ROM extents' if bank_crossing_data(unit) else 'permitted bank extents'
            raise PackingError(f'{unit.name}: {unit.size} bytes cannot fit {extent}')
        _, _, b, start = min(candidates)
        reserve(b, start, unit.size)
        result[unit.name] = (b, start)

    if large_data_first:
        for u in sorted(units, key=lambda u: (-u.size, u.name)):
            if u.size > ROM_BANK and bank_crossing_data(u):
                place(u, range(banks))

    code = [u for u in units if u.kind == 'code']
    if stage < 4:
        groups = [('all', code, 0 if stage == 1 else 1)] if stage < 3 else [
            ('application', [u for u in code if u.owner == 'application'], 1),
            ('runtime', [u for u in code if u.owner != 'application'], 2)]
        for name, group, bank in groups:
            if bank >= banks:
                raise PackingError(f'stage {stage} needs bank {bank + 1}')
            # Group members share one bank; source identity gives a stable order
            for u in group:
                place(u, [bank])
    else:
        for u in sorted(code, key=lambda u: (-u.size, u.name)):
            place(u, range(banks))
    # Place each batch as one bank-local extent, then expose the original units
    # to the linker. Matching the WRAM residue preserves every member alignment
    members = {}
    residues = {}
    batch_units = []
    by_name = {u.name: u for u in units}
    for batch in batches:
        first = batch[0]
        name = 'BATCH_' + first.name
        alignment = max(by_name[span.name].alignment for span in batch)
        members[name] = batch
        residues[name] = first.address % alignment
        size = batch[-1].address + batch[-1].size - first.address
        batch_units.append(Unit(name, size, alignment, "data", "runtime"))
    grouped = {span.name for batch in batches for span in batch}
    data = [u for u in units if u.kind != 'code' and u.name not in grouped and u.name not in result]
    data.extend(batch_units)
    for u in sorted(data, key=lambda u: (-u.size, u.name)):
        place(u, range(banks), residues.get(u.name, 0))
        if u.name in members:
            bank, offset = result.pop(u.name)
            for span in members[u.name]:
                result[span.name] = bank, offset + span.address - members[u.name][0].address
    return result, free


def config(units, placements, banks, nmi_parts, runtime_ram=None, near_objects=(), promoted=(), *,
           stack_size=1024, batches=(), expanded=None, sram=None, sram_objects=()):
    layout = RomLayout(banks)
    symbols = [' __console_init: type=weak, value=0;',
               ' __format_float_hook: type=weak, value=0;',
               ' __format_int64_hook: type=weak, value=0;',
               ' __STACK_BOTTOM__: type=export, value=$0100;',
               f' __STACK_SIZE__: type=weak, value=${stack_size:04X};',
               ' __STACK_TOP__: type=export, value=__STACK_BOTTOM__ + __STACK_SIZE__ - 1;',
               ' __ARITH_BASE__: type=export, value=__SCRATCH_START__;',
               ' __dp_scratch: type=weak, value=__SCRATCH_START__, addrsize=zp;',
               ' __zicc_reset_offset__: type=weak, value=0, addrsize=far;']
    symbols += [f' __vector_{n}: type=weak, value=unused_interrupt;' for n in ['nmi','irq','brk','cop']]
    if sram is not None:
        symbols.extend(sram.linker_symbols())
    memory = [' DP: start=$000022, size=$DE, type=rw, file="", define=yes;',
              ' SCRATCH: start=$000002, size=$20, type=rw, file="", define=yes;',
              ' NEAR: start=$7E0100 + __STACK_SIZE__, size=$FF00 - __STACK_SIZE__, type=rw, file="", define=yes;']
    segments = [' ZEROPAGE: load=DP, type=zp, optional=yes, define=yes, align=2;',
                ' DP_SCRATCH: load=SCRATCH, type=zp, optional=yes, define=yes;',
                ' LORAM_BSS: load=NEAR, type=bss, optional=yes, define=yes, align=2;']
    near_segments = {name: f' {name}: load=NEAR, type=bss, define=yes, align={alignment};'
                     for name, alignment in near_objects if name.startswith('NEAR_BSS_')}
    segments.append(' BSS: load=NEAR, type=bss, optional=yes, define=yes, align=2;')
    runtime_ram = runtime_ram or backfill([])
    symbols += [f' __RUNTIME_RAM_BOTTOM__: type=export, value=${runtime_ram["lower"]:06X};',
                ' __RUNTIME_RAM_TOP__: type=export, value=$800000;']
    for record in runtime_ram['objects']:
        name=record['name']
        memory.append(f' RAM7F_{name}: start=${record["address"]:06X}, size=${record["size"]:X}, type=rw, file="";')
        segments.append(f' {name}: load=RAM7F_{name}, type=bss, define=yes, align={record["alignment"]};')
    expanded_parts = {p['name']: p for p in wram.parts(expanded)}
    memory.extend(wram.run_regions(expanded))
    segments.extend(wram.segment(p) for p in expanded_parts.values() if p['clear'])

    # Emit each allocator-owned alignment byte as an explicit ROM zero
    padded = {placements[right.name] for batch in batches for left, right in zip(batch, batch[1:])
              if left.address + left.size < right.address}

    def region(name, address, size, fill=0xff):
        memory.append(f' {name}: start=${address:06X}, size=${size:X}, type=ro, file=%O, fill=yes, fillval=${fill:02X};')

    rom = []
    for u in sorted(units, key=lambda u: placements[u.name]):
        b, off = placements[u.name]
        address = layout.address(b, off)
        file_offset = layout.file_offset(b, off)
        load = 'LOAD_' + u.name
        if (b, off) in padded:
            rom.append((file_offset - 1, f'INIT_PAD_{b}_{off-1}', address - 1, 1, 0))
        rom.append((file_offset, load, address, u.size, 0xff))
        if u.name.startswith('NEAR_DATA_'):
            near_segments[u.name] = f' {u.name}: load={load}, run=NEAR, type=rw, define=yes, align={u.alignment};'
        elif u.name in expanded_parts:
            segments.append(wram.segment(expanded_parts[u.name], load))
        elif u.name in INITIALIZED:
            segment = f' {u.name}: load={load}, run=NEAR, type=rw, define=yes, align=2;'
            if u.name == 'LORAM_DATA': segments.insert(3, segment)
            else: segments.append(segment)
        elif u.name == 'INTERRUPT':
            for name, _, alignment in nmi_parts:
                segments.append(f' {name}: load={load}, type=ro, align={alignment};')
        else:
            segments.append(f' {u.name}: load={load}, type=ro;')
    # Bank zero reads the ExHiROM header bank, or the first HiROM bank
    alias = 0 if layout.extended else 0x800000
    for name, off in [('VECTOR_STUBS', 0xFFA0), ('HEADER', 0xFFC0), ('VECTORS', 0xFFE0)]:
        rom.append((layout.file_offset(layout.header_bank, off), 'LOAD_' + name, alias + off, 32, 0xff))
        segments.append(f' {name}: load=LOAD_{name}, type=ro;')
    # ld65 emits memory areas in declaration order. Gaps have no load address
    cursor = 0
    for offset, name, address, size, fill in sorted(rom):
        if offset < cursor:
            raise RuntimeError(f'overlapping ROM placement at {name}')
        if offset > cursor:
            region(f'GAP_{cursor}', 0, offset - cursor)
        region(name, address, size, fill)
        cursor = offset + size
    if cursor < banks * ROM_BANK:
        region(f'GAP_{cursor}', 0, banks * ROM_BANK - cursor)
    for name in sorted(INITIALIZED):
        if not any(u.name == name for u in units):
            memory.append(f' EMPTY_{name}: start=$C08000, size=0, type=ro, file="";')
            segment = f' {name}: load=EMPTY_{name}, run=NEAR, type=rw, define=yes, optional=yes, align=2;'
            if name == 'LORAM_DATA': segments.insert(3, segment)
            else: segments.append(segment)
    # Pinned LoRAM is followed by complete interrupt groups. Spilled candidates
    # use ordinary WRAM without consuming the interrupt allocation budget
    segments[4:4] = [near_segments[name] for name in promoted]
    segments.extend(near_segments[name] for name, _ in near_objects if name not in promoted)
    tail = wram.near_tail(expanded)
    if tail:
        segments.append(tail)
    if sram is not None:
        sram_memory, sram_segments = sram.linker_regions(sram_objects)
        memory.extend(sram_memory)
        segments.extend(sram_segments)
    return 'SYMBOLS {\n'+'\n'.join(symbols)+'\n}\nMEMORY {\n'+'\n'.join(memory)+'\n}\nSEGMENTS {\n'+'\n'.join(segments)+'\n}\n'


def inspect(obj, log):
    dump = run([CC65 / f'od65{EXE}', '--dump-segments', '--dump-imports', '--dump-exports', obj], log)
    segment_text, rest = dump.split('  Imports:', 1)
    imports, exports = rest.split('  Exports:', 1)
    segs = [(n, int(z), int(a)) for n, z, a in re.findall(r'Name:\s*"([^"]+)"\s+Flags:\s+\d+\s+Size:\s+(\d+)\s+Alignment:\s+(\d+)', segment_text)]
    return segs, set(re.findall(r'Name:\s*"([^"]+)"', imports)), set(re.findall(r'Name:\s*"([^"]+)"', exports))


def assemble_object(source, asm, obj, text, flags, cacheable, log):
    assembler = CC65 / f'ca65{EXE}'
    options = ['--cpu', '65816', '-g', '-I', ROOT, '-I', source.parent, *flags]
    entry = None
    cache_directory = os.environ.get('ZICC_RUNTIME_OBJECT_CACHE_DIR')
    # Units with external assembler inputs still use normal dependency resolution
    if (cacheable and (cache_directory or (ROOT / 'build').is_dir())
            and os.environ.get('ZICC_RUNTIME_OBJECT_CACHE', '1') != '0'
            and not re.search(r'\.(?:include|incbin)\b', text, re.I)):
        key = [1, text, str(assembler.resolve()), file_sha256(assembler),
               file_sha256(CC65 / f'od65{EXE}'), list(map(str, options))]
        digest = hashlib.sha256(json.dumps(key).encode()).hexdigest()
        directory = Path(cache_directory or ROOT / 'build/runtime-object-cache')
        entry = directory / digest[:2] / (digest + '.json')
        try:
            cached = json.loads(entry.read_text(encoding='utf-8'))
        except (OSError, ValueError):
            cached = None
        # The linked debug file is redirected to this build's assembly
        if cached:
            log.write(f'Runtime object cache hit: {obj} <- {cached["assembly"]}')
            return ([tuple(segment) for segment in cached['segments']], set(cached['imports']),
                    set(cached['exports']), cached)

    save(asm, text)
    run([assembler, *options, '-o', obj, asm], log)
    segments, imports, exports = inspect(obj, log)
    if entry is not None:
        cached = dict(assembly=str(asm), object=base64.b64encode(obj.read_bytes()).decode('ascii'),
                      segments=segments, imports=sorted(imports), exports=sorted(exports))
        entry.parent.mkdir(parents=True, exist_ok=True)
        handle, temporary = tempfile.mkstemp(dir=entry.parent, suffix='.tmp')
        try:
            with os.fdopen(handle, 'w', encoding='utf-8') as stream:
                json.dump(cached, stream)
            try:
                os.replace(temporary, entry)
            except PermissionError:
                # A concurrent Windows reader can hold the existing entry open
                if not entry.is_file():
                    raise
        finally:
            Path(temporary).unlink(missing_ok=True)
    return segments, imports, exports, None


def materialize_object(unit):
    cached = unit.pop('cached', None)
    if cached is None:
        return
    obj = unit['path']
    obj.write_bytes(base64.b64decode(cached['object']))
    save(obj.with_suffix('.s'), unit.pop('assembly'))
    unit['debug_source'] = cached['assembly']


def relocate_debug_sources(debug, objects):
    sources = {}
    encoding = 'mbcs' if os.name == 'nt' else 'utf-8'
    for unit in objects:
        assembly = unit['path'].with_suffix('.s')
        cached_source = unit.get('debug_source')
        if cached_source is not None and cached_source != str(assembly):
            sources.setdefault(cached_source.encode(encoding), assembly)
    if not sources:
        return

    # Keep debugger line records attached to this build even after cache cleanup
    def relocate(match):
        assembly = sources.get(match['name'])
        if assembly is None:
            return match[0]
        stat = assembly.stat()
        record = f'{assembly}",size={stat.st_size},mtime=0x{int(stat.st_mtime):08X}'
        return match['prefix'] + record.encode(encoding)

    pattern = rb'^(?P<prefix>file\t[^\r\n]*?\bname=")(?P<name>[^"\r\n]+)",size=\d+,mtime=0x[\da-fA-F]+'
    debug.write_bytes(re.sub(pattern, relocate, debug.read_bytes(), flags=re.M))


def segment_sizes(objects):
    sizes = {}; aligns = {}
    for obj in objects:
        for name, size, alignment in obj['segments']:
            if not size and name not in INITIALIZED:
                continue
            sizes[name] = ((sizes.get(name, 0) + alignment - 1) & -alignment) + size
            aligns[name] = max(aligns.get(name, 1), alignment)
    return sizes, aligns


def runtime_long(text, source):
    if source.stem == 'far-heap':
        return 'FAR_HEAP_LONG_CALLS=1\n' + text
    if source.parent.name == 'math':
        text = 'MATH_RETURN_EXTRA=1\n' + text
    if source.parent.name in {'strings', 'bitops'} or source.stem in {
        'sprintf', 'qsort', 'bsearch', 'strtoint', 'strto64', 'strcmp',
        'abs', 'labs', 'fabs', 'fabsf', 'ldexp', 'ldexpf', 'sram',
    }:
        text = 'LIBC_RETURN_EXTRA=1\n' + text
    # Only caller-owned argument offsets change. Local stack saves and the
    # executable memcpy thunk retain their exact offsets
    thresholds = {'strcpy': 11, 'memcpy-near': 8, 'memmove': 3, 'memset': 9, 'io': 9, 'assert': 3}
    if source.stem in thresholds:
        minimum = thresholds[source.stem]
        text = re.sub(r'\b(\d+),s', lambda m: f'{int(m[1])+1},s' if int(m[1]) >= minimum else m[0], text)
    if source.stem == 'memcpy':
        lines = text.splitlines()
        for i, line in enumerate(lines):
            # 6,S is saved destination; all other >=3 operands read arguments
            lines[i] = re.sub(r'\b(\d+),s', lambda m: f'{int(m[1])+1},s' if int(m[1]) >= 3 and int(m[1]) != 6 else m[0], line)
        text = '\n'.join(lines) + '\n'
    if source.parent.name == 'ieee32':
        if source.stem in {'engine', 'unpack'}:
            text = 'LIBC_RETURN_EXTRA=1\n' + text
        # Caller-owned homes move one byte for JSL/RTL; private frames do not
        stack_min = {'dec-copy':5, 'match':5, 'render':5, 'rounded':5,
                     'exponent':7, 'ieee-decimal':11, 'ieee-decimal-compare':5,
                     'dec-format':5, 'dec-format-spec':7, 'dec-format-raw':7}
        frame_min = {'hexparse':37, 'ieee-parse':61, 'dec-format-raw':101,
                     'dec-format':85, 'dec-format-spec':85}
        if source.stem in stack_min:
            text = re.sub(r'\b(\d+),s', lambda m: f'{int(m[1])+1},s' if int(m[1]) >= stack_min[source.stem] else m[0], text)
        if source.stem in frame_min:
            text = re.sub(r'a:(\d+),y', lambda m: f'a:{int(m[1])+1},y' if int(m[1]) >= frame_min[source.stem] else m[0], text)
    if source.parent.name == 'ieee64' and source.stem in {'rounded', 'decimal-compare'}:
        text = re.sub(r'\b(\d+),s', lambda m: f'{int(m[1])+1},s' if int(m[1]) >= 5 else m[0], text)
    if source.parent.name == 'ieee64' and source.stem == 'decimal-parse':
        text = re.sub(r'a:(\d+),y', lambda m: f'a:{int(m[1])+1},y' if int(m[1]) >= 61 else m[0], text)
    if source.parent.name == 'ieee64' and source.stem == 'hexparse':
        text = re.sub(r'a:(\d+),y', lambda m: f'a:{int(m[1])+1},y' if int(m[1]) >= 55 else m[0], text)
    if source.parent.name == 'ieee64' and source.stem in {'sqrt', 'log', 'exp', 'atan', 'trig'}:
        text = re.sub(r'\b(\d+),s', lambda m: f'{int(m[1])+1},s' if int(m[1]) >= 5 else m[0], text)
    if source.stem == 'console':
        text = text.replace('lda a:73,y', 'lda a:74,y').replace('lda a:75,y', 'lda a:76,y').replace('adc #77', 'adc #78')
    text = re.sub(r'(?m)^(\s*)rts\b', r'\1rtl', text)
    text = re.sub(r'(?m)^(\s*)jsr\s+\.loword\(([^)]+)\)', r'\1jsl \2', text)
    # Inter-unit tail calls must preserve PBR; local jumps remain short
    imported = {sym for line in re.findall(r'(?m)^\.import\s+(.+)$', text)
                for sym in re.findall(r'\b[A-Za-z_]\w*', line.split(';')[0])}
    for symbol in imported:
        text = re.sub(rf'\bjmp\s+\.loword\({re.escape(symbol)}\)', f'jml {symbol}', text)
    return text


def interrupt_objects(inputs):
    """Resolve DBR-relative symbol operands in emitted C interrupt bodies."""
    definitions = {}
    handlers = []
    for source, _, ident, _, text, _ in inputs:
        if source.suffix != '.c':
            continue
        for storage, symbol, linkage in re.findall(
                r'^\.segment "(BSS|DATA)"\n; allocation object (\w+) (local|global)$', text, re.M):
            scope = ident if linkage == 'local' else None
            definitions[scope, symbol] = ident, f'NEAR_{storage}_{ident}_{symbol}'
        for body in re.findall(r'^; allocation function \d+ begin\n(.*?)^; allocation function \d+ end$', text, re.M | re.S):
            vector = re.search(r'^\.export __vector_(\w+) := (\w+)$', body, re.M)
            if not vector:
                continue
            lvalues = set(re.findall(r'^; interrupt lvalue (\w+)$', body, re.M))
            operands = [symbol for immediate, symbol in re.findall(
                r'^ +(?!(?:jmp|jsr|jml|jsl)\b)\w+ +(#?)(?:a:)?\.loword\((_\w+)[+\-)]', body, re.M)
                        if not immediate or symbol in lvalues]
            handlers.append((vector[2], ident, dict.fromkeys(operands)))
    candidates = {}
    groups = {}
    for handler, ident, operands in handlers:
        group = groups[handler] = []
        for symbol in operands:
            definition = definitions.get((ident, symbol)) or definitions.get((None, symbol))
            if definition:
                owner, name = definition
                candidates.setdefault(owner, {})[symbol] = name
                group.append(name)
    return candidates, groups


def place_interrupt_objects(groups, sizes, aligns, near_start):
    cursor = near_start
    for name in ('LORAM_BSS', 'LORAM_DATA'):
        cursor = ((cursor + 1) & -2) + sizes.get(name, 0)
    promoted = {}
    for names in groups.values():
        pending = [name for name in names if name in sizes and name not in promoted]
        end = cursor
        for name in pending:
            end = ((end + aligns[name] - 1) & -aligns[name]) + sizes[name]
        if end <= 0x7E2000:
            promoted.update(dict.fromkeys(pending))
            cursor = end
    return promoted, cursor


def transform(text, ident, owner, stage, runtime_symbols, candidates=None):
    function = None; serial = 0; segments = {}; lines = []
    for line in text.splitlines():
        obj = re.fullmatch(r'; allocation object (\w+) (?:local|global)', line)
        if obj and candidates and obj[1] in candidates:
            lines[-1] = f'.segment "{candidates[obj[1]]}"'
            continue
        m = re.match(r'; allocation function (\d+) (begin|end)', line)
        if m:
            function = m[1] if m[2] == 'begin' else None
        m = re.match(r'\.segment "([^"]+)"(.*)', line)
        if m and wram.PART.fullmatch(m[1]):
            segments[m[1]] = ('wram-data' if m[1].startswith('ZWRAM_D_') else 'wram-bss', owner)
        if (m and not m[1].startswith(wram.UNQUALIFIED) and not wram.PART.fullmatch(m[1])
                and not cartridge_sram.PART.fullmatch(m[1])
                and m[1] not in RAM | FIXED | INITIALIZED | {'NMI_USER', 'NMI_BANK', 'NMI_LIBRARY', 'NMI_END'}):
            old = m[1]
            if old in {'CODE', 'STARTUP'}:
                suffix = function or ('STARTUP' if owner == 'runtime' and ident.endswith('_startup') else old)
                name = f'C_{ident}_{suffix}'
                kind = 'code'
            else:
                serial += 1; name = f'R_{ident}_{serial}'
                kind = 'asset' if old == 'EMBED' else 'constant'
            segments[name] = (kind, owner)
            line = f'.segment "{name}"{m[2]}'
        lines.append(line)
    return '\n'.join(lines) + '\n', segments


@dataclass(frozen=True)
class NearSpan:
    name: str
    address: int
    size: int
    region: str

    @property
    def clear(self):
        return self.name.startswith('NEAR_BSS_')


def near_layout(near_objects, promoted, sizes, near_start, *, with_end=False):
    # Match config's run order. Keep the existing interrupt placement groups
    # and never batch across the promoted/ordinary boundary
    ordinary = [name for name, _ in near_objects if name not in promoted]
    alignments = dict(near_objects)
    cursor = near_start
    spans = []
    for region, names in (
        ('pinned', ('LORAM_BSS', 'LORAM_DATA')),
        ('interrupt', promoted),
        ('main', ('BSS', 'DATA')),
        ('ordinary', ordinary),
    ):
        for name in names:
            alignment = alignments.get(name, 2)
            cursor = (cursor + alignment - 1) & -alignment
            size = sizes.get(name, 0)
            if size and region in {'interrupt', 'ordinary'}:
                spans.append(NearSpan(name, cursor, size, region))
            cursor += size
    return (spans, cursor) if with_end else spans


def initializer_runs(spans, group_data):
    runs = []
    for span in spans:
        if runs:
            run = runs[-1]
            first, last = run[0], run[-1]
            if (first.region == span.region and last.clear == span.clear
                    and (span.clear or group_data)
                    and last.address + last.size == span.address
                    and span.address + span.size - first.address <= 0x10000):
                run.append(span)
                continue
        runs.append([span])
    if not group_data:
        return runs

    padded = []
    for run in runs:
        if padded:
            left = padded[-1]
            last, first = left[-1], run[0]
            if (not last.clear and not first.clear and last.region == first.region
                    and last.address + last.size + 1 == first.address
                    and run_size(left + run) <= 0x10000):
                merged = left + run
                _, left_bytes, left_clocks = run_cost(left)
                _, right_bytes, right_clocks = run_cost(run)
                _, size, clocks = run_cost(merged)
                if size <= left_bytes + right_bytes and clocks <= left_clocks + right_clocks:
                    padded[-1] = merged
                    continue
        padded.append(run)
    return padded


def run_size(run):
    return run[-1].address + run[-1].size - run[0].address


def run_cost(run):
    size = run_size(run)
    first = run[0]
    words, tail = divmod(size, 2)
    # Long loads/stores cost four bytes and 5 cycles, plus one cycle
    # in A16. An odd tail needs SEP/REP (four bytes, six cycles)
    direct_bytes = (3 + 4 * (words + tail) if first.clear else 8 * (words + tail)) + 4 * tail
    direct_cycles = (3 + 6 * words + 5 * tail if first.clear else 12 * words + 10 * tail) + 6 * tail
    # Known-count DMA is 43 bytes, 56 CPU cycles of setup, plus eight
    # master clocks per byte. Model FastROM at six clocks per bus cycle
    # and WRAM writes at eight, with no DMA synchronization overhead
    direct_clocks = 6 * direct_cycles + 2 * size
    dma_clocks = 6 * 56 + 8 * size
    if direct_bytes <= 43 and direct_clocks <= dma_clocks:
        return True, direct_bytes, direct_clocks
    return False, 43, dma_clocks


def emit_near_run(lines, run):
    first = run[0]
    size = run_size(run)
    direct, _, _ = run_cost(run)
    dest = f'__{first.name}_RUN__'
    lines.append(f'.import {dest}')
    source = 'startup_zero'
    if not first.clear:
        source = f'__{first.name}_LOAD__'
        lines.append(f'.import {source}')
    if not direct:
        mode = '$08' if first.clear else '$00'
        lines.append(f'    boot_dma_known {source}, {dest}, {size}, {mode}')
        return
    if first.clear:
        lines.append('    lda #0')
    for offset in range(0, size, 2):
        if offset == size - 1:
            lines.extend(('    sep #$20', '    .a8'))
        if not first.clear:
            lines.append(f'    lda f:{source}+{offset}')
        lines.append(f'    sta f:{dest}+{offset}')
    if size % 2:
        lines.extend(('    rep #$20', '    .a16'))


def assemble_ram_initializer(directory, runs, runtime_segments, log, variant="", expanded=None):
    asm = directory / f'ram-init{variant}.s'
    lines = ['.setcpu "65816"', '.include "runtime/startup-dma.inc"',
             '.import startup_zero', '.a16', '.i16', '.segment "C_NEAR_INIT"',
             '.export __initialize_extra_ram', '__initialize_extra_ram:']
    lines.extend(f'    boot_clear "{name}"' for name in runtime_segments)
    for run_spans in runs:
        emit_near_run(lines, run_spans)
    lines.extend(wram.init_lines(expanded))
    lines.append('    rtl')
    if wram.near_tail(expanded):
        lines.extend((f'.segment "{wram.TAIL}"', '    .res 1'))
    save(asm, '\n'.join(lines) + '\n')
    obj = asm.with_suffix('.o')
    run([CC65/f'ca65{EXE}', '--cpu', '65816', '-g', '-I', ROOT, '-o', obj, asm], log)
    return obj


# Start with a small closed program that neither writes RAM except for sticky
# flags nor transfers control to unknown code. The startup clears BSS, and
# environment-state and terminate are the only additional runtime dependencies
# In particular, importing any mode setter or decimal conversion defeats this
# proof, including routines that change the mode only temporarily
DEFAULT_ROUNDING_IMPORTS = {
    'main_exit': 'runtime/startup.s',
    '_abort': 'runtime/terminate.s',
    '_exit': 'runtime/terminate.s',
    '__fp_exceptions': 'runtime/ieee64/environment-state.s',
    '__fp_round_mode': 'runtime/ieee64/environment-state.s',
}
ROUNDING_READ = 'lda a:.loword(__fp_round_mode)'
ROUNDING_SAFE_LINE = re.compile(
    r'\.(?:setcpu "65816"|a16|i16|segment "(?:CODE|RODATA)"|export _main)'
    r'|(?:_main|cg_\w+|return_\w+):'
    r'|(?:cg_\w+|return_\w+) = \*|__size_main = \* - _main'
    r'|(?:lda|ldx|ldy|cmp|cpx|cpy|bit) #(?:\$[0-9A-Fa-f]+|[0-9]+)'
    r'|(?:lsr|asl|inc|dec) a|clc|sec|tax|tay|txa|tya|rts|rtl'
    r'|b(?:cc|cs|eq|mi|ne|pl|ra|vc|vs) cg_\w+'
    r'|jmp \.loword\(cg_\w+\)|jml cg_\w+'
    r'|(?:jmp|jsr) \.loword\(_(?:abort|exit)\)|(?:jml|jsl) _(?:abort|exit)'
    r'|tsb a:\.loword\(__fp_exceptions\)|' + re.escape(ROUNDING_READ)
)


def default_rounding_unit(text, runtime_providers):
    for line in text.splitlines():
        line = line.split(';', 1)[0].strip()
        if line.startswith('.import '):
            symbol = line.removeprefix('.import ')
            expected = DEFAULT_ROUNDING_IMPORTS.get(symbol)
            if expected is None or runtime_providers.get(symbol) != [ROOT / expected]:
                return False
        elif line and not ROUNDING_SAFE_LINE.fullmatch(line):
            return False
    return True


def specialize_default_rounding(inputs, application_compiles, runtime_providers, directory,
                                cache_dir, stage, show, log):
    application = [unit for unit in inputs if unit[1] == 'application']
    rounding_units = [unit for unit in application if ROUNDING_READ in unit[4]]
    if not rounding_units or not all(default_rounding_unit(unit[4], runtime_providers)
                                     for unit in application):
        return inputs

    # Preserve the original objects' source and header identities, including
    # missing headers whose appearance could change include resolution
    specialized = {}
    for source, owner, ident, long_return, _, resources in rounding_units:
        flags, original_dependencies = application_compiles[ident]
        asm = directory / (ident + '.rounding.s')
        try:
            text, dependencies = compile_unit(source, asm, [*flags, '--rom-default-rounding'],
                                              cache_dir, stage, show, log, track_dependencies=True)
        except (RuntimeError, OSError):
            return inputs
        if (dependencies != original_dependencies or ROUNDING_READ in text or
                not default_rounding_unit(text, runtime_providers)):
            return inputs
        specialized[ident] = (source, owner, ident, long_return, text, resources)
    if any(dependency_hash(path) != digest for _, deps in application_compiles.values()
           for path, digest in deps.items()):
        return inputs
    return [specialized.get(unit[2], unit) for unit in inputs]


def transform_input(source, text, ident, owner, stage, runtime_symbols, candidates):
    if source.suffix == '.c':
        # The HiROM vector stub already establishes the handler bank
        text = re.sub(r'(?m)^(\.export __vector_\w+ := _\w+\n'
                      r'(?:\.export __nmi_entry := _\w+\n)?)'
                      r'    jml (interrupt_body_\w+)\n(?=\2:$)', r'\1', text)
    text, descriptions = transform(text, ident, owner, stage, runtime_symbols, candidates.get(ident))
    return text, descriptions


def resolve_objects(objects, mandatory, metadata, directory, stage, runtime_symbols, log):
    # Resolve runtime members like an archive, application definitions winning
    selected = list(mandatory)
    while True:
        exports = set().union(*(o['exports'] for o in selected))
        missing = set().union(*(o['imports'] for o in selected)) - exports - LINK_SYMBOLS
        added = False
        for name in sorted(missing):
            provider = next((o for o in objects if name in o['exports']), None)
            if provider is None and name.startswith(('__fnptr_', '__fnptr64_')):
                wide_result = name.startswith('__fnptr64_')
                prefix = '__fnptr64_' if wide_result else '__fnptr_'
                target = '_' + name.removeprefix(prefix)
                entry = next((o for o in objects if target in o['exports']), None)
                if entry is not None:
                    owner = entry['owner']
                    ident = f'callback_{len(objects)}'
                    asm = directory / (ident + '.s')
                    obj = asm.with_suffix('.o')
                    long_call = stage == 4 or stage == 3 and owner == 'runtime'
                    call = f'jsl {target}' if long_call else f'jsr .loword({target})'
                    result_cleanup = ('    tya\n    tcs\n    rtl\n' if wide_result else
                                      '    sta z:__arith_rhs\n    tya\n    tcs\n    lda z:__arith_rhs\n    rtl\n')
                    adapter = ('.setcpu "65816"\n.a16\n.i16\n.segment "CODE"\n'
                               f'.import {target}\n.importzp __arith_rhs\n'
                               f'.export {name}\n{name}:\n'
                               f'    {call}\n{result_cleanup}')
                    text, descriptions = transform(adapter, ident, owner, stage, runtime_symbols)
                    save(asm, text)
                    run([CC65/f'ca65{EXE}', '--cpu', '65816', '-g', '-o', obj, asm], log)
                    segs, imports, exports = inspect(obj, log)
                    provider = dict(path=obj, source=asm, owner=owner, segments=segs,
                                    imports=imports, exports=exports, resources=set(),
                                    ident=ident, flags=[])
                    objects.append(provider)
                    metadata.update(descriptions)
            if provider is None: raise RuntimeError(f'unresolved symbol {name}')
            if provider not in selected: selected.append(provider); added = True
        if not added: break
    return selected


def measure_wram(selected, sizes, aligns, near_objects, promoted, near_start):
    records = [dict(name=name, size=sizes[name], alignment=aligns[name],
                    members=[dict(source=str(o['source']), owner=o['owner'], size=size, alignment=alignment)
                             for o in selected for n, size, alignment in o['segments'] if n == name and size])
               for name in RUNTIME_RAM if sizes.get(name)]
    runtime = backfill(records)
    spans, near_end = near_layout(near_objects, promoted, sizes, near_start, with_end=True)
    expanded = wram.objects((name, size, aligns[name]) for o in selected
                            for name, size, _ in o['segments'] if size and name in sizes and wram.PART.fullmatch(name))
    exported = set().union(*(o['exports'] for o in selected))
    for obj in expanded:
        marker = f'__zicc_wram_{"X" if obj.crossing else "H"}_{obj.name}'
        for unit in selected:
            if (marker in exported and unit['source'].suffix == '.c'
                    and '_' + obj.name in unit['imports'] and marker not in unit['imports']):
                raise ValueError(f"{unit['source']}: conflicting WRAM placement for '{obj.name}'")
    heap = any(o['owner'] == 'runtime' and o['exports'] & wram.HEAP_EXPORTS for o in selected)
    return runtime, spans, wram.place(expanded, near_start, near_end, runtime, heap)


def specialize_wram(inputs, objects, mandatory, metadata, directory, stage, runtime_symbols, candidates,
                    compiles, cache_dir, show, track_dependencies, expanded, near_objects, promoted, near_start, log):
    if not expanded:
        return None
    near_names = {obj['name'] for obj in expanded['objects'] if obj['end'] <= wram.BOUNDARY}
    if not near_names:
        return None
    by_ident = {o['ident']: o for o in mandatory}
    replacements = {}
    alternate = directory / 'wram-specialized'
    descriptions = dict(metadata)
    try:
        for source, owner, ident, _, _, _ in inputs:
            if ident not in compiles:
                continue
            obj = by_ident[ident]
            referenced = {m[4] for name, _, _ in obj['segments'] if (m := wram.PART.fullmatch(name))}
            referenced.update(m[1] for name in obj['imports'] if (m := re.fullmatch(r'__zicc_wram_[HX]_(\w+)', name)))
            names = sorted(referenced & near_names)
            if not names:
                continue
            alternate.mkdir(exist_ok=True)
            asm = alternate / (ident + '.s')
            flags, original_dependencies = compiles[ident]
            text, deps = compile_unit(source, asm, [*flags, '--near-wram-objects', ','.join(names)],
                                      cache_dir, stage, show, log, track_dependencies=track_dependencies)
            if deps != original_dependencies:
                raise ValueError(f'{source}: compile dependencies changed')
            text, info = transform_input(source, text, ident, owner, stage, runtime_symbols, candidates)
            path = asm.with_suffix('.o')
            segs, imports, exports, _ = assemble_object(source, asm, path, text, obj['flags'], False, log)
            replacements[ident] = dict(obj, path=path, segments=segs, imports=imports, exports=exports)
            descriptions.update(info)
        if not replacements:
            return None
        providers = [replacements.get(o['ident'], o) for o in objects]
        roots = [replacements.get(o['ident'], o) for o in mandatory]
        selected = resolve_objects(providers, roots, descriptions, alternate, stage, runtime_symbols, log)
        sizes, aligns = segment_sizes(selected)
        declared = [(name, aligns[name]) for name in sizes if name.startswith(('NEAR_BSS_', 'NEAR_DATA_'))]
        if near_objects != declared:
            raise ValueError('specialization changed mandatory application objects')
        _, _, layout = measure_wram(selected, sizes, aligns, near_objects, promoted, near_start)
        if layout != expanded:
            raise ValueError('specialization changed WRAM placement')
        return selected, descriptions
    except (RuntimeError, ValueError, OSError) as error:
        log.write(f'WRAM specialization fallback: {error}')
        return None


def build(args):
    units = {}
    for source in args.sources:
        # Match the ASCII sanitization and 63-byte limit of Parser.unit
        stem = source.resolve().stem.encode('mbcs' if os.name == 'nt' else 'utf-8', errors='replace')
        name = re.sub(rb'[^A-Za-z0-9_]', b'_', stem)[:63]
        if name in units:
            raise RuntimeError(f'translation units have the same sanitized name {name.decode()!r}: '
                               f'{units[name]} and {source}')
        units[name] = source
    output = args.output.resolve(); output.parent.mkdir(parents=True, exist_ok=True)
    evidence = output.parent / (output.stem + '-allocation') / datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%S.%fZ'); evidence.mkdir(parents=True)
    log = BuildTranscript(evidence)
    try:
        return build_image(args, output, log)
    finally:
        if not getattr(args, 'keep_intermediates', False):
            log.prune_intermediates()


def build_image(args, output, log):
    sram = args.sram
    near_start = 0x7E0100 + args.stack_size
    evidence = log.evidence
    output.unlink(missing_ok=True)
    output.with_suffix('.allocation.json').unlink(missing_ok=True)
    history = []
    runtime_paths = [ROOT / 'runtime' / (n + '.s') for n in
                     ['startup', 'vectors', 'rom_header', 'nmi', 'nmi-bank', 'clock', 'clock_rate', 'dp-scratch',
                      'malloc', 'free', 'strcpy', 'strcmp', 'memcpy', 'memcpy-near', 'memset', 'memmove',
                      'terminate', 'sprintf', 'fabs', 'fabsf', 'ldexp', 'ldexpf', 'errno', 'sram']]
    runtime_paths += sorted((ROOT / 'runtime/integers').glob('*.s'))
    runtime_paths += sorted((ROOT / 'runtime/conversions').glob('*.s'))
    runtime_paths += sorted((ROOT / 'runtime/math').glob('*.s'))
    runtime_paths += sorted((ROOT / 'runtime/strings').glob('*.s'))
    runtime_paths += sorted((ROOT / 'runtime/bitops').glob('*.s'))
    runtime_paths += sorted((ROOT / 'runtime/ctype').glob('*.s'))
    runtime_paths += [ROOT / 'runtime/ieee32' / (name + '.s') for name in
                      ('fadd32', 'fsub32', 'fmul32', 'fdiv32', 'fcmp32',
                       'unpack', 'pack', 'right-a', 'normalize', 'addsub', 'mul', 'div', 'cmp', 'test', 'marker',
                       'tables', 'decimal-state')]
    runtime_paths += [ROOT / 'runtime/int64' / (name + '.s') for name in ('shift', 'mul', 'div', 'cmp', 'format')]
    ieee64 = ('environment-state', 'environment', 'cmp', 'neg', 'extend', 'truncate', 'fromint32', 'toint32',
              'fromint64', 'fromint64-to-float', 'toint64', 'addsub', 'mul', 'div')
    if args.binary64:
        ieee64 += ('sqrt', 'log', 'exp', 'atan', 'trig')
    ieee64 += ('decimal', 'decimal-compare', 'decimal-estimate', 'decimal-refine',
               'decimal-parse', 'hexparse', 'rounded', 'format')
    runtime_paths += [ROOT / 'runtime/ieee64' / (name + '.s') for name in ieee64]
    decimal_members = re.search(r'^DECIMAL_ASM := (.+)$', (ROOT/'Makefile').read_text(), re.M)[1].split()
    runtime_paths += [ROOT/'runtime/ieee32'/(name+'.s') for name in decimal_members]
    if args.console: runtime_paths += [ROOT / 'runtime/console.s']
    input_copy = evidence/'input.bin'
    input_copy.write_bytes(args.input.read_bytes().replace(b'\r\n', b'\n') if args.input else b'')
    runtime_paths += [ROOT / 'runtime/io.s']
    runtime_paths += [ROOT / 'runtime/qsort.s', ROOT / 'runtime/bsearch.s', ROOT / 'runtime/assert.s']
    runtime_paths += [ROOT / 'runtime/strtoint.s', ROOT / 'runtime/strto64.s', ROOT / 'runtime/abs.s', ROOT / 'runtime/labs.s']
    runtime_paths += [ROOT / 'runtime/calloc.s', ROOT / 'runtime/realloc.s']
    runtime_paths += [ROOT / 'runtime/int64/mul32.s']
    runtime_providers = {}
    for p in runtime_paths:
        if p.suffix == '.s':
            for line in p.read_text().splitlines():
                if line.startswith('.export '):
                    for symbol in re.findall(r'\b[A-Za-z_]\w*', line.split(';')[0][8:].split(':=')[0]):
                        runtime_providers.setdefault(symbol, []).append(p)
    for file, names in FAR_LIBRARY.items():
        for name in names:
            runtime_providers[name] = [ROOT / 'runtime' / file]
    far_import = re.compile(r'\b(?:' + '|'.join(name for names in FAR_LIBRARY.values() for name in names) + r')\b')
    runtime_symbols = set(runtime_providers)
    compile_cache = getattr(args, 'compile_cache', None) if not args.lto else None
    cache_dir = compile_cache.resolve() if compile_cache else None
    compile_dependencies = {}
    show = getattr(args, 'show_translation_units', False)
    can_prove_rounding = not (getattr(args, 'assembly', []) or args.console or args.input)
    cache = {}
    extended_banks = getattr(args, 'exhirom_banks', None)
    layouts = [64, extended_banks] if extended_banks else [
        banks for banks in [1, 2, 4, 8, 16, 32, 64] if banks * ROM_BANK <= args.max_rom]
    hirom_fits = False
    for banks in layouts:
        layout = RomLayout(banks)
        probe = extended_banks is not None and not layout.extended
        for stage in ([args.stage] if args.stage else [1] if banks == 1 else [1, 2] if banks == 2 else [1, 2, 3, 4]):
            if stage not in cache:
                directory = evidence / f'stage{stage}'; directory.mkdir(exist_ok=True)
                objects = []; metadata = {}; mandatory = []; inputs = []
                application_compiles = {}
                application_sources=args.sources[:1] if args.lto else args.sources
                for i, (source, owner) in enumerate([(p.resolve(), 'application') for p in application_sources+getattr(args,'assembly',[])] + [(p, 'runtime') for p in runtime_paths]):
                    resources = set()
                    ident = f'{i}_' + re.sub(r'[^A-Za-z0-9_]', '_', source.stem); asm = directory / (ident + '.s'); obj = asm.with_suffix('.o')
                    long_return = stage == 4 or stage == 3 and owner == 'runtime'
                    if source.suffix == '.c':
                        flags = []
                        if args.lto and owner == 'application':
                            flags = ['--lto', *[item for path in args.sources[1:]
                                                for item in ('--lto-source', path.resolve())]]
                        if owner == 'application':
                            flags.append('--large-rom-objects')
                            flags.extend(sram.compiler_flags())
                        if args.binary64: flags.append('--binary64')
                        if args.no_inline and owner == 'application': flags.append('--no-inline')
                        if long_return: flags.append('--long-return')
                        if stage == 3 and owner == 'application':
                            flags += ['--long-calls', ','.join(sorted(runtime_symbols))]
                        text, dependencies = compile_unit(source, asm, flags, cache_dir, stage, show, log,
                                                          track_dependencies=can_prove_rounding and owner == 'application')
                        if owner == 'application':
                            application_compiles[ident] = (flags, dependencies)
                        compile_dependencies.update(dependencies)
                        resources.update(re.findall(r'^; Embedded resource: (.*)$', text, re.M))
                        resources.update(re.findall(r'^; Source LTO dependency: (.*)$', text, re.M))
                    else:
                        text = source.read_text()
                        if owner == 'runtime' and source.stem == 'sprintf':
                            text = 'STRING_FORMAT=1\n.ifndef CALC\nCALC=1\n.endif\n' + (ROOT/'runtime/console.s').read_text()
                        if args.binary64: text = 'ZICC_BINARY64=1\n' + text
                        if owner == 'runtime' and source.stem == 'io': text = text.replace('build/input.bin', input_copy.as_posix())
                        if long_return and owner=='runtime': text = runtime_long(text, source)
                    # Reset optional console hook may cross banks in stage 3/4
                    if owner == 'runtime' and source.stem == 'startup' and stage >= 3:
                        text = text.replace('jsr .loword(__console_init)', 'jsl __console_init')
                    if owner == 'runtime' and source.stem == 'rom_header':
                        mode = 0x35 if extended_banks else 0x31
                        cart_type, sram_exponent = sram.header_bytes()
                        text = (f'.segment "HEADER"\n.res 21,0\n'
                                f'.byte ${mode:02X},{cart_type},0,{sram_exponent}\n.res 7,0\n')
                    inputs.append((source, owner, ident, long_return, text, resources))
                if any(far_import.search(text) for _, owner, _, _, text, _ in inputs if owner == 'application'):
                    for file in FAR_LIBRARY:
                        source = ROOT / 'runtime' / file
                        ident = f'{len(inputs)}_' + source.stem.replace('-', '_')
                        long_return = stage >= 3
                        if source.suffix == '.c':
                            flags = ['--long-return'] if long_return else []
                            text, _ = compile_unit(source, directory / (ident + '.s'), flags, cache_dir, stage, show, log)
                        else:
                            text = source.read_text()
                            if long_return:
                                text = runtime_long(text, source)
                        inputs.append((source, 'runtime', ident, long_return, text, set()))
                if can_prove_rounding:
                    inputs = specialize_default_rounding(inputs, application_compiles, runtime_providers,
                                                         directory, cache_dir, stage, show, log)
                candidates, interrupt_groups = interrupt_objects(inputs)
                for source, owner, ident, long_return, text, resources in inputs:
                    asm = directory / (ident + '.s'); obj = asm.with_suffix('.o')
                    text, descriptions = transform_input(source, text, ident, owner, stage, runtime_symbols, candidates)
                    for dependency in re.findall(r'(?m)^\s*\.(?:incbin|include)\s+"([^"]+)"', text):
                        candidate = ROOT/dependency
                        if not candidate.exists(): candidate = source.parent/dependency
                        resources.add(str(candidate.resolve()))
                    if owner == 'application':
                        log.keep_assembly.add(asm)
                    flags = ['-D', 'HIROM=1']
                    if source == ROOT/'runtime/startup.s': flags += ['-D', 'AUTO_RAM_INIT=1']
                    if owner=='application' and source.suffix=='.s': flags += ['-D',f'ZICC_LONG_CALLS={int(long_return)}']
                    if args.console: flags += ['-D', 'CONSOLE=1']
                    if args.input: flags += ['-D', 'CALC=1']
                    segs, imports, exports, cached = assemble_object(source, asm, obj, text, flags, owner == 'runtime', log)
                    info = dict(path=obj, source=source, owner=owner, segments=segs, imports=imports, exports=exports,
                                resources=resources, ident=ident, flags=flags)
                    if cached is not None:
                        info.update(cached=cached, assembly=text)
                        if getattr(args, 'keep_intermediates', False):
                            materialize_object(info)
                    objects.append(info); metadata.update(descriptions)
                    if owner == 'application' or source.stem in {'startup', 'vectors', 'rom_header', 'console'}: mandatory.append(info)
                selected = resolve_objects(objects, mandatory, metadata, directory, stage, runtime_symbols, log)
                # Keep NMI ordering independent of dependency traversal order
                sizes, aligns = segment_sizes(selected)
                near_objects = [(name, aligns[name]) for name in sizes if name.startswith(('NEAR_BSS_', 'NEAR_DATA_'))]
                promoted, low_end = place_interrupt_objects(interrupt_groups, sizes, aligns, near_start)
                runtime_ram, spans, expanded = measure_wram(selected, sizes, aligns, near_objects, promoted, near_start)
                specialized = specialize_wram(inputs, objects, mandatory, metadata, directory, stage, runtime_symbols,
                                              candidates, application_compiles, cache_dir, show, can_prove_rounding, expanded,
                                              near_objects, promoted, near_start, log)
                if specialized:
                    selected, metadata = specialized
                    sizes, aligns = segment_sizes(selected)
                    runtime_ram, spans, expanded = measure_wram(selected, sizes, aligns, near_objects, promoted, near_start)
                if expanded:
                    expanded['specialized'] = bool(specialized)
                    defining_units = {name: o for o in selected for name, size, _ in o['segments']
                                      if size and wram.PART.fullmatch(name)}
                    for ram in expanded['objects']:
                        definition = defining_units[ram['parts'][0]['name']]
                        symbol = '_' + ram['name']
                        ram['definition'] = str(definition['source'])
                        ram['linkage'] = 'external' if symbol in definition['exports'] else 'internal'
                        ram['reference_units'] = [str(o['source']) for o in selected if symbol in o['imports']]
                select_interrupts = interrupt_groups and not args.fixed_interrupt_addressing
                if select_interrupts:
                    exports, local = interrupt_addressing.objects(inputs, promoted)
                library_nmi = 'NMI_BANK' in sizes or 'NMI_LIBRARY' in sizes
                for o in selected:
                    materialize_object(o)
                    if o['source'].suffix != '.c':
                        continue
                    obj = o['path']
                    asm = obj.with_suffix('.s')
                    text = asm.read_text()
                    addressed = interrupt_addressing.select(
                        text, exports | local.get(o['ident'], {}), library_nmi,
                        low_end < 0x7E2000) if select_interrupts else text
                    optimized = accumulator_width.select(addressed)
                    candidate = obj.with_suffix('.addressing.o')
                    for updated in dict.fromkeys((optimized, addressed)):
                        if updated == text:
                            save(asm, text)
                            break
                        save(asm, updated)
                        try:
                            run([CC65/f'ca65{EXE}', '--cpu', '65816', '-g', '-I', ROOT, '-I', o['source'].parent,
                                 *o['flags'], '-o', candidate, asm], log)
                        except RuntimeError as error:
                            if 'Range error' not in str(error):
                                raise
                            # Retry without width edits if a relaxed branch
                            # went out of range, then fall back to the original
                            save(asm, text)
                            continue
                        candidate.replace(obj)
                        o.pop('debug_source', None)
                        o['segments'], _, _ = inspect(obj, log)
                        break
                sizes, aligns = segment_sizes(selected)
                sram_objects = sram.allocate(
                    [(name, size, alignment) for obj in selected for name, size, alignment in obj['segments']
                     if size and cartridge_sram.PART.fullmatch(name)],
                    [name.removeprefix(wram.UNQUALIFIED) for obj in selected for name, _, _ in obj['segments']
                     if name.startswith(wram.UNQUALIFIED)])
                runtime_segments = [name for name in RUNTIME_RAM if sizes.get(name)]
                units = []; nmi_parts = []
                for name, size in sizes.items():
                    if name in RAM | FIXED or name.startswith(('NEAR_BSS_', 'ZWRAM_B_')) or not size: continue
                    if cartridge_sram.PART.fullmatch(name): continue
                    if name in {'NMI_USER', 'NMI_BANK', 'NMI_LIBRARY', 'NMI_END'}: continue
                    kind, owner = metadata.get(name, ('data', 'runtime'))
                    units.append(Unit(name, size, aligns[name], kind, owner))
                cursor = 0
                for name in ['NMI_USER', 'NMI_BANK', 'NMI_LIBRARY', 'NMI_END']:
                    if name in sizes:
                        nmi_parts.append((name, sizes[name], aligns[name]))
                        cursor = ((cursor + aligns[name] - 1) & -aligns[name]) + sizes[name]
                if cursor: units.append(Unit('INTERRUPT', cursor, max(a for _,_,a in nmi_parts), 'code', 'runtime'))
                for unit in units:
                    if unit.size > ROM_BANK and not bank_crossing_data(unit):
                        raise RuntimeError(f'indivisible allocation {unit.name} exceeds a 64 KiB bank ({unit.size} bytes)')
                cache[stage] = (selected, units, nmi_parts, set().union(*(o['resources'] for o in selected)),
                                runtime_ram, near_objects, promoted, spans, runtime_segments, directory, {}, expanded, sram_objects)
            selected, units, nmi_parts, resources, runtime_ram, near_objects, promoted, spans, runtime_segments, directory, variants, expanded, sram_objects = cache[stage]
            for group_data in (True, False):
                if not group_data and not variants[True][2]:
                    continue
                if group_data not in variants:
                    runs = initializer_runs(spans, group_data)
                    batches = [batch for batch in runs if len(batch) > 1 and not batch[0].clear]
                    suffix = '' if group_data else '-unbatched'
                    initializer = assemble_ram_initializer(directory, runs, runtime_segments, log, suffix, expanded)
                    init_segments, _, _ = inspect(initializer, log)
                    init_units = [Unit(name, size, alignment, 'code', 'runtime')
                                  for name, size, alignment in init_segments if size and name != wram.TAIL]
                    init_object = dict(path=initializer, source=initializer.with_suffix('.s'), resources=set(),
                                       segments=init_segments, owner='runtime')
                    variants[group_data] = init_object, init_units, batches
                init_object, init_units, batches = variants[group_data]
                link_units = units + init_units
                large_data_first = False
                try:
                    try:
                        placements, free = pack(link_units, banks, stage, batches)
                    except PackingError:
                        if not layout.extended or stage != 4 or not any(
                                u.size > ROM_BANK and bank_crossing_data(u) for u in link_units):
                            raise
                        # Moving code can free an entire contiguous ROM region
                        large_data_first = True
                        placements, free = pack(link_units, banks, stage, batches, large_data_first=True)
                except PackingError as error:
                    if not probe:
                        history.append(dict(stage=stage, capacity=banks*ROM_BANK, grouped_data=bool(batches), error=str(error)))
                        (evidence/'rejected-layouts.json').write_text(json.dumps(history, indent=2)+'\n')
                else:
                    break
            else:
                continue
            if probe:
                hirom_fits = True
                break
            units = link_units
            selected = selected + [init_object]
            attempt = evidence / f'{banks*64}k-stage{stage}'; attempt.mkdir(exist_ok=True)
            cfg = attempt/'link.cfg'
            save(cfg, config(units, placements, banks, nmi_parts, runtime_ram, near_objects, promoted,
                             stack_size=args.stack_size, batches=batches, expanded=expanded,
                             sram=sram, sram_objects=sram_objects))
            temp = attempt/'image.raw'
            debug = output.with_suffix('.dbg')
            log.keep_assembly.update(o['path'].with_suffix('.s') for o in selected)
            run([CC65/f'ld65{EXE}', '-C', cfg, '-m', output.with_suffix('.map'), '--dbgfile', debug,
                 '-Ln', output.with_suffix('.labels'), '-o', temp, *[o['path'] for o in selected]], log)
            relocate_debug_sources(debug, selected)
            map_text = output.with_suffix('.map').read_text()
            linked = {name:(int(address,16),int(size,16)) for name,address,size in
                      re.findall(r'^(\w+)\s+([0-9A-F]+)\s+[0-9A-F]+\s+([0-9A-F]+)\s+[0-9A-F]+\s*$',map_text,re.M)}
            symbol_text = output.with_suffix('.labels').read_text()
            symbols = {name:int(address,16) for address,name in re.findall(r'^al (\w+) \.(\S+)$',symbol_text,re.M)}
            for span in spans:
                if linked.get(span.name) != (span.address, span.size):
                    raise RuntimeError(f'final WRAM placement differs for {span.name}')
            for name in promoted:
                address, size = linked[name]
                if not near_start <= address < address + size <= 0x7E2000:
                    raise RuntimeError(f'final interrupt object {name} exceeds low WRAM')
            for record in runtime_ram['objects']:
                if linked.get(record['name']) != (record['address'],record['size']):
                    raise RuntimeError(f"final runtime RAM placement differs for {record['name']}")
            addresses = {name: layout.address(*placement) for name, placement in placements.items()}
            for unit in units:
                address = addresses[unit.name]
                if unit.name == 'INTERRUPT':
                    cursor = address
                    for name, size, alignment in nmi_parts:
                        cursor = (cursor+alignment-1)&-alignment
                        if linked.get(name) != (cursor,size): raise RuntimeError(f'final NMI placement differs for {name}')
                        cursor += size
                elif unit.name in INITIALIZED or unit.name.startswith(('NEAR_DATA_', 'ZWRAM_D_')):
                    if linked.get(unit.name,(0,0))[1] != unit.size or symbols.get('__'+unit.name+'_LOAD__') != address:
                        raise RuntimeError(f'final {unit.name} load placement differs from measured layout')
                elif linked.get(unit.name) != (address,unit.size):
                    raise RuntimeError(f'final placement differs from measured layout for {unit.name}')
            if expanded:
                wram.verify(expanded, linked, symbols, addresses)
            cartridge_sram.verify(sram_objects, linked)
            capacity = banks * ROM_BANK
            if temp.stat().st_size != capacity:
                raise RuntimeError('linked ROM length does not match manifest')
            temp.replace(output)
            manifest = dict(evidence=str(evidence), mapping=layout.mapping, stage=stage, capacity=capacity,
                            sram=dict(sram.manifest(), objects=sram_objects),
                            order='large-data-first' if large_data_first else 'code-first', history=history,
                            units=[dict(name=u.name, size=u.size, alignment=u.alignment, kind=u.kind, owner=u.owner,
                                        address=addresses[u.name], file_offset=layout.file_offset(*placements[u.name])) for u in units],
                            free=free, runtime_ram=runtime_ram, stack_size=args.stack_size,
                            sha256=file_sha256(output),
                             linked_objects={o['path'].relative_to(evidence).as_posix(): file_sha256(o['path'])
                                             for o in selected},
                            sources={str(o['source'].relative_to(ROOT) if o['source'].is_relative_to(ROOT) else o['source']):hashlib.sha256(o['source'].read_bytes()).hexdigest() for o in selected},
                            resources={name:hashlib.sha256(Path(name).read_bytes()).hexdigest() for name in sorted(resources)},
                            tools={name:hashlib.sha256((CC65/name).read_bytes()).hexdigest() for name in [f'ca65{EXE}',f'ld65{EXE}',f'od65{EXE}']},
                            compiler_sha256=file_sha256(compiler_executable()),
                            source_lto=args.lto, lto_sources={str(p.resolve()):hashlib.sha256(p.read_bytes()).hexdigest() for p in args.sources} if args.lto else {})
            if expanded:
                manifest['application_wram'] = expanded
            if cache_dir is not None:
                manifest['compile_cache_hits'] = log.compile_cache_hits
                manifest['compile_dependencies'] = {path: digest is not None
                                                    for path, digest in compile_dependencies.items()}
            output.with_suffix('.allocation.json').write_text(json.dumps(manifest, indent=2)+'\n')
            if hirom_fits:
                print(f'warning: this build fits in HiROM at 4096 KiB or less. '
                      f'Writing the requested {capacity//1024} KiB ExHiROM image.', file=sys.stderr)
            print(f'{output}: {"ExHiROM" if layout.extended else "HiROM"}, {capacity//1024} KiB')
            return manifest
    hint = '' if extended_banks else '\nConsider --mapping exhirom --rom-size 6144 or 8192 (KiB).'
    raise RuntimeError(f'cannot pack within maximum {"ExHiROM" if extended_banks else "HiROM"} capacity: '
                       + json.dumps(history) + hint)


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('sources', type=Path, nargs='+', help='one or more C source files')
    p.add_argument('-o', '--output', type=Path, required=True, help='path for the raw ROM image')
    p.add_argument('--stage', type=int, choices=[1,2,3,4], help='try only this layout stage when diagnosing a build (the ROM can still grow)')
    p.add_argument('--console', action='store_true', help='include the text console')
    p.add_argument('--binary64', action='store_true', help='use 64 bits for double and long double')
    p.add_argument('--stack-size', type=int, default=1024, metavar='BYTES',
                   help='reserve 256 to 7936 stack bytes (default: 1024)')
    p.add_argument('--show-translation-units', action='store_true', help='print each source filename before compiling it')
    p.add_argument('--keep-intermediates', action='store_true',
                   help='keep unlinked assembly and all object files for build diagnosis')
    p.add_argument('--compile-cache', type=Path, metavar='DIR',
                   help='reuse saved assembly when the source and its dependencies match (without --lto)')
    p.add_argument('--lto', action='store_true', help='allow the compiler to inline functions across C files after preprocessing each file')
    p.add_argument('--no-inline', action='store_true', help='inline an application function only when explicitly required')
    p.add_argument('--fixed-interrupt-addressing', action='store_true', help='use DBR $7E and D $0000 for interrupt comparisons')
    p.add_argument('--assembly', type=Path, action='append', default=[], help='link a ca65 assembly file (ZICC_LONG_CALLS selects how C calls its entries)')
    p.add_argument('--input', type=Path, help='bundle fixed input for fgets and enable floating-point console formatting')
    p.add_argument('--mapping', choices=['hirom', 'exhirom'], default='hirom')
    p.add_argument('--sram-size', type=int, default=0, metavar='KIB',
                   help='battery-backed cartridge RAM in KiB (default: 0)')
    p.add_argument('--rom-size', type=int, choices=[6144, 8192], metavar='KIB',
                   help='required ExHiROM image size, 6144 or 8192 KiB')
    p.add_argument('--max-rom', type=int, help='maximum HiROM bytes, up to 4 MiB')
    args = p.parse_args()
    if not 256 <= args.stack_size <= 7936:
        p.error('--stack-size must be between 256 and 7936 bytes')
    if any(source.suffix != '.c' for source in args.sources): p.error('application inputs must be C translation units')
    try:
        args.sram = cartridge_sram.CartridgeSram(args.mapping, args.sram_size)
    except ValueError as error:
        p.error(str(error))
    if args.mapping == 'exhirom':
        if args.rom_size is None or args.max_rom is not None:
            p.error('ExHiROM requires --rom-size 6144 or 8192 and does not use --max-rom')
        args.exhirom_banks = args.rom_size // 64
    else:
        if args.rom_size is not None:
            p.error('--rom-size requires --mapping exhirom')
        if args.max_rom is None:
            args.max_rom = 4 * 1024 * 1024
        if not ROM_BANK <= args.max_rom <= 4*1024*1024 or args.max_rom & (args.max_rom-1):
            p.error('--max-rom must be a power of two from 65536 to 4194304')
    try: build(args)
    except (RuntimeError, ValueError, OSError) as e: p.exit(1, str(e)+'\n')


if __name__ == '__main__': main()
