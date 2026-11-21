"""Link a ROM with a chosen memory layout and place its data in working RAM.

A first link measures the runtime pieces the program uses. A final link sets
aside RAM for them, assigns each application object its address in RAM and
its source in ROM when needed, and adds the startup code that fills RAM.
"""
import argparse
from datetime import datetime, timezone
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
from runtime_ram import RUNTIME_RAM, backfill, LOW
import application_wram as wram
import cartridge_sram

ROOT=Path(__file__).resolve().parents[1]
EXE = '.exe' if os.name == 'nt' else ''
CC65 = Path(os.environ.get('CC65_BIN') or ('C:/bin/cc65/bin' if os.name == 'nt' else
                                           Path(shutil.which('ca65') or '/usr/bin/ca65').parent))
ROM_AREA=re.compile(r'^\s*(ROM(?:_DATA|[0-9A-F]{2})?):[^;]*\bfile\s*=\s*%O[^;]*;', re.M)
INIT='ZWRAM_INIT'


def capacity_hint(config_path):
    if re.fullmatch(r'lorom\d+', config_path.stem):
        return ('Consider automatic HiROM, or ExHiROM with '
                'tools/build-rom.py --mapping exhirom --rom-size 6144 or 8192 (KiB).')
    if re.fullmatch(r'hirom\d+', config_path.stem):
        return 'Consider tools/build-rom.py --mapping exhirom --rom-size 6144 or 8192 (KiB).'
    return ''


def config(text, layout=None, *, sram=None, sram_objects=()):
    lines=[]
    for line in text.splitlines():
        stripped=line.strip()
        if ('RAM7F_' in line or '__RUNTIME_RAM_BOTTOM__:' in line or
            '__RUNTIME_RAM_TOP__:' in line or re.match(r'__runtime_\w+_size:',stripped)):
            continue
        if any(stripped.startswith(name+':') for name in RUNTIME_RAM):
            continue
        lines.append(line)
    text='\n'.join(lines)+'\n'
    if layout is None:
        memory=[' RAM7F_PROBE: start=$7F0000, size=$10000, type=rw, file="";']
        segments=[f' {name}: load=RAM7F_PROBE, type=bss, optional=yes, define=yes, align=2;' for name in RUNTIME_RAM]
        lower=LOW
    else:
        memory=[];segments=[];lower=layout['lower']
        for obj in layout['objects']:
            name=obj['name']
            memory.append(f' RAM7F_{name}: start=${obj["address"]:06X}, size=${obj["size"]:X}, type=rw, file="";')
            segments.append(f' {name}: load=RAM7F_{name}, type=bss, define=yes, align={obj["alignment"]};')
    symbols=[f' __RUNTIME_RAM_BOTTOM__: type=export, value=${lower:06X};',
             ' __RUNTIME_RAM_TOP__: type=export, value=$800000;']
    if layout is not None:
        live = {obj['name'] for obj in layout['objects']}
        symbols.extend(f' __{name}_{suffix}__: type=weak, value=0;'
                       for name in RUNTIME_RAM if name not in live for suffix in ('RUN', 'SIZE'))
    if sram is not None:
        symbols.extend(sram.linker_symbols())
        sram_memory, sram_segments = sram.linker_regions(sram_objects)
        memory.extend(sram_memory)
        segments.extend(sram_segments)
    return text.replace('MEMORY {','MEMORY {\n'+'\n'.join(memory)).replace('SEGMENTS {','SEGMENTS {\n'+'\n'.join(segments)).replace('SYMBOLS {','SYMBOLS {\n'+'\n'.join(symbols))


def run(command,log, *, cwd=None, rom_hint=''):
    result=subprocess.run(list(map(str,command)),capture_output=True,text=True,cwd=cwd)
    with log.open('a', encoding='utf-8') as stream:
        stream.write(subprocess.list2cmdline(list(map(str,command)))+'\n'+result.stdout+result.stderr+'\n')
    if result.returncode:
        # ld65 can quote names with ASCII or UTF-8 punctuation. Match the
        # words independently of the active Windows console code page
        overflows = re.findall(r'Segment \W*(\w+)\W* overflows memory area \W*NEAR\W* by (\d+) bytes?',
                               result.stderr, re.ASCII)
        if overflows:
            segment, excess = max(overflows, key=lambda item: int(item[1]))
            count = int(excess)
            sys.stderr.write(wram.near_exhaustion(
                f'Static allocations exceed the available space by at least {count:,} '
                f'{"byte" if count == 1 else "bytes"} after placing segment {segment}.') + '\n')
        if rom_hint and re.search(r'overflows memory area \W*ROM(?:_DATA|[0-9A-F]{2})?\W',
                                  result.stderr, re.ASCII):
            sys.stderr.write(rom_hint + '\n')
        sys.stdout.write(result.stdout);sys.stderr.write(result.stderr)
        raise SystemExit(result.returncode)
    return result


def input_files(args):
    """Resolve explicit ld65 modules and its supplied object/library paths."""
    search = {'object': [Path.cwd()], 'library': [Path.cwd()]}
    paths = {'-L': 'library', '--lib-path': 'library', '--obj-path': 'object'}
    inputs = {'--obj': 'object', '--lib': 'library'}
    values = {'-D', '--define', '-S', '--start-addr', '-t', '--target',
              '-u', '--force-import', '--cfg-path', '--module-id', '--color'}
    modules = []
    args = iter(args)
    for arg in args:
        if arg in paths:
            search[paths[arg]].append(Path(next(args)))
        elif arg in inputs:
            modules.append((next(args), inputs[arg]))
        elif arg in values:
            next(args)
        elif not arg.startswith('-'):
            modules.append((arg, None))
    for name, kind in modules:
        for folder in (search[kind] if kind else search['object'] + search['library']):
            path = (folder/name).resolve()
            if path.is_file():
                yield path
                break


def inspect(path, evidence):
    dump = run([CC65/f'od65{EXE}', '--dump-segments', path], evidence).stdout
    return [(name, int(size), int(alignment)) for name, size, alignment in
            re.findall(r'Name:\s*"([^"]+)"\s+Flags:\s+\d+\s+Size:\s+(\d+)\s+Alignment:\s+(\d+)', dump)]


def annotated_segments(probe, evidence):
    names = {}
    log = evidence / 'link.log'

    def record(path):
        for name, size, alignment in inspect(path, log):
            if size and (wram.PART.fullmatch(name) or cartridge_sram.PART.fullmatch(name)):
                names[name] = max(alignment, names.get(name, 1))

    for i, path in enumerate(dict.fromkeys(input_files(probe))):
        data = path.read_bytes()
        if b'ZWRAM_' not in data and b'ZSRAM_' not in data:
            continue
        if data[:4] == b'naUz':
            members = run([CC65/f'ar65{EXE}', 'l', path], log).stdout.splitlines()
            members = [m for m in members if Path(m).name == m and m not in {'.', '..'}]
            if not members:
                continue
            directory = evidence/f'archive{i}'
            directory.mkdir()
            # Extract individually to stay within the Windows command length limit
            for member in members:
                run([CC65/f'ar65{EXE}', 'x', path, member], log, cwd=directory)
                candidate = directory/member
                data = candidate.read_bytes()
                if b'ZWRAM_' in data or b'ZSRAM_' in data:
                    record(candidate)
                candidate.unlink()
            directory.rmdir()
        else:
            record(path)
    return names


def probe_config(original, names, sram):
    text = config(original, sram=sram)
    memory = [f' P_{name}: start=$7F0000, size=$20000, type=rw, file="";' for name in sorted(names)]
    segments = [f' {name}: load=P_{name}, type={"rw" if name.startswith("ZWRAM_D_") else "bss"}, '
                f'align={names[name]}, optional=yes;'
                for name in sorted(names)]
    symbols = {wram.PART.fullmatch(name)[4] if wram.PART.fullmatch(name)
               else cartridge_sram.PART.fullmatch(name)[6] for name in names}
    memory.append(' WRAM_DECLARATIONS: start=0, size=0, file="";')
    segments.extend(f' {wram.UNQUALIFIED}{name}: load=WRAM_DECLARATIONS, type=ro, optional=yes, define=yes;'
                    for name in sorted(symbols))
    text = text.replace('MEMORY {', 'MEMORY {\n' + '\n'.join(memory))
    text = text.replace('SEGMENTS {', 'SEGMENTS {\n' + '\n'.join(segments))
    return ROM_AREA.sub(lambda m: m[0] if 'define' in m[0] else m[0][:-1]+', define=yes;', text)


def label_values(path):
    return {name: int(address,16) for address,name in re.findall(r'^al (\w+) \.(\S+)$',path.read_text(),re.M)}


def map_extents(text):
    return {name: (int(address,16), int(size,16), int(alignment,16)) for name,address,size,alignment in
            re.findall(r'^(\w+)\s+([0-9A-F]+)\s+[0-9A-F]+\s+([0-9A-F]+)\s+([0-9A-F]+)\s*$',text,re.M)}


def expanded_config(original, runtime, expanded, evidence, probe_labels, rom_hint='', *, sram, sram_objects):
    lines=['.setcpu "65816"', '.include "runtime/startup-dma.inc"',
           '.import startup_zero, reset_native', '.a16', '.i16',
           f'.segment "{INIT}"', '.export __zicc_wram_reset', '__zicc_wram_reset:',
           '    rep #$30', *wram.init_lines(expanded), '    jml reset_native']
    tail = wram.near_tail(expanded)
    if tail:
        lines.extend((f'.segment "{wram.TAIL}"', '    .res 1'))
    asm = evidence/'wram-init.s'
    asm.write_text('\n'.join(lines)+'\n')
    obj = asm.with_suffix('.o')
    run([CC65/f'ca65{EXE}', '--cpu', '65816', '-I', ROOT, '-g', '-o', obj, asm], evidence/'link.log')
    init_size = next(size for name,size,_ in inspect(obj,evidence/'link.log') if name == INIT)
    windows = {}
    for match in ROM_AREA.finditer(original):
        name = match[1]
        start = probe_labels[f'__{name}_START__']
        end = start + probe_labels[f'__{name}_SIZE__']
        free = probe_labels[f'__{name}_LAST__']
        if (start >> 16) == ((end-1) >> 16) and free < end:
            windows[name] = [free, end]
    load_addresses = {}
    segments = [wram.segment(p) for p in wram.parts(expanded) if p['clear']]
    data = [p for p in wram.parts(expanded) if not p['clear']]
    for p in sorted(data + [dict(name=INIT,size=init_size,alignment=1)], key=lambda p: (-p['size'], p['name'])):
        size, alignment, segment_name = p['size'], p['alignment'], p['name']
        for area, (free,end) in windows.items():
            start = wram.align_up(free, alignment)
            if start+size > end:
                continue
            windows[area][0] = start+size
            load_addresses[segment_name] = start
            if segment_name == INIT:
                segments.append(f' {INIT}: load={area}, type=ro;')
            else:
                segments.append(wram.segment(p, area)[:-1]+f', align_load={alignment};')
            break
        else:
            message = f'no contiguous ROM load window for {segment_name} ({size} bytes)'
            raise ValueError('\n'.join(filter(None, (message, rom_hint))))
    if tail:
        segments.append(tail)
    text = config(original,runtime,sram=sram,sram_objects=sram_objects)
    text = re.sub(r'__zicc_reset_offset__:.*?;', '__zicc_reset_offset__: type=export, '
                  'value=__zicc_wram_reset - reset_native, addrsize=far;', text)
    text = text.replace('MEMORY {', 'MEMORY {\n'+'\n'.join(wram.run_regions(expanded)))
    # Appending preserves the manual config's original run and load order
    begin = text.index('SEGMENTS {')
    end = text.index('}', begin)
    text = text[:end]+'\n'.join(segments)+'\n'+text[end:]
    return text, obj, load_addresses


def main():
    parser = argparse.ArgumentParser(allow_abbrev=False, description=__doc__,
                                     epilog='Pass the usual ld65 options, including -C and -o.')
    parser.add_argument('--sram-size', type=int, default=0, metavar='KIB')
    parser.add_argument('--mapping', choices=['lorom', 'hirom'])
    options, args = parser.parse_known_args()
    cfg=Path(args[args.index('-C')+1]).resolve()
    named_mapping = re.fullmatch(r'(lorom|hirom)\d+', cfg.stem, re.IGNORECASE)
    config_mapping = named_mapping[1].lower() if named_mapping else None
    if config_mapping and options.mapping and config_mapping != options.mapping:
        parser.error(f'--mapping conflicts with {cfg.name}')
    mapping = options.mapping or config_mapping
    if options.sram_size and not mapping:
        parser.error('--sram-size with a custom layout requires --mapping lorom or hirom')
    sram = cartridge_sram.CartridgeSram(mapping or 'lorom', options.sram_size)
    rom_hint=capacity_hint(cfg)
    output=Path(args[args.index('-o')+1]).resolve()
    evidence=output.parent/(output.stem+'-runtime-ram')/datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%S.%fZ')
    evidence.mkdir(parents=True)
    original=cfg.read_text()
    probe_cfg=evidence/'probe.cfg'
    # Retain all input/selection options, replacing only output artifacts
    probe=[];index=0
    output_options={'-C','-o','-m','-Ln','--dbgfile','--mapfile','--label-file','--config'}
    while index<len(args):
        if args[index] in output_options:index+=2
        else:probe.append(args[index]);index+=1
    ld65=CC65/f'ld65{EXE}'
    names=annotated_segments(probe,evidence)
    probe_cfg.write_text(probe_config(original,names,sram) if names else config(original,sram=sram))
    probe_map=evidence/'probe.map'
    label=evidence/'probe.labels'
    label_args=['-Ln',label] if names else []
    run([ld65,*probe,'-C',probe_cfg,'-m',probe_map,*label_args,'-o',evidence/'probe.raw'],
        evidence/'link.log', rom_hint=rom_hint)
    sram.check_rom_size((evidence/'probe.raw').stat().st_size)
    text=probe_map.read_text();records=[]
    for name in RUNTIME_RAM:
        match=re.search(r'^'+name+r'\s+[0-9A-F]+\s+[0-9A-F]+\s+([0-9A-F]+)\s+([0-9A-F]+)\s*$',text,re.M)
        if match and int(match[1],16):
            members=[];owner=None
            for line in text.splitlines():
                if line and not line[0].isspace() and line.endswith(':'):owner=line[:-1]
                m=re.match(r'\s+'+name+r'\s+Offs=\w+\s+Size=(\w+)\s+Align=(\w+)',line)
                if m and int(m[1],16):members.append(dict(object=owner,owner='explicit-runtime-class',size=int(m[1],16),alignment=int(m[2],16)))
            records.append(dict(name=name,size=int(match[1],16),alignment=int(match[2],16),members=members))
    layout=backfill(records)
    expanded=None
    sram_objects=[]
    if names:
        extents=map_extents(text)
        live=wram.objects((name,size,alignment) for name,(_,size,alignment) in extents.items())
        sy=label_values(label)
        for obj in live:
            if f'__{wram.UNQUALIFIED}{obj.name}_RUN__' in sy:
                raise ValueError(f"conflicting WRAM placement for '{obj.name}'")
        if any(wram.PART.fullmatch(name) for name in names):
            expanded=wram.place(live,sy['__NEAR_START__'],sy['__NEAR_LAST__'],layout,bool(sy.keys() & wram.HEAP_EXPORTS))
        sram_objects=sram.allocate(
            [(name,size,alignment) for name,(_,size,alignment) in extents.items()
             if size and cartridge_sram.PART.fullmatch(name)],
            [name.removeprefix(f'__{wram.UNQUALIFIED}').removesuffix('_RUN__')
             for name in sy if name.startswith(f'__{wram.UNQUALIFIED}') and name.endswith('_RUN__')])
    final_cfg=evidence/'link.cfg'
    final=list(args);final[final.index('-C')+1]=str(final_cfg)
    if expanded:
        if '__zicc_reset_offset__' not in sy or 'reset_native' not in sy:
            raise ValueError('expanded WRAM requires a current zicc startup object and linker configuration')
        final_text, init, loads=expanded_config(original,layout,expanded,evidence,sy,rom_hint,
                                               sram=sram,sram_objects=sram_objects)
        final.append(init)
    else:
        final_text=config(original,layout,sram=sram,sram_objects=sram_objects)
    if expanded or sram_objects:
        final_map=evidence/'link.map'
        final_labels=evidence/'link.labels'
        artifacts = [(('-m','--mapfile'),final_map,'map')]
        if expanded:
            artifacts.append((('-Ln','--label-file'),final_labels,'labels'))
        for options, default, current in artifacts:
            used=next((Path(final[final.index(o)+1]) for o in options if o in final),None)
            if used is None:final.extend([options[0], default])
            elif current=='map':final_map=used
            else:final_labels=used
    final_output = output
    if mapping:
        final_output = evidence/'image.raw'
        final[final.index('-o')+1] = str(final_output)
    final_cfg.write_text(final_text)
    result=run([ld65,*final],evidence/'link.log', rom_hint=rom_hint)
    if expanded or sram_objects:
        final_extents={n:(a,s) for n,(a,s,_) in map_extents(final_map.read_text()).items()}
        cartridge_sram.verify(sram_objects, final_extents)
    if expanded:
        final_symbols=label_values(final_labels)
        wram.verify(expanded,final_extents,final_symbols,loads)
        if final_symbols.get('__zicc_wram_reset') != loads[INIT]:
            raise RuntimeError('final WRAM startup initializer address differs from plan')
        for record in layout['objects']:
            if final_extents.get(record['name']) != (record['address'],record['size']):
                raise RuntimeError(f"final runtime RAM placement differs for {record['name']}")
    if mapping:
        sram.check_manual_header(final_output)
        final_output.replace(output)
    if expanded or sram.capacity:
        manifest=dict(evidence=str(evidence),runtime_ram=layout,sram=dict(sram.manifest(),objects=sram_objects))
        if expanded:
            manifest['application_wram'] = expanded
        output.with_suffix('.allocation.json').write_text(json.dumps(manifest,indent=2)+'\n')
    else:
        output.with_suffix('.allocation.json').unlink(missing_ok=True)
    (evidence/'runtime-ram.json').write_text(json.dumps(layout,indent=2)+'\n')
    sys.stdout.write(result.stdout);sys.stderr.write(result.stderr)


if __name__=='__main__':
    try:
        main()
    except (ValueError, RuntimeError) as error:
        sys.exit(str(error))
