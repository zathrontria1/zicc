"""List the C functions, variables and assembly entry points that the debugger can show. Skip constants."""
import argparse
import json
from pathlib import Path
import re


def collect(labels):
    labels = Path(labels)
    debug = labels.with_suffix('.dbg').read_text()
    names = {}
    source_names = {}
    called = set()
    def assembly_name(name):
        return name if name.startswith('__') else name.removeprefix('_')
    for filename in re.findall(r'^file\s+[^\n]*?name="([^"]+)"', debug, re.M):
        source = Path(filename)
        if not source.is_absolute():
            source = Path.cwd() / source
        text = source.read_text(errors='replace')
        if '; ABI: near7e-far24pad32' in text:
            source_names.update(re.findall(r'^; debug symbol (\S+) (\S+)$', text, re.M))
        else:
            # Only explicit label definitions are entries. ca65 can report
            # address aliases created with := as type=lab too
            definitions = set(re.findall(r'^\s*(\w+):(?!=)', text, re.M))
            procedures = set(re.findall(r'^\s*\.proc\s+(\w+)', text, re.M))
            definitions.update(procedures)
            targets = set(re.findall(r'^\s*js[rl]\s+(?:\.loword\(\s*)?([A-Za-z_]\w*)', text, re.M | re.I))
            called.update(targets)
            for name in procedures | targets:
                names[name] = assembly_name(name)
            for exports in re.findall(r'^\.export(?:zp)?\s+([^;\n]+)', text, re.M):
                for name in exports.split(','):
                    name = name.strip().split()[0]
                    if name in definitions:
                        names[name] = assembly_name(name)
    # A C declaration knows whether underscores belong to the source name;
    # calls from assembly must not override it with ABI spelling
    names.update(source_names)
    addresses = {}
    # Read resolved symbols directly: RAM code entry equates are absent from
    # ld65's label file. Only explicit call targets can opt into equates
    for row in re.findall(r'^sym\s+(.+)$', debug, re.M):
        fields = dict(re.findall(r'(\w+)=("[^"]*"|[^,\s]+)', row))
        raw = fields['name'].strip('"')
        if raw not in names or 'val' not in fields or 'seg' not in fields:
            continue
        if fields.get('type') != 'lab' and not (raw in called and fields.get('type') == 'equ'):
            continue
        name, value = names[raw], int(fields['val'], 16)
        if name in addresses and addresses[name] != value:
            raise ValueError(f'Conflicting symbol {name}')
        addresses[name] = value
    if not addresses:
        raise ValueError('No function or variable debug symbols found; rebuild with current zicc')
    return addresses


def write(labels, output):
    labels, output = Path(labels), Path(output)
    symbols = collect(labels)
    ordered = sorted(symbols.items(), key=lambda item: (item[1], item[0]))
    output.write_text(''.join(f'{value:06x} {name}\n' for name, value in ordered), encoding='ascii')
    manifest = labels.with_suffix('.allocation.json')
    mapping = json.loads(manifest.read_text()).get('mapping') if manifest.exists() else None
    hirom = mapping in {'hirom', 'exhirom'}
    rows = []
    for name, value in ordered:
        if hirom and 0xc00000 <= value <= 0xffffff:
            kind, offset = 'SnesPrgRom', value - 0xc00000
        elif mapping == 'exhirom' and 0x400000 <= value < 0x7e0000:
            kind, offset = 'SnesPrgRom', value
        elif mapping == 'exhirom' and value < 0x400000 and value & 0xffff >= 0x8000:
            kind, offset = 'SnesPrgRom', value + 0x400000
        elif 0x808000 <= value <= 0xffffff and value & 0xffff >= 0x8000:
            kind = 'SnesPrgRom'
            offset = ((value & 0x3f0000) + (value & 0xffff) if hirom else
                      ((value >> 16) & 0x7f) * 0x8000 + (value & 0x7fff))
        elif 0x7e0000 <= value <= 0x7fffff:
            kind, offset = 'SnesWorkRam', value & 0x1ffff
        elif value < 0x2000:
            kind, offset = 'SnesWorkRam', value
        else:
            continue
        rows.append(f'{kind}:{offset:06x}:{name}\n')
    output.with_suffix('.mlb').write_text(''.join(rows), encoding='ascii')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('labels', type=Path)
    parser.add_argument('output', type=Path)
    args = parser.parse_args()
    write(args.labels, args.output)
