"""Check how much near RAM remains when the runtime uses bank $7F, and interrupt the program while it changes banks."""
import os
import importlib.util
import hashlib
import json
import re
import tempfile
from pathlib import Path
import sys

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'tools'))
from runtime_ram import backfill, LOW, HIGH
from mesen_core import Core, SnesConfig
spec=importlib.util.spec_from_file_location('ram_support',ROOT/'tests/check-compiler.py')
c=importlib.util.module_from_spec(spec);spec.loader.exec_module(c)
OUT=Path(os.environ.get('ZICC_LOGS_DIR', 'logs')).resolve() / 'runtime-ram-check'


def records(*items):
    return [dict(name=n,size=s,alignment=a,members=[dict(source=n,owner='runtime')]) for n,s,a in items]


def allocation_checks():
    assert backfill([])['lower']==HIGH
    full=backfill(records(('full',65536,2)))
    assert full['lower']==LOW and full['used']==65536
    padded=backfill(records(('b',3,4),('a',1,2)))
    assert [r['name'] for r in padded['objects']]==['a','b'] and padded['padding']==4
    hole=backfill(records(('buffer',8,2)),[(HIGH-4,HIGH)])
    assert hole['objects'][0]['address']==HIGH-12
    for values in (records(('individual',65537,1)),records(('a',32768,2),('b',32769,2)),
                   records(('a',65535,2),('b',1,1))):
        try:backfill(values)
        except ValueError as error:assert 'overflow' in str(error) and 'available' in str(error)
        else:raise AssertionError('runtime overflow accepted')
    try:backfill(records(('full',65536,1)),[(LOW,LOW+1)])
    except ValueError:pass
    else:raise AssertionError('reserved extent collision accepted')
    return dict(exact_bank=full,padding=padded,reserved_extent=hole)


def manual_checks():
    # Exported member sizes, not hardcoded linker reservations, drive each
    # supported layout. Include multiple contributing assembly translation units
    base=(ROOT/'tests/link_smoke.s').read_text()
    base=base.replace('.res 2048','.res 4096').replace(':= 2048',':= 4096')
    base+='''
.segment "RUNTIME_CLOCK"
.align 2
clock_start: .res 4
.export __runtime_runtime_clock_size := 4
.segment "RUNTIME_CONSOLE"
.align 2
console_start: .res 8
.export __runtime_runtime_console_size := 8
.segment "RUNTIME_BSS"
.align 2
decimal_start: .res 284
.export __runtime_runtime_bss_size := 284
'''
    asm=OUT/'manual.s';asm.write_text(base)
    c.run([c.CC65/'ca65.exe','--cpu','65816','-g','-o',asm.with_suffix('.o'),asm])
    vectors=OUT/'hirom-vectors.o'
    c.run([c.CC65/'ca65.exe','--cpu','65816','-D','HIROM=1','-o',vectors,ROOT/'runtime/vectors.s'])
    report={}
    for cfg in sorted((ROOT/'linker').glob('*.cfg')):
        label=OUT/(cfg.stem+'.labels')
        c.run([c.CC65/'ld65.exe','-C',cfg,'-o',OUT/(cfg.stem+'.raw'),'-Ln',label,
               asm.with_suffix('.o'),ROOT/'build/rom_header.o',
               vectors if cfg.stem.startswith('hirom') else ROOT/'build/vectors.o'])
        sy={n.removeprefix('_'):int(a,16) for a,n in re.findall(r'^al (\w+) \.(\S+)$',label.read_text(),re.M)}
        assert sy['_RUNTIME_RAM_BOTTOM__']==HIGH-4096-284-4-8
        assert sy['_CONSOLE_MAP_RUN__']==HIGH-4096
        assert sy['_RUNTIME_BSS_RUN__']==HIGH-4096-284
        assert sy['_RUNTIME_CLOCK_RUN__']==HIGH-4096-284-4
        assert sy['_RUNTIME_CONSOLE_RUN__']==HIGH-4096-284-4-8
        assert sy['_NEAR_LAST__']==0x7e0580
        report[cfg.stem]=sy['_RUNTIME_RAM_BOTTOM__']
    with tempfile.TemporaryDirectory(dir=OUT) as temporary:
        folder=Path(temporary)
        raw=folder/'retention.raw'
        ev_root=folder/'retention-runtime-ram'
        custom=ev_root/'saved-baseline'
        for i in range(3):
            c.run([sys.executable,ROOT/'tools/link-runtime-ram.py','-C',ROOT/'linker/lorom32.cfg',
                   '-o',raw,asm.with_suffix('.o'),ROOT/'build/rom_header.o',ROOT/'build/vectors.o'])
            if i==0:
                custom.mkdir()
            runs=sorted(p for p in ev_root.iterdir() if p!=custom)
            assert len(runs)==(1 if i==0 else 2) and custom.is_dir(),(i,runs)
    return report


SOURCE='''#include <stdio.h>
#include <time.h>
#include <stdlib.h>
volatile unsigned nmis;
unsigned char user_buffer[0xfae0];
__interrupt(nmi) void bank_nmi(void){unsigned local[3];local[0]=nmis;local[1]=1;local[2]=local[0]+local[1];nmis=local[2];}
int main(void){void *p;clock_t start=clock();
 printf("%g\\n",1.25);fflush(stdout);
 while(clock()==start){}
 user_buffer[0]=17;user_buffer[0xfadf]=29;
 p=malloc(16);if(!p)return 1;*(unsigned *)p=0x1234;
 if(*(unsigned *)p!=0x1234||user_buffer[0]!=17||user_buffer[0xfadf]!=29)return 2;
 free(p);return nmis==0;
}
'''


def stage_worker(stage,region):
    stem=OUT/f'stage{stage}'
    sy={n.removeprefix('_'):int(a,16) for a,n in re.findall(r'^al (\w+) \.(\S+)$',stem.with_suffix('.labels').read_text(),re.M)}
    manifest=json.loads(stem.with_suffix('.allocation.json').read_text())
    assert manifest['runtime_ram']['payload']==4096+92+804+4
    for name in ('console_map','console_cursor','console_error','clock_frames','ieee64_dec_digits','ieee64_dec_n','ieee64_dec_scale'):
        assert LOW<=sy[name]<HIGH,name
    assert 0x7e0500<=sy['__stdout']<0x7f0000
    assert 0x7effe0<=sy['_NEAR_LAST__']<0x7effee,'runtime state consumed near heap'
    home=OUT/f'stage{stage}-{region}';home.mkdir(exist_ok=True)
    data=stem.with_suffix('.sfc').read_bytes()
    def offset(address):return address-0xc00000
    assert data[offset(sy['clock']):offset(sy['clock'])+6]==bytes.fromhex('8bf47f7fab ab'.replace(' ',''))
    targets=[sy['clock']+i for i in (1,4,5,6)]+[sy['console_putc']+i for i in (1,4,5,6)]
    # Redirect the real foreground instructions to WAI once at each boundary
    # Hardware NMI then interrupts the exact saved bank, partially consumed PEA
    # stack and register state, before resuming the original instruction
    script=f'''local armed=false
local seen={{}}
local waiting=nil
local completed=0
local function redirect(a) local s=emu.getState();s['cpu.k']=a>>16;s['cpu.pc']=a&65535;emu.setState(s) end
local function word(a)return emu.read16(a&0x1ffff,emu.memType.snesWorkRam,false)end
emu.addMemoryCallback(function()armed=true end,emu.callbackType.exec,{sy['main']},{sy['main']})
local targets={{{','.join(map(str,targets))}}}
for _,address in ipairs(targets)do
 emu.addMemoryCallback(function()
  if not armed or seen[address] or waiting then return end
  seen[address]=true
  local s=emu.getState();local scratch={{}}
  for i=0,15 do scratch[i]=word(0x02+i*2)end
  waiting={{state=s,target=address,scratch=scratch,count=word({sy['nmis']})}}
  redirect({sy['bank_pause']})
 end,emu.callbackType.exec,address,address)
end
emu.addMemoryCallback(function()
 assert(waiting,'unarmed pause');local s=emu.getState();local old=waiting.state
 assert(word({sy['nmis']})==waiting.count+1,'one hardware NMI')
 for _,k in ipairs({{'a','x','y','d','dbr','sp','ps'}})do assert(s['cpu.'..k]==old['cpu.'..k],'interrupted '..k)end
 for i=0,15 do assert(word(0x02+i*2)==waiting.scratch[i],'interrupt scratch')end
 local target=waiting.target;waiting=nil;completed=completed+1;redirect(target)
end,emu.callbackType.exec,{sy['bank_resume']},{sy['bank_resume']})
emu.addMemoryCallback(function()
 local s=emu.getState();assert(s['cpu.a']==0 and s['cpu.sp']==0x4ff and s['cpu.dbr']==0x7e and s['cpu.d']==0,'exit ABI')
 assert(completed==#targets and not waiting,'bank-transition coverage '..completed)
 emu.log('PASS runtime bank stage {stage} {region} transitions='..completed);emu.breakExecution()
end,emu.callbackType.exec,{sy['main_exit']},{sy['main_exit']})
'''
    lua=home/'check.lua';lua.write_text(script);core=Core(home)
    try:
        cfg=SnesConfig();cfg.Region=1 if region=='ntsc' else 2;cfg.Port1.Type=1;cfg.DisableFrameSkipping=True;cfg.RamPowerOnState=1;cfg.GsuClockSpeed=100;cfg.BsxCustomDate=-1
        for i in range(8):cfg.ChannelVolumes[i]=100
        core.bind('SetSnesConfig',None,SnesConfig)(cfg)
        core.load(stem.with_suffix('.sfc'),lua,script);core.start();log=core.wait_for('PASS runtime bank',60)
        print(next(x for x in log.splitlines() if x.startswith('PASS ')),flush=True)
    finally:core.close_with_log(home/'check.log')


def main():
    OUT.mkdir(parents=True,exist_ok=True);c.OUT=OUT
    if len(sys.argv)>1:stage_worker(int(sys.argv[1]),sys.argv[2]);return
    report=dict(allocation=allocation_checks(),manual_layouts=manual_checks())
    source=OUT/'driver.c';source.write_text(SOURCE)
    # This non-ABI fixture helper reserves at least three bytes. Install WAI
    # inside its measured extent, retaining the patch and both image hashes
    pause=OUT/'pause.c';pause.write_text('void bank_pause(void){while(1){*(volatile unsigned char * __far)0x7e0400UL=0;}}\n')
    for stage in (1,2,3,4):
        raw=OUT/f'stage{stage}.raw'
        c.run([sys.executable,ROOT/'tools/build-rom.py',source,pause,'--console','--input',ROOT/'samples/input.txt','--stage',str(stage),'-o',raw],timeout=120)
        labels={n.removeprefix('_'):int(a,16) for a,n in re.findall(r'^al (\w+) \.(\S+)$',raw.with_suffix('.labels').read_text(),re.M)}
        data=bytearray(raw.read_bytes());address=labels['bank_pause'];at=address-0xc00000
        manifest=json.loads(raw.with_suffix('.allocation.json').read_text())
        assert any(u['address']==address and u['size']>=3 for u in manifest['units'])
        before=bytes(data[at:at+3]);data[at:at+3]=bytes.fromhex('cb80fd');raw.write_bytes(data)
        manifest['fixture_patch']=dict(address=address,before=before.hex(),after='cb80fd',original_sha256=manifest['sha256'])
        manifest['sha256']=hashlib.sha256(data).hexdigest()
        raw.with_suffix('.allocation.json').write_text(json.dumps(manifest,indent=2)+'\n')
        with raw.with_suffix('.labels').open('a') as f:f.write(f'al {address+1:06X} ._bank_resume\n')
        c.run([ROOT/'build/romtool.exe',raw,raw.with_suffix('.sfc'),ROOT/'tests/title.txt'])
        for region in ('ntsc','pal'):
            report[f'stage{stage}-{region}']=c.run([sys.executable,__file__,str(stage),region],timeout=90).stdout
            print(report[f'stage{stage}-{region}'].strip(),flush=True)
    (OUT/'results.json').write_text(json.dumps(report,indent=2)+'\n')
    print('PASS runtime RAM allocation, all manual layouts, four stages and bank-transition NMIs')


if __name__=='__main__':main()
