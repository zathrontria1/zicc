"""Matched frame trials with explicit compiler provenance and ABI checks in Mesen."""
import argparse
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import random
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'tools'))
from mesen_core import Core

SPEC = importlib.util.spec_from_file_location('support', ROOT / 'tests/check-compiler.py')
support = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(support)

ABI = '''
int word(int a,int b,int c,int d){int x=a+b; c+=d; return x+c;}
unsigned long wide(unsigned long a,int b,int c){unsigned long x=a+b; return x+c;}
float real(float a){float x=a; return x;}
float real_short(float a){return a;}
unsigned long ulong_identity(unsigned long a){return a;}
int pair(int a,int b){if(a<0)return b;return a+b;}
long widen(int a,int b){if(a<0)return (long)b;return (long)a+(long)b;}
int *pointer(int *p,int n){int *q=p; if(n)q=q+1; return q;}
signed char byte(int a){signed char b=a; return b;}
void store(int *p,int a){int b=a+1; *p=b;}
int fib(int n){int l,r;if(n<2)return n;l=fib(n-1);r=fib(n-2);return l+r;}
int down(int n){int saved=n;if(n<0)return n;if(n==0)return 0;return saved+down(n-1);}
int visits;
int initialized(int n){int z=++visits;if(n<2)return n;return z+n;}
int two(int n,int other){int z;if(n<2)return other;z=n+other;return z;}
int main(void){int i,a[2];unsigned long v;
 for(i=0;i<100;i++){
  if(word(i,2,3,4)!=i+9)return 1;
  v=wide(0x1234ffffUL,i,1);if(v!=0x12350000UL+i)return 2;
  real(1.5F);
  real_short(1.5F);
  if(ulong_identity(0x89abcdefUL)!=0x89abcdefUL)return 3;
  if(pair(-1,1234)!=1234||pair(10,1234)!=1244)return 11;
  if(widen(-1,-32768)!=-32768L||widen(32767,2)!=32769L)return 12;
  if(pointer(a,0)!=a||pointer(a,1)!=a+1)return 4;
  if(byte(255)!=-1||byte(128)!=-128||byte(127)!=127)return 5;
  store(a,i);if(a[0]!=i+1)return 6;
 }
 if(fib(10)!=55||fib(-32768)!=-32768)return 7;
 if(down(15)!=120||down(-32768)!=-32768)return 8;
 if(initialized(0)!=0||visits!=1||initialized(2)!=4||visits!=2)return 9;
 if(two(0,1234)!=1234||two(3,1234)!=1237)return 10;
 return 0;}
'''
NAMES = ('function_calls', 'insertion_sort', 'string_processing',
         'integer_operations', 'integer_operations_runtime', 'abi', 'guards', 'forwarding', 'reloads', 'stack_arguments', 'register_arguments', 'entry_cursors', 'bank7e_loops')

RELOADS = '''
int global;
int identity(int n){return n;}
int immediate(int n){return n-1;}
int assign(int n){int a;a=n+1;return a;}
int join(int n){int a=7;if(n){a=8;}return a;}
int loop(int n){int a=7;while(n){a=8;n=0;}return a;}
int clobber(int n){global=n;return n+99;}
int after_call(int n){int a=n;clobber(n);return a;}
int call_result(int n){int a;a=identity(n);return a;}
int byte_value(int n){signed char a=n;return a;}
int boolean(int n){int a;a=n<2;return a;}
int truth(int n){int a;a=n+1;if(a)return 1;return 0;}
int wide_narrow(long n){int a;a=n;return a;}
int cast_product(unsigned char a,unsigned char b){return (signed char)a*b;}
int cast_divide(unsigned char a,unsigned char b){return (signed char)a/b;}
int cast_modulo(unsigned char a,unsigned char b){return (signed char)a%b;}
int cast_both(unsigned char a,unsigned char b){return (signed char)a/(signed char)b;}
int main(void){int n;
 for(n=-100;n<=100;n++){
  if(immediate(n)!=n-1||assign(n)!=n+1)return 1;
  if(join(n)!=(n?8:7)||loop(n)!=(n?8:7))return 2;
  if(after_call(n)!=n||global!=n||call_result(n)!=n)return 3;
  if(boolean(n)!=(n<2)||truth(n)!=(n!=-1))return 4;
 }
 if(byte_value(255)!=-1||byte_value(128)!=-128||byte_value(127)!=127)return 5;
 if(wide_narrow(0x12340000L)!=0||wide_narrow(0x12348000L)!=-32768)return 6;
 if(cast_product(255,2)!=-2||cast_product(128,255)!=-32640||cast_product(127,255)!=32385)return 7;
 if(cast_divide(255,2)!=0||cast_modulo(255,2)!=-1||cast_both(128,255)!=128)return 8;
 return 0;}
'''

FORWARDING = '''
int global;
int *escaped;
int identity(int n){return n;}
unsigned int uidentity(unsigned int n){return n;}
int sum(int n){int left=n+3,right;right=identity(n);return left+right;}
int many(int a,int b,int c,int d){int left=c+d,right;right=identity(a+b);return left+right;}
int swapped(int n){int left=n+3,right;right=identity(n);return right+left;}
int bits_and(int n){int left=n+3,right;right=identity(n);return left&right;}
int bits_or(int n){int left=n+3,right;right=identity(n);return left|right;}
int bits_xor(int n){int left=n+3,right;right=identity(n);return left^right;}
int touch(int *p,int n){*p=n+7;return n+1;}
int changed_other(int n){int left=n,right;right=touch(&left,n);return left+right;}
int hole(int n){int right,left=n+3;right=identity(n);return left+right;}
int zero(void){int right;right=identity(7);return right+3;}
unsigned int usum(unsigned int n){unsigned int left=n+3U,right;right=uidentity(n);return left+right;}
int observed(int n){int left=n+3,right;right=identity(n);global=right;right=identity(n);return left+right;}
int address_taken(int n){int left=n+3,right;escaped=&right;right=identity(n);return left+right;}
int parameter(int n){int left=n+3;n=identity(n);return left+n;}
int global_temp(int n){int left=n+3;global=identity(n);return left+global;}
int difference(int n){int left=n+3,right;right=identity(n);return left-right;}
int twice(int n){int right;right=identity(n);return right+right;}
int byte_temp(void){int left=3;signed char right;right=identity(255);return left+right;}
int effect(int n){global+=1;return n;}
int other_call(int n){int right;right=identity(n);return effect(n)+right;}
int main(void){int n;
 for(n=-100;n<=100;n++){
  if(sum(n)!=2*n+3||swapped(n)!=2*n+3||hole(n)!=2*n+3||many(n,2,3,4)!=n+9)return 1;
  if(bits_and(n)!=((n+3)&n)||bits_or(n)!=((n+3)|n)||bits_xor(n)!=((n+3)^n))return 2;
  if(changed_other(n)!=2*n+8)return 3;
  if(observed(n)!=2*n+3||global!=n||address_taken(n)!=2*n+3)return 4;
  if(parameter(n)!=2*n+3||global_temp(n)!=2*n+3||global!=n)return 5;
  if(difference(n)!=3||twice(n)!=n+n)return 6;
  global=0;if(other_call(n)!=n+n||global!=1)return 7;
 }
 if(zero()!=10||byte_temp()!=2)return 8;
 if(usum(0U)!=3U||usum(32767U)!=1U||usum(32768U)!=3U||usum(65535U)!=1U)return 9;
 return 0;}
'''


def guard_fixture():
    rng = random.Random(65816)
    values = [0, 1, 2, 3, 127, 128, 255, 256, 32766, 32767, 32768, 32769, 65534, 65535]
    values += [rng.randrange(65536) for _ in range(256)]
    source, checks, columns = 'unsigned int input;\n', [], []
    operations = ('<', '<=', '>', '>=', '==', '!=')
    for unsigned in (False, True):
        for index, op in enumerate(operations):
            name = ('u' if unsigned else 's') + str(index)
            t = 'unsigned int' if unsigned else 'int'
            source += f'{t} expected_{name};\n{t} {name}({t} n){{int z;if(n{op}2)return n;z=n^0x1357;return z;}}\n'
            checks.append(f'if({name}(input)!=expected_{name})return {len(checks)+1};')
            column = []
            for value in values:
                n = value if unsigned or value < 32768 else value - 65536
                hit = (n < 2, n <= 2, n > 2, n >= 2, n == 2, n != 2)[index]
                column.append(value if hit else value ^ 0x1357)
            columns.append((name, column))
    source += 'int check(void){' + ''.join(checks) + 'return 0;}\n'
    source += f'int main(void){{int i;for(i=0;i<{len(values)};i++)if(check())return 1;return 0;}}\n'
    return source, values, columns


def worker(args):
    out = args.output.resolve() / args.worker
    out.mkdir(parents=True, exist_ok=True)
    support.OUT = out
    original_run = support.run
    def run(command, **kw):
        command = list(command)
        if Path(command[0]) == ROOT / 'build/zicc.exe':
            # These assertions describe Y-frame layouts; direct-page homes
            # are checked by tests/check-dp-homes.py and stack-relative
            # frames by tests/check-stack-frames.py
            command[0] = args.compiler.resolve();command += ['--no-dp-homes', '--no-stack-frames','--no-inline']
        return original_run(command, **kw)
    support.run = run
    if args.worker == 'guards':
        source, guard_values, guard_columns = guard_fixture()
    else:
        fixtures = dict(abi=ABI, forwarding=FORWARDING, reloads=RELOADS,
                        stack_arguments=(ROOT/'tests/stack_argument_cases.c').read_text(),
                        register_arguments=(ROOT/'tests/register_argument_cases.c').read_text(),
                        entry_cursors=(ROOT/'tests/entry_cursor_cases.c').read_text(),
                        bank7e_loops=(ROOT/'tests/bank7e_loop_cases.c').read_text())
        source = fixtures[args.worker] if args.worker in fixtures else (ROOT / 'samples' / (args.worker + '.c')).read_text()
    workspace = out / 'workspace.s'
    workspace.write_text('.exportzp __arith_lhs,__arith_rhs\n.segment "DP_SCRATCH": zeropage\n'
                         '__arith_lhs: .res 4\n__arith_rhs: .res 28\n')
    run([support.CC65 / 'ca65.exe', '-o', out / 'workspace.o', workspace])
    extra = [out / 'workspace.o', args.runtime_object.resolve()]
    if args.worker == 'stack_arguments':
        extra = [ROOT/'build/arithmetic.o',ROOT/'build/ieee_engine.o',ROOT/'build/tables.o',args.runtime_object.resolve()]
    if args.worker == 'integer_operations_runtime':
        run([args.compiler, ROOT / 'samples/integer_kernels.c', '-o', out / 'kernels.s'])
        run([support.CC65 / 'ca65.exe', '--cpu', '65816', '-g', '-o', out / 'kernels.o', out / 'kernels.s'])
        extra.insert(-1, out / 'kernels.o')
    _, rom, labels = support.compile_case(args.worker, source, extra_objects=extra)
    if args.worker in ('stack_arguments','register_arguments','entry_cursors','bank7e_loops'):
        host=out/'reference.exe'
        run([ROOT/'tools/msvc.cmd','/nologo','/std:c17','/O2',
             '/Fo'+str(out/'reference.obj'),'/Fe'+str(host),out/(args.worker+'.c')])
        run([host])
    main, end = labels['main'], labels['main_exit']
    assembly = (out / (args.worker + '.s')).read_text()
    if args.worker=='bank7e_loops':
        assert 0x7e6000<=labels['high']<=0x7effff,labels['high']
        if args.expect_small_frames:
            def body(name):return assembly.split('_'+name+':',1)[1].split('__size_'+name,1)[0]
            for name in ('bank7e_row','bank7e_nested','bank7e_byte','bank7e_wide'):
                assert '; entry-only cursor leaf: no frame' in body(name),name
                assert 'sta a:' in body(name) and 'sta z:$' not in body(name),name
            for name in ('far_matrix','switch_loops'):
                assert '; entry-only cursor leaf' not in body(name),name
            assert '; eliminated induction home' not in body('switch_loops')
            assert 'lda f:_rom+' in body('named_far_scaled')
    if args.worker=='entry_cursors' and args.expect_small_frames:
        def body(name):return assembly.split('_'+name+':',1)[1].split('__size_'+name,1)[0]
        for name in ('row_fill','column_fill','nonzero_start','negative_start_leaf','negative_coefficient',
                     'doubled_row','small_stride','literal_value','stack_offset','unsigned_value',
                     'unsigned_start_leaf','constant_address','base_address','byte_copy','wide_copy','register_value','byte_register','wide_literal','visible_index','visible_unsigned','visible_negative','nested_byte','nested_wide','nested_negative'):
            text=body(name)
            assert '; entry-only cursor leaf: no frame' in text,name
            assert not re.search(r'^\s+(?:ph[axy]|pl[axy]|t[sc][cs]|tay|tya)\b',text,re.M),name
            assert ',y' not in text,name
        for name in ('costly_scale','narrow_row','global_reload','extra_statement','nested_large'):
            assert '; entry-only cursor leaf:' not in body(name),name
        for name,value in (('visible_index','0003'),('visible_unsigned','FFFF'),('visible_negative','0001')):
            assert 'visible final index: constant recovery' in body(name) and 'lda #$'+value+'\n    rts' in body(name),name
        assert re.findall(r'^    [^;].*',body('empty_leaf'),re.M)==['    rts']
        assert re.findall(r'^    [^;].*',body('nested_empty'),re.M)==['    rts']
        assert re.findall(r'^    [^;].*',body('visible_empty'),re.M)==['    lda #$0005','    rts']
        assert '    lda 7,s\n' in body('stack_offset')
        assert 'sep #$20\n.a8' in body('byte_copy') and 'rep #$20\n.a16' in body('byte_copy')
        assert body('wide_copy').count('sta a:')==6
        assert 'sta z:__arith_lhs' in body('register_value')
        for name in ('staged_row','extra_statement'):
            assert '; strength cursor' not in body(name),name
        for name in ('staged_subtract','staged_scale'):
            assert '; direct pointer scale: no stack staging' in body(name),name
            region=body(name).split('; direct pointer scale: no stack staging',1)[1]
            assert '    pha\n' not in region and '    pla\n' not in region,name
        assert body('global_reload').count('lda a:.loword(_global_value)')==3
    if args.worker == 'register_arguments' and args.expect_small_frames:
        def body(name):
            return assembly.split('_'+name+':',1)[1].split('__size_'+name,1)[0]
        masks={'unused_both':(0,0),'unused_x':(2,2),'unused_a':(1,1),
               'unused_with_stack':(0,0),'unused_wide_return':(2,2),
               'overwrite_both':(3,0),'overwrite_x':(3,2),'overwrite_a':(3,1),
               'call_before_write':(3,1),'overwrite_byte':(1,0),'overwrite_pointer':(3,2),'cursor_setup':(3,1),'escape_after_write':(3,1),
               'branch_both':(3,1),'branch_return':(3,1),'for_initializer':(3,1),
               'do_write':(3,1),'branch_escape':(3,1),'do_escape':(3,1),'for_escape':(3,1),'cursor_late':(3,1)}
        for name,(homes,spills) in masks.items():
            assert f'; register entry: homes ${homes:02X}, spills ${spills:02X}' in body(name),name
        assert '; strength cursor' in body('cursor_late') and '; cursor entry deferred to defining write' in body('cursor_late')
        assert not body('unused_both').split(';',1)[0].strip()
        assert body('unused_with_stack').split(';',1)[0]=='\n    phy\n    tsc\n    tay\n'
        # A private copy can share the immutable parameter's surviving home
        # Both layouts must preserve the value across bump(), checked below
        # by target execution and the ordinary callee ABI assertions
        assert body('unused_x').split(';',1)[0] in ('\n    phy\n    pha\n    pha\n    tsc\n    tay\n',
                                                       '\n    phy\n    pha\n    tsc\n    tay\n')
        assert body('unused_a').split(';',1)[0] in ('\n    phy\n    pha\n    phx\n    tsc\n    tay\n',
                                                       '\n    phy\n    phx\n    tsc\n    tay\n')
        for name in ('escaped_then_write','branch_write','rhs_read','while_write','do_break','do_continue','branch_escape_early','condition_read'):
            assert '; register entry:' not in body(name),name+' lost a conservative entry value'
        for name in ('overwrite_both','overwrite_a','call_before_write'):
            assert 'sta z:__arith_rhs' not in body(name).split(';',1)[0],name
        for name in ('overwrite_both','overwrite_x','overwrite_pointer'):
            assert 'sta a:$0001,y' not in body(name).split(';',1)[0],name
    if args.worker == 'stack_arguments' and args.expect_small_frames:
        def body(name):
            return assembly.split('_'+name+':',1)[1].split('__size_'+name,1)[0]
        for name in ('stack_only','stack_only_word','stack_only_void','stack_only_float'):
            text=body(name)
            assert text.split(';',1)[0]=='\n    phy\n    tsc\n    tay\n',text
            assert '    ply\n    rts\n' in text and '    tcs\n' not in text,text
        for name,push in (('wide_then_word','pha'),('word_then_wide','phx'),('recursive_stack','pha')):
            assert body(name).split(';',1)[0]=='\n    phy\n    '+push+'\n    tsc\n    tay\n',name
        for name,push in (('wide_word_local','pha'),('word_wide_local','phx'),('two_words','phx'),('mixed_eight','phx')):
            assert body(name).split(';',1)[0]=='\n    phy\n    pha\n    '+push+'\n    tsc\n    tay\n',name
    if args.worker == 'function_calls' and args.expect_small_frames:
        text = assembly.split('_factorial:', 1)[1].split('__size_factorial', 1)[0]
        assert '    phy\n    phx\n    tsc\n    tay\n' in text, text
        assert text.count('lda a:$0001,y') == 1, text
        assert '    plx\n    ply\n    rts' in text, text
    if args.worker == 'reloads' and args.expect_reloads:
        def body(name):
            return assembly.split('_' + name + ':', 1)[1].split('__size_' + name, 1)[0]
        assert 'lda a:$0001,y' not in body('immediate'), body('immediate')
        assert 'lda a:$0003,y' not in body('assign'), body('assign')
        for name in ('join','loop'):
            assert 'lda a:$0003,y' in body(name), body(name)
        # The result remains in A; its private store may be dead. A retained
        # reload must use that same home before the return
        assert re.search(r'(?:jsr|jmp) \.loword\(_identity\)\s+(?:sta a:\$0003,y\s+(?:lda a:\$0003,y\s+)?)?(?:;[^\n]*\s+)*return_call_result',
                         body('call_result')),body('call_result')
        # The copy in after_call may disappear, but clobber() still invalidates
        # A. Require an actual reload/restore afterward, from the copy, input home, or stack save
        assert re.search(r'jsr \.loword\(_clobber\).*?(?:lda a:\$(?:0001|0003),y|plx(?:\s*;[^\n]*)?\s+txa)',
                         body('after_call'),re.S),body('after_call')
        assert 'and #$00FF' in body('byte_value'), body('byte_value')
    if args.worker == 'forwarding' and args.expect_forwarding:
        def body(name):
            return assembly.split('_' + name + ':', 1)[1].split('__size_' + name, 1)[0]
        for name, instruction in (('sum','adc'),('swapped','adc'),('bits_and','and'),('bits_or','ora'),('bits_xor','eor')):
            text = body(name)
            assert re.search(r'jsr \.loword\(_identity\)\s+(?:clc\s+)?' + instruction + r' a:\$0003,y', text), text
            if args.expect_small_frames:
                assert '    phy\n    pha\n    phx\n    tsc\n    tay\n' in text, text
                assert '    plx\n    plx\n    ply\n    rts' in text, text
            else:
                assert 'sbc #$0004' in text, text
            assert 'sta a:$0005,y' not in text, text
        assert 'tcs' not in body('zero'), body('zero')
        assert 'sbc #$0006' in body('hole') and 'adc a:$0005,y' in body('hole'), body('hole')
        for name in ('observed','address_taken','difference'):
            assert 'sta a:$0005,y' in body(name), body(name)
        assert 'sta a:$0003,y' in body('twice'), body('twice')
    functions = re.findall(r'^\.export _(\w+)$', assembly, re.M)
    script = '''local start=0
local expected_sp=0
local frames={}
local targets={}
local calls=0
local lowest=65535
local instruction_lowest=65535
local function entry(is_main,name)
 local s=emu.getState()
 assert(s['cpu.dbr']==0x7e,'C entry DBR')
 local sp=s['cpu.sp']
 lowest=math.min(lowest,sp)
 local ret=emu.read16(((sp+1)&0x1ffff),emu.memType.snesWorkRam,false)
 local bank=is_main and emu.read(((sp+3)&0x1ffff),emu.memType.snesWorkRam,false) or s['cpu.k']
 local target=(bank<<16)|((ret+1)&65535)
 frames[#frames+1]={target=target,sp=sp+(is_main and 3 or 2),y=s['cpu.y'],d=s['cpu.d'],dbr=s['cpu.dbr'],name=name}
 calls=calls+1
 if not targets[target] then
  targets[target]=true
  emu.addMemoryCallback(function()
   local f=frames[#frames]
   if not f or f.target~=target then error('return order') end
   local s=emu.getState()
   if s['cpu.sp']~=f.sp or s['cpu.y']~=f.y or s['cpu.d']~=f.d or s['cpu.dbr']~=f.dbr then error('ABI preservation') end
   if (f.name=='real' or f.name=='real_short') and (s['cpu.a']~=0 or s['cpu.x']~=0x3fc0) then error('float return') end
   frames[#frames]=nil
  end,emu.callbackType.exec,target,target)
 end
end
'''
    for fn in functions:
        script += f'emu.addMemoryCallback(function() entry({str(fn == "main").lower()},"{fn}") end,emu.callbackType.exec,{labels[fn]},{labels[fn]})\n'
    if args.worker in ('stack_arguments','register_arguments','entry_cursors','bank7e_loops'):
        script += '''emu.addMemoryCallback(function()
 if #frames>0 then instruction_lowest=math.min(instruction_lowest,emu.getState()['cpu.sp']) end
end,emu.callbackType.exec,0x808000,0x80ffbf)
'''
    if args.worker == 'guards':
        assembly_guards = assembly.count('; entry guard before frame allocation')
        # The signed != case can also compare the incoming X directly and
        # return a literal on its known n==2 fallthrough without any frame
        signed_ne=assembly.split('\n_s5:\n',1)[1].split('__size_s5',1)[0]
        frameless=(
            '; scalar leaf without Y frame' in signed_ne and
            re.search(r'^    cpx #\$0002\n    beq ',signed_ne,re.M) and
            '    txa\n    rts' in signed_ne and '    lda #$1355\n    rts' in signed_ne and
            not re.search(r'^    (?:ph[axy]|tsc|tcs)\b',signed_ne,re.M)
        )
        covered=assembly_guards+int(bool(frameless))
        assert assembly_guards==0 or covered==12,covered
        if args.expect_guards:
            assert covered==12,covered
    if args.worker == 'abi' and args.expect_guards:
        for fn in ('initialized', 'two'):
            body = assembly.split('_' + fn + ':', 1)[1].split('__size_' + fn, 1)[0]
            assert '; entry guard' not in body, fn
    if args.worker == 'guards':
        rows = []
        for i, value in enumerate(guard_values):
            rows.append('{' + ','.join(map(str, [value] + [column[i] for _, column in guard_columns])) + '}')
        script += 'local cases={' + ','.join(rows) + '}\nlocal case_index=0\n'
        script += 'local function word(p,v) emu.write(((p)&0x1ffff),v&255,emu.memType.snesWorkRam);emu.write(((p+1)&0x1ffff),(v>>8)&255,emu.memType.snesWorkRam) end\n'
        script += 'emu.addMemoryCallback(function() case_index=case_index+1;local c=cases[case_index]\n'
        script += f'word({labels["input"]},c[1])\n'
        for index, (name, _) in enumerate(guard_columns, 2):
            script += f'word({labels["expected_"+name]},c[{index}])\n'
        script += f'end,emu.callbackType.exec,{labels["check"]},{labels["check"]})\n'
    script += f'''
emu.addMemoryCallback(function()
 local s=emu.getState();start=s.masterClock;expected_sp=s['cpu.sp']+3
end,emu.callbackType.exec,{main},{main})
emu.addMemoryCallback(function()
 local s=emu.getState()
 if s['cpu.a']~=0 or s['cpu.sp']~=expected_sp then error('result/stack '..s['cpu.a']) end
 emu.log('RESULT '..(s.masterClock-start)..' '..calls..' '..lowest)
 emu.log('MIN_SP '..instruction_lowest)
 emu.log('DONE');emu.breakExecution()
end,emu.callbackType.exec,{end},{end})
'''
    scriptfile = out / 'measure.lua'
    scriptfile.write_text(script)
    core = Core(out / 'home')
    try:
        core.load(rom, scriptfile, script)
        core.start()
        log = core.wait_for('DONE', 45)
        clocks, calls, lowest = map(int, re.search(r'RESULT (\d+) (\d+) (\d+)', log).groups())
        # CODE size excludes startup, runtime objects and ROM padding
        segments = run([support.CC65 / 'od65.exe', '--dump-segments', out / (args.worker + '.o')]).stdout
        code_bytes = int(re.search(r'Name:\s+"CODE".*?Size:\s+(\d+)', segments, re.S)[1])
        if args.worker == 'integer_operations_runtime':
            segments = run([support.CC65 / 'od65.exe', '--dump-segments', out / 'kernels.o']).stdout
            code_bytes += int(re.search(r'Name:\s+"CODE".*?Size:\s+(\d+)', segments, re.S)[1])
        result = dict(run_id=os.environ.get('ZICC_VERIFICATION_RUN_ID'),master_clocks=clocks, calls=calls, lowest_entry_sp=lowest,
                      lowest_instruction_sp=int(re.search(r'MIN_SP (\d+)',log)[1]),
                      application_code_bytes=code_bytes, return_value=0,
                      compiler=str(args.compiler.resolve()),
                      compiler_sha256=hashlib.sha256(args.compiler.read_bytes()).hexdigest(),
                      runtime_sha256=hashlib.sha256(args.runtime_object.read_bytes()).hexdigest(),
                      source_sha256=hashlib.sha256(source.encode()).hexdigest(),
                      rom_sha256=hashlib.sha256(rom.read_bytes()).hexdigest(), emulator=core.version)
        (out / 'result.json').write_text(json.dumps(result, indent=2) + '\n')
        print(args.worker, clocks, code_bytes, flush=True)
    finally:
        core.close_with_log(out / 'measure.log')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--compiler', type=Path, required=True)
    parser.add_argument('--runtime-object', type=Path, default=ROOT / 'build/integers.o')
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--worker', choices=NAMES)
    parser.add_argument('--list-parts',action='store_true')
    parser.add_argument('--collect',action='store_true')
    parser.add_argument('--expect-guards', action='store_true')
    parser.add_argument('--expect-forwarding', action='store_true')
    parser.add_argument('--expect-reloads', action='store_true')
    parser.add_argument('--expect-small-frames', action='store_true')
    args = parser.parse_args()
    if args.list_parts:
        print(json.dumps(list(NAMES)));return
    if args.collect:
        results={name:json.loads((args.output/name/'result.json').read_text()) for name in NAMES}
        for row in results.values():
            assert row['run_id']==os.environ.get('ZICC_VERIFICATION_RUN_ID'),'stale frame worker'
            assert row['compiler_sha256']==hashlib.sha256(args.compiler.read_bytes()).hexdigest()
            assert row['runtime_sha256']==hashlib.sha256(args.runtime_object.read_bytes()).hexdigest()
        (args.output/'results.json').write_text(json.dumps(results,indent=2)+'\n');return
    if args.worker:
        worker(args)
    else:
        results = {}
        for name in NAMES:
            command = [sys.executable, __file__, '--compiler', str(args.compiler),
                       '--runtime-object', str(args.runtime_object), '--output', str(args.output), '--worker', name]
            if args.expect_guards:
                command.append('--expect-guards')
            if args.expect_forwarding:
                command.append('--expect-forwarding')
            if args.expect_reloads:
                command.append('--expect-reloads')
            if args.expect_small_frames:
                command.append('--expect-small-frames')
            subprocess.run(command, check=True)
            results[name] = json.loads((args.output / name / 'result.json').read_text())
        (args.output / 'results.json').write_text(json.dumps(results, indent=2) + '\n')


if __name__ == '__main__':
    main()
