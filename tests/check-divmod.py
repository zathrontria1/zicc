"""Check when division and remainder can share work, including when branches or assignments change the inputs."""
import os
import importlib.util
import json
import re
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
OUT = Path(os.environ.get('ZICC_LOGS_DIR', 'logs')).resolve() / 'divmod-check'
spec = importlib.util.spec_from_file_location('checks', ROOT / 'tests/check-strength.py')
checks = importlib.util.module_from_spec(spec)
spec.loader.exec_module(checks)

CASES = {
    'unsigned_pair': '''int main(void){unsigned long a=0xfedcba98UL,b=0x1234UL;
        if(a/b!=0xe0042UL||a%b!=0x930UL)return 1;return 0;}''',
    'signed_pair': '''int main(void){long a=-1234567L,b=97L;
        if(a/b!=-12727L)return 1;if(a%b!=-48L)return 2;return 0;}''',
    'remainder_first': '''int main(void){long a=-1234567L,b=-97L;
        if(a%b!=-48L)return 1;if(a/b!=12727L)return 2;return 0;}''',
    'word_pair': '''int main(void){int a=-32767,b=97,q,r;q=a/b;r=a%b;
        if(q!=-337||r!=-78)return 1;return 0;}''',
    'scratch_clobber': '''int main(void){unsigned long a=1234567UL,b=97UL,q,r,x=123UL;
        q=a/b;x=x*543UL;if(x!=66789UL)return 1;r=a%b;
        return q!=12727UL||r!=48UL;}''',
    'assignment': '''int main(void){unsigned long a=100UL,b=7UL,q,r;
        q=a/b;a=101UL;r=a%b;if(q!=14UL||r!=3UL)return 1;
        q=a/b;b=9UL;r=a%b;return q!=14UL||r!=2UL;}''',
    'compound': '''int main(void){int a=100,b=7,q,r;q=a/b;a+=1;r=a%b;
        if(q!=14||r!=3)return 1;q=a/b;++b;r=a%b;return q!=14||r!=5;}''',
    'compound_after_indirect_store': '''unsigned int output[3];
        int run(unsigned long value,unsigned int divisor,unsigned int index){
            output[index]=(unsigned int)(value%divisor);
            value/=divisor;
            return value!=928327UL||output[index]!=313U;}
        int main(void){unsigned long input=0x12345678UL;return run(input,329U,1U);}''',
    'compound_expression': '''int main(void){long a=-1234567L,b=97L,q,r;
        q=a/b;r=(a%=b);return q!=-12727L||r!=-48L||a!=r;}''',
    'compound_after_alias_write': '''int main(void){long a=100L,b=7L,r;long *p=&a;
        r=a%b;*p=105L;a/=b;return r!=2L||a!=15L;}''',
    'alias': '''int main(void){long a=100L,b=7L,q,r;long *p=&a;
        q=a/b;*p=101L;r=a%b;return q!=14L||r!=3L;}''',
    'array_store': '''int main(void){long a=100L,b=7L,q,r;long *p=&a;
        q=a/b;p[0]=101L;r=a%b;return q!=14L||r!=3L;}''',
    'call': '''long a;void change(void){a=101L;}int main(void){long b=7L,q,r;
        a=100L;q=a/b;change();r=a%b;return q!=14L||r!=3L;}''',
    'recursion': '''int run(int n){long a=100L+n,b=7L,q,r;int child=0;
        q=a/b;if(n)child=run(n-1);r=a%b;
        if(q*b+r!=a)return 1;return child;}
        int main(void){return run(5);}''',
    'branches': '''int run(int flag){long a=101L,b=7L,q=0L,r;
        if(flag)q=a/b;else a=102L;r=a%b;
        if(flag)return q!=14L||r!=3L;return r!=4L;}
        int main(void){return run(0)||run(1);}''',
    'both_arms': '''int run(int flag){long a=101L,b=7L,q,r;
        if(flag)q=a/b;else q=a/b;r=a%b;return q!=14L||r!=3L;}
        int main(void){return run(0)||run(1);}''',
    'short_circuit': '''int run(int flag){long a=101L,b=7L,q=0L,r;
        if(flag&&(q=a/b))a=102L;r=a%b;
        if(flag)return q!=14L||r!=4L;return r!=3L;}
        int main(void){return run(0)||run(1);}''',
    'short_side_effect': '''int run(int flag){long a=101L,b=7L,q,r;
        q=a/b;if(flag||(a=102L)){}r=a%b;
        return q!=14L||(flag?r!=3L:r!=4L);}
        int main(void){return run(0)||run(1);}''',
    'conditional': '''int run(int flag){long a=101L,b=7L,q,r;
        q=flag?a/b:0L;r=a%b;return (flag?q!=14L:q!=0L)||r!=3L;}
        int main(void){return run(0)||run(1);}''',
    'loops': '''int main(void){int i;long a=100L,b=7L,q,r;
        q=a/b;for(i=0;i<5;i++){if(i==2){a++;continue;}q=a/b;r=a%b;
        if(q*b+r!=a)return 1;a++;}r=a%b;if(r!=0L)return 2;
        do{q=a/b;a--;if(a==102L)continue;r=a%b;if(r!=a-q*b&&a!=104L)return 3;}while(a>100L);
        return 0;}''',
    'while_condition': '''int main(void){long a=100L,b=7L,r;int i=0;
        while(a/b==14L){r=a%b;if(r!=2L+i)return 1;a++;i++;}
        return i!=5;}''',
    'typed_operands': '''int main(void){unsigned short a=65535U,b=97U;long q;unsigned long r;
        q=(long)a/(long)b;r=(unsigned long)a%(unsigned long)b;
        return q!=675L||r!=60UL;}''',
}


# Constant locals now propagate and fold, which would remove the divisions
# under test. An out-of-line identity keeps each declared initial value
# unknown at compile time without changing the division expressions
OPAQUE = '#ifdef __ZICC__\n__noinline\n#endif\nunsigned long zicc_opaque(unsigned long v){return v;}\n'
DECLARATION = re.compile(r'\b(?:unsigned |signed )?(?:long|short|int|char)\s[^;(){}]*;')
INITIALIZER = re.compile(r'=\s*(-?(?:0x[0-9a-fA-F]+|\d+)[uUlL]*)(?=\s*[,;])')


def opaque(source):
    body = DECLARATION.sub(lambda m: INITIALIZER.sub(r'=zicc_opaque(\1)', m[0]), source)
    assert 'zicc_opaque(' in body, source
    return OPAQUE + body


def main():
    OUT.mkdir(parents=True, exist_ok=True)
    checks.OUT = OUT
    report = {}
    for name, source in CASES.items():
        source = opaque(source)
        host = OUT / (name + '-host.c')
        host.write_text(source, encoding='ascii')
        exe = host.with_suffix('.exe')
        checks.support.run([ROOT / 'tools/msvc.cmd', '/nologo', '/std:c17', '/O2',
                            '/Fo' + str(host.with_suffix('.obj')), '/Fe' + str(exe), host])
        assert subprocess.run([str(exe)], timeout=5).returncode == 0, name
        pair = {key: checks.build(name + '_' + key, source, True, divmod_reuse=(key == 'on'))
                for key in ('off', 'on')}
        if name in ('unsigned_pair', 'signed_pair', 'remainder_first', 'word_pair', 'scratch_clobber',
                    'compound_after_indirect_store', 'compound_expression', 'both_arms', 'while_condition'):
            assert '; divmod reuse' in pair['on']['assembly'], name
        assert '; divmod ' not in pair['off']['assembly']
        if name in ('alias', 'array_store', 'compound_after_alias_write', 'call', 'recursion', 'branches',
                    'short_circuit', 'short_side_effect', 'conditional', 'typed_operands'):
            assert '; divmod ' not in pair['on']['assembly'], name
        if name in ('unsigned_pair', 'signed_pair', 'remainder_first', 'word_pair'):
            calls = re.findall(r'(?:jsr|jmp) .loword\(__(?:[us]div(?:mod)?(?:8|16|32)|[us]mod(?:8|16|32))\)', pair['on']['assembly'])
            assert len(calls) == 1, (name, calls)
            if name == 'word_pair':
                assert '__sdivmod16' in calls[0], calls
            assert pair['on']['master_clocks'] < pair['off']['master_clocks'], name
        report[name] = {key: {field: value[field] for field in ('master_clocks', 'code_bytes')}
                        for key, value in pair.items()}
        print('PASS ' + name + ' ' + str(report[name]), flush=True)
    source = opaque((ROOT / 'samples/integer_operations.c').read_text())
    pair = {key: checks.build('integer_operations_' + key, source, True, divmod_reuse=(key == 'on'))
            for key in ('off', 'on')}
    assert pair['on']['assembly'].count('; divmod produce') == 2
    assert pair['on']['assembly'].count('; divmod reuse') == 2
    report['integer_operations'] = {key: {field: value[field] for field in ('master_clocks', 'code_bytes')}
                                    for key, value in pair.items()}
    (OUT / 'results.json').write_text(json.dumps(report, indent=2), encoding='utf-8')
    print('PASS integer_operations ' + str(report['integer_operations']), flush=True)


if __name__ == '__main__':
    main()
