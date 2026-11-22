"""Preprocessor semantics and diagnostics, independent of target code generation."""
import os
import json
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[1]
OUT = Path(os.environ.get('ZICC_LOGS_DIR', 'logs')).resolve() / 'preprocessor-check'


def run(command):
    return subprocess.run(list(map(str, command)), cwd=ROOT, capture_output=True,
                          text=True, timeout=30, creationflags=subprocess.CREATE_NO_WINDOW)


def body(text):
    text = re.sub(r'^\s*#line[^\n]*', '', text, flags=re.M)
    return re.findall(r'''"(?:\\.|[^"\\])*"|'(?:\\.|[^'\\])*'|[A-Za-z_]\w*|[0-9]+|<<=|>>=|->|&&|\|\||<<|>>|<=|>=|==|!=|\S''', text)


def build_driver(output):
    output.mkdir(parents=True, exist_ok=True)
    driver = output / 'preprocess.exe'
    built = run([ROOT / 'tools/msvc.cmd', '/nologo', '/std:c17', '/W4', '/WX', '/O2',
                 '/D_CRT_SECURE_NO_WARNINGS', '/Fo' + str(output) + '/', '/Fe' + str(driver),
                 ROOT / 'tests/preprocess-driver.c', ROOT / 'src/preprocess.c'])
    assert built.returncode == 0, built.stdout + built.stderr
    return driver


def main():
    driver = build_driver(OUT)
    params = ','.join(f'p{i}' for i in range(127))
    args = ','.join(['0'] * 126 + ['TAIL'])
    cases = {
        'disabled_nested': ('#if 0\n#define HIDDEN 1\n#if 1/0\nwrong\n#endif\n'
                            '#else\nright\n#endif\n#ifdef HIDDEN\nwrong\n#endif\n', 'right'),
        'elif_chain': ('#define N 7\n#if N == 6\nwrong\n#elif N == 7\nright\n'
                       '#elif 1/0\nwrong\n#else\nwrong\n#endif\n', 'right'),
        'defined': ('#define FLAG\n#define ALIAS FLAG\n#if defined FLAG && defined(FLAG) && '
                    '!defined(MISSING) && defined(ALIAS) && !MISSING\nright\n#endif\n', 'right'),
        'undef': ('#define N 1\n#undef N\n#if N\nwrong\n#elif !defined N\nright\n#endif\n', 'right'),
        'operators': ('#if 2+3*4 == 14 && (17/3 == 5) && 17%3 == 2 && '
                      '((1<<4)|3) == 19 && ((31>>2)^2) == 5 && (7&3) == 3 && '
                      '~0 == -1 && 4>=4 && 3<=4 && 4>3 && 2!=3 && +2 == 2\nright\n#endif\n', 'right'),
        'short_circuit': ('#if (0 && 1/0) || (1 || 1/0)\nright\n#endif\n'
                          '#if (1 ? 7 : 1/0) == 7 && (0 ? 1/0 : 8) == 8\nalso\n#endif\n', 'right also'),
        'signed_unsigned': ('#if -7/3 == -2 && -7%3 == -1 && -2 < -1 && '
                            '-1 > 1U && '
                            '0xffffffffffffffffULL == ~0U && (-4>>1) == -2\nright\n#endif\n', 'right'),
        'constants': ("#if 010 == 8 && 0x20UL == 32 && 'A' == 65 && '\\n' == 10 && "
                      "'\\x41' == 65 && '\\101' == 65 && '\\\\' == 92\nright\n#endif\n", 'right'),
        'function': ('#define ADD(a,b) ((a)+(b))\nADD(1, ADD(2,3))\n', '( ( 1 ) + ( ( ( 2 ) + ( 3 ) ) ) )'),
        'structassign': ('#define structassign(d,s) d = s\nstructassign(*p->next, *global);\n',
                         '* p -> next = * global ;'),
        'nested_commas': ('#define PAIR(a,b) a + b\nPAIR(call(1,2), (3,4))\n',
                          'call ( 1 , 2 ) + ( 3 , 4 )'),
        'empty_arguments': ('#define NOTHING()\n#define KEEP(a,b) a b\n'
                            'KEEP(,7) KEEP(8,) KEEP(,) NOTHING() tail\n', '7 8 tail'),
        'alias_rescan': ('#define F(x) ((x)+1)\n#define A F\n#define APPLY(f) f\n'
                         'A(2) APPLY(F)(3)\n', '( ( 2 ) + 1 ) ( ( 3 ) + 1 )'),
        'recursion': ('#define SELF SELF\n#define A B\n#define B A\n#define F(x) F(x)\n'
                      'SELF A F(F(1))\n', 'SELF A F ( F ( 1 ) )'),
        'not_invoked': ('#define F(x) x\nF + 1\n', 'F + 1'),
        'quoted': ('#define NAME expanded\n#define ID(x) x\nID("NAME,(x)") ID(\'N\') NAME\n',
                   '"NAME,(x)" \'N\' expanded'),
        'comments': ('/* prefix */ #define F(x) x/* separator */+1\n'
                     '#if 0\n/*\n#endif\n*/\n#else\nF/* gap */(2)\n#endif\n', '2 + 1'),
        'multiline': ('#define ADD(a,b) ((a)+\\\n(b))\nADD\n(1,\n2)\n', '( ( 1 ) + ( 2 ) )'),
        'object_parenthesis': ('#define N (7)\n#define F/**/(x) x\nN F\n', '( 7 ) ( x ) x'),
        'header': ('#include "fixture.h"\n#if HEADER == 42\nINC(HEADER)\n#endif\n', '( 42 + 1 )'),
        'macro_header': ('#define PICK(x) x\n#define HEADER_PATH PICK("fixture.h")\n#include HEADER_PATH\nINC(HEADER)\n', '( 42 + 1 )'),
        'line_directive': ('#define LINE_NUMBER 75\n#line LINE_NUMBER "logical.c"\n'
                           '__LINE__ __FILE__\n#include "fixture.h"\n'
                           '#line 100\n__LINE__ __FILE__ HEADER\n',
                           '75 "logical.c" 100 "logical.c" 42'),
        'stringify': ('#define S(x) #x\n#define S2(x) S(x)\n#define WORD expanded\n'
                      '#define BEFORE(x) S(a x)\n#define BESIDE(x) S(a+x)\n'
                      'S(  WORD/**/+ 1  ) S2(WORD) S() S("x") BEFORE(b) BESIDE( WORD)\n',
                      r'"WORD + 1" "expanded" "" "\"x\"" "a b" "a+expanded"'),
        'redefinition': ('#define F(x) x\n#undef F\n#define F 3\nF\n', '3'),
        'null_directive': ('#\nright\n', 'right'),
        'ternary_unsigned': ('#if !((1 ? -1 : 0U) < 0)\nright\n#endif\n', 'right'),
        'token_boundaries': ('#define X +\n#define Y -\nX+1 Y-1\n', '+ + 1 - - 1'),
        'paste': ('#define CAT(a,b) a##b\n#define NUM 7\n#define xy 42\n'
                  'CAT(x,y) CAT(,tail) CAT(head,) CAT(,) CAT(12,UL) CAT(NUM,U)\n',
                  '42 tail head 12UL NUMU'),
        'many_macros': (''.join('#define M%d %d\n'%(i,i) for i in range(300))+
                        '#define ADD(x) M299+x\nADD(1)\n', '299 + 1'),
        'wide_macro': (f'#define TAIL 42\n#define tagTAIL 9\n'
                       f'#define WIDE({params}) p126 p126 #p126 tag##p126\nWIDE({args})\n'
                       '#undef WIDE\n#define WIDE(x) x\nWIDE(17)\n',
                       '42 42 "TAIL" 9 17'),
    }
    (OUT / 'fixture.h').write_text('#ifndef FIXTURE_H\n#define FIXTURE_H\n#define HEADER 42\n'
                                      '#define INC(x) (x+1)\n#endif\n')
    results = {}
    for name, (source, expected) in cases.items():
        path = OUT / (name + '.c'); path.write_text(source)
        result = run([driver, path, ROOT / 'include'])
        assert result.returncode == 0, (name, result.stderr)
        assert body(result.stdout) == body(expected), (name, result.stdout, expected)
        results[name] = 'PASS'
    # Compare all successful fixtures with MSVC's conforming preprocessor in one
    # invocation, avoiding repeated MSVC environment initialization per fixture
    names = sorted(set(re.findall(r'^#(?:define|ifndef)\s+(\w+)',
                                 '\n'.join(s for s, _ in cases.values()) +
                                 '\n' + (OUT / 'fixture.h').read_text(), re.M)))
    reset = ''.join('#undef ' + name + '\n' for name in names)
    reference_source = OUT / 'reference.c'
    # The installed MSVC preprocessor keeps the selected signed arm's type in
    # this mixed-type ?: case. Test our unsigned conversion independently
    reference_cases = {n: c for n, c in cases.items() if n != 'ternary_unsigned'}
    reference_source.write_text(''.join(reset + name + '\n' + source + '\n'
                                        for name, (source, _) in reference_cases.items()))
    reference = run([ROOT / 'tools/msvc.cmd', '/nologo', '/std:c17', '/Zc:preprocessor',
                     '/EP', '/TC', reference_source])
    assert reference.returncode == 0, reference.stderr
    expected = ' '.join(name + ' ' + text for name, (_, text) in reference_cases.items())
    assert body(reference.stdout) == body(expected), reference.stdout
    results['msvc_reference'] = 'PASS'
    failures = {
        'unmatched_elif': ('#elif 1\n', 'unmatched #elif'),
        'elif_after_else': ('#if 0\n#else\n#elif 1\n#endif\n', '#elif after #else'),
        'duplicate_else': ('#if 0\n#else\n#else\n#endif\n', 'duplicate #else'),
        'unmatched_endif': ('#endif\n', 'unmatched #endif'),
        'unterminated_if': ('#if 1\n', 'unterminated conditional'),
        'missing_expression': ('#if\n#endif\n', 'expected operand'),
        'bad_expression': ('#if 1 +\n#endif\n', 'expected operand'),
        'extra_expression': ('#if 1 2\n#endif\n', 'unexpected token'),
        'bad_defined': ('#if defined(42)\n#endif\n', 'expected identifier'),
        'bad_number': ('#if 09\n#endif\n', 'invalid integer'),
        'bad_float': ('#if 1.0\n#endif\n', 'invalid integer'),
        'overflow': ('#if 18446744073709551616U\n#endif\n', 'exceeds 64 bits'),
        'zero_divisor': ('#if 1/0\n#endif\n', 'division by zero'),
        'bad_shift': ('#if 1<<64\n#endif\n', 'invalid shift'),
        'bad_ternary': ('#if 1 ? 2\n#endif\n', "expected ':'"),
        'extra_argument': ('#define F(x) x\nF(1,2)\n', 'wrong number'),
        'missing_argument': ('#define F(x,y) x\nF(1)\n', 'wrong number'),
        'zero_arguments': ('#define F() 1\nF(,)\n', 'wrong number'),
        'unclosed_call': ('#define F(x) x\nF(1\n', 'unterminated macro'),
        'duplicate_parameter': ('#define F(x,x) x\n', 'duplicate macro parameter'),
        'too_many_parameters': (f'#define F({params},overflow) 1\n', 'too many macro parameters'),
        'too_many_arguments': (f'#define F({params}) 1\nF({args},0)\n', 'wrong number'),
        'variadic': ('#define F(...) 1\n', 'variadic macros are unsupported'),
        'bad_stringify': ('#define F(x) #other\n', 'stringification requires a parameter'),
        'paste': ('#define F(x,y) x##y\nF(+,*)\n', 'token paste'),
        'unterminated_comment': ('#if 0\n/*\n#endif\n', 'unterminated'),
        'trailing_endif': ('#if 1\n#endif extra\n', 'unexpected token'),
    }
    for name, (source, diagnostic) in failures.items():
        path = OUT / (name + '.c'); path.write_text(source)
        result = run([driver, path, ROOT / 'include'])
        assert result.returncode != 0 and diagnostic in result.stderr, (name, result.stderr)
        assert re.search(r':\d+:1: error:', result.stderr), result.stderr
        results[name] = 'rejected'
    # Check a supplied target header and its nested includes
    include = ROOT / 'include'
    result = run([driver, include / 'stdint.h', include])
    assert result.returncode == 0, result.stderr
    tokens = body(result.stdout)
    assert 'uint16_t' in tokens and 'size_t' in tokens
    results['target_header'] = 'PASS'
    # Check lone CR and mixed line endings using raw bytes
    (OUT / 'cr_data.h').write_bytes(b'#if 1\r#define CR_VAL 99\r#endif\r')
    cr_cases = {
        'cr_conditional': (b'#if 1\rint g;\r#endif\r', ['int', 'g', ';']),
        'cr_function_directive': (b'int f(void)\r{\r#if 1\r  return 2;\r#endif\r}\r',
                                  ['int', 'f', '(', 'void', ')', '{', 'return', '2', ';', '}']),
        'cr_continuation': (b'#define ADD(a,b) ((a)+\\\r(b))\rADD(1,2)\r',
                            ['(', '(', '1', ')', '+', '(', '2', ')', ')']),
        'cr_line_comment': (b'// comment\rint x;\r', ['int', 'x', ';']),
        'cr_mixed_lines': (b'__LINE__\r__LINE__\r\n__LINE__\n\r__LINE__\r', ['1', '2', '3', '5']),
        'cr_include': (b'#include "cr_data.h"\nCR_VAL\n', ['99']),
        'cr_long_file': (b'int a0;\r' * 700, ['int', 'a0', ';'] * 700),
    }
    for name, (raw_bytes, expected_tokens) in cr_cases.items():
        path = OUT / (name + '.c')
        path.write_bytes(raw_bytes)
        result = run([driver, path, ROOT / 'include'])
        assert result.returncode == 0, (name, result.stderr)
        assert body(result.stdout) == expected_tokens, (name, result.stdout, expected_tokens)
        if name == 'cr_function_directive':
            non_line = [ln for ln in result.stdout.splitlines() if ln.lstrip().startswith('#') and not ln.lstrip().startswith('#line')]
            assert not non_line, non_line
        results[name] = 'PASS'
    cr_failures = {
        'cr_unterminated_continuation': (b'int x;\\\r', 'unterminated line continuation'),
        'cr_line_too_long': (b'//' + b'a' * 4094 + b'\r', 'source line exceeds 4095 bytes'),
    }
    for name, (raw_bytes, diagnostic) in cr_failures.items():
        path = OUT / (name + '.c')
        path.write_bytes(raw_bytes)
        result = run([driver, path, ROOT / 'include'])
        assert result.returncode != 0 and diagnostic in result.stderr, (name, result.stderr)
        results[name] = 'rejected'
    (OUT / 'results.json').write_text(json.dumps(results, indent=2) + '\n')
    print(f'PASS: {len(cases)} preprocessor cases; {len(failures)} diagnostics; standalone frontend driver')


if __name__ == '__main__':
    main()
