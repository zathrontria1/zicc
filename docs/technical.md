# Compiler technical guide

If you're building a game, start with the [setup guide](../README.md), then
look up [C features](operations.md), [ROM sizes](rom-allocation.md) or
[library functions](libc.md).

If you're changing the compiler, start with the
[architecture and pass pipeline](technical/architecture.md) to see how stages
fit together, then use the [development commands](#development-commands)
to build it and the [verification guide](#verification) to check your change.
To see why zicc chose an instruction, start with the C and assembly examples in
the [optimization guide](optimizations.md). Its [implementation reference](technical/optimization-catalog.md)
points to the source code, tests and detailed reports for each change.

## Implementation milestones

- Opt-in source LTO enables cross-TU inlining after independent preprocessing
  and typed binding. See [usage and limits](technical/source-lto.md).

- Same-TU inlining supports automatic selection, inline hints, forced expansion
  and noinline barriers. See [policies, semantics and limits](technical/inlining.md).
- General structured code generation now covers the array/address, byte-loop
  and guarded-retry shapes in Dhrystone's Proc_8, main and Func_2. See
  [features, ideal targets and verification](technical/structured-codegen.md).

- Low-WRAM integration uses a `$0100`–`$04FF` hardware stack, near allocation
  from `$7E0500` and constrained file-scope `__loram` objects through `$7E1FFF`.
  See [the application contract](operations.md#low-ram-placement).
- The integrated compiler passes master's current cached `make check`: 27/27
  suites and 757 jobs at 20 workers in 332.33 seconds, retaining all 200,873
  arithmetic cases. The cache reused 82 emulator results and ran 1,214 live.
  The compiler SHA-256 was `b6287d707b0fe8a506ed86ffeab447e52b941efa8f7c78ebb7a1ab27aafd112e`.
- Loop allocation uses direct-page homes for eligible functions and regions,
  keeps eligible cursors in X, and removes some redundant indices. The
  compiler also tracks workspace use by known callees in the same source
  file and simplifies signed-word comparisons against constants. See
  [current allocation rules](technical/operations.md#direct-page-homes-and-register-cursors).
- The shared verification queue uses staged jobs, dependency scheduling,
  measured-duration ordering and host-build caching.
- The retained `speed-final` and `speed-warm` full checks each pass all 27 suites
  and 756 jobs. Their compiler SHA-256 is
  `1d2ec083f862f6a6d394fd6077ac3d454c239164b3121184119b2062e68e71ac`,
  recorded before the low-WRAM integration.

## Project status and history

An independently written C frontend/backend, built with MSVC, emitting ca65
assembly linked by ld65. Benchmark reports identify the saved builds and
include file checksums where available.

## Development commands

```text
make                 # compiler, ROM utility, runtime library and headers in bin/
make samples         # optional sample ROMs in build/
make check           # headers, MSVC references, Mesen execution, arithmetic/decimal checks
make check-changed   # only suites whose inputs changed since they last passed
make check CHECK_NO_CACHE=1 # emulate every ROM (no reuse of cached emulator results)
make check CHECK_JOBS=1 # same suites, serial execution
```

## ROM layout and build artifacts

Sample ROMs are written to `build/`. Default images start at 64 KiB HiROM and
expand to twice the capacity when packing fails, up to 4 MiB. Code is allocated
before ROM data. Each build records the chosen call stage, addresses, free space,
resource/compiler/tool hashes and rejected layouts in `.allocation.json` and a
timestamped `build/<name>-allocation/` directory. The assembly actually linked is
retained there. Siblings include `.map`, ca65/ld65 `.dbg`, flat `.sym`, and Mesen
`.mlb` labels. See [ROM allocation](technical/rom-allocation.md).
`make minimal` and `make prompt` select individual images. `make smoke`
builds the 32 KiB LoROM assembly regression fixture.

## Historical Dhrystone measurements

The 2026-11-08 review measured call and frame costs and compared a hand-written
Proc_8 under the ABI at that time. The two benchmark translation units were
compiled separately. The archived aggregate-scheduling baseline reported
743 Dhrystones per second on NTSC and 738 on PAL using nominal frame timing
and integer truncation. SlowROM reported 638 and 632 respectively.

## Host toolchain

Use a native Windows build of GNU Make, cc65 (`$CC65_BIN`),
Python 3, and MSVC discoverable with vswhere. The compiler builds with
`/std:c17 /W4 /WX /O2`. Override `CC65_BIN` if needed. Verification also
uses PowerShell, Pillow, and Mesen.

## From C source to assembly

To see what the compiler does with one C file, build the tools with `make`
and run this command from the repository root.

```text
build/zicc.exe samples/minimal.c -o build/minimal-inspect.s -I include --dependencies build/minimal-inspect.deps
```

The input comes first, then `-o` and the assembly output path. Options follow.
The compiler preprocesses the source, parses C declarations and expressions,
checks their types, and emits ca65 assembly. A library file can compile on its
own without a `main` function. For an entire game, use the
[ROM builder](rom-allocation.md). The option parser is in [main.c](../src/main.c).

| Option | What it does |
| --- | --- |
| `-I directory` | Sets the one include directory. It defaults to `include`. If repeated, the last setting wins. |
| `--dependencies file` | Writes one path per line. `+` marks a header opened or a resource found. `-` marks a resource path tried and missed, including probes. The primary C input is supplied separately. LTO collects all inputs' dependency records in the same file. |
| `--binary64` | Gives `double` and `long double` eight bytes. `float` still uses four. Build all parts of a program with matching floating-point settings. |
| `--c89-keywords` | Lets older code use `inline` as an identifier. The extension spellings `__inline` and `__inline__` still request inline expansion. |
| `--lto`, `--lto-source file.c` | Parses each input on its own and then combines the typed programs. Each additional source option enables LTO. Supply at most 32 files, with distinct names after the compiler replaces punctuation in their stems with underscores and limits the stem to 63 characters. |
| `--long-return`, `--long-calls symbols` | Select the long-call convention for the unit, or request long calls to a comma-separated list of assembly symbols. The ROM builder normally handles these choices when it assigns banks. |
| `--near-wram-objects names` | Lets the builder identify expanded-WRAM objects it proved will land in the near bank. Their declared addresses still have the far pointer type. |
| `--runtime-objects names` | Marks listed uninitialized, writable file-scope objects for banked runtime storage. The decimal assembly comparison uses this when compiling its C reference. |
| `--rom-default-rounding` | Lets the builder pass its proof of the ROM's default rounding mode to code generation. A compilation containing a native interrupt entry or basic inline assembly drops this assumption. |

Flags beginning with `--no-` let a comparison turn off a particular code
selection. For example, `--no-loop-unroll` disables cost-based loop unrolling, and
`--no-inline` disables automatic and hinted inlining while retaining explicit
forced requests. Find the switches in the [list of optimization controls](technical/optimization-catalog.md#controls-and-verification)
and examples in the [optimization guide](optimizations.md). For cross-file builds, zicc checks external types,
member layouts and WRAM placement, keeps same-named private objects distinct,
and rejects duplicate definitions. The assembly lists its source units,
source paths and embedded resources. See [source LTO](technical/source-lto.md),
the [merge code](../src/source_lto.inc), and its [checks](../tests/check-source-lto.py).

### Headers, macros and binary files

A quoted header such as `"level.h"` is looked up beside the file containing
the directive. An angle header such as `<stdlib.h>` uses the include directory.
A macro can supply either header name. Quoted `#embed` resources try the
containing directory first and the include directory second. The preprocessor
records missing resource candidates so a later build can detect a newly added
file. For example, `__has_embed` distinguishes a missing resource, an empty one
and a nonempty one. See [binary asset rules](operations.md#binary-assets-with-embed)
and [resource checks](../tests/check-embed.py).

Object and function macros expand on tokens. Function macros accept multiline
calls and empty arguments. `#` turns the original argument text into a string,
and `##` joins tokens. The result is scanned again while expansion of the
same macro is suppressed where needed. Conditional directives include
`#elifdef` and `#elifndef`. In a `#if`, integers use signed or unsigned
64-bit arithmetic, unknown names count as zero, and `&&`, `||` and `?:`
skip unevaluated arithmetic. `#line` can change the filename and line number
reported by diagnostics, `__FILE__` and `__LINE__`. These changes leave the
physical search path for includes and resources intact.

The six predefined table entries are `__ZICC__` (1), `__ZICC_BINARY64__`
(0 or 1), `__SIZE_TYPE__` (`unsigned int`), and the three
`__STDC_EMBED_...__` results (NOT_FOUND 0, FOUND 1, EMPTY 2). The table
starts with room for 4,092 more definitions. Names can have up to 63
characters and function macros up to 127 parameters. The preprocessor allows
16 nested includes, 32 nested conditional groups, 1 MiB per source or header,
and 8 MiB of expanded text. A physical source line has a 4,095-byte limit.
Macro-argument and conditional-expression nesting each have a limit of 64,
and expansion limits a chunk to 262,144 tokens or expansion steps. Its
host interface returns expanded text and the
ranges occupied by embedded data. See the [preprocessor](../src/preprocess.c),
[interface](../src/headers/preprocess.h) and [host tests](../tests/check-preprocessor.py).

### Types, expressions and calls

zicc chooses literal types using SNES widths. For example, `32768` is a
signed `long`, while `0x8000` fits in an unsigned `int`. Integer suffixes
can request unsigned, long or long long types. Decimal and hexadecimal
floating literals use the selected precision, and an `f` suffix selects
binary32. Single-byte character constants, octal and hex escapes, and adjacent
string literals are supported. See the [lexer](../src/main.c) and
[integer and floating literal checks](../tests/check-int64-frontend.py).

The parser keeps separate scopes for local declarations and function-wide
`goto` labels. A label can be used before its definition. Duplicate and
missing labels are errors. File and block declarations can use typedefs,
parenthesized declarators, arrays, pointers to arrays and function pointers.
An incomplete external array can acquire its bound from a compatible later
definition. A tentative array that still lacks a bound at the end of its
file gets one element. See [declarations and initialization](operations.md#local-initialization-and-static-storage)
and the [parser](../src/parser.inc).

Each parsed C file has space for 1,024 symbols, 64 typedef entries, 64
struct/union/enum tags and 128 source-location paths. The compact pointer
type can describe 31 pointer levels. Recursive expression and declarator
parsing has a separate limit of 256 active steps. One pair of parentheses
can use several steps. See the [parser state](../src/main.c).

An expression such as `(tick(), item)` calls `tick` first, then yields the
value of `item`. The right operand can be a struct or union. That value can be
copied, returned, read for a field or passed to another function. The result
of the comma expression cannot itself be assigned to. For compound updates
with a call on the right, the compiler can save the right operand before
reading and writing the destination. It can remove the temporary for an
automatic scalar whose address is never taken. See [object and expression checks](../tests/check-object-initializers.py).

The startup entry takes no arguments and may return `int` or `void`. Calls
from C and callbacks cannot target `main` or a native interrupt entry. A
typed prototype checks argument counts and conversions. For a K&R definition
or a call without a prototype, the compiler uses default argument promotions.
For example, a K&R `char` parameter arrives as an `int` and is converted back
to `char` on entry. A later unprototyped declaration preserves a prototype
already in scope. See the [legacy declaration code](../src/legacy_functions.inc),
[legacy checks](../tests/check-legacy-functions.py) and [startup checks](../tests/check-main-entry.py).

Taking a function's address gives an indirect call a stable entry across ROM
layouts. When an entry is needed for a linked function, the ROM builder can
supply a small wrapper that calls the target using the chosen bank layout,
restores the stack and returns with `RTL`. For an eight-byte result, the
value stays in the arithmetic workspace across the return. See the
[wrapper builder](../tools/build-rom.py) and [callback checks](../tests/check-callbacks.py).

Functions support up to 127 declared parameters and calls up to 256 arguments.
When checking the fixed 1,024-byte call budget, the parser counts stack
arguments, three bytes for a direct call or 13 for an indirect call, and a
two-byte result address for a returned aggregate. The initial frame estimate
also has a separate 768-byte limit. Changing the ROM's reserved stack space
does not change those compiler checks. See the [call parser](../src/parser.inc)
and [callback checks](../tests/check-callbacks.py).

### Built-in operations and attributes

- `offsetof` can walk nested members and constant array subscripts on complete
  structs and unions. A bit-field has no addressable byte offset of its own.
  `va_start` checks for the last named parameter of a variadic function.
  `va_arg` advances a writable cursor once and reads the requested promoted
  type, pointer or complete aggregate. See the [parser](../src/parser.inc),
  [stdarg header](../include/stdarg.h) and [ABI checks](../tests/check-priority4.py).
- `__builtin_ffs`, `__builtin_clz`, `__builtin_popcount` and `__builtin_parity`
  find the first set bit (counting from 1), count leading zeros, count set bits,
  and report whether that count is odd. Each has `l` and `ll` forms for 32 and
  64 bits. zicc can fold constant arguments. Runtime values can use callable
  functions. See the [bit operations header](../include/bitops.h) and
  [constant and runtime checks](../tests/check-bitops.py).
- The compiler recognizes `__builtin_` spellings for `memset`, `memcpy`,
  `memmove`, `memcmp`, `memchr`, `strcmp`, `strncmp`, `strlen`, `strcpy`,
  `strncpy`, `strcat`, `strncat`, `strspn`, `strcspn` and `printf`. They
  use the target library signatures. In particular, `__builtin_memchr` on a
  near pointer can return a near result even though the underlying function
  uses far addresses. `__builtin_abort` uses the runtime termination entry.
  `__builtin_inff()` and `__builtin_nanf()` supply binary32 constants. See the
  [parser](../src/parser.inc) and [library checks](../tests/check-libc-new.py).
- `__attribute__((noclone))` on a function prevents bank-specific copies.
  Its effect survives compatible redeclarations and source LTO. Inlining has
  separate hints and controls. Basic `__asm` and `__asm__` statements accept
  whitespace-separated `wai` and `nop` in a string literal, optionally marked
  `volatile`. The compiler treats the statement as an optimization barrier.
  See [bank-call checks](../tests/check-bank-calls.py),
  [inlining rules](technical/inlining.md) and [inline assembly](operations.md#basic-inline-assembly).

### How initial values reach memory

For a static object, zicc evaluates the initializer at compile time. It writes
little-endian bytes and records addresses the linker must fill in later, such
as a field pointing into another array. For a local automatic object, it
creates assignments that run each time the declaration is reached. Those
assignments can call functions. Both paths follow nested arrays, structs,
unions and bit-fields in declaration order and fill omitted elements with
zero. The first member of a union receives a positional initializer.

Constant arithmetic uses the target types, including mixed integer and
floating operands and binary64 when enabled. Invalid evaluated divisions,
shifts and out-of-range conversions can produce diagnostics. A
`sizeof` of 65,536 bytes or more has type `unsigned long`, so a large object
size can be represented. See [initializer implementation](../src/initializer.inc),
[constant-folding checks](../tests/check-constant-folding.py), and
[writable initializer checks](../tests/check-writable-initializers.py).

## C support and aggregate lowering

Scalar compound updates use direct frame/global homes and avoid preserving
unused wide results. [The scalar-home trial](technical/scalar-home-updates.md) records
correctness coverage and the matched catalog timing/size improvement.

Repeated member operands can share one pure structure-element address and use
fixed field displacements. [The shared-element trial](technical/shared-element-addresses.md)
records its safety limits and incremental timing/size results.

Tagged and untagged structures and unions provide two-byte layout, stable type
identity, complete/incomplete tag tracking, zero-filled storage, `sizeof`, and
typed `.`/`->` member access. Union members overlap at offset zero; positional
initializers select the first member. Nested aggregate members must be named.
Scalar fields support reads, writes, address-of and updates. Whole structure
and union assignment supports chaining, const sources and nested members, with
cost-based inline/loop/MVN copies; see [aggregate assignment](technical/operations.md#structure-and-union-assignment). Explicit const global initializers stay in aligned ROM
storage. For a writable global, the ROM holds its starting bytes and the linker
assigns its working address in RAM. Startup copies these bytes before console
initialization and `main`. The DATA segment, low RAM and larger application
RAM objects can each have their own copy spans. See [structure support](technical/operations.md#structure-definitions-and-layout).

C23 `#embed` supports binary byte inclusion, macro-generated resource names,
`limit`, `prefix`, `suffix`, `if_empty`, their underscored spellings, and
`__has_embed` feature probing. Global arrays can infer their outer dimension
from an initializer; embedded const objects can be packed into other ROM banks.

Fixed multidimensional arrays support typedefs, array parameters and row
pointers. Eligible loops hoist row addresses and use running frame/X cursors;
see [affine loop lowering](technical/affine-array-loops.md). Eligible counted loops
borrow a [locally saved direct-page counter](technical/dp-loop-counters.md).
[Cost-based unrolling](technical/loop-unrolling.md) removes short loops or groups
runtime iterations with scalar remainders.
See [array support and assignment-loop assembly](technical/multidimensional-arrays.md).

A `switch` evaluates its control expression once. It can compare case labels,
test a range, or look up the result in ROM when the cases yield constants.
When a case body runs, it can still fall through to the next case. A `break` leaves the
switch and a `continue` inside a switch still targets the enclosing loop.
See [switch selection](optimizations.md#switch-dispatch-without-a-saved-control-value-home).

Implicit int and K&R function definitions are accepted with warnings. Calls
without prototypes use default argument promotions through the existing ABI;
see [legacy calls](technical/operations.md#calls-frames-and-returns).

## Runtime, memory model and library

The runtime uses native A/X/Y16, D=$0000, DBR=$7E, 16-bit near pointers, 32-bit `__far` pointers, 16-bit int,
32-bit long, 64-bit long long, IEEE binary32 floating types by default, and
binary64 double/long double with `--binary64`.
Ordinary near globals share bank $7E with the stack. Their available space
starts at $7E:0100 plus the configured stack size, or $7E:0500 with the
default 1,024-byte stack. The linker keeps `__loram` objects below $7E:2000.
An object marked `__hiram` or `__farram` can go in either WRAM bank if it
fits wholly within that bank. An object marked `__xbankram` may cross from
$7E into $7F. See [application RAM placement](operations.md#expanded-application-wram).
ROM/literal addresses are far; MMIO uses explicit bank-zero far addresses. See
[the memory model](technical/operations.md#machine-and-storage). Console startup enables NMI;
other applications explicitly enable it after initializing handler state. Startup sets the hardware stack pointer first. It clears the direct page
storage, the compiler's scratch space and the linked zero-initialized objects.
The automatic ROM build supplies a routine for the extra RAM spans used by
the program and runtime. Startup also copies the initial values for
`LORAM_DATA` and `DATA` from ROM, sets the data bank to $7E, initializes the
512x224 Mode 5 console if linked, and calls `main` with JSL. Stages 1-2 retain ordinary JSR/RTS calls; stage 3 separates
application and runtime banks, using long calls at the runtime boundary; stage 4
uses JSL/RTL throughout ordinary code. Main returns with RTL into a halt loop. ROM metadata and checksums are generated by `romtool`; no copier header is
added. Change `TITLE_FILE` to a file containing the desired 0-21 character title.

`<stdlib.h>` provides near-RAM `malloc`/`free`; `<string.h>` provides
`strcpy` with a near destination and far source, and `strcmp` with two far
sources. `memcpy` and `memmove` accept near destinations and far sources;
`memset` fills near RAM. These seven functions are assembly routines in
`build/libc.a`; link the archive
after application objects. See [C library contracts](technical/libc.md).
[Struct reductions](technical/struct-reduction-banks.md) borrow Y once for field
loads and share the same private RAM/ROM bank-entry mechanism.
[Known-bank private entries](technical/bank-call-specialization.md) narrow proven
object-pointer arguments without inlining; generic far loops use the existing
call-clobbered arithmetic workspace without redundant saves.
[Indexed far loops](technical/indexed-far-loops.md) keep near cursors in X and share
a Y displacement across eligible far cursors, with bank-wrap handling.
[Far loop recovery](technical/far-loop-recovery.md) documents the byte-loop,
counted-reduction and shared-member paths restored for passed far pointers.

`<time.h>` provides a 32-bit unsigned `clock_t`, `clock()` and runtime
`CLOCKS_PER_SEC` (60 NTSC, 50 PAL). `clock()` reads an NMI frame counter and never
enables interrupts. The rate query alone requires no NMI. Optional library ticks
follow the user NMI body before the shared epilogue. Native `__interrupt(nmi)`,
`__interrupt(irq)`, `__interrupt(brk)` and `__interrupt(cop)` handlers use their
user-supplied names as vector entries and perform no automatic RDNMI/TIMEUP reads.
See [frame timing](technical/operations.md#frame-timing)
for the clock's units, wrap and NMI ownership.

See [operation and ABI documentation](technical/operations.md) for storage, expression
lowering, stack frames, arithmetic helpers, control flow, I/O and supported C
limits.

### How the ROM builder uses the final RAM layout

A far address stays valid whichever WRAM bank the linker chooses. Once the
builder knows that an entire object fits in $7E, it can recompile the C files
that use it so that a direct load or store can omit the bank byte. The address
a C program gets from `&object` still has the declared far type. The builder
measures the replacement objects and accepts them only if the RAM layout and
the set of required near objects still match. The compiler also emits linker
checks for the object's declared extent and bank restrictions. For an
initialized expanded-RAM object, it splits the ROM source into pieces of up
to 16 KiB so a manual LoROM link can place each copy inside one source
window. An address to be filled in by the linker stays wholly within one piece.

At startup, neighboring spans in the same region can share a clear or copy.
For near spans, the builder compares direct CPU loads and stores with DMA,
which copies a block of bytes in hardware. It chooses direct instructions
when they fit within both the size and time estimates for DMA. Two initialized
runs can also share one copy across a single padding byte when doing so is
at least as good on both measures. See the [ROM builder](../tools/build-rom.py),
[reset code](../runtime/startup.s), [near startup checks](../tests/check-near-startup.py)
and [application RAM checks](../tests/check-application-wram.py).

## How the compiler chooses assembly

The compiler makes decisions at three different points. Knowing which step
made a choice helps when comparing a C file with the assembly in a built ROM.

1. Before emitting functions, zicc has the parsed bodies for the unit. It can
   inline a call, reduce a private constant table, or record which arguments
   always have a known value or point into a known bank. Inside each function
   it can use those facts when choosing instructions and storage for locals.
2. After emitting a function, zicc can see register loads, stack slots and
   branches that have become redundant. Functions that use eight-byte values
   get a separate cleanup path because a returned value can still occupy the
   arithmetic workspace. The compiler records the final scratch use after
   cleanup so interrupt handlers can save the words they need.
3. Once the unit's assembly is ready, zicc measures branch distances. The
   ROM builder later chooses call forms and memory placement across files.
   The allocation report points to the assembly that actually went into the ROM.

See the [instruction selector](../src/codegen/codegen.inc),
[branch layout code](../src/relax.c) and [optimization examples](optimizations.md).

## Loop and branch optimization

Loop strength reduction maintains private running pointers for eligible affine
word indices, including struct arrays. [The struct cursor trial](technical/struct-loop-cursors.md)
records the incremental timing, code and frame costs. Use `--no-strength-reduction` when invoking `build/zicc.exe` to
disable that pass for comparison. Index values retain their normal C meaning;
the cursor allocation and conservative aliasing rules are documented above.

Eligible byte scans, copies, fills and constant transforms keep running pointers
in X/Y and A in byte mode throughout the loop. Unobserved unit counters can be
recovered from pointer movement at exit. A lifetime check also removes frame
homes from eligible loop leaf functions. `--no-register-loops` disables these
selections; [operation details](technical/operations.md) describe the safety limits.

Two-ended indexed byte loops can also lower to running X/Y cursors. A private
byte temporary with one use per definition can occupy B through XBA while A
stays byte-wide, eliminating the saved-character home from swap loops.

Short-circuit byte tests and equality comparisons can share loaded values and
carry exit flags into Boolean returns. String equality loops can therefore use
direct X/Y byte comparisons without pointer homes or repeated exit loads.

Proven bank-zero-accessible writable array cursors can use full-width `dp,X`
with D still zero; high-WRAM/general near cursors retain DBR-relative addressing.
`--no-indexed-dpage` disables that selector for comparisons.

The compiler relaxes branches to a fixed point after laying out its emitted
instructions. In-range transfers use Bcc/BRA; out-of-range transfers retain safe
long sequences. `--no-branch-relaxation` disables the pass. Boundary/cascade
checks used paired executable ROMs with matching debug companions and runtime
imports.

## Console and floating runtime

`fgets` currently replays `samples/input.txt` on every call. The program computes
repeatedly; there is no interactive keyboard/controller input yet. `printf`
supports literal text, `%%`, `%d`/`%i`, `%u`, `%ld`/`%li`, `%lu`, `%x`/`%X`, `%lx`/`%lX`, `%c`,
near strings `%s` and far strings `%S`, with numeric widths, precision and
`-`/`0` padding. The floating console (`CALC=1`) also supports `%f` and `%g`
(six digits by default), including Dhrystone's `%6.1f`. NMI automatically uploads
changed tilemap rows during VBlank; `fflush` waits for pending presentation.
The 512x224 Mode 5 display shows 64x28 characters using the original 8x8 font.
Scrolling uses two circular maps and the BG1/BG2 vertical scroll registers;
each dirty range is uploaded for both backgrounds. Presentation defers at
line 228 NTSC / 278 PAL to retain the maximum 4 KiB DMA budget.
Linking the console initializes it after
RAM/DATA setup and enables NMI, using the user handler or the default wrapper.
Clock-only programs still enable NMI explicitly. `volatile` supports direct
MMIO through explicit bank-zero `__far` pointers, with exact byte accesses and
retained reads/writes; see [volatile semantics](technical/operations.md#volatile-accesses-and-mmio).
The font/palette provenance is documented under `assets/console/`.
The project first developed these 65816 binary32 routines as an extension
in the local VBCC fork. zicc reused arithmetic and decimal code with ca65
syntax and its own calling convention. The
[provenance record](../runtime/ieee32/provenance.json) identifies the original
files and the source revision used by zicc.
Decimal parsing and formatting use assembly entries with the existing ABI;
the C implementations remain as references.

## Verification

For a single change, run the suite that covers it. For example,
`python tools/run-checks.py --suite members` checks struct member access.
Use `make check` for the full run. Keep one run active per checkout and wait
for it to finish before changing its source files or tools.

The full run fills WRAM with a known byte before startup, then checks that the
right areas were cleared. It checks CPU registers, ROM headers, interrupt
vectors and checksums. It runs
the minimal and prompt ROMs in Mesen and compares every visible prompt pixel.
Other tests check function calls, saved registers, stack balance, recursion,
loops, arithmetic, byte stores and parsing decimal and hexadecimal text. They
cover NaNs, zero, and 2,001 binary32 decimal formatting and parsing cases
checked against MSVC. Look under `logs/*-check/` for the results. The tests cover the supported
features. Full C conformance is outside their scope.

Verification and Make prerequisite builds default to
`max(4, hardware threads - 2)` jobs.
`CHECK_JOBS=N` limits the verification queue independently of Make's
prerequisite builds. The prerequisite builds started by `make check` and
verification workers run below normal process priority. Explicit `-j` and
`CHECK_JOBS` settings remain available. The normal check entry point initializes
MSVC once before its prerequisite builds.

The 27 logical suites expand into compiler/strength parts, arithmetic and decimal
batches, frame workers, setup jobs and collectors. The total job count depends
on the worker manifests; the retained full runs above contain 756 jobs, replacing
the earlier 105-job layout. All work shares the same bounded queue, with a
separate process/output directory/emulator home per worker. Setups publish worker
manifests; collectors run only after every prerequisite succeeds and reject stale
setup evidence. Unknown jobs start first, otherwise ready work uses recorded
successful durations, longest first; newly released dependencies take priority.
Failures block descendants while unrelated queued work finishes.

The 50 batches still cover all 200,873 arithmetic cases. The collector checks
the case counts, compiler and runtime identities, and integer widths. It keeps
the cases in their original order. Run `python tests/check-compiler.py --list-parts`
to list the compiler checks. Register new checks as compiler parts or suites.

Console output reports each job's status and elapsed time. Each suite has one
transcript containing the command, stdout and stderr of each finished job.
Failed jobs in split suites also have a separate failure log. The fresh
`logs/check/<UTC timestamp>/` directory includes `summary.json` with the
compiler hash, timings and byte offsets for individual jobs. All suites finish
even if another suite fails, and `make check` returns failure if any suite fails. Set
`CHECK_OUTPUT=logs/my-check-run` to choose a fresh log directory explicitly.
Existing log directories are refused to preserve previous evidence.

Emulation is deterministic (fixed RAM power-on state), so `tools/run_cache.py`
reuses the recorded output of an emulator run whose emulator build,
configuration, ROM bytes and Lua script are byte-identical to an earlier run
that completed as expected. Every test still compiles and links its ROMs and
evaluates all of its assertions; only emulating an unchanged ROM is skipped, so
a compiler change re-emulates exactly the programs whose code it changed.
Scripts that use external files, time, randomness or savestates run live.
Screenshots encoded as PNG bytes in stdout can be cached with the log and are
recreated and checked on each run; other screenshot paths bypass caching.
`summary.json` records cache counts per job, planning/build time, dependency-chain
and worker-utilization data. Run `python tools/run-checks.py --cache-trace` to
retain detailed cache events in a single SQLite file. Set `ZICC_VERBOSE_LOGS=1`
to retain individual emulator transcripts from checks that support diagnostic logs.
`tools/host_cache.py` separately caches MSVC reference
EXE/DLL builds using toolchain, flags and transitive input hashes;
`ZICC_HOST_CACHE=0` disables that cache. Use `CHECK_NO_CACHE=1` or
`--no-cache` to disable the emulator cache.

`tools/build-rom.py` caches runtime objects and their inspected segments and
symbols in `build/runtime-object-cache/`. It keys entries by transformed
assembly, assembler options and tool hashes. Runtime units with external
assembler inputs still assemble on every build. On cache hits only selected
objects are written to the build directory by default. The linker debug file
points to the selected assembly saved with the current build, so it works
after the cache or an earlier evidence directory is removed. The build
transcript records object cache hits. The allocation
manifest lists source compile-cache hits when the compile cache is enabled. Set
`ZICC_RUNTIME_OBJECT_CACHE=0` to disable reuse or set
`ZICC_RUNTIME_OBJECT_CACHE_DIR` to select a different cache directory.
For a run without any of the three caches, set both cache environment
variables to `0` and use `make check CHECK_NO_CACHE=1`.

Every run records the input fingerprint of each passing suite in
`logs/check/last-pass.json`: its test scripts and the fixtures they reference
(including through scripts they run or import), plus the compiler and ROM
tools, runtime, linker configurations, headers, samples, harness tools,
assembler, linker and emulators. `make check-changed`
(`run-checks.py --changed`) runs only suites whose fingerprint differs from
their last pass; a failed suite always runs again.

After `make check-prerequisites BINARY64=1`, a focused rerun of the opt-in
compiler and runtime checks can use
`python tools/run-checks.py --suite members` (repeat `--suite` to select more).
Use `--suite small-integers` to run just its batches with the shared worker limit.
The standalone runner also initializes MSVC once when needed. Separate full
verification invocations still share the normal build and suite output paths;
run those invocations one at a time within a checkout.

## Compiler comparisons and arithmetic optimization

`tools/debug_symbols.py INPUT.labels OUTPUT.sym` writes the address-based
profiling companion and a matching Mesen `.mlb`. Compiler assembly records an
explicit source-function/object name list; the exporter resolves only actual
labels from that list, plus exported assembly labels, `.proc` entries and direct
JSR/JSL targets (including private routines). Called RAM-code equates are
resolved from DBG records, since ld65 omits them from its label file. Constants,
linker metadata, inline markers and private branch labels stay out of these
debugger files. Source-name underscores are preserved, including static helpers
qualified by translation unit; no C ABI underscore is added. Different names at
the same address are retained. Assembly runtime names beginning with `__`, such
as `__mul16` and `__shl32`, retain that internal-helper prefix. Temporary code
constructed on the hardware stack has no stable address to label. Raw `.labels`
and `.dbg` remain linker/source-map
evidence for low-level execution probes and linker checks, not curated label
lists. The PowerShell `labels-to-sym.ps1` entry point delegates to this exporter.

The original `integer_operations.c` largely disappears under VBCC constant
folding. `integer_operations_runtime.c` calls separately compiled
`integer_kernels.c` so both compilers must execute the arithmetic.
Integer helpers now use S-CPU byte multiplication
and hardware division for divisor magnitudes through 255, including wide
dividends; larger divisors use software division.
Matching scalar `/` and `%` expressions now share a division when control flow
and unchanged operands permit it. Both results live in the invocation's frame;
`--no-divmod-reuse` disables this pass for comparison.

Native long arithmetic uses direct operands, large shifts move whole words,
and condition comparisons branch directly. Simple long helper/arithmetic
wrappers and `mix_words` use stack arguments without a frame. The wide-codegen
regression checks carry/borrow boundaries, all 32 valid shift counts, signed and
unsigned comparisons, writable parameter homes, and recursion. Signed/unsigned
word arithmetic functions use their register arguments without frames, and
variable shift helpers keep one word in A instead of shifting both in memory.

General framed functions now restore the stack according to their result width:
word returns need no staging slot, and wide returns stage only their low word.
Eligible leading scalar guards return before allocating a frame. The
[frame investigation](technical/frame-optimization.md) compares the original compiler,
the individual trials and the final compiler against VBCC, including code and
non-asset ROM bytes.

Tiny frames now push register parameters directly into their homes and release
homes with pulls. Integer multiply/divide/remainder automatically select byte,
word or long helpers according to the operation's type and proven operand range.
These are unconditional defaults; no build option is required. The
[word-call investigation](technical/word-call-optimization.md) records their timing
and code-size tradeoffs.

Word arithmetic now uses cost-selected constant shift/add recipes and a general
side-effect-free expression planner. Eligible arithmetic returns use register
inputs, incoming stack arguments and reusable scratch without a frame. Calls,
indirection, byte/wide types and resource-heavy expressions retain their normal
lowering. See [the expression investigation](technical/word-expression-optimization.md)
for the generated combine leaf, before/after measurements and structure-member
compatibility checks.

Long commutative arithmetic can defer a fixed operand load until after a pure
subexpression. Products of two widened words use four hardware partial products
for the full 32-bit result, preserving each source's signedness. See the
[widened-product investigation](technical/widened-product-optimization.md) for the
current add_scaled assembly, validation and runtime-size tradeoff.

The historical inventory study compiled identical driver and kernel sources
separately, then verified every call and product. See
[the runtime inventory comparison](technical/structures-runtime-comparison.md).

Guarded signed-word field updates can now keep their pointer and computed value
in incoming X/A across the sign test and conditional store, without a frame.
See [guarded-update selection](technical/guarded-updates.md) for eligibility, fallback
rules and the measured `adjust_quantity` assembly.


General arithmetic-region selection, typed byte bounds, private-value cleanup
and faster mixed-width multiplication/word division are documented in
[arithmetic regions](technical/arithmetic-regions.md).

The four cumulative BouncingSprites milestones
record scalar/conditional regions, phase recurrences, dual scaled indices, indexed
updates and completed reuse/path facts, with per-item CPU cycles, master clocks,
code sizes and correctness evidence.

The four further improvements
add demanded-bit/flag cleanup, min/max subtraction fusion, temporary byte-index
bindings and private region liveness/byte-width selection on master. Each item
reports code size and timing in CPU cycles and master clocks. Repeated runs
checked the expected output on all 600 updates.

General recurrence coalescing
then removes the gradient's copied phase home and safely widens low-bit-only
recurrences. Repeated 600-update runs save another 1,176 CPU cycles and 23 code
bytes; focused verification passes, with no full check requested.

CFG accumulator reuse tracks
word values separately from N/Z through branches, joins and loop backedges.
BouncingSprites saves a further 240 CPU cycles per update and 14 code bytes;
repeated measurements and focused verification pass without a full check.

Collision range propagation
adds bounded abstract execution, per-cell intervals and affine min/max span
bounds. BouncingSprites saves another 434.98 CPU cycles per update and 76 code
bytes, with unchanged state, pixels and workload counts at both ROM speeds.

Bounded signed min/max selection
uses the established non-overflow bounds to preserve A with CMP/N branches.
Against the verified baseline with recurrence coalescing and collision range analysis,
BouncingSprites saves 604.79 CPU cycles per
update and 20 code bytes; repeated measurements and focused tests pass.

Nested-loop index retention
keeps the outer displacement in Y across inner X-retained loop entries.
BouncingSprites saves another 430 CPU cycles per update and 29 code bytes;
repeated timing, full state/pixel checks and exact workload probes pass.

Gradient loop completion
eliminates unobserved retained counters, folds literal displacement setup and
recycles dead private DP homes for pure word combines. BouncingSprites saves
another 1,255 CPU cycles per update and 51 code bytes; the gradient is 98 bytes.

General selection/frame/call cleanup
shares unchanged predicates, colors nonoverlapping private stack homes while
retaining logical ownership, and removes unused-result and wide-load setup.
BouncingSprites saves 2,545.82 FastROM / 3,028.24 SlowROM master clocks per update,
135 linked code bytes and 22 main-frame bytes across the three items.

Recent codegen optimizations add native power-of-two division/remainder and
word shifts, structured byte regions, safe loop fusion, copy widening and
shared discarded-update selection.
