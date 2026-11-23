# Same-translation-unit inlining

Inlining replaces a function call with the body of the function. zicc can then
optimize that body in the context of its caller. It does this on the typed
syntax tree, before choosing storage or instructions. It can use a definition
anywhere in the same C file, even below the call. Enable [source LTO](source-lto.md)
to include definitions from other C files. Indirect calls and definitions in
separately compiled files stay ordinary calls.

## Policies and linkage

| Declaration | Selection policy |
| --- | --- |
| Ordinary function | Automatically inline profitable eligible calls |
| `inline`, `__inline`, `__inline__` | Hint: increase the profitability/growth allowance |
| `__attribute__((always_inline))`, `__forceinline` | Force eligible calls; diagnose failures |
| `__attribute__((noinline))`, `__noinline` | Never substitute this function |

The GCC double-underscore attribute names `__always_inline__` and
`__noinline__` are also accepted. Attributes can precede the declaration or
follow its parameter list, and merge across declarations. Forced and prohibited
policies conflict and produce an error. `inline` plus `noinline` retains the
inline linkage rules but prohibits substitution.

`--no-inline` disables automatic and hinted selection. Explicit forced calls
still expand or produce a diagnostic. It is useful when a test or profiler
requires actual ABI call boundaries.

Plain `inline` is not forced. An external inline definition whose file-scope
declarations are all inline without extern supplies an inline body but no
external definition. A call left out of line imports the external symbol.
`extern inline`, or a non-inline file-scope declaration of the same function,
provides the external definition. `static inline` has internal linkage. An
internal body made unreachable by substitution can be omitted; externally
visible ordinary definitions remain available to other translation units.

## Selection and limits

Selection is per call site. The initial target model estimates call/setup/frame
savings, extra private word homes and code expansion. Arguments known at the
site earn a simplification allowance. Estimated pressure above fourteen private
words incurs a spill penalty. This is a conservative heuristic, not a proof
that final allocation is spill-free or a trial compilation of both alternatives.

Ordinary calls have a 32-point body limit and a 128-point caller growth budget;
hints raise these to 96 and 384. The structural cost includes expression nodes,
extra charges for calls/multiply/divide, and a 32-point loop charge. Non-tail
returns add 32 points for their completion flag and continuation guards, rather
than being priced like tail trees. Hints increase the estimated benefit.
This allows the same helper to expand in a
small caller and remain a call in a crowded caller.

Forced selection bypasses profitability limits. All policies retain an eight-
level expansion limit, a 2,048-point per-body and 4,096-point caller hard limit,
the existing symbol/frame limits, and recursion/structural checks. Recursive
strongly connected components, variadic/unknown argument lists, interrupt
boundaries, unavailable definitions and switch bodies are not substituted in
this initial implementation. An explicit forced call diagnoses the reason.

## Semantics and optimization

Every expansion gets fresh parameter/local/result symbols. Arguments are
evaluated once in the existing call order. Typed conversions, volatile
qualification, near/far pointer widths, array storage and aggregate alignment
are retained. Deferred aggregate-value temporaries are cloned as well.

Expression work is lifted into ordinary statements. Logical operators and
conditional expressions keep their conditional evaluation. Assignment
destinations are captured before right-hand work; compound assignments also
capture the previous value first. Ordinary binary operands retain left-first
evaluation, while call arguments retain their existing right-to-left order.
Aggregate copies remain address operations rather than scalar snapshots.

Tail return trees assign a private result without an exit flag. Earlier returns
use a private completion flag and structured guards. Nested loops stop on that
flag; a returning for-loop does not execute its step. Calls expanded in loop
tests and steps preserve test frequency, break scope and continue behavior.
Unused pure return computations and unnecessary initial result stores disappear.

Existing scalar/body passes simplify bindings and results before allocation.
Eligible native expression leaves can therefore emerge from an expanded call.
No allocated registers, shared return labels or callee stack offsets are copied.

## Execution evidence and tests

Generated assembly identifies substitutions with `; inlined call: caller callee`
and exported zero-byte `__inlined_*` entry labels. The normal emitter retains
these through optimization; the native word-expression selector also retains
unconditional empty prefix markers. Other whole-function selectors fall back
when they cannot retain marker placement. Markers add no machine instructions.

The Dhrystone verifier counts actual ABI entries and substituted entry markers.
ABI input assertions remain attached to real calls; the same per-iteration
array, string, record, result, stack, interrupt and screen checks remain active.
Markers describe execution of substituted source regions, not a guarantee that
every original operation survived legitimate constant folding. Generated
assembly and opaque runtime workloads remain necessary for throughput claims.

`python tests/check-compiler.py --part inlining` runs automatic, hinted, forced,
prohibited, pressure, forward-definition, recursive fallback, sequencing,
aliasing, local-array/struct, aggregate-value, byte/word/wide/far, early-return,
loop/continue/break, external-inline linkage and stage-4 JSL/RTL tests. Forced
failures have explicit diagnostic checks. Opaque drivers are separate C units,
and semantic results also have an MSVC reference.

Older tests whose purpose is an ABI boundary now explicitly prohibit inlining:
console/checkpoint hooks, assembly-reference case hooks, the divmod opacity
helper, the banked sum-call probe and the widened-product call barrier. Frame
instruction-shape checks use `--no-inline`; normal inlining remains enabled in
semantic, arithmetic and sample comparisons.

The 3,000-iteration Dhrystone interval drops from 62,747,618 to 61,042,722
FastROM master clocks (2.72%) and from 73,013,668 to 71,227,870 SlowROM clocks
(2.45%). Application code grows 92 bytes, from 2,686 to 2,778. Public out-of-line
definitions remain available; the ROM container stays 64 KiB. Matched runtime
sample rows are unchanged, as their driver/kernel calls cross C files.

The required full check used the default twenty hardware workers, retaining all
200,873 arithmetic cases. Initial failures exposed destination/old-value
sequencing and aggregate-address issues, now covered by explicit regressions.
The nine affected suites were rerun; the remaining scalar/DP shape and
checkpoint checks then passed their focused parts. Final forced/forward-void
and conservative early-return-cost fixes passed the complete inlining part.
The original full and recovery summaries are retained separately; combined
evidence does not replace the original failed full-command exit status.

Each compiler matrix has 51 builds and 102 completed repeated measurements.
The void-step fix rebuilt all 34 zicc ROM variants byte-identically, allowing
successful measurements to remain valid. The final cost correction changed
only the two original structures ROM variants; all four of their measurements
were rerun. Directory/READY failures were resumed individually. Fresh final
Dhrystone NTSC/PAL runs additionally check state, ABI and screen pixels.
Raw source/compiler/runtime/ROM hashes, previous variants and replay logs are
retained under `build/inlining/`, including `rebuild-proof.json`,
`cost-rebuild-proof.json` and `verification.json`.
