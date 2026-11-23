# Source-based LTO and cross-TU inlining

Normally zicc compiles one C file at a time. Source LTO lets it use a function
defined in one file to simplify a call in another. To enable it, pass the C
sources together as shown below.

```text
python tools/build-rom.py driver.c kernels.c --lto -o build/game.raw
build/zicc.exe driver.c -o build/program.s -I include --lto-source kernels.c
```

The compiler also accepts `--lto` for a single input. Repeated `--lto-source`
options imply `--lto`. Ordinary builds retain separate translation units and
same-TU inlining. No serialized IR or object-file LTO format is introduced.

Each input has its own preprocessing, macro state, parser, typedefs and tags.
The merge joins typed trees before inlining, body optimization, frame/home
allocation and instruction selection. It does not concatenate C text. All
participating application C sources must be available at build time; runtime
assembly and separately linked library objects retain their existing ABI.

## Policies and binding

The [existing inlining policies](inlining.md) apply across the merged program:
automatic profitability selection, `inline` hints, forced expansion and
`noinline` barriers. Policies merge across external declarations. Conflicting
forced/prohibited requests diagnose an error. `--no-inline` disables automatic
and hinted application expansion while retaining explicit forced requests.
Recursion across files is detected by the existing call graph and retains
calls; forced recursive expansion is an error. Other existing eligibility and
pressure/growth limits remain in force.

Public declarations bind to one external definition. Return, object and
parameter types, pointer widths/qualifiers, aggregate member layouts and
placement attributes are checked across every pair of declarations. Incomplete
arrays/aggregate declarations are accepted when compatible; they cannot bridge
two conflicting complete declarations. Recursive aggregate shapes are compared
with a bounded visited-pair set. Private same-named types remain distinct unless
compatibility of a shared external declaration establishes their identity.

Private file-scope symbols receive reserved per-input assembly names. Function
owners and local symbol references are remapped. Original static storage and
string objects remain shared with every expansion of their owning body; LTO
does not create a fresh string object at each inline site.

C inline linkage is preserved. An inline-only definition supplies that TU's
alternative inline body, while an out-of-line call resolves to the actual
external provider. The provider may have a different body. `extern inline`
provides an external definition. Two actual external definitions are rejected,
including two tentative object definitions (there is no common-symbol merging).

## Allocation and evidence

The builder produces one application assembly object, with the usual separate
per-function placement units. It regenerates code for each attempted allocation
stage, preserving near calls/returns, application/runtime split banks and stage
4 long calls/returns. An application definition replacing a runtime export uses
the application's call convention. External assembly functions remain imports.

Allocation manifests record `source_lto`, C source hashes, and dependencies
reported by every independently preprocessed input. Generated assembly retains
source/dependency comments, inline-selection comments and zero-byte inline entry
markers for execution instrumentation.

Limits are 32 inputs, distinct sanitized input basenames, 1,024 combined symbols,
1,024 functions and 128 aggregate pairs per type comparison. Per-TU frontend
limits and all inlining budgets still apply. LTO currently rebuilds the source
set on every invocation; there is no archive extraction, persistent IR cache,
profile-guided selection or automatic whole-program removal of public symbols.
Externally visible definitions remain available even after all visible calls
inline. This can increase code size.

## Verification

`python tests/check-compiler.py --part source-lto` runs the focused suite;
`make check` includes it. Tests cover all four bank/call stages, automatic and
hinted selection, forced expansion, defining-TU noinline barriers, independent
macros and private symbols/types, recursive public types, literal identity,
C inline provider/fallback semantics, reversed source order, cross-TU recursion,
external assembly calls and application runtime overrides. Negative tests cover
duplicate definitions, incompatible types/placement/policies, incomplete-type
bridges, forced recursion and interrupt calls. Selected cases also run as
separately compiled host C references.
