# Runtime RAM backfill in bank $7F

Moving library buffers into RAM bank $7F leaves more room for a game's own
variables in bank $7E. The calculator recovered 4,472 bytes this way. Ordinary
application variables still live in the same place, near pointers still take
two bytes, and the data bank register stays at $7E.

The change was tested on 2026-11-08 against the saved compiler from before the runtime RAM backfill. The final compiler
SHA-256 is `6c00d01c6eb0093b117d8ccc59452bcf707b92d61fa6c95420ba359a28e91902`.

## Recovered near capacity

These figures come from the final linked `__NEAR_START__` / `__NEAR_LAST__`
symbols, including all near static objects and alignment. Heap capacity is the
remaining bank-$7E extent, before per-allocation headers.

| Program | Before near statics | After near statics | Recovered | Remaining near heap |
|---|---:|---:|---:|---:|
| Prompt | 4,190 | 2 | 4,188 | 64,254 |
| Calculator | 4,606 | 134 | 4,472 | 64,122 |
| Dhrystone | 9,334 | 5,142 | 4,192 | 59,114 |

The console contributes its 4,096-byte map and 92 private state bytes. Decimal
formatting/parsing contributes 284 bytes: 200 digits, 80 output bytes, and two
two-byte words. The optional clock counter contributes four bytes. Dhrystone
does not link decimal state. Programs without these services reserve none of
their buffers. Application globals/statics, constrained `__loram` objects,
stack frames and DP workspace keep their existing placement.

Public stdin/stdout tokens and errno remain near. Small near control exceptions
are the clock-rate cache, allocator-ready word and strtok cursor; each is two
bytes and appears only when its owning member is linked. A pointer's storage
bank remains independent of the bank of its pointed-to data.

## Placement and interfaces

`tools/runtime_ram.py` places live, explicitly classified segments in stable
name order from exclusive cursor $800000 downward. Every placement retains
measured size/alignment, contributing member records, address/end and padding.
It rejects individual, cumulative, alignment-induced and reserved-extent
overflow. The automatic builder checks final segment addresses/sizes against
the allocation manifest. Runtime RAM is never treated as a ROM packing unit.

The classes are CONSOLE_MAP, RUNTIME_BSS, RUNTIME_CLOCK and RUNTIME_CONSOLE.
C `static` is not a placement rule. The internal compiler switch
`--runtime-objects dec_digits,dec_n,dec_scale,dec_output` marks the decimal
translation unit's selected objects as banked mutable BSS, so generated C
references and address formation use far provenance. Initialized/const,
`__loram` and DP objects are rejected by this switch. All migrated production
state is BSS, initialized by the existing full two-bank startup clear; no new
initialized runtime copy span is required.

The internal `dec_format` / `dec_format_spec` results are padded four-byte far
pointers in A/X. Their existing raw helpers continue to take near destinations.
The wrappers format into an 80-byte invocation-local stack buffer and copy the
completed string to the far output. Console consumers retain both return words.
All-C reference implementations and assembly fixtures exercise this contract.
Public printf, sprintf, snprintf and other stdio signatures are unchanged.

Foreground code retains DBR=$7E. Console leaf helpers and clock snapshots save
DBR, establish $7F and restore the interrupted/entry bank; decimal helpers use
explicit long accesses, including replacements for instructions without long
addressing forms. The clock keeps its high/low/high retry protocol.

NMI order is user body and frame cleanup, one shared NMI_BANK boundary
(`PEA $7F7F; PLB; PLB`), linked NMI_LIBRARY services, and the common epilogue.
The epilogue restores the original DBR directly, using only stack and DP work
after library services. The boundary member is selected only when a library
service requires it. User DMA still precedes library DMA, deferred console work
does not skip the clock, and interrupt enabling/acknowledgement policy is
unchanged.

## Manual links

Use `python tools/link-runtime-ram.py` with the usual ld65 arguments, for example:

```text
python tools/link-runtime-ram.py -C linker/lorom32.cfg -o build/app.raw ...objects...
```

The wrapper first resolves archive members with a temporary region in bank $7F,
measures only selected segments, then relinks the same inputs with exact
backfilled extents. Both commands, configs, the probe map and runtime-ram.json
are retained under `build/app-runtime-ram/<UTC timestamp>/`, keeping only the
latest and previous timestamped run directories. All 16 supplied
LoROM/HiROM layouts are covered. Bare ld65 still places these classes in $7F,
but the wrapper is required for top-down placement and the report showing where each buffer went.
The normal automatic HiROM builder performs selection/measurement directly and
does not use this extra probe link.

Referencing archive-exported size metadata in MEMORY expressions was rejected:
it pulled in optional clock/decimal members merely to calculate their sizes.
The measured two-pass manual link avoids that selection side effect. The
standard smoke build and shared manual-link test helper use the wrapper.

## Performance and stack

Each entry below is a pair of identical fresh NTSC measurements. Clocks are
master clocks; code is all linked executable code, excluding data/assets/fill.
Samples retain the established checkpoint boundaries and Dhrystone measures
its 3,000-iteration kernel, excluding printed reports.

| Program / runtime mode | Before Fast | After Fast | Before Slow | After Slow | Code before → after |
|---|---:|---:|---:|---:|---:|
| Prompt | 368,202 | 368,320 | 370,216 | 370,324 | 1,917 → 1,945 |
| Calculator | 501,822 | 504,698 | 526,316 | 529,618 | 10,697 → 10,851 |
| Dhrystone | 81,100,196 | 81,120,260 | 94,156,466 | 94,182,582 | 8,397 → 8,432 |

Dhrystone changes by +0.0247% Fast / +0.0277% Slow; the calculator checkpoint
changes by +0.573% / +0.627%. Minimal, sorting, strings, integer operations,
function calls and structures retain identical clocks and code sizes in both
runtime configurations. Application code bytes remain unchanged. These are
whole linked-program measurements, including normal interrupt and console
behavior, rather than isolated instruction throughput.

The post-migration write trace's lowest stack addresses are $04A8 for prompt,
$03D5 for calculator, and $0480 within Dhrystone's kernel: respectively 88,
299 and 128 bytes below exclusive stack top $0500. These are interval-specific
written high-water marks, not proofs about unexecuted paths or untouched frame
reservation. The trace observes bank-zero and bank-$7E stack aliases and excludes
ordinary globals below the active stack pointer. There is no measured baseline
stack trace. The stack remains $0100-$04FF.

The [complete post-migration comparison](runtime7f-compiler-comparison.md)
includes original/split workloads and stock vbcc65816_r2. The earlier
[comparison](current-compiler-comparison.md) remains the measured baseline.

## Verification and evidence

- Final `make check-changed`: 27/27 suites, 761 jobs, 20 hardware-thread workers,
  312.82 seconds, all 200,873 arithmetic cases preserved. It follows the required
  full `make check`; failed parts were corrected and rerun individually before
  changed-suite verification. Final summary:
  `build/check/20261108T023830.589610Z/summary.json`.
- Runtime RAM tests cover empty/full-bank allocation, overflow/padding/reserved
  extents, every manual layout, all four HiROM stages, and live NTSC/PAL NMIs
  at eight actual foreground bank-transition checkpoints per stage. The fixture
  uses a $FAE0-byte application buffer plus formatting, clock, console and near malloc.
  Separate clock tests retain race/rollover cases and preserve $7E/$7F/$12
  interrupted DBRs across A8/A16 and X8/X16 modes.
- C and assembly decimal fixtures retain numeric vectors, work/ABI assertions,
  nested IRQ/NMI checks, and near-pointer alias cases that now distinguish
  equal low words in different banks. The full decimal collector passed.
- Post-migration sample matrix: 51 builds / 102 matching final runs, input/tool/
  runtime hashes, ROMs, assembly, maps, manifests, stack traces and Lua assertions
  in `build/runtime7f-comparison-20261108/`. Baseline evidence is retained under
  `build/current-comparison-20261108/`; neither its ROMs nor its report was
  overwritten.
- Normal `make dhrystone` output passed NTSC and PAL final state, all expected
  procedure counts and exact 512×224 console pixels. Reports/screenshots:
  `build/runtime7f-dhrystone-final/ntsc/` and `pal/`.

No physical-hardware measurement was made. The allocator tests covered
reserved extents.
