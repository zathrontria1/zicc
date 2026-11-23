# Frame and recursive-call investigation

A recursive function can answer a simple case before it sets aside stack space. In the Fibonacci sample, the base case now returns immediately. Each recursive call that does need space uses six bytes instead of ten.

The later [tiny-frame and integer-width investigation](word-call-optimization.md)
supersedes the generic two-/four-byte frame sequences and arithmetic helper
selection described in this historical report.

Completed 2026-11-06. Original means the saved compiler with byte predicate lowering and exit-flag reuse. The original, return-only and final compilers were built separately under `build/frame-trial/`; no sample algorithm or recursion was changed.

## Findings and implementation

The old generic epilogue staged both A and X in four reserved frame bytes for every framed function. Word results now survive stack restoration in caller-clobbered X and transfer back to A; the four staging bytes disappear. Wide integer and binary32 returns leave X untouched and stage only A in two frame bytes. The public argument/result ABI, preserved Y/D/DBR, and main JSL/RTL entry remain unchanged.

A separate selector moves a leading integer guard before frame allocation. It requires exactly one word integer parameter, a comparison against a word constant, and an integer return of that parameter or a constant. It skips only empty declarations/statements; it never bypasses an initializer. Additional arguments, calls, alternate branches and more complex expressions use the ordinary framed path. The selector reuses the normal signed/unsigned comparison emitter.

For `fibonacci`, the base case now returns before PHY or local allocation. The recursive path allocates six bytes instead of ten; its return sequence is eight instructions including RTS instead of eleven. Its body shrinks from 83 to 71 bytes. The sample still executes 217 fibonacci invocations; VBCC separately observes 108 because it transforms/inlines the source differently.

## Incremental trial

This ABI harness times main entry through `main_exit`, including 18 clocks after the root return that the standard comparison below excludes. Each run checks return zero, stack balance, Y/D/DBR preservation at generated function returns, and call order.

| Trial | Master clocks | Application code bytes | Generated C calls | Lowest function-entry S |
| --- | ---: | ---: | ---: | ---: |
| Original | 219,526 | 513 | 233 | $1F72 |
| Width-specific returns | 186,928 | 480 | 233 | $1F9A |
| Returns plus entry guards | 144,980 | 472 | 233 | $1F9A |

The return-only change saves 32,598 clocks; moving the guards saves another 41,948. The minimum observed function-entry stack pointer rises by 40 bytes. This is an entry-point stack measurement, not a claim about every transient push in library helpers.

## Matched performance

Times are SNES master clocks. Basic samples run from main entry through its return; the calculator runs from its first printf entry through return from the result printf, including its ordinary console behavior. Every comparison uses two fresh emulator runs with identical elapsed results and ROM hashes. The VBCC results were independently rerun for both original and final trials and agree.

zicc uses FastROM bank $80, near pointers and its own runtime. VBCC is the installed stock r2 release, `-O3 -msfp4 -lms4 -lvc`, with its stock bank-$00 SlowROM startup and libraries. These are system comparisons, not equal-memory-speed backend comparisons.

| Workload | Original | Final | VBCC | Final reduction vs original |
| --- | ---: | ---: | ---: | ---: |
| insertion_sort | 30,744 | 30,024 | 35,430 | 2.34% |
| string_processing | 13,258 | 13,122 | 25,152 | 1.03% |
| integer_operations | 26,606 | 26,430 | 202 | 0.66% |
| function_calls | 219,508 | 144,962 | 146,150 | 33.96% |
| integer_operations_runtime | 45,398 | 45,398 | 77,748 | 0.00% |
| calculator | 629,612 | 626,176 | 1,501,200 | 0.55% |

The original `integer_operations` is mostly constant-folded by VBCC; its 202 clocks do not measure arithmetic throughput. `integer_operations_runtime` separately compiles the kernels and verifies all twelve are called exactly once. Those frame-free kernels are unchanged. The calculator includes console polling and phase-dependent timing; its measured 0.55% improvement should not be generalized to pure computation.

## Whole code and non-asset bytes

Code includes application functions, startup and linked runtime code. Non-asset ROM additionally includes strings, numeric tables, headers, vectors and initialization images; graphics, RAM BSS and unused ROM padding are excluded. Each cell is **all code / non-asset ROM bytes**.

| Workload | Original | Final | VBCC |
| --- | ---: | ---: | ---: |
| insertion_sort | 513 / 577 | 499 / 563 | 1,192 / 1,268 |
| string_processing | 511 / 614 | 504 / 607 | 1,317 / 1,430 |
| integer_operations | 1,433 / 1,497 | 1,426 / 1,490 | 552 / 628 |
| function_calls | 1,414 / 1,478 | 1,373 / 1,437 | 1,137 / 1,213 |
| integer_operations_runtime | 1,526 / 1,590 | 1,526 / 1,590 | 1,340 / 1,416 |
| calculator | 12,767 / 13,247 | 12,674 / 13,154 | 12,873 / 13,568 |

## Application code bytes

Application bytes include all emitted functions from the sample C translation unit, plus the separately compiled integer kernels where applicable. Calculator decimal conversion belongs to the runtime, so its size savings appear in the whole-code table.

| Workload | Original | Final | VBCC |
| --- | ---: | ---: | ---: |
| insertion_sort | 417 | 403 | 729 |
| string_processing | 415 | 408 | 854 |
| integer_operations | 532 | 525 | 89 |
| function_calls | 513 | 472 | 550 |
| integer_operations_runtime | 625 | 625 | 607 |
| calculator | 632 | 612 | 2,145 |

## Validation and reproduction

`make check` passed: ROM/startup, console and calculator, integer hardware, div/mod reuse, 3,712 wide cases, arrays, string/register/indexed loops, predicates, comparisons, strength reduction, direct-page addressing, branch relaxation, and 2,001 decimal round trips plus 14 boundaries.

`tests/check-frames.py` passed for the private original, return-only and final builds, and for the normal final compiler. It checks word, pointer, signed-byte, long and binary32 returns; writable stack arguments; recursive live locals; void calls; initializer side effects; and the two-argument fallback. Its guard fixture checks all six signed and unsigned comparisons across 270 boundary/deterministic inputs (3,240 comparisons), including subtraction overflow. The normal check requires all twelve guard functions to select the optimized path.

The normal compiler and private final compiler produce byte-identical ROMs for all five basic samples. Source hashes, common calculator runtime object hashes, and VBCC library/reference hashes match between original and final comparison manifests. MSVC executable hashes differ between builds because compiler build products carry build provenance; the private compiler hashes used for the comparisons are:

- Original: `c0a94e66c495b58807813b72f2833e7d4a4af0d9ffe285f4de225c4e63e35d6e`.
- Final: `fc725e1e1b85776c5242740e395220cb702ed5a9aa455861ffdce56f5e051bec`.

Raw manifests, commands, emitted assembly, ROM/debug companions, per-function profiles and paired run results are retained in `build/frame-trial/original-comparison/` and `build/frame-trial/candidate-comparison/`. The incremental ABI trial is in `build/frame-trial/{baseline,returns,guards}/`; the normal regression run is in `build/frame-check/`. The original code generator snapshot is `build/frame-trial/baseline/codegen.inc`.

```text
python tests/check-frames.py --compiler build/zicc.exe --output build/frame-check --expect-guards
```

The initial frame changes reduced return and recursive entry overhead.

## Accumulator reuse follow-up, 2026-11-06

This comparison uses the initial frame changes as its baseline. This follow-up removes the redundant temporary store/reload at the end of Fibonacci and the parameter reload immediately after its prologue store.

The first change substitutes a private word temporary into an immediately following commutative return. Exactly one definition and one use in the entire function exclude extra observations and address escape. The other operand must be a direct word operand. Calls in the defining RHS still complete before the other operand is read. A trailing eliminated home can be removed without relocating other locals; non-trailing holes are retained. The AST retains ownership of the moved RHS, and the unused assignment/object nodes are released.

The second change omits a frame-home load when the immediately preceding store already left that value in A. Only source comments may intervene. Its producer must have set full-word N/Z from A, so removing LDA preserves flags as well as the value. Labels, calls, mode changes, byte/wide accesses and uncertain flag provenance are barriers.

Fibonacci now uses a four-byte frame rather than six, emits 62 bytes rather than 71, and still makes the same recursive calls. Its recursive body is:

```asm
    txa
    sta a:$0001,y           ; save n; A still contains n
    sec
    sbc #$0001
    tax
    jsr .loword(_fibonacci)
    sta a:$0003,y           ; left survives the second call

    lda a:$0001,y
    sec
    sbc #$0002
    tax
    jsr .loword(_fibonacci)
    clc
    adc a:$0003,y           ; add left to right already in A
```

### Follow-up performance

The same comparison intervals, runtime objects, source hashes, VBCC settings and two-fresh-run requirements described above apply. The baseline here is the just-committed frame optimization, not the original pre-frame compiler.

| Workload | Initial frame changes | Forward temporary only | Both changes | VBCC |
| --- | ---: | ---: | ---: | ---: |
| insertion_sort | 30,024 | 30,024 | 30,024 | 35,430 |
| string_processing | 13,122 | 13,122 | 13,122 | 25,152 |
| integer_operations | 26,430 | 26,430 | 26,350 | 202 |
| function_calls | 144,962 | 136,162 | 131,322 | 146,150 |
| integer_operations_runtime | 45,398 | 45,398 | 45,398 | 77,748 |
| calculator | 626,176 | 626,176 | 625,714 | 1,501,200 |

Function calls save 8,800 clocks from forwarding and another 4,840 from reload removal: 13,640 clocks total, or 9.41% below the committed version. The combined result is 40.17% below the initial 219,508-clock compiler and 10.15% below the measured stock VBCC system. The FastROM/SlowROM caveat and constant-folded integer sample caveat still apply.

### Follow-up bytes

Each cell is total code / non-asset ROM bytes; definitions are unchanged.

| Workload | Initial frame changes | Both changes | VBCC |
| --- | ---: | ---: | ---: |
| insertion_sort | 499 / 563 | 499 / 563 | 1,192 / 1,268 |
| string_processing | 504 / 607 | 504 / 607 | 1,317 / 1,430 |
| integer_operations | 1,426 / 1,490 | 1,420 / 1,484 | 552 / 628 |
| function_calls | 1,373 / 1,437 | 1,361 / 1,425 | 1,137 / 1,213 |
| integer_operations_runtime | 1,526 / 1,590 | 1,526 / 1,590 | 1,340 / 1,416 |
| calculator | 12,674 / 13,154 | 12,656 / 13,136 | 12,873 / 13,568 |

Targeted forwarding tests cover both operand orders, addition/AND/OR/XOR, a callee changing the other operand, stack arguments, non-trailing homes, complete frame elimination, unsigned carry boundaries, and conservative fallbacks for escaped or multiply used locals, globals, parameters, byte temporaries, subtraction and another return-side call. Reload tests cover branch/loop joins, call boundaries, byte sign extension, Boolean/zero results and wide-to-word conversion. The new shape checks are part of `make check`. The full suite passed for both the forward-only trial and the final compiler; logs are `build/return-forward/check.log` and `build/return-forward/reload-check.log`. The additional stack-argument fixture also passed in a separate final forwarding run.

Before, forward-only, and final comparison manifests and paired profiles are in `build/return-forward/{before-comparison,after-comparison,final-comparison}/`. The initial code-generator snapshot and compiler are in `build/return-forward/baseline/`; the isolated forward-only compiler is in `build/return-forward/candidate/`. The final comparison uses the normal `build/zicc.exe`, with hash `0a40440ee51b190376247604561cad73b393fd1c60a9b040b2c8dc6efe03d3aa`. All five normal sample ROMs match their final trial ROMs byte for byte. The normal basic/calculator reports are refreshed.

```text
python tests/check-frames.py --compiler build/zicc.exe --output build/frame-check --expect-guards --expect-forwarding --expect-reloads
```
