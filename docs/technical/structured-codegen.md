# Structured code generation and Dhrystone (2026-11-08)

The Dhrystone sample showed three places where the SNES did extra work while
accessing arrays, looping over bytes or retrying a calculation. zicc now
recognizes these patterns in other programs too. It checks types, possible
side effects, which values another pointer could reach, and instruction cost.
The benchmark C and runtime code stayed the same. See the
[historical Dhrystone measurements](../technical.md#historical-dhrystone-measurements).

## General features

- Bounded private-scalar facts propagate constants and copies through structured
  blocks and matching branch exits. Assignments invalidate dependent facts;
  mutation within an expression is handled before substitutions. Dead private
  stores and their frame slots disappear while effectful right sides remain.
- Short signed loops with a common stable affine root can unroll without a
  literal starting value. Selection is limited to four trips and 24 flat
  statements. Signed offsets are mathematical offsets, not wrapped differences.
  Unsigned or widening steps, signedness-changing casts, escaped counters,
  changing dependencies and non-flat control flow retain ordinary lowering.
- A single guarded, nonoverflowing progress step can normalize a retry loop.
  The predicate is still executed on every retry. Exit facts apply only after
  that loop terminates. Wider comparisons and potentially wrapping steps are
  rejected; mutating predicates retain their original shape.
- Near-address normalization and bounded straight-line address reuse share
  scaled array addresses. Calls, conditional evaluation and dependency writes
  stop reuse. Payload loads and stores remain in order, including reloads when
  array bases overlap. Up to four temporary pointer homes are introduced.
- Nonvolatile near word updates use native memory INC/DEC, preserving old/new
  expression values where needed. Discarded named byte updates operate directly
  in A8. Unsigned byte relations compare in A8 and restore A16 before branching.
  Volatile operations retain their access contracts.
- Small near pointer offsets use wrapping INX/DEX. An internal annotation stops
  later displacement folding from turning 16-bit pointer wrap into a bank carry.
- Pure word argument pairs can load X first and A second when the second load
  preserves X. Effectful arguments retain the existing snapshot/evaluation
  order. Basic-block register reuse observes writes, base-register changes,
  calls, stack motion, width changes and control flow.
- DP homes now support incoming stack arguments. Complete promotion can remove
  the local frame while addressing the original incoming stack slots in place.
  Partial promotion, stacked wide arguments, recursion and long returns retain
  the existing ABI. Procedures without a valued return omit unused generated
  results and result-preservation shuffles; main retains its implicit zero.
- Standard strcmp calls with proven near-origin arguments use a private word
  input adapter. Unknown far origins, volatile pointer reads, custom local
  definitions and mismatched signatures retain the public call. The adapter
  preserves Y/D/DBR/SP and far bank progression, including a public strcmp
  fallback after a complete 64-KiB scan. The public library ABI is unchanged.
- Literal-to-near strcpy MVN no longer saves/restores DBR redundantly: its
  destination bank already matches the ABI's bank $7E. Existing interrupt
  restoration remains in force.

`--no-body-optimizations` disables the structured body pass, near strcmp
adapter, ordered-byte compare selection and procedure-result omission, and
restores the old literal-copy DBR saves. Existing `--no-strength-reduction`,
`--no-loop-unroll`, `--no-dp-homes` and `--no-line-passes` switches isolate the
other selectors. A complete conservative differential pair uses the relevant
switches together; the new switch alone does not disable every optimization.

## Ideal targets and generated shapes

| Function | Before, bytes | After, bytes | Hand target |
| --- | ---: | ---: | --- |
| Proc_8 | 272 | 123 | 97-byte retained candidate |
| Func_2 | 205 | 67 | approximately 64 bytes with tighter branch/return layout |
| main | 1,964 | 1,906 | hot byte increment matches the five-instruction target |
| Proc_7 | 22 | 19 | unused procedure result removed |

Application code, including the new 73-byte near-string adapter, drops from
2,982 to 2,686 bytes (9.93%). These are logical code bytes, excluding data,
assets, padding and linked runtime. The ROM container remains 64 KiB.

### Proc_8

The generated function has no Y frame or loop-counter home. It shares a row
address and a diagonal cursor, emits the two fixed stores, uses a native memory
increment and reloads the source array after the preceding potentially aliasing
writes. The hand-written 97-byte candidate and its verified whole-benchmark
trial are retained in `build/dhrystone-assembly-review/ideal-proc8.s` and the
assembly review. Its 26-byte advantage is still useful headroom for improved
register scheduling and cursor lifetimes. It is a workload-checked sketch,
whereas the compiler selectors also have pointer-wrap and overlap coverage.

### Func_2

The ideal control/data shape under the existing word-argument ABI is:

```asm
    ; Save the two near roots in call-safe private homes
retry:
    ; X = zero-extended first[2], A = zero-extended second[3]
    ; Form each near address with 16-bit wrapping cursor operations
    jsr Func_1
    cmp #0
    bne retry
    ; X/A = the saved roots; no padded far arguments or caller stack cleanup
    jsr private_near_strcmp
    cmp #0
    beq false_result
    bmi false_result
    lda #10
    sta Int_Glob
    lda #1
    rts
false_result:
    lda #0
    rts
```

Generated code now has this data flow: two DP pointer homes, fixed offsets 2/3,
the original Func_1 calls and actual string scan, no local counter/character
home, and no Y frame. The dead W/Z/R tests disappear from proven finite-exit
facts. Remaining layout overhead is an inverted retry branch plus BRA, and a
shared return reached with BRA: approximately three bytes beyond this sketch.
The sketch is an ideal layout target, not a separately measured ROM or a claim
that arbitrary nonterminating retries can be deleted.

### main

The old character increment took 17 instructions. The compiler now emits the
same five instructions as the hand target:

```asm
    sep #$20
    lda a:$0007,y
    inc a
    sta a:$0007,y
    rep #$20
```

The unsigned character loop test likewise loads and compares bytes directly:

```asm
    sep #$20
    lda a:$0007,y
    cmp a:.loword(_Ch_2_Glob)
    rep #$20
    beq body
    bcs done
```

Pure argument pairs avoid unnecessary push/pull staging. Repeated literal
copies avoid redundant DBR saves. main still owns live address-taken locals
and local strings, and contains startup/report printing outside the timed
interval; its whole-function byte reduction understates the hot-loop change.
Further whole-program constant propagation or call removal is not assumed.

## Timing and execution evidence

The interval is return from the first clock() through entry of the second,
covering 3,000 iterations, normal NMI activity and refresh. Initial repeated
NTSC measurements are 81,120,260 -> 62,747,618 master clocks in FastROM and
94,182,582 -> 73,013,668 in SlowROM. PAL correctness and final screen pixels also
pass.

The Dhrystone measurement harness reuses the complete Dhrystone verifier,
adds the exact clock boundary hooks, and retains assembly, objects, sources,
ROMs, logs, screenshots and hashes. Fast/Slow variants differ only in MEMSEL,
the header speed bit and checksum. Every run uses a fresh uncached Core process.
The full sample comparison additionally checks both compilers' actual work.

## Verification

The registered body-codegen compiler part compares opaque kernels and drivers
in separate translation units against MSVC references and a conservative
current-compiler fallback. It covers alternate array dimensions, overlapping
bases, mutable pointers, operand side effects, branch facts, signed/unsigned
conversions, old/new update values, near wrap, bank crossing, full-span string
scans and stage-4 JSL/RTL calls. All 65,536 opaque byte pairs exercise all six
relations in both modes. Bounded volatile witnesses require unsigned-wrap and
widened-bound loops to continue, with stable stack and observable progress.

The required full `make check` was run with the machine's 20-worker default.
All 200,873 arithmetic cases passed. Initial failures were stale instruction
shape assertions and a rounded-assembly reference model assuming STA's byte
write order for native memory INC. Targeted recovery retains every previous
passing job and reruns the affected assertions and previously unreached work.
The model now checks INC's high-byte-first word writes, retaining exact values,
counts, reads, alias cases and interrupts. Counter performance tests isolate
the saved-$00 selector from the independently improved home allocator.
Final conservative eligibility/base-invalidation guards receive focused body,
scalar, loop and home-allocation coverage. Raw verification paths and hashes
are recorded alongside the before/after results; the initial failed full-run
summary is retained rather than represented as a successful full command.
