# Typed known-bit and range selection

After `value & 31`, zicc knows the result is between 0 and 31, even if it
doesn't know `value`. It tracks facts like this when choosing instructions.
The later [word-shift and RAM-store changes](byte-shuffle-stores.md) build on
this work.

Implemented in the isolated homebrew-samples checkout after
[X/Y loop index retention](loop-index-retention.md). The frozen executable and
accepted ROMs from that milestone are this comparison's baseline. The compiler
change is general; sample sources and assets are unchanged. Initial validation
used focused checks followed by a full verification run.

## Implementation

`src/known_values.inc` tracks explicit known-zero/known-one word bits and signed
or unsigned value bounds on typed expressions. It runs after inlining and the
existing body/induction preparation. Facts survive casts, private scalar copies,
bitwise operations, bounded addition/subtraction, constant shifts and conditional
expressions. A join intersects bit proofs and unions bounds. Simple comparisons
refine the true/false arm; the triangle's two arms consequently both prove 0..31.

Only unescaped, nonvolatile automatic integer scalars have tracked homes.
Globals, indirect loads and escaped locals contribute their type bounds alone.
Unknown calls cannot change the tracked private objects. Every expression's
writes are invalidated before analyzing any operand or argument, avoiding an
assumed C evaluation order. Nested assignments do not publish facts. Loop entry
and exit invalidate every modified home; body-written homes are invalidated
again before steps/conditions to account for continue edges. Loop-invariant
private facts remain usable. Switch bodies and interrupt functions conservatively
retain existing selection. This is a bounded structured analysis, not a complete
CFG solver or alias analysis.

The emitter uses these proofs to:

- Remove bit masks whose cleared bits are already zero, while retaining the
  expression's type and evaluation.
- Replace `(2^n-1)-value` with XOR when all bits outside that mask are proven zero.
- Omit narrowing/bool normalization only when the incoming normalized register
  value is representable in the destination. Compound assignments distinguish
  the pre-conversion result from its narrowed result.
- Select word CMP for proven nonnegative signed comparisons and bounded promoted
  byte comparisons, avoiding signed overflow repair or accumulator-width changes.
- Recognize proven nonnegative byte values for existing arithmetic selectors.

Signed byte extension remains intact. Facts describe C/register values, not the
unused neighboring byte in a byte object's memory slot; byte loads still perform
their required normalization. There are no source/function/asset-name selectors.
`--no-known-values` disables this milestone independently; the existing
`--no-strength-reduction` and `--no-body-optimizations` switches also disable it.

## BouncingSprites results

Average work over 600 logical updates, excluding startup and VBlank waiting:

| Build | X/Y baseline clocks | New clocks | New ms | Fewer work clocks |
| --- | ---: | ---: | ---: | ---: |
| FastROM | 272,608.06 | 255,928.04 | 11.916227 | 6.12% |
| SlowROM | 324,734.98 | 304,283.20 | 14.167684 | 6.30% |

Two fresh runs per speed agree exactly. All four runs match every update's
expected positions, velocities, full OAM shadow, HDMA table and phase. The state
sequence SHA-256 remains
`0bad2bb9b559eb75c14a74746e26f6122a74175e2d3291d8deb1742b5576fd1d`.
All final screenshots match baseline pixels, RGB SHA-256
`31f30fb3c18a97acbb3e58b3b7d8341e3289865420afda2a34fff77933192b5a`.

Both speeds remain at 600 logical updates in 600 physical frames. Including waits,
the averages are 357,366.03 clocks / 16.639265 ms for FastROM and 357,365.92 clocks /
16.639260 ms for SlowROM. Maximum update work is 265,726 and 316,088 clocks.
Milliseconds retain the 21,477,272-master-clocks/second convention. Memory speeds,
startup/runtime, separate translation units, emulator and measurement interval
match the baseline. Disabling this pass produces byte-identical assembly to the
frozen baseline compiler for both sample C units, using identical input paths.

| Category | X/Y baseline bytes | New bytes | Change |
| --- | ---: | ---: | ---: |
| Application and shared support code | 4,997 | 4,934 | -63 |
| Runtime code | 3,460 | 3,460 | 0 |
| Total linked code | 8,457 | 8,394 | -63 |
| Constants | 4,520 | 4,520 | 0 |
| Initialized data | 64 | 64 | 0 |
| Padded ROM | 65,536 | 65,536 | 0 |

The gradient shrinks 314 -> 275 bytes; main shrinks 3,010 -> 3,004 bytes. In the
gradient, all three `63-p` sequences become XOR, redundant `AND #$00FF` instructions
fall from 28 to 23, and A8 entries fall from seven to four. The three triangle
comparisons use word CMP without signed overflow handling. Shifts still use the
existing instruction chains, and the two HDMA byte stores remain separate.
The later [byte-shuffle and store changes](byte-shuffle-stores.md) cover those cases.

## Focused validation and evidence

The registered `known-values` part passes in selected, disabled, no-line-pass and
no-inline modes, with an MSVC host reference. It executes 256 opaque byte/word
vectors across private assignments, valid/invalid joins, inline chains, narrowing,
boolean conversion, signed comparisons/shifts, wrapping, loop backedges,
continue, short-circuit assignments, escaped locals and calls with global writes.
Assembly assertions require the intended XOR/compare choices and conservative
fallbacks. No existing test expectation was changed.

Existing focused parts passed: index-retention, indexed-operands, body-codegen,
inlining, arithmetic-regions, compare-constants, volatile and scalar-values.
These ran sequentially against one unchanged compiler binary. Scalar-values also
checks NTSC/PAL hardware and instruction-boundary software interrupts.

`build/known-values/results.json` records compiler/source/runtime hashes, frozen
baseline identity, matching staged-input hashes, disabled-pass controls, focused
results, code sizes, ROM hashes and repeated timing/state/pixel results.
`final-build/` retains staged C, assembly, maps and ROMs; `final-timing/` retains all
four sets of Lua scripts, expected states, logs and screenshots; `control/` retains exact assembly comparisons.

```text
cmd.exe /d /c tools\build-compiler.cmd
python tests/check-compiler.py --part known-values
```

Use fresh output paths and repeat the timing command for FastROM run 2 and SlowROM
runs 1/2. Earlier trial evidence is retained separately.
