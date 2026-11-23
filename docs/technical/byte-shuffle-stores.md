# Exact word shifts and adjacent RAM stores

To shift a 16-bit word by eight bits, the CPU can swap its two bytes and
mask off the byte it no longer needs. This report also covers when a single
16-bit write can replace two adjacent byte writes to RAM. The later
[analysis of private storage](private-regions.md) uses this build as its baseline.

The baseline included the homebrew sample imports, compatibility fixes, indexed
operands, X/Y retention and known-value selection. The first measurements used
focused verification.

## Selection

`src/word_shifts.inc` provides a shared costed plan for A16 expression emission
and `WordPlan`. It selects exact XBA/mask/shift sequences for constant word
shifts when cheaper than the ordinary chain:

- Arbitrary word `<<8`: `XBA; AND #$FF00`; logical `>>8`:
  `XBA; AND #$00FF`. Counts above eight add the remaining shifts.
- Proven zero upper byte permits `XBA; ASL; ASL` for `<<10`, and
  `XBA; LSR; LSR; LSR` for `<<5`. A proven zero low byte allows the corresponding
  short logical-right-shift form.
- Signed right shifts use these forms only when the input is proven
  nonnegative; other signed inputs retain arithmetic shifts.

XBA alone sets byte N/Z even in A16. Every selected sequence ends in a full-word
mask or shift, including count eight, so the emitter's word-flag contract remains
valid. A/X/Y widths and the index registers are unchanged. This does not alter
32-bit shifts or introduce lookup tables. `--no-byte-shuffles` independently
disables this selection.

`src/store_fusion.inc` recognizes two consecutive discarded byte assignments:
the low byte and high byte of the same unescaped, nonvolatile private word, in
that order, to adjacent bytes of named near RAM. It emits a single A16 STA.
It supports fixed offsets, bounded pure private indices and validated retained
X/Y displacements. The full two-byte span must fit inside the declared object;
wrapped/nonadjacent indices and unsafe register contexts fall back. No pointer
variable, escaped/global source, volatile access, MMIO write, intervening
observation, changed source or narrowing of the shift input is coalesced.

Address CSE preserves structurally eligible indexed store pairs instead of hiding
their base behind a pointer temporary. Actual range and object-boundary checks
still run at emission. This allows the general non-loop case as well as retained
loops. The two original memory writes still invalidate the relevant value caches.
`--no-store-fusion` independently disables both selection and this CSE deferral.

Both selectors are structural and typed; there are no sample/function names.
`--no-strength-reduction` disables both; `--no-body-optimizations` also disables
store fusion. Existing generic paths remain available.

## BouncingSprites measurements

The staged C, shared headers, assets, runtime sources, separate translation units,
ABI, ROM speeds, NTSC emulator settings and 600-logical-update measurement interval
match the known-value baseline. Disabling both new selectors reproduces
byte-identical assembly from its frozen compiler for both C units at identical
input paths.

Average work excluding startup and VBlank waiting:

| Build | Baseline clocks | Combined clocks | Combined ms | Fewer work clocks |
| --- | ---: | ---: | ---: | ---: |
| FastROM | 255,928.04 | 235,208.24 | 10.951495 | 8.10% |
| SlowROM | 304,283.20 | 279,555.70 | 13.016351 | 8.13% |

Two fresh runs per speed agree exactly. Both retain 600 logical updates in 600
physical frames. Including waits, both average 357,365.99 clocks / 16.639264 ms.
Maximum update work is 245,016 FastROM and 291,332 SlowROM clocks. Milliseconds use
21,477,272 master clocks per second.

| Selection | FastROM work clocks | SlowROM work clocks | Linked code bytes |
| --- | ---: | ---: | ---: |
| Baseline | 255,928.04 | 304,283.20 | 8,394 |
| Shifts only | 247,402.59 | 294,352.09 | 8,374 |
| Stores only | 240,186.09 | 285,469.77 | 8,368 |
| Combined | 235,208.24 | 279,555.70 | 8,352 |

The independent gains overlap: store fusion removes a high-byte extraction that
shift selection also shortens. Component variants compile the same two C units
with one selector disabled, then use the existing allocator's assembly-input API.
The same runtime inputs and ROM-speed finalization are retained; runtime code
remains 3,460 bytes in every variant. The retained component build driver is
`build/byte-shuffle-stores/build-components.py`.

Combined application/shared code shrinks 4,934 -> 4,892 bytes, saving **42 bytes**.
Constants remain 4,520 bytes, initialized data 64 bytes and padded ROM 65,536 bytes.
Gradient shrinks 275 -> 241 bytes; main remains 3,004 bytes. Its two color shifts
use XBA forms and its two HDMA byte assignments become `STA hdmaTable+3,X`, with
no byte-width store regions or high-byte extraction. Arithmetic temporaries and
other broader frame/collision overhead remain.

All twelve captures (two repeats, two speeds, three selections) match every
update's expected positions, velocities, OAM shadow, HDMA table and phase. State
sequence SHA-256 remains
`0bad2bb9b559eb75c14a74746e26f6122a74175e2d3291d8deb1742b5576fd1d`.
Every final screenshot matches baseline pixels, RGB SHA-256
`31f30fb3c18a97acbb3e58b3b7d8341e3289865420afda2a34fff77933192b5a`.

## Verification

The full cached `make check` passes **27/27 suites** with the default 20 workers
in 78.27 seconds: 1,357 cached and six fresh emulator runs. Evidence is
`build/check/20261108T105312.860393Z/summary.json` and adjacent logs. All 200,873
arithmetic cases and existing assertions remain. This full run uses the exact
compiler binary measured above; no source edits/rebuilds occurred during it.

Two new registered compiler parts pass:

- `byte-shuffles`: all 16 shift counts over 48 opaque boundary/pseudorandom words,
  2,304 shift results per mode, additional known-bit cases, signed fallbacks and
  full-word zero/sign predicates. Modes: selected, disabled, no-line-pass and
  no-known-values. Expected bit patterns are generated independently in Python.
  The MSVC host reference uses /Od: the installed /O2 incorrectly folds the
  signed-short left-shift predicate for input $0080; /Od gives the expected result.
- `store-fusion`: 256 opaque words with varying low/high bytes; fixed, dynamic,
  retained and end-of-object stores; explicit rejection of pointer/global/escaped
  sources, observations, reversed/gapped/different-source stores, narrowed shift
  inputs, wrapping, volatile RAM and MMIO. Modes: selected, disabled, no-line-pass,
  no-retention and no-byte-shuffles. An MSVC host reference also passes.

The full check above also passes the updated interrupt scratch contract.

## Evidence and reproduction

`build/byte-shuffle-stores/results.json` records compiler/source/runtime hashes,
baseline identity, disabled-pass controls, full-check identity, component sizes,
matching input hashes, ROM hashes, repeated timings and state/pixel hashes.
`final-build/`, `shifts-only/` and `stores-only/` retain staged sources, assembly,
maps and ROMs; their `timing-*` directories retain all twelve captures. `control/`
retains exact baseline/disabled assembly comparisons. Earlier trials are retained.

```text
cmd.exe /d /c tools\build-compiler.cmd
python tests/check-compiler.py --part byte-shuffles
python tests/check-compiler.py --part store-fusion
make check
```

Use fresh paths and repeat profiling for FastROM run 2 and SlowROM runs 1/2.
