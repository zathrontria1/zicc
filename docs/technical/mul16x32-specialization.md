# Word by long multiplication specialization

Multiplying a 32-bit number by a value that started as a 16-bit number needs just seven byte multiplications to get the low 32 bits. The compiler can use this shortcut even when the original 16-bit value was negative.

The new `__mul16x32` accepts a sign/zero-extended word in `__arith_lhs` and an
unrestricted long in `__arith_rhs`, returning the low 32 product bits in A/X.
Y, D, DBR and 16-bit register widths are preserved as in the existing helper ABI.
The arithmetic workspace and all public C types are unchanged.

Only seven byte products contribute: four from the word's low byte, and three
from its high byte, at offsets whose sum is below four. For a negative signed
word, subtracting the other operand's low word from the result's high word
accounts for sign extension. Equivalently, `(a - 65536)*b = a*b - (b << 16)`
modulo 2^32. This works for either signedness of the 32-bit operand and retains
signed-word conversion to unsigned long. Hardware result reads retain the
existing eight-CPU-cycle minimum wait sequence.

Selection follows cast provenance: a word widened to long qualifies; arbitrary
longs retain `__mul32`. Truncations and word signedness changes remain part of
the source value before extension. Either operand order is accepted, normalizing
the helper slots while preserving the existing expression evaluation order and
saving values across calls which may clobber scratch. Two proven words still
prefer the four-product `__mul16wide`. Shared struct-field expressions and the
counted-reduction selector use the same width distinction.

## Matched catalog measurement

The baseline is the counted reduction build with an eight-byte frame counter.
Source, startup, FastROM settings and linker layout match;
each compiler has two independent agreeing Mesen runs, return zero and balanced
stacks. Time spans main entry through its return, excluding startup/exit cleanup.

| Metric | General multiply | Word by long |
| --- | ---: | ---: |
| Main master clocks | 17,450 | 15,066 |
| Microseconds at 21.477272 MHz | 812.49 | 701.49 |
| inventory_value code bytes | 105 | 105 |
| Application code bytes | 359 | 359 |
| All linked code bytes | 1,635 | 1,836 |
| Used non-asset ROM bytes | 1,723 | 1,924 |
| inventory_value frame bytes | 8 | 8 |
| Hardware products per multiply | 10 | 7 |

Elapsed time drops 2,384 master clocks (13.66%). Four multiplication calls total
10,456 -> 8,032 profiled master clocks; individual new calls span 1,998-2,038.
The elapsed interval and per-function profiles are distinct measurements; their
differences need not distribute identically among unchanged functions.

The new helper occupies 201 bytes. The integer runtime is linked as one object,
so adding this helper retains the existing general helper and increases linked
code by all 201 bytes, including for integer programs which do not select it.
The C translation unit and frame sizes do not change. A control build using the
old compiler with the new runtime still takes 17,450 clocks, isolating the
execution improvement from merely adding/repositioning runtime code.
`__mul32` itself retains identical source body and all 256 machine-code bytes.

## Verification and evidence

The widened-product suite preserves its original deterministic vectors and adds
32-bit boundary operands. It checks 4,349 vectors / 113,074 top-level product
results, including word minima/maxima, negative values, full-width high words,
overflow, either order and signedness, calls on both sides, truncation and
signedness changes, and shared struct-field addresses. It verifies the 4/7/10
hardware-product counts, hardware latency and ABI, and requires general-width
expressions to retain the old helper. Counted-reduction signed/overflow/layout
tests also retain their on/off execution checks.

Saved baseline/candidate compilers and runtime objects, a runtime-only control,
assembly/maps/ROMs, commands, source/compiler/ROM hashes, repeated profiles,
`comparison.json` and full verification logs are in `build/mul16x32-trial/`.

Full `make check CHECK_OUTPUT=build/mul16x32-trial/full-check` passed all 27
logical suites / 76 jobs using the actual hardware default of 20 workers, in
52.11 seconds of verification time. All 200,873 arithmetic cases were retained.
Focused widened-products, shared-elements and struct-cursors checks also passed.
