# Implemented compiler optimizations

When zicc sees `(9 + 3) * 4`, it can put `48` straight into the ROM. The
SNES gets the same answer and skips the arithmetic. That's one example of an
optimization. The examples below show when zicc can take a shortcut and
which instructions the SNES can then skip.

Assembly examples show the important instructions, leaving out surrounding
setup and cleanup. Actual output also depends on types, surrounding code and
other optimizations. Here, `int` and `unsigned` are 16 bits and `long` is 32 bits.
Unless shown otherwise, the accumulator and index registers are 16 bits.

In the conditions below, **private** means a local value whose storage cannot be
accessed through another pointer or function. A value is **live** while later
code may still read it.

Quick navigation: [values](#values-and-control-flow),
[arithmetic](#arithmetic-and-comparisons), [memory](#memory-accesses-and-copies),
[loops](#loops-and-induction), [frames](#registers-frames-and-private-storage),
[calls](#calls-banks-and-whole-program-selection),
[final assembly](#final-assembly-and-code-layout),
[caller and instruction checks](#shortcuts-found-from-callers-and-final-instructions).

## Values and control flow

### Constant folding and refolding

Evaluate integer literal arithmetic, casts and conditions during compilation,
including constants exposed by propagation.

```c
return (9 + 3) * 4;
```
```asm
lda #$0030
rts
```

Conditions: supported integer operators and conversions; signed overflow is not
invented, and effectful operands still execute. [Details](technical/optimization-catalog.md#frontend-and-typed-ir).

### Dominating private copies and constants

Replace immutable local copies with their source and remove unnecessary homes.

```c
unsigned f(unsigned x) { unsigned a = x, b = a; return b + 3; }
```
```asm
txa                       ; x arrives in X
clc
adc #$0003                ; no a/b frame homes
```

Conditions: dominating definitions, private unescaped destinations, stable
sources and preserved conversions. [Details](technical/scalar-values.md).

### Single-use computed temporary forwarding

Move a private calculation into its next consumer without duplicating work.

```c
unsigned t = x + 3;
return t ^ 7;
```
```asm
; A = x
clc
adc #$0003
eor #$0007                ; no t store/reload
```

Conditions: one definition/use, pure immutable operands and the next executable
consumer; calls and intervening effects block forwarding. [Details](technical/computed-stores.md).

### Structured facts, dead branches and dead private stores

Propagate compatible facts through blocks and branch joins; remove private
definitions that have no observable use while retaining effectful RHS work.

```c
if (flag) x = 4; else x = 4;
return x + 1;
```
```asm
lda #$0005                ; when the assignments/condition are eliminable
rts
```

Conditions: bounded structured analysis and unescaped private objects; mutations,
aliases and effects invalidate facts. [Details](technical/structured-codegen.md).

### Dominated named-value reuse

Evaluate a repeated eligible array read once at its original execution site.

```c
a = table[i];
b = table[i] + 1;
```
```asm
lda a:_table,x            ; X already holds the scaled i
sta z:cached
; later: use cached instead of loading table[i] again
```

Conditions: pure stable index, eligible named byte/word storage and no intervening
write/call/alias invalidation; mutable-array reuse has stricter version checks.
[Details](technical/value-reuse.md).

### Comparison reuse and proven predicates

Reuse a dominating comparison or its proven truth instead of retesting it.

```c
if (x < limit) { a = x + 1; if (x < limit) b = x + 2; }
```
```asm
; A = x
cmp limit
bcs done
; calculate a and b without a second comparison
```

Conditions: neither calculation changes x or limit, and no intervening call or
aliasing write invalidates the comparison. [Details](technical/value-reuse.md).

### Known bits, ranges and demanded masks

Track possible values and bits through casts, operations and conditional joins;
remove redundant masks and choose narrower operations.

```c
unsigned f(unsigned char p) { return ((p & 255) + 42) & 63; }
```
```asm
; A = already normalized p
clc
adc #$002A
and #$003F                ; the earlier AND #$00FF is unnecessary
```

Conditions: explicit typed proofs and consumer demands, not observed benchmark
values; narrowing, signedness and needed flags are preserved.
[Details](technical/known-values.md), [mask cleanup](technical/arithmetic-regions.md#scalar-control-flow).

### Per-cell and relational range propagation

Use dominating source clamps and min/max relationships to simplify later
coordinate arithmetic and comparisons.

```c
if (x[i] < 0) x[i] = 0;
else if (x[i] > 240) x[i] = 240;
/* eligible later operations on this same cell */
```
```asm
; a later bounded signed comparison can omit overflow repair
cmp a:_bound,x
bmi less
```

Conditions: proven cell identity, bounds, source control flow and unchanged
memory versions. Partial clamps, aliases and loop exits weaken the proof.

### Shared-predicate private selections

Select several private results with one unchanged predicate.

```c
maxx = flag ? 192 : 240;
maxy = flag ? 160 : 208;
```
```asm
; A = flag
beq small
lda #192
sta maxx
lda #160
sta maxy
; small path selects 240 and 208
```

Conditions: adjacent eligible assignments, pure matching predicates/arms and
private destinations; the first assignment cannot change the next predicate.

## Arithmetic and comparisons

### Direct ALU operands and word-expression planning

Use immediate/home/fixed-element operands directly, schedule pure word trees
into A and reuse short-lived DP temporaries rather than staging every subtree.

```c
return a + b * 2;
```
```asm
; A = b, X = a
asl a
stx z:__arith_lhs
clc
adc z:__arith_lhs
```

Conditions: supported pure word arithmetic/bitwise/constant-shift trees and a
successful bounded plan; grouping and subtraction roles remain intact.
[Details](technical/word-expression-optimization.md).

### Costed constant multiplication

Replace cheap word products with shifts, additions, subtraction or negation.

```c
return x * 5;
```
```asm
; A = x
sta z:__arith_rhs
asl a
asl a
clc
adc z:__arith_rhs
```

Conditions: a constant word coefficient and an accepted costed recipe; the
operand executes once, even for zero. Expensive products retain helpers.
[Details](technical/word-expression-optimization.md#general-selection-rules).

### Width-specific multiply/divide helpers

Choose byte, mixed-width, word or wide arithmetic from types and proven bounds.

```c
unsigned f(unsigned char a, unsigned char b) { return a * b; }
```
```asm
sta f:$004202             ; write the first byte
; load the second byte
sta f:$004203             ; start the multiplication
; wait for the product and restore the word width
lda f:$004216             ; read the word result
```

Both operands must fit in unsigned bytes for this sequence. The compiler
can evaluate an operand that also uses the hardware before programming the
registers for the outer multiply. A product of two ordinary global bytes
outside a loop can call `__mul8`. When just one operand fits a byte, zicc can
select `__mul8x16` or `__mul16x8`. A known byte divisor also enables the
hardware division path. [Details](technical/word-call-optimization.md),
[mixed widths and runtime paths](technical/arithmetic-regions.md).

### Signed-byte dot products

A loop can use the SNES byte multiplier for a sum such as
`x[i] * a + y[i] * b`. The hardware multiplies unsigned bytes. zicc prepares
the signs and magnitudes of the coefficients before the loop, adjusts each
input byte, and adds a correction to recover the signed sum. The repeated
work uses the hardware multiply registers at `$4202`, `$4203`, and `$4216`.

The inputs must be supported signed-byte loads. Each coefficient must be a
private signed word that stays constant throughout the loop, with values
proven to lie from -255 through 255. The compiler must also be able to form
the addresses without losing a partial sum. [Selection rules](../src/codegen/dot_products.inc).

### Widened word products and word-by-long multiplication

Avoid a generic 32-bit product when one operand is still a word.

```c
unsigned long f(unsigned a, unsigned long b) { return (unsigned long)a * b; }
```
```asm
; staged word/wide operands
jsr .loword(__mul16x32)
```

Conditions: recognized widening and operand-width semantics; signed word
extensions retain their required correction. [Details](technical/widened-product-optimization.md),
[word-by-long specialization](technical/mul16x32-specialization.md).

### Native wide ALU and constant-shift selection

Operate on low/high words directly instead of invoking a generic helper where
the operation has a bounded inline sequence.

```c
return value + 1UL;
```
```asm
; A = low, X = high; low result is temporarily protected
clc
adc #1
pha
txa
adc #0
tax
pla
```

Conditions: supported integer operations, preserved carry and operand order;
wide shifts handle surviving words and sign fill explicitly.
[Details](technical/operations.md#expressions).

### Exact byte-shuffle word shifts

Use XBA plus masks and a few shifts for cheaper constant word shifts.

```c
return x << 8;
```
```asm
xba
and #$FF00
```

Conditions: word-width operation and a cheaper exact plan. Known-zero bits can
remove masks, including short forms for byte-bounded shifts by five or ten.
[Details](technical/byte-shuffle-stores.md#selection).

### Division and remainder by a power of two

For unsigned `x / 4U`, two right shifts give the quotient. For `x % 4U`,
`and #$0003` keeps the two remainder bits. The compiler recognizes constant
powers of two for both 16-bit and 32-bit integers. Signed division needs
extra work when the input can be negative. For example, C requires
`-7 / 4 == -1` and `-7 % 4 == -3`. The signed path handles the sign before
returning the result, including when the divisor is negative.
[Implementation](../src/codegen/word_shifts.inc).

### Looking up a bounded expression

Consider `0x0101U * (0xFFU >> (a & 7U))`. There are only eight possible
results. The compiler can work them out once and emit a ROM table. At run
time it masks `a`, doubles it for a word table, and reads the answer with
`lda f:table,x`. Results that all fit in a byte can use byte entries.

This applies to supported word arithmetic with a variable shift, one input
bounded within 0 through 15, and no calls, writes, or volatile reads. Every
possible shift must be valid. If every possible input gives the same answer,
the compiler emits that constant directly. For other variable word shifts,
it can shift a word in a counted loop. [Selection rules](../src/codegen/word_shifts.inc)
and [tested expressions](../tests/check-word-expressions.py).

### Quotient/remainder reuse

One integer division produces both a quotient and a remainder. If the same
inputs reach a later calculation, zicc can keep both results in the current
call's stack frame. This works for signed and unsigned 16-bit and 32-bit
integers.

```c
q = value / divisor;
r = value % divisor;
```
```asm
jsr .loword(__udiv16)
sta quotient_slot,y
lda z:__arith_lhs+8       ; the helper also produced the remainder
sta remainder_slot,y
; later, reload the saved result for the matching expression
```

The first division must run on every path to the reuse. Writes to an input,
unknown pointer writes, and calls invalidate the saved pair. In a suitable
loop with an unsigned byte divisor, zicc can read both outputs of the SNES
hardware divider. A divisor range that straddles 255 can use a runtime test
and fall back to the word helper. [Implementation](../src/codegen/divmod.inc)
and [paired division checks](../tests/check-divmod.py).

### Direct word comparisons and branch flags

Branch on comparison flags without materializing a Boolean or using a helper.

```c
if (u < limit) action();   /* unsigned word operands */
```
```asm
; A = u
cmp limit
bcc action
```

Conditions: compatible typed operands. Signed order uses overflow-correct
lowering unless bounds justify a simpler form; zero and constant comparisons
have specialized paths. [Details](technical/operations.md#word-comparisons-and-condition-flags).

### Min/max and fused selection subtraction

Keep the selected operand in A and combine compatible selections directly.

```c
v = a < b ? a : b;
```
```asm
; A = a; bounded signed example
cmp b
bmi selected
lda b
selected:
```

Conditions: pure matching test/arms; CMP/N signed order additionally needs a
non-overflow proof. Unsigned/same-sign selection and paired min/max subtraction
have their own safe paths; value flags are repaired when needed.

For a one-bit choice such as `(flags & 0x0100U) ? 1 : 0`, zicc can move that
bit into position with `xba` and use `and #1`. The reverse choice adds
`eor #1`. This path recognizes word masks 1, 2, 4, 256, 512, 1024 and 32768,
requires opposite literal results of 0 and 1, and evaluates the input once.
[Bit selection](../src/codegen/selections.inc).

### Shifts and products on eight-byte integers

The processor works on two bytes at a time. For the unsigned 64-bit expression
`(u >> 16) | (u << 48)`, the result is the same four words in a different
order. When both reads come from the same fixed, nonvolatile object, zicc
loads the four words in that order. For a rotate that falls between word
boundaries, it moves whole words first, then rotates the remaining bits
through carry. A signed right shift also has to fill the high bits from the
original sign. A plain shift by a whole number of words can skip the bit loop.

For `(long long)x * y` with two signed 32-bit inputs, zicc can use
`__smul32wide`. This helper takes the original 32-bit operands and produces
the full eight-byte result. In a loop, a 64-bit index with known bounds that
fit one word can be tested and incremented using only its low word. A loop
that only works on narrow values can also use the ordinary loop selectors
inside a function that does other work on 64-bit values.
See the [instruction selector](../src/codegen/codegen.inc)
and [64-bit code generation checks](../tests/check-int64-codegen.py).

### Comparing floats with constants

For a branch such as `if (temperature > 1.0f)`, zicc can first compare the
upper word of a stored 32-bit float. It reads the lower word when needed to
settle a tie or distinguish infinity from a NaN. Equality against a finite,
nonzero constant also starts with the high word. These shortcuts require a
fixed, nonvolatile operand. Strict comparisons against zero account for both
signed zeros and values smaller than the smallest normal float.

Converting a large integer to float can round to either of two neighboring
values. When the integer and comparison bound are both literals, zicc can
compare both possibilities at compile time. It still sets the sticky inexact
flag when the conversion loses bits. If the answers differ, ordinary code
reads the active rounding mode. For a small ROM whose application instructions
and runtime imports prove that rounding always stays at its default, the ROM
builder can recompile that comparison with its answer already known. Added
assembly, console or input support disables that whole-ROM shortcut.
See the [selector](../src/codegen/codegen.inc), [builder](../tools/build-rom.py)
and [floating-point runtime checks](../tests/check-ieee64-runtime.py).

### Direct wide equality

Compare the two words of a wide integer directly when a comparison helper is
unnecessary.

```c
if (value == 0x12345678UL) action();
```
```asm
; A = low word, X = high word
cmp #$5678
bne different
cpx #$1234
beq equal
```

Conditions: eligible equality operands and correct type conversion; ordered
wide and floating comparisons keep their appropriate comparison paths.
[Details](technical/operations.md#word-comparisons-and-condition-flags).

### Byte comparisons and short-circuit predicates

Compare eligible promoted bytes in A8 and branch directly through `&&`/`||`.

```c
if (a[i] != 0 && b[i] < 10) action(); /* unsigned-byte arrays */
```
```asm
sep #$20
lda a:_a,x
beq false_path
lda a:_b,x
cmp #10
; selected paths restore A16 before leaving the byte region
```

Conditions: compatible byte proofs or selected byte-loop grammar; mixed
signedness, needed wide values and volatile contracts retain appropriate
fallbacks. [Details](technical/operations.md#short-circuit-byte-predicates-and-exit-values),
[promoted byte relations](technical/scalar-values.md).

### Using carry for overflow checks and bit tests

For unsigned words, `a <= 65535u - b && limit > a + b` asks whether the sum
fits and lies below `limit`. zicc can add once and branch on carry if it
overflows. Only when the sum fits does it evaluate the remaining comparison.
The pattern requires matching operands and expressions with no side effects.

A shift also leaves the bit it just removed in carry. For a 32-bit unsigned
value, zicc recognizes `if (x & 1) x = (x >> 1) ^ mask; else x >>= 1;`
with a constant mask. It can shift once and use carry to decide whether to
apply the XOR. In another pattern, three or four independent tests set
successive bits in a private word initially set to zero. When their inputs
can be read in reverse order, the compiler can rotate each comparison's carry
bit into the result. See the [instruction selector](../src/codegen/codegen.inc),
[overflow guard checks](../tests/check-banked-rom.py) and
[shift checks](../tests/check-known-values.py).

A read-only byte table offers another short-circuit shortcut. In a test like
`table[i] != 0 && table[i] != table[i - 1]`, zicc can keep the first byte in
A and fetch the previous byte only if needed. This requires the same immutable
table and a private unsigned word index.

### Demanded words of wide homes

Load only a demanded low word or a high word selected by unsigned `>>16`.

```c
unsigned low(unsigned long x) { return (unsigned)x; }
```
```asm
lda 3,s                   ; selected stack-home leaf; no high-word load
rts
```

Conditions: fixed nonvolatile 32-bit homes and representation-preserving cast
chains; Boolean/float conversions and volatile sources retain normal lowering.

## Memory accesses and copies

### Direct named-array and field operands

Keep a fixed near base in the instruction and compute only its displacement.

```c
return words[i] + 3;
```
```asm
; X = 2*i
lda a:_words,x
clc
adc #3
```

Conditions: eligible named near byte/word objects, pure address structure and
valid fixed offsets; general pointers, wide/float and volatile transfers keep
their established paths. [Details](technical/direct-indexed-operands.md).

### Smaller read-only record tables

A file-private ROM table can sometimes use one byte per field even when the
C program declares the field as a 16-bit integer.

```c
struct Point { int x, y; };
static const struct Point points[] = {{-2, 3}, {4, -5}};
int get_y(unsigned i) { return points[i].y; }
```

Here each record can take two ROM bytes instead of four. A read extends the
signed byte back to the declared integer type. The compiler checks **each
field across all rows**. A signed field must fit from -128 through 127, and
an unsigned field must fit from 0 through 255. Wider fields keep their two
bytes and alignment. The new record must actually be smaller.

The compiler must see the full initializer and every use. It accepts direct,
nonvolatile member reads. Taking a record's address, exposing a pointer from
another initializer, or copying the whole record prevents the change.
[Implementation](../src/codegen/narrow_rodata.inc).

### Shared element addresses and near-address CSE

Form one pure struct/array address for several accesses with fixed offsets.

```c
p[i].x = a;
p[i].y = b;
```
```asm
; X = address of p[i], formed once
lda a
sta a:$0000,x
lda b
sta a:$0002,x
```

Conditions: identical stable address dependencies, supported widths and no
intervening invalidation; payload accesses and alias-sensitive reloads stay in
source order. [Details](technical/shared-element-addresses.md),
[straight-line address reuse](technical/structured-codegen.md).

### Named ROM and indexed far loads

Use long addressing for fixed ROM bases and indexed long-indirect forms for
eligible far pointers.

```c
return rom_bytes[i];       /* banked constant byte array */
```
```asm
; X = byte index
lda f:_rom_bytes,x
and #$00FF
```

Conditions: recognized banked object/index and exact result width; general far
arithmetic retains 24-bit carry and near-pointer wrap is not changed.

### Reading consecutive ROM words into a RAM buffer

When the same pair of pointers supplies several rows, the compiler can keep a
far source address and a near destination address ready for the next row.

```c
row = src[0]; dest[64] |= (row >> 1) & 0x7f7f; dest[66] = (row & 0x0101) << 7;
row = src[1]; dest[65] |= (row >> 1) & 0x7f7f; dest[67] = (row & 0x0101) << 7;
```

The fast path reads a source word once and uses it for both stores. It
accepts two through eight consecutive source words, fixed destination
offsets, supported masks or shifts, and nonvolatile accesses through private
pointers. A check on the destination chooses the wrapping path if an indexed
store could cross the near-address boundary. Known source and destination
arrays can use their labels directly. Suitable switch cases can share the
wrapping path. [Implementation](../src/codegen/word_rows.inc),
[test source](../tests/far_loop_kernels.c), and [assembly checks](../tests/check-far-loops.py).

### Direct-page pointer and bank-zero accesses

Use hardware DP modes when storage placement and address interpretation prove
them valid.

```c
unsigned char * __dpage p;
value = *p;
```
```asm
lda (_p)
and #$00FF
```

Conditions: a genuine static DP pointer; far forms use `[p]`/`[p],y`. Separate
bank-zero indexed selection requires an actual bank-zero proof, not merely a
near WRAM pointer. [Details](technical/dpage-pointer-access.md),
[placement/addressing rules](technical/operations.md#machine-and-storage).

### Fixed far-address transfers

Access a known far address directly instead of constructing an indirect pointer.

```c
*(volatile unsigned char * __far)0x004200UL = 0x80;
```
```asm
lda #$0080
sep #$20
sta f:$004200
rep #$20
```

Conditions: a recognized constant address and transfer width. Volatile accesses
keep their required width and order; this does not authorize combining MMIO
writes.

### Small near-pointer offsets

Use wrapping index-register steps instead of a full address addition.

```c
return *(p + 1);           /* near byte pointer */
```
```asm
; X = p
inx
lda a:$0000,x
```

Conditions: supported small displacement and near-pointer representation;
16-bit wrap must not become a far bank carry.
[Details](technical/structured-codegen.md).

### Scalar home and native memory updates

Update a direct home without general destination-address/result staging.

```c
counter++;                /* discarded nonvolatile word result */
```
```asm
inc counter
```

Conditions: supported direct/fixed near homes, correct old/new value requirements
and dead A where an assembly rewrite replaces LDA/INC/STA. Compound operations
use direct ALU operands; byte updates use guarded A8 regions.
[Details](technical/scalar-home-updates.md), [region RMW](technical/arithmetic-regions.md#private-values-and-frame-homes).

### Pure RHS before an A-preserving destination load

Compute a value first and then load the store address into X without saving A.

```c
next->value = current->value;
```
```asm
ldx current_home
lda a:$0006,x
ldx next_home
sta a:$0006,x
```

Conditions: pure source, eligible near destination and an X-load path that
preserves A; calls, volatile accesses and general address calculations fall back.

### Updating one packed bit-field

Suppose `flags.ready` is a one-bit field in a word shared with other fields.
For the standalone statement `flags.ready = 1;`, zicc can load the word,
set just that bit with `ORA` and store it back. A zero uses `AND` to clear
the bit. An assignment to a wider field can use both masks. For an update
such as `flags.count += n;` on a fixed word, the compiler can add in place
and mask the result so a carry cannot change the next field. These cases
require a discarded assignment result and nonvolatile field accesses. See
the [bit-field selector](../src/codegen/codegen.inc).

### Adjacent RAM byte-store fusion

Combine neighboring low/high stores of one value into one word store.

```c
bytes[k] = (unsigned char)v;
bytes[k + 1] = (unsigned char)(v >> 8);
```
```asm
; A = v, X = k
sta a:_bytes,x
```

Conditions: same proven destination/value, adjacent in-bounds nonvolatile RAM
bytes, preserved evaluation and safe alias relationships. MMIO is excluded.
[Details](technical/byte-shuffle-stores.md).

### Retained-index byte regions

Share byte-index conversion and accumulator-width changes across eligible
copies, swaps, negations and sign actions.

```c
t = velocity[i]; velocity[i] = velocity[j]; velocity[j] = t;
```
```asm
; after saving/rebasing the retained offsets to byte indices
sep #$20
lda a:_velocity,y
sta temporary
lda a:_velocity,x
sta a:_velocity,y
lda temporary
sta a:_velocity,x
; restore A16 and the saved scaled index registers
```

Conditions: proven private byte temporaries, supported consecutive operations
and correctly owned/saved X/Y bindings.

### Costed aggregate copies and discarded aggregate results

Select inline, loop or guarded MVN copying, and omit an unused result address.

```c
*destination = *source;    /* compatible nonvolatile structures */
```
```asm
; selected near MVN core: X=source, A=destination, N=copy size
phy
tay
lda #N-1
mvn #$7E, #$7E
ply
```

Conditions: copy size, address/bank/span and cost proofs. Runtime guards retain
fallbacks; padding, overlapping-copy rules, observable results and volatile byte
order remain correct.
[Copy policy](technical/operations.md#structure-and-union-assignment).

### Passing and returning small records

When a function returns a struct, its caller supplies the destination address.
A function that fills a local record with constants and returns it can write
those constants directly to that address. This handles even sizes from two
through eight bytes when every member byte is supplied. If the function
instead copies each member of the same by-value parameter in declaration
order, zicc can return that parameter directly. Neither shortcut applies to
unions, volatile objects, arrays as members or bit-fields.

For a by-value call argument, an eligible record of up to twelve bytes can go
straight onto the stack in short pushes. For a larger, directly addressed
near-RAM record, the compiler can reserve the stack space and copy the bytes
there with the processor's `MVN` block move. See the
[copy and return selectors](../src/codegen/codegen.inc).

### Short fills and plain format strings

For `memset(p, 0x5a, 5)`, the compiler can load `#$5A5A`, store two words
and write the one remaining byte. A runtime fill value is evaluated once and
stored byte by byte. This shortcut needs the standard near `memset`
declaration, a constant length from 1 through 8, and a call outside an
interrupt handler. The result, when used, is still `p`.

For `sprintf(p, "OK")`, the compiler can store the word `#$4B4F`, write the
terminating zero and return 2. It requires the standard external declaration,
a near destination, and a literal format of at most 15 characters before
the first zero. A percent sign before that zero, extra arguments, or volatile
operands prevent the shortcut. Both selections honor `--no-copy-selection`.
[String and fill implementations](../src/codegen/aggregate_copy.inc) and [library checks](../tests/check-libc.py).

### Literal strcpy selection

Replace eligible standard-library copies with a known-length inline or guarded
MVN transfer, including the first NUL.

```c
strcpy(destination, "OK");
```
```asm
; X = evaluated near destination; representative inline stores
sep #$20
lda f:literal+0            ; 'O'
sta a:$0000,x
inx
lda f:literal+1            ; 'K'
sta a:$0000,x
inx
lda f:literal+2            ; NUL
sta a:$0000,x
; restore A16; retain the original destination if the result is used
```

Conditions: standard compatible declaration, direct literal source and an
accepted cost plan; custom definitions and unknown/volatile contracts fall back.
[Details](technical/literal-copies.md).

## Loops and induction

### Running array and structure pointers

Calculate an element address before the loop, then advance it by the element
size instead of multiplying the index on every iteration.

```c
for (i = start; i < count; ++i) total += records[i].value;
```
```asm
; X = current record address
lda a:$0002,x
; consume value, then advance a record of eight bytes
txa
clc
adc #8
tax
```

Conditions: a predictable index step and unchanged base/stride. The compiler
keeps the C index when the program still needs it. Nested arrays and structure
fields use their actual layout. [Details](technical/affine-array-loops.md),
[structure cursors](technical/struct-loop-cursors.md).

Two stores of the same literal word can share their loop setup. In
`for (i = 0; i < end; ++i) { a[i] = 7; b[i] = 7; }`, the compiler can put
the two near addresses in X and Y, write each in source order, then advance
both by the same byte stride. This path checks the unsigned bound, requires
a private index with no uses after the loop, and skips both stores when the
initial index is already at or above the bound.
[Paired stores](../src/codegen/affine_loops.inc).

### Retaining loop indices in X/Y

Keep frequently used array offsets in registers across iterations.

```c
for (i = 0; i < 10; ++i) { x[i] += 1; y[i] += 2; }
```
```asm
; word-array offsets remain in X
inc a:_x,x                 ; representative word update
; update y[i]
inx
inx
```

Conditions: eligible bounded loops with private counters and compatible
register use. A scalar counter or second stride can use Y when frame access
does not need it. [Details](technical/loop-index-retention.md).

### Retaining an outer index across an inner loop

Let the inner loop use X while the outer loop keeps its offset in Y.

```c
for (i = 0; i < 10; ++i)
    for (j = i + 1; j < 10; ++j) { x[i] += y[j]; y[j] += x[i]; }
```
```asm
; Y = 2*i and X = 2*j
lda a:_y,x
clc
adc a:_x,y
sta a:_x,y
; advance X; retain Y for the next inner-loop entry
```

Conditions: a supported two-level bounded nest, unchanged outer counter and
compatible strides; inner setup, body and exits must preserve Y.

### Terminating on the array offset alone

Remove a separate loop counter when only the array offset is needed.

```c
for (i = 0; i < 56; ++i) { bytes[i*5+3] = 0; bytes[i*5+4] = 1; }
```
```asm
ldx #0
loop:
; stores at offsets from X
txa
clc
adc #5
tax
cpx #280
bcc loop
```

Conditions: no remaining scalar use of the counter, no needed final value and
a scaled bound that cannot wrap. Constant starts are folded into the initial
X load.

### Eliminating or recovering an induction variable

Stop updating the original C index when a running pointer or countdown already
contains enough information. Recover its final value only if needed.

```c
for (i = 0; i < count; ++i) destination[i] = value;
```
```asm
; store through the running pointer
dec remaining
bne loop                   ; no separate i++ inside the selected loop
; recover i here if a later C statement uses it
```

Conditions: a supported loop and a proof that index removal/recovery preserves
zero trips, exits and wrap behavior. Fully unrolled loops can also lose unused
index and cursor homes. [Details](technical/frame-home-cleanup.md),
[loop counters](technical/dp-loop-counters.md).

### Replacing index tests with cursor tests

Test a running pointer against its base or stop address instead of maintaining
an otherwise unused index solely for the loop condition.

```c
while (j > 0) { /* eligible accesses using data[j] */ --j; }
```
```asm
; a selected cursor tracks data + stride*j
cpx #.loword(_data)
beq done
```

Conditions: the index's entire range and updates are proven, scaling cannot
create a false sentinel match, and no other observation needs its home.
[Details](technical/optimization-catalog.md#loops-and-addresses).

### Saved direct-page countdowns

Borrow the fast word at DP address zero for an eligible loop's remaining count.

```c
for (i = start; i < bound; ++i) action();
```
```asm
; after the entry test: save the borrowed word and set bound-start
pei ($00)
; initialize $0000, then execute the body
dec z:$0000
bne loop
; restore the borrowed word on exit
```

Conditions: a private word counter and stable bound with a supported step and
exit shape. Borrowing is saved/restored locally, including nested callers.
[Details](technical/dp-loop-counters.md).

### Byte-bounded action-loop countdowns

Replace repeated upward comparison in loops whose bodies do not inspect the
index; retain the final C value when required.

```c
for (i = 0; i < limit; ++i) action(); /* limit is proven byte-bounded */
```
```asm
; after checking the range and initializing a remaining count
dec remaining
bne loop
```

Conditions: private unchanged index/bound, proven byte bounds, and no exits or
body reads of the index. Potentially wrapping word loops are excluded.
[Details](technical/arithmetic-regions.md#scalar-control-flow).

### Descending arithmetic loops in registers

Keep index-minus-one in X and, when useful, an affine scalar in Y while ordinary
arithmetic lowering handles the body.

```c
for (i = 32; i > 0; --i) { /* eligible arithmetic using bytes[i-1] */ }
```
```asm
ldx #31
loop:
; use byte array operands indexed by X
dex
bpl loop
```

Conditions: a bounded positive start, supported straight-line body and compatible
register/helper use. Array bounds and final scalar values must remain valid.
[Details](technical/arithmetic-regions.md#register-resident-arithmetic-regions).

### Byte loops in registers and A8

Keep byte cursors and temporary values in registers, and switch accumulator
width once around a suitable loop.

```c
while ((*destination++ = *source++) != 0) { }
```
```asm
; representative near-pointer loop: X=destination, Y=source
sep #$20
loop:
lda a:$0000,y
sta a:$0000,x
inx
iny
cmp #0
bne loop
rep #$20
```

Conditions: the supported byte-loop operations, no conflicting calls/escapes,
and correct cursor/temporary lifetimes. Counted loops, byte arithmetic and
short-circuit predicates also have selected forms.
[Details](technical/operations.md#register-loops-and-accumulator-width).

### Filtering, copying and filling byte arrays

For `image[slots[i] * 4 + 1] = backup[i]`, a loop with a stable bound can
keep the word index in X or Y while it reads and writes bytes in A. A second
register can hold a useful scaled index. The compiler checks the loop's
updates, branches, array accesses and bound. A write through an unknown
pointer that could change the bound prevents this choice. [Byte-loop tests](../tests/check-structured-byte-loops.py).

For a fixed forward copy, two bytes at a time fit in a single word load and
store. In the example below zicc copies six words and one final byte. When
`i` is read afterward, its value is still 15.

```c
for (i = 2; i < 15; ++i)
    small[i] = image[500 + i];
```

The source and destination must fit inside known objects, the byte ranges
must be disjoint, and the count must fit the full-unroll limit. For a fill
such as `bytes[i] = 0x5a`, the compiler can load `#$5A5A` once and write
it to each pair of bytes. The fill also requires known bounds and
nonvolatile byte storage. [Copy rules](../src/codegen/byte_loop_regions.inc)
and [fill rules](../src/codegen/index_retention.inc).

### Combining independent loops

Two adjacent loops that count through the same values can share one counter
and one end test.

```c
for (unsigned i = first; i < end; ++i) small[i] = image[i];
for (unsigned j = first; j < end; ++j) other[j] = tags[j];
```

Here all four arrays are distinct. The compiler proves that interleaving the
two bodies preserves every observed value. If the second loop reads a value
the first loop writes on a later trip, the two traversals must stay separate.
Matching tests inside combined loops can also share a branch when the first
body cannot change the test. A small private helper may be inlined to bring
both loops into the same function. [Fusion rules](../src/codegen/loop_fusion.inc)
and [positive and negative tests](../tests/check-structured-byte-loops.py).

### Far byte loops and shared indexed far bases

Advance far pointers without rebuilding a four-byte address on every access.
Compatible far bases can share a Y displacement while a near cursor uses X.

```c
while ((*near_destination++ = *far_source++) != 0) { }
```
```asm
; source is a far base in DP; X is the near destination
sep #$20
loop:
lda [source],y
sta a:$0000,x
; test the byte, then advance X/Y; maintain the far base on Y wrap
```

Conditions: supported call-free byte loops and ordered cursor steps. Generic
far paths preserve physical bank crossings and 24-bit wrap.
[Details](technical/far-loop-recovery.md), [indexed far loops](technical/indexed-far-loops.md).

### Cost-based loop unrolling

Repeat a small loop body directly when the saved loop work justifies the code
growth; larger loops can use an unroll factor plus a remainder.

```c
for (i = 0; i < 4; ++i) destination[i] = value;
```
```asm
; A = value, X = destination
sta a:$0000,x
sta a:$0002,x
sta a:$0004,x
sta a:$0006,x
```

Conditions: an eligible affine store and accepted cost plan. Supported byte,
word and wide stores retain their access order. Some short signed loops can
also unroll from a stable common starting expression rather than a literal.
[Details](technical/loop-unrolling.md), [relative bounds](technical/structured-codegen.md).

### Entry-only address inputs

Consume incoming argument registers while setting up a selected store loop,
avoiding parameter homes that would be unused afterward.

```c
void fill(unsigned *p, unsigned row) {
    unsigned i;
    for (i = 0; i < 4; ++i) p[row * 4 + i] = 7;
}
```
```asm
; form X = p + row*8 using the incoming X/A values
lda #7
sta a:$0000,x
sta a:$0002,x
sta a:$0004,x
sta a:$0006,x
```

Conditions: a selected affine/unrolled loop and bounded pure setup; needed
incoming values are preserved while forming the address. Eligible nested-store
forms have a related leaf selection. [Details](technical/entry-only-cursors.md),
[extensions](technical/loop-follow-ups.md).

### Exact value recurrences and shared recurrence homes

Replace a repeated expression such as `i + phase` with an initialized value
that advances with the loop.

```c
for (i = 0; i < 56; ++i) { p = (unsigned char)(i + phase); use_low_bits(p); }
```
```asm
; initialize a phase recurrence once
loop:
; use the recurrence instead of reloading phase and adding i
inc recurrence
```

Conditions: the supported private counter/value pattern, stable inputs and
compatible control flow. A copied byte home can share the recurrence when its
old/final values are dead; widening requires every use to discard high bits.

A bounded loop that tests `(1U << i) == key` can start a mask at
`1U << first` and double it after each trip. The comparison then uses the
current mask directly. The index must be private, increase by one, and stay
in a proven range where the seed shifted by the largest index fits in a
word. The original stopping condition still runs.
[Shift recurrence](../src/codegen/value_recurrence.inc).

### Combining repeated counter updates

For fixed nonvolatile words `i` and `total`, with `total` unsigned, the loop
`for (i = 2; i < 12; ++i) total += 3;` can become a single addition of 30
followed by a store of 12 to `i`. This gives the same final values as ten trips. The endpoints must be constants, the index must increase by
one and the loop must take at least two trips. The body can also be empty.

A different loop shortcut keeps the work of each trip. For a private unsigned
sum updated by `sum = sum * 2 + far_data[i];`, zicc can load the unsigned byte
or word once and double the sum with a shift. For eligible fixed runs of up
to four elements it can set up one far base and read each element at its own
offset. See the [loop selectors](../src/codegen/codegen.inc).

### Circular buffers and bit scans

In an eight-element word buffer, `i = (i + 1) & 7` wraps from the last slot
back to the first. For an eligible `do` loop, zicc can keep the byte offset
instead. It advances by two, wraps with mask 14 and uses that offset directly
to access the word. It converts back to the C index when the loop exits. The
index must have private direct-page storage, and the compiler must recognize
all of its uses. See the [ring-buffer example and assembly checks](../tests/check-banked-rom.py).

When a loop shifts a stored byte or word until a bit changes, zicc can keep
the shifting value in A and the count in X. For example, in
`while (!(word & 1)) { word >>= 1; ++count; }`, the mask tests the value
already in A. If the value must survive the loop, zicc writes it back on
exit. A signed right shift copies the sign bit. See the
[shift scan examples](../tests/check-comparisons.py).

A simple `while` condition may also move to the bottom of the loop. zicc can
repeat a cheap, side-effect-free test at entry to skip the body when the
first test is false. If the immediately preceding assignment already proves
the first test true, the body can start straight away. See the
[loop selector](../src/codegen/codegen.inc).

### Guarded retry-loop normalization

Simplify a retry loop with one proven progress step while still reevaluating
its predicate on every retry.

```c
int index = 2;
while (index <= 2) { if (ready()) { action(); ++index; } }
```
```asm
retry_loop:
; evaluate ready() on each retry
beq retry_loop
; perform action() and the single increment once
```

Conditions: the recognized structured shape and a non-overflowing step; calls
and predicates keep their original executions. Arbitrary wrapping updates are
not normalized. [Details](technical/structured-codegen.md).

### Scanning records for a match

A search can keep a near pointer to the current record in X for the entire
loop. For example, this unsigned subtraction handles a range that wraps at
the edge of a 16-bit coordinate.

```c
struct Point *p = points;
while (p != end) {
    if ((unsigned)(p->x - left) < width) return 1;
    ++p;
}
return 0;
```

The compiler recognizes a complete function walking a named near array to a
matching end pointer. It accepts one or two field tests with unsigned word
parameters, constant hit and miss results, and a limited sequence of calls on
the hit path. If the array has at least eight records, the stride is at most
eight bytes, and the code fits the size budget, it can test two candidates
per iteration. A final single-record check honors the actual end pointer.
[Implementation](../src/codegen/range_scans.inc) and [scan tests](../tests/check-banked-rom.py).

### Counted structure-product reductions

Select a compact cursor/countdown implementation for a supported field-product
sum rather than lowering each index expression separately.

```c
for (i = 0; i < count; ++i)
    total += (unsigned long)p[i].signed_word * p[i].wide_value;
```
```asm
; load fields at the current record, then multiply/accumulate
jsr .loword(__mul16x32)
; advance by the parsed record stride
dec remaining
bne loop
```

Conditions: the documented whole-function reduction shape, types and dead
index, with no extra observable work. Nonpositive counts skip data access.
[Details](technical/counted-reductions.md), [banked setup](technical/struct-reduction-banks.md).

## Registers, frames and private storage

### Frame-free scalar leaves and computed stores

Use incoming registers/stack arguments directly for eligible small functions.

```c
void store(unsigned *p, unsigned value) { *p = value + 3; }
```
```asm
; X = p, A = value
clc
adc #3
sta a:$0000,x
rts
```

Conditions: a supported scalar body or pure store calculation and compatible
arguments. General scalar leaves and stack-relative variants have broader
documented cases; unsupported calls/control flow keep a frame.
[Details](technical/computed-stores.md), [scalar leaves](technical/scalar-values.md).

### Guarded scalar-update leaves

Keep a computed field value in A through a guard and its successful store.

```c
int update(struct Item *p, int delta) {
    int next = p->value + delta;
    if (next < 0) return 0;
    p->value = next;
    return 1;
}
```
```asm
; X = p, A = delta; value is at offset 2
clc
adc a:$0002,x
bmi failed
sta a:$0002,x
lda #1
rts
```

Conditions: the documented signed-word field/update/return grammar, private
temporary and no additional effects or escaped state.
[Details](technical/guarded-updates.md).

Two other checks can avoid a stack frame on a common return path.

- A function such as `move_entry(p, dx, dy)` can return immediately when both
  deltas are zero if the compiler proves that path merely writes back existing
  nonvolatile fields. A call that records the zero move blocks the shortcut.
  A Boolean wrapper can also return zero early when a masked input is zero
  and the compiler proves that calls on that path have no observable effect.
- A byte lookup can return a fixed missing value for a null near pointer or
  for an unsigned byte below a threshold. Otherwise it subtracts the same
  threshold. For `if (value < 2) return 65535U; return value - 2;`, the
  successful `cmp #2` supplies the carry for `sbc #2`. The pointer must
  come from a nonvolatile global and be copied to a private local. Both
  failure paths must return the same constant.

[Guard implementations](../src/codegen/guarded_updates.inc) and [sample functions](../tests/check-banked-rom.py).

### Omitted parameter homes and incoming-stack reservations

Do not allocate or initialize a local home for an unused incoming register
value, and use existing incoming stack arguments in place.

```c
unsigned f(unsigned unused, unsigned b, unsigned c) { return b + c; }
```
```asm
; A = b; c remains in its incoming stack home in a selected leaf
clc
adc 3,s
rts
```

Conditions: parameter liveness includes early cursor setup and address escape.
Overwritten incoming values can omit their entry spill, while live arguments
retain homes. [Details](technical/register-argument-homes.md),
[stack reservations](technical/stack-argument-reservations.md).

### Tiny frames, smaller epilogues and early guards

Allocate very small frames with pushes, preserve only the needed result during
restoration, and return from simple base cases before allocating a frame.

```c
int factorial(int n) { if (n <= 1) return 1; return n * factorial(n - 1); }
```
```asm
; selected base-case test precedes allocation
; recursive path with a two-byte frame:
phy
phx
tsc
tay
```

Conditions: frame size/result width and entry-guard shape must qualify. Initializers
are never bypassed; wide returns retain the required A/X preservation.
[Details](technical/word-call-optimization.md), [early guards/returns](technical/frame-optimization.md).

### Whole-function and regional DP homes

Put hot local words in the compiler's fast DP workspace. Functions with calls
can promote a suitable loop region and copy only needed values at its edges.

```c
unsigned total = 0;
for (i = 0; i < count; ++i) total += values[i];
```
```asm
; representative promoted accumulator
clc
adc z:total_home
sta z:total_home
```

Conditions: available workspace and verified helper/callee clobbers, no conflicting
address escape, and valid entry/exit ownership. Full promotion can remove a frame;
partial promotion leaves ordinary homes for the rest.
[Details](technical/operations.md#direct-page-homes-and-register-cursors).

### Promoting a workspace value to Y

Keep a hot DP value in an otherwise available Y register.

```c
unsigned phase = start;
for (i = 0; i < count; ++i) {
    a[i] = phase & 63; b[i] = (phase + 21) & 63; ++phase;
}
```
```asm
; Y holds the phase instead of a DP word
tya
; calculate from phase
iny
```

Conditions: emitted register/stack analysis proves Y available and all updates,
saves and exits compatible. Y is not borrowed from a still-needed frame base.
[Details](technical/operations.md#direct-page-homes-and-register-cursors).

### Private frame-slot packing

Let local values that are never live together share a physical stack slot.

```c
{ unsigned a = first(); consume(a); }
{ unsigned b = second(); consume(b); }
```
```asm
; a and b can use the same physical home at different times
sta a:$0001,y              ; a
; after a is dead
sta a:$0001,y              ; b
```

Conditions: proven nonoverlapping lifetimes, including loops and exits. Addressed,
volatile, aggregate, parameter and hidden cursor storage stays pinned. Logical
identities remain distinct, and incoming argument addresses move with the frame.

### Private forwarding, dead stores and frame trimming

Remove redundant private copies/spills and trailing unused frame storage,
including safe regions inside functions that also access hardware.

```c
unsigned temporary = value;
/* temporary becomes dead without an observable use */
```
```asm
; no store to the dead private home
```

Conditions: byte-accurate liveness, known frame identity and alias/width checks.
Hardware accesses stay in place; unknown indirect accesses and calls limit
forwarding. [Details](technical/private-regions.md),
[frame trimming](technical/arithmetic-regions.md#private-values-and-frame-homes).

### Reusing a dead DP home for a calculation

Accumulate partial results in an already consumed private home instead of
pushing them onto the stack.

```c
color = red | green | blue;
```
```asm
; representative middle/final combination
ora z:color_home
sta z:color_home
; calculate the next component in A
ora z:color_home
```

Conditions: supported pure word operations and a DP home proven dead before
reuse, with no later use of its old value.

### A reuse within and across blocks

Keep a value already in A rather than loading its home again; intersect facts
at branches so reuse is also possible after compatible joins.

```c
if (x < 0) x = 0;
else if (x > limit) x = limit;
output = x;
```
```asm
; all incoming paths leave the current x in A
sta output                 ; no LDA x at the join
```

Conditions: both value and needed flags must be valid. Memory writes, aliases,
calls, width/register changes and differing predecessors invalidate the relevant
facts.
See [basic-block reuse](technical/structured-codegen.md).

## Calls, banks and whole-program selection

### Pure argument ordering and direct argument staging

Load a pure argument pair into X/A without pushing one argument unnecessarily;
push simple stack arguments directly from literals or homes.

```c
callee(a, b);
```
```asm
ldx a_home
lda b_home
jsr .loword(_callee)
```

Conditions: the A load preserves X and reordering cannot change observations.
Effectful arguments keep the established evaluation/snapshot order.
[Details](technical/structured-codegen.md), [argument setup](technical/bank-call-specialization.md).

### Fixed RAM object arguments and unused call results

Use a known RAM bank for real object addresses and avoid preserving a call
result that the C program discards.

```c
send(packet.bytes, 0, 544); /* first parameter is a far pointer */
```
```asm
; representative fixed far stack argument
pea $007E
pea .loword(_packet+2)
; after the call, discarded-result cleanup can adjust S without saving A/X
```

Conditions: a proven object/subobject address; pointer variables retain their
NULL-preserving conversion. Live results retain their normal ABI handling.

### Same-unit known-bank private entries

Keep a public far-pointer function while using a cheaper private entry for
calls whose object extents and banks are known.

```c
copy_bytes(ram_buffer, rom_literal); /* eligible same-unit byte-loop callee */
```
```asm
; low-word arguments in X/A for a selected RAM/ROM entry
jsr .loword(private_bank_entry)
```

Conditions: supported callee/call shape, visible definition, real declared
objects with proven bank-contained extents and a supported bank pattern.
Unknown pointers keep the generic bank-crossing entry. A byte loop with two
ROM cursors also uses that entry because the CPU has no absolute-long,Y
instruction for the second cursor. The linker checks the selected ROM bank
and the object's extent. A `noclone` function cannot get a private bank
variant. Structure reductions have a related specialization.
[Bank selection](../src/codegen/bank_calls.inc),
[details](technical/bank-call-specialization.md),
[reductions](technical/struct-reduction-banks.md).

### Near-origin strcmp adapter

Avoid padded far argument setup when standard strcmp arguments have proven
near origins, while keeping correct far progression for a long scan.

```c
int compare(char *a, char *b) { return strcmp(a, b); }
```
```asm
; near inputs in X/A
jsr .loword(private_near_strcmp)
```

Conditions: the standard compatible external declaration and proven argument
origins; custom definitions, unknown origins and volatile reads fall back.
[Details](technical/structured-codegen.md).

### Same-unit inlining

Replace an eligible call with its body so later passes can optimize across it.

```c
static unsigned add3(unsigned x) { return x + 3; }
unsigned f(unsigned x) { return add3(x); }
```
```asm
; selected caller body
txa
clc
adc #3                    ; no call to add3
rts
```

Conditions: supported body/types, recursion and growth policy. Inline hints,
forced-inline and noinline controls have documented rules. Unreferenced private
copies can disappear after expansion. [Details](technical/inlining.md).

### Source LTO and cross-unit inlining

Make independently preprocessed translation units visible to the same typed
optimization pipeline, allowing eligible cross-unit calls to inline.

```c
/* a.c */ unsigned add3(unsigned x) { return x + 3; }
/* b.c */ unsigned f(unsigned x) { return add3(x); }
```
```asm
; an eligible LTO caller can contain ADC #3 instead of JSR _add3
```

Conditions: opt in with `--lto`/`--lto-source` or the builder's LTO option.
Bindings, external entries and noinline barriers are preserved; this does not
make every external definition removable. [Details](technical/source-lto.md).

### Tail calls and unused procedure results

Jump directly to a suitable final callee, and omit result work in procedures
whose return value is not used or produced.

```c
void wrapper(void) { callee(); }
```
```asm
; eligible no-cleanup near tail call
jmp .loword(_callee)        ; callee's RTS returns to wrapper's caller
```

Conditions: the selected call/return ABI and no remaining argument/frame cleanup.
Main and valued/wide returns keep their required behavior.
[Details](technical/structured-codegen.md), [call/return internals](technical/operations.md#calls-frames-and-returns).

## Final assembly and code layout

### Switch dispatch without a saved control-value home

Keep the switch value in registers while testing its cases.

```c
switch (value) { case 1: first(); break; case 2: second(); break; }
```
```asm
; A = controlling word, evaluated once
cmp #1
bne next_case
jmp first_case
next_case:
cmp #2
```

The compiler chooses a different test when the case labels have a useful pattern.

- Three to 64 consecutive word values with the same simple action can share
  one range check. The action and the facts used to compile it must match.
- For different actions on consecutive keys, 6 to 16 keys can use two shorter
  groups of comparisons. From 17 through 64 keys, the compiler can check the
  bounds once and use a balanced tree to find the case. A negated word can use
  the original input by negating the case keys instead.
- A switch that returns constants or assigns constants to one object can look
  up the result in ROM. For example, cases 7 through 10 can subtract 7, check
  that the result is below 4, then load one of four words. The table holds
  values. A missing key may use a known default if at least half the range is
  occupied. The table covers at most 64 slots.
- A small set of word cases such as `v |= 1`, `v |= 8` and `v |= 32` can
  select a mask, then share one update to `v`. This also works for compatible
  XOR and AND assignments. The unmatched path must leave the object alone.

Other shapes use comparisons with the promoted input. Case bodies keep their
source order so fallthrough works. [Switch selection](../src/codegen/switch.inc),
[execution and assembly checks](../tests/check-switch.py).

### Register/address peepholes and dead assembly

Remove redundant loads, transfers, unused workspace stores and unreachable code;
combine address steps and immediate additions when their flag effects allow it.

```c
x += 2;
x += 3;                   /* eligible private calculation */
```
```asm
; where only the combined final result is needed
clc
adc #5
```

Conditions: register/value/flag liveness, exact addressing and recognized control
flow. Rewrites are reanalyzed so overlapping patterns cannot reuse stale facts.
[Details](technical/arithmetic-regions.md#scalar-control-flow),
[pass inventory](technical/optimization-catalog.md#assembly-cleanup).

### Branch layout and relaxation

Use a fall-through edge where possible and replace long branches/jumps with
short branches once final distances are known.

```c
if (condition) action();
```
```asm
beq after_action           ; when condition/flags and displacement permit
; action
after_action:
```

The layout pass drops jumps to the next instruction. If a short edge would
reach farther than 127 bytes forward or 128 bytes back, it grows to a jump,
or an inverted condition followed by a jump. The pass measures again because
growing one instruction can push another branch out of reach.

Within generated functions the pass also recognizes four smaller shapes:

- A jump straight to a return can use that same `RTS` or `RTL` at its source.
- A short backward jump to an immediate compare and loop-exit test can repeat
  the test at the bottom, so the last trip falls through.
- A conditional branch landing on another jump can go straight to its final
  target when the target stays in the same placement and within short reach.
- Two 16-bit `BIT` tests on the same accumulator that branch on nonzero to
  the same label can test the combined mask once if nothing enters between them.

See the [layout pass](../src/relax.c) and its [distance and control-flow checks](../tests/check-relax.py).
[Details](technical/operations.md#iterative-branch-relaxation).

### Selective interrupt scratch preservation

Save only the arithmetic workspace words a native handler actually writes.

```c
__interrupt(nmi) void handler(void) { /* eligible integer-only work */ }
```
```asm
; inside the normal interrupt wrapper, if only one workspace word is written
pei ($02)
; handler body
pla
sta z:$02
```

Conditions: emitted effects and helper contracts prove the clobber set. This
does not relax register, interrupt or hardware-arithmetic safety requirements.
[Details](technical/interrupt-scratch-preservation.md).

### Bank-aware call and ROM allocation

The build pipeline tries compact call/layout arrangements before spending more
bytes on wider calls or a larger ROM.

```c
callee();
```
```asm
jsr .loword(_callee)        ; when the selected placement permits a near call
; otherwise the selected build uses the required long call
```

Conditions: the linker proves the layout, bank capacity and resource constraints.
This is a build-time optimization; application semantics and public bank rules
are preserved. [Details](technical/rom-allocation.md).

## Shortcuts found from callers and final instructions

The assembly cleanup pass sees instructions, register widths, labels and possible
branches. zicc uses those facts to decide what a later instruction could still
read. Normal functions get the full set of eligible checks. A native interrupt
handler gets a smaller set for byte-width regions and repeated store constants.
A function that uses the eight-byte result workspace takes the separate exit
path described below. These choices also apply to eligible FastROM builds.
[Assembly reader](../src/codegen/assembly_lines.inc),
[pass selection](../src/codegen/line_passes.inc).

### Reading all calls to a private function

If every call passes the same array, the callee can use the array's name
directly. The body-codegen test has a private function called `ipa_cell`.
Every call passes `ipa_out` as its output buffer. The compiler can name
the output array in the store instruction.

```c
out[idx * 2u + 8u] = v + 2u;
```

```asm
sta a:.loword(_ipa_out+$0010),x
```

Each array element is two bytes, so the eight-element offset is 16 bytes.
This works even with `__noinline`. The compiler examines every live direct
call before it emits the private function. It can substitute a shared integer
constant, use a fixed object address, or narrow a far parameter when every
call supplies a suitable near address. It also combines known argument ranges.

When every argument expression is free of side effects and volatile reads,
zicc can drop unused arguments and move the most useful remaining word
arguments into X and A. It changes both the caller and the callee. An exported
function or a function whose address escapes keeps its calling interface.
Variadic, old-style, interrupt and aggregate-ABI functions also keep it.
Runtime-object builds use only the range information from this pass.
[Private call analysis](../src/codegen/static_ipa.inc),
[compiler test](../tests/check-body-codegen.py).

### Computing a small result at build time

```c
int has_letter(void) { return strchr("sprite", 'r') != 0; }
```

```asm
lda #$0001                ; 'r' occurs before the terminating zero
```

For this test, zicc recognizes the library declaration, knows both inputs
and needs only a yes-or-no result. It follows the same stopping rule as
`strchr`, including searches for the terminating zero. A fixed byte offset
into a string literal can also supply a constant. For a read of a constant
function pointer, a known relocation can identify the called function directly.
[Scalar simplification](../src/codegen/scalar_values.inc).

The same idea applies to private tables and short loops. If every later use
of a local table is a known slot, zicc can replace the reads with their
initial values and skip filling the table. For a loop that writes the same
values each time, it can keep one set of writes when it knows the loop runs.
It keeps the final index if later code needs it. A calculation shared by all
trips can move before a loop when zicc proves it will execute there safely.
Calls, possible overlapping writes and volatile reads limit what can move.
[Body simplification](../src/codegen/body_opt.inc),
[value reuse and loop-invariant calculations](../src/codegen/value_reuse.inc).

Inlining can expose enough constants to run a small loop during compilation.
zicc follows supported tests and private updates within a fixed work budget.
It can also simplify a wrapper that only returns a callee's result, a loop
whose inlined guard permits just one trip, or a selector fixed by an inlined
output store. If the input is unknown or the budget runs out, the ordinary
runtime path remains available.

Short helpers that move a structure also have special cases. A helper that
only copies a record of up to four bytes from a by-value argument into a
known destination can copy straight from the caller's object. A helper that
returns one field of a record can expose just that field when zicc can account
for the other arguments and the source is safe to read. A one-field record
with a known constant result can become a store to that field.
[Inlining](../src/codegen/inline.inc).

A floating-point counter has a separate rule. For example,
`for (i = -3.0f; i <= 7.0f; i += 3.0f) {}` ends with `i == 9.0f`.
zicc can produce that value directly when all the relevant integers,
including the last step, are exact in binary32 and the body has no observable
work. A fractional step, a volatile write, or a final step that would round
keeps the runtime behavior. [Loop checks](../tests/check-comparisons.py).

### Using a flag the processor already set

```c
int below_half(unsigned *p) { return *p < 0x8000u; }
```

```asm
lda a:$0000,x
bmi upper_half            ; branch if the loaded word has bit 15 set
```

Here the high bit answers the entire question. In a byte comparison the
corresponding threshold is `0x80`. The load must have the right width, and
the program must have no further use for the flags a separate comparison
would have set. Other rules reuse the flags from an increment or decrement,
keep a word in A across several bit tests, and carry a known clear carry bit
past instructions that preserve it. A literal low word can even decide the
carry into a known high word at build time.

When a private signed word is only compared in a loop, zicc can flip its sign
bit when the value first arrives. The resulting unsigned words sort in signed
order. Copies between these private loop values can keep that representation.
An arithmetic use, an escaping address or inline assembly can prevent this
change. [Flag and word operations](../src/codegen/line_passes.inc),
[signed loop comparisons](../src/codegen/body_opt.inc).

### Moving a choice out of a loop

A loop that needs both `n / divisor` and `n % divisor` may use the SNES
hardware divider for a small divisor. When a private divisor stays unchanged,
zicc can test its width once before a short `do` loop.

```asm
cmp #$0100
bcs wide_divisor          ; take the version that handles a wider divisor
```

Each version retains the original countdown and shares the quotient and
remainder. A similar choice between two constant XOR masks can move outside
a short loop whose cost justifies making two copies. A nested loop can skip
repeated length checks when the same private parameter rules out all inner
trips. Outer updates still happen.
[Loop selection](../src/codegen/region_homes.inc),
[loop and branch simplification](../src/codegen/body_opt.inc).

### Reading a byte once on the way to a word store

```c
while (count && *src) {
    *dst++ = 0x1200u | *src++;
    --count;
}
```

Here `src` is a far pointer to unsigned bytes and `dst` is a near pointer
to words. zicc can keep the constant high byte in the accumulator and use
the single byte read for both the stop test and the store.

```asm
lda [__arith_lhs]         ; read the next byte with A in 8-bit mode
beq done
rep #$20
.a16
sta a:$0000,x             ; write the saved high byte and the byte just read
```

This shape requires private pointers and a private unsigned word count.
When the count starts at zero, it skips the first read. A zero byte ends
the loop before the store. The source pointer advances across bank
boundaries, and the exit keeps the final count and pointers.
[Sentinel loop](../src/codegen/region_homes.inc).

### Reusing register values after branches

When a condition joins two paths, zicc checks what reached the join from
*both* directions. For example, if both paths leave the same private word in
X and the next operation needs it in A, a transfer can replace a memory read.

```asm
txa                       ; take the word already in X
```

zicc tracks the value separately from the flags for zero and negative. A
valid register value can survive an instruction that changes a flag, while
a later branch might still need that flag set again. The check also tracks
whether the address used X or Y. Changing an index can invalidate a saved
array read. Similar passes keep a scaled word index or a running sum in a
register through a loop, use an indexed array element directly in an
arithmetic instruction, and remove an index known to be zero from an
address. Unknown memory effects, calls, width changes and ambiguous branch
targets stop reuse where they could affect the result.
[Register facts across branches](../src/codegen/accumulator_cfg.inc),
[assembly and register passes](../src/codegen/line_passes.inc).

### Using the stack slot that already holds an argument

For a fixed variadic argument, a word can sometimes be read directly at a
known offset from the stack pointer S. A short wrapper that passes on its
incoming variable arguments can point the callee at the original argument
block and jump to the callee once its own temporary frame is gone.

```asm
lda 5,s                   ; example word five bytes above the current S
```

The stack offset must still refer to the same bytes after pushes or pops.
The wrapper must match the supported call and return convention. A leaf
function can also read incoming words in place, push
only the registers its frame needs, or keep an incoming pointer in Y while
using stack offsets for the other slots. Register saves can move to the call
that needs them. A literal return value can load after stack cleanup so it
does not need saving and restoring. [Frame and call passes](../src/codegen/frame_regions.inc),
[late assembly passes](../src/codegen/line_passes.inc).

For repeated far reads, zicc can keep a copy of a frame pointer in two unused
direct-page words. Only paths that have already prepared that pointer can
reuse it. A call or a write that overlaps the source invalidates the copy.
A leaf with a suitable far argument on the stack can temporarily set the
direct-page register D to S and read the byte through that argument. For a
repeated access it may instead move the pointer to unused direct-page space.
Both routes account for stack movement and preserve the required registers.
[Pointer reuse](../src/codegen/private_regions.inc),
[direct-page allocation](../src/codegen/dp_homes.inc).

A call inside the function does not always rule out fast storage. zicc
checks which scratch words that callee may overwrite and which locals are
still needed after the call. Two private locals with disjoint lifetimes can
share a physical stack slot. Eligible four-byte values need two adjacent
slots. Private-store cleanup tracks the bytes that are still needed, so
writing a low byte alone cannot remove a high byte that will be read later.
[Frame packing](../src/codegen/frame_packing.inc),
[private byte lifetimes](../src/codegen/private_values.inc).

### Doing useful work while hardware divides

The SNES divider needs time between the write that starts it and the read
of its result. A two-cycle index step can occupy a two-cycle wait slot.

```asm
inx                       ; replaces one NOP during the divider wait
```

Moving the step must leave the index and flags unchanged everywhere they
are read. zicc checks the whole delay sequence before making the swap.
Other matched patterns can compute a private masked value in the delay
slots, load only the low byte needed for the divisor, or store the quotient
before loading the remainder. The hardware still gets its full wait.
[Divider scheduling](../src/codegen/line_passes.inc).

Some leaf functions make several fixed hardware-register accesses in a row.
For the supported mirror addresses, zicc counts the cost of temporarily
changing D or the data bank register DBR, including the cost to restore them.
It can choose shorter direct-page or absolute operands when both time and
space improve. The register addresses, access widths and access order stay
the same. Calls, other accesses that depend on D or DBR, and branches that
could observe changed flags limit this choice. [Hardware addressing](../src/codegen/line_passes.inc).

### Removing work on a path that ends the program

```c
exit(0);
```

```asm
jmp .loword(_exit)        ; the runtime resets the stack on this path
```

For the known external `void exit(int)`, zicc can replace a call with a
jump, keep the exit status and omit work after it. The long-call equivalent
uses `JML`. When all subsequent paths reset the stack without reading it, an
earlier stack adjustment or a final private store may also disappear. A user
definition with its own behavior does not qualify. Some eight-byte-result
functions use this limited exit cleanup because their return value lives in
workspace that ordinary dead-store cleanup could otherwise discard.

The final passes also recognize two nearby writes that raise the same
sticky floating-point inexact flag. They keep the first raise and can skip
the second when nothing between them clears the bit or needs the lost flags.
[Termination and exception handling](../src/codegen/line_passes.inc).

For a dated inventory of switches, source files and verification coverage, see
the [implementation reference](technical/optimization-catalog.md).
