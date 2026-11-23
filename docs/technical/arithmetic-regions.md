# General arithmetic-region and runtime optimizations

The compiler can skip arithmetic it can prove is unnecessary. For instance, when one unsigned 16-bit number is divided by another that is at least 256, the answer fits in eight bits. The divider only needs eight steps to find it.

These changes use typed expressions,
control flow, liveness and helper effects; no function name, array name,
benchmark dimensions or observed PI quotient participates in selection.
Application C sources are unchanged.

## Runtime arithmetic

The unsigned word divider's existing large-divisor dispatch proves that the
quotient fits a byte whenever the divisor is at least 256. The software path
seeds its accumulator remainder with the dividend's high byte and consumes
only eight low bits. Its remainder stays in A, CMP supplies SBC carry, and X
is saved/restored. The hardware word/byte path remains for divisors below 256.
Both paths preserve X/Y. Signed word wrappers and remainder entries reuse the
same implementation. Division by zero remains undefined in C; the helper keeps
a deterministic all-ones quotient and original dividend remainder.

New __mul8x16 and __mul16x8 entries compute the low word of mixed-width products
using two hardware partial products. __mul16 retains its three-product generic
path; __mul8 retains its single product. All these multiplier entries preserve
X/Y and share the existing L/R/T scratch contract and hardware timing rules.
The generated helper workspace-clobber table includes both new entries.

## Typed byte bounds

Private, unescaped, nonvolatile word scalars can retain a zero-extended-byte
fact when every assignment proves that bound. A fixed point handles private
copy/cast chains; parameters, increments, compound updates and unknown writes
cannot introduce such a fact. Casts remain explicit so signed-byte extension
and truncation semantics survive propagation. Explicit unsigned-byte operand
types also enable mixed-width selection without flow facts.

These bounds select mixed multiplication, byte-divisor entries and byte-sized
comparisons. A signed word multiplied by a proven unsigned byte still has the
same low-word product; the transform does not assume the other operand is
nonnegative or that a runtime observation bounds it.

## Register-resident arithmetic regions

A descending for loop can keep index-1 in X, and an optional affine scalar in
Y, when its constant initial index is positive and at most 32768 (32767 for a
signed index). The condition must be index>0 and its step a unit decrement.
The body must be straight-line, nonvolatile, and must neither expose nor modify
the index. Global near-byte array accesses must be provably in bounds for the
entire range. An affine scalar assigned once at the body's start can occupy Y;
its coefficients are bounded small integers and arithmetic retains word wrap.

Normal typed expression emission remains in use. A speculative assembly scan
rejects unsummarized calls, any conflicting X/Y use, unresolved Y-frame access
and unsupported register effects. Only known preserving arithmetic helpers may
cross the region. DP home selection frees the frame anchor where possible;
otherwise the existing lowering is retained. The selector restores the C
index and affine scalar values at exit, including their final iteration values.
The signed branch after rebasing is justified by the proven initial range.

`--no-register-cursors` or `--no-body-optimizations` disables this selection.
All allocation stages regenerate near/long helper calls normally.

## Private values and frame homes

A basic-block copy pass forwards values through private homes and low-byte
stores, while respecting helper clobbers, overlapping stores, stack movement,
width changes and unknown aliases. Pure inline execution markers are transparent
only when no control-flow edge enters them. Other labels remain barriers.

Byte-granular control-flow liveness removes dead private stores and dead region
entry/exit copies. Indirect pointer operands and PEI are reads of their address
workspace. Escaping/aggregate/volatile frame objects are excluded. Dead private
stores do not justify dropping observable global or volatile stores.

After cleanup, trailing unused frame homes can be removed only when the frame
prologue/epilogues, surviving Y-relative operands and object-address formations
are understood. Incoming stack argument offsets move with the frame adjustment.
Unknown frame/address shapes retain the original allocation.

`--no-line-passes` disables these assembly-level transformations.

## Scalar control flow

Unsigned relations against zero use their known carry/zero properties instead
of redundant comparisons and branches. Proven byte operands use byte comparisons
with normal promotion semantics. Immediate equality retains the word path to
avoid a more expensive pair of accumulator-width switches. Consecutive immediate additions combine only
when final carry/overflow are dead; each rewrite is reanalyzed before another
can overlap it.

Private byte-bound action loops whose bodies never inspect/change the index or
bound can count down, then restore the source loop's final index. Calls cannot
observe an unescaped private bound. Loops with exits, index uses, mutable/escaped
bounds or arbitrary word bounds retain the original shape. Constant loops are
left to the existing unroller/counting machinery. In particular, the unsigned
j<=65535 wraparound case is not converted to a finite loop.

## Verification and measurements

`tests/check-arithmetic-regions.py` is registered in `make check`. It covers
mixed operand orders, full-word division boundaries, X/Y preservation, alternate
coefficients/dimensions, final loop values, byte truncation, aliases, far/wide
reads, packed byte stores, chained additions/carry, countdown bounds and update
forms, disabled-selection controls and split-bank/long-return builds.
Existing arithmetic, pointer, ABI, frame, struct, inlining and decimal suites
supply broader dependent coverage. The complete 200,873 arithmetic cases remain.

## Generated PI shape and remaining limits

The final hot loop has 44 executed caller instructions versus 75 before,
excluding helper bodies, and directly addresses A,X while Y carries the affine
divisor. calculate_pi has 477 application bytes versus 625; its local frame is
22 bytes versus 30, plus saved Y. main and print_digit remain 16 and 20 bytes.
The full-program measurements use the generated compiler output, not the
standalone ideal assembly from the analysis.

The 32-instruction reference remains a tighter hand allocation. General lowering
still spills one arithmetic subexpression across multiplication and conservatively
retains some compiler-DP clone stores when an opaque call could read workspace.
The new passes eliminate copies only when their alias/liveness proof permits it;
this is not a claim that every generated sequence equals the reference.

New runtime entries grow the integer helper group by 120 bytes. Programs that
already retain that group can grow even when their application instructions do
not change; PI's application reduction more than offsets this. Tables report
both application and complete linked code to expose this tradeoff.
