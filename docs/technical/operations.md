# Operations and target ABI internals

zicc turns C source into instructions that the SNES can run. The compiler
itself is written in C17 and built on the PC with MSVC. A ROM build works
through these steps.

1. `src/preprocess.c` handles supported preprocessor directives, such as macros.
2. `src/main.c` splits the text into tokens and keeps track of types.
3. `src/parser.inc` groups those tokens into typed expressions and statements.
4. `src/codegen/codegen.inc` turns that tree into ca65 assembly.
5. ca65 assembles the code, ld65 links it, and `romtool` adds the ROM title
   and checksum. VBCC serves as a separate compiler for comparisons.

For the rules that apply when writing a game, see the
[game-development reference](../operations.md).

## Machine and storage

Application rules: [Machine and storage](../operations.md#machine-and-storage).

Default builds use FastROM HiROM at $C0:0000 and grow from 64 KiB through 4 MiB
in powers of two. The staged build driver allocates code first; see
[ROM allocation](rom-allocation.md). Explicit LoROM linker configurations remain
available for regression fixtures and manual builds.
DBR=$7E, D=$0000, native mode, A/X/Y 16 bits, decimal mode clear. Ordinary
object pointers are 16-bit near addresses in bank $7E. General globals occupy
`__NEAR_START__` through $7E:FFFF, with constrained `__loram` objects placed first. Explicit `__dpage` globals use $0022-$00FF. $0000-$0001 are
compiler-owned and excluded from C objects so an object's address cannot equal
the null pointer. Eligible loops borrow that word with local save/restore; see
[direct-page counters](dp-loop-counters.md). Call-clobbered scratch `__dp_scratch` occupies $0002-$0021. The legacy aliases `__arith_lhs` and `__arith_rhs` name offsets 0 and 4. Eligible functions
and loop regions also place proven non-conflicting frame words there. The linker
reserves `__STACK_SIZE__` bytes from $0100 and startup sets SP to
`__STACK_TOP__ = $00FF + __STACK_SIZE__`. Near RAM starts at
`__NEAR_START__ = $7E0100 + __STACK_SIZE__`. The default 1,024 bytes gives
SP=$04FF and near RAM beginning at $7E:0500. D/stack operations use bank zero; low
WRAM is mirrored at the same offsets in bank $7E. PBR follows the selected code bank independently
of DBR; the automatic HiROM builder uses banks $C0-$FF. Linker RAM symbols carry their physical $7E bank; near operands and values
use their low words.

Selected persistent console and decimal buffers/state and the optional clock
counter occupy bank $7F, allocated downward only after member selection. Public
near objects remain in $7E. Foreground leaf scopes preserve DBR; the NMI library
section uses a single $7F boundary after user-frame cleanup. Internal decimal
formatter results are far pointers. See [runtime RAM backfill](runtime-ram-backfill.md)
for allocation classes, manual linking, interfaces and measured near capacity.

File-scope `__loram` is an object placement attribute, not a pointer qualifier:
`static __loram unsigned flags;` or `extern __loram char table[];`.
Every constrained object must lie entirely between `__NEAR_START__` and $7E:1FFF. BSS and
initialized objects are allocated before ordinary near storage, which can use
the remaining low space. Overflow, including aggregate allocation/alignment,
is a link error. The attribute must precede the object's definition and uses;
later declarations may omit it within the same translation unit. Apply it to
declarations in shared headers and definitions. Used cross-unit extern
constraints check the defining C object's exported size, including incomplete
array declarations. Handwritten assembly providers must supply the matching
`__zicc_object_size_name` absolute size export when consumed this way.
Unused extern declarations do not force allocation or symbol resolution.

`__loram` rejects functions, automatic objects, parameters, typedef placement and
`__dpage` combinations. A pointer variable's attribute places its storage, not
its target. `__loram const` retains C const semantics but resides in near RAM;
its initializer is copied from the LORAM_DATA ROM image. Startup copies
LORAM_DATA and DATA separately before console/main and establishes DBR=$7E.
The malloc heap begins after all near statics. Runtime buffers remain in bank
$7E; arithmetic scratch and the console's indirect cursor retain direct-page
storage. Stack use beyond 1 KiB reaches direct page, so frame-size checks alone
cannot establish safety for recursive calls and interrupt nesting.

Far-pointer ABI details:

- Four-byte arguments use the existing stack argument ABI.
- Returns use A for the low word and X for the bank-and-padding word.
- Far object pointers introduce no new call instruction or function-pointer
  representation.

For declarations, representation and conversions, see
[near and far pointers](../operations.md#near-and-far-pointers).

Known ROM scalar/subscript reads use absolute long addressing (X for indexed
access); arbitrary far accesses use long-indirect DP scratch. Recursive
evaluation keeps live addresses on the invocation stack. Interrupt scratch
preservation includes the selected far-address staging words. Near register/row/DP
loop optimizations retain their proven address constraints. Current far-loop
selectors and fallback paths are described in [far loop recovery](far-loop-recovery.md)
and [indexed far loops](indexed-far-loops.md).

Runtime hardware accesses use explicit long operands. A byte far dereference
performs one byte access in A8, then restores A16. The console's DMA source bank
is $7E. Application-facing pointer and access-width requirements are documented
under [volatile accesses and MMIO](../operations.md#volatile-accesses-and-mmio).

Scalar char locals/arguments have two-byte homes; reads mask and optionally sign
extend. Packed char writes briefly select A8, write one byte, then restore A16.
Near nonvolatile byte reads normally load a word and mask its upper byte. Far byte
accesses use A8, including explicit MMIO accesses. `sizeof` reports the C object
size rather than padded stack homes.

Scalar-object compound updates use fixed homes rather than constructing an
indirect destination address. Same-width integer add/subtract/bitwise updates can
consume a side-effect-free RHS directly; C calls/writes retain the previous
left-value snapshot order. Discarded wide results omit preservation/reloads.
See [scalar-home updates](scalar-home-updates.md) for the safety rules and paired
measurements. This applies to expression statements and discarded `for` steps.

Repeated member operands in an integer binary expression can compute their
common element address once and read fixed field displacements. Typed structural
matching and a pure-address check exclude observable address side effects.
Existing fixed-memory and widened multiply selections are preserved. See
[shared element addresses](shared-element-addresses.md) for the selection limits,
target tests and incremental measurements. This does not add loop cursors.

## Enumerations

Application rules: [Enumerations](../operations.md#enumerations).

Enum tag metadata is frontend-only; the backend receives the existing int
representation. Enum expressions, parameters and returns use the integer ABI.
No runtime helpers or storage for enumerator constants are added.

`tests/check-enums.py` checks target execution, an MSVC reference, accepted and
rejected declarations, absence of enumerator storage and identical instruction
output for equivalent enum/int programs. It runs in the existing compiler suite.

## Structure definitions and layout

Application rules: [Structure definitions and layout](../operations.md#structure-definitions-and-layout).

The storage, member access, qualification and completeness rules below also
apply to unions. Both use the existing aggregate addressing and scalar codegen;
no instruction-selection or ABI changes are required.

Zero-filled global structures and arrays begin at even addresses, including
explicit direct-page objects. Local structure homes use even offsets from the
even Y frame base; two extra home bytes preserve that alignment and frame parity
without changing scalar homes or the call ABI. This home slack does not affect
`sizeof` or array stride. Dynamic pointer offsets use shifts for power-of-two
strides and the existing word multiply helper for other strides.

The base expression is evaluated once, including compound assignments whose
right side calls a function. Named object fields and constant array elements
use fixed memory operands; other member reads/stores can use a constant field
displacement from X. Dotted nesting combines member offsets. The existing
call-safe address spill path preserves destinations while evaluating a RHS.
This does not add a new register allocator or struct-loop cursor optimization.

All writable initialized objects, including internal-linkage objects and objects
from separate translation units, are concatenated into one linker DATA segment.
The segment has a contiguous ROM load image and a contiguous RAM run region;
object symbols refer to RAM. Alignment gaps and aggregate padding are part of
the copied image. Const initialized objects remain in RODATA, and uninitialized
objects remain in BSS/ZEROPAGE under the existing full-WRAM clear.

After clearing WRAM and establishing the stack, startup copies DATA before
console initialization or main. Linker symbols __DATA_LOAD__, __DATA_RUN__ and
__DATA_SIZE__ supply the source, destination and byte count. A zero count skips
the copy; otherwise one MVN block move with A=size-1 copies exactly size bytes.
Startup leaves DBR at $7E and retains the existing D=0, A16/X16, A/X/Y=0 main
entry contract. Link-time assertions require a count below 65536 and both spans
within individual banks. The current near-RAM capacity is smaller still. Custom
linker configurations must supply DATA with define=yes and ROM-load/RAM-run
addresses. There are no per-object copy records or initializer function calls.

Local aggregates use scalar initialization stores at their target-layout offsets;
missing subobjects are zero initialized. Static locals have one private global
storage symbol and a separate scoped binding, so inlining retains storage identity.
Pointer initializers emit linker relocations for low words and far bank bytes,
with zero padding for the four-byte far ABI. Source LTO remaps relocation targets
alongside executable references. Near RAM relocations retain bank `$7E` and
link-time range checks; ROM relocations retain their actual placed bank.

See the [calling rules](../operations.md#calls-frames-and-returns) for aggregate
arguments and returns by value. Aggregate arithmetic,
comparisons, casts, conditional values and compound
assignments remain outside the supported expression subset. Nameless member promotion, bit-fields and
flexible array members remain unsupported. Empty definitions, duplicate members,
redefinitions, incomplete or void members and oversized layouts receive source-location diagnostics.
`tests/check-structs.py` checks recorded layouts directly and executes size,
alignment, stride and recursive-storage checks in Mesen. `tests/check-members.py`
adds MSVC references, Mesen member semantics and codegen/diagnostic checks.
The initializer suite also runs `tests/check-writable-initializers.py`: seeded
WRAM, exact linked images, empty/one/odd/1025-byte spans, separate translation
units, subsequent writes, and pre-console/main copy and ABI assertions.
The structs suite also runs `tests/check-unions.py`: independent recorded layouts,
Mesen overlapping access, exact ROM images, tag scope/identity and diagnostics.

## Structure and union assignment

Application rules: [Structure and union assignment](../operations.md#structure-and-union-assignment).

Both operand addresses are evaluated once, with destination first. A stack-owned
address survives source-side calls and nested assignments. Assignment results are
non-lvalues and support chaining and member reads. Array-containing aggregate
results used for member access receive private temporary snapshots, so subsequent
index evaluation cannot change the chosen result value. Temporary homes are
allocated only for expressions retained in the executable AST, preserving sizeof's
unevaluated behavior. Existing frame-capacity limits apply. The host snapshot
reference uses an explicit temporary to avoid relying on another compiler's
operand-evaluation choices.

src/aggregate_copy.inc selects inline word loads/stores, a descending word loop
for fixed globals, or MVN for near-bank copies. A fixed ROM source uses its
actual ROM bank and a RAM destination uses $7E; near RAM-to-RAM MVN uses $7E,$7E
and leaves DBR at $7E. Computed far banks use a long-indirect word loop, with
addresses staged in arithmetic scratch after evaluating each operand once.
No executable stack code is required. The emitter preserves Y and interrupt
wrappers preserve live registers/scratch so transfers can resume after an NMI.
Discarded assignment results omit their address preservation, and eligible
direct source-address loads avoid spilling the destination. Scalar field stores
can defer a pure destination-base load until after evaluating the source.
The cost policy below applies to the existing near/fixed-bank paths; runtime-bank
copies currently use the general loop rather than an MVN trampoline.

The default policy minimizes estimated nominal CPU cycles plus eight cycles per
emitted code byte. It also limits inline expansion to 128 bytes. This is a stated
size/speed policy, not a measured fastest-copy threshold. Common address/result
staging is omitted from candidate scores. For N even bytes at fixed global
addresses, the models are inline 5N cycles/3N bytes, loop 9.5N+2 cycles/13 bytes,
and MVN 7N+18 cycles/14 bytes. The loop is eligible through N=32768. Thus fixed
2/4-byte copies inline, 6/8-byte copies loop, and copies of 10 bytes or more use
MVN. For computed addresses, indexed inline costs 6N cycles/3N body bytes;
MVN costs 7N+3 cycles/6 body bytes, excluding common staging. Two-byte copies
inline and larger copies use MVN under this policy. SNES bus wait states are not
represented as uniform CPU cycles in these estimates.

--no-copy-selection forces the simple inline reference, without the expansion
limit, for semantic comparisons. It does not disable temporary-value snapshots.
It also retains ordinary library calls for known-literal `strcpy`; otherwise
those calls use the shared copy policy as described in [literal copies](literal-copies.md).
The branch layout pass recognizes MVN's three-byte encoding. No function-call ABI
or runtime library changes are required.

The members suite runs tests/check-aggregate-copy.py: selected/inline-reference
and MSVC semantics, const/type/value-category diagnostics, bytewise target copies
including padding, recursive storage, side-effecting addresses, chaining, temporary
snapshots and all three selection forms. NTSC/PAL checks exercise all four
handlers under A8/A16/X8/X16 entry modes and verify registers, stack, DP0 and
arithmetic scratch. Separate foreground tests require real NMI interruption
inside MVN and inside an inline reference copy, and check completed contents.

## Calls, frames and returns

Application rules: [Calls, frames and returns](../operations.md#calls-frames-and-returns).

K&R definitions receive promoted types. A character parameter gets a private
declared-type home initialized by an ordinary frontend conversion, preserving
truncation, signed loads, sizeof, const qualification and address-of semantics
inside the body. This uses the existing frame/call/load/store codegen.

The compiler suite runs tests/check-legacy-functions.py: separate-TU target and
MSVC execution, warning diagnostics, signed/unsigned character narrowing,
wide/float/array/recursive/eight-argument calls, and comparison with explicit
modern frontend lowerings. Source comments and file-derived label prefixes are
normalized for the instruction comparison.

Ordinary calls use JSR/RTS in short-call layouts. Stage 3 uses JSL/RTL at
the runtime boundary; stage 4 uses JSL/RTL for ordinary calls throughout. See
[stage-specific call conventions](rom-allocation.md#call-conventions-and-fixed-entries). Named word argument 0 uses X and named word
argument 1 uses A. Other arguments, every 32-bit argument, and every unnamed
variadic argument are pushed right to left. A 32-bit value is pushed high word
then low word, so its low word is closest to the return address. Argument
positions are fixed: a 32-bit argument does not donate its unused register slot
to a later argument. Immediate word stack arguments use PEA. Callers discard
stack arguments after the call without destroying A/X return values.

A contains a word return; A low/X high contain a 32-bit integer or binary32 return.
A, X, flags and arithmetic scratch are caller-clobbered. Y, D and DBR are preserved.
Far byte-loop leaves follow this same scratch contract. Eligible direct calls may
use [private known-bank entries](bank-call-specialization.md), with low-word
pointer arguments in X/A; their public far entry and its ABI remain available.
Functions needing a frame save Y, allocate one stack frame and use Y as its
stable base. Register parameters are copied into frame or promoted direct-page homes at entry; stack
parameters are addressed in their incoming argument slots, which are private
writable copies for that invocation. Recursive operands and values that must survive unresolved calls belong to
the stack. Proven non-conflicting direct-page homes may survive known same-unit
calls; the public workspace remains call-clobbered. Word returns temporarily use caller-clobbered X
while the epilogue restores S, then transfer back to A before restoring Y.
They need no return staging slot. Wide returns keep their high word in X and
stage only A in the final two frame bytes, recovering it with PLA before PLY.
Frames with at most four local bytes instead allocate homes with pushes:
incoming X/A parameters fill their homes directly, and PHA reserves other
uninitialized homes. TSC/TAY establishes the same Y-relative layout. Returns
discard these homes with PLX for word results or PLY for wide results, then
restore caller Y with PLY. Wide tiny frames need no return staging bytes.
After emission, a word-result Y frame whose Y register serves only the frame is
rewritten to stack-relative `n,s` operands (`stack_frames` in `codegen.inc`).
The pass tracks push depth along every path, requires the same depth at each
label, removes PHY/TSC/TAY/PLY, moves incoming stack arguments down two bytes,
and routes frame LDX through A where A and N/Z are dead. Any other Y use, a
dynamic TCS, interrupts and wide results keep the Y frame; `--no-stack-frames`
disables the pass. After the frame passes, finished functions also drop
`sta X; lda X` reloads of frame and scratch slots with dead N/Z (not in
functions with volatile accesses), drop `pha/pla` pairs that protect nothing,
merge constant byte stores under one `sep`, and turn `jsr f; rts` into `jmp f`
outside `--long-return`. A Y frame whose Y also indexes far loads in
`phy … ply` windows converts too: the windows go and the prologue's PHY saves
the caller's Y once. Finally `src/codegen/line_passes.inc` (`--no-line-passes`) runs
liveness-checked rewrites over the function's lines: precomputed loop-exit
bounds, a workspace word promoted to Y (saved at entry), constant store
forwarding and branch folding, unreachable and dead instruction removal,
register reloads, `inx/dex` folding into non-negative displacements, and a
pushed `X` replaced by an already computed `A = X + c`.
Leaf functions without
frame storage omit that prologue. Simple long arithmetic/helper wrappers and
the paired-shift XOR expression used by `mix_words` use native stack-relative
argument loads and RTS without a frame. Stack offsets account for temporary
pushes. In the paired-shift case the count stays in `__arith_rhs` across the
two shift helpers, which preserve that count. General expressions with C calls,
local storage or control flow retain the normal frame path. Simple 16-bit
integer arithmetic functions with up to two word parameters use their X/A
arguments directly. Signed and unsigned add/sub select the same ADC/SBC
instructions; signed inputs are required to have a representable result.

More general single-return word functions can also omit their frame. The word
expression planner accepts pure add/subtract/bitwise trees, unary operations,
bounded constant multiplication and constant shifts. It retains parameter 0 in
X, saves parameter 1 from A only when a later use needs it, and reads additional
word parameters in their incoming stack slots. Up to four existing scratch
words hold expression temporaries; temporary lifetimes permit reuse. Named
fixed structure fields and array elements use the existing direct-operand
selector. The same planner reduces expression spills in ordinary framed code.

Constant word multiplication chooses a bounded shift/add/subtract/negate recipe
from an operation-cost model. Its 32-cycle inline budget includes preserving the
base when needed. Either operand may be constant, and an effectful operand is
evaluated once before inline multiplication, including multiplication by zero.
The planner preserves each C subtree and does not reassociate sums. It plans
before emitting text, falling back without changes when the tree is unsupported,
scratch is exhausted or 128 instructions are exceeded. Calls, dynamic member
accesses, byte/wide operands and control flow keep their established handling.
See [the expression measurements and validation](word-expression-optimization.md).

Long addition and bitwise operations can defer a fixed left operand until after
a pure right subtree, avoiding its stack spill. Two widened word operands use
`__mul16wide` for their full 32-bit product, with independent sign/zero extension;
true long operands retain `__mul32`. Calls and writes prevent deferred loads,
and effectful product operands keep call-safe preservation. These selections are
unconditional. See [the widened-product report](widened-product-optimization.md)
for before/after/VBCC measurements and the shared runtime cost.

Larger frame allocation uses `TSC; SEC; SBC #frame; TCS; TAY`. TCS leaves A unchanged,
so TAY consumes the new stack address directly; no second TSC is needed.

A leading `if (parameter comparison constant) return parameter_or_constant;`
can run before frame allocation when the function takes one 16-bit integer
parameter and returns a 16-bit integer. The test reads incoming X and reuses
the normal signed/unsigned comparison lowering. The returning path uses RTS
directly; the continuing path establishes the ordinary frame. Empty declarations
can precede the guard, but initializers, other statements, additional parameters,
calls and alternate branches retain the normal path. See
[the measured frame investigation](frame-optimization.md).

A private integer temporary assigned immediately before a commutative return
can feed that operation directly in A. This requires exactly one definition and
one use in the entire function, with the other operand a direct word operand.
The assignment and read are replaced before code selection; address escapes,
additional uses, globals, parameters, byte/wide temporaries and noncommutative
operations retain their ordinary lowering. A trailing unused home is removed
without relocating other locals. Calls in the assigned expression still run
before reading the other operand.

An immediately repeated load of a word frame home can also reuse A after its
store or an earlier load. Source comments and PHA may intervene: PHA preserves
A/N/Z and does not change a Y-relative address. A store's producer must already
have set full-word N/Z from A. Labels, calls, mode changes and uncertain flags
stop reuse. This preserves both the value and the flags the load would establish.

Address selection accounts for the consumer's register. When X needs a local
address at Y+1, it uses TYX/INX, leaving A available for another argument. Frame
offsets zero through three use TYX followed by the required INXs; larger offsets
use TYA/CLC/ADC/TAX because that costs fewer CPU cycles than four or more INXs.
A word value already in a frame/global home can load directly into X with LDX.
Byte values still use their required masking/sign extension, and addresses needed
in A continue to use the accumulator path. Only representation-preserving word
casts can forward directly through the X selector.

Startup clears both 64 KiB WRAM banks before using the stack, sets S=$1FFF,
copies the linked DATA image into RAM, initializes the console, clears A/X/Y
and uses **JSL main**. Thus main sees S=$1FFC.
This explicit root call helps Mesen profiling. Main's epilogue uses RTL; startup
then enters `main_exit`, an infinite loop. Main cannot be called from C. Ordinary
functions use the selected stage's call convention. Console initialization enables NMI; timer IRQ and
HDMA remain disabled unless explicitly configured by the application.

## Expressions

Application rules: [Expressions](../operations.md#expressions-and-control-flow).

Word scalar and pointer increments update their homes directly without arithmetic
scratch. A discarded update needs no saved old value; a postfix address consumer
keeps the old pointer in X while A updates its home. Unit steps use INC/DEC A.
Indirect assignments save X only when evaluating the source may overwrite it.
String loops retain byte stores and their per-byte termination/aliasing behavior;
unknown-length copies are not widened into paired stores.

| Operation | Lowering |
| --- | --- |
| 16-bit +, -, &, \|, ^ | A word operation; CLC/SEC before add/subtract |
| 32-bit +, - | Low word in A, high word in X; direct immediate/home RHS where possible; carry/borrow propagated |
| 32-bit &, \|, ^ | Independent word operations |
| Multiply | One 8x8 product for proven unsigned-byte inputs, three for word results, four for two widened words, seven for word-by-long, ten for general long results; eligible constants use shift/add recipes |
| Divide/remainder | Width-specific word/long paths; SNES CPU 16/8 for divisor magnitudes 1..255, otherwise 16/32-step restoring division; signed wrappers apply signs |
| Shift | Constant shifts inline with whole-word moves for counts >=16; variable helpers also split off a 16-bit move |
| Word compare | CMP for equality/unsigned order; SBC with N xor V for signed order |
| 32-bit integer compare | Direct word equality where possible; ordered/general comparison helper returns -1/0/+1 |
| Floating +, -, *, / | binary32 helper with operands in scratch, result A/X |
| Floating compare | IEEE compare helper; unordered is distinct from -1/0/+1 |
| `&&`, `\|\|`, `!`, `?:` | Conditional branches; unselected expressions are not evaluated |
| `++`, `--`, compound assignment | Evaluate destination address once, operate, store |
| Dereference | Absolute indexed through X; explicit DP pointer can use `(dp)` |

Variable shift helpers retain one word in A throughout the loop: low for left
shifts, high for logical/arithmetic right shifts. Only the other word uses a DP
read/modify/write per bit. Counts >=16 shift just the surviving word in A and
fill the other word with zero or the sign. Each helper writes the final pair
back to the left workspace, returns A low/X high, and preserves the RHS count.

Basic integer operations use a literal or scalar/fixed-array home directly as
the RHS. Long addition/subtraction keep low/high words in A/X, using one
temporary low-word push across the high-word operation. A complex RHS retains
the recursive stack path, but only that RHS needs staging before native integer
operations. Helper calls load simple operands straight from homes into DP,
without first assembling each operand in A/X. More general binary expressions
evaluate the left operand, save it on the stack, evaluate the right operand,
then stage both operands in arithmetic scratch. For a simple RHS, the left
value can go directly into scratch without a stack spill/reload.
General helper/C calls may overwrite scratch; recursive expression values do
not live there across calls. The dedicated paired-shift leaf uses the narrower
contract that the three shift helpers preserve `__arith_rhs`. This allows
recursion in the calculator. It does not make
the decimal runtime reentrant: its digit/output buffers are shared globals.

Long multiplication uses ten 8x8 byte partial products, omitting terms above
bit 31. Word multiplication uses only the 00, 10 and 01 products contributing
below bit 16. Proven unsigned-byte operands select one full 8x8-to-16 product;
signed bytes use the word helper so negative values and C promotions remain
correct. Word operands stage only their low words. Byte-divisor division uses
one hardware operation for a 16-bit dividend,
or three for a wider dividend: high word first, followed by two remainder/byte
steps. Unsigned division leaves the quotient in `__arith_lhs` and the remainder at
`__arith_lhs+8`; the remainder wrapper returns that result. Signed wrappers
preserve C truncation toward zero and give the remainder the dividend's sign.
Larger divisors, including the sample's `$1234`,
retain software division, with sixteen iterations for word operands. Long
division by a word divisor uses a word-remainder loop; it runs sixteen steps
when the dividend's high word is below the divisor and thirty-two otherwise.
A divisor of at least 65536 bounds the quotient below 65536, so it also runs
sixteen steps. Division by zero keeps the original thirty-two full-width steps.
Multiplication helpers write each multiplicand byte to WRMPYA once and rely on
its latch for the following WRMPYB products. Proven unsigned-byte division/remainder can enter
the hardware word path directly. Signed-byte division remains a promoted signed
word operation (for example, -128 / -1 returns 128). Hardware accesses assume
the documented DBR=$7E ABI.
The S-CPU multiplier/divider are shared hardware; interrupt handlers must not
use them during these helpers. Startup enables NMI when the console is linked. The library clock
tick never uses these helpers or their workspace; generated user handlers save
and restore workspace and reject hardware-arithmetic helpers.

ALU scheduling counts opcode/operand fetches. Multiplication needs no NOPs;
division uses two NOPs plus REP, RTS, and the caller's result-load fetches.
The [SNES development manual, chapter 15](https://floating.muncher.se/bot/manual/book1_text.pdf#page=82)
specifies eight and sixteen machine cycles respectively. The hardware regression
checks both results and read timing in FastROM.

### Quotient/remainder reuse

`src/codegen/divmod.inc` collects matching integer `/` and `%` expressions whose operands
are scalar objects, literals or casts of those. For an eligible pair it calls
the divider once and saves both results in four private frame bytes for word
results or eight for long results. Unsigned pairs use the matching `__udiv8`,
`__udiv16` or `__udiv32` entry; signed pairs use `__sdivmod16` or
`__sdivmod32`, which sign both results.
Either `/` or `%` may occur first. Later uses load the saved result even if an
intervening comparison or multiplication overwrote arithmetic scratch.

Reuse requires a producer on every incoming path and unchanged operands.
Stores to either operand invalidate its cache; indirect stores and C calls
invalidate all caches. Branch joins intersect availability. Loop entries, exits
and continue targets conservatively clear it, while a condition's always-run
division can supply the loop body. A trial emission identifies candidates with
an actual dominated reuse; candidates with none get no frame storage or cache
stores. This is conservative local reuse, not interprocedural optimization:
separate functions still divide independently. Complex operands with calls,
dereferences, increments or arithmetic retain normal evaluation.

`--no-divmod-reuse` disables the pass for differential checks. It preserves the
SNES hardware helpers. `tests/check-divmod.py` executes both variants, including
signed/remainder-first pairs, branches, loops, aliases, calls and mutations.
The hardware regression also verifies the exact number of ALU operations so a
correct-but-duplicated quotient/remainder computation fails that check.

### Array accesses and stores

Array element width is a compile-time constant; the index may still be a runtime
value. Constant in-bounds subscripts of declared arrays become fixed memory
operands. A local array uses its Y-relative frame offset plus index times element
size; a global array uses its symbol plus that constant displacement. For example,
`int values[8]; values[2] = 32000;` uses `LDA #$7D00` and `STA $0005,Y` when the
array starts at frame offset one. There is no computed pointer or scratch spill.
Byte elements still get byte-wide stores; four-byte elements use two word stores.

For a pointer variable and a simple side-effect-free word index, indexing loads
the index, scales it with zero/one/two ASLs for 1/2/4-byte elements, then adds the
pointer directly from its home. Constant displacements use immediate arithmetic.
An indexed store keeps its address in X if evaluating the RHS preserves X. If
the RHS can clobber X or call another function, the address is saved on the stack
and restored with PLX before a word/byte store; the value remains in A. This avoids
sending word stores through the shared arithmetic workspace.

The specific adjacent copy `p[j] = p[j - 1]` reuses the source address in X and
stores at `element_size,X` when both bases name the same object and both indices
read the same simple scalar variable. It is currently selected for byte/word
elements. Calls, pointer/index side effects and unproven relationships use the
general path, which evaluates the destination once. This is local instruction
selection, not general alias analysis or register caching across loop iterations.

Native indexed direct addressing uses full-width X with D=$0000, but `dp,X`
addresses bank zero rather than DBR. The selector therefore requires a proven
bank-zero-accessible cursor; general near pointers and high-WRAM arrays retain
DBR-relative absolute indexed addressing. ROM bases retain absolute-long reads.
`--no-indexed-dpage` disables this selector.

### Loop strength reduction

`src/codegen/strength.inc` finds affine array indices of the form `i`, `i + constant` or
`i - constant` inside loops. It maintains a private near cursor equal to
`base + i * element_size`, using one extra two-byte frame slot per base/index
pair. The original C integer `i` is retained. Index assignments, copies,
increments/decrements and compound updates keep the cursor synchronized; ordinary
uses, comparisons, arguments and returned indices still see the C integer.

Complete struct element strides are supported as well as the original two/four
byte elements. A normal unit index update advances a struct cursor by its size;
`inventory_value` uses an eight-byte step and no body index scaling. Each pair
still costs two frame bytes. Power-of-two synchronization uses shifts and other
sizes use word multiplication only at initialization/reassignment. Explicit ROM
initializer images are excluded from the WRAM addressing hint; writable DATA
arrays retain that hint. See the measured
[struct cursor trial](struct-loop-cursors.md) for tests and the timing/size/frame
tradeoff. This does not pin a register across calls or remove the C index.

For `insertion_sort`, `i = 1` initializes one cursor at `values + 2`; `j = i`
copies that cursor to a second slot. Incrementing i advances its cursor by two;
decrementing j moves its cursor back by two. Array accesses load the cursor into
X directly. There are no index-scaling shifts in that function. Its frame grows
from 14 to 18 bytes, and recursive invocations own independent cursor slots.

The initial safety rules accept declared arrays and unchanged pointer parameters,
with local/parameter word integer indices. Taking the address of an index or
pointer base disables the corresponding candidate, as does explicitly changing
the pointer base anywhere in the function. Global pointer variables and local
pointer variables are currently excluded. The pass respects the existing frame
size limit and selects at most 32 pairs. Calls are safe for eligible non-escaped
locals because the cursors live in the preserved Y-based frame.

Constant initializers and copies from another cursor with the same base need no
scale. An arbitrary assignment or nonlinear update can instead resynchronize the
cursor by scaling once at that write; a parameter index can require one initial
scale. Complex/non-affine accesses retain the original address path. Maintaining
cursors has a cost, so the speedup depends on the access/update pattern.
`--no-strength-reduction` disables this pass for controlled comparisons while
retaining the other instruction-selection improvements. Regression tests compile
and execute the same sources with the pass enabled and disabled, alongside MSVC.

### Direct-page homes and register cursors

The compiler allocates frame slots and loop cursors after the whole-function
leaf selectors. It also simplifies comparisons against constants.
The C-visible storage and public ABI are unchanged.

- `frame_operand()` centralizes frame accesses. Trial emission counts references,
  weighted by loop nesting, and emits temporary home placeholders for validation.
- `src/codegen/dp_homes.inc` maps eligible frame words to unused words of $E0-$FF.
  A scan reserves workspace references and helper clobbers, including literal
  workspace operands. `tools/helper-clobbers.py` derives the integer-helper table.
- Same-unit summaries cover already-emitted functions, their helpers and their
  known callees. Recursion, later-defined/external callees and unknown indirect
  transfers remain unresolved; their calls prevent whole-function promotion.
- If all used homes can move, the Y frame is omitted. Otherwise remaining homes
  retain their frame locations. Register parameters can enter DP homes directly.
  Volatile functions, interrupt functions and unsupported address-taking paths
  retain ordinary lowering; a failed validation rolls emission back.
- `src/codegen/bound_cursors.inc` can hold one strength-reduced cursor plus a constant
  displacement in X throughout an innermost loop. Entry loads its home once;
  exits through the loop end write it back. Unrelated X writes, calls, width
  changes or residual home accesses reject the trial.
- `src/codegen/lftr.inc` removes a private signed-word index used only through cursors
  and leading `j > 0`/`j != 0` tests. Restricted initializations and guarded unit
  decrements prove nonnegativity; cursor strides must be at most two bytes.
  Tests compare the tracked cursor with its base, accounting for any X bias.
  Any remaining observation of the index home rejects the transformation.
- `src/codegen/region_homes.inc` promotes hot words around an eligible outermost loop
  when the function still needs its frame. It copies words in before the whole
  loop statement and out after it, including zero-trip exits. The region must
  avoid unresolved calls and conflicting workspace use. Trip estimates and
  weighted access savings must repay the copy cost; unknown trip counts use eight.
- Loops estimated at at most three iterations keep their existing DP index instead of
  borrowing the separate $0000 counter.

Differential switches on `zicc` are `--no-dp-homes`, `--no-register-cursors`,
`--no-index-elimination`, `--no-dp-summaries` and `--no-region-homes`.
`--no-dp-homes` also disables region promotion. Compiler parts `dp-homes`,
`compare-constants`, `index-elimination` and `region-homes` exercise semantic,
code-shape and fallback behavior against MSVC and enabled/disabled ROMs.

### Register loops and accumulator width

A separate loop IR selects straight-line byte operations in `while` and `for`
loops. It allocates up to two private near byte pointers to X/Y, keeps index
registers 16-bit, and enters A8 once for the entire region. It currently accepts
byte dereferences, byte stores, constants, constant addition/subtraction and
bitwise operations, plus unit pointer updates. A null byte or an integer
countdown (`n` or `n != 0`, with net `--n`) can control the loop. Countdowns
compare a running pointer against an endpoint, without switching A's width.

Scalar unit counters whose intermediate values are unobserved are derived from
the displacement of a pointer that advances or retreats one byte per iteration.
Nonzero initial values, multiple counters and unsigned wrap retain their normal
C meaning. A byte loaded for the condition can also supply the body until a
pointer update, byte operation or potentially aliasing store invalidates that
available value. Byte reads and writes remain in their original iteration order.

At a normal region boundary the emitter saves/restores the Y frame base and
materializes final pointer and counter values back into their homes. Only setup
and teardown use the existing arithmetic workspace; no new DP range is reserved.
If a function contains only constant local initializers, one eligible loop, final
constant byte stores and a scalar return, lifetime analysis can omit its frame.
It uses ABI input moves, saves only the needed initial cursor, writes terminal
bytes while still in A8, then returns the derived counter, final pointer or
constant. Stack arguments and both register argument orders are supported. Y is
preserved and A16 is restored before returning.

Pure returned counter expressions can be reduced to a constant plus a constant
multiple of the iteration count. Addition, subtraction and multiplication by
constants use target word arithmetic; narrowing casts stop this reduction.
Short framed regions still have setup/teardown costs, so register residency is
not a guarantee of a speedup for every trip count.

The pointer and counter homes must belong to the current invocation and must
not escape anywhere in the function. Calls, branches, early exits, nested loops,
observed intermediate counters, global running pointers, more than two pointers
and word/wide data operations currently use the ordinary emitter. Existing
affine-index cursors also prevent deferred updates to the same index. The
selection is structural and does not depend on function or variable names.
`--no-register-loops` disables both the region and loop leaf selections.

`tests/check-register-loops.py` compares 26 programs with the pass enabled and
disabled, using MSVC references and Mesen execution. It covers both register
argument orders, stack arguments, live homes, counter wrap, reverse traversal,
byte page boundaries, overlap and conservative fallbacks. Results are retained
under `build/register-loop-check/`. The string sample's `copy_text` is 30 bytes;
two fresh Mesen profiler runs measured its three calls at 2,482 master clocks,
versus 9,696 before this pass. The complete sample measured 38,888 versus 46,102
clocks. Profiler records and compiler/ROM hashes are retained under
`build/register-loop-performance/`.

### Indexed byte cursors and temporary lifetimes

The loop IR also accepts private word indices in a `left < right` condition,
byte accesses through invariant bases indexed by those variables, and net
`++left`/`--right` updates. Each base/index pair becomes an X/Y cursor. The
initial signed or unsigned relation is checked before forming the addresses;
the iteration count is the rounded-up half of the initial index distance.
An endpoint comparison then controls the byte-wide loop without per-iteration
index arithmetic or accumulator mode changes. Different invariant bases and
negative indices relative to an interior pointer are supported.

One unescaped byte temporary with one use per definition can live in B, the
accumulator high byte, while the region stays in A8. XBA saves/restores that
value around byte loads, stores and arithmetic. Its lifetime must end within
the iteration, and no use outside the loop may observe its final value. Other
cases retain their ordinary homes. No new direct-page storage is allocated.

For larger functions, final index and scalar counter values are materialized
after restoring the frame base. Pure affine parameter initializers and dead
scalar outputs also allow an indexed loop leaf to omit its frame. Zero-origin
bounds can consume the register arguments directly and omit dead index homes.
This selection uses the same loop IR and does not recognize function names.

`tests/check-indexed-byte-loops.py` checks 14 programs with MSVC and paired
Mesen execution, including empty/one-byte/negative lengths, odd/even sizes,
page boundaries, signed and unsigned bounds, stack/reordered arguments,
different bases, live indices, temporary arithmetic and fallback lifetimes.
Evidence is under `build/indexed-byte-loop-check/`. `reverse_text` is now 47
bytes instead of 158; its four sample calls measured 3,816 master clocks
instead of 15,456 in two agreeing fresh profiler runs. The full string sample
measured 27,248 clocks; records are under `build/indexed-byte-loop-performance/`.

### Short-circuit byte predicates and exit values

The loop IR accepts ordered conjunctions of byte truth/zero tests and byte
equality/inequality, including atomic negation. It preserves short-circuit read
order, tracks the available byte in A separately from the meaning of Z, and
compares directly against memory through the other index register. For example,
`*left == *right && *left` needs a fresh zero test after the comparison even
though the left byte is still in A. Different signed/unsigned byte extensions
are not collapsed into a raw byte comparison unless explicit char casts make
the equality representations compatible.

For a loop leaf returning a byte predicate, each loop failure edge carries its
available byte and comparison flags into the return. A matching comparison
supplies Z directly; an earlier short-circuit failure evaluates any missing
final comparison. A16 is restored without destroying Z before producing the
word Boolean result. Thus `text_equal` reads the right byte on a left-NUL exit
because its C return expression requires that read, but avoids reloading either
operand on a comparison mismatch. Calls and unsupported predicates retain the
general path. Framed regions continue to materialize live pointer/counter homes.

`tests/check-byte-predicates.py` compares 18 programs with MSVC and paired Mesen
runs. Tests cover equal/unequal/empty/prefix strings, high bytes, page boundaries,
predicate order, short-circuit null pointers, complemented results, reverse
steps, stack/reordered arguments, signed conversions and conservative fallbacks.
Raw byte returns are distinguished from Boolean returns. The same tests reject
a redundant `TCS; TSC` pair in emitted frame prologues.

`text_equal` is now 35 bytes instead of 124; its four sample calls measured
3,880 master clocks versus 17,898 previously. Two fresh profiler runs for every
ROM agreed: the full string sample measured 13,258 clocks versus stock VBCC's
25,152, with the existing FastROM/SlowROM distinction. The updated all-function
comparison, maps, hashes and raw profiles are under `build/byte-predicate-samples/`;
predicate regression evidence is under `build/byte-predicate-check/`.

### Word comparisons and condition flags

Word comparisons use an immediate, frame-relative, global or fixed array operand
directly when available. Thus `if (values[0] != 9)` loads the frame slot, executes
`CMP #9`, and branches on Z. If the RHS needs arbitrary evaluation, the left
value is saved on the stack and the RHS temporarily uses one scratch word. No
word comparison helper or unused high-word initialization is needed.

Equality uses CMP's Z flag; unsigned ordering uses its C/Z flags. Signed ordering
uses SEC/SBC so V is defined, then tests N xor V. For greater-than/less-or-equal,
equality is checked before adjusting N, preserving correct behavior at -32768
and +32767. Signed-word branch comparisons against literal constants use a
specialized path: zero tests reuse N/Z when valid, and nonzero constants resolve
overflow directly from the constant's sign before testing N/Z, without the
usual `EOR #$8000` normalization. `>`/`<=` handle equality separately. The
`compare-constants` compiler part checks boundary values and emitted shapes.
Byte operands are narrowed/promoted before the comparison, rather
than comparing a byte and its unrelated neighbor as one word.

Condition contexts branch directly from flags. Only value contexts such as
`result = a < b` materialize C's zero or one. The branch emitter tracks which
target follows immediately, including short-circuit expressions, so it can omit
the jump to that target. The final layout pass selects short branches after the
target distances are known. Long integer equality against a simple RHS compares
low and high words directly. Ordered/general long and floating comparisons use
their helper result directly for the branch, including unordered floating
results, without materializing a Boolean and comparing it with zero again.
Constant conditions select their branch without loading/comparing a constant;
word object loads and the combined long truth value already supply valid Z.
Other word truth tests also reuse Z when the immediately preceding emitted
instruction sets it from the full A result, including masked byte loads. Calls,
labels, index-register updates and accumulator mode changes require a fresh
comparison unless a subsequent instruction establishes A's flags.

## Control flow

Application rules: [Control flow](../operations.md#expressions-and-control-flow).

`if`/`else`, general `while(expression)`, `for`, `do`/`while`, `break`, `continue`
and early returns lower to local labels and near JMPs. Conditions consume either
a word, both words of a long, or binary32 magnitude bits (both signed zeros are
false). Constant-false loops are omitted; constant-true loops omit condition
work. General early returns share the function's epilogue; eligible leading
scalar guards return before creating a frame. Break targets the nearest loop or
switch; continue targets the nearest loop through any enclosing switches.
Misplaced break/continue are diagnosed while parsing, including unreachable code.
Generated transfers pass through the layout phase below.

### Switch dispatch

Switch expressions must have integer or enum type and undergo integer promotion.
The controlling expression is evaluated exactly once. The ordinary path in
`src/codegen/switch.inc` uses a chain of immediate comparisons. A dense word
range of 17 to 64 cases uses an unsigned bounds check and a balanced tree of
direct branches. Dense dispatch can also negate the case keys at compile time
and compare the input to a word negation directly. The value stays in A for
16-bit dispatch and A-low/X-high for 32-bit dispatch. Both words must match a long case.
No dispatch helper, scratch workspace or saved switch-value home is needed.

Labels can occur within nested statements, including Duff-style loops. The
emitter keeps generating switch-body labels beyond return/break/continue and
retains otherwise constant-false loop bodies while emitting a switch. Loops
inside a switch use ordinary lowering rather than register/DP/affine loop
shortcuts, preventing dispatch from bypassing borrowed-state setup or labels.
Case entry and switch exit invalidate division/remainder reuse state. Breaks in
nested switches do not make an enclosing infinite loop appear escapable.

Transfers to case bodies start as near JMPs so large bodies remain valid even in
interrupt segments outside the ordinary CODE branch-relaxation path.

The compiler suite runs tests/check-switch.py: separate-TU MSVC/Mesen execution,
16/32-bit signed/unsigned controls and char promotion, single evaluation, enum/
sizeof/constant cases, 64-case bodies, nested switches, fallthrough, Duff labels,
labels after returns and in false loops/ifs, and all break/continue targets.
Nineteen rejection tests cover constraints and converted duplicates. NTSC/PAL
checks use all four handlers, A8/A16/X8/X16 interrupted states, distant case targets
and full register/stack/scratch restoration.

### Iterative branch relaxation

`src/relax.c` runs inside the MSVC-built compiler. The emitter buffers its own
ca65 output; the pass tracks CODE labels and exact instruction sizes, including
the assembler's declared accumulator/index widths. It folds inverse-branch/JMP
skip pairs when their anonymous skip label has no other users. Anonymous targets
get stable private names so later expansion cannot retarget another branch.

The layout begins with short candidates, removes transfers to the next
instruction, then repeatedly expands branches that exceed -128 through +127
bytes from the end of the branch. Iteration stops only at a fixed point. Starting
small also catches mutually dependent branches that fit only when both are short;
a greedy long-to-short scan can miss those. Without alignment directives in CODE,
expansion only increases distances, so no oscillation is possible.

In-range conditional transfers use Bcc; in-range unconditional transfers use
BRA. Distant conditions retain inverse-Bcc over a 16-bit JMP, and distant
unconditional transfers retain JMP. Linker-only targets outside this translation
unit remain long. The pass understands only this backend's assembly subset and
rejects unsupported size-changing CODE directives rather than guessing. ca65
checks every resulting relative displacement when assembling the output.

`--no-branch-relaxation` preserves the original long sequences for comparison.
Tests cover both signed range limits, forward/backward transfers, cascades,
mutual dependencies, all eight conditions, mixed register widths, shared
anonymous labels and execution of the same C program with the pass on/off.
The paired inspection ROMs link the same runtime modules requested by their
imports; insertion sort links no integer or floating arithmetic helper code.

## Floating runtime and text I/O

Application rules: [Floating runtime and text I/O](../operations.md#floating-runtime-and-text-io).

The assembly files and `product.inc` under `runtime/ieee32/` implement IEEE arithmetic.
They round to the nearest value, breaking ties toward even, support gradual
underflow and use a fixed quiet NaN bit pattern. Multiplication uses the SNES
CPU's 8x8 multiplier. Division runs in software. The assembly wrappers preserve Y.
`provenance.json` identifies the earlier project-authored 65816 binary32
implementation and the source revision reused by zicc.

The integer-only exact decimal parser and formatter use assembly in `runtime/ieee32/`; `decimal.c` is retained as a reference for host and differential tests. Small decimal
integers through 2^24 use an exact bit-packing fast path. Other inputs use the
original exact-midpoint search; this can be substantially slower because each
candidate expands into decimal digits. `%g` defaults to six significant digits and
rounds ties to even; it is not a shortest-round-trip conversion. Special values,
hexadecimal parsing and subnormals retain the imported algorithms. The formatter
also supports fixed-point `%f`. Both accept precision from 0 through 32 and
round the exact binary32 value, including carries into the integer part.

Console format support and error behavior are listed in the
[application reference](../operations.md#console-formats). Formatter state and
integer digits live on the invocation's stack; floating decimal scratch/output
buffers remain shared.

`strtod` tail-jumps to the binary32 parser under the target's all-binary32
floating rule. `printf` updates a 4 KiB WRAM tilemap containing the BG1/BG2 maps;
the library NMI presents pending changes to VRAM. The console uses noninterlaced
Mode 5 at 512x224 with 64x28 characters and separate font/palette assets.

Linking the console supplies the `__console_init` startup hook; supplied linker
configurations default it to zero when absent. Both ordinary and console-named
startup objects honor it. Initialization runs after WRAM clearing and DATA
copying, configures/uploads the console, reads RDNMI once and writes `$80` to
NMITIMEN. A valid NMI wrapper is linked, or the user's NMI is used. Linked clock
ticks retain the user-code-then-library order.

The two 32x32 physical tilemaps are circular buffers showing 28 rows. The
logical cursor uses 64x28 character coordinates; scrolling advances the physical
top row and clears the new bottom row without copying old rows. A row is dirty
only when a cell changes. NMI coalesces adjacent dirty physical rows into DMA
ranges for both backgrounds, including changed hidden rows. Ring wrap splits
runs; separated runs avoid transferring clean gaps. Repeated identical output
and idle frames perform no DMA. Initial forced-blank upload initializes both maps.

Each foreground character/cursor/row update raises a busy counter. NMI skips
presentation while busy, preserving pending rows and scroll state for a later
frame. Otherwise it uploads all dirty ranges, then applies BG1/BG2 vertical scroll,
then clears the pending flag. A completed character may be presented before
the rest of a long printf; partially updated rows/scroll operations are protected.
There is no need to insert `fflush` calls for automatic display, even after main
returns. Explicit `fflush(stdout)`/`fflush(NULL)` waits until pending presentation
finishes; a clean flush returns immediately. NMI must remain enabled and the user
handler must leave enough VBlank time for a pending flush to finish.

User NMI code retains priority. Before presenting, the console checks VBlank and
latches the vertical counter. It defers starts on/after line 228 NTSC or 278 PAL,
leaving at least 34 full scanlines for scanning, DMA setup and at most 4 KiB of
transfers. Deferred presentation does not advance the displayed scroll position.
The console owns DMA channel 0, its BG1/BG2 resources and VRAM upload registers; a
presentation also uses the PPU H/V counter latch. No compiler DP scratch is used
by the library presentation routine. `tests/check-console.py`, within the prompt
suite, checks exact dirty ranges, ring wrap, clean flushes, busy deferral and late
user-handler deadlines on NTSC/PAL; prompt screenshots cover a full ring wrap.

## Native interrupt functions

Application rules: [Native interrupt functions](../operations.md#native-interrupt-functions).

The user function's actual assembly name labels its interrupt entry. Its native
vector points to that entry's bank-zero mirror, where JML enters the bank-$80
body. There is no separately named user-entry dispatch function. The prologue
establishes 16-bit A/X/Y, saves A/X/Y/D/DBR, establishes D=0 and DBR=$7E, and
saves only compiler arithmetic workspace words the handler can overwrite. Locals
use the ordinary private stack frame. Both `return;` and fallthrough restore
that frame and reach the common tail; RTI restores the original processor flags
and interrupted widths. Scratch sets combine writes in the selected emitted
body/frame cleanup with explicit clobber contracts for allowed helpers. Reads
alone do not require preservation. Comparisons only read workspace; the three
shift helpers overwrite `$E0/$E2`. Input staging stores count separately. Saves
use ascending PEI words and restores use the same set in descending order. Each
handler starts with a fresh mask, and scratch-free handlers emit no scratch
pushes/restores. The library clock tick remains scratch-free.

The wrapper uses nine software-stack bytes for registers plus two per saved
scratch word, the four-byte native hardware frame and any local frame. Nested
native interrupts need their own such space. See
[scratch preservation evidence](interrupt-scratch-preservation.md).

NMI composition uses consecutive linker segments:

1. `NMI_USER`: entry/prologue, user body and local-frame cleanup.
2. `NMI_LIBRARY`: only library fragments actually required by linked code.
3. `NMI_END`: scratch/register restoration and RTI.

Thus user DMA executes before library work, including on an early `return;`.
IRQ/BRK/COP use the same preservation scheme and finish directly with RTI.
The generated native handlers perform **no implicit RDNMI or TIMEUP reads**.
User code owns hardware-source acknowledgement, IRQ configuration/CLI and NMI
enabling. BRK/COP return through the processor's saved PC, already past their
signature operand. Emulation-mode vector slots remain unused RTI entries.

`runtime/vectors.s` uses weak `__vector_nmi/irq/brk/cop` defaults from
`linker/lorom32.cfg`, pointing unused native vectors at `unused_interrupt`.
Attributed definitions override the corresponding vector alias. `build/nmi.o`
is now an ar65 archive at the existing link path, so existing ld65 commands can
keep their object list. It contains separate clock, rate-query and default-NMI
modules. A link-time clock dependency extracts the default wrapper only if a
user NMI definition has not supplied `__nmi_entry`. Custom linker scripts must
provide the weak vector defaults and the three consecutive NMI segments.
NMI function-size symbols cover their entry/user portion; the library tail and
shared epilogue occupy separate segments. NMI_USER branches retain the safe
unrelaxed sequences; ordinary CODE branch relaxation also understands PEI.

`tests/check-interrupts.py` verifies all 16 handler subsets with/without clock
usage, plus region-query-only programs with/without a user NMI, in NTSC and PAL
(68 ROM runs). Tests exercise actual BRK/COP, PPU IRQ and NMI delivery, all four
A/X width combinations in combined-handler cases, user DMA before clock ticks,
early returns, scratch/register/stack restoration and malformed declarations.
IRQ fixtures explicitly read TIMEUP in user code; handlers otherwise read
neither acknowledgement register. Unused handlers and clock state are checked
for absence in linked images.

## Volatile accesses and MMIO

Application rules: [Volatile accesses and MMIO](../operations.md#volatile-accesses-and-mmio).

Each evaluated volatile scalar read/write is emitted, including discarded
reads, repeated reads, and read-modify-write expressions. Assignment expressions
return the assigned value without rereading the destination. Taking an address
or applying `sizeof` does not read the object. Short-circuit/conditional paths
read only evaluated operands; C's unspecified operand/argument order is unchanged.
Value caching, division/remainder reuse, leaf specialization, and loop transforms
that could change volatile observations are bypassed for affected expressions
or regions. Independent ordinary loops can still use the existing optimizations.

Byte objects use A8 for exactly one byte transfer, including near RAM accesses.
Word objects use one 16-bit transfer. Four-byte values use two 16-bit transfers
in increasing address order (low word then high word). Volatile aggregate reads
and assignments visit every object byte, including padding, in increasing
address order with byte transfers. No access width is inferred from a hardware
register: choose the C type matching the device's required width. Volatile is
not an atomic operation or a general synchronization primitive.

`tests/check-volatile.py`, run within the compiler verification suite, retains
NTSC/PAL byte-bus traces and checks qualification, access counts/order, NMI
composition and direct C MMIO enablement.

## Frame timing

Application rules: [Frame timing](../operations.md#frame-timing).

`runtime/clock.s` contains the four-byte frame counter, low-word increment with
carry and a high/low/high snapshot read. `clock()` returns A low/X high, retrying
if the high word changes, and preserves Y/D/DBR without masking NMI. There is no
initialization helper call on the read path. Counter and unsigned subtraction
wrap modulo 2^32; intervals spanning a complete wrap cannot be distinguished.
`runtime/clock_rate.s` owns the two-byte cached rate. Without a user NMI, the
archive supplies the minimal register-preserving wrapper from `runtime/nmi.s`.
Neither its wrapper nor the tick uses compiler arithmetic scratch or calls C.
The console presents dirty rows from its library NMI section during VBlank.

`tests/check-time.py` retains 18 NTSC/PAL timing, carry/wrap, snapshot-race and
width-preservation cases. Its application fixture enables NMI explicitly; it
requires zero RDNMI/TIMEUP reads in the handler. Both interrupt and time checks
run sequentially inside the existing compiler suite and shared verification queue.
Use `CLOCKS_PER_SEC` for timing conversions that must work on both NTSC and PAL.

## Cost-based loop unrolling

Application rules: [Cost-based loop unrolling](../operations.md#expressions-and-control-flow).

Eligible affine store regions can use full short-span unrolling or grouped
runtime loops with scalar remainders. Selection estimates time and code size;
`--no-loop-unroll` retains rolled output. See [cost policy and validation](loop-unrolling.md).

## Fixed multidimensional arrays

Application rules: [Fixed multidimensional arrays](../operations.md#fixed-multidimensional-arrays).

## Debugging and current limits

Application rules: [Debugging and current limits](../operations.md#debugging-and-current-limits).

Builds retain emitted assembly, ld65 `.map`/`.dbg`, and normalized `.sym` labels.
Function sizes are constants named `__size_*`, not end-address labels, so they do
not compete with the next function's entry in a debugger. Static function names
are prefixed with their translation unit. Current source mapping is assembly
mapping; full original-C source stepping is not implemented.

## Preprocessing

Application rules: [Preprocessing](../operations.md#preprocessing).

`src/preprocess.c` implements the supported preprocessing subset described in
[the application reference](../operations.md#preprocessing). It retains source
locations through markers, uses per-token disabled-macro sets to suppress
self/mutual recursion and diagnoses malformed active directives. Binary resources
are read without text conversion; numeric global-array bound inference is
handled by the initializer frontend. `tests/check-embed.py` covers binary resource
inclusion, probes and initializer limits.

`python tests/check-preprocessor.py` tests this stage through a standalone host
driver, without relying on target parser/codegen support. It also compares
fixtures against MSVC's conforming preprocessor. The mixed signed/unsigned `?:`
fixture is checked independently because the installed MSVC preprocessor retains
the selected signed arm's type. The compiler suite runs these checks under the
existing shared `make check` queue.
