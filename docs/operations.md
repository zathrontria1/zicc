# Supported C features and target rules

On the SNES, an `int` takes two bytes and an ordinary pointer can reach one
64 KiB bank of working memory. If you are bringing code over from a PC, check
[type sizes](#scalar-types) and [pointer sizes](#near-and-far-pointers) first.
For a game that talks to the hardware, see [hardware registers](#volatile-accesses-and-mmio)
and [interrupt handlers](#native-interrupt-functions). The compiler's register
and calling rules are in the [assembly reference](technical/operations.md).

## Cross-file optimization

The builder normally compiles each C file on its own. Pass all your C files to
`tools/build-rom.py` with `--lto` to let the compiler replace a call in one
file with the function body from another. Each file still has its own macros
and private names. The usual rules for automatic, hinted, forced and disabled
inlining still apply. See [source LTO](technical/source-lto.md).

## Machine and storage

- Normal ROM builds use FastROM HiROM, starting at 64 KiB and growing up to 4 MiB.
  See [building and sizing your ROM](rom-allocation.md) for placement and outputs.
- Ordinary objects use near RAM in bank `$7E`. General globals can use the
  space above the hardware stack through `$7E:FFFF`.
- Explicit `__dpage` globals use `$0022`–`$00FF`.
- `__dpage` places the declared object, including a pointer variable; it does
  not place the pointer's target or change its width. Eligible dereferences of
  named nonvolatile DP pointers can use their stored address directly. Other
  accesses retain the normal lowering; see
  [direct DP pointer accesses](technical/dpage-pointer-access.md) for limits.
- Calls support up to 256 arguments and declarations up to 127 parameters.
  Calls are rejected if their outgoing stack arguments plus three bytes for a
  possible long-call return address exceed the compiler's fixed 1 KiB
  per-call limit.
- Startup clears allocated zero-initialized storage in both WRAM banks and
  copies initialized WRAM objects before console initialization and `main()`.
- Returning from `main()` enters a halt loop. Calling `main()` from C is rejected.

### Hardware stack

Functions share a hardware stack for return addresses and temporary storage.
It starts at `$0100` and defaults to 1,024 bytes. The stack pointer (SP)
starts at the top, `$04FF`, and moves down as the stack fills.
You can reserve 256–7,936 bytes. Each option below reserves 1,536 bytes and
starts SP at `$06FF`.

- ROM builder: `--stack-size 1536`
- Make: `make minimal STACK_SIZE=1536`
- Manual ld65 link: `-D __STACK_SIZE__=1536` with any supplied linker config

The linker exports `__STACK_BOTTOM__`, `__STACK_TOP__` and `__NEAR_START__`.
Allow enough space for local variables, nested calls, recursion and interrupts.
The runtime does not check how much stack space is left.

### Low-RAM placement

Use the `__loram` placement attribute when a static-storage object's entire storage
must fit between `__NEAR_START__` and `$7E1FFF` (by default
`$7E0500`–`$7E1FFF`):

```c
__loram unsigned char dma_table[256];
static __loram unsigned flags;
extern __loram unsigned char shared_table[];
```

- Constrained objects allocate first. Ordinary globals can use the remaining
  low space and the rest of bank `$7E`. At the maximum stack reservation,
  `__NEAR_START__` is `$7E2000` and there is no space for `__loram` objects.
- A final-link overflow, including other translation units and alignment, is an
  error. Constrained objects never spill past `$1FFF`.
- The attribute places an object; it does not change pointer width or its
  pointee. Its address remains a 16-bit near pointer.
- Initialized `__loram` objects are copied from ROM before `main()`. This also
  applies to `__loram const` objects, which retain C const semantics in near RAM.
- Put the attribute on declarations in shared headers and before definition/use.
  Later declarations in the same translation unit may omit it. Used extern
  constraints check the defining object's complete size, including incomplete
  array declarations.
- It applies to static storage duration, with or without the `static` keyword.
  Automatic locals, parameters, functions, typedef placement and `__dpage`
  combinations are rejected. A block-scope declaration can use `static __loram`.
- Arithmetic workspace remains in direct page. Persistent console and decimal
  buffers and the clock frame counter backfill bank `$7F` from the top down;
  ordinary application objects and the near heap remain in `$7E`. Public stream
  tokens and `errno` retain their near addresses.

### Expanded application WRAM

```c
__hiram unsigned char tiles[8192];
extern __farram unsigned char tiles[8192]; /* Same attribute as __hiram */
__xbankram unsigned char staging[80000UL];
```

`__hiram` and `__farram` place a whole object in either WRAM bank. Each object
can occupy at most 65,536 bytes. `__xbankram` also permits an object to straddle
`$7E:FFFF` and `$7F:0000`. An object can use more than 65,536 bytes if it fits
in the free space in both banks. Mark every declaration of a spillable object
with the same attribute. These attributes also apply to block-scope statics.
Combining placement attributes or applying them to automatic storage,
parameters, functions, or typedefs is an error.

Addresses and array decay always produce four-byte far pointers, including
when the object lands in `$7E`. Use `__far` pointer parameters for these objects.
The automatic HiROM builder can select absolute instructions for a proven
near access. This retains the declared pointer type and far relocations.
A spillable `const` object is read-only in C and has a WRAM run address.
Static initialization uses its ROM load image or a startup clear, as
appropriate.

The default stack leaves 64,256 bytes in `$7E` and up to 65,536 bytes in
`$7F`, for 129,792 bytes before ordinary allocations, runtime backfill,
alignment, and heap headers. The builder places ordinary allocations first
and reserves the live runtime spans at the top of `$7F`. It prefers `$7E`
for spillable storage unless the near heap is linked. A crossing object
occupies the near bank's tail and leaves no contiguous space for that heap.
The allocation JSON records run addresses, ROM load spans, padding, and
the usable near heap extent.

If ordinary static allocations fill `$7E`, the builders report a 16-bit WRAM
overflow and the excess in bytes. Move eligible buffers to expanded WRAM and
use far pointers where their addresses are taken. If the standard heap runs
out at runtime, `malloc` returns `NULL`.

Use `tools/build-rom.py` for automatic HiROM and ExHiROM or `tools/link-runtime-ram.py`
for manual LoROM and HiROM. Manual builds use the current runtime startup
object and a supplied linker configuration. Separately compiled and
archived objects can retain conservative far instructions. Bare ld65
reports an unassigned segment for spillable definitions.

`size_t` is 16-bit. An object of 65,536 bytes or more has an
`unsigned long` result for `sizeof`. `far_memcpy`, `far_memmove`, and
`far_memset` in `<string.h>` accept far destinations and
`unsigned long` byte counts. The standard memory routines take near
destinations.

To allocate far memory at runtime, set aside a WRAM buffer just for the
allocator. An array of `unsigned int` gives it the required even address.
Declare a separate `far_heap_t` to track free space. Pass it, the buffer and
the buffer's size in bytes to `far_heap_init` from `<stdlib.h>`. Keep both
objects alive for as long as you use the heap. Pass the same control object
to `far_malloc`, `far_calloc`, `far_realloc` and `far_free`. These functions
use far pointers and accept wide byte counts. Call them from foreground code.
The standard allocator uses near pointers into free space in bank `$7E`.

### Cartridge SRAM

Build with `tools/build-rom.py --sram-size KIB` to add battery-backed storage.
The default is zero. Choose a power of two starting at 2 KiB. The supported
address profiles are:

| Mapping | CPU address windows | Window size | Maximum capacity |
| --- | --- | ---: | ---: |
| LoROM | `$70–$7D:$0000–$7FFF` | 32 KiB | 256 KiB |
| HiROM | `$A0–$BF:$6000–$7FFF` | 8 KiB | 256 KiB |
| ExHiROM | `$80–$BF:$6000–$7FFF` | 8 KiB | 512 KiB |

For a manual build pass `--sram-size KIB` to `tools/link-runtime-ram.py`.
Use `--mapping lorom` or `--mapping hirom` when using a custom configuration
filename. LoROM builds with more than 32 KiB of SRAM need a ROM of at least
2 MiB. When compiling a manual build that uses `__sram`, pass the matching
`--sram-layout BANK,WINDOW_BYTES,CAPACITY_BYTES` to zicc. For example, a 64 KiB
LoROM cartridge uses `--sram-layout 112,32768,65536`. Finalize the raw ROM
with `romtool` as usual. Match the board wiring and installed chip to the
configuration when running on hardware.
Mesen's generic cartridge loader caps SRAM at 256 KiB.
[Mesen cartridge loader](https://github.com/nesdev-org/MesenCE/blob/master/Core/SNES/BaseCartridge.cpp#L243-L247).

The build setting alone is enough for raw far-pointer access. For example,
`*(volatile unsigned char * __far)0xA06000UL` accesses the first byte of
HiROM SRAM. Advance to the next mapped window after reaching its end.

For portable byte transfers use `sram_read(offset, dst, count)` and
`sram_write(offset, src, count)` from `<sram.h>`. Offsets are 32-bit byte
counts from the start of SRAM. Each call copies up to 65,535 bytes to or
from a valid near WRAM buffer. Call from foreground code. The functions
return zero for success and reject requests past `sram_capacity()`.

```c
typedef struct { unsigned char bytes[4096]; } save_data_t;
static __sram(0) save_data_t saves[8];
```

In a 32 KiB HiROM build this declaration stores two records per window.
`saves[slot]` and `&saves[slot]` select one record. Use direct indexing for
spanning arrays and keep pointer arithmetic within the selected record.
An array that fits in one window supports ordinary far-pointer decay.
Specify a complete matching `__sram` declaration in every source file
that refers to the object. SRAM definitions take no initializer and
startup leaves their contents intact. The allocation JSON reports each
object's CPU address, logical byte offset, and size. The game owns the
save format and the layout when it mixes the three access methods.

### Scalar types

| Type | Size and representation |
| --- | --- |
| `char`, `unsigned char` | Unsigned, 8 bits |
| `signed char` | Signed, 8 bits |
| `_Bool` (`bool` via `<stdbool.h>`) | One byte, values 0 and 1 |
| `short`, `int` | Signed, 16 bits |
| `unsigned short`, `unsigned int` | Unsigned, 16 bits |
| `long`, `unsigned long` | 32 bits |
| `long long`, `unsigned long long` | 64 bits |
| `float` | IEEE binary32, 32 bits |
| `double`, `long double` | IEEE binary32 by default, IEEE binary64 with `--binary64` |
| Ordinary pointer | 16-bit near address |
| `__far` pointer | Four-byte storage for a 24-bit address |

- Plain char is distinct from signed char and unsigned char. It has the
  same representation and promotion as unsigned char.
- Short and int have distinct type identities. Short promotes to int and
  unsigned short promotes to unsigned int on this target.
- Signed integers use two's complement; the target is little endian.
- `sizeof` reports object size. Arrays have packed elements; structure and union
  padding follows the rules below.
- Character values promote to `int`. Arithmetic uses the usual conversions to
  the common integer or floating type.
- `_Bool` promotes to `int`. Assignment, initialization, parameter/return conversion
  and casts normalize scalar values to 0 or 1; both floating zeros become false.
- Integer-to-float conversions round to nearest, ties to even. Runtime
  float-to-integer conversions truncate toward zero; values outside the
  destination type's representable range have no promised behavior.
- Signed overflow, invalid shifts and integer division by zero have no promised
  behavior. Signed integer division truncates toward zero; the remainder has the
  dividend's sign.

### Near and far pointers

An ordinary (near) pointer holds a location inside RAM bank `$7E`. A far
pointer holds both the bank number and the location within that bank. Use a
far pointer to reach data stored in ROM or in the other RAM bank.

- `unsigned char * __far p` declares a far pointer. Its four bytes hold a
  two-byte address, a one-byte bank number and a zero padding byte.
- `__far` qualifies the pointer level immediately after `*`. `const` and `__far`
  may appear in either order.
- Explicit casts from a pointer to an integer keep the raw address bits:
  a far pointer yields its 24-bit address (`0x00BBAAAA`, bank in bits 16-23)
  in 32-bit (`long`/`unsigned long`) and 64-bit integers, and truncates to its
  low bits in narrower integers. A near pointer zero-extends its 16-bit offset
  (`0x0000AAAA`) in 32-bit and 64-bit integers without adding bank `$7E`;
  widen to `__far` first if you need the full `$7E` address.
  Pointer-to-integer casts are runtime conversions and cannot initialize
  static integers from symbol addresses.
- Explicit casts from an integer to a pointer use the low 16 bits for near
  pointers and the low 24 bits (clearing the padding byte) for far pointers;
  signed 16-bit inputs sign-extend before masking to 24 bits.
- Typedefs and pointers to arrays retain the qualifier.
- A compact pointer type supports up to 31 consecutive pointer levels.
- A near pointer to a far-pointer object is still two bytes. For example,
  `typedef char * __far Far; Far *slot;` declares a near pointer named `slot`.
- Named initialized const objects without an explicit WRAM attribute and string literals reside in ROM and produce
  far addresses automatically.
- `const char *p` is a near pointer to read-only RAM. Pointee `const` does not
  imply a far pointer; readers accepting either ROM or RAM need far parameters.
- Near-to-far conversion is implicit: non-null pointers gain bank `$7E`, and
  null remains all zeroes.
- Implicit far-to-near conversion is diagnosed. An explicit narrowing cast
  requires null or a bank-`$7E` address with a nonzero low word. Known wrong-bank
  constants, ROM addresses and `$7E:0000` are diagnosed.
- Far arithmetic and comparisons use the full address. Far pointer differences
  use signed `long`; near differences use signed `int`.
- Pointer stepping and differences use the pointed-to element size, including
  whole array rows. Pointer arithmetic must remain within valid C object bounds.
- Pointer initializers accept nulls, explicit numeric pointer constants and
  static object/string addresses, including constant member/element offsets.
  ROM addresses still require explicit far pointer destinations.

## Enumerations

- Named and anonymous enums, enum typedefs and complete enum-tag references are
  supported at file and block scope. Trailing commas are accepted.
- Enum objects have signed 16-bit `int` representation, size two and alignment
  two. Enumerators are `int` constants with no object storage.
- Values start at zero and increment, or use an integer constant expression.
  Duplicate values are allowed; duplicate names in the same scope are rejected.
- Every value must be between -32768 and 32767, including implicit successors.
  After 32767, use an explicit valid initializer to restart the sequence.
- Enum constants can appear in array bounds, casts, `sizeof` expressions and
  ROM initializers. Floating or nonconstant initializers are rejected.
- Struct, union and enum tags share a namespace. Enumerators share the ordinary
  identifier namespace with objects, functions and typedefs. Block definitions
  can shadow outer definitions and expire at block exit.
- Enumerators cannot be assigned, incremented or addressed.
- Incomplete enum forward declarations are unsupported.

## Structure definitions and layout

- Tagged and untagged structures/unions, typedef aliases, named nested members
  and fixed multidimensional array members are supported.
- Tagged structures and unions support forward declarations. Completing a tag
  completes earlier references; each definition has its own type identity,
  preserved by typedefs. Matching layouts alone do not make types compatible.
- Block tags can shadow outer tags. An inner standalone forward declaration
  introduces a new tag; an ordinary reference uses the nearest visible tag.
- Character members align to one byte. Other scalars, pointers and nested
  aggregates align to two bytes. Structure members retain declaration order.
- Every structure has two-byte alignment and an even total size. Array stride
  includes tail padding, without rounding to a power of two. For example,
  `{ char flag; unsigned long value; }` has offsets 0 and 2 and size 6.
- Union members overlap at offset zero. Union size is the largest member's size
  rounded up to an even byte count, with two-byte alignment.
- Unions have no runtime discriminator. Reading another member interprets the
  stored bytes without numeric conversion. Partial writes retain other bytes;
  unwritten local bytes have no promised value.
- `sizeof` accepts complete aggregate types, objects, dereferenced pointers and
  fixed array types without executing operand side effects.
- Pointers to incomplete types are valid. Object storage, embedded members,
  `sizeof` and pointer arithmetic require complete object types.
- Larger layouts can be used through far pointers and in `__xbankram` storage,
  up to the available WRAM capacity. Ordinary object, argument, and frame
  limits still apply to aggregate values passed by value.
  There are at most 64 tag/type records per translation unit, including untagged
  definitions.

### Member access and qualification

- Use `.` on aggregate objects and results, and `->` on a pointer to a
  complete aggregate. A member of a non-lvalue result can be read.
- Scalar members support reads, writes, compound assignment, pre/post increment
  and address-of. Nested member/index expressions are supported.
- Array members decay to their first element's address except in `sizeof` and
  address-of. Taking an array's address produces a pointer to its array type.
- Member-access base expressions are evaluated once, including updates whose
  right-hand side calls a function.
- Const aggregates qualify their members, including pointer and array members,
  without making a mutable object reached through a pointer member const.
- Address-of and indexing preserve qualification. Implicitly discarding pointee
  const qualification is diagnosed.

### Global initializers

- Explicitly initialized const globals live in ROM unless given a WRAM placement attribute.
  Writable initialized globals live in RAM and receive their initial contents
  before `main()` or the console.
- Supported initializers include scalars, fixed arrays, structures and unions,
  with nested braces, trailing commas and zero filling of omitted values.
- Union initializers select the first member recursively. Additional values
  beyond the first member are rejected.
- Padding and unused union bytes are initialized to zero.
- Integer constant expressions use target widths and support casts, arithmetic,
  bitwise/comparison operators, conditional expressions and short-circuiting.
  Invalid evaluated divisions, shifts and signed overflow are diagnosed.
- Static arithmetic initializers support binary32 and binary64 expressions, including mixed
  integer and floating operands. Evaluated overflow, division by zero and
  out-of-range floating-to-integer conversions are diagnosed.
- Global arrays can infer their outer dimension from a nonempty
  initializer. Read-only ROM objects can occupy up to 65,536 bytes. Ordinary
  initialized WRAM objects can occupy up to 65,534 bytes. The expanded WRAM
  attributes have the separate limits described above.
- `sizeof` normally has the 16-bit unsigned `size_t` type. As a target
  extension, a result of 65,536 or more has type `unsigned long`. Keep that result in
  a 32-bit type when storing or passing it. Conversion to 16-bit `size_t`
  wraps to zero.
- Character arrays accept string initializers, adjacent strings and embedded
  NULs. An omitted bound includes the terminator; an exact character-count bound
  may omit it. Larger arrays are zero filled; shorter arrays are diagnosed.
- Pointer fields and arrays retain linker relocations for static object/string
  addresses. Near-to-far RAM addresses gain bank `$7E`; ROM banks are resolved
  by the linker. Incompatible pointer types and implicit narrowing are rejected.
- Nested arrays, structs and unions can omit their inner braces. Explicit inner
  braces limit initialization to that subobject, and omitted entries are zero filled.
- Designators and empty initializer lists are unsupported.
- Explicit `__dpage` initializers are unsupported. Const globals without an
  explicit initializer retain zero-filled RAM storage.

### Local initialization and static storage

- Automatic arrays, structures and unions support nested braced initialization,
  runtime scalar expressions and zero filling of omitted subobjects. Structures
  and unions can also initialize from another value of the same aggregate type.
- Automatic arrays can infer their outer bound from a braced list or character
  string. Initialization runs each time execution reaches the declaration.
- Block-scope `static` objects have private static storage, constant or zero
  initialization before `main()`, and normal block scope/shadowing. Inlined calls
  share the original static object. Initialized nonvolatile const statics use ROM
  under the same near/far rules as file-scope objects.
- Comma expressions evaluate left then right, discard the left value and produce
  a non-lvalue result. Parenthesize them in argument and initializer lists.
- A declaration in a `for` initializer is scoped to that loop.
- Local objects can use explicit `auto`. Block-scope `extern` and function
  declarations resolve through linkage while retaining block scope.
- Type specifiers, qualifiers and storage classes can appear in supported
  combinations in different orders. Ordinary declarators can be parenthesized.
- Compatible file-scope incomplete array declarations merge with complete
  definitions; conflicting bounds and element types are rejected.
- Typedefs can name arrays with an unknown outer bound. An object declared
  through such a typedef can infer its bound from its own initializer.
- A tentative definition with external linkage can be completed later in the
  translation unit. At the end of the unit, an array still missing its outer
  bound gets one element. An incomplete structure or union requires a definition
  of its tag before the end of the unit.

### Unsupported aggregate features

- Aggregate arithmetic, comparison, casts, conditional/comma values and compound
  assignment.
- Nameless aggregate member promotion and flexible array members.
- Empty definitions, duplicate members, incomplete or void members and layouts
  exceeding the limits above.

## Structure and union assignment

- Simple assignment copies complete aggregates with the same type identity,
  including array members, nested aggregates and padding.
- Sources may be const. Destinations must be modifiable and contain no const
  embedded member, recursively through arrays, structures and unions.
- Const pointer members prevent aggregate assignment; pointers to const objects
  do not. Qualifying a pointer typedef qualifies the pointer object.
- Arrays themselves are not assignable. Self-assignment is valid; partial
  overlap between distinct objects is outside the assignment contract.
- Both addresses are evaluated once, destination first. Results are non-lvalues
  and support chaining and member reads.
- Array-containing assignment results use snapshots for member access, so later
  index evaluation cannot change the selected result. Frame-capacity limits apply.

## Calls, frames and returns

- Function definitions, prototypes, recursion and scalar arguments/returns are
  supported. Prototypes check argument counts, types and conversions.
- Array parameters adjust to pointers, including pointers to multidimensional
  rows. Function parameters declared with function type adjust to function
  pointers. `register` is accepted on parameters and locals as a storage hint.
- Implicit `int`, K&R definitions, empty-parenthesis non-prototype declarations
  and calls to undeclared functions are accepted with warnings. An undeclared
  called function is assumed to return `int`; undeclared objects remain errors.
- Calls without prototypes apply default promotions: character values become
  `int`, and `float` uses the selected `double` ABI.
- K&R parameter declarations bind by identifier-list order. Character parameters
  are converted back to their declared type inside the function body.
- Prototypes combined with legacy declarations must match promoted parameter
  types. A prototype `char` parameter or a variadic prototype cannot be combined
  with a non-prototype declaration.
- Calls use the declaration visible at the call. Source LTO checks compatible
  declarations across its input translation units. Ordinary object linking
  resolves symbols without comparing C types.
- Aggregate arguments use private stack copies, and aggregate results use a
  caller-owned temporary whose near address is the first stack argument.
  The ordinary scalar register positions stay the same. Variadic definitions
  can access promoted scalar, pointer, and aggregate arguments using
  `<stdarg.h>`. Interrupt functions have additional rules below.
- Eight-byte scalar arguments use stack slots; eight-byte scalar results use
  the arithmetic scratch result slot. The wide arithmetic and conversion
  routines are separate archive members and are linked only when referenced.
  Interrupt handlers save the scratch words their own generated code uses;
  narrow handlers do not acquire wide-helper save/restore code.

### Function pointers

- Function pointers contain a 24-bit callable entry address with a zero padding
  byte. Function types are distinct from object types, and the near/far rules
  for data pointers still apply.
- Function designators decay to pointers. Address-taking, compatible assignment,
  explicit function-pointer casts, null and equality comparisons, and indirect
  calls through prototypes are supported. Startup and interrupt entries have
  special calling conventions and cannot be used as callbacks.
- Use `tools/build-rom.py` to link a program that takes function addresses.
  It adds one adapter per referenced function and selects the near or long
  entry according to the final bank layout. The adapter retains the target's
  normal argument and result registers and supports nested indirect calls.

### Bit-fields

- Plain and explicitly signed `int` fields are signed. Unsigned fields narrower
  than 16 bits promote to `int`. Writes retain the low bits of the value.
- Fields pack from the least significant bit of an aligned 16-bit word and
  never straddle words. Unnamed fields reserve bits, an unnamed zero-width field
  starts a new word, and union fields start at bit zero.
- Reads and updates use the containing word. Updates preserve adjacent fields
  and evaluate the storage address once. Address-taking, `sizeof`, and
  `offsetof` on bit-fields are diagnosed.

## Expressions and control flow

- Integer arithmetic, bitwise operators, shifts, comparisons, scalar casts,
  assignment, compound updates, increments, dereferences and address-of are
  supported, subject to the target and conversion limits above.
- Floating addition, subtraction, multiplication, division and comparison use
  the operand's binary32 or binary64 representation. Both signed zeros are
  false in conditions; NaNs retain IEEE behavior.
- `&&`, `||` and `?:` evaluate only the selected operands. Updates evaluate their
  destination address once.
- `if`/`else`, `while`, `for`, `do`/`while`, `break`, `continue` and early returns
  are supported. `break` targets the nearest loop or switch; `continue` targets
  the nearest loop, including through an enclosing switch.
- `goto` targets a function-scope label. Duplicate and undefined labels are
  diagnosed. Functions with labels use stable local homes and skip structured
  control-flow optimizations. Misplaced `break` and `continue` are diagnosed.

### Switch dispatch

- Controls must be integer or enum expressions. Integer promotion applies, and
  the controlling expression is evaluated once.
- Cases accept integer constant expressions, including enums, casts, `sizeof`
  and constant arithmetic/conditional expressions. Values convert to the promoted
  control type before duplicate checking.
- Stacked labels, fallthrough, nested switches, a default in the middle of the
  body and labels nested inside statements (including Duff-style loops) work.
- Without a matching case or default, execution continues after the switch.
- Duplicate converted cases, multiple defaults, noninteger controls,
  nonconstant cases and labels outside switches are diagnosed.
- At most 64 loop/switch contexts can be active at once.

## Fixed multidimensional arrays

- Fixed-size nested arrays preserve row types through indexing, typedefs,
  address-of and parameter adjustment.
- Array parameters decay only at the outer dimension: `int a[][5]` receives a
  near pointer to a five-int row.
- Row-pointer stepping, nested ROM initializers and per-dimension `sizeof` are
  supported.

## Floating runtime and text I/O

- Floating arithmetic uses round-to-nearest/ties-to-even, gradual underflow and
  a fixed quiet NaN for each format. `strtod` parses to the selected `double` format.
  Ctype functions are ASCII-only.
- Decimal formatting supports special values and subnormals. Parsing also
  supports hexadecimal input. `%g` defaults to six significant digits and is not
  a shortest-round-trip conversion; floating precision ranges from 0 through 32.
- Floating decimal scratch/output buffers are shared; decimal I/O is not reentrant.
- `fgets` replays the bundled input file on each call. It does not implement
  interactive controller or keyboard input.
- `printf` accepts a far format string. `strtod` accepts far input and a near
  pointer to a far end-pointer object. Mutable buffers and `FILE` objects remain
  near.

### Console formats

- Supported conversions include `%%`, `%d`/`%i`, `%u`, `%ld`/`%li`,
  `%lu`, `%x`/`%X`, `%lx`/`%lX`, `%lld`/`%lli`, `%llu`, `%llx`/`%llX`, their `j`-length
  equivalents, and `%c`.
- `%s` takes a near RAM string. `%S` takes a far string, including ROM literals;
  passing a far pointer to `%s` is a type mismatch.
- Format strings and far strings can cross banks.
- Decimal widths through 999, `-`/`0` flags, integer precision and string precision
  are supported. Integer precision overrides zero padding; string precision
  limits bytes read.
- `%f` and `%g` require the floating console build (`CALC=1`). The basic console
  does not link the floating library.
- Success returns the number of emitted characters. Unsupported conversions or
  excessive width/precision print `?`, set `console_error=1` and return -1.
- Dynamic `*` widths/precision, `+`, space and `#` flags, octal conversions,
  `%e`, `%a`, `%p`, `%n` and wide characters are unsupported.

### Display and interrupt ownership

- The console displays 64×28 characters at 512×224 in noninterlaced Mode 5,
  using BG1/BG2, its font/palette and tilemap VRAM, DMA channel 0, VRAM upload
  registers and the PPU H/V counter latch. Coordinate game rendering with those
  resources; see the [console layout](technical/console-hires-trial.md).
- Linking the console initializes it after WRAM/DATA setup, clears RDNMI once and
  enables NMI before `main()`. User NMI state must be valid through zero/static
  initialization because the handler can run before `main()`.
- Timer IRQs and automatic joypad reading remain disabled until configured by
  the application.
- NMI presents changed rows during VBlank after the user handler. Busy foreground
  updates or late VBlank entry defer presentation to a later frame.
- Output wraps, handles CR/LF and scrolls. Automatic presentation continues
  without `fflush`, including after `main()` returns.
- `fflush(stdout)` and `fflush(NULL)` wait for pending presentation; a clean flush
  returns immediately. NMI must remain enabled, and the user handler must leave
  enough VBlank time for presentation to finish.

## Function inlining

Ordinary functions can inline automatically at profitable same-TU call sites.
`inline` is a hint with C inline linkage semantics. Use `__forceinline` or
`__attribute__((always_inline))` to require eligible substitution, and
`__noinline` or `__attribute__((noinline))` to preserve calls. Forced failures
produce a diagnostic; automatic/hinted calls retain their ordinary fallback.
`--no-inline` disables automatic and hinted selection while honoring forced
requests. See [selection, linkage and limits](technical/inlining.md).
`__attribute` is an alternate spelling of `__attribute__`. An empty attribute
list has no effect.

## Basic inline assembly

`__asm("wai");` and `__asm__ volatile ("nop");` emit instructions directly.
This subset accepts whitespace-separated `wai` and `nop` instructions. It
treats the statement as a compiler barrier and preserves the C register and
bank contract. Extended asm operands and clobbers are unsupported, as is basic
asm inside interrupt functions. Use a ca65 unit for larger assembly routines.

## Native interrupt functions

Keep interrupt handlers free of library calls and operations that compile to
runtime helper calls. Defer helper-dependent work such as floating-point
arithmetic, parsing and formatting to foreground code.

Declare a native-mode vector handler before its return type:

```c
__interrupt(nmi) void vblank(void)
{
    /* Application VBlank work, including DMA */
}
```

- Supported attributes are `__interrupt(nmi)`, `__interrupt(irq)`,
  `__interrupt(brk)` and `__interrupt(cop)`.
- Each handler needs external linkage, `void` return type and an explicit `(void)`
  parameter list. Each vector accepts one definition; prototypes must agree.
- Ordinary calls to handlers are rejected. Handlers cannot return values or call
  ordinary C functions.
- Software comparison/shift helpers are permitted. Helpers using shared hardware
  arithmetic or floating state are rejected; inline constant arithmetic works.
- Registers, interrupted widths and overwritten compiler scratch are restored
  on return. Account for interrupt stack usage when sizing local storage.
- User NMI work precedes library work, including after an early `return;`.
- Generated handlers perform no implicit RDNMI or TIMEUP reads. The application
  owns hardware acknowledgement, NMI enabling and IRQ configuration/CLI.
- BRK/COP resume past their signature operand. Emulation-mode handlers are not
  supplied as C application handlers.

## Volatile accesses and MMIO

Some SNES addresses control hardware. Reading or writing one of them can
change the device. Use a bank-zero far pointer to reach a hardware register,
match its width, and mark the register `volatile` so each requested access
happens.

- `volatile` can qualify scalars, pointer objects, array elements and aggregate
  members, and can combine with `const` and `__far`.
- `volatile T *p` qualifies the pointee; `T * volatile p` qualifies the pointer.
  Aggregate qualification applies to members, not objects reached through pointer
  members. Implicitly discarding pointee volatile qualification is diagnosed.
- Every evaluated volatile read/write is retained, including discarded and
  repeated reads. Assignments return their value without rereading the destination.
- Address-of and `sizeof` do not read the object. Short-circuit paths access only
  evaluated operands; C's unspecified operand/argument order remains unspecified.
- Byte objects transfer exactly one byte. Word objects use one 16-bit transfer;
  four-byte values use low-word then high-word transfers. Volatile aggregate
  reads/assignments visit every byte, including padding, in increasing order.
- Choose the C type matching the hardware register width. Volatile does not
  provide atomicity or general synchronization.
- Near `(char *)0x4200` addresses RAM `$7E:4200`. MMIO requires an explicit
  bank-zero far pointer.

For an application without the console's automatic initialization, the following
statements can run inside `main()` after handler state is ready:

```c
#define RDNMI (*(const volatile unsigned char * __far)0x004210UL)
#define NMITIMEN (*(volatile unsigned char * __far)0x004200UL)

(void)RDNMI;
NMITIMEN = 0x80;
```

This reads RDNMI once and writes NMITIMEN once, touching neither TIMEUP nor the
adjacent WRIO register. Console initialization already performs this sequence;
subsequent changes belong to the application.

## Frame timing

- `<time.h>` provides unsigned 32-bit `clock_t`, `clock()` and a runtime
  `CLOCKS_PER_SEC` expression.
- `clock()` counts delivered NMI frames, including waits, starting with the first
  NMI after enabling. It does not initialize hardware, enable NMI or acknowledge
  RDNMI/TIMEUP. The counter does not advance while NMI is disabled.
- `CLOCKS_PER_SEC` reports nominal 60 Hz NTSC or 50 Hz PAL, detected through
  STAT78. Querying the rate alone does not require an NMI handler or frame counter.
- Without the console, initialize handler state and explicitly enable NMI as in
  the MMIO example. Clock API calls never rewrite NMITIMEN.
- Counter values and unsigned subtraction wrap modulo 2^32. Intervals spanning
  a complete wrap cannot be distinguished.
- This is frame-quantized elapsed time, not CPU cycles or calendar time. Nominal
  rates approximate physical refresh frequencies. `time_t`, `time()` and calendar
  conversion are unsupported.

## Preprocessing

- Literal quoted/angle includes, object/function-like macros, `#undef`, nested
  `#if`/`#ifdef`/`#ifndef`/`#elif`/`#else`/`#endif`, `#elifdef` and `#elifndef`
  are supported. `__FILE__` and `__LINE__` expand at the use site.
- Conditional expressions support `defined`, integer/single-byte character
  constants, unary/arithmetic/shift/comparison/bitwise/logical operators and `?:`.
  Unknown identifiers become zero; logical operators and `?:` short-circuit.
- Preprocessing uses signed/unsigned 64-bit arithmetic independently of target
  `int`. Signed overflow has no promised behavior.
- Function macros accept up to 127 named parameters, empty arguments, nested calls
  and parenthesized commas. Arguments expand before substitution except operands
  of `#` and `##`, which use raw tokens for stringification and pasting.
  Empty paste operands are supported;
  a nonempty paste must form exactly one preprocessing token. Replacements are
  rescanned with recursive expansion suppression.
- Backslash-newline continuations and multiline invocations work. Comments
  separate tokens; strings and character literals retain their contents.
- Limits: 4,096 macro slots (including table-backed predefined macros),
  32 nested conditional groups, 16 include levels,
  64 expression/argument nesting levels, 262,144 tokens/expansion operations per
  chunk, 1 MiB per source/header and 8 MiB expanded text.
- Include directives accept macro-expanded header names.
  `#line` remaps source locations and the predefined file and line macros.
  Variadic macros and general pragmas are unsupported.
- The parser limits recursive expression and declarator processing to 256
  active steps. Nested expressions can use multiple steps per source level.

### Binary assets with `#embed`

For example, include a binary asset as a ROM byte array:

```c
const unsigned char tiles[] = {
#embed "tiles.bin"
};
```

- Resource names can be macro-generated. Quoted resource names search relative to the containing source/header, then
  `-I`; angle names search `-I`. Absolute paths are accepted.
- Files contribute 8-bit binary values, without character conversion or an
  implicit terminator. Use them in supported numeric global initializers.
- `limit`, `prefix`, `suffix`, `if_empty` and their `__name__` spellings work.
  Delimiters must balance and duplicate parameters are rejected.
- `limit` uses nonnegative 64-bit preprocessing arithmetic and forbids `defined`.
  `limit(0)` selects the empty case. Prefix/suffix apply only to nonempty data;
  `if_empty` replaces an empty result. Missing files remain errors with `if_empty`.
- `__has_embed` works in conditionals and feature checks, returning NOT_FOUND=0,
  FOUND=1 or EMPTY=2. Unsupported vendor parameters return NOT_FOUND in probes
  and produce errors in actual directives.

## Debugging and current limits

- The `--c89-keywords` compiler option permits `inline` as a name and retains the extension
  spellings `__inline` and `__inline__`.
- `__const`, `__volatile` and `__signed` are alternate keyword spellings. Their
  forms with trailing double underscores are also accepted.

- The compiler implements a C subset, not a complete conforming C implementation.
- Unsupported features include aggregate casts and conditional values.
  Additional initializer and preprocessor limits appear above.
- Builds retain emitted assembly, maps and debugger labels. Debug source mapping
  uses generated assembly; original-C source stepping is not implemented.
- For library pointer requirements and allocation rules, see the
  [supported C library](libc.md). For assembly integration and compiler
  behavior, see [the internal reference](technical/operations.md).
