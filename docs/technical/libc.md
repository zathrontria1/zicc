# C library internals

The [public library guide](../libc.md) lists supported APIs under each header,
including pointer requirements, return values and application restrictions.
This reference covers linking, assembly implementation and verification.

## Linking and ABI

- `make all` assembles members under `build/libc-new/` and builds
  `build/libc-new/libc.a`, also copied to `build/libc.a`. For manual links, put it after application
  objects; members are selected only when referenced.
- That archive supplies allocation, memory, the requested string and ASCII ctype
  routines, termination, and buffer formatting. Decimal parsing and timing use
  separate runtime components; buffer formatting imports the decimal runtime.
- The automatic ROM builder resolves required members and builds stage-specific
  variants. Do not mix their call conventions with the manual short-call archive;
  see [ROM allocation internals](rom-allocation.md).
- Manual links use `python tools/link-runtime-ram.py` with the usual ld65
  arguments to backfill only selected runtime state into bank $7F. It measures
  a probe link before generating exact RAM extents; see
  [runtime RAM placement](runtime-ram-backfill.md#manual-links).
- Archive entry points use A16/X16, D=$0000 and DBR=$7E, preserving Y. Word
  argument 0 uses X and argument 1 uses A; later and four-byte arguments use the
  stack. Returns use A, and X for the high word of four-byte values.

See [the internal ABI reference](operations.md#calls-frames-and-returns) for
frames, clobbers and return conventions.

## Allocation

- The heap starts after linked static allocation and extends through $7E:FFFF.
  Supplied linker configurations export `__NEAR_LAST__`; no fixed heap buffer is
  reserved.
- `malloc` uses first fit and two-byte block headers. It splits a block only if
  the remainder holds a header plus at least two payload bytes.
- `free` coalesces both free neighbors to recover larger contiguous allocations.
- Allocation state is shared and not interrupt-reentrant. Ordinary interrupts
  may preempt foreground allocation, but handlers must not reenter the allocator.

## String routines

- `strcpy` transfers exactly one byte per character, including the terminator,
  and locally saves/restores reserved DP scratch $E0–$E3.
- `strcmp` reads individual unsigned bytes until a difference or terminator,
  with locally preserved DP scratch $E0–$E7.
- Both accept far sources and carry across physical bank boundaries. Destinations
  remain near; source/destination contracts are in the [public guide](../libc.md#stringh).

## Memory routines

### `memcpy`

- A source span contained in one physical bank uses MVN.
- A private four-byte stack thunk (`MVN source,$7E; RTL`) supplies the immediate
  source bank. It is entered in bank $00 and returns to the library's program bank.
- The thunk stays above the active stack pointer, including during interrupts
  and nested library calls.
- Cross-bank spans use long-indirect byte reads with bank carry, locally
  preserving $E0–$E3.

### `memset`

- The first byte receives the low byte of `value`; overlapping MVN fills the rest.
- Counts zero and one bypass MVN to avoid count-minus-one underflow.
- The routine uses no DP scratch.

### `memmove`

- Overlap with a destination above a bank-$7E source uses MVP from the last byte.
- Other copies use `memcpy`.
- Low-WRAM source aliases in banks $00–$3F/$80–$BF are recognized. Backward
  overlapping alias copies use long-indirect byte reads, locally preserving
  $E0–$E3 and the source's mapping at the $2000 boundary.

All three routines preserve Y/D/DBR and DP scratch and restore A16/X16. Valid
disjoint ranges may be used from an assembly interrupt handler that preserves
the interrupted CPU state. Source-level C handlers still obey the compiler's
[interrupt restrictions](../operations.md#native-interrupt-functions).

## Other header implementations

- `runtime/ctype.s` supplies all fourteen ASCII classification/conversion entries.
- `runtime/strings.s` adds the remaining string entries. Each invocation saves
  Y and DP $E0-$EF on the stack; far cursors carry across physical banks. The
  assembly's `LIBC_RETURN_EXTRA` parameter handles both short and long returns.
- `runtime/terminate.s` restores `__STACK_TOP__` and jumps long to `main_exit`.
- `runtime/io.s` supplies `fgets`, `stdin` and `errno`.
  The demand-linked binary64 decimal parser supplies `strtod`. The input
  fixture is embedded as binary bytes followed by a zero terminator.
  `runtime/io-compat.s` assembles this body together with ctype into the plain
  compatibility object `build/io.o`, preserving older manual links and decimal
  reference tests. Put the public library archive after these runtime objects.
- `runtime/console.s` supplies `printf`, `fflush` and `stdout`. Integer formatter
  state lives on the invocation stack; floating decimal buffers remain shared.
  See [console implementation](operations.md#floating-runtime-and-text-io).
- `runtime/sprintf.s` assembles the same formatter with `STRING_FORMAT` enabled.
  This removes display/stream code and replaces the output sink with a bounded
  near-RAM writer. Its 72-byte stack frame adds destination, remaining capacity
  and count-overflow homes; it preserves Y, DP scratch and the private far cursor.
  The count saturates at `INT_MAX` with an independent overflow flag. All output,
  including discarded bytes after truncation, participates in the count.
- `runtime/ieee32/` supplies floating arithmetic and decimal/hexadecimal parsing
  and formatting. Assembly entries are used by normal builds; C implementations
  remain references.
- `runtime/clock.s` supplies the frame counter and snapshot read;
  `runtime/clock_rate.s` supplies cached region detection. Separate archive members
  avoid linking a counter/NMI wrapper for a rate-only query. See
  [frame timing internals](operations.md#frame-timing).

## Verification

`python tests/check-libc.py` runs target ROM checks on NTSC and PAL, including
independent assembly probes for Y/D/DBR, stack, register widths and DP scratch
preservation. Memory cases cover ROM/RAM, zero/one/odd lengths, bank crossings,
overlap in both directions, low WRAM aliases, 50000-byte counts and destinations
ending at $7E:FFFF. A real NMI makes nested memory calls during an MVN copy.

The compiler suite includes these checks in `make check`. No host allocator,
string or memory library substitutes for the target implementations. I/O,
interrupt and clock verification is described in the corresponding sections of
[the internal operations reference](operations.md).

`python tests/check-libc-new.py` checks the added public surface on NTSC/PAL,
all ctype byte values plus EOF, string and formatter bank crossings, 50000-byte
counts, zero capacities, truncation and overflow, constant types/bit images,
Boolean conversions and termination. An independent assembly caller checks
Y/D/DBR, stack, M/X/decimal flags and all reserved DP words. Combined string and
buffer-formatting ROMs also execute every staged call ABI. The registered
`libc-new` compiler part retains sources, assembly, ROMs, logs and hashes under
`build/libc-new/check/`.
