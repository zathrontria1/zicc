# Automatic ROM allocation internals

For application build commands, options, sizing behavior and outputs, start with
[building and sizing your ROM](../rom-allocation.md). This document describes
placement, call conventions, resource lowering and verification.

`tools/build-rom.py` coordinates separate C translation units, ca65 measurement,
stage selection, placement and ld65. It introduces no LTO or cross-translation-unit
constant folding; the low-level `zicc` executable still emits assembly.

The public `build/libc.a` and existing LoROM object rules retain their short-call
ABI for manual links and regression fixtures. The staged driver builds its own
stage-specific runtime objects; mixing objects from different stages is unsupported.

## Placement and growth

Near storage begins at $7E:0500. LORAM_BSS and LORAM_DATA allocate before
ordinary BSS/DATA; final-link checks constrain them through
$7E:1FFF. Initialized low objects have a separate bank-contained ROM load image,
packed with the other data, and startup copies both DATA spans. The hardware
stack is $0100-$04FF; arithmetic workspace retains its ownership. Selected
persistent runtime buffers backfill bank $7F after member selection; see
[runtime RAM placement](runtime-ram-backfill.md) and
[the storage contract](operations.md#machine-and-storage).


Header, vectors and bank-zero-reachable entry stubs are reserved in file bank
0 for HiROM and file bank 64 for ExHiROM. The allocator associates each usable
extent with its CPU address and file offset. The linker emits the extents in
file order and fills gaps with `$FF`, including the two ExHiROM holes.

HiROM tries 64, 128, 256, 512, 1024, 2048 and 4096 KiB up to the chosen cap.
ExHiROM uses the requested size and probes a 4096 KiB HiROM layout for its
fit warning. Stages are attempted in order where their bank requirements allow.

| Stage | Code placement | Calls/returns |
|---|---|---|
| 1 | All code in `$C0` | Existing short calls; main remains a long entry |
| 2 | All code in `$C1` | Short calls within that bank |
| 3 | Application code in `$C1`; startup and runtime in `$C2` | Short application calls; long runtime calls/returns |
| 4 | Individual C functions packed across eligible banks | Ordinary calls/returns uniformly use JSL/RTL |

The default policy favors short calls over the smallest possible image. If
stage 2 fails, grow to 256 KiB and try stage 3 before uniform long-call packing,
even if a forced stage-4 build could fit at 128 KiB. Stages 3 and 4 enter the
normal escalation sequence once four physical banks are available; a three-bank stage-3 layout requires a four-bank image. Extra
assets can increase capacity while retaining stage 1. A forced `--stage N`
option exists for diagnostics and exercises that convention at every capacity.

Functions are indivisible allocation units. Assembly runtime code with shared
local branches remains grouped by source unit; NMI user/library/epilogue pieces
remain one ordered allocation. Internal jumps stay within those units. Stage 4
packs code largest first, preferring FastROM banks and then the smallest
fitting extent. Earlier stages preserve group order. ROM data is normally packed
largest first after code. If stage 4 ExHiROM cannot fit, the allocator can retry
with read-only objects over 64 KiB placed before code. Fragmentation can cause
growth even when total unoccupied bytes appear sufficient.

DATA load bytes form one contiguous bank-contained ROM image. Its run addresses
remain in `$7E:0500-$7E:FFFF` after the low prefix, and startup copies it before calling the console
hook and main. All ROM object addresses remain far. DBR stays `$7E`, D stays
zero. Read-only ROM objects can span multiple banks if both their CPU addresses
and file offsets are contiguous. The automatic builder enables this for C
objects up to 4 MiB, subject to the free space in a single contiguous extent.
Code, DMA initializer batches and individual writable ROM load images remain
bank-contained. Writable initialized objects remain limited to 65,534 bytes.

## Call conventions and fixed entries

The driver selects long entries before compiler branch relaxation. Public,
private optimized and assembly runtime call sites must agree with their return
convention. The compiler's `--long-return` increases incoming stack-argument
offsets by one and emits RTL for ordinary returns, including optimized scalar
store/general leaves. Literal-copy runtime fallbacks use the same stage-aware
call selector as ordinary calls. `--long-calls names` supplies
stage-3 runtime entries while application functions retain their short entry
convention. All long-return runtime C functions also use long calls internally.
Handwritten runtime variants adjust caller-owned argument offsets, leaving
local saves and the memcpy execution thunk unchanged.

Main remains a JSL/RTL entry in every stage, including startup in a different
bank. Interrupt entry stubs use JML to their actual handlers; handlers return
with RTI. HiROM code uses the full `$C0-$FF` mapping, including addresses below
`$8000` and functions spanning that offset. Fixed vector entry addresses stay
above `$8000` in bank zero. Finalization writes FastROM metadata at file offset
`$FFC0` for HiROM and `$40FFC0` for ExHiROM. The checksum sums the entire file
and counts the final 2 MiB of a 6 MiB image twice to account for mirroring.
Explicit LoROM images use `$7FC0` metadata.

## Binary resources

Supported directives, search rules and parameter behavior are documented under
[binary assets with `#embed`](../operations.md#binary-assets-with-embed).

- The driver supplies the repository include directory through `-I`; there is
  no separate embed search-path option.
- Outer global array dimensions can be inferred from nonempty numeric
  initializers, including embedded bytes.
- Const embedded objects become independent ROM placement units. Writable
  embedded objects use the contiguous DATA load image and startup copy.
- Resource paths and hashes are retained in allocation evidence. Standard raw-image
  Make rules rerun the driver to observe changed bytes without a generated
  initializer or manually maintained asset count.

## Evidence and verification

Every invocation writes a fresh timestamped `build/<name>-allocation/` evidence
directory. It retains stage-specific C/assembly output, measured object files,
rejected layouts and the selected linker configuration/raw image. Sibling
`.allocation.json`, `.map`, `.dbg` and `.labels` files describe the successful
build. The manifest records stage, capacity, unit ownership, alignment, address,
size, free extents, raw ROM hash, compiler hash, linker/assembler hashes and
embedded-resource hashes. The final `.sfc` checksum is reported by romtool.

Default raw-image rules rerun the driver so changes to resource bytes are
observed without maintaining a generated initializer or hand-written asset
count. Only the latest and previous timestamped evidence directories are kept;
copy or archive a directory externally for longer retention. Failed builds remove the previous
raw image and success manifest so stale placement cannot be mistaken for a
successful rebuild.

`tests/check-embed.py` covers expansion, probing, macro names, empty/missing
resources, arbitrary octets, parameter diagnostics and inferred arrays.
`tests/check-banked-rom.py` executes every stage in Mesen, including recursion,
stack arguments, wide operations, optimized struct reduction, DATA copying,
string/memory/heap/decimal runtime calls, cross-bank copies, user NMI composition,
NMI-driven console output, a console entry at bank offset zero, asset
fidelity, rebuilding changed assets, growth, and a function spanning `$8000`.
Both run inside the existing compiler verification suite, preserving the shared
verification queue and arithmetic batches. Run the full `make check` after
compiler/code-generation changes, with its hardware-thread worker default.
