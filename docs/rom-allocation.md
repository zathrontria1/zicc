# Building and sizing your ROM

The ROM builder turns your C files and assets into one image that the SNES can
run. It adds the library code you use, picks addresses and grows the ROM when
your game needs more space. The default image uses the FastROM HiROM layout.

## Build a ROM

After building the tools with `make`, run from the repository root:

```text
python tools/build-rom.py application.c other.c -o build/application.raw
bin/romtool.exe build/application.raw build/application.sfc tests/title.txt
```

- Replace `application.c other.c` with your C files. Give each file a different
  name before the `.c` extension. The builder compiles them separately by default.
- The first command creates the raw image. The second adds the title and
  checksum. Open the resulting `.sfc` file in your emulator.
- Replace `tests/title.txt` with a file containing your 0–21 character title.
- The standard Minimal and Prompt Make targets use this
  same automatic allocation path.

| Option | Use |
| --- | --- |
| `-o path` | Required raw-image output path |
| `--console` | Include the text console explicitly |
| `--input path` | Supply the fixed `fgets` input fixture and enable floating console formatting; combine with `--console` for console output |
| `--stack-size bytes` | Reserve 256 through 7,936 bytes of hardware stack (default 1,024) |
| `--max-rom bytes` | Limit HiROM size to a power of two from 65,536 through 4,194,304 bytes |
| `--mapping exhirom --rom-size KIB` | Build a fixed-size ExHiROM image of 6144 or 8192 KiB |
| `--stage N` | Force a call/placement stage for diagnosis; normally leave automatic |
| `--keep-intermediates` | Keep candidate assembly and object files for detailed build diagnosis or relinking |

For example, cap the image at 256 KiB:

```text
python tools/build-rom.py application.c --max-rom 262144 -o build/application.raw
```

### Build an ExHiROM

```text
python tools/build-rom.py application.c --mapping exhirom --rom-size 6144 -o build/application.raw
bin/romtool.exe build/application.raw build/application.sfc tests/title.txt
```

The builder warns when the same inputs can fit in 4 MiB HiROM and still writes
the requested ExHiROM image. Use 8192 KiB for more room. The 8192 KiB file has
two 32 KiB padding ranges at offsets `$7E0000` and `$7F0000`, where the
console's WRAM makes those ROM bytes inaccessible. The upper halves of the
corresponding ROM banks are available through `$3E:8000` and `$3F:8000`.

### Add assembly code

Pass `--assembly path.s` to include a ca65 file alongside your C files.
Use `.segment "CODE"` for code, `.segment "RODATA"` for read-only data,
`.segment "EMBED"` for binary assets, and the documented RAM segments for storage. For functions
called from C, use `ZICC_LONG_CALLS` to choose the return instruction and stack
offsets. It is 1 in stage 4 (RTL) and 0 in other stages (RTS). Internal assembly
calls keep their original calling rules.

## RAM placement

Near globals share the space from the end of the hardware stack through
`$7EFFFF`, starting at `$7E0500` by default. File-scope `__loram` objects
allocate first and must fit entirely through `$7E1FFF`. Ordinary globals can
use the remaining space. Startup copies both ordinary and low-RAM initializers
before your code runs. See [stack size and low-RAM placement](operations.md#hardware-stack).

## How automatic placement works

- HiROM images start at 64 KiB and grow through 128, 256, 512, 1024, 2048 and 4096 KiB
  when a layout cannot fit within the selected limit.
- The bank visible to the console at `$00:FFA0` reserves space for the
  header, vectors and interrupt entry stubs. The builder normally places
  code first. ExHiROM can move code to make room for large contiguous assets.
- The builder first tries layouts that keep short calls. As code grows, it can
  separate application and runtime code, then distribute functions across banks
  using long calls.
- The policy favors short calls over the smallest image. A larger ROM can be
  selected even when a long-call layout could fit in a smaller one. More assets
  can also grow the ROM while code retains short calls.
- Functions and some runtime groups must fit together within one 64 KiB bank.
  Fragmentation can prevent a layout even when its total free bytes look sufficient.

The build reports the selected capacity and stage. Stage 1 keeps code in the
first bank, stage 2 moves it to the second, stage 3 separates application/runtime
banks, and stage 4 packs functions across banks with long calls. See the
[technical allocation reference](technical/rom-allocation.md#placement-and-growth)
for exact placement and call rules.

## Assets and RAM limits

- Use [`#embed`](operations.md#binary-assets-with-embed) in a const global byte
  array to include a binary asset in ROM. The allocator places const objects
  independently; ROM addresses use far pointers.
- Writable initialized objects consume both a ROM load image and RAM. Startup
  copies their initial contents before console initialization and `main()`.
- Automatic HiROM and ExHiROM builds can place a read-only object across
  adjacent CPU banks when there is a contiguous free ROM span. In ExHiROM,
  file bytes at the end of bank `$FF` and start of bank `$40` need separate
  objects because those banks are far apart in the CPU address space.
- A bigger ROM gives the program more space for code and read-only data.
  Writable initialized objects remain limited to 65,534 bytes. Functions
  and startup copy sources must fit in their own banks.
- The initialized writable-data image must fit contiguously within a bank and
  within available near RAM. See [storage rules](operations.md#machine-and-storage)
  for the RAM budget.

## Outputs and failed builds

For `build/application.raw`, the useful outputs are:

| Output | What it tells you |
| --- | --- |
| `build/application.allocation.json` | Mapper, selected stage and capacity, object addresses and file offsets, sizes, hashes, free extents and rejected layouts |
| `build/application.map` | Linker memory layout |
| `build/application.dbg`, `build/application.labels` | Generated-assembly debugging information and symbol addresses |
| `build/application-allocation/<timestamp>/` | One `build.log` transcript, linked assembly and retained layout attempts |
| `build/application.sfc` | Finalized ROM, after running `romtool` |

- The allocation manifest points to the current build's evidence directory.
  By default it keeps application assembly, assembly referenced by the
  linked debug file, layout records and build diagnostics. The builder discards
  temporary objects and unlinked runtime assembly when it exits. Builds made
  with `--keep-intermediates` retain those files as well.
- `build/<name>-allocation/` keeps only the latest and previous timestamped
  run directories automatically; copy or archive a directory externally if you
  want to keep older history.
- If packing fails, inspect the rejected-layout messages for the unit and bank
  constraint that prevented placement. Check the ROM cap and individual object
  sizes before raising the limit.
- Failed builds remove the previous raw image and success manifest. A previously
  finalized `.sfc` can remain on disk; only run it after both build commands succeed.
- Standard Make rules rerun allocation so changed binary resources are included.

Manual LoROM links and stage-specific runtime mixing have additional contracts.
See [allocation internals](technical/rom-allocation.md) for those rules, the
packing algorithm and verification evidence.
