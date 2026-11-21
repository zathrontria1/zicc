# zicc

zicc turns C programs into ROM files you can run on a Super NES or in an emulator.

zicc runs on Windows and Linux. It turns C into 65816 assembly, ca65 assembles that code,
and ld65 links it into a ROM. The included runtime starts your program and
provides a text console, interrupt support, math routines and a small C library.
Check which C features zicc supports before you port an existing program.
[Supported C features and limits](docs/operations.md#debugging-and-current-limits)

## Getting started

Install these tools on Windows.

- MSVC with C17 support, discoverable through `vswhere`.
- ca65/ld65 and the other cc65 tools (default: `C:/bin/cc65/bin`).
- A native Windows build of GNU Make on `PATH`. Check that `make --version` reports `Built for Windows32`.
- Python 3 and PowerShell. Verification also uses Pillow and Mesen.

In PowerShell, open the folder containing this README and run `make`.

```powershell
make
```

This builds `bin/zicc.exe`, `bin/romtool.exe`, `bin/libc.a`, and the target
headers in `bin/include/`. The compiler finds these headers beside its
executable. Use `-I` to select a different header directory. Intermediate
files and the tools used by the repository's ROM builder stay in `build/`.

Pass `samples` to build the sample ROMs.

```powershell
make samples
```

Open `build/minimal.sfc` for an idle loop or `build/prompt.sfc` for a text
prompt. See the [samples guide](samples/readme.md) for the other ROMs.

Use the `minimal` or `prompt` target to build an individual ROM. Pass
`"CC65_BIN=C:/path/to/cc65/bin"` if cc65 is installed elsewhere. Other
project guides use `make` for the same native Windows build of GNU Make.

### Linux

On Linux, install GNU Make, a C17 compiler (`cc`, or set `CC`), cc65 and
Python 3. Make uses the cc65 tools on `PATH`. Pass `CC65_BIN=/path/to/cc65/bin`
if they are elsewhere.

```sh
make
make samples
```

## Building your own ROM

[The samples](samples/readme.md) show the supported language and library features.
Use `samples/minimal.c` as a starting point for a program that initializes its own
video and hardware, or `samples/prompt.c` for the bundled text console.

After `make`, the ROM builder accepts one or more C source files. For example:

```text
python tools/build-rom.py samples/minimal.c -o build/my-game.raw
bin/romtool.exe build/my-game.raw build/my-game.sfc tests/title.txt
```

Replace `samples/minimal.c` with your own C files. Give each file a different
name before the `.c` extension, even if the files are in different folders. Add `--console` to the Python command to include
the text console. The second command adds the ROM title and checksum. Supply your
own title file containing 0-21 characters, or use `TITLE_FILE=path/to/title.txt`
with the sample Make targets.

A normal build starts with a 64 KiB FastROM HiROM image. If the program needs
more space, the builder doubles the ROM size, up to 4 MiB. It saves the linked
assembly and a map showing where it placed the code and data. It also saves
debugger labels and the details of each placement attempt. See
[ROM building and allocation](docs/rom-allocation.md) for details.

## Target essentials

- Integer sizes on the SNES can differ from those on your PC. `char` is
  unsigned and 8 bits wide. `short` and `int` are 16 bits, `long` is 32 bits,
  and `long long` is 64 bits. All floating types use IEEE binary32
  by default. Pass `--binary64` to zicc or the ROM builder, or
  `BINARY64=1` to Make, to select binary64 `double` and `long double`.
- The hardware stack defaults to 1,024 bytes at `$0100`–`$04FF`. Set
  `--stack-size BYTES` in the ROM builder or `STACK_SIZE=BYTES` in Make to
  reserve 256–7,936 bytes. Near globals start immediately above the stack.
  File-scope `__loram` globals allocate first and must fit entirely through
  `$7E1FFF`. See [stack size and low-RAM placement](docs/operations.md#hardware-stack).
- Ordinary pointers are 16-bit addresses into WRAM bank `$7E`. ROM objects and
  literals use 32-bit `__far` pointers. A pointer to `const` alone does not make
  it far.
- Hardware registers require explicit bank-zero far addresses. For example,
  `*(unsigned char * __far)0x004200UL = 0x80;` writes NMITIMEN.
- Startup clears WRAM and copies initialized writable globals before `main()`.
  Linking the console also initializes its display and enables NMI. Other
  applications enable NMI after initializing their handler state.
- Native `__interrupt(nmi)`, `__interrupt(irq)`, `__interrupt(brk)` and
  `__interrupt(cop)` handlers are supported. See the
  [interrupt contracts](docs/operations.md#native-interrupt-functions)
  before writing handlers.

Structures, unions, fixed multidimensional arrays, typedefs, switch statements,
recursion and binary asset inclusion through C23 `#embed` are supported.
The [calling rules](docs/operations.md#calls-frames-and-returns) cover aggregate
arguments and returns by value, including passing a returned aggregate directly
as an argument. The [function pointer rules](docs/operations.md#function-pointers)
cover callbacks and indirect calls. The
[language and target reference](docs/operations.md) describes the exact
rules, including memory layout, `volatile` MMIO and preprocessing.

## Library and console

The [C library reference](docs/libc.md) lists the APIs supported under
each header, including console I/O, allocation, strings, character tests and timing.
`<time.h>` provides an NMI-driven frame clock at 60 Hz NTSC or 50 Hz PAL;
[frame timing](docs/operations.md#frame-timing) explains interrupt ownership.

The optional console displays 64x28 characters in 512x224 Mode 5. Use
`printf` to write text. The console updates the screen during the pause between
frames (VBlank). Use `fflush` to wait for pending updates.
`fgets` currently replays the bundled input file on each call. The samples do not
yet provide interactive keyboard or controller input. See
[text I/O](docs/operations.md#floating-runtime-and-text-io) for formats
and floating-console support.

## Further reading

- [Sample programs](samples/readme.md)
- [Supported C features and target rules](docs/operations.md)
- [Supported C library](docs/libc.md)
- [Compiler optimizations, examples and conditions](docs/optimizations.md)
- [Compiler internals, verification and performance reports](docs/technical.md)
- [Third-party sources and notices](docs/third-party.md)

Compiler development commands, benchmark methodology, optimization history and
verification evidence are documented in the technical guide.
