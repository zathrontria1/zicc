# MSVC builds the compiler on Windows. Use a native Windows build of GNU Make there
# On Linux the host C compiler (CC, default cc) builds it instead
BINARY64 ?= 0
STACK_SIZE ?= 1024
BINARY64_FLAGS := $(if $(filter 1,$(BINARY64)),--binary64)
BINARY64_ASM := $(if $(filter 1,$(BINARY64)),-D ZICC_BINARY64=1)
.DEFAULT_GOAL := all

ifeq ($(OS),Windows_NT)
PYTHON ?= python
CC65_BIN ?= C:/bin/cc65/bin
EXE := .exe
SHELL := cmd.exe
.SHELLFLAGS := /d /c
ZICC := build\zicc.exe
ROMTOOL := build\romtool.exe
else
PYTHON ?= python3
# Default to the cc65 tools found on PATH
CC65_BIN ?= $(or $(patsubst %/,%,$(dir $(shell which ca65 2>/dev/null))),/usr/bin)
EXE :=
ZICC := build/zicc
ROMTOOL := build/romtool
CFLAGS ?= -std=c17 -O2
endif

export ZICC_MAKE := $(MAKE_COMMAND)
export PYTHON

# Use at least four workers and leave two hardware threads free when possible
# Nested builds inherit the worker count. Use -j to set it yourself
ifeq ($(filter -j% --jobs%,$(MAKEFLAGS)),)
MAKEFLAGS += -j$(shell $(PYTHON) -c "import os; print(max(4, (os.cpu_count() or 1) - 2))")
endif

export CC65_BIN
NATIVE_ROOT := $(shell $(PYTHON) -c "from pathlib import Path; print(Path.cwd().as_posix())")
CA65 := $(CC65_BIN)/ca65$(EXE)
LD65 := $(CC65_BIN)/ld65$(EXE)
AR65 := $(CC65_BIN)/ar65$(EXE)
TITLE_FILE ?= tests/title.txt

STANDALONE_SAMPLES := insertion_sort string_processing integer_operations function_calls structures_and_tables loop_access
STANDALONE_ROMS := $(addprefix build/,$(addsuffix .sfc,$(STANDALONE_SAMPLES)))
SPLIT_ROMS := build/integer_operations_runtime.sfc build/structures_and_tables_runtime.sfc
BIN_HEADERS := $(patsubst include/%,bin/include/%,$(wildcard include/*.h))

.PHONY: all samples smoke check minimal prompt FORCE
all: bin/zicc$(EXE) bin/romtool$(EXE) bin/libc.a $(BIN_HEADERS)

samples: minimal prompt $(STANDALONE_ROMS) $(SPLIT_ROMS) build/empty-template.sfc

bin bin/include:
	$(PYTHON) -c "from pathlib import Path; Path('$@').mkdir(parents=True, exist_ok=True)"

bin/zicc$(EXE) bin/romtool$(EXE) bin/libc.a: bin/%: build/% | bin
	$(PYTHON) -c "from shutil import copy; copy('$<', '$@')"

$(BIN_HEADERS): bin/include/%: include/% | bin/include
	$(PYTHON) -c "from shutil import copyfile; copyfile('$<', '$@')"

build:
	$(PYTHON) -c "from pathlib import Path; Path('$@').mkdir(exist_ok=True)"

ZICC_SOURCES := $(wildcard src/*.c src/*.inc src/codegen/*.inc src/headers/*.h)

ifeq ($(OS),Windows_NT)
build/romtool$(EXE): tools/romtool.c tools/build-romtool.cmd | build
	tools\build-romtool.cmd

build/zicc$(EXE): $(ZICC_SOURCES) tools/build-compiler.cmd tools/msvc.cmd | build
	tools\build-compiler.cmd
else
build/romtool: tools/romtool.c | build
	$(CC) $(CFLAGS) -o "$@" tools/romtool.c

build/zicc: $(ZICC_SOURCES) | build
	$(CC) $(CFLAGS) -o "$@" src/main.c src/preprocess.c src/relax.c
endif

build/minimal.s: samples/minimal.c build/zicc$(EXE)
	$(ZICC) "$<" -o "$@" $(BINARY64_FLAGS)

build/minimal.o: build/minimal.s
	"$(CA65)" --cpu 65816 -g -o "$@" "$(NATIVE_ROOT)/$<"

build/startup.o: runtime/startup.s runtime/startup-dma.inc | build
	"$(CA65)" --cpu 65816 -I "$(NATIVE_ROOT)" -g -o "$@" "$(NATIVE_ROOT)/$<"

build/interrupt-nmi.o: runtime/nmi.s | build
	"$(CA65)" --cpu 65816 -g -o "$@" "$(NATIVE_ROOT)/$<"

build/interrupt-clock.o: runtime/clock.s | build
	"$(CA65)" --cpu 65816 -g -o "$@" "$(NATIVE_ROOT)/$<"

build/interrupt-rate.o: runtime/clock_rate.s | build
	"$(CA65)" --cpu 65816 -g -o "$@" "$(NATIVE_ROOT)/$<"

build/interrupt-bank.o: runtime/nmi-bank.s | build
	"$(CA65)" --cpu 65816 -g -o "$@" "$(NATIVE_ROOT)/$<"

# ld65 reads nmi.o as an archive even though existing builds use the .o name
build/nmi.o: build/interrupt-nmi.o build/interrupt-clock.o build/interrupt-rate.o build/interrupt-bank.o
	$(PYTHON) -c "from pathlib import Path; Path('$@').unlink(missing_ok=True)"
	"$(AR65)" a "$@" build/interrupt-clock.o build/interrupt-rate.o build/interrupt-bank.o build/interrupt-nmi.o

build/minimal.raw: build/startup.o build/minimal.o build/nmi.o build/vectors.o build/rom_header.o linker/lorom32.cfg tools/build-rom.py FORCE
	$(PYTHON) tools/build-rom.py --stack-size "$(STACK_SIZE)" $(BINARY64_FLAGS) samples/minimal.c -o "$@"

build/minimal.sfc: build/minimal.raw build/romtool$(EXE) $(TITLE_FILE) FORCE
	$(ROMTOOL) "$<" "$@" "$(TITLE_FILE)"

build/minimal.sym: build/minimal.raw tools/debug_symbols.py
	$(PYTHON) tools/debug_symbols.py build/minimal.labels "$@"

minimal: build/minimal.sfc build/minimal.sym

build/prompt.s: samples/prompt.c include/stdio.h build/zicc$(EXE)
	$(ZICC) "$<" -o "$@" $(BINARY64_FLAGS) -I include

build/prompt.o: build/prompt.s
	"$(CA65)" --cpu 65816 -g -o "$@" "$(NATIVE_ROOT)/$<"

build/prompt_startup.o: runtime/startup.s runtime/startup-dma.inc | build
	"$(CA65)" --cpu 65816 -I "$(NATIVE_ROOT)" -D CONSOLE=1 -g -o "$@" "$(NATIVE_ROOT)/$<"

assets/console/ascii8x8.1bpp: assets/console/ascii8x8.2bpp tools/build-console-font.py
	$(PYTHON) tools/build-console-font.py

build/console.o: runtime/console.s assets/console/ascii8x8.1bpp assets/console/palette.bgr555 build/float-abi | build
	"$(CA65)" --cpu 65816 $(BINARY64_ASM) -I "$(NATIVE_ROOT)" -g -o "$@" "$(NATIVE_ROOT)/$<"

build/prompt.raw: build/prompt_startup.o build/prompt.o build/console.o build/nmi.o build/vectors.o build/rom_header.o linker/lorom32.cfg tools/build-rom.py FORCE
	$(PYTHON) tools/build-rom.py --stack-size "$(STACK_SIZE)" $(BINARY64_FLAGS) samples/prompt.c --console -o "$@"

build/prompt.sfc: build/prompt.raw build/romtool$(EXE) $(TITLE_FILE) FORCE
	$(ROMTOOL) "$<" "$@" "$(TITLE_FILE)"

build/prompt.sym: build/prompt.raw tools/debug_symbols.py
	$(PYTHON) tools/debug_symbols.py build/prompt.labels "$@"

prompt: build/prompt.sfc build/prompt.sym

$(STANDALONE_ROMS:.sfc=.raw): build/%.raw: samples/%.c build/zicc$(EXE) tools/build-rom.py FORCE
	$(PYTHON) tools/build-rom.py --stack-size "$(STACK_SIZE)" $(BINARY64_FLAGS) "$<" -o "$@"

build/integer_operations_runtime.raw: samples/integer_operations_runtime.c samples/integer_kernels.c build/zicc$(EXE) tools/build-rom.py FORCE
	$(PYTHON) tools/build-rom.py --stack-size "$(STACK_SIZE)" $(BINARY64_FLAGS) $(filter %.c,$^) -o "$@"

build/structures_and_tables_runtime.raw: samples/structures_and_tables_runtime.c samples/inventory_kernels.c samples/inventory_runtime.h build/zicc$(EXE) tools/build-rom.py FORCE
	$(PYTHON) tools/build-rom.py --stack-size "$(STACK_SIZE)" $(BINARY64_FLAGS) $(filter %.c,$^) -o "$@"

build/empty-template.raw: samples/empty-template/main.c samples/empty-template/snes_regs.h build/zicc$(EXE) tools/build-rom.py FORCE
	$(PYTHON) tools/build-rom.py --stack-size "$(STACK_SIZE)" $(BINARY64_FLAGS) "$<" -o "$@"

build/empty-template.sfc: build/empty-template.raw build/romtool$(EXE) samples/empty-template/rom-title.txt
	$(ROMTOOL) "$<" "$@" samples/empty-template/rom-title.txt

$(STANDALONE_ROMS) $(SPLIT_ROMS): build/%.sfc: build/%.raw build/romtool$(EXE) $(TITLE_FILE)
	$(ROMTOOL) "$<" "$@" "$(TITLE_FILE)"

build/link_smoke.o: tests/link_smoke.s | build
	"$(CA65)" --cpu 65816 -g -o "$@" "$(NATIVE_ROOT)/$<"

build/rom_header.o: runtime/rom_header.s | build
	"$(CA65)" --cpu 65816 -g -o "$@" "$(NATIVE_ROOT)/$<"

build/vectors.o: runtime/vectors.s | build
	"$(CA65)" --cpu 65816 -g -o "$@" "$(NATIVE_ROOT)/$<"

build/link_smoke.raw: build/link_smoke.o build/rom_header.o build/vectors.o linker/lorom32.cfg tools/link-runtime-ram.py tools/runtime_ram.py FORCE
	$(PYTHON) tools/link-runtime-ram.py -C linker/lorom32.cfg -D "__STACK_SIZE__=$(STACK_SIZE)" -m build/link_smoke.map --dbgfile build/link_smoke.dbg -Ln build/link_smoke.labels -o "$@" build/link_smoke.o build/rom_header.o build/vectors.o

# Write the title again each time so a new TITLE_FILE takes effect
build/link_smoke.sfc: build/link_smoke.raw build/romtool$(EXE) $(TITLE_FILE) FORCE
	$(ROMTOOL) build/link_smoke.raw "$@" "$(TITLE_FILE)"

smoke: build/link_smoke.sfc

# Set up MSVC once for the build and all test workers
# CHECK_JOBS sets the number of test workers. Use make -j for build jobs
CHECK_JOBS ?= $(shell $(PYTHON) -c "import os; print(max(4, (os.cpu_count() or 1) - 2))")
CHECK_OUTPUT ?=
# Set CHECK_NO_CACHE=1 to run the emulator again even when its inputs match
# Set CHECK_CHANGED=1 to run only suites whose inputs changed since their last pass
CHECK_NO_CACHE ?=
CHECK_CHANGED ?=
.PHONY: check-prerequisites check-suites check-changed
ifeq ($(OS),Windows_NT)
check:
	+tools\check.cmd
else
check:
	@echo "make check needs Windows (MSVC, PowerShell and Mesen)" >&2; exit 1
endif
check-changed:
	+$(MAKE) --no-print-directory check CHECK_CHANGED=1

check-prerequisites: smoke minimal prompt build/float_console.o build/libc.a \
	build/arithmetic.o build/integers.o build/ieee_engine.o build/io.o build/tables.o build/decimal.o build/malloc.o build/free.o

check-suites: $(if $(CHECK_PREREQUISITES_DONE),,check-prerequisites)
	$(PYTHON) tools/run-checks.py --jobs $(CHECK_JOBS) $(if $(CHECK_OUTPUT),--output "$(CHECK_OUTPUT)") $(if $(CHECK_NO_CACHE),--no-cache) $(if $(CHECK_CHANGED),--changed)

FORCE:

build/decimal-body.o: runtime/ieee32/decimal-state.s | build
	"$(CA65)" --cpu 65816 -g -o "$@" "$(NATIVE_ROOT)/$<"

DECIMAL_ASM := match render rounded hexval dec-copy exponent dec-format dec-format-raw ieee-decimal ieee-decimal-compare hexparse ieee-parse dec-format-spec
DECIMAL_ASM_OBJS := $(addprefix build/decimal-,$(addsuffix .o,$(DECIMAL_ASM)))

build/decimal-%.o: runtime/ieee32/%.s | build
	"$(CA65)" --cpu 65816 -g -o "$@" "$(NATIVE_ROOT)/$<"

# Keep the filename used by existing builds. ld65 detects the archive by its contents
build/decimal.o: build/decimal-body.o $(DECIMAL_ASM_OBJS)
	$(PYTHON) -c "from pathlib import Path; Path('$@').unlink(missing_ok=True)"
	"$(AR65)" a "$@" $^

build/input.bin: samples/input.txt
	$(PYTHON) -c "from pathlib import Path; Path('$@').write_bytes(Path('$<').read_bytes().replace(bytes([13,10]),bytes([10])))"

build/libc-new/io-compat.o: runtime/io-compat.s runtime/io.s runtime/errno.s $(wildcard runtime/ctype/*.s) build/input.bin | build/libc-new
	"$(CA65)" --cpu 65816 -I "$(NATIVE_ROOT)" -I "$(NATIVE_ROOT)/runtime" -g -o "$@" "$(NATIVE_ROOT)/$<"

# Manual builds expect io.o to supply the original ctype functions
# Some link io.o before the decimal objects, so it must be a plain object file
build/io.o: build/libc-new/io-compat.o
	$(PYTHON) -c "from pathlib import Path; Path('$@').write_bytes(Path('$<').read_bytes())"

build/dp-scratch.o: runtime/dp-scratch.s | build
	"$(CA65)" --cpu 65816 -g -o "$@" "$(NATIVE_ROOT)/$<"

IEEE32_WRAP_OBJS := $(addprefix build/ieee32-,fadd32.o fsub32.o fmul32.o fdiv32.o fcmp32.o)
IEEE32_ENGINE_OBJS := $(addprefix build/ieee32-,unpack.o pack.o right-a.o normalize.o addsub.o mul.o div.o cmp.o test.o marker.o)
INTEGER_ASM_OBJS := $(patsubst runtime/integers/%.s,build/integers-%.o,$(sort $(wildcard runtime/integers/*.s)))

build/ieee32-%.o: runtime/ieee32/%.s | build
	"$(CA65)" --cpu 65816 -I "$(NATIVE_ROOT)" -g -o "$@" "$(NATIVE_ROOT)/$<"

build/ieee32-mul.o: runtime/ieee32/product.inc

build/integers-%.o: runtime/integers/%.s | build
	"$(CA65)" --cpu 65816 -g -o "$@" "$(NATIVE_ROOT)/$<"

# Keep the filenames used by existing builds. ld65 links only the members in use
build/arithmetic.o: build/dp-scratch.o $(IEEE32_WRAP_OBJS)
	$(PYTHON) -c "from pathlib import Path; Path('$@').unlink(missing_ok=True)"
	"$(AR65)" a "$@" $^

build/integers.o: $(INTEGER_ASM_OBJS)
	$(PYTHON) -c "from pathlib import Path; Path('$@').unlink(missing_ok=True)"
	"$(AR65)" a "$@" $^

build/ieee_engine.o: $(IEEE32_ENGINE_OBJS)
	$(PYTHON) -c "from pathlib import Path; Path('$@').unlink(missing_ok=True)"
	"$(AR65)" a "$@" $^

build/tables.o: runtime/ieee32/tables.s | build
	"$(CA65)" --cpu 65816 -g -o "$@" "$(NATIVE_ROOT)/$<"

build/float_console.o: runtime/console.s assets/console/ascii8x8.1bpp assets/console/palette.bgr555 build/float-abi
	"$(CA65)" --cpu 65816 $(BINARY64_ASM) -D CALC=1 -I "$(NATIVE_ROOT)" -g -o "$@" "$(NATIVE_ROOT)/$<"

# ld65 pulls in only the C library members the program uses
build/malloc.o: runtime/malloc.s | build
	"$(CA65)" --cpu 65816 -g -o "$@" "$(NATIVE_ROOT)/$<"

build/free.o: runtime/free.s | build
	"$(CA65)" --cpu 65816 -g -o "$@" "$(NATIVE_ROOT)/$<"

build/strcpy.o: runtime/strcpy.s | build
	"$(CA65)" --cpu 65816 -g -o "$@" "$(NATIVE_ROOT)/$<"

build/strcmp.o: runtime/strcmp.s | build
	"$(CA65)" --cpu 65816 -g -o "$@" "$(NATIVE_ROOT)/$<"

build/memcpy.o build/memset.o build/memmove.o: build/%.o: runtime/%.s | build
	"$(CA65)" --cpu 65816 -g -o "$@" "$(NATIVE_ROOT)/$<"

LIBC_NEW_NAMES := malloc free strcpy strcmp memcpy memcpy-near memset memmove terminate sprintf fabsf ldexpf $(if $(filter 1,$(BINARY64)),fabs ldexp) qsort bsearch assert strtoint strto64 abs labs calloc realloc errno sram
LIBC_NEW_OBJS := $(addprefix build/libc-new/,$(addsuffix .o,$(LIBC_NEW_NAMES)))
LIBC_NEW_OBJS += $(addprefix build/libc-new/,$(addsuffix .o,far-memory far-heap))
LIBC_NEW_OBJS += $(patsubst runtime/strings/%.s,build/libc-new/strings-%.o,$(sort $(wildcard runtime/strings/*.s)))
LIBC_NEW_OBJS += $(patsubst runtime/ctype/%.s,build/libc-new/ctype-%.o,$(sort $(wildcard runtime/ctype/*.s)))
LIBC_NEW_OBJS += $(patsubst runtime/bitops/%.s,build/libc-new/bitops-%.o,$(sort $(wildcard runtime/bitops/*.s)))
LIBC_NEW_OBJS += $(patsubst runtime/conversions/%.s,build/libc-new/conversions-%.o,$(sort $(wildcard runtime/conversions/*.s)))
LIBC_NEW_OBJS += $(patsubst runtime/math/%.s,build/libc-new/math-%.o,$(sort $(wildcard runtime/math/*.s)))
LIBC_NEW_OBJS += $(addprefix build/libc-new/int64-,$(addsuffix .o,shift mul div cmp format mul32))
LIBC_NEW_OBJS += $(addprefix build/libc-new/ieee64-,$(addsuffix .o,environment-state environment cmp neg extend truncate fromint32 toint32 fromint64 fromint64-to-float toint64 addsub mul div $(if $(filter 1,$(BINARY64)),sqrt log exp atan trig) decimal decimal-compare decimal-estimate decimal-refine decimal-parse hexparse rounded format))
LIBC_NEW_OBJS += build/decimal-render.o build/decimal-exponent.o build/decimal-match.o
LIBC_NEW_OBJS += $(addprefix build/decimal-,$(addsuffix .o,$(filter-out render exponent match,$(DECIMAL_ASM))))
LIBC_NEW_OBJS += build/decimal-body.o build/tables.o
LIBC_NEW_OBJS += $(IEEE32_WRAP_OBJS) $(IEEE32_ENGINE_OBJS) $(INTEGER_ASM_OBJS)

build/libc-new:
	$(PYTHON) -c "from pathlib import Path; Path('$@').mkdir(parents=True, exist_ok=True)"

build/libc-new/%.o: runtime/%.s | build/libc-new
	"$(CA65)" --cpu 65816 -g -I "$(NATIVE_ROOT)/runtime" -o "$@" "$(NATIVE_ROOT)/$<"

build/libc-new/far-memory.o: build/libc-new/%.o: runtime/%.c build/zicc$(EXE) include/string.h | build/libc-new
	$(ZICC) "$<" -o "$(@:.o=.s)" -I include
	"$(CA65)" --cpu 65816 -g -o "$@" "$(NATIVE_ROOT)/$(@:.o=.s)"

build/libc-new/strings-%.o: runtime/strings/%.s runtime/strings/common.inc | build/libc-new
	"$(CA65)" --cpu 65816 -g -I "$(NATIVE_ROOT)/runtime/strings" -o "$@" "$(NATIVE_ROOT)/$<"

build/libc-new/ctype-%.o: runtime/ctype/%.s | build/libc-new
	"$(CA65)" --cpu 65816 -g -o "$@" "$(NATIVE_ROOT)/$<"

build/libc-new/bitops-%.o: runtime/bitops/%.s | build/libc-new
	"$(CA65)" --cpu 65816 -g -o "$@" "$(NATIVE_ROOT)/$<"

build/libc-new/conversions-%.o: runtime/conversions/%.s | build/libc-new
	"$(CA65)" --cpu 65816 -g -o "$@" "$(NATIVE_ROOT)/$<"

build/libc-new/math-%.o: runtime/math/%.s runtime/math/common.inc build/float-abi | build/libc-new
	"$(CA65)" --cpu 65816 -g $(BINARY64_ASM) -I "$(NATIVE_ROOT)" -I "$(NATIVE_ROOT)/runtime/math" -o "$@" "$(NATIVE_ROOT)/$<"

build/libc-new/math-trigf.o: runtime/math-two-over-pi.inc

build/libc-new/int64-%.o: runtime/int64/%.s | build/libc-new
	"$(CA65)" --cpu 65816 -g -o "$@" "$(NATIVE_ROOT)/$<"

build/libc-new/ieee64-%.o: runtime/ieee64/%.s | build/libc-new
	"$(CA65)" --cpu 65816 -g -I "$(NATIVE_ROOT)/runtime/ieee64" -o "$@" "$(NATIVE_ROOT)/$<"

build/float-abi: FORCE | build
	$(PYTHON) -c "from pathlib import Path; p=Path('$@'); s='$(BINARY64)'; p.write_text(s) if not p.exists() or p.read_text()!=s else None"

build/minimal.s build/prompt.s: build/float-abi

build/libc-new/sprintf.o: runtime/sprintf.s runtime/console.s build/float-abi | build/libc-new
	"$(CA65)" --cpu 65816 -g $(BINARY64_ASM) -I "$(NATIVE_ROOT)/runtime" -o "$@" "$(NATIVE_ROOT)/runtime/sprintf.s"
build/libc-new/fabs.o build/libc-new/fabsf.o: build/libc-new/%.o: runtime/%.s build/float-abi | build/libc-new
	"$(CA65)" --cpu 65816 -g $(BINARY64_ASM) -o "$@" "$(NATIVE_ROOT)/$<"
build/libc-new/ldexp.o build/libc-new/ldexpf.o: build/libc-new/%.o: runtime/%.s runtime/ldexp-common.inc build/float-abi | build/libc-new
	"$(CA65)" --cpu 65816 -g $(BINARY64_ASM) -I "$(NATIVE_ROOT)/runtime" -o "$@" "$(NATIVE_ROOT)/$<"
build/libc-new/ieee64-trig.o: runtime/ieee64/trig-two-over-pi.inc
build/libc-new/qsort.o build/libc-new/bsearch.o: runtime/callback.inc

build/libc-new/libc.a: $(LIBC_NEW_OBJS)
	$(PYTHON) -c "from pathlib import Path; Path('$@').unlink(missing_ok=True)"
	"$(AR65)" a "$@" $^

# Keep this assembly path for new and existing manual builds
build/libc.a: build/libc-new/libc.a
	$(PYTHON) -c "from pathlib import Path; Path('$@').write_bytes(Path('$<').read_bytes())"
