# Repository Guidelines

## Project Structure

- `src/` contains zicc, including preprocessing, parsing, and 65816 code generation in `src/codegen/`. See `docs/technical/architecture.md` for the pass pipeline and shared state map.
- `runtime/` contains target startup and library code, `include/` exposes target C headers, and `linker/` holds ld65 memory layouts.
- `samples/` contains example ROM sources and benchmarks. `assets/` holds console resources, `tests/` holds verification scripts and fixtures, and `tools/` contains build and analysis utilities. Find target and ABI details in `docs/operations.md`.

## Build and Development

Run native Windows GNU Make from the repository root with MSVC (C17), cc65, and Python 3. Override `CC65_BIN` if needed. Verification also uses PowerShell, Pillow, and Mesen.

- `make` builds the compiler, ROM utility, runtime library and target headers in `bin/`. Use `make samples` for the optional sample ROMs in `build/`.
- `make check-prerequisites BINARY64=1` builds the fixtures for focused verification. `make smoke` builds only the dedicated link-smoke ROM and its dependencies.

## Coding Style

Write new and edited code in a readable, uncrowded style instead of copying legacy dense one-liners:

- Use one statement per line, consistent four-space indentation in C and Python, tabs for Make recipes, and empty lines between logical blocks to avoid walls of text.
- Keep variable and function names clear (`snake_case` in C and Python). Name Python verification scripts `check-<feature>.py`.
- Add short, plain ELI5 comments where the code is not obvious (either `//` above a block or a brief `//` to the right of a variable or short assignment). Avoid parroting what the code already says, and never end a single-line comment with a period `.`.
- Splitting a large file (such as `codegen.inc` or `line_passes.inc`) into focused files that own their own state instead of sharing global `cg` is an allowed and encouraged improvement when working in that area.
- Keep changes purposeful and preserve existing target ABI behavior unless the change explicitly addresses it.

For compiler-provided libraries, helpers, and functions (e.g. internal multiplication/division helpers, libc functions) implement in 65816 assembly instead of self-compiled C.

## Testing

- Use the smallest check that covers the change. After fixing a miscompile, keep unaffected results and rerun checks for the failure and affected dependencies.
- Individual compiler passes may have their own small, focused unit or pass-level tests (in C or Python) to test one pass's input/output or invariant directly, alongside the end-to-end ROM verification suites.
- Select a suite with `python tools/run-checks.py --suite members`. List compiler parts with `python tests/check-compiler.py --list-parts` and run one with `--part NAME`. Preserve coverage and register new checks as suites or compiler parts.
- Run `make check` only when requested or just before committing compiler changes. Keep emulator caching enabled unless investigating the cache or its inputs.
- Run one verification invocation per checkout. Leave sources and binaries untouched while it runs. The default is `max(4, hardware threads - 2)` workers. Override it with `CHECK_JOBS` in Make or `--jobs` in the runner. See [the verification workflow](docs/technical.md) and logs under `logs/check/`.

## Temporary Test Builds

- Delete temporary test build folders under `build/` (do not archive them) once they have served their purpose (after the tested changes are accepted and committed, or rejected).
- Before reporting cleanup complete, check `build/` for temporary directories created by test scripts as well as manual builds. Preserve reusable caches and comparison reports.

## Compiler Comparisons

- For matched runtime throughput, compile identical drivers and kernels as separate translation units without LTO. Keep inputs opaque at compile time and allow normal kernel optimization.
- Inspect assembly and use execution hooks or equivalent instrumentation to verify calls, iterations, or operations and their inputs and results. Check for inlining before concluding that work was removed.
- Report whole-program results separately and label constant-folded cases. Match memory speed when isolating code generation and record FastROM/SlowROM, pointer width, ABI, and linked runtime differences.
- Retain assembly, execution assertions, source, compiler, and runtime hashes, and repeated measurements. Follow the [comparison methodology](docs/technical/structures-runtime-comparison.md).

## Commits and Pull Requests

- Use short imperative subjects such as “Split runtime helpers into linkable objects.” Commit the implementation and related tests and build, benchmark, verification, or reproduction scripts together unless asked to split them. Keep handoff notes in the local, ignored `handoff.md`.
- Before committing, review staged and unstaged changes and untracked files. Include related work already present and preserve unrelated edits. After committing, inspect the commit's file list and `git status --short`, and commit any missing work-item files before reporting completion.
- In pull requests, explain the affected compiler or runtime behavior, link any relevant issue, and report the commands run and their results.

## Execution and Communication

- Talk to me ELI5 by default and go deeper if I ask.
- No em dashes.
- For single-line comments, never end with a period '.'
- Do not use these words: "authoritative", "oracle", "arena", "canonical"
- Prefer simple, maintainable changes. Reuse existing safeguards, remove redundant checks, and keep verification proportional to risk. Treat one-time incidents on their own merits before adding permanent requirements.
- Coordinate specialized agents without duplicating work. Finish once the acceptance criteria are met.
- Lead with the result and keep explanations direct. Include caveats and context when they affect the conclusion.
