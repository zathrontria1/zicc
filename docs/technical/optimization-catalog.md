# Optimization implementation reference

Start with the [optimization guide](../optimizations.md) for a C example, or
read the [compiler architecture](architecture.md) for the full pass order and
shared state.
Use the table here to find the compiler code that implements it and the tests
that check it. Timing figures belong to the builds described in the linked
reports.

## Reading the examples

The guide's assembly blocks are excerpts with simplified symbols and stated
register assumptions. They are not complete alternative implementations of the
surrounding C. Omitted work includes argument evaluation, sign extension,
address scaling, stack/width restoration and final flag repair. Whether a
particular selection wins also depends on other enabled passes.

For complete current output from representative kernels:

```text
make
build/zicc.exe docs/technical/optimization-examples.c -o build/optimization-examples.s -I include
```

The [example translation unit](optimization-examples.c) has external calls on
purpose: compiling it to assembly requires no application driver or external
definitions. It is not a ROM or a timing workload. The registered tests below
provide runtime, aliasing, boundary and fallback coverage. Use `-o` immediately
after the input filename, as required by the compiler command line.

Normal code uses A16/X16, D=0 and DBR=$7E. Pointer representation, signed
promotion, 16-bit near wrap, 24-bit far carry, volatile access order and public
argument/result ownership remain part of every optimization's contract.

## Loop lowering phases

| Phase | Owner and handoff |
| --- | --- |
| Normalize the body | [Body optimizer](../../src/codegen/body_opt.inc) puts equivalent counted loops into one form when safe before planning. |
| Plan function-wide homes | [Function emission](../../src/codegen/codegen.inc) prepares strength cursors, affine regions and induction homes before selecting leaf or framed emission. [Affine planning](../../src/codegen/affine_loops.inc) owns running addresses and the unroll plan. Wide and other ABI-sensitive functions take restricted planning paths. |
| Select the loop | `emit_loop` enters region homes and tries scaled-ring lowering. `emit_loop_body` tries specialized emitters in order, then combines any affine cursor and DP counter with the common loop emitter. The common emitter also handles generic control flow when no plan applies. |
| Clean up assembly | [Line passes](../../src/codegen/line_passes.inc) rewrite eligible emitted functions after frame selection. [Relaxation](../../src/relax.c) resolves branch distances after emission. |

Search for `; loop lowering:` in generated assembly to see the selected
dispatcher path. Specialized emitters keep their detailed comments, such as
the unroll factor or cursor stride. A generic fallback means no specialized
dispatcher path won. Body rewrites and whole-function leaf emitters can
replace a loop before it reaches this dispatcher.

## Frontend and typed IR

| Guide topics | Implementation | Detailed rules and verification |
| --- | --- | --- |
| Literal folding/refolding | [parser.inc](../../src/parser.inc), [scalar_values.inc](../../src/codegen/scalar_values.inc) | [expression rules](operations.md#expressions); constant-folding/conversions parts |
| Dominating copies/constants; computed temporary forwarding | [scalar_values.inc](../../src/codegen/scalar_values.inc) | [scalar values](scalar-values.md), [computed stores](computed-stores.md); scalar-values/private-cleanups parts |
| Structured facts, dead local definitions and branches | [body_opt.inc](../../src/codegen/body_opt.inc) | [structured codegen](structured-codegen.md); body-codegen part |
| Shared-predicate selections | [body_opt.inc](../../src/codegen/body_opt.inc) | selection fusion; private-cleanups part |
| Named immutable/mutable-value reuse; comparison reuse | [value_reuse.inc](../../src/codegen/value_reuse.inc) | [versioned reuse](value-reuse.md); value-reuse/value-placement parts |
| Known bits, range joins, conversion proofs | [known_values.inc](../../src/codegen/known_values.inc) | [known values](known-values.md); known-values part |
| Per-cell ranges and relational span bounds | [range_values.inc](../../src/codegen/range_values.inc) | collision range propagation; range-values part |
| Exact recurrences and copied-home coalescing | [value_recurrence.inc](../../src/codegen/value_recurrence.inc) | recurrences; value-placement/gradient-codegen parts |

Facts are bounded analyses, not profile feedback. A failed proof or exhausted
budget retains ordinary lowering. Side-effecting definitions are not discarded
just because their destination is dead. Reuse must preserve when a read first
executes; it cannot hoist a potentially invalid memory access onto a new path.

## Arithmetic and comparisons

| Guide topics | Implementation | Detailed rules and verification |
| --- | --- | --- |
| Direct integer operands, native wide ALU, deferred commutative loads | [wide.inc](../../src/codegen/wide.inc), [codegen.inc](../../src/codegen/codegen.inc) | [expressions](operations.md#expressions); wide-codegen/word-expressions suites |
| Word trees, constant coefficients and temporary scheduling | [word_expr.inc](../../src/codegen/word_expr.inc) | [word planner](word-expression-optimization.md); word-expressions suite |
| Exact XBA/mask/shift sequences | [word_shifts.inc](../../src/codegen/word_shifts.inc) | [word shifts](byte-shuffle-stores.md); byte-shuffles part |
| Byte/mixed/word/wide helper selection | [codegen.inc](../../src/codegen/codegen.inc), [wide.inc](../../src/codegen/wide.inc), `runtime/integers.s` | [width selection](word-call-optimization.md), [arithmetic regions](arithmetic-regions.md), [wide products](widened-product-optimization.md); arithmetic and hardware suites |
| Word-by-long multiplication and reduction corrections | [wide.inc](../../src/codegen/wide.inc), [counted_reductions.inc](../../src/codegen/counted_reductions.inc) | [mixed product](mul16x32-specialization.md); widened-products suite |
| Matching unsigned quotient/remainder reuse | [divmod.inc](../../src/codegen/divmod.inc) | [reuse rules](operations.md#quotientremainder-reuse); divmod suite |
| Direct word/wide equality, zero/constant tests and direct condition branches | [codegen.inc](../../src/codegen/codegen.inc) | [comparison flags](operations.md#word-comparisons-and-condition-flags); comparisons, compare-constants and body-codegen checks |
| Min/max, non-overflow CMP/N and paired selection subtraction | [selections.inc](../../src/codegen/selections.inc) | bounded signed selection, four residual items; signed-minmax/value-placement parts |
| Byte relations and short-circuit predicates | [codegen.inc](../../src/codegen/codegen.inc), [register_loops.inc](../../src/codegen/register_loops.inc) | [byte predicates](operations.md#short-circuit-byte-predicates-and-exit-values), [scalar conversions](scalar-values.md); byte-predicates and body-codegen checks |
| Demanded low/high word loads | [codegen.inc](../../src/codegen/codegen.inc) | projection rules; private-cleanups part |

Runtime entries also contain optimized hardware partial products, byte-divisor
division, bounded software division and register-held shift loops. Those are
helper implementations, distinct from the compiler's decision to call them.
Their contracts and arithmetic vectors are described in
[operations](operations.md#expressions) and [arithmetic regions](arithmetic-regions.md).
See the [C library math reference](../libc.md#mathh) for the assembly math functions.

## Loops and addresses

| Guide topics | Implementation | Detailed rules and verification |
| --- | --- | --- |
| Function/loop cursors, row strides and structure strides | [strength.inc](../../src/codegen/strength.inc), [affine_loops.inc](../../src/codegen/affine_loops.inc) | [affine arrays](affine-array-loops.md), [struct cursors](struct-loop-cursors.md); strength suite |
| X-held loop cursors and address setup | [bound_cursors.inc](../../src/codegen/bound_cursors.inc) | [cursor allocation](operations.md#direct-page-homes-and-register-cursors), [setup](loop-address-setup.md); register-loops/frames checks |
| X/Y retained indices; borrowed outer displacement | [index_retention.inc](../../src/codegen/index_retention.inc) | [retention](loop-index-retention.md), nested ownership; index-retention/private-cleanups parts |
| Displacement-only termination and folded literal setup | [index_retention.inc](../../src/codegen/index_retention.inc) | gradient completion; gradient-codegen part |
| Induction/sentinel test replacement | [lftr.inc](../../src/codegen/lftr.inc), [line_passes.inc](../../src/codegen/line_passes.inc) | [allocation rules](operations.md#direct-page-homes-and-register-cursors); index-elimination part |
| Saved DP-zero counters and index recovery | [dp_counters.inc](../../src/codegen/dp_counters.inc) | [DP counters](dp-loop-counters.md); strength suite |
| Byte-bounded action-loop countdown | [body_opt.inc](../../src/codegen/body_opt.inc) | [control-flow rules](arithmetic-regions.md#scalar-control-flow); arithmetic-regions part |
| Descending arithmetic register regions | [numeric_loops.inc](../../src/codegen/numeric_loops.inc) | [register regions](arithmetic-regions.md#register-resident-arithmetic-regions); arithmetic-regions part |
| Near byte-loop IR, byte temporaries and predicates | [register_loops.inc](../../src/codegen/register_loops.inc) | [register loops](operations.md#register-loops-and-accumulator-width), [temporary lifetimes](operations.md#indexed-byte-cursors-and-temporary-lifetimes); register-loops/byte-predicates suites |
| Generic far cursors and shared indexed far bases | [far_loops.inc](../../src/codegen/far_loops.inc), [indexed_far_loops.inc](../../src/codegen/indexed_far_loops.inc) | [far recovery](far-loop-recovery.md), [indexed far loops](indexed-far-loops.md); far-loops/bank-pointers parts |
| Costed full/partial unrolling and relative signed bounds | [loop_unroll.inc](../../src/codegen/loop_unroll.inc), [body_opt.inc](../../src/codegen/body_opt.inc) | [unrolling](loop-unrolling.md), [relative bounds](structured-codegen.md); strength/body-codegen checks |
| Entry-only inputs and nested store leaves | [entry_cursors.inc](../../src/codegen/entry_cursors.inc) | [entry cursors](entry-only-cursors.md), [follow-ups](loop-follow-ups.md); frames suite |
| Guarded retry normalization | [body_opt.inc](../../src/codegen/body_opt.inc) | [structured codegen](structured-codegen.md); body-codegen part |
| Field-product reductions | [counted_reductions.inc](../../src/codegen/counted_reductions.inc) | [reductions](counted-reductions.md), [far/bank setup](struct-reduction-banks.md); structs/frame checks |

Induction removal has several independent forms. The strict descending LFTR
proof establishes a nonnegative bounded index, recognized updates and a scale
that cannot produce a false base/sentinel match. Later stop-bound rewriting
also requires a proven equivalent pointer test. Fully unrolled regions can
drop unused index/cursor homes without applying that descending-loop proof.
The displacement-only retained selector instead proves no remaining scalar
index observation and no scaled-bound wrap. None of these makes an arbitrary
potentially wrapping C loop finite.

## Memory, frames and calls

| Guide topics | Implementation | Detailed rules and verification |
| --- | --- | --- |
| Direct named-array/field ALU and memory operands | [indexed_operands.inc](../../src/codegen/indexed_operands.inc) | [direct indexing](direct-indexed-operands.md); indexed-operands part |
| Shared element/address calculations | [shared_elements.inc](../../src/codegen/shared_elements.inc), [body_opt.inc](../../src/codegen/body_opt.inc) | [shared elements](shared-element-addresses.md), [address CSE](structured-codegen.md); shared-elements suite |
| Named-ROM, fixed-address and far indexed transfers | [far.inc](../../src/codegen/far.inc) | [far byte loads](indexed-far-byte-loads.md), [costs](far-pointer-costs.md); far-pointer-costs/bank-pointers parts |
| DP pointers and bank-zero fixed accesses | [dpage_access.inc](../../src/codegen/dpage_access.inc), [codegen.inc](../../src/codegen/codegen.inc) | [DP pointers](dpage-pointer-access.md), [machine/storage rules](operations.md#machine-and-storage); dpage-access/indexed-dpage checks |
| Small wrapping near offsets | [codegen.inc](../../src/codegen/codegen.inc) | [structured codegen](structured-codegen.md); body-codegen part |
| Direct scalar updates and pure-source stores | [codegen.inc](../../src/codegen/codegen.inc) | [home updates](scalar-home-updates.md), [destination scheduling](aggregate-results.md); scalar-homes suite |
| Neighboring RAM stores and byte regions | [store_fusion.inc](../../src/codegen/store_fusion.inc), [byte_regions.inc](../../src/codegen/byte_regions.inc) | [store fusion](byte-shuffle-stores.md), byte-index regions; store-fusion/value-placement parts |
| Aggregate transfer selection and discarded aggregate results | [aggregate_copy.inc](../../src/codegen/aggregate_copy.inc) | [aggregate results](aggregate-results.md), [copy contracts](operations.md#structure-and-union-assignment); structs/members suites |
| Literal strcpy | [aggregate_copy.inc](../../src/codegen/aggregate_copy.inc) | [literal copies](literal-copies.md); literal-copies part |
| Scalar return/store leaves and stack-relative leaves | [scalar_values.inc](../../src/codegen/scalar_values.inc), [word_expr.inc](../../src/codegen/word_expr.inc), [wide.inc](../../src/codegen/wide.inc) | [computed stores](computed-stores.md), [scalar leaves](scalar-values.md); scalar-values/stack-frames parts |
| Guarded field-update leaf | [guarded_updates.inc](../../src/codegen/guarded_updates.inc) | [guarded updates](guarded-updates.md); frames suite |
| Parameter homes, spills, stack reservations | [codegen.inc](../../src/codegen/codegen.inc) | [register homes](register-argument-homes.md), [stack reservations](stack-argument-reservations.md); frames suite |
| Small frame allocation, result restoration and early guards | [codegen.inc](../../src/codegen/codegen.inc) | [tiny frames](word-call-optimization.md), [early guards](frame-optimization.md); frames suite |
| Function/regional DP allocation and helper/callee summaries | [dp_homes.inc](../../src/codegen/dp_homes.inc), [region_homes.inc](../../src/codegen/region_homes.inc) | [allocation contracts](operations.md#direct-page-homes-and-register-cursors); dp-homes/region-homes parts |
| Physical private-slot coloring | [frame_packing.inc](../../src/codegen/frame_packing.inc), [codegen.inc](../../src/codegen/codegen.inc) | packing and address relocation; private-cleanups/decimal-assembly/frame checks |
| Dead-home word accumulation | [codegen.inc](../../src/codegen/codegen.inc) | gradient completion; gradient-codegen/private-cleanups parts |
| Direct staging, fixed addresses and discarded call results | [codegen.inc](../../src/codegen/codegen.inc) | call setup, [argument scheduling](structured-codegen.md); private-cleanups/bank-pointers parts |
| Known-bank private byte-loop/reduction entries | [bank_calls.inc](../../src/codegen/bank_calls.inc) | [private bank entries](bank-call-specialization.md), [reduction entries](struct-reduction-banks.md); bank-calls/bank-reductions parts |
| Near-origin standard strcmp adapter | [near_libcalls.inc](../../src/codegen/near_libcalls.inc) | [adapter contracts](structured-codegen.md); body-codegen part |
| Same-TU inlining and private-body reachability | [inline.inc](../../src/codegen/inline.inc) | [inlining policy](inlining.md); inlining part |
| Cross-TU typed optimization/inlining | [source_lto.inc](../../src/source_lto.inc) | [source LTO](source-lto.md); source-lto part |

Whole-function leaf selectors have deliberately narrow grammars. Their ordinary
fallback remains available; the existence of a leaf selector is not a claim of
general-purpose register allocation. Likewise, physical frame packing keeps
logical symbol identities separate so DP and value analysis cannot confuse
different locals that happen to share a slot.

## Assembly cleanup

[line_passes.inc](../../src/codegen/line_passes.inc) combines several smaller transformations. The guide groups
them by their visible effect:

| Transformation | Main entry points |
| --- | --- |
| Repeated frame/home loads and values already in A/X/Y | `lp_reloads`, `lp_ax_reuse`, `lp_register_values`, `frame_value_in_a` |
| A availability across CFG joins | `lp_cfg_accumulator` in [accumulator_cfg.inc](../../src/codegen/accumulator_cfg.inc) |
| Private-copy forwarding and dead private stores | [private_values.inc](../../src/codegen/private_values.inc), [private_regions.inc](../../src/codegen/private_regions.inc) |
| Constants and dead compiler-workspace writes | `lp_forward_constants`, `lp_dead_workspace` |
| Unused arithmetic/results and unreachable instructions | `lp_dead_code`, `lp_const_branches`, `lp_unreachable` |
| Folded address steps and cheaper Y forms | `lp_fold_steps`, `lp_y_forms` |
| Fewer argument push/address-adjustment shuffles | `lp_push_offsets` |
| Y-held workspace values | `lp_y_promote` |
| Combined immediate additions | `lp_add_constants` |
| Redundant masks and adjacent accumulator-width transitions | `lp_demanded_masks`, `lp_byte_region_modes` |
| Native private INC/DEC and unused frame tails | `lp_private_word_steps`, `lp_trim_private_frame` |
| Near tail jumps and final branch sizing | `near_relocations`, [relax.c](../../src/relax.c) |

All depend on emitted instruction effects, widths, alias/frame identity and
live registers/flags. Labels and calls are barriers unless a more specific CFG
or audited helper proof applies. See [private regions](private-regions.md),
[arithmetic regions](arithmetic-regions.md) and
[branch relaxation](operations.md#iterative-branch-relaxation).

Switch dispatch already keeps its control value in A or A/X rather than a saved
home, using direct immediate comparisons. Jump tables and balanced switch trees
are not implemented; see [switch lowering](operations.md#switch-dispatch).

Native interrupt wrappers separately save the emitted workspace clobber set;
see [scratch preservation](interrupt-scratch-preservation.md). ROM allocation
and near/long call-stage selection belong to the build pipeline; see
[allocation](rom-allocation.md). Neither is permission to alter volatile bus
accesses or application execution counts.

## Controls and verification

Optimizations are normally enabled by default. Source LTO is opt-in. A
`--no-*` switch isolates a family, not an optimization level: other enabled
passes can still simplify the same source. The current CLI advertises:

```text
--no-strength-reduction  --no-body-optimizations  --no-inline
--no-known-values       --no-value-reuse         --no-private-regions
--no-byte-shuffles      --no-store-fusion        --no-copy-selection
--no-indexed-operands   --no-direct-dpage        --no-indexed-dpage
--no-register-loops     --no-register-cursors    --no-loop-index-retention
--no-dp-counters        --no-index-elimination   --no-loop-unroll
--no-dp-homes           --no-region-homes        --no-dp-summaries
--no-stack-frames       --no-divmod-reuse        --no-line-passes
--no-bank-specialization --no-branch-relaxation
```

Inlining has separate forced/noinline rules. See its documentation before using
`--no-inline` to require call boundaries. Run `make check` for complete coverage
after compiler changes, following [the verification workflow](../technical.md#verification).
Assembly-only inspection is useful for documentation, but does not establish
runtime correctness, executed workload or timing.
