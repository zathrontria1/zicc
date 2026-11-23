// Entry point and orchestration for post-emission assembly line passes
// Sub-modules own their helpers and read per-function state through lp_state

#include "lp_core.inc"
#include "lp_basic_passes.inc"
#include "lp_cfg_passes.inc"
#include "lp_cleanup.inc"
#include "lp_peepholes.inc"

// Bind line-pass state from the current codegen context
static void lp_bind_from_codegen(int is_volatile, int frame_address, int word_result,
                                 int value_result)
{
    lp_bind_state(cg.parser, &cg.label, &cg.arithmetic, cg.frame_map, &cg.assembly, &cg.length,
                  is_volatile, frame_address, word_result, value_result);
}

// A terminal transfer cannot expose the wide-result workspace
static void lp_wide_runtime_exit(Function *f, size_t at)
{
    LpRunner runner = {0};

    if (cg.parser->no_line_passes || f->symbol->interrupt) {
        return;
    }

    lp_bind_from_codegen(0, 0, 0, 1);

    if (lp_run(&runner, f, at, lp_jump_to_runtime_exit)) {
        lp_run(&runner, f, at, lp_unreachable);
    }

    while (lp_run(&runner, f, at, lp_repeated_inexact_raise)) {
    }

    lp_invalidate(&runner);
    free(runner.work);
}

// Prune unreachable lines before retrying Y-frame to S-relative conversion
static int lp_prune_before_frames(Function *f, size_t at)
{
    LpRunner runner = {0};
    int changed;

    if (cg.parser->no_line_passes) {
        return 0;
    }

    lp_bind_from_codegen(0, 0, 0, 1);
    changed = lp_run(&runner, f, at, lp_unreachable);

    lp_invalidate(&runner);
    free(runner.work);
    return changed;
}

// Set a literal return value after dismantling the stack frame
static int lp_delay_epilogue_literal(LpUnit *u, Function *f, size_t at)
{
    (void)at;

    if (u->indirect || body_asm_statements(f->body)) {
        return 0;
    }

    lp_liveness(u);

    for (unsigned i = 0; i < u->count; ++i) {
        LpLine *load = &u->lines[i];
        long value = lp_immediate(load);

        unsigned j = i + 1;

        if (j + 1 < u->count && lp_is(&u->lines[j], "jmp") && u->lines[j].target == (int)j + 1 &&
            u->lines[j + 1].first_incoming == (int)j && u->lines[j].next_incoming < 0) {
            j += 2;
        } else if (j < u->count && u->lines[j].label && u->lines[j].first_incoming < 0 &&
                   !strncmp(u->lines[j].text, "return_", 7)) {
            ++j;
        }

        if (j + 5 >= u->count) {
            continue;
        }

        LpLine *save = &u->lines[j];
        LpLine *base = &u->lines[j + 1];
        LpLine *carry = &u->lines[j + 2];
        LpLine *size = &u->lines[j + 3];
        LpLine *stack = &u->lines[j + 4];
        LpLine *restore = &u->lines[j + 5];

        if (value < 0 || load->m8 || load->x8 || !lp_is(load, "lda") || !lp_line_is(save, "tax") ||
            (!lp_line_is(base, "tya") && !lp_line_is(base, "tsc")) || !lp_line_is(carry, "clc") ||
            !lp_is(size, "adc") || lp_immediate(size) < 0 || !lp_line_is(stack, "tcs") ||
            !lp_line_is(restore, "txa") || (restore->out & LP_X)) {
            continue;
        }

        lp_set(restore, "    lda #$%04lX", value);
        load->deleted = save->deleted = 1;
        return 1;
    }

    return 0;
}

static void line_passes(Function *f, size_t at)
{
    LpRunner runner = {0};

    if (cg.parser->no_line_passes) {
        return;
    }

    // Interrupt handlers only run safe byte-mode and immediate-reuse cleanups
    if (f->symbol->interrupt) {
        lp_bind_from_codegen(0, 0, 0, 0);

        if (!statement_inline_markers(f->body)) {
            lp_run(&runner, f, at, lp_byte_region_modes);

            if (!lp_state.parser->no_value_reuse) {
                lp_run(&runner, f, at, lp_reuse_store_immediates);
            }
        }

        goto done;
    }

    int is_volatile = volatile_statements(f->body);
    int frame_address = frame_address_visible(f->body);
    int word_result = reg_width(f->symbol->type) == 2;
    int value_result = !cg.parser->no_body_optimizations && strcmp(f->symbol->name, "main")
                           ? body_value_returns(f->body)
                           : 1;

    lp_bind_from_codegen(is_volatile, frame_address, word_result, value_result);

    // Phase 1: early loop-bound setup and baseline cleanup
    if (!lp_state.parser->no_index_elimination) {
        lp_run(&runner, f, at, lp_stop_bounds);
    }

    while (lp_run(&runner, f, at, lp_step_literal_store)) {
    }

    lp_cleanup(&runner, f, at, 0);

    // Phase 2: Y promotion and stack-frame rewriting
    if (lp_run(&runner, f, at, lp_y_promote)) {
        lp_cleanup(&runner, f, at, 0);
    }

    if (lp_run(&runner, f, at, lp_y_promote_split)) {
        lp_cleanup(&runner, f, at, 0);
    }

    lp_run(&runner, f, at, lp_trim_private_frame);

    if (lp_run(&runner, f, at, lp_call_frame_homes)) {
        lp_cleanup(&runner, f, at, 1);

        if (lp_run(&runner, f, at, lp_late_call_save)) {
            lp_cleanup(&runner, f, at, 1);
        }
    } else if (lp_run(&runner, f, at, lp_pointer_frame_home)) {
        lp_run(&runner, f, at, lp_y_forms);
        lp_run(&runner, f, at, lp_push_parameter_frame);
        lp_run(&runner, f, at, lp_snapshot_index);

        while (lp_run(&runner, f, at, lp_equal_sum)) {
            lp_run(&runner, f, at, lp_relocated_dead_stores);
        }

        while (lp_run(&runner, f, at, lp_stage_subtract_before_sum)) {
        }
    }

    if (lp_run(&runner, f, at, lp_tail_wrapper)) {
        lp_run(&runner, f, at, lp_unreachable);
    }

    if (lp_run(&runner, f, at, lp_register_parameter_frame)) {
        lp_cleanup(&runner, f, at, 0);
    }

    if (lp_run(&runner, f, at, lp_leaf_stack_arguments)) {
        lp_run(&runner, f, at, lp_dead_inner_y_save);
        lp_run(&runner, f, at, lp_reload_saved_x);
        lp_run(&runner, f, at, lp_delay_byte_extract);
        lp_run(&runner, f, at, lp_test_indexed_mask);
        lp_cleanup(&runner, f, at, 0);
    }

    if (lp_run(&runner, f, at, lp_remove_index_save)) {
        while (lp_run(&runner, f, at, lp_remove_index_save)) {
        }

        lp_run(&runner, f, at, lp_register_values);
    }

    lp_run(&runner, f, at, lp_store_zero);
    lp_run(&runner, f, at, lp_outgoing_move_frame);
    lp_run(&runner, f, at, lp_unused_push_frame);
    lp_run(&runner, f, at, lp_unused_call_save);

    if (lp_run(&runner, f, at, lp_closed_frame) && !lp_state.is_volatile) {
        lp_cleanup(&runner, f, at, 0);
    }

    if (lp_run(&runner, f, at, lp_dead_stack_frame_stores)) {
        lp_cleanup(&runner, f, at, 0);
    }

    lp_run(&runner, f, at, lp_far_frame_cache);

    if (lp_run(&runner, f, at, lp_hoist_local_y_saves)) {
        lp_cleanup(&runner, f, at, 0);
    }

    // Phase 3: register, loop, divider, MMIO, and constant peepholes
    if (lp_run(&runner, f, at, lp_ax_reuse)) {
        lp_run(&runner, f, at, lp_dead_code);
    }

    while (lp_run(&runner, f, at, lp_retain_word_index)) {
    }

    lp_run(&runner, f, at, lp_tail_index_dispatch);

    if (!lp_state.parser->no_value_reuse) {
        lp_run(&runner, f, at, lp_reuse_store_immediates);
    }

    if (lp_run(&runner, f, at, lp_mmio_addressing) && !lp_state.parser->no_value_reuse) {
        lp_run(&runner, f, at, lp_reuse_store_immediates);
    }

    while (lp_run(&runner, f, at, lp_keep_post_cursors)) {
    }

    while (lp_run(&runner, f, at, lp_word_scan_cursor)) {
    }

    while (lp_run(&runner, f, at, lp_divider_index_wait)) {
    }

    while (lp_run(&runner, f, at, lp_forward_interleaved_words)) {
    }

    while (lp_run(&runner, f, at, lp_divider_remainder_last)) {
    }

    while (lp_run(&runner, f, at, lp_keep_loop_word_in_a)) {
    }

    while (lp_run(&runner, f, at, lp_chain_reduction_in_a)) {
    }

    while (lp_run(&runner, f, at, lp_keep_reduction_in_a)) {
        lp_run(&runner, f, at, lp_forward_constants);
        lp_run(&runner, f, at, lp_reloads);
    }

    while (lp_run(&runner, f, at, lp_forward_conditional_word)) {
    }

    lp_run(&runner, f, at, lp_forward_shifted_word);
    lp_run(&runner, f, at, lp_forward_or_chain);
    lp_run(&runner, f, at, lp_reuse_clear_carry);

    while (lp_run(&runner, f, at, lp_redundant_y_offset)) {
    }

    while (lp_run(&runner, f, at, lp_commute_spilled_add)) {
    }

    while (lp_run(&runner, f, at, lp_forward_workspace_copy)) {
    }

    while (lp_run(&runner, f, at, lp_direct_rhs_operand)) {
    }

    lp_run(&runner, f, at, lp_drop_dead_workspace_stores);

    while (lp_run(&runner, f, at, lp_zero_extended_byte_compare)) {
    }
    lp_run(&runner, f, at, lp_scaled_word_latch);

    while (lp_run(&runner, f, at, lp_rmw_reload)) {
    }

    while (lp_run(&runner, f, at, lp_narrow_divisor_load)) {
    }

    lp_run(&runner, f, at, lp_divider_wait_mask);

    while (lp_run(&runner, f, at, lp_sink_branch_store)) {
    }

    lp_run(&runner, f, at, lp_thread_equal_store);

    if (lp_run(&runner, f, at, lp_cache_stored_word)) {
        while (lp_run(&runner, f, at, lp_cache_stored_word)) {
        }

        lp_cleanup(&runner, f, at, 0);
        lp_run(&runner, f, at, lp_dead_stack_frame_stores);
    }

    while (lp_run(&runner, f, at, lp_demanded_masks)) {
    }

    lp_run(&runner, f, at, lp_sign_extension_branch);
    lp_run(&runner, f, at, lp_duplicate_stores);
    lp_run(&runner, f, at, lp_known_accumulator_mode);

    while (lp_run(&runner, f, at, lp_y_saved_index)) {
        lp_run(&runner, f, at, lp_reloads);
        lp_run(&runner, f, at, lp_register_values);
    }

    while (lp_run(&runner, f, at, lp_y_scratch_reuse)) {
        lp_run(&runner, f, at, lp_reloads);
        lp_run(&runner, f, at, lp_register_values);
    }

    lp_run(&runner, f, at, lp_dead_x_save);
    lp_run(&runner, f, at, lp_byte_rmw);

    while (lp_run(&runner, f, at, lp_demanded_masks)) {
    }

    lp_run(&runner, f, at, lp_dead_epilogue_stores);
    lp_run(&runner, f, at, lp_dead_code);
    lp_run(&runner, f, at, lp_dead_stack_word_save);
    lp_run(&runner, f, at, lp_store_pulled_pair);

    if (lp_run(&runner, f, at, lp_store_low_before_high)) {
        lp_cleanup(&runner, f, at, 0);
    }

    while (lp_run(&runner, f, at, lp_post_index_test)) {
    }

    while (lp_run(&runner, f, at, lp_scaled_displacement)) {
    }

    if (lp_run(&runner, f, at, lp_literal_shifts)) {
        lp_cleanup(&runner, f, at, 0);
    }

    while (lp_run(&runner, f, at, lp_signed_difference_flags)) {
    }

    while (lp_run(&runner, f, at, lp_stage_pair_words)) {
    }

    if (lp_run(&runner, f, at, lp_pair_store_order)) {
        while (lp_run(&runner, f, at, lp_pair_store_order)) {
        }

        if (lp_run(&runner, f, at, lp_dead_stack_frame_stores)) {
            lp_cleanup(&runner, f, at, 0);
        }
    }

    if (lp_run(&runner, f, at, lp_reloads)) {
        lp_run(&runner, f, at, lp_dead_stack_frame_stores);
    }

    if (lp_run(&runner, f, at, lp_push_register_pair)) {
        lp_run(&runner, f, at, lp_dead_stack_frame_stores);
    }

    lp_run(&runner, f, at, lp_cancel_pull_push);
    lp_run(&runner, f, at, lp_index_carry);
    lp_run(&runner, f, at, lp_increment_wrap_test);
    lp_run(&runner, f, at, lp_postdecrement_truth);
    lp_run(&runner, f, at, lp_small_accumulator_steps);

    while (lp_run(&runner, f, at, lp_index_transfer_steps)) {
    }

    if (lp_run(&runner, f, at, lp_materialized_zero_flag)) {
        lp_run(&runner, f, at, lp_jump_threading);
    }

    lp_run(&runner, f, at, lp_sign_bit_order);

    if (lp_run(&runner, f, at, lp_reuse_far_byte)) {
        while (lp_run(&runner, f, at, lp_reuse_far_byte)) {
        }

        lp_run(&runner, f, at, lp_drop_dead_workspace_stores);
    }

    while (lp_run(&runner, f, at, lp_keep_mask_source)) {
    }

    while (lp_run(&runner, f, at, lp_signed_home_positive)) {
    }

    while (lp_run(&runner, f, at, lp_keep_loop_word_in_a)) {
    }

    if (lp_run(&runner, f, at, lp_fixed_stack_argument)) {
        while (lp_run(&runner, f, at, lp_fixed_stack_argument)) {
        }

        while (lp_run(&runner, f, at, lp_dead_stack_frame_stores)) {
            lp_cleanup(&runner, f, at, 0);
        }
    }

    lp_run(&runner, f, at, lp_store_zero);

    while (lp_run(&runner, f, at, lp_byte_region_modes)) {
    }

    if (lp_run(&runner, f, at, lp_zero_extended_byte_compare)) {
        while (lp_run(&runner, f, at, lp_zero_extended_byte_compare)) {
        }

        while (lp_run(&runner, f, at, lp_demanded_masks)) {
        }
    }

    lp_run(&runner, f, at, lp_store_zero);
    lp_run(&runner, f, at, lp_sink_branch_store);
    lp_run(&runner, f, at, lp_thread_equal_store);

    if (lp_run(&runner, f, at, lp_cache_stored_word)) {
        while (lp_run(&runner, f, at, lp_cache_stored_word)) {
        }

        lp_cleanup(&runner, f, at, 0);
        lp_run(&runner, f, at, lp_dead_stack_frame_stores);
    }

    while (lp_run(&runner, f, at, lp_demanded_masks)) {
    }

    lp_run(&runner, f, at, lp_duplicate_stores);
    lp_run(&runner, f, at, lp_known_accumulator_mode);

    while (lp_run(&runner, f, at, lp_reverse_signed_literal)) {
        lp_run(&runner, f, at, lp_drop_dead_workspace_stores);
    }

    while (lp_run(&runner, f, at, lp_far_stack_read)) {
    }

    lp_run(&runner, f, at, lp_varargs_stack_read);

    if (!lp_state.parser->no_private_regions) {
        lp_run(&runner, f, at, lp_pushed_index_checks);
    }

    lp_run(&runner, f, at, lp_varargs_tail_call);

    if (lp_run(&runner, f, at, lp_literal_to_index)) {
        lp_run(&runner, f, at, lp_dead_push_pairs);
    }

    lp_run(&runner, f, at, lp_literal_stack_argument_bytes);
    lp_run(&runner, f, at, lp_push_immediate_word);

    while (lp_run(&runner, f, at, lp_indexed_alu_rhs)) {
    }

    while (lp_run(&runner, f, at, lp_preserved_range_pointer)) {
    }

    while (lp_run(&runner, f, at, lp_saved_index_steps)) {
    }

    while (lp_run(&runner, f, at, lp_scaled_base_steps)) {
    }

    while (lp_run(&runner, f, at, lp_restore_indirect_index)) {
    }

    while (lp_run(&runner, f, at, lp_carry_from_shift_byte)) {
    }

    lp_run(&runner, f, at, lp_test_index);

    if (lp_run(&runner, f, at, lp_saved_x_read)) {
        lp_run(&runner, f, at, lp_reuse_far_byte);
    }

    while (lp_run(&runner, f, at, lp_cleared_byte_loop)) {
    }

    if (lp_run(&runner, f, at, lp_const_branches)) {
        lp_cleanup(&runner, f, at, 0);
    }

    if (lp_run(&runner, f, at, lp_published_frame_read)) {
        while (lp_run(&runner, f, at, lp_published_frame_read)) {
        }

        lp_run(&runner, f, at, lp_forward_constants);
        lp_cleanup(&runner, f, at, 0);
    }

    lp_run(&runner, f, at, lp_zero_high_across_byte_load);

    while (lp_run(&runner, f, at, lp_delay_index_literal)) {
    }

    if (lp_run(&runner, f, at, lp_overwritten_stores)) {
        lp_cleanup(&runner, f, at, 0);
    }

    if (lp_run(&runner, f, at, lp_unused_push_frame)) {
        lp_cleanup(&runner, f, at, 0);
    }

    while (lp_run(&runner, f, at, lp_step_literal_store)) {
    }

    if (lp_run(&runner, f, at, lp_zero_index_address)) {
        while (lp_run(&runner, f, at, lp_zero_index_address)) {
        }

        if (lp_run(&runner, f, at, lp_forward_constants)) {
            lp_cleanup(&runner, f, at, 0);
        }
    }

    if (lp_run(&runner, f, at, lp_direct_relocated_read)) {
        lp_cleanup(&runner, f, at, 0);
    }

    if (lp_run(&runner, f, at, lp_dead_stack_frame_stores)) {
        lp_cleanup(&runner, f, at, 0);
    }

    lp_run(&runner, f, at, lp_skip_dead_loop_step);

    while (lp_run(&runner, f, at, lp_delay_epilogue_literal)) {
    }

    while (lp_run(&runner, f, at, lp_delay_guarded_y_init)) {
    }

    while (lp_run(&runner, f, at, lp_delay_guarded_x_store)) {
    }

    while (lp_run(&runner, f, at, lp_keep_frame_argument_in_x)) {
    }

    while (lp_run(&runner, f, at, lp_forward_named_latch_load)) {
    }

    while (lp_run(&runner, f, at, lp_named_counter_in_x)) {
    }

    while (lp_run(&runner, f, at, lp_workspace_index_backedge)) {
    }

    while (lp_run(&runner, f, at, lp_skip_repeated_far_loop_guard)) {
    }

    while (lp_run(&runner, f, at, lp_repeated_inexact_raise)) {
    }

    lp_run(&runner, f, at, lp_far_advance_return);
    lp_run(&runner, f, at, lp_dead_retained_varargs_cursor);
    lp_run(&runner, f, at, lp_dead_literal_before_call);

    if (lp_run(&runner, f, at, lp_literal_limb_carry)) {
        lp_cleanup(&runner, f, at, 0);
    }

    if (lp_run(&runner, f, at, lp_compare_past_frame_clear)) {
        lp_cleanup(&runner, f, at, 0);
    }

    if (lp_run(&runner, f, at, lp_compare_saved_frame_offset)) {
        lp_cleanup(&runner, f, at, 0);
    }

    if (lp_run(&runner, f, at, lp_forward_frame_clear)) {
        lp_cleanup(&runner, f, at, 0);
    }

    lp_run(&runner, f, at, lp_byte_loop_test_exits);

    if (lp_run(&runner, f, at, lp_jump_to_runtime_exit)) {
        lp_run(&runner, f, at, lp_unreachable);
    }

    if (lp_run(&runner, f, at, lp_stack_cleanup_before_exit)) {
        lp_cleanup(&runner, f, at, 0);
    }

    while (lp_run(&runner, f, at, lp_dead_exit_frame_store)) {
        lp_cleanup(&runner, f, at, 0);
    }

    while (lp_run(&runner, f, at, lp_home_private_cursor)) {
    }

    lp_run(&runner, f, at, lp_address_only_frame);

    if (lp_run(&runner, f, at, lp_reuse_stack_word)) {
        while (lp_run(&runner, f, at, lp_index_transfer_steps)) {
        }
    }

    lp_run(&runner, f, at, lp_home_far_stack_argument);
    lp_run(&runner, f, at, lp_load_index_from_workspace);

    while (lp_run(&runner, f, at, lp_reuse_frame_copies)) {
    }

    // Phase 4: guard-frame scheduling and final carry cleanup
    lp_run(&runner, f, at, lp_schedule_entry_words);
    lp_run(&runner, f, at, lp_delay_guard_frame);
    lp_run(&runner, f, at, lp_remove_stack_guard_frame);

    // Arithmetic peepholes still need the original carry setup, so this runs last
    while (lp_run(&runner, f, at, lp_carry_on_fallthrough)) {
    }

done:
    lp_invalidate(&runner);
    free(runner.work);
}
