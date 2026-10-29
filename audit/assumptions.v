(** Split assumption audit. Not run during migration. *)
From cjr Require Import adequacy primitive_laws generic_laws buffer buffer_laws.
From cjr.examples Require Import arith struct_upd cell class_upd vtable cj_print generic_print generic_examples generic_tests.
Print Assumptions cjr_adequacy.
Print Assumptions sum_one_adequate.
Print Assumptions bump_adequate.
Print Assumptions cell_adequate.
Print Assumptions class_bump_adequate.
Print Assumptions vtable_adequate.
Print Assumptions wp_mul.
Print Assumptions wp_rem.
Print Assumptions wp_bitxor.
Print Assumptions wp_bitand.
Print Assumptions wp_div.
Print Assumptions erase_legacy.
Print Assumptions erase_instantiate.
Print Assumptions erase_subst.
Print Assumptions generic_wp_legacy.
Print Assumptions generic_wp_instantiate.
Print Assumptions generic_adequacy.
Print Assumptions extracted_program_checked.
Print Assumptions generic_program_valid.
Print Assumptions identity_spec.
Print Assumptions pair_construct_spec.
Print Assumptions pair_first_spec.
Print Assumptions pair_second_spec.
Print Assumptions box_construct_spec.
Print Assumptions box_get_spec.
Print Assumptions box_map_spec.
Print Assumptions generic_main_wp.
Print Assumptions generic_main_adequate.
Print Assumptions buffer.buffer_fill_closed.
Print Assumptions buffer.buffer_make_closed.
Print Assumptions buffer.closed_lit.
Print Assumptions buffer_laws.buffer_zero_cells.
Print Assumptions buffer_laws.wp_buffer_fill.
Print Assumptions buffer_laws.wp_buffer_make.
