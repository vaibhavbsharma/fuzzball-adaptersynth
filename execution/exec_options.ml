(*
  Copyright (C) BitBlaze, 2009-2013, and copyright (C) 2010 Ensighta
  Security Inc.  All rights reserved.
*)


type offset_strategy = UniformStrat | BiasedSmallStrat

let offset_strategy_of_string s =
  match s with
    | "uniform" -> UniformStrat
    | "biased-small" -> BiasedSmallStrat
    | _ -> failwith "Unknown offset strategy"

(* This type plays a similar role to Asmir.arch and
   Libasmir.bfd_architecture, but it's structured to be easier to use
   in matching by exporting the full list of values, and only
   including architectures supported by Vine execution. More recently
   the other ones have been changed to be more similar too, so
   there's some duplication that could be removed. *)
type execution_arch = X86 | X64 | ARM

let execution_arch_of_string s =
  match s with
    | "i386"|"x86" -> X86
    | "x64"|"x86-64"|"x86_64"|"amd64"|"intel64" -> X64
    | "arm" -> ARM
    | _ -> failwith "Unrecognized architecture"

let asmir_arch_of_execution_arch = function
  | X86 -> Asmir.arch_i386
  | X64 -> Asmir.arch_x64
  | ARM -> Asmir.arch_arm

let libasmir_arch_of_execution_arch = function
  | X86 -> Libasmir.Asmir_arch_x86
  | X64 -> Libasmir.Asmir_arch_x64
  | ARM -> Libasmir.Asmir_arch_arm

let max_input_string_length = ref 0
let input_string_mem_prefix = ref None

let next_periodic_influence : int ref = ref (-1)

let opt_trace_temps = ref false
let opt_trace_temps_encoded = ref false
let opt_use_tags = ref false
let opt_fail_offset_heuristic = ref true
let opt_trace_solver = ref false
let opt_measure_influence_syscall_args = ref false
let opt_solver_timeout = ref None
let opt_timeout_as_unsat = ref false
let opt_solver_slow_time = ref 1.0
let opt_save_solver_files = ref false
let opt_solver_path = ref "stp"
let opt_follow_path = ref ""
let opt_branch_preference = Hashtbl.create 10
let opt_branch_preference_unchecked = Hashtbl.create 10
let opt_always_prefer = ref None
let opt_iteration_limit = ref 1000000000000L
let opt_f2_iteration_limit = ref 1000000000000L
let opt_iteration_limit_enforced = ref None
let opt_f2_iteration_limit_enforced = ref None
let opt_insn_limit = ref Int64.minus_one
let opt_watch_expr_str = ref None
let opt_watch_expr = ref None
let opt_path_depth_limit = ref 1000000000000L
let opt_query_branch_limit = ref 999999999
let opt_random_seed = ref 0
let opt_trace_decision_tree = ref false
let opt_save_decision_tree_interval = ref None
let opt_decision_tree_use_file = ref false
let opt_trace_randomness = ref false
let opt_measure_influence_derefs = ref false
let opt_measure_influence_reploops = ref false
let opt_measure_deref_influence_at = ref None
let opt_measure_expr_influence_at = ref None
let opt_multipath_influence_only = ref false
let opt_stop_at_measurement = ref false
let opt_periodic_influence = ref None
let opt_influence_bound = ref (-2.0)
let opt_disqualify_addrs = ref []
let opt_check_condition_at = ref []
let opt_trace_assigns = ref false
let opt_trace_assigns_final_pc = ref false
let opt_trace_assigns_string = ref false
let opt_trace_conditions = ref false
let opt_trace_decisions = ref false
let opt_trace_binary_paths = ref false
let opt_trace_binary_paths_delimited = ref false
let opt_trace_binary_paths_bracketed = ref false
let opt_trace_insns = ref false
let opt_trace_loads = ref false
let opt_trace_stores = ref false
let opt_trace_callstack = ref false
let opt_trace_sym_addrs = ref false
let opt_trace_sym_addr_details = ref false
let opt_trace_syscalls = ref false
let opt_match_syscalls_addr_range = ref []
let opt_ret_zero_missing_x64_syscalls = ref false
let opt_trace_detailed_ranges = ref []
let opt_extra_conditions = ref []
let opt_tracepoints = ref []
let opt_string_tracepoints = ref []
let opt_concrete_path = ref false
let opt_concrete_path_simulate = ref false
let opt_concolic_prob = ref None
let opt_solve_path_conditions = ref false
let opt_no_sym_regions = ref false
let opt_trace_regions = ref false
let opt_trace_struct_adaptor = ref false
let opt_trace_mem_snapshots = ref false
let opt_trace_adaptor = ref false
let opt_fragments = ref false
let opt_check_store_sequence = ref false
let opt_dont_compare_mem_se = ref false
let opt_dont_compare_syscalls = ref false
let opt_check_for_null = ref false
let opt_offset_strategy = ref UniformStrat
let opt_concretize_divisors = ref false
let opt_nonzero_divisors = ref false
let opt_trace_stopping = ref false
let opt_redirect_stderr_to_stdout = ref false
let opt_trace_setup = ref false
let opt_extra_env = Hashtbl.create 10
let opt_skip_call_addr = ref []
let opt_synth_adaptor = ref []
let opt_synth_ret_adaptor = ref []
let opt_synth_struct_adaptor = ref []
let opt_struct_adaptor_params = ref (0,0,0)
let opt_adaptor_search_mode  = ref false
let opt_adaptor_ivc = ref false
let opt_split_target_formulas = ref false
let opt_synth_simplelen_adaptor = ref []
let synth_extra_conditions = ref []
let opt_skip_func_addr = ref []
let opt_skip_call_addr_symbol = ref []
let opt_skip_func_addr_symbol = ref []
let opt_skip_call_addr_region = ref []
let opt_skip_func_addr_region = ref []
let opt_skip_call_addr_symbol_once = ref []
let opt_trace_eip = ref false
let opt_trace_unique_eips = ref false
let opt_trace_ir = ref false
let opt_trace_orig_ir = ref false
let opt_trace_iterations = ref false
let opt_trace_completed_iterations = ref false
let opt_coverage_stats = ref false
let opt_gc_stats = ref false
let opt_solver_stats = ref false
let opt_time_stats = ref false
let opt_nonfatal_solver = ref false
let opt_num_paths = ref None
let opt_pid = ref (-1)
let opt_external_uname = ref false
let opt_translation_cache_size = ref None
let opt_prefix_out = ref None
let opt_omit_pf_af = ref false
let opt_nop_system_insns = ref false
let opt_symbolic_syscall_error = ref None
let opt_stop_on_symbolic_syscall_args = ref false
let opt_skip_output_concretize = ref false
let opt_chroot_path = ref None
let opt_finish_on_nonfalse_cond = ref false
let opt_stop_on_nonfalse_cond = ref false
let opt_finish_reasons_needed = ref 1
let opt_total_timeout = ref None
let opt_x87_emulator = ref None
let opt_x87_entry_point = ref None
let opt_trace_fpu = ref false
let opt_target_region_start = ref None
let opt_target_region_string = ref ""
let opt_target_region_formula_strings = ref []
let opt_target_region_formulas = ref []
let opt_trace_target = ref false
let opt_target_no_prune = ref false
let opt_finish_on_target_match = ref false
let opt_target_guidance = ref 0.0
let opt_trace_guidance = ref false
let opt_trace_tables = ref false
let opt_table_limit = ref 0
let opt_offset_limit = ref 0
let opt_trace_offset_limit = ref false
let opt_no_table_store = ref false
let opt_max_table_store_num = ref 1000000000
let opt_tables_as_arrays = ref false
let opt_implied_value_conc = ref false
let opt_trace_ivc = ref false
let opt_ite_ivc = ref false
let opt_periodic_stats = ref None
let opt_trace_working_ce_cache = ref false
let opt_trace_global_ce_cache = ref false
let opt_global_ce_cache_limit = ref 100
let opt_disable_ce_cache = ref false
let opt_narrow_bitwidth_cutoff = ref None
let opt_t_expr_size = ref 10

let opt_symbolic_memory = ref false
let opt_zero_memory = ref false
let opt_region_limit = ref None
let opt_random_memory = ref false

let opt_fuzz_start_addr_count = ref 1
let opt_fuzz_end_addrs = ref []
let opt_trace_end_jump = ref None

let opt_check_read_operands = ref false
let opt_check_write_operands = ref false
let opt_fix_write_operands = ref false
let opt_trace_registers = ref false
let opt_trace_segments = ref false
let opt_trace_taint = ref false
let opt_trace_unexpected = ref false
let opt_progress_interval = ref None
let opt_final_pc = ref false
let opt_solve_final_pc = ref false
let opt_skip_untainted = ref false
let opt_arch = ref X86
let opt_trace_stmts = ref false
let opt_trace_eval = ref false
let opt_track_sym_usage = ref false
let opt_trace_client_reqs = ref false

let asmir_arch () =
  asmir_arch_of_execution_arch !opt_arch

let split_string char s =
  let delim_loc = String.index s char in
  let s1 = String.sub s 0 delim_loc in
  let s2 = String.sub s (delim_loc + 1) ((String.length s) - delim_loc - 1)
  in
    (s1, s2)

let add_delimited_simplelen_info opt char s = 
  let rec loop arg_str =
    try 
      let delim_loc = String.index arg_str char in
      let str1 = String.sub arg_str 0 delim_loc in
      let str2 = String.sub arg_str (delim_loc + 1) 
                   ((String.length arg_str) - delim_loc - 1) in
      [str1] @ (loop str2)
    with Not_found -> [arg_str]
  in
  let list_str = loop s in
  opt := ((Int64.of_string (List.hd list_str)),
   (Int64.of_string (List.nth list_str 1)), 
   (Int64.of_string (List.nth list_str 2)), 
   (Int64.of_string (List.nth list_str 3)), 
   (Int64.of_string (List.nth list_str 4))) :: !opt

let add_delimited_info_10 opt char s =
  let rec loop arg_str =
    try 
      let delim_loc = String.index arg_str char in
      let str1 = String.sub arg_str 0 delim_loc in
      let str2 = String.sub arg_str (delim_loc + 1) 
                   ((String.length arg_str) - delim_loc - 1) in
      [(Int64.of_string str1)] @ (loop str2)
    with Not_found -> [(Int64.of_string arg_str)]
  in
  let list_str = loop s in
  opt := ((List.nth list_str 0), (List.nth list_str 1), (List.nth list_str 2), 
	  (List.nth list_str 3), (List.nth list_str 4), (List.nth list_str 5),
	  (List.nth list_str 6), (List.nth list_str 7), (List.nth list_str 8),
	  (List.nth list_str 9))
  :: !opt
  
let add_delimited_info opt char s =
  let rec loop arg_str =
    try 
      let delim_loc = String.index arg_str char in
      let str1 = String.sub arg_str 0 delim_loc in
      let str2 = String.sub arg_str (delim_loc + 1) 
                   ((String.length arg_str) - delim_loc - 1) in
      [str1] @ (loop str2)
    with Not_found -> [arg_str]
  in
  let list_str = loop s in
  opt := ((List.hd list_str),
   (Int64.of_string (List.nth list_str 1)), 
   (Int64.of_string (List.nth list_str 2)), 
   (Int64.of_string (List.nth list_str 3)), 
   (Int64.of_string (List.nth list_str 4))) :: !opt

let add_delimited_info_4 opt char s =
  let rec loop arg_str =
    try 
      let delim_loc = String.index arg_str char in
      let str1 = String.sub arg_str 0 delim_loc in
      let str2 = String.sub arg_str (delim_loc + 1) 
                   ((String.length arg_str) - delim_loc - 1) in
      [str1] @ (loop str2)
    with Not_found -> [arg_str]
  in
  let list_str = loop s in
  opt := ((Int64.of_string (List.nth list_str 0)), 
   (Int64.of_string (List.nth list_str 1)), 
   (Int64.of_string (List.nth list_str 2)), 
   (Int64.of_string (List.nth list_str 3))) :: !opt

let add_delimited_info_s_i_i_i opt char s =
  let rec loop arg_str =
    try 
      let delim_loc = String.index arg_str char in
      let str1 = String.sub arg_str 0 delim_loc in
      let str2 = String.sub arg_str (delim_loc + 1) 
                   ((String.length arg_str) - delim_loc - 1) in
      [str1] @ (loop str2)
    with Not_found -> [arg_str]
  in
  let list_str = loop s in
  opt := ((List.nth list_str 0), 
   (Int64.of_string (List.nth list_str 1)), 
   (Int64.of_string (List.nth list_str 2)), 
   (Int64.of_string (List.nth list_str 3))) :: !opt

let add_delimited_info_3 opt char s =
  let rec loop arg_str =
    try 
      let delim_loc = String.index arg_str char in
      let str1 = String.sub arg_str 0 delim_loc in
      let str2 = String.sub arg_str (delim_loc + 1) 
        ((String.length arg_str) - delim_loc - 1) in
      [str1] @ (loop str2)
    with Not_found -> [arg_str]
  in
  let list_str = loop s in
  opt := (List.nth list_str 0, 
   (Int64.of_string (List.nth list_str 1)), 
   (Int64.of_string (List.nth list_str 2))) :: !opt

let add_delimited_pair opt char s =
  let (s1, s2) = split_string char s in
    opt := ((Int64.of_string s1), (Int64.of_string s2)) :: !opt

let add_delimited_num_str_pair opt char s =
  let (s1, s2) = split_string char s in
    opt := ((Int64.of_string s1), s2) :: !opt

let add_delimited_num_escstr_pair opt char s =
  let (s1, s2) = split_string char s in
    opt := ((Int64.of_string s1), (Exec_utils.unescaped s2)) :: !opt

let add_delimited_str_num_pair opt char s =
  let (s1, s2) = split_string char s in
    opt := (s1, (Int64.of_string s2)) :: !opt

let add_delimited_int64_int_pair opt char s= 
  let (s1, s2) = split_string char s in
    opt := ((Int64.of_string s1), (int_of_string s2)) :: !opt

let add_delimited_int_int_pair opt char s= 
  let (s1, s2) = split_string char s in
  opt := ((int_of_string s1), (int_of_string s2))

let add_delimited_int_triple opt char s= 
  let (s1, s2') = split_string char s in
  let (s2, s3) = split_string char s2' in
  opt := ((int_of_string s1), (int_of_string s2), (int_of_string s3))

let opt_program_name = ref None
let opt_start_addr = ref None
let opt_argv = ref []
let state_start_addr = ref None
