(*
  Copyright (C) BitBlaze, 2009-2013. All rights reserved.
*)

module V = Vine;;

open Exec_domain;;
open Exec_exceptions;;
open Exec_utils;;
open Exec_options;;
open Frag_simplify;;
open Fragment_machine;;
open Sym_path_frag_machine;;
open Sym_region_frag_machine;;
open Exec_run_common;;
open Exec_runloop;;
open Exec_stats;;

let loop_w_stats count fn =
  let iter = ref 0L and
      start_wtime = Unix.gettimeofday () and
      start_ctime = Sys.time () in
    (try
       while (match count with
		| None -> true
		| Some i -> !iter < i)
       do
	 iter := Int64.add !iter 1L;
	 let old_wtime = Unix.gettimeofday () and
             old_ctime = Sys.time () and
	     is_final = ref false in
	   if !opt_trace_iterations then 
	     Printf.printf "Iteration %Ld:\n%!" !iter;
	   (try
	      fn !iter;
	    with LastIteration -> is_final := true);
	   let wtime = Unix.gettimeofday() in
	     if !opt_time_stats then
	       ((let ctime = Sys.time() in
		   Printf.printf "CPU time %f sec, %f total\n"
		     (ctime -. old_ctime) (ctime -. start_ctime));
		(Printf.printf "Wall time %f sec, %f total\n"
		   (wtime -. old_wtime) (wtime -. start_wtime)));
	     if !opt_trace_completed_iterations then
	       Printf.printf "Iteration %Ld completed\n%!" !iter;
	     flush stdout;
	     (match !opt_total_timeout with
		| None -> ()
		| Some t ->
		    if (wtime -. start_wtime) > t then
		      (Printf.printf "Total exploration time timeout.\n";
		       raise LastIteration));
	     if !is_final then raise LastIteration
       done
     with
	 LastIteration -> ());
    if !opt_gc_stats then
      Gc.full_major () (* for the benefit of leak checking *)

let fuzz start_eip opt_fuzz_start_eip end_eips
    (fm : fragment_machine) asmir_gamma symbolic_init reset_cb =
  if !opt_trace_setup then
    (Printf.printf "Initial registers:\n";
     fm#print_regs);
  (match !opt_periodic_stats with
     | Some p -> add_periodic_hook fm p
     | None -> ());
  flush stdout;
  if !opt_gc_stats then
    at_exit final_check_memory_usage;
  let fuzz_start_eip = ref opt_fuzz_start_eip
  and extra_setup = ref (fun () -> ()) in
  (try
     Sys.set_signal  Sys.sighup
       (Sys.Signal_handle(fun _ -> raise (Signal "HUP")));
     Sys.set_signal  Sys.sigint
       (Sys.Signal_handle(fun _ -> raise (Signal "INT")));
     Sys.set_signal Sys.sigterm
       (Sys.Signal_handle(fun _ -> raise (Signal "TERM")));
     Sys.set_signal Sys.sigquit
       (Sys.Signal_handle(fun _ -> raise (Signal "QUIT")));
     Sys.set_signal Sys.sigusr1
       (Sys.Signal_handle(fun _ -> raise (Signal "USR1")));
     Sys.set_signal Sys.sigusr2
       (Sys.Signal_handle(fun _ -> periodic_stats fm false true));
     (try 
	if start_eip <> opt_fuzz_start_eip then
	  (if !opt_trace_setup then Printf.printf "Pre-fuzzing execution...\n";
	   flush stdout;
	   runloop fm start_eip asmir_gamma
	     (fun a ->
		if a = opt_fuzz_start_eip then
		  (decr opt_fuzz_start_addr_count;
		   if !opt_fuzz_start_addr_count = 0 then 
		     opt_iteration_limit_enforced := Some !opt_iteration_limit;
		   !opt_fuzz_start_addr_count = 0
		  )
		else
		  false))
      with
	| StartSymbolic(eip, setup) ->
	    fuzz_start_eip := eip;
	    extra_setup := setup);
     let path_cond = fm#get_path_cond in
     if path_cond <> [] then 
       failwith ("The path condition is non-empty before fm#start_symbolic,"^
	 "you may want to re-run fuzzball with the -zero-memory option");
     fm#start_symbolic;
     
     let rec simple_loop n out_nargs type_name type_size =
       let var_name = String.make 1 (Char.chr ((Char.code 'a') + n)) in
       ignore(fm#get_fresh_symbolic (var_name^"_f_val") 64);
       ignore(fm#get_fresh_symbolic (var_name^"_f"^type_name) type_size);
       let var_val = fm#get_fresh_symbolic (var_name^"_val") 64 in
       let var_type = fm#get_fresh_symbolic (var_name^type_name) type_size in
       (*ignore(fm#get_fresh_symbolic (var_name^"_val") 64);*)
       (*ignore(fm#get_fresh_symbolic (var_name^type_name) type_size);*)
       let var_type_type = 
	 if type_size = 1 then V.REG_1 
	 else if type_size = 8 then V.REG_8
	 else failwith "unsupported type_size in exec_fuzzloop#simple_loop"
       in
       let tmp_cond = 
	 (if out_nargs > 0L then 
	   V.BinOp(
	     V.BITOR,
	     V.BinOp(V.EQ,var_type,V.Constant(V.Int(var_type_type,1L))),
	     V.BinOp(V.LT,var_val,V.Constant(V.Int(V.REG_64,out_nargs))))
	 else (
           V.BinOp(V.EQ,var_type,V.Constant(V.Int(var_type_type,1L)))
	 )) in
       opt_extra_conditions := tmp_cond :: !opt_extra_conditions;
       (*Printf.printf "opt_extra_condition.length = %d n=%d out_nargs=%Lx tmp_cond = %s\n" 
	 (List.length !opt_extra_conditions) n out_nargs (V.exp_to_string tmp_cond);*)
       if n > 0 then simple_loop (n-1) out_nargs type_name type_size; 
     in
     let _ = (if (List.length !opt_synth_simplelen_adaptor) <> 0 then
      (let (_,out_nargs,_,in_nargs,_) = List.hd !opt_synth_simplelen_adaptor in
      simple_loop ((Int64.to_int in_nargs)-1) out_nargs "_type" 8)) 
     in
     (if ((List.length !opt_synth_adaptor) <> 0) then
	 let (mode, _, out_nargs, _, in_nargs) = List.hd !opt_synth_adaptor in 
       let rec chartrans_loop n = 
	 let var_name = "tableX" ^ (Printf.sprintf "%02x" n) in
	 ignore(fm#get_fresh_symbolic var_name 8);
	 if n > -1 then chartrans_loop (n-1); in
       if mode = "simple" 
       then simple_loop ((Int64.to_int in_nargs)-1) out_nargs "_is_const" 1
       else if mode = "typeconv"
       then simple_loop ((Int64.to_int in_nargs)-1) out_nargs "_type" 8
       else if (mode = "arithmetic_int")   
       then (
	 if (in_nargs <> 0L) then
	   Adaptor_synthesis.arithmetic_int_extra_conditions
	     fm out_nargs ((Int64.to_int in_nargs)-1);)
       else if mode = "arithmetic_float"
       then Adaptor_synthesis.arithmetic_float_extra_conditions
         fm out_nargs ((Int64.to_int in_nargs)-1)
       else if mode = "chartrans"
       then chartrans_loop 255
       else (Printf.printf "Unsupported adaptor mode\n"; flush stdout));
     
     let (_, i_n_fields, _) = !opt_struct_adaptor_params in 
     for i = 1 to i_n_fields do
       ignore(fm#get_fresh_symbolic (Printf.sprintf "m%d_arith" i) 64);
       ignore(fm#get_fresh_symbolic (Printf.sprintf "c%d_arith" i) 64);
       let field_size_str = Printf.sprintf "f%d_size" i in
       let field_n_str = Printf.sprintf "f%d_n" i in
       let field_n = fm#get_fresh_symbolic field_n_str 16 in
       let field_sz_sym = fm#get_fresh_symbolic field_size_str 16 in
       let tmp_cond = (* f1_size == (1 || 2 || 4 || 8) *)
	 V.BinOp(V.BITOR, 
		 V.BinOp(V.EQ,field_sz_sym,V.Constant(V.Int(V.REG_16,1L))),
		 V.BinOp(V.BITOR,
			 V.BinOp(V.EQ,field_sz_sym,V.Constant(V.Int(V.REG_16,2L))),
			 V.BinOp(V.BITOR,
				 V.BinOp(V.EQ,field_sz_sym,V.Constant(V.Int(V.REG_16,4L))),
				 V.BinOp(V.EQ,field_sz_sym,V.Constant(V.Int(V.REG_16,8L)
				 )))))
       in
       opt_extra_conditions := tmp_cond :: !opt_extra_conditions;
       let f_type_str = Printf.sprintf "f%d_type" i in
       (* this target field cannot overlap with another target field
	  this means that two inner fields cannot be mapped to the same target
	  field (sorry twins!) *)
       let f_type_sym = fm#get_fresh_symbolic f_type_str 64 in
       let i_start_b = V.BinOp(V.RSHIFT, f_type_sym, 
			       V.Constant(V.Int(V.REG_8, 32L))) in
       let i_end_b = V.BinOp(
	 V.BITAND, 
	 V.Constant(V.Int(V.REG_64, 65535L)), 
	 V.BinOp(V.RSHIFT, f_type_sym, 
		 V.Constant(V.Int(V.REG_8, 16L)))) in
       for j=1 to i_n_fields do
	 if i <> j then (
	   let f2_type_sym = fm#get_fresh_symbolic (Printf.sprintf "f%d_type" j) 64 in
	   let j_start_b = V.BinOp(V.RSHIFT, f2_type_sym, 
				   V.Constant(V.Int(V.REG_8, 32L))) in
	   let j_end_b = V.BinOp(
	     V.BITAND, V.Constant(V.Int(V.REG_64, 65535L)), 
	     V.BinOp(V.RSHIFT, f2_type_sym, 
		     V.Constant(V.Int(V.REG_8, 16L)))) in
	   let expr_s_b = V.BinOp(V.BITAND, 
				  V.BinOp(V.LE, j_start_b, i_start_b), 
				  V.BinOp(V.LE, i_start_b, j_end_b  )) in
	   let expr_e_b = V.BinOp(V.BITAND, 
				  V.BinOp(V.LE, j_start_b, i_end_b), 
				  V.BinOp(V.LE, i_end_b,   j_end_b)) in
	   let tmp_cond2 = V.UnOp(V.NOT, V.BinOp(V.BITOR, expr_s_b, expr_e_b)) in
	   Printf.printf "exec_fuzzloop adding tmp_cond2 = %s\n"
	     (V.exp_to_string tmp_cond2);
	   opt_extra_conditions := tmp_cond2 :: !opt_extra_conditions; 
	 );
       done; (* end for j *)
      
       (* end_byte must be >= start_byte *)
       opt_extra_conditions := V.BinOp(V.LE, i_start_b, i_end_b) :: !opt_extra_conditions;
      
	(*  i_end_b - i_start_b + 1 should be divisible by field_n *) 
       let i_bytes = V.BinOp(V.MINUS, 
			     V.BinOp(
			       V.PLUS, i_end_b, V.Constant(V.Int(V.REG_64, 1L))),
			     i_start_b) in
       let tmp_cond3 = V.BinOp(V.EQ, 
			       V.BinOp(V.MOD, i_bytes, 
				       V.Cast(V.CAST_UNSIGNED, V.REG_64, field_n)), 
			       V.Constant(V.Int(V.REG_64, 0L))) in
       Printf.printf "exec_fuzzloop adding tmp_cond3 = %s\n"
	 (V.exp_to_string tmp_cond3);
       opt_extra_conditions := tmp_cond3 :: !opt_extra_conditions; 
       
       (* (end_byte-start_byte+1)/n == 1, 2, 4, or 8 *)
       let size_cond1 = V.BinOp(V.EQ, V.Constant(V.Int(V.REG_64, 1L)), 
				       V.BinOp(V.DIVIDE, i_bytes, 
					       V.Cast(
						 V.CAST_UNSIGNED, V.REG_64, field_n))) in
       let size_cond2 = V.BinOp(V.EQ, V.Constant(V.Int(V.REG_64, 2L)), 
				       V.BinOp(V.DIVIDE, i_bytes, 
					       V.Cast(
						 V.CAST_UNSIGNED, V.REG_64, field_n))) in
       let size_cond3 = V.BinOp(V.EQ, V.Constant(V.Int(V.REG_64, 4L)), 
				       V.BinOp(V.DIVIDE, i_bytes, 
					       V.Cast(
						 V.CAST_UNSIGNED, V.REG_64, field_n))) in 
       let size_cond4 = V.BinOp(V.EQ, V.Constant(V.Int(V.REG_64, 8L)), 
				       V.BinOp(V.DIVIDE, i_bytes, 
					       V.Cast(
						 V.CAST_UNSIGNED, V.REG_64, field_n))) in
       opt_extra_conditions := V.BinOp(V.BITOR, size_cond1, 
					       V.BinOp(V.BITOR, size_cond2, 
						       V.BinOp(V.BITOR, size_cond3, size_cond4)))
       :: !opt_extra_conditions;
      
     done; (* end for i *)
     
     if (List.length !opt_synth_ret_adaptor) <> 0 then (
       let (_, _, _, in_nargs) = List.hd !opt_synth_ret_adaptor in
       let var_type = (fm#get_fresh_symbolic ("ret_type") 8) in
       let var_val = (fm#get_fresh_symbolic ("ret_val") 64) in
       if in_nargs > 0L then
	 ( let tmp_cond = 
	     V.BinOp(
	       V.BITOR,
	       V.BinOp(V.EQ,var_type,V.Constant(V.Int(V.REG_8,1L))),
	       V.BinOp(V.LT,var_val,V.Constant(V.Int(V.REG_64,in_nargs)))) in
	   opt_extra_conditions := tmp_cond :: !opt_extra_conditions;
	 (*Printf.printf "opt_extra_condition.length = %d in_nargs=%Lx tmp_cond = %s\n" 
	   (List.length !opt_extra_conditions) in_nargs (V.exp_to_string tmp_cond);*)
	 );
     );

     if !opt_trace_setup then
       (Printf.printf "Setting up symbolic values:\n"; flush stdout);
     symbolic_init ();
     !extra_setup ();
     fm#make_snap ();
     if !opt_trace_setup then
       (Printf.printf "Took snapshot\n"; flush stdout);

     (* Populate hashtable of adaptor vars *)
     let _ =
       if !opt_trace_struct_adaptor then
	 Printf.printf "adaptor_vals: Iterating through %d extra conditions\n" 
	   (List.length !opt_extra_conditions);
       List.iter ( fun cond ->
	 (match cond with
	 | V.BinOp(V.EQ,V.Lval(V.Temp((_, s, _))),
		   V.Constant(V.Int(ty,value))) 
	 | V.BinOp(V.EQ,V.Constant(V.Int(ty,value)),
		   V.Lval(V.Temp((_, s, _)))) ->
	   if !opt_trace_struct_adaptor then (
	     if Hashtbl.mem Adaptor_synthesis.adaptor_vals s then 
	       Printf.printf "adaptor_vals already had value for %s, panic!\n" s
	     else Printf.printf "adding %s to adaptor_vals\n" s;);
	   Hashtbl.replace Adaptor_synthesis.adaptor_vals s
	     (V.Constant(V.Int(ty,value)))
	 | _ -> ());
       ) !opt_extra_conditions; 
     in
     if i_n_fields <> 0 then 
       Adaptor_synthesis.create_field_ranges_l fm ;
     let field_ranges = Adaptor_synthesis.ranges_by_field_num in
     let ranges = ref [] in
     for i = 1 to i_n_fields do
       ranges := !ranges @ !((!field_ranges).(i));
     done;
     for i = 1 to i_n_fields do
       let f_type_str = Printf.sprintf "f%d_type" i in
       let f_type_sym = fm#get_fresh_symbolic f_type_str 64 in
       (* f_type should equal only one of the valid values *)
       let constify a = V.Constant(V.Int(V.REG_64, a)) in
       let or_list l = 
	 match l with 
	 | [] -> constify 0L
	 | [a] -> constify a
	 | e :: r -> List.fold_left (
	   fun a b -> V.BinOp(V.BITOR, a, 
			      (V.BinOp(V.EQ, f_type_sym, (constify b))))
	 ) (V.BinOp(V.EQ, f_type_sym, (constify e))) r
       in
       let this_cond = (or_list !ranges) in
       Printf.printf "list of valid values = %s\n" (V.exp_to_string this_cond);
       opt_extra_conditions := this_cond :: !opt_extra_conditions;
     done;

     (try
	loop_w_stats !opt_num_paths
	  (fun iter ->
	     let old_tcs = Hashtbl.length trans_cache in
	     let stop str = if !opt_trace_stopping then
	       let stop_eip = fm#get_eip in
	         Printf.printf "Stopping %s at 0x%08Lx\n" str stop_eip
	     in
	       fm#set_iter_seed (Int64.to_int iter);
	       (try
		  runloop fm !fuzz_start_eip asmir_gamma
		    (fun a -> List.mem a end_eips);
		with
		  | SimulatedExit(_) -> stop "when program called exit()"
		  | SimulatedAbort -> stop "when program called abort()"
		  | KnownPath -> stop "on previously-explored path"
		      (* KnownPath currently shouldn't happen *)
		  | DeepPath -> stop "on too-deep path"
		  | SymbolicJump -> stop "at symbolic jump"
		  | NullDereference -> stop "at null deref"
		  | UnsupportedAddress -> stop "at access to unsupported address"
		  | JumpToNull -> stop "at jump to null"
		  | DivideByZero -> stop "at division by zero"
		  | TooManyIterations -> stop "after too many loop iterations"
		  | UnhandledTrap -> stop "at trap"
		  | IllegalInstruction -> stop "at bad instruction"
		  | UnhandledSysCall(s) ->
		      Printf.printf "[trans_eval WARNING]: %s\n%!" s;
		      stop "at unhandled system call"
		  | SymbolicSyscall -> stop "at symbolic system call"
		  | ReachedMeasurePoint -> stop "at measurement point"
		  | ReachedInfluenceBound -> stop "at influence bound"
		  | DisqualifiedPath -> stop "on disqualified path"
		  | BranchLimit -> stop "on branch limit"
		  | SolverFailure when !opt_nonfatal_solver
		      -> stop "on solver failure"
		  | UnproductivePath -> stop "on unproductive path"
		  | Signal("USR1") -> stop "on SIGUSR1"
		  (* | NotConcrete(_) -> () (* shouldn't happen *)
		     | Simplify_failure(_) -> () (* shouldn't happen *)*)
	       );
	       if (List.length !opt_match_syscalls_addr_range) <> 0 then
		 if ((fm#match_syscalls ()) <> true)  ||
		   ( ((fm#match_writes ()) <> true) && 
		       (!opt_dont_compare_mem_se = false))
		 then
		   ((* too late to raise DisqualifiedPath *)
		   let stop_eip = fm#get_eip in
		   Printf.printf "Disqualified path at 0x%08Lx\n" stop_eip;);
	       if (List.length !opt_synth_struct_adaptor) <> 0 then
		 fm#reset_struct_counts;
	       if (List.length !opt_match_syscalls_addr_range) <> 0 then
		 fm#reset_syscalls ;
	       if (List.length !opt_synth_ret_adaptor) <> 0 then
		 fm#reset_saved_arg_regs ;
	       if !opt_coverage_stats && 
		 (Hashtbl.length trans_cache - old_tcs > 0) then
		   Printf.printf "Coverage increased to %d on %Ld\n"
		     (Hashtbl.length trans_cache) iter;
	       periodic_stats fm false false;
	       if not fm#finish_path then raise LastIteration;
	       if !opt_concrete_path then raise LastIteration;
	       (match fm#finish_reasons with
		  | (s :: rest) as l
		      when (List.length l) >= !opt_finish_reasons_needed
			->
		      if !opt_trace_stopping then
			Printf.printf "Finished, %s\n"
			  (String.concat ", " l);
		      raise LastIteration
		  | _ -> ());
	       if !opt_concrete_path_simulate then
		 opt_concrete_path_simulate := false; (* First iter. only *)
	       reset_cb ();
	       fm#reset ()
	  );
      with
	| LastIteration -> ()
	| Signal("QUIT") -> Printf.printf "Caught SIGQUIT\n");
     fm#after_exploration
   with
     | LastIteration -> ()
     | Signal(("INT"|"HUP"|"TERM") as s) -> Printf.printf "Caught SIG%s\n" s
    (*
     | e -> Printf.printf "Caught fatal error %s\n" (Printexc.to_string e);
	 Printexc.print_backtrace stderr *) );
  if !opt_coverage_stats then
    Printf.printf "Final coverage: %d\n"
      (Hashtbl.length trans_cache);
  periodic_stats fm true false
