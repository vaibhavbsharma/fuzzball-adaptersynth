(*
  Copyright (C) BitBlaze, 2009-2011. All rights reserved.
*)

module V = Vine

open Exec_exceptions
open Exec_options
open Frag_simplify
open Fragment_machine
open Exec_run_common

let call_replacements fm last_eip eip =
  let (ret_reg, set_reg_conc, set_reg_sym, set_reg_fresh) =
    match !opt_arch with
    | X86 -> (R_EAX, fm#set_word_var, fm#set_word_reg_symbolic,
	      fm#set_word_reg_fresh_symbolic)
    | X64 -> (R_RAX, fm#set_long_var, fm#set_long_reg_symbolic,
	      fm#set_long_reg_fresh_symbolic)
    | ARM -> (R0, fm#set_word_var, fm#set_word_reg_symbolic,
	      fm#set_word_reg_fresh_symbolic)
  in
  let canon_eip eip =
    match !opt_arch with
      | X86 -> eip
      | X64 -> eip
      | ARM -> Int64.logand 0xfffffffeL eip (* undo Thumb encoding *)
  in
  let lookup targ l =
    List.fold_left
      (fun ret (addr, retval) -> 
	 if ((canon_eip addr) = (canon_eip targ)) then Some (retval) else ret)
      None l
  in
  let lookup_info targ l =
    List.fold_left
      (fun ret (str, addr1, val1, addr2, val2) -> 
	let addr = match !opt_arch with 
	  (* not a function of the architecture, just how we're doing things *)
	  | X64 | X86 -> addr1 
	  | ARM -> addr2
	in
	 if ((canon_eip addr) = (canon_eip targ)) then 
           Some (str,val1,addr2,val2) 
         else ret)
      None l
  in
  let lookup_simple_len_info targ l = 
    List.fold_left
      (fun ret (addr1, val1, addr2, val2, len) ->
	if ((canon_eip addr1) = (canon_eip targ)) then
	  Some (val1,addr2,val2,len) 
	else ret)
      None l
  in
  let lookup_ret_info targ l = 
    List.fold_left
      (fun ret (str, addr1, addr2, nargs) ->
	if ((canon_eip addr1) = (canon_eip targ)) || 
	  ((canon_eip addr2) = (canon_eip targ)) then
	  Some (str,addr1,addr2,nargs) 
	else ret)
      None l
  in
  let lookup_single_addr addr1 addr2 =
    if addr1 = addr2 then Some addr1 else None in
  let my_eip = match !opt_arch with
    (* not a function of the architecture, just how we're doing things *)
    | X64 | X86 -> last_eip
    | ARM -> eip
  in
    match ((lookup eip      !opt_skip_func_addr),
	   (lookup eip      !opt_skip_func_addr_symbol),
	   (lookup eip      !opt_skip_func_addr_region),
	   (lookup last_eip !opt_skip_call_addr),
	   (lookup last_eip !opt_skip_call_addr_symbol),
	   (lookup last_eip !opt_skip_call_addr_symbol_once),
	   (lookup last_eip !opt_skip_call_addr_region),
	   (lookup_info my_eip !opt_synth_adapter),
	   (lookup_ret_info eip !opt_synth_ret_adapter),
	   (lookup_simple_len_info last_eip !opt_synth_simplelen_adapter),
	   (lookup_single_addr eip !opt_repair_frag_end))
    with
      | (None, None, None, None, None, None, None, None, None, None, None) -> None
      | (Some sfa_val, None, None, None, None, None, None, None, None, None, None) ->
	  Some (fun () -> set_reg_conc ret_reg sfa_val; None)
      | (None, Some sfas_sym, None, None, None, None, None, None, None, None, None) ->
	  Some (fun () -> ignore(set_reg_fresh ret_reg sfas_sym); None)
      | (None, None, Some sfar_sym, None, None, None, None, None, None, None, None) ->
	  Some (fun () -> fm#set_reg_fresh_region ret_reg sfar_sym; None)
      | (None, None, None, Some cfa_val, None, None, None, None, None, None, None) ->
	  Some (fun () -> set_reg_conc ret_reg cfa_val; None)
      | (None, None, None, None, Some cfas_sym, None, None, None, None, None, None) ->
	  Some (fun () -> ignore(set_reg_fresh ret_reg cfas_sym); None)
      | (None, None, None, None, None, Some cfaso_sym, None, None, None, None, None) ->
	  Some (fun () -> set_reg_sym ret_reg cfaso_sym; None)
      | (None, None, None, None, None, None, Some cfar_sym, None, None, None, None) ->
	  Some (fun () -> fm#set_reg_fresh_region ret_reg cfar_sym; None)
      | (None, None, None, None, None, None, None, 
          Some (adapter_mode,out_nargs,in_addr,in_nargs), None, None, None) ->
          (*** simple adapter ***)
          if adapter_mode = "simple" 
          then Some (fun () -> 
	    Adapter_synthesis.simple_adapter fm out_nargs in_nargs;
	    fm#conc_mem_struct_adapter false;
	    fm#sym_region_struct_adapter;
            (Some in_addr))
	  else if adapter_mode = "typeconv"
	  then Some (fun () -> 
	    Adapter_synthesis.typeconv_adapter fm out_nargs in_nargs;
	    fm#conc_mem_struct_adapter false;
	    fm#sym_region_struct_adapter;
	    (*Adapter_synthesis.float_typeconv_adapter fm out_nargs in_nargs;*)
            (Some in_addr))
	  (*** adapter using trees of arithmetic (integer) expressions ***)
          else if adapter_mode = "arithmetic_int" 
            then Some (fun () -> 
              Adapter_synthesis.arithmetic_int_adapter fm out_nargs in_nargs;
	      Adapter_synthesis.struct_adapter fm;
              (Some in_addr))
          (*** adapter using trees of arithmetic (SSE floating point) expressions ***)
          else if adapter_mode = "arithmetic_float" 
            then Some (fun () -> 
              Adapter_synthesis.arithmetic_float_adapter fm out_nargs in_nargs;
	      Adapter_synthesis.struct_adapter fm;
              (Some in_addr))
          (*** character translation adapter ***)
          else if adapter_mode = "chartrans"
	  then Some (fun () ->
	    Printf.printf "running adapter chartrans\n";
	    let map_n fn n =
	      let l = ref [] in
	      for i = (n-1) downto 0 do
		l := (fn i) :: !l
	      done;
	      !l
	    in
	    let get_adapter_var index = 
              let var_name = "tableX" ^ (Printf.sprintf "%02x" index) in
              fm#get_fresh_symbolic var_name 8
	    in
	    let table = map_n (fun i -> get_adapter_var i) 256
	    in
	    Printf.printf "table length = %d\n" (List.length table);
	    let rec translate_bytes base_addr index =
              if index >= 0L then
                let byte_symb = fm#load_byte_symbolic (Int64.add base_addr index) in
                let byte_expr = fm#make_table_lookup table byte_symb 8 V.REG_8 in
                fm#store_byte_symbolic (Int64.add base_addr index) 
		  (V.BinOp(V.PLUS, byte_symb, byte_expr));
                translate_bytes base_addr (Int64.pred index)
            in
            (* Assuming we are running on X86_64 *)
            let base_addr = fm#get_long_var R_RDI in
            translate_bytes base_addr (Int64.pred in_nargs);
	    (Some in_addr))
            (*** other adapters ***)
          else if adapter_mode = "string" 
          then Some (fun () ->
            Printf.printf "string adapter not supported yet";
            (Some in_addr))
	  else Some (fun () ->
            Printf.printf "unsupported adapter";
            (Some in_addr))
      | (None, None, None, None, None, None, None, None, 
          Some (adapter_mode, addr1, addr2, in_nargs), None, None) ->
	if (adapter_mode = "return-typeconv") && addr2 = eip then (
          Some (fun () ->
	    Printf.printf "addr2 = 0x%Lx, eip = 0x%Lx\n" addr2 eip;
	    flush(stdout);
	    Adapter_synthesis.ret_typeconv_adapter fm in_nargs;
            (Some addr2))
	)
	else if (adapter_mode = "return-typeconv") && addr1 = eip then
        Some (fun () -> 
	  if !opt_trace_adapter then
	    Printf.printf "exec_runloop#thunk() should save arg regs here\n";
	  fm#save_args in_nargs;
          (Some addr1))
	else if (adapter_mode = "return-simple+len") && addr2 = eip then
          Some (fun () ->
		  Adapter_synthesis.ret_simplelen_adapter fm in_nargs;
		  (Some addr2))
	else if (adapter_mode = "return-simple+len") && addr1 = eip then
          Some (fun () ->
		  fm#save_args in_nargs;
		  (Some addr1))
	else Some (fun () ->
          Printf.printf "unsupported adapter\n";
          (Some eip))
      | (None, None, None, None, None, None, None, None, None,
	 Some (out_nargs, in_addr, in_nargs, max_depth), None) ->
	  (* an adapter that tries permutations of arguments as well as 
	     permutations of length of other arguments
	     var_type is used as follows:
	     1: a constant value in var_val is used
	     0: the argument corresponding to var_val is plugged in
	     any other value: the length of the argument corresponding 
	     to var_val is plugged in*)
         Some (fun () -> 
	   Printf.printf "Running simple+len adapter in call_replacements\n";
	   (* Assuming we are running on X86_64 *)
           let arg_regs = [R_RDI;R_RSI;R_RDX;R_RCX;R_R8;R_R9] in
	   (*let lower_bound = 0L in
	     let upper_bound = (Int64.sub (Int64.shift_left 1L 31) 1L) in*)
           let get_ite_expr if_arg if_op if_const_type if_const 
               then_val else_val = 
             V.Ite(
               V.BinOp(if_op,if_arg,V.Constant(V.Int(if_const_type, if_const))),
               then_val,
               else_val)
           in
           let rec get_ite_arg_expr arg_val n_arg =
             if n_arg <> 1L then
               get_ite_expr arg_val V.EQ V.REG_64 (Int64.sub n_arg 1L) 
                 (fm#get_reg_symbolic 
                    (List.nth arg_regs ((Int64.to_int n_arg)-1)))
                 (get_ite_arg_expr arg_val (Int64.sub n_arg 1L))
             else
               (fm#get_reg_symbolic (List.nth arg_regs 0))
           in
	   let rec get_len_expr n_arg pos =
	     let base_addr = fm#get_long_var 
	       (List.nth arg_regs (Int64.to_int n_arg)) in
             (*Printf.printf 
e       "get_len_expr n_arg = %Lx pos = %Ld base_addr = %Lx\n" 
		n_arg pos base_addr;*)
	     let b = (fm#load_byte_symbolic (Int64.add base_addr pos)) in
	     if pos < max_depth then
	       get_ite_expr b V.EQ V.REG_8 0L 
		 (V.Constant(V.Int(V.REG_64,0L)))
		 (V.BinOp(V.PLUS,V.Constant(V.Int(V.REG_64,1L)),
			  (get_len_expr n_arg (Int64.succ pos))))
	     else
	       get_ite_expr b V.EQ V.REG_8 0L
		 (V.Constant(V.Int(V.REG_64,0L)))
		 (V.Constant(V.Int(V.REG_64,1L)))
	   in
	   let rec get_ite_len_expr arg_val n_arg =
	     if n_arg <> 1L then
	       get_ite_expr arg_val V.EQ V.REG_64 (Int64.sub n_arg 1L)
		 (get_len_expr (Int64.sub n_arg 1L) 0L)
		 (get_ite_len_expr arg_val (Int64.sub n_arg 1L))
	     else 
		(get_len_expr 0L 0L)
	   in
	   (*let restrict_range node_type node_val lower upper =
             V.BinOp(
             V.BITOR,
             V.BinOp(V.NEQ, node_type, V.Constant(V.Int(V.REG_8, 1L))),
             V.BinOp(
             V.BITAND, 
             V.UnOp(V.NOT, 
             V.BinOp(V.LT, node_val, V.Constant(V.Int(V.REG_64, lower)))),
             V.BinOp(V.LE, node_val, V.Constant(V.Int(V.REG_64, upper)))))
	     in*)
           let symbolic_args = ref [] in
	   let rec loop n =
             let var_name = String.make 1 (Char.chr ((Char.code 'a') + n)) in
	     (*Printf.printf "loop var_name = %s\n" var_name;*)
             let var_type = 
               fm#get_fresh_symbolic (var_name^"_type") 8 in
             let var_val = fm#get_fresh_symbolic (var_name^"_val") 64 in
             let arg = get_ite_expr var_type V.EQ V.REG_8 1L var_val 
	       (get_ite_expr var_type V.EQ V.REG_8 0L (get_ite_arg_expr var_val out_nargs)
		  (get_ite_len_expr var_val out_nargs)) in
	     (*Printf.printf "call_replacements thunk() exp=%s\n" (V.exp_to_string arg);*)
             fm#add_to_path_cond
               (V.BinOp(
                 V.BITOR,
                 V.BinOp(V.EQ,var_type,V.Constant(V.Int(V.REG_8,1L))),
                 V.BinOp(V.LT,var_val,V.Constant(V.Int(V.REG_64,out_nargs))))
	       (*:: (restrict_range var_type var_val lower_bound upper_bound)*)
               );
	     symbolic_args := arg :: !symbolic_args;
             if n > 0 then loop (n-1); 
           in
           loop ((Int64.to_int in_nargs)-1);
	   (*Printf.printf "symbolic_args length=%d\n" (List.length !symbolic_args);*)
	   List.iteri (fun index expr ->
	     fm#set_reg_symbolic (List.nth arg_regs index) expr;) !symbolic_args;
	   let rec decision_loop n = 
             let var_name = String.make 1 (Char.chr ((Char.code 'a') + n)) in
	     (*Printf.printf "decision_loop var_name = %s\n" var_name;*)
             let var_type = 
               fm#get_fresh_symbolic (var_name^"_type") 8 in
	     let (b1,_) = fm#query_condition (V.BinOp(
	       V.BITAND,
	       V.BinOp(V.NEQ,var_type,V.Constant(V.Int(V.REG_8,0L))),
	       V.BinOp(V.NEQ,var_type,V.Constant(V.Int(V.REG_8,1L))))) None (0x6c00+n*10+1) in
	     (*Printf.printf "Chose b1 = %B\n" b1;*)
	     if b1 <> true then
	       ((*let b2 = *)
		 ignore(fm#query_condition (
		 V.BinOp(V.NEQ,var_type,V.Constant(V.Int(V.REG_8,1L)))) None (0x6c00+n*10))
		(*in
		  Printf.printf "Chose b2 = %B\n" b2;*));
	     if n > 0 then decision_loop (n-1);
	   in
	   decision_loop ((Int64.to_int in_nargs)-1);
	   Adapter_synthesis.struct_adapter fm;
           (Some in_addr))
      | (None, None, None, None, None, None, None, None, None, None, Some addr) ->
	 (* Reached end of target fragment to be repaired *)
	 let (_, num_total_tests) = !opt_repair_tests_file in
	 let (_, num_invalid_total_tests) = !opt_invalid_repair_tests_file in
	 let num_invalid_tests_processed = fm#get_invalid_repair_tests_processed in
	 (* We should have at least one counterexample and zero or more invalid 
	    tests in adapter search mode. Otherwise, the number of counterexamples
	    and invalid tests should equal zero. *)
	 assert(((not !opt_verify_adapter || not !opt_adapter_search_mode)
		 && (num_total_tests = 0) && (num_invalid_total_tests = 0))
		|| (!opt_adapter_search_mode && (num_total_tests > 0 && num_invalid_total_tests >= 0))); 
	 if !opt_trace_repair then (
	   Printf.printf "repair: %d of %d tests processed, %d of %d invalid tests processed\n"
	     fm#get_repair_tests_processed num_total_tests num_invalid_tests_processed num_invalid_total_tests;
	   flush(stdout););
	 if (fm#get_in_f1_range ()) then Some (fun () ->
	   if !opt_trace_repair then (
	     Printf.printf "repair: jumping to repair-frag-start\n";
	     flush(stdout););
           (Some !opt_repair_frag_start))
	 else (
	   assert (fm#get_in_f2_range ());
	   if fm#get_repair_tests_processed >= num_total_tests then (
	     ignore(fm#inc_invalid_repair_tests_processed);)
	   else ignore(fm#inc_repair_tests_processed);
	   if fm#get_repair_tests_processed < num_total_tests ||
	     fm#get_invalid_repair_tests_processed < num_invalid_total_tests then Some (fun () -> 
	     if !opt_trace_repair then (
	       Printf.printf "repair: %d of %d tests processed, %d of %d invalid tests processed, jumping to repair-frag-start\n"
		 fm#get_repair_tests_processed num_total_tests num_invalid_tests_processed num_invalid_total_tests;
	       flush(stdout););
             (Some !opt_repair_frag_start))
	   else Some (fun () -> (); (Some eip)));
      | _ -> 
	Printf.printf "eip = 0x%Lx\n" eip;
	failwith "Contradictory replacement options"

let loop_detect = Hashtbl.create 1000
let f2_loop_detect = Hashtbl.create 1000

let decode_insn_at fm gamma eipT =
  try
    let insn_addr = match !opt_arch with
      | ARM ->
	  (* For a Thumb instruction, change the last bit to zero to
	     find the real instruction address *)
	  if Int64.logand eipT 1L = 1L then
	    Int64.logand eipT (Int64.lognot 1L)
	  else
	    eipT
      | _ -> eipT
    in
    (* The number of bytes read must be long enough to cover any
       single instruction. Naively you might think that 16 bytes
       would be enough, but Valgrind client requests count as single
       instructions for VEX, and they can be up to 19 bytes on
       x86-64 and 20 bytes on ARM. *)
    let bytes = Array.init 20
      (fun i -> Char.chr (fm#load_byte_conc
			    (Int64.add insn_addr (Int64.of_int i))))
    in
    let prog = decode_insn gamma eipT bytes in
      prog
  with
      NotConcrete(_) ->
	Printf.printf "Jump to symbolic memory 0x%08Lx\n" eipT;
	raise IllegalInstruction

let rec last l =
  match l with
    | [e] -> e
    | a :: r -> last r
    | [] -> failwith "Empty list in last"

let rec decode_insns fm gamma eip k first =
  if k = 0 then ([], []) else
    let (dl, sl) = decode_insn_at fm gamma eip in
      if
	List.exists (function V.Special("int 0x80") -> true | _ -> false) sl
      then
	(* Make a system call be alone in its basic block *)
	if first then (dl, sl) else ([], [])
      else
	match last (rm_unused_stmts sl) with
	  | V.Jmp(V.Name(lab)) when lab <> "pc_0x0" ->
	      let next_eip = label_to_eip lab in
	      let (dl', sl') = decode_insns fm gamma next_eip (k - 1) false in
		(dl @ dl', sl @ sl')
	  | _ -> (dl, sl) (* end of basic block, e.g. indirect jump *)

let bb_size = 1

let decode_insns_cached fm gamma eip =
  with_trans_cache eip (fun () -> decode_insns fm gamma eip bb_size true)

let rec runloop (fm : fragment_machine) eip asmir_gamma until =
  let rec loop last_eip eip is_final_loop num_insns_executed =
    let is_too_many_iterations loop_detect eip f2_only =
      let old_count =
	(try
	   Hashtbl.find loop_detect eip
	 with Not_found ->
	   Hashtbl.replace loop_detect eip 1L;
	   1L)
      in
      if f2_only && (fm#get_in_f2_range ()) then (
	Hashtbl.replace loop_detect eip (Int64.succ old_count);
      );
      if not f2_only then
	Hashtbl.replace loop_detect eip (Int64.succ old_count);
      let it_lim_enforced =
	if f2_only then opt_f2_iteration_limit_enforced
	else opt_iteration_limit_enforced
      in
      (match !it_lim_enforced with
      | Some lim -> if old_count > lim then (
	raise TooManyIterations;);
      | _ -> ())
    in
    is_too_many_iterations loop_detect eip false;
    is_too_many_iterations f2_loop_detect eip true;
    if ((fm#get_in_f2_range () = false) &&
      ((Hashtbl.length f2_loop_detect) <> 0)) then
      (Hashtbl.clear f2_loop_detect;);
    let (dl, sl) = decode_insns_cached fm asmir_gamma eip in
    let prog = (dl, sl) in
    let nargs = ref 0L in
    let match_adapter_eip call_eip =
      let adapter_eip_var = fm#get_fresh_symbolic "repair_EIP" 64 in
      let cond = V.BinOp(V.EQ, adapter_eip_var, V.Constant(V.Int(V.REG_64, call_eip))) in
      let get_constant_val const_exp =
	match const_exp with
	| V.Constant(V.Int(V.REG_64, value)) -> value
	| _ -> failwith "unexpected expression provided to get_constant_val"
      in
      if not !opt_adapter_search_mode then (
	(get_constant_val (Hashtbl.find Adapter_vars.adapter_vals "repair_EIP")) = call_eip)
      else (
	let (b,_) = (fm#query_condition cond (Some true) 0x6cff) in
	if b = true then (
	  if !opt_trace_repair then
	    Printf.printf "repair: setting repair_EIP to 0x%08Lx\n" call_eip; flush(stdout);
	  true
	) else (
	  if !opt_trace_repair then
	    Printf.printf "repair: not setting repair_EIP to 0x%08Lx\n" call_eip; flush(stdout);
	  false
	))
    in
    if (is_adapted_target_call_insn fm sl)
	&& ((eip = !opt_apply_call_repair_adapter_at) || (match_adapter_eip eip)) then (
      if !opt_trace_adapter || !opt_trace_repair then (
	Printf.printf "repair: applying simple repair adapter at eip=0x%Lx\n" eip;
	flush(stdout););
      match !opt_synth_repair_adapter with
      | Some (adapter_name, _nargs) when adapter_name = "simple" ->
	 nargs := _nargs;
	 Adapter_synthesis.simple_adapter fm !nargs !nargs;
      (* if !opt_synth_repair_ret_adapter <> None then (fm#save_args !nargs); *)
      | _ -> failwith "unsupported repair adapter"
    );
    if eip = !opt_repair_frag_end && fm#get_in_f2_range ()
    && !opt_synth_repair_ret_adapter <> None then (
      (* turning off return adapter that also tries to plug in an argument as the return value *)
      match !opt_synth_repair_ret_adapter with
      | Some (_, nargs) when nargs = 0L -> 
	 Adapter_synthesis.ret_typeconv_adapter fm 0L;
      | _ -> failwith "non-zero argument to retvalsub adapter not supported in repair mode"
    );
      let prog' = match call_replacements fm last_eip eip with
	| None -> prog
	| Some thunk ->
	  let fake_insn = match (!opt_arch, 
                                 (Int64.logand eip 1L), thunk ()) with
	    | (X86, _,None) -> [|'\xc3'|] (* ret *)
	    | (X64, _,None) -> [|'\xc3'|] (* ret *)
	    | (X86, _,Some addr)
	    | (X64, _,Some addr) ->  (* Jump to the inner function *)
	      if addr <> eip then (
		let in_addr = addr in
		let temp = (Int64.sub in_addr eip) in
		let offset = (Int64.sub temp 5L) in
		let offset_byte_0 = (Int64.logand offset 255L) in
		let offset_byte_1 = 
		  (Int64.shift_right_logical 
		     (Int64.logand offset (Int64.shift_left 255L 8)) 8) in
		let offset_byte_2 = 
		  (Int64.shift_right_logical 
		     (Int64.logand offset (Int64.shift_left 255L 16)) 16) in
		let offset_byte_3 = 
		  (Int64.shift_right_logical 
		     (Int64.logand offset (Int64.shift_left 255L 24)) 24) in
		let offset_char_arr = [|(char_of_int (Int64.to_int offset_byte_0));
					(char_of_int (Int64.to_int offset_byte_1));
					(char_of_int (Int64.to_int offset_byte_2));
					(char_of_int (Int64.to_int offset_byte_3))|] in
		(*Printf.printf "eip %Lx:jumping to adapter %Lx using offset %Lx\n" 
		  eip in_addr offset;*)
		(*Array.iter 
                  ( function ele -> Printf.printf "%Lx\n" (Int64.of_int (Char.code ele))) offset_char_arr;*)
		Array.append [|'\xe9'|] offset_char_arr)
	      else (* noop because this was a return value adapter *)
		(
		  (* Printf.printf "nooping because no call replacement required\n"; *)
		  [||]
		)
	    | (ARM, 0L,_) -> 
	      if !opt_trace_adapter then 
		Printf.printf "no adapter synth. call replacement to be done\n";
	      flush(stdout);
	      [||] (* nop *)
	      (* [|'\x1e'; '\xff'; '\x2f'; '\xe1'|] *) (* bx lr *)
	    | (ARM, 1L,_) -> [|'\x70'; '\x47'|] (* bx lr (Thumb) *)
	    | (ARM, _,_) -> failwith "Can't happen (logand with 1)"
	  in
	  if (Array.length fake_insn) <> 0 then
	    decode_insn asmir_gamma eip fake_insn
	  else prog
      in
	if !opt_trace_insns then
	  print_insns eip prog' None '\n';
	if !opt_trace_ir then
	  V.pp_program print_string prog';
	fm#set_frag prog';
	(* flush stdout; *)
	let new_eip = label_to_eip (fm#run ()) in
	  if is_final_loop then
	    Printf.printf "End jump to: %Lx\n" new_eip
	  else if num_insns_executed = !opt_insn_limit then
	    Printf.printf "Stopping after %Ld insns\n" !opt_insn_limit
	  else
	    match (new_eip, until, !opt_trace_end_jump) with
	      | (e1, e2, Some e3) when e1 = e3 ->
	          loop eip new_eip true (Int64.succ num_insns_executed)
	      | (e1, e2, _) when e2 e1 -> ()
	      | (0L, _, _) -> raise JumpToNull
	      | _ -> loop eip new_eip false (Int64.succ num_insns_executed)
    in
    Hashtbl.clear loop_detect;
    Hashtbl.clear f2_loop_detect;
    loop (0L) eip false 1L
