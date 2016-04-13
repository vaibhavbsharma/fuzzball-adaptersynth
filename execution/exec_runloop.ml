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
  let ret_reg = match !opt_arch with
    | X86 -> R_EAX
    | X64 -> R_RAX
    | ARM -> R0
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
	 if ((canon_eip addr1) = (canon_eip targ)) then 
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
    match ((lookup eip      !opt_skip_func_addr),
	   (lookup eip      !opt_skip_func_addr_symbol),
	   (lookup eip      !opt_skip_func_addr_region),
	   (lookup last_eip !opt_skip_call_addr),
	   (lookup last_eip !opt_skip_call_addr_symbol),
	   (lookup last_eip !opt_skip_call_addr_symbol_once),
	   (lookup last_eip !opt_skip_call_addr_region),
	   (lookup_info last_eip !opt_synth_adaptor),
	   (lookup_simple_len_info last_eip !opt_synth_simplelen_adaptor))
    with
      | (None, None, None, None, None, None, None, None, None) -> None
      | (Some sfa_val, None, None, None, None, None, None, None, None) ->
	  Some (fun () -> fm#set_word_var ret_reg sfa_val; None)
      | (None, Some sfas_sym, None, None, None, None, None, None, None) ->
	  Some (fun () -> fm#set_word_reg_fresh_symbolic ret_reg sfas_sym; None)
      | (None, None, Some sfar_sym, None, None, None, None, None, None) ->
	  Some (fun () -> fm#set_word_reg_fresh_region ret_reg sfar_sym; None)
      | (None, None, None, Some cfa_val, None, None, None, None, None) ->
	  Some (fun () -> fm#set_word_var ret_reg cfa_val; None)
      | (None, None, None, None, Some cfas_sym, None, None, None, None) ->
	  Some (fun () -> fm#set_word_reg_fresh_symbolic ret_reg cfas_sym; None)
      | (None, None, None, None, None, Some cfaso_sym, None, None, None) ->
	  Some (fun () -> fm#set_word_reg_symbolic ret_reg cfaso_sym; None)
      | (None, None, None, None, None, None, Some cfar_sym, None, None) ->
	  Some (fun () -> fm#set_word_reg_fresh_region ret_reg cfar_sym; None)
      | (None, None, None, None, None, None, None, 
          Some (adaptor_mode,out_nargs,in_addr,in_nargs), None) ->
          (*** simple adaptor ***)
          if adaptor_mode = "simple" 
          then Some (fun () -> 
	    Adaptor_synthesis.simple_adaptor fm out_nargs in_nargs;
            (Some in_addr))
	  (*** adaptor using trees of arithmetic (integer) expressions ***)
          else if adaptor_mode = "arithmetic_int" 
            then Some (fun () -> 
              Adaptor_synthesis.arithmetic_int_adaptor fm out_nargs in_nargs;
              (Some in_addr))
          (*** adaptor using trees of arithmetic (SSE floating point) expressions ***)
          else if adaptor_mode = "arithmetic_float" 
            then Some (fun () -> 
              Adaptor_synthesis.arithmetic_float_adaptor fm out_nargs in_nargs;
              (Some in_addr))
          (*** character translation adaptor ***)
          else if adaptor_mode = "chartrans"
	  then Some (fun () ->
	    Printf.printf "running adaptor chartrans\n";
	    let map_n fn n =
	      let l = ref [] in
	      for i = (n-1) downto 0 do
		l := (fn i) :: !l
	      done;
	      !l
	    in
	    let get_adaptor_var index = 
              let var_name = "tableX" ^ (Printf.sprintf "%02x" index) in
              fm#get_fresh_symbolic var_name 8
	    in
	    let table = map_n (fun i -> get_adaptor_var i) 256
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
            (*** other adaptors ***)
          else if adaptor_mode = "string" 
          then Some (fun () ->
            Printf.printf "string adaptor not supported yet";
            (Some in_addr))
	  else Some (fun () ->
            Printf.printf "unsupported adaptor";
            (Some in_addr))
      | (None, None, None, None, None, None, None, None, 
	 Some (out_nargs, in_addr, in_nargs, max_depth)) ->
	  (* an adaptor that tries permutations of arguments as well as 
	     permutations of length of other arguments
	     var_type is used as follows:
	     1: a constant value in var_val is used
	     0: the argument corresponding to var_val is plugged in
	     any other value: the length of the argument corresponding 
	     to var_val is plugged in*)
         Some (fun () -> 
	   (*Printf.printf "Running simple+len adaptor in call_replacements\n";*)
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
	       "get_len_expr n_arg = %Lx pos = %Ld base_addr = %Lx\n" 
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
             opt_extra_conditions :=
               V.BinOp(
                 V.BITOR,
                 V.BinOp(V.EQ,var_type,V.Constant(V.Int(V.REG_8,1L))),
                 V.BinOp(V.LT,var_val,V.Constant(V.Int(V.REG_64,out_nargs))))
	     (*:: (restrict_range var_type var_val lower_bound upper_bound)*)
             :: !opt_extra_conditions;
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
	     let b1 = fm#query_condition (V.BinOp(
	       V.BITAND,
	       V.BinOp(V.NEQ,var_type,V.Constant(V.Int(V.REG_8,0L))),
	       V.BinOp(V.NEQ,var_type,V.Constant(V.Int(V.REG_8,1L))))) (0x6c00+n*10+1) in
	     (*Printf.printf "Chose b1 = %B\n" b1;*)
	     if b1 <> true then
	       ((*let b2 = *)
		 ignore(fm#query_condition (
		 V.BinOp(V.NEQ,var_type,V.Constant(V.Int(V.REG_8,1L)))) (0x6c00+n*10))
		(*in
		  Printf.printf "Chose b2 = %B\n" b2;*));
	     if n > 0 then decision_loop (n-1);
	   in
	   decision_loop ((Int64.to_int in_nargs)-1);
           (Some in_addr))
      | _ -> failwith "Contradictory replacement options"

let loop_detect = Hashtbl.create 1000

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
    let bytes = Array.init 16
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
    (let old_count =
       (try
	  Hashtbl.find loop_detect eip
	with Not_found ->
	  Hashtbl.replace loop_detect eip 1L;
	  1L)
     in
       Hashtbl.replace loop_detect eip (Int64.succ old_count);
       if old_count > !opt_iteration_limit then raise TooManyIterations);
    let (dl, sl) = decode_insns_cached fm asmir_gamma eip in
    let prog = (dl, sl) in
      let prog' = match call_replacements fm last_eip eip with
	| None -> prog
	| Some thunk ->
	  let fake_insn = match (!opt_arch, 
                                 (Int64.logand eip 1L), thunk ()) with
	    | (X86, _,_) -> [|'\xc3'|] (* ret *)
	    | (X64, _,None) -> [|'\xc3'|] (* ret *)
	    | (X64, _,Some in_addr) ->  (* Jump to the inner function *)
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
	      Array.append [|'\xe9'|] offset_char_arr
	    | (ARM, 0L,_) -> [|'\x1e'; '\xff'; '\x2f'; '\xe1'|] (* bx lr *)
	    | (ARM, 1L,_) -> [|'\x70'; '\x47'|] (* bx lr (Thumb) *)
	    | (ARM, _,_) -> failwith "Can't happen (logand with 1)"
	  in
	  decode_insn asmir_gamma eip fake_insn
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
    loop (0L) eip false 1L
