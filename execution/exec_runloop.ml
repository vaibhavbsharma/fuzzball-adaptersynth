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
    match ((lookup eip      !opt_skip_func_addr),
	   (lookup eip      !opt_skip_func_addr_symbol),
	   (lookup eip      !opt_skip_func_addr_region),
	   (lookup last_eip !opt_skip_call_addr),
	   (lookup last_eip !opt_skip_call_addr_symbol),
	   (lookup last_eip !opt_skip_call_addr_symbol_once),
	   (lookup last_eip !opt_skip_call_addr_region),
	   (lookup_info last_eip !opt_synth_adaptor))
    with
      | (None, None, None, None, None, None, None, None) -> None
      | (Some sfa_val, None, None, None, None, None, None, None) ->
	  Some (fun () -> fm#set_word_var ret_reg sfa_val; None)
      | (None, Some sfas_sym, None, None, None, None, None, None) ->
	  Some (fun () -> fm#set_word_reg_fresh_symbolic ret_reg sfas_sym; None)
      | (None, None, Some sfar_sym, None, None, None, None, None) ->
	  Some (fun () -> fm#set_word_reg_fresh_region ret_reg sfar_sym; None)
      | (None, None, None, Some cfa_val, None, None, None, None) ->
	  Some (fun () -> fm#set_word_var ret_reg cfa_val; None)
      | (None, None, None, None, Some cfas_sym, None, None, None) ->
	  Some (fun () -> fm#set_word_reg_fresh_symbolic ret_reg cfas_sym; None)
      | (None, None, None, None, None, Some cfaso_sym, None, None) ->
	  Some (fun () -> fm#set_word_reg_symbolic ret_reg cfaso_sym; None)
      | (None, None, None, None, None, None, Some cfar_sym, None) ->
	  Some (fun () -> fm#set_word_reg_fresh_region ret_reg cfar_sym; None)
      | (None, None, None, None, None, None, None, 
          Some (adaptor_mode,out_nargs,in_addr,in_nargs)) ->
          (*** simple adaptor ***)
          if adaptor_mode = "simple" 
          then Some (fun () -> 
		(* Assuming we are running on X86_64 *)
            let arg_regs = [R_RDI;R_RSI;R_RDX;R_RCX;R_R8;R_R9] in
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
            let rec loop n =
              let var_name = String.make 1 (Char.chr ((Char.code 'a') + n)) in
              let var_is_const = 
                fm#get_fresh_symbolic (var_name^"_is_const") 1 in
              let var_val = fm#get_fresh_symbolic (var_name^"_val") 64 in
              let arg = get_ite_expr var_is_const V.NEQ V.REG_1 0L 
                var_val (get_ite_arg_expr var_val out_nargs) in
              opt_extra_conditions :=
                V.BinOp(
                  V.BITOR,
                  V.BinOp(V.EQ,var_is_const,V.Constant(V.Int(V.REG_1,1L))),
                  V.BinOp(V.LT,var_val,V.Constant(V.Int(V.REG_64,out_nargs))))
              :: !opt_extra_conditions;
              fm#set_reg_symbolic (List.nth arg_regs n) arg;
              if n > 0 then loop (n-1); 
            in
            loop ((Int64.to_int in_nargs)-1);
            (Some in_addr))
          (*** adaptor using trees of arithmetic (integer) expressions ***)
          else if adaptor_mode = "arithmetic_int" 
            then Some (fun () -> 
              let arg_regs = [R_RDI;R_RSI;R_RDX;R_RCX;R_R8;R_R9] in (* assumes X86_64 *)
              let val_type = V.REG_32 in (* 32- or 64-bit values *)
              let get_ite_expr if_arg if_op if_const_type if_const then_val else_val = 
                V.Ite(V.BinOp(if_op,if_arg,V.Constant(V.Int(if_const_type,if_const))),
                      then_val,
                      else_val) in
              let rec get_ite_arg_expr arg_val n_arg =
                if n_arg <> 1
                then
                  get_ite_expr arg_val V.EQ val_type (Int64.of_int (n_arg - 1)) 
                    (if val_type = V.REG_32
                     then V.Cast(V.CAST_LOW, V.REG_32,
                                 fm#get_reg_symbolic (List.nth arg_regs (n_arg - 1)))
                     else fm#get_reg_symbolic (List.nth arg_regs (n_arg - 1)))
                    (get_ite_arg_expr arg_val (n_arg - 1))
                else 
                  (if val_type = V.REG_32
                     then V.Cast(V.CAST_LOW, V.REG_32,
                                 fm#get_reg_symbolic (List.nth arg_regs 0))
                     else fm#get_reg_symbolic (List.nth arg_regs 0)) in
              let binops = [V.PLUS; V.MINUS; V.TIMES; V.BITAND; V.BITOR; V.XOR;
                            V.DIVIDE; V.SDIVIDE; V.MOD; V.SMOD; V.LSHIFT; 
                            V.RSHIFT; V.ARSHIFT] in
              let unops = [V.NEG; V.NOT] in
              let special_ops1 = [V.DIVIDE; V.SDIVIDE; V.MOD; V.SMOD] in
              let special_ops2 = [V.LSHIFT; V.RSHIFT; V.ARSHIFT] in
              let num_ops = (List.length binops) + (List.length unops) in
              let get_oper oper l_expr r_expr =
                let rec get_unop ops n =
                  match ops with 
                  | [] -> failwith "Missing operators for the arithmetic adaptor"
                  | unop::[] -> 
                      (V.UnOp(unop, l_expr))
                  | unop::tl -> 
                      get_ite_expr oper V.EQ val_type n
                        (V.UnOp(unop, l_expr))
                        (get_unop tl (Int64.add n 1L)) in
                let rec get_binop ops n =
                  match ops with 
                  | [] -> get_unop unops n
                  | binop::[] when (List.length unops) = 0 -> 
                      if (List.mem binop special_ops1)
                      then (* (oper l_expr (if r_expr=0 then 1 else r_expr)) *)
                        V.BinOp(binop, l_expr, 
                          get_ite_expr r_expr V.EQ val_type 0L 
                            (V.Constant(V.Int(val_type, 1L))) 
                            r_expr)
                      else 
                        if (List.mem binop special_ops2)
                        then (* (oper l_expr (r_expr & X)) where X is 31 or 63 *)
                          V.BinOp(binop, l_expr, 
                            V.BinOp(V.BITAND, r_expr, 
                              if val_type = V.REG_32
                              then V.Constant(V.Int(val_type, 31L))
                              else V.Constant(V.Int(val_type, 63L))))
                        else (* (oper l_expr r_expr) *)
                          (V.BinOp(binop, l_expr, r_expr))
                  | binop::tl -> 
                      let expr = if (List.mem binop special_ops1)
                                 then (* (oper l_expr (if r_expr=0 then 1 else r_expr)) *)
                                   V.BinOp(binop, l_expr, 
                                     get_ite_expr r_expr V.EQ val_type 0L 
                                       (V.Constant(V.Int(val_type, 1L))) 
                                       r_expr)
                                 else 
                                   if (List.mem binop special_ops2)
                                   then (* (oper l_expr (r_expr & X))
                                           where X is 31 or 63 *)
                                     V.BinOp(binop, l_expr, 
                                       V.BinOp(V.BITAND, r_expr, 
                                       if val_type = V.REG_32
                                       then V.Constant(V.Int(val_type, 31L))
                                       else V.Constant(V.Int(val_type, 63L))))
                                   else (* (oper l_expr r_expr) *)
                                     (V.BinOp(binop, l_expr, r_expr)) in
                      get_ite_expr oper V.EQ val_type n 
                        expr (get_binop tl (Int64.add n 1L)) in
                get_binop binops 0L
              in
              let rec main_loop n =
                let var_name = String.make 1 (Char.chr ((Char.code 'a') + n)) in
                let tree_depth = 3 in (* hardcoded for now *)
                (*
                NOTE: this code is commented out to prevent 'unused X' warnings,
                      but it will work fine if you uncomment it.
                
                (* create a restricted range for constant values *)
                let restrict_range node_type node_val lower upper =
                  V.BinOp(
                    V.BITOR,
                    V.BinOp(V.NEQ, node_type, V.Constant(V.Int(V.REG_8, 0L))),
                    V.BinOp(
                      V.BITAND, 
                      V.UnOp(V.NOT, 
                             V.BinOp(V.LT, node_val, V.Constant(V.Int(val_type, lower)))),
                      V.BinOp(V.LE, node_val, V.Constant(V.Int(val_type, upper))))) in*)
                (* specify all possible values *)
                let specify_vals node_type node_val vals =
                  let rec list_vals l = 
                    match l with
                    | [] -> failwith "Bad value list for arithmetic adaptor"
                    | v::[] -> V.BinOp(V.EQ, node_val, V.Constant(V.Int(val_type, v)))
                    | v::t -> V.BinOp(
                                V.BITOR, 
                                V.BinOp(V.EQ, node_val, V.Constant(V.Int(val_type, v))),
                                list_vals t) in
                  V.BinOp(
                    V.BITOR,
                    V.BinOp(V.NEQ, node_type, V.Constant(V.Int(V.REG_8, 0L))),
                    (* note: for implementation reasons, the vals list must always contain 0 *)
                    list_vals (0L::vals)) in
                
                
                let rec zero_lower d base =
                  let node_type = fm#get_fresh_symbolic (var_name ^ "_type_" ^ base) 8 in
                  let node_val = fm#get_fresh_symbolic (var_name ^ "_val_" ^ base) 
                                   (if val_type = V.REG_32 then 32 else 64) in
                  if d = 1 
                  then 
                    V.BinOp(
                      V.BITAND, 
                      V.BinOp(V.EQ, node_type, V.Constant(V.Int(V.REG_8, 0L))), 
                      V.BinOp(V.EQ, node_val, V.Constant(V.Int(val_type, 0L))))
                  else
                    V.BinOp(
                      V.BITAND, 
                      V.BinOp(
                        V.BITAND, 
                        V.BinOp(V.EQ, node_type, V.Constant(V.Int(V.REG_8, 0L))), 
                        V.BinOp(V.EQ, node_val, V.Constant(V.Int(val_type, 0L)))),
                      V.BinOp(
                        V.BITAND, 
                        zero_lower (d-1) (base ^ "0"),
                        zero_lower (d-1) (base ^ "1"))) in
                (* type_X - the type of this node
                            0 -> constant value (= val_X)
                            1 -> the argument at position val_X
                            2 -> an integer operation (= val_X)
                   Here 'X' is a string consisting of 'R' (for 'root') followed
                   by some number of 0's and 1's corresponding to the path to
                   the node (0 for left and 1 for right) *)
                let rec build_tree d base =
                  if d <= 0 then failwith "Bad tree depth for arithmetic adaptor"
                  else 
                    let node_type = fm#get_fresh_symbolic (var_name ^ "_type_" ^ base) 8 in
                    let node_val = fm#get_fresh_symbolic (var_name ^ "_val_" ^ base) 
                                     (if val_type = V.REG_32 then 32 else 64) in
                     if d = 1 
                     then 
                        (* add the following conditions:
                           - type <= 1
                           - if type = 1, then val < (# of arguments)
                           - if type = 0, then val must be in the specified range,
                             or be one of the specified values
                         note: shouldn't have an operator at a leaf *)
                       (opt_extra_conditions := 
                          (V.BinOp(V.LE, node_type, V.Constant(V.Int(V.REG_8, 1L)))) ::
                          (V.BinOp(
                             V.BITOR,
                             V.BinOp(V.NEQ, node_type, V.Constant(V.Int(V.REG_8, 1L))),
                             V.BinOp(V.LT, node_val, V.Constant(V.Int(val_type, out_nargs))))) :: 
                          (*(restrict_range node_type node_val 0L 10L) ::*)
                          (specify_vals node_type node_val [-1L; 1L; 31L]) ::
                          !opt_extra_conditions;
                        get_ite_expr node_type V.EQ V.REG_8 0L 
                          node_val 
                          (get_ite_arg_expr node_val (Int64.to_int out_nargs)))
                      else
                        (* add the following conditions:
                           - type <= 2
                           - if type = 1, then val < (# of arguments)
                           - if type = 2, then val < (# of operators)
                           - if type = 0, then val must be in the specified range,
                             or be one of the specified values *)
                        (opt_extra_conditions := 
                           (V.BinOp(V.LE, node_type, V.Constant(V.Int(V.REG_8, 2L)))) ::
                           (V.BinOp(
                              V.BITOR,
                              V.BinOp(V.NEQ, node_type, V.Constant(V.Int(V.REG_8, 1L))),
                              V.BinOp(V.LT, node_val, V.Constant(V.Int(val_type, out_nargs))))) :: 
                           (V.BinOp(
                              V.BITOR,
                              V.BinOp(V.NEQ, node_type, V.Constant(V.Int(V.REG_8, 2L))),
                              V.BinOp(V.LT, node_val, 
                                      V.Constant(V.Int(val_type, Int64.of_int num_ops))))) ::
                           (*(restrict_range node_type node_val 0L 10L) ::*)
                           (specify_vals node_type node_val [-1L; 1L; 31L]) ::
                           !opt_extra_conditions;
                        (* - require all lower branches to be zero when the node
                             type is 0 or 1 (constant or variable)
                           - require the right branch to be zero when the node 
                             type is 2 and the value is >= # bin ops (unary operator) *)
                        opt_extra_conditions :=
                        (V.BinOp(
                              V.BITOR,
                              V.BinOp(V.EQ, node_type, V.Constant(V.Int(V.REG_8, 2L))),
                              V.BinOp(V.BITAND, 
                                      zero_lower (d-1) (base ^ "0"), 
                                      zero_lower (d-1) (base ^ "1")))) ::
                        (V.BinOp(
                              V.BITOR,
                              V.BinOp(V.BITOR, 
                                      V.BinOp(V.NEQ, node_type, V.Constant(V.Int(V.REG_8, 2L))), 
                                      V.BinOp(V.LT, node_val, 
                                        V.Constant(V.Int(val_type, 
                                          Int64.of_int (List.length binops))))),
                             zero_lower (d-1) (base ^ "1"))) ::
                          !opt_extra_conditions;             
                        let left_expr = build_tree (d-1) (base ^ "0") in
                        let right_expr = build_tree (d-1) (base ^ "1") in
                        get_ite_expr node_type V.EQ V.REG_8 0L 
                          node_val 
                          (get_ite_expr node_type V.EQ V.REG_8 1L
                             (get_ite_arg_expr node_val (Int64.to_int out_nargs)) 
                             (get_oper node_val left_expr right_expr))) in
                let expr = build_tree tree_depth "R" in
                fm#set_reg_symbolic (List.nth arg_regs n) expr;
                if n > 0 then main_loop (n-1); 
              in
              main_loop ((Int64.to_int in_nargs) - 1);
              (Some in_addr))
          (*** adaptor using trees of arithmetic (SSE floating point) expressions ***)
          else if adaptor_mode = "arithmetic_float" 
            then Some (fun () -> 
              let arg_regs = [R_YMM0_0; R_YMM1_0; R_YMM2_0; R_YMM3_0] in (* NOTE: not tested! *)
              let val_type = V.REG_64 in (* 32- or 64-bit values *)
              let get_ite_expr if_arg if_op if_const_type if_const then_val else_val = 
                V.Ite(V.BinOp(if_op, if_arg, V.Constant(V.Int(if_const_type,if_const))),
                      then_val,
                      else_val) in
              let rec get_ite_arg_expr arg_val n_arg =
                if n_arg <> 1
                then
                  get_ite_expr arg_val V.EQ val_type (Int64.of_int (n_arg - 1)) 
                    (if val_type = V.REG_32
                     then V.Cast(V.CAST_LOW, V.REG_32,
                                 fm#get_reg_symbolic (List.nth arg_regs (n_arg - 1)))
                     else fm#get_reg_symbolic (List.nth arg_regs (n_arg - 1)))
                    (get_ite_arg_expr arg_val (n_arg - 1))
                else 
                  (if val_type = V.REG_32
                     then V.Cast(V.CAST_LOW, V.REG_32,
                                 fm#get_reg_symbolic (List.nth arg_regs 0))
                     else fm#get_reg_symbolic (List.nth arg_regs 0)) in
              let binops = [V.FPLUS(*; V.FMINUS; V.FTIMES; V.FDIVIDE*)] in
              let unops = [V.FNEG] in
              let num_ops = (List.length binops) + (List.length unops) in
              let rm = Vine_util.ROUND_NEAREST in
              let get_oper oper l_expr r_expr =
                let rec get_unop ops n =
                  match ops with 
                  | [] -> failwith "Missing operators for the arithmetic adaptor"
                  | unop::[] -> 
                      (V.FUnOp(unop, rm, l_expr))
                  | unop::tl -> 
                      get_ite_expr oper V.EQ val_type n
                        (V.FUnOp(unop, rm, l_expr))
                        (get_unop tl (Int64.add n 1L)) in
                let rec get_binop ops n =
                  match ops with 
                  | [] -> get_unop unops n
                  | binop::[] when (List.length unops) = 0 -> 
                      if binop = V.FDIVIDE 
                      then (* (oper l_expr (if r_expr=0 then 1 else r_expr)) *)
                        V.FBinOp(binop, rm, l_expr, 
                                 get_ite_expr r_expr V.EQ val_type 0L 
                                   (V.Constant(V.Int(val_type, 1L))) 
                                   r_expr)
                      else (* (oper l_expr r_expr) *)
                        V.FBinOp(binop, rm, l_expr, r_expr)
                  | binop::tl -> 
                      let expr = 
                        if binop = V.FDIVIDE 
                        then (* (oper l_expr (if r_expr=0 then 1 else r_expr)) *)
                          V.FBinOp(binop, rm, l_expr, 
                                   get_ite_expr r_expr V.EQ val_type 0L 
                                     (V.Constant(V.Int(val_type, 1L))) 
                                     r_expr)
                        else (* (oper l_expr r_expr) *)
                          V.FBinOp(binop, rm, l_expr, r_expr) in
                      get_ite_expr oper V.EQ val_type n 
                        expr (get_binop tl (Int64.add n 1L)) in
                get_binop binops 0L
              in
              let rec main_loop n =
                let var_name = String.make 1 (Char.chr ((Char.code 'a') + n)) in
                let tree_depth = 2 in (* hardcoded for now *)
                (*
                (* create a restricted range for constant values *)
                let restrict_range node_type node_val lower upper =
                  V.BinOp(
                    V.BITOR,
                    V.BinOp(V.NEQ, node_type, V.Constant(V.Int(V.REG_8, 0L))),
                    V.BinOp(
                      V.BITAND, 
                      V.UnOp(V.NOT, 
                             V.BinOp(V.LT, node_val, V.Constant(V.Int(val_type, lower)))),
                      V.BinOp(V.LE, node_val, V.Constant(V.Int(val_type, upper))))) in
                (* specify all possible values *)
                let specify_vals node_type node_val vals =
                  let rec list_vals l = 
                    match l with
                    | [] -> failwith "Bad value list for arithmetic adaptor"
                    | v::[] -> V.BinOp(V.EQ, node_val, V.Constant(V.Int(val_type, v)))
                    | v::t -> V.BinOp(
                                V.BITOR, 
                                V.BinOp(V.EQ, node_val, V.Constant(V.Int(val_type, v))),
                                list_vals t) in
                  V.BinOp(
                    V.BITOR,
                    V.BinOp(V.NEQ, node_type, V.Constant(V.Int(V.REG_8, 0L))),
                    (* note: for implementation reasons, the vals list must always contain 0 *)
                    list_vals (0L::vals)) in
                
                *)
                let rec zero_lower d base =
                  let node_type = fm#get_fresh_symbolic (var_name ^ "_type_" ^ base) 8 in
                  let node_val = fm#get_fresh_symbolic (var_name ^ "_val_" ^ base) 
                                   (if val_type = V.REG_32 then 32 else 64) in
                  if d = 1 
                  then 
                    V.BinOp(
                      V.BITAND, 
                      V.BinOp(V.EQ, node_type, V.Constant(V.Int(V.REG_8, 0L))), 
                      V.BinOp(V.EQ, node_val, V.Constant(V.Int(val_type, 0L))))
                  else
                    V.BinOp(
                      V.BITAND, 
                      V.BinOp(
                        V.BITAND, 
                        V.BinOp(V.EQ, node_type, V.Constant(V.Int(V.REG_8, 0L))), 
                        V.BinOp(V.EQ, node_val, V.Constant(V.Int(val_type, 0L)))),
                      V.BinOp(
                        V.BITAND, 
                        zero_lower (d-1) (base ^ "0"),
                        zero_lower (d-1) (base ^ "1"))) in
                (* type_X - the type of this node
                            0 -> constant value (= val_X)
                            1 -> the argument at position val_X
                            2 -> an integer operation (= val_X)
                   Here 'X' is a string consisting of 'R' (for 'root') followed
                   by some number of 0's and 1's corresponding to the path to
                   the node (0 for left and 1 for right) *)
                let rec build_tree d base =
                  if d <= 0 then failwith "Bad tree depth for arithmetic adaptor"
                  else 
                    let node_type = fm#get_fresh_symbolic (var_name ^ "_type_" ^ base) 8 in
                    let node_val = fm#get_fresh_symbolic (var_name ^ "_val_" ^ base) 
                                     (if val_type = V.REG_32 then 32 else 64) in
                     if d = 1 
                     then 
                        (* add the following conditions:
                           - type <= 1
                           - if type = 1, then val < (# of arguments)
                           - if type = 0, then val must be in the specified range,
                             or be one of the specified values
                         note: shouldn't have an operator at a leaf *)
                       (opt_extra_conditions := 
                          (V.BinOp(V.LE, node_type, V.Constant(V.Int(V.REG_8, 1L)))) ::
                          (V.BinOp(
                             V.BITOR,
                             V.BinOp(V.NEQ, node_type, V.Constant(V.Int(V.REG_8, 1L))),
                             V.BinOp(V.LT, node_val, V.Constant(V.Int(val_type, out_nargs))))) :: 
                          (*(restrict_range node_type node_val 0L 10L) ::
                          (specify_vals node_type node_val [-1L; 1L; 31L]) ::*)
                          !opt_extra_conditions;
                        get_ite_expr node_type V.EQ V.REG_8 0L 
                          node_val 
                          (get_ite_arg_expr node_val (Int64.to_int out_nargs)))
                      else
                        (* add the following conditions:
                           - type <= 2
                           - if type = 1, then val < (# of arguments)
                           - if type = 2, then val < (# of operators)
                           - if type = 0, then val must be in the specified range,
                             or be one of the specified values *)
                        (opt_extra_conditions := 
                           (V.BinOp(V.LE, node_type, V.Constant(V.Int(V.REG_8, 2L)))) ::
                           (V.BinOp(
                              V.BITOR,
                              V.BinOp(V.NEQ, node_type, V.Constant(V.Int(V.REG_8, 1L))),
                              V.BinOp(V.LT, node_val, V.Constant(V.Int(val_type, out_nargs))))) :: 
                           (V.BinOp(
                              V.BITOR,
                              V.BinOp(V.NEQ, node_type, V.Constant(V.Int(V.REG_8, 2L))),
                              V.BinOp(V.LT, node_val, 
                                      V.Constant(V.Int(val_type, Int64.of_int num_ops))))) ::
                           (*(restrict_range node_type node_val 0L 10L) ::
                           (specify_vals node_type node_val [-1L; 1L; 31L]) ::*)
                           !opt_extra_conditions;
                        (* - require all lower branches to be zero when the node
                             type is 0 or 1 (constant or variable)
                           - require the right branch to be zero when the node 
                             type is 2 and the value is >= # bin ops (unary operator) *)
                        opt_extra_conditions :=
                        (V.BinOp(
                              V.BITOR,
                              V.BinOp(V.EQ, node_type, V.Constant(V.Int(V.REG_8, 2L))),
                              V.BinOp(V.BITAND, 
                                      zero_lower (d-1) (base ^ "0"), 
                                      zero_lower (d-1) (base ^ "1")))) ::
                        (V.BinOp(
                              V.BITOR,
                              V.BinOp(V.BITOR, 
                                      V.BinOp(V.NEQ, node_type, V.Constant(V.Int(V.REG_8, 2L))), 
                                      V.BinOp(V.LT, node_val, 
                                        V.Constant(V.Int(val_type, 
                                          Int64.of_int (List.length binops))))),
                             zero_lower (d-1) (base ^ "1"))) ::
                          !opt_extra_conditions;             
                        let left_expr = build_tree (d-1) (base ^ "0") in
                        let right_expr = build_tree (d-1) (base ^ "1") in
                        get_ite_expr node_type V.EQ V.REG_8 0L 
                          node_val 
                          (get_ite_expr node_type V.EQ V.REG_8 1L
                             (get_ite_arg_expr node_val (Int64.to_int out_nargs)) 
                             (get_oper node_val left_expr right_expr))) in
                let expr = build_tree tree_depth "R" in
                fm#set_reg_symbolic (List.nth arg_regs n) expr;
                if n > 0 then main_loop (n-1); 
              in
              main_loop ((Int64.to_int in_nargs) - 1);
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
  let rec get_offset_as_hex_array offset arr current_byte =
    (if current_byte < 0 then arr
    else
      (* let hex_str = Printf.sprintf "\\x%lx" *)
      let hex_str = char_of_int
                      (Int32.to_int 
                        (Int32.shift_right_logical
                          (Int32.shift_left 
                            (Int64.to_int32 offset) (current_byte*8)) 
                          24)) in
      (* Printf.printf "%s\n" hex_str; *)
      if hex_str <> '\x00'  then 
        get_offset_as_hex_array offset 
          (Array.append [|hex_str|] arr) (current_byte-1)
      else arr
    );
  in
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
                (*Printf.printf "eip %Lx:jumping to adapter %Lx \n" eip in_addr;*)
                let off = (Int64.sub in_addr eip) in
                let off_arr = (get_offset_as_hex_array off [||] 3) in
                let off_1 = (Int64.sub off 
                           (Int64.of_int ((Array.length off_arr)+1))) in
                let off_arr_1 = (get_offset_as_hex_array off_1 [||] 3) in
                (* Array.iter 
                  ( function ele -> Printf.printf "%s\n" ele) off_arr_1; *)
                Array.append [|'\xeb'|] off_arr_1
	      | (ARM, 0L,_) -> [|'\x1e'; '\xff'; '\x2f'; '\xe1'|] (* bx lr *)
	      | (ARM, 1L,_) -> [|'\x70'; '\x47'|] (* bx lr (Thumb) *)
	      | (ARM, _,_) -> failwith "Can't happen (logand with 1)"
	    in
	      decode_insn asmir_gamma eip fake_insn
	      (* decode_insn asmir_gamma eip fake_ret *)
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
