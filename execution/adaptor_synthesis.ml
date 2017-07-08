(* Extra file with helper code for adaptor synthesis. The functions 
   defined here are used in exec_fuzzloop.ml and exec_runloop.ml *)

module V = Vine;;

open Fragment_machine;;
open Exec_options;;
open Exec_exceptions;;
open Exec_utils;;


let adaptor_vals = Hashtbl.create 10
 
(*** general helper code used in multiple adaptors ***)

let get_ite_expr arg op const_type const then_val else_val = 
  V.Ite(V.BinOp(op, arg, V.Constant(V.Int(const_type, const))),
        then_val,
        else_val)

let rec get_ite_arg_expr fm arg_idx idx_type regs n =
  if n = 1L
  then fm#get_reg_symbolic (List.nth regs 0) 
  else get_ite_expr arg_idx V.EQ idx_type (Int64.sub n 1L) 
         (fm#get_reg_symbolic (List.nth regs ((Int64.to_int n) - 1)))
         (get_ite_arg_expr fm arg_idx idx_type regs (Int64.sub n 1L))


(* build an expression that restricts v to be in a certain range; the lower 
   and upper bounds are inclusive *)
let restrict_range v v_type lower upper =
  V.BinOp(V.BITAND, 
          V.UnOp(
            V.NOT, 
            V.BinOp(V.SLT, v, V.Constant(V.Int(v_type, lower)))),
          V.BinOp(V.SLE, v, V.Constant(V.Int(v_type, upper))))

(* build an expression that restricts v to be one of a specified list *)
let rec specify_vals v v_type vals =
match vals with
| [] -> failwith "Bad value list for arithmetic adaptor"
| v'::[] -> V.BinOp(V.EQ, v, V.Constant(V.Int(v_type, v')))
| v'::t -> 
    V.BinOp(V.BITOR, 
            V.BinOp(V.EQ, v, V.Constant(V.Int(v_type, v'))),
            specify_vals v v_type t)

(* restrict the value of expr to be in a specified range or one of a 
   specified value *)
let restrict expr expr_type restricted_range restricted_list =
  match restricted_range with
  | None -> 
      (match restricted_list with
       | None -> V.exp_true
       | Some l -> specify_vals expr expr_type l)
  | Some (lower, upper) -> restrict_range expr expr_type lower upper

(* build an arithmetic expression tree; this function is a little messy because 
   it takes so many arguments, but it's useful to reuse code between the integer 
   and floating point adaptor code
   
   type = 0 ----> constant value
   type = 1 ----> argument at the position val
   type = 2 ----> operator at position val (in int_binops @ int_unops) applied
                  to the left and right subtrees *)
let get_arithmetic_expr fm var arg_regs val_type out_nargs get_oper_expr depth
      apply_special_conditions =
  let rec build_tree d base =
    if d <= 0 then failwith "Bad tree depth for arithmetic adaptor"
    else 
      let node_type = if not !opt_adaptor_search_mode then 
	  Hashtbl.find adaptor_vals (var ^ "_type_" ^ base)
	else fm#get_fresh_symbolic (var ^ "_type_" ^ base) 8 in
      let node_val = if not !opt_adaptor_search_mode then 
	  Hashtbl.find adaptor_vals (var ^ "_val_" ^ base)
	else fm#get_fresh_symbolic (var ^ "_val_" ^ base) 
                       (if val_type = V.REG_32 then 32 else 64) in
      if d = 1 
      then if out_nargs = 0L
           then node_val
           else 
             get_ite_expr node_type V.EQ V.REG_8 0L 
               node_val 
               (let reg_expr = get_ite_arg_expr fm node_val val_type arg_regs out_nargs in
                if val_type = V.REG_32 
                then V.Cast(V.CAST_LOW, V.REG_32, reg_expr)
                else reg_expr)
      else
        let left_expr = build_tree (d-1) (base ^ "0") in
        let right_expr = build_tree (d-1) (base ^ "1") in
        (* TODO:: in progress
        let left_expr_sym = fm#get_fresh_symbolic (var ^ "_subtree_" ^ base ^ "0") 
                              (if val_type = V.REG_32 then 32 else 64) in
        let right_expr_sym = fm#get_fresh_symbolic (var ^ "_subtree_" ^ base ^ "1") 
                              (if val_type = V.REG_32 then 32 else 64) in
        let _ = fm#check_adaptor_condition 
                  (V.BinOp(V.EQ, left_expr_sym, left_expr)) in
        let _ = fm#check_adaptor_condition 
                  (V.BinOp(V.EQ, right_expr_sym, right_expr)) in*)
        let _ = match apply_special_conditions with
                | None -> ()
                | Some f -> f node_type node_val left_expr right_expr in
        if out_nargs = 0L
        then
          get_ite_expr node_type V.EQ V.REG_8 0L
            node_val
            (get_oper_expr node_val left_expr right_expr)
        else
          get_ite_expr node_type V.EQ V.REG_8 0L 
            node_val 
            (get_ite_expr node_type V.EQ V.REG_8 1L
               (let reg_expr = get_ite_arg_expr fm node_val val_type arg_regs out_nargs in
                if val_type = V.REG_32 
                then V.Cast(V.CAST_LOW, V.REG_32, reg_expr)
                else reg_expr) 
               (get_oper_expr node_val left_expr right_expr)) in
  build_tree depth "R"

(* add extra conditions on the structure of the int/float arithmetic adaptors' 
   expression trees; there are a lot of arguments here too, but this saves
   some copying & pasting later *)
let add_arithmetic_tree_conditions fm var_name val_type out_nargs 
      restrict_const_node binops unops depth =
  (* zeros-out nodes in an arithmetic expression subtree *)
  let rec zero_lower d base =
    let node_type = if not !opt_adaptor_search_mode then 
	Hashtbl.find adaptor_vals (var_name ^ "_type_" ^ base)
      else fm#get_fresh_symbolic (var_name ^ "_type_" ^ base) 8 in
    let node_val = if not !opt_adaptor_search_mode then 
	Hashtbl.find adaptor_vals (var_name ^ "_val_" ^ base)
      else fm#get_fresh_symbolic (var_name ^ "_val_" ^ base)
                     (if val_type = V.REG_32 then 32 else 64) in
    if d = 1 
    then 
      V.BinOp(V.BITAND, 
              V.BinOp(V.EQ, node_type, V.Constant(V.Int(V.REG_8, 0L))), 
              V.BinOp(V.EQ, node_val, V.Constant(V.Int(val_type, 0L))))
    else
      V.BinOp(V.BITAND, 
              V.BinOp(
                V.BITAND, 
                V.BinOp(V.EQ, node_type, V.Constant(V.Int(V.REG_8, 0L))), 
                V.BinOp(V.EQ, node_val, V.Constant(V.Int(val_type, 0L)))),
              V.BinOp(
                V.BITAND, 
                zero_lower (d-1) (base ^ "0"),
                zero_lower (d-1) (base ^ "1"))) in
  (* adds various conditions for every node in a tree *)
  let rec traverse_tree d base = 
    if d <= 0 then failwith "Bad tree depth for arithmetic adaptor"
    else 
      let node_type = if not !opt_adaptor_search_mode then 
	Hashtbl.find adaptor_vals (var_name ^ "_type_" ^ base)
	else fm#get_fresh_symbolic (var_name ^ "_type_" ^ base) 8 in
      let node_val = if not !opt_adaptor_search_mode then 
	Hashtbl.find adaptor_vals (var_name ^ "_val_" ^ base)
	else fm#get_fresh_symbolic (var_name ^ "_val_" ^ base)
                       (if val_type = V.REG_32 then 32 else 64) in
        if d = 1
        then 
          (* in this case we are at a leaf in the tree, we require:
             - type <= 1
             - if type = 1, then val < (# of arguments)
             - if type = 0, then val must be in the specified range,
               or be one of the specified values
             - also, if out_nargs = 0 then we only want to allow constants *)
          synth_extra_conditions := 
            (V.BinOp(V.LE, node_type, V.Constant(V.Int(V.REG_8, 1L)))) ::
              (V.BinOp(
                 V.BITOR,
                 V.BinOp(V.NEQ, node_type, V.Constant(V.Int(V.REG_8, 1L))),
                 V.BinOp(V.LT, node_val, V.Constant(V.Int(val_type, out_nargs))))) :: 
            (restrict_const_node node_type node_val) ::
            (if out_nargs = 0L 
             then (V.BinOp(V.EQ, node_type, V.Constant(V.Int(V.REG_8, 0L)))) :: !synth_extra_conditions 
             else !synth_extra_conditions)
        else
          (* in this case we are at a non-leaf node, we require:
             - type <= 2
             - if type = 1, then val < (# of arguments)
             - if type = 2, then val < (# of operators)
             - if type = 0, then val must be in the specified range,
               or be one of the specified values
             - if the type is 0 or 1 (constant or variable) then the nodes in
               the left and right subtrees must be zero
             - if type = 2 and val corresponds to a unary operator, then nodes
               in the right subtree must be zero
             - also, if out_nargs = 0 then we only want to allow constants & operators *)
          (synth_extra_conditions := 
            (V.BinOp(V.LE, node_type, V.Constant(V.Int(V.REG_8, 2L)))) ::
            (V.BinOp(
               V.BITOR,
               V.BinOp(V.NEQ, node_type, V.Constant(V.Int(V.REG_8, 1L))),
               V.BinOp(V.LT, node_val, V.Constant(V.Int(val_type, out_nargs))))) :: 
            (V.BinOp(
               V.BITOR,
               V.BinOp(V.NEQ, node_type, V.Constant(V.Int(V.REG_8, 2L))),
               V.BinOp(
                 V.LT, 
                 node_val, 
                 V.Constant
                 (V.Int(
                    val_type, 
                    Int64.of_int ((List.length binops) + (List.length unops))))))) ::
            (restrict_const_node node_type node_val) ::
            (V.BinOp(
               V.BITOR,
               V.BinOp(V.EQ, node_type, V.Constant(V.Int(V.REG_8, 2L))),
               V.BinOp(V.BITAND, 
                       zero_lower (d-1) (base ^ "0"), 
                       zero_lower (d-1) (base ^ "1")))) ::
            (V.BinOp(
               V.BITOR,
               V.BinOp(
                 V.BITOR, 
                 V.BinOp(V.NEQ, node_type, V.Constant(V.Int(V.REG_8, 2L))), 
                 V.BinOp(V.LT, node_val, 
                         V.Constant(
                           V.Int(
                             val_type, 
                             Int64.of_int (List.length binops))))),
               zero_lower (d-1) (base ^ "1"))) ::
            (if out_nargs = 0L
             then (V.BinOp(V.BITOR,
                           V.BinOp(V.EQ, node_type, V.Constant(V.Int(V.REG_8, 0L))),
                           V.BinOp(V.EQ, node_type, V.Constant(V.Int(V.REG_8, 2L))))) ::
                  !synth_extra_conditions 
             else !synth_extra_conditions);
            traverse_tree (d-1) (base ^ "0");
            traverse_tree (d-1) (base ^ "1")) in
  traverse_tree depth "R"

(*** integer arithmetic adaptor ***)

(* use the variables below to specify the kinds of adaptors and 
   counterexamples that can be synthesized; these variables will be used
   in arithmetic_int_adaptor and arithmetic_int_extra_conditions *)
(* tree depth *)
let int_arith_depth = 2
(* 32 or 64-bit values (int vs. long int) *)
let int_val_type = V.REG_64
(* binary and unary operators; all possible operators:
   V.PLUS; V.MINUS; V.TIMES; V.BITAND; V.BITOR; V.XOR; V.DIVIDE; 
   V.SDIVIDE;V.MOD; V.SMOD; V.LSHIFT; V.RSHIFT; V.ARSHIFT;
   V.NEG; V.NOT 
   
   if shift operations are included in the list, put them all next to each 
   other (consecutive); do the smae if mod or division operations are included
   in the list; this makes placing restrictions on the operands to these
   operators a little easier *)
let int_binops = [V.PLUS; V.MINUS; V.BITAND; V.BITOR; V.XOR; V.LSHIFT; V.RSHIFT; V.ARSHIFT]
let int_unops = [V.NEG; V.NOT]
(* restrict the constant values generated; int_restrict_constant_range
   should be 'None' or 'Some (lower, upper)' and int_restrict_constant_list 
   should be 'None' or 'Some [v1; v2; ...; vn]' (NOTE: this list must contain
   zero if used) *)
let int_restrict_constant_range = None (* Some (0L, 16L) used for killpg <- kill *) (* Some (-187L, 187L) used for isupper <-> islower *)
let int_restrict_constant_list = None
(* restrict the input and output of the adaptor (input restrictions reflect
   f1 preconditions and output restrictions reflect f2 preconditions)
   int_restrict_X_range should be 'None' or 'Some (lower, upper)' and 
   int_restrict_X_list should be 'None' or 'Some [v1; v2; ...; vn]' (NOTE:
   this list must contain zero if used) *)
let int_restrict_input_range = Some (0L, 2147483647L) (* Used for killpg <- kill *)
let int_restrict_input_list = None
let int_restrict_output_range = None
let int_restrict_output_list = None

(* creates symbolic variables representing the adaptor function and encodes
   the rules for applying the adaptor function; this function is called in 
   exec_runloop *)
let arithmetic_int_adaptor fm out_nargs in_nargs =
  (* argument registers -- assumes x86-64 *)
  let arg_regs = [R_RDI;R_RSI;R_RDX;R_RCX;R_R8;R_R9] in
  (* operators that require special handling *)
  let div_ops = [V.DIVIDE; V.SDIVIDE; V.MOD; V.SMOD] in
  let shift_ops = [V.LSHIFT; V.RSHIFT; V.ARSHIFT] in
  (* builds an expression that applies some operator to apply to l and r *)
  let get_oper_expr node_value l r =
    let rec unop_expr ops n =
      match ops with 
      | [] -> failwith "Missing operators for the arithmetic adaptor"
      | unop::[] -> V.UnOp(unop, l)
      | unop::tl -> 
          get_ite_expr node_value V.EQ int_val_type n
            (V.UnOp(unop, l))
            (unop_expr tl (Int64.add n 1L)) in
    let rec binop_expr ops n =
      match ops with 
      | [] -> unop_expr int_unops n
      | binop::tl -> 
          let expr = 
            if (List.mem binop div_ops)
            then (* accounts for div. by zero *)
              V.BinOp(
                binop, l, 
                get_ite_expr r V.EQ int_val_type 0L 
                  (V.Constant(V.Int(int_val_type, 1L))) r)
            else 
              if (List.mem binop shift_ops)
              then (* forces shifts by valid values *)
                V.BinOp(
                  binop, l, 
                  V.BinOp(
                    V.BITAND, r, 
                    if int_val_type = V.REG_32
                    then V.Constant(V.Int(int_val_type, 31L))
                    else V.Constant(V.Int(int_val_type, 63L))))
              else (* standard binary operator application *)
                V.BinOp(binop, l, r) in
          if (tl = [] && int_unops = [])
          then expr
          else get_ite_expr node_value V.EQ int_val_type n
                 expr (binop_expr tl (Int64.add n 1L)) in
    binop_expr int_binops 0L in
  (* build a function that restricts the operands of shift, mod, and division
     to be 'good'; this function will be run in get_arithmetic_expr *)
  (* TODO: in progress
    let other_restrictions node_type node_val left_expr right_expr = 
    let get_op_indices l = 
      List.filter (fun el -> el <> (-1L)) 
                  (List.mapi 
                     (fun idx el -> if (List.mem el l) 
                                    then Int64.of_int idx else -1L) 
                  int_binops) in
    let shift_indices = get_op_indices shift_ops in
    let div_indices = get_op_indices div_ops in
    (match shift_indices with
     | [] -> ()
     | l -> (* if the current node corresponds to a shift operation, force the 
               right operand to be <= 32 or <=64 *)
         let expr =
           V.BinOp(
             V.BITOR,
             V.UnOp(
               V.NOT, 
               V.BinOp(
                 V.BITAND,
                 V.BinOp(V.EQ, node_type, V.Constant(V.Int(V.REG_8, 2L))),
                 specify_vals node_val int_val_type shift_indices)),
             V.BinOp(
               V.BITAND,
               V.UnOp(
                 V.NOT, 
                 V.BinOp(V.LT, right_expr, V.Constant(V.Int(int_val_type, 0L)))),
               V.BinOp(
                 V.LE, 
                 right_expr, 
                 V.Constant(
                   V.Int(int_val_type, 
                         if int_val_type = V.REG_32 then 32L else 64L))))) in
         fm#check_adaptor_condition expr;
     match div_indices with
     | [] -> ()
     | l -> (* if the current node corresponds to a division/mod operation, 
               force the right operand to be <> 0 *)
         let expr =
           V.BinOp(
             V.BITOR,
             V.UnOp(
               V.NOT, 
               V.BinOp(
                 V.BITAND,
                 V.BinOp(V.EQ, node_type, V.Constant(V.Int(V.REG_8, 2L))),
                 specify_vals node_val int_val_type div_indices)),
             V.BinOp(
               V.NEQ,
               right_expr,
               V.Constant(V.Int(int_val_type, 0L)))) in
         fm#check_adaptor_condition expr) in*)
  (* we store symbolic expressions representing adaptors in a list and then 
     later call set_reg_symbolic on each expression in that list *)
  let symbolic_exprs = ref [] in
  let rec get_exprs n =
    let var_name = String.make 1 (Char.chr ((Char.code 'a') + n)) in
    symbolic_exprs :=
      (get_arithmetic_expr fm var_name arg_regs int_val_type out_nargs 
         get_oper_expr int_arith_depth None) 
      :: !symbolic_exprs;
    if n > 0 then get_exprs (n-1) else () in
  if in_nargs > 0L
  then
    (get_exprs ((Int64.to_int in_nargs) - 1);
     List.iteri
       (fun idx expr ->
          (*let var_name = String.make 1 (Char.chr ((Char.code 'a') + idx)) in 
          let root_sym = fm#get_fresh_symbolic (var_name ^ "_subtree_R") 
                           (if int_val_type = V.REG_32 then 32 else 64) in
          fm#check_adaptor_condition (V.BinOp(V.EQ, root_sym, expr));
          fm#set_reg_symbolic (List.nth arg_regs idx) root_sym;
          fm#check_adaptor_condition 
            (restrict root_sym int_val_type int_restrict_output_range 
               int_restrict_output_list)*)
          fm#set_reg_symbolic (List.nth arg_regs idx) expr;
          fm#check_adaptor_condition 
            (restrict expr int_val_type int_restrict_output_range 
               int_restrict_output_list))
       !symbolic_exprs)
  else ()
   
let arithmetic_int_init_sym_vars fm in_nargs = 
  let rec create_arith_int_sym_vars prev_type_str prev_val_str d =
    ignore(fm#get_fresh_symbolic (prev_type_str^"0") 8);
    ignore(fm#get_fresh_symbolic (prev_val_str^"0") 64);
    ignore(fm#get_fresh_symbolic (prev_type_str^"1") 8);
    ignore(fm#get_fresh_symbolic (prev_val_str^"1") 64);
    if d <> 1 then (
      create_arith_int_sym_vars (prev_type_str^"0") (prev_val_str^"0") (d-1);
      create_arith_int_sym_vars (prev_type_str^"1") (prev_val_str^"1") (d-1);
    );
  in
  for i = 0 to in_nargs do
    let type_str = Printf.sprintf "%c_type_R" (Char.chr ((Char.code 'a') + i)) in
    let val_str = Printf.sprintf "%c_val_R" (Char.chr ((Char.code 'a') + i)) in
    ignore(fm#get_fresh_symbolic type_str 8);
    ignore(fm#get_fresh_symbolic val_str 64);
    create_arith_int_sym_vars type_str val_str int_arith_depth;
  done;
 ()
 
(* adds extra conditions on the input variables and associated 
   adaptor variables; this function is called in exec_fuzzloop *)
let rec arithmetic_int_extra_conditions fm out_nargs n = 
  let var_name = String.make 1 (Char.chr ((Char.code 'a') + n)) in
  let var = fm#get_fresh_symbolic var_name 
      (if int_val_type = V.REG_32 then 32 else 64) in
  (* restrict the value of a constant node to be in a specified range or 
     one of a specified value *)
  let restrict_const_node node_type node_val =
    match int_restrict_constant_range with
    | None -> 
        (match int_restrict_constant_list with
         | None -> V.exp_true
         | Some l -> 
             V.BinOp(
               V.BITOR,
               V.BinOp(V.NEQ, node_type, V.Constant(V.Int(V.REG_8, 0L))),
               specify_vals node_val int_val_type l))
    | Some (lower, upper) ->
        V.BinOp(
          V.BITOR,
          V.BinOp(V.NEQ, node_type, V.Constant(V.Int(V.REG_8, 0L))),
          restrict_range node_val int_val_type lower upper) in
  (* restrict the generated counterexamples *)
  let _ = synth_extra_conditions := 
    (restrict var int_val_type int_restrict_input_range int_restrict_input_list) 
      :: !synth_extra_conditions in
  add_arithmetic_tree_conditions fm var_name int_val_type out_nargs 
    restrict_const_node int_binops int_unops int_arith_depth;
  if n > 0 then arithmetic_int_extra_conditions fm out_nargs (n-1) else ()

(*** floating point arithmetic adaptor ***)

(* use the variables below to specify the kinds of adaptors and 
   counterexamples that can be synthesized; these variables will be used
   in arithmetic_float_adaptor and arithmetic_float_extra_conditions *)
(* tree depth *)
let float_arith_depth = 2
(* 32 or 64-bit values (float vs. double) *)
let float_val_type = V.REG_32
(* binary and unary operators; all possible operators:
   V.FPLUS; V.FMINUS; V.FTIMES; V.FDIVIDE; V.FNEG *)
let float_binops = [V.FPLUS; V.FMINUS; V.FTIMES]
let float_unops = [V.FNEG]
let float_rm = Vine_util.ROUND_NEAREST
(* restrict the constant values generated; float_restrict_constant_range
   should be 'None' or 'Some (lower, upper)' and float_restrict_constant_list 
   should be 'None' or 'Some [v1; v2; ...; vn]'; these may not actually
   be useful because e.g. the restricting range has to be very narrow to 
   noticeably reduce the search space *)
let float_restrict_constant_range = None
let float_restrict_constant_list = None
(* restrict the counterexamples generated; float_restrict_counterexample_range
   should be 'None' or 'Some (lower, upper)' and float_restrict_counterexample_list 
   should be 'None' or 'Some [v1; v2; ...; vn]'; same note as above: these may
   not be very useful *)
let float_restrict_counterexample_range = Some (0.0, 0.5)
let float_restrict_counterexample_list = None

(* creates symbolic variables representing the adaptor function and encodes
   the rules for applying the adaptor function; this function is called in 
   exec_runloop *)
let arithmetic_float_adaptor fm out_nargs in_nargs =
  (* argument registers -- assumes SSE floating point *)
  let arg_regs = [R_YMM0_0; R_YMM1_0; R_YMM2_0; R_YMM3_0; R_YMM4_0; R_YMM5_0] in
  (* operators that require special handling *)
  let special_type = [V.FDIVIDE] in
  (* builds an expression that applies some operator to apply to l and r *)
  let get_oper_expr node_value l r =
    let rec unop_expr ops n =
      match ops with 
      | [] -> failwith "Missing operators for the arithmetic adaptor"
      | unop::[] -> V.FUnOp(unop, float_rm, l)
      | unop::tl -> 
          get_ite_expr node_value V.EQ float_val_type n
            (V.FUnOp(unop, float_rm, l))
            (unop_expr tl (Int64.add n 1L)) in
    let rec binop_expr ops n =
      match ops with 
      | [] -> unop_expr float_unops n
      | binop::tl -> 
          let expr = 
            if (List.mem binop special_type)
            then (* accounts for div. by zero *)
              V.FBinOp(
                binop, float_rm, l, 
                get_ite_expr r V.EQ V.REG_32 0L 
                  (V.Constant(V.Int(V.REG_32, 1L))) r) 
            else (* standard binary operator application *)
              V.FBinOp(binop, float_rm, l, r) in
          if (tl = [] && float_unops = [])
          then expr
          else get_ite_expr node_value V.EQ float_val_type n
                 expr (binop_expr tl (Int64.add n 1L)) in
    binop_expr float_binops 0L in
  (* we store symbolic expressions representing adaptors in a list and then 
     later call set_reg_symbolic on each expression in that list *)
  let symbolic_exprs = ref [] in
  let rec get_exprs n =
    let var_name = String.make 1 (Char.chr ((Char.code 'a') + n)) in
    symbolic_exprs :=
      (get_arithmetic_expr fm var_name arg_regs float_val_type out_nargs 
         get_oper_expr float_arith_depth None) :: !symbolic_exprs;
    if n > 0 then get_exprs (n-1) else () in
  (get_exprs ((Int64.to_int in_nargs) - 1);
   List.iteri 
     (fun idx expr ->
        fm#set_reg_symbolic (List.nth arg_regs idx) expr) !symbolic_exprs)
  
(* adds extra conditions on the input variables and associated adaptor 
   variables; this function is called in exec_fuzzloop; note that we use 
   integer comparisons (instead of floating point comparisons) in some of 
   our extra conditions, we can do this because the symbolic variables 
   just correspond to (kind of) typeless sequences of bits  *)
let rec arithmetic_float_extra_conditions fm out_nargs n = 
  let var_name = String.make 1 (Char.chr ((Char.code 'a') + n)) in
  let var = fm#get_fresh_symbolic var_name 
              (if float_val_type = V.REG_32 then 32 else 64) in
  let get_bits v = 
    if float_val_type = V.REG_32
    then Int64.of_int32 (Int32.bits_of_float v)
    else Int64.bits_of_float v in
  (* restrict a value to be in a certain range; the lower and upper bounds 
     are inclusive *)
  let restrict_range v lower upper =
    V.BinOp(V.BITAND, 
            V.UnOp(
              V.NOT, 
              V.FBinOp(V.FLT, float_rm, v, 
                       V.Constant(V.Int(float_val_type, get_bits lower)))),
            V.FBinOp(V.FLE, float_rm, v, 
                     V.Constant(V.Int(float_val_type, get_bits upper)))) in
  (* restrict a value to be one of a specified list
     NOTE: for implementation reasons, we always add 0L to the list of 
           possible values *)
  let rec specify_vals v vals =
    match vals with
    | [] -> failwith "Bad value list for arithmetic adaptor"
    | v'::[] -> 
        V.BinOp(V.BITOR, 
                V.BinOp(V.EQ, v, V.Constant(V.Int(float_val_type, get_bits v'))),
                V.BinOp(V.EQ, v, V.Constant(V.Int(float_val_type, 0L))))
    | v'::t -> 
        V.BinOp(V.BITOR, 
                V.BinOp(V.EQ, v, V.Constant(V.Int(float_val_type, get_bits v'))),
                specify_vals v t) in
  (* restrict the value of a constant node to be in a specified range or 
     one of a specified value *)
  let restrict_const_node node_type node_val =
    match float_restrict_constant_range with
    | None -> 
        (match float_restrict_constant_list with
         | None -> V.exp_true
         | Some l -> 
             V.BinOp(
               V.BITOR,
               V.BinOp(V.NEQ, node_type, V.Constant(V.Int(V.REG_8, 0L))),
               specify_vals node_val l))
    | Some (lower, upper) ->
        V.BinOp(
          V.BITOR,
          V.BinOp(V.NEQ, node_type, V.Constant(V.Int(V.REG_8, 0L))),
          restrict_range node_val lower upper) in
  (* restrict the value of the input variable to be in a specified range 
     or one of a specified value *)
  let restrict_input input =
    match float_restrict_counterexample_range with
    | None -> 
        (match float_restrict_counterexample_list with
         | None -> V.exp_true
         | Some l -> specify_vals input l)
    | Some (lower, upper) -> restrict_range input lower upper in
  (* restrict the generated counterexamples *)
  let _ = synth_extra_conditions := 
            (restrict_input var) ::
            !synth_extra_conditions in
  add_arithmetic_tree_conditions fm var_name float_val_type out_nargs 
    restrict_const_node float_binops float_unops float_arith_depth;
  if n > 0 then arithmetic_float_extra_conditions fm out_nargs (n-1) else ()  
  
(*** simple adaptor ***)

let simple_adaptor fm out_nargs in_nargs =
  Printf.printf "Starting simple adaptor\n";
  let arg_regs = 
    match !opt_arch with
    | X64 -> [R_RDI;R_RSI;R_RDX;R_RCX;R_R8;R_R9] 
    | ARM -> [R0; R1; R2; R3]
    | _ -> failwith "argregs unsupported for architecture"
  in
  let symbolic_args = ref [] in
  let (size, vine_size) = 
    match !opt_arch with 
    | X64 -> (64, V.REG_64)
    | ARM -> (32, V.REG_32)
    | _ -> failwith "argregs unsupported for architecture"
  in
  let rec main_loop n =
    let var_name = String.make 1 (Char.chr ((Char.code 'a') + n)) in
    let var_val = fm#get_fresh_symbolic (var_name^"_val") size in
    let var_is_const = fm#get_fresh_symbolic (var_name^"_is_const") 1 in
    let arg =  
      (if out_nargs = 0L then (
	(* These extra conditions should be getting added in exec_fuzzloop 
	   to make them get added at the beginning of each iteration *)
	(*opt_extra_conditions :=  
          V.BinOp(V.EQ,var_is_const,V.Constant(V.Int(V.REG_1,1L)))
	  :: !opt_extra_conditions;*)
	var_val
       ) 
       else ( 
	 (* Assuming adaptor_vals maps strings to Vine expressions
	    where each string is the name of an adaptor variable *)
	 if not !opt_adaptor_search_mode then (
	   let var_is_const_val = Hashtbl.find adaptor_vals (var_name^"_is_const") in
	   let var_val_val = Hashtbl.find adaptor_vals (var_name^"_val") in
	   if var_is_const_val = V.Constant(V.Int(V.REG_1, 0L)) then (
	     match var_val_val with
	     | V.Constant(V.Int(vine_size, n)) ->
	       let r = if n >= out_nargs then (Int64.pred out_nargs) else n in
	       (fm#get_reg_symbolic (List.nth arg_regs (Int64.to_int r) ))
	     | _ -> failwith (Printf.sprintf "failed to get value of %s_val" var_name)
	   ) else var_val_val
	 ) else 
	   get_ite_expr var_is_const V.NEQ V.REG_1 0L  
	     var_val (get_ite_arg_expr fm var_val vine_size arg_regs out_nargs) 
	 (*opt_extra_conditions :=  
	   V.BinOp(
           V.BITOR,
           V.BinOp(V.EQ,var_is_const,V.Constant(V.Int(V.REG_1,1L))),
           V.BinOp(V.LT,var_val,V.Constant(V.Int(V.REG_64,out_nargs))))
	   :: !opt_extra_conditions;*)
	     
       )) 
    in
    let arg' =
      (V.Cast(V.CAST_LOW, vine_size, (match arg with 
      | V.Lval(V.Temp((_, s, _))) -> 
	if Hashtbl.mem adaptor_vals s then
	  Hashtbl.find adaptor_vals s
	else arg
      | _ -> arg)))
    in
    Printf.printf "setting arg=%s\n" (V.exp_to_string arg');
    symbolic_args := arg' :: !symbolic_args;
    if n > 0 then main_loop (n-1); 
  in
  if in_nargs > 0L then  (
    main_loop ((Int64.to_int in_nargs)-1);
    List.iteri (fun index _expr ->
      let expr =  
	if (not !opt_adaptor_ivc) || !opt_adaptor_search_mode then 
	  _expr
	else (
	  match fm#query_unique_value _expr vine_size with
	  | Some v ->
	    Printf.printf "%s has unique value %Lx\n" 
	      (V.exp_to_string _expr) v;
	    (V.Constant(V.Int(vine_size, v)))
	  | None -> 
	    Printf.printf "%s does not have unique value\n" 
	      (V.exp_to_string _expr);
	    _expr
	)
      in
      fm#set_reg_symbolic (List.nth arg_regs index) expr;
    ) !symbolic_args;
  )

(* Simple adaptor code ends here *)


(* Type conversion adaptor *)

let get_ite_typeconv_expr fm arg_idx idx_type regs n =
  V.Cast(V.CAST_SIGNED, V.REG_64, 
	 V.Cast(V.CAST_LOW, V.REG_32, 
		(get_ite_arg_expr fm arg_idx idx_type regs n)
	 )
  ) 

let get_typeconv_expr src_operand src_type extend_op =
  V.Cast( extend_op, 
	 (match !opt_arch with
	 | X64 -> V.REG_64
	 | ARM -> V.REG_32
	 | _ -> failwith "unsupported return register for architecture"), 
	 (V.Cast(V.CAST_LOW, src_type, src_operand)) )

(* 
   type = 0 -> use the outer function argument in var_val
   type = 1 -> constant in var_val
   type = 11 -> 32-to-64 bit sign extension on outer function arg in var_val
   type = 12 -> 32-to-64 bit zero extension on outer function arg in var_val
   type = 21 -> 16-to-64 bit sign extension on outer function arg in var_val
   type = 22 -> 16-to-64 bit zero extension on outer function arg in var_val
   type = 31 -> 8-to-64 bit sign extension on outer function arg in var_val
   type = 32 -> 8-to-64 bit zero extension on outer function arg in var_val
   type = 41 -> 1-to-64 bit sign extension on outer function arg in var_val
   type = 42 -> 1-to-64 bit zero extension on outer function arg in var_val
   type = 43 -> 64-to-1 bit ITE operation on outer function arg in var_val
*)

let typeconv_adaptor fm out_nargs in_nargs =
  Printf.printf "Starting typeconv adaptor\n";
  let arg_regs = 
    match !opt_arch with
    | X64 -> [R_RDI;R_RSI;R_RDX;R_RCX;R_R8;R_R9] 
    | ARM -> [R0; R1; R2; R3]
    | _ -> failwith "argregs unsupported for architecture"
  in
  (* argument registers -- assumes SSE floating point *)
  (*let f_arg_regs = [R_YMM0_0; R_YMM1_0; R_YMM2_0; R_YMM3_0] in*)
  let symbolic_args = ref [] in
    let rec main_loop n =
    let var_name = String.make 1 (Char.chr ((Char.code 'a') + n)) in
    let var_val = fm#get_fresh_symbolic (var_name^"_val") 64 in
    let var_type = fm#get_fresh_symbolic (var_name^"_type") 8 in
    let arg =  
      (if out_nargs = 0L then (
	(* These extra conditions should be getting added in exec_fuzzloop 
	   to make them get added at the beginning of each iteration *)
	(*opt_extra_conditions :=  
          V.BinOp(V.EQ,var_type,V.Constant(V.Int(V.REG_8,1L)))
			      :: !opt_extra_conditions;*)
	var_val
       ) 
       else ( 
	 let ite_arg_expr = (get_ite_arg_expr fm var_val V.REG_64 arg_regs out_nargs) in
	 let type_11_expr = (get_typeconv_expr ite_arg_expr V.REG_32 V.CAST_SIGNED) in
	 let type_12_expr = (get_typeconv_expr ite_arg_expr V.REG_32 V.CAST_UNSIGNED) in
	 let type_21_expr = (get_typeconv_expr ite_arg_expr V.REG_16 V.CAST_SIGNED) in
	 let type_22_expr = (get_typeconv_expr ite_arg_expr V.REG_16 V.CAST_UNSIGNED) in
	 let type_31_expr = (get_typeconv_expr ite_arg_expr V.REG_8 V.CAST_SIGNED) in
	 let type_32_expr = (get_typeconv_expr ite_arg_expr V.REG_8 V.CAST_UNSIGNED) in
	 let type_41_expr = (get_typeconv_expr ite_arg_expr V.REG_1 V.CAST_SIGNED) in
	 let type_42_expr = (get_typeconv_expr ite_arg_expr V.REG_1 V.CAST_UNSIGNED) in
	 let type_43_expr = 
	   (get_ite_expr ite_arg_expr V.EQ V.REG_64 0L 
	      (V.Constant(V.Int(V.REG_64,0L))) 
	      (V.Constant(V.Int(V.REG_64,1L)))) in
	 (*opt_extra_conditions :=  
	   V.BinOp(
             V.BITOR,
             V.BinOp(V.EQ,var_type,V.Constant(V.Int(V.REG_8,1L))),
             V.BinOp(V.LT,var_val,V.Constant(V.Int(V.REG_64,out_nargs))))
			       :: !opt_extra_conditions;*)


	 get_ite_expr var_type V.EQ V.REG_8 1L var_val 
	   (get_ite_expr var_type V.EQ V.REG_8 0L ite_arg_expr
	    (get_ite_expr var_type V.EQ V.REG_8 11L type_11_expr
             (get_ite_expr var_type V.EQ V.REG_8 12L type_12_expr
	      (get_ite_expr var_type V.EQ V.REG_8 21L type_21_expr
               (get_ite_expr var_type V.EQ V.REG_8 22L type_22_expr
	        (get_ite_expr var_type V.EQ V.REG_8 31L type_31_expr
                 (get_ite_expr var_type V.EQ V.REG_8 32L type_32_expr
	          (get_ite_expr var_type V.EQ V.REG_8 41L type_41_expr
                   (get_ite_expr var_type V.EQ V.REG_8 42L type_42_expr
		      type_43_expr)
		  ))))))))
       )
      )
    in
    (*Printf.printf "setting arg=%s\n" (V.exp_to_string arg);*)
    symbolic_args := arg :: !symbolic_args;
    if n > 0 then main_loop (n-1); 
  in
  if in_nargs > 0L then  (
    main_loop ((Int64.to_int in_nargs)-1);
    List.iteri (fun index expr ->
	fm#set_reg_symbolic (List.nth arg_regs index) expr;) !symbolic_args;
  )

(* Type conversion adaptor code ends here *)


(* Floating point type conversion adaptor code starts here *)

let get_ite_ftypeconv_expr ite_arg_expr =
  V.FCast(V.CAST_FWIDEN, Vine_util.ROUND_NEAREST, V.REG_64, 
	 V.Cast(V.CAST_LOW, V.REG_32, ite_arg_expr) ) 

let float_typeconv_adaptor fm out_nargs_1 in_nargs_1 =
  Printf.printf "Starting float-typeconv adaptor\n";
  let out_nargs = (if out_nargs_1 > 4L then 4L else out_nargs_1) in
  let in_nargs = (if in_nargs_1 > 4L then 4L else in_nargs_1) in
  (* argument registers -- assumes SSE floating point *)
  let arg_regs = [R_YMM0_0; R_YMM1_0; R_YMM2_0; R_YMM3_0] in
  let symbolic_args = ref [] in
    let rec main_loop n =
    let var_name = String.make 1 (Char.chr ((Char.code 'a') + n)) in
    let var_val = fm#get_fresh_symbolic (var_name^"_f_val") 64 in
    let var_type = fm#get_fresh_symbolic (var_name^"_f_type") 8 in
    let arg =  
      (if out_nargs = 0L then (
	opt_extra_conditions :=  
          V.BinOp(V.EQ,var_type,V.Constant(V.Int(V.REG_8,1L)))
			      :: !opt_extra_conditions;
	var_val
       ) 
       else ( 
	 let ite_arg_expr = (get_ite_arg_expr fm var_val V.REG_64 arg_regs out_nargs) in
	 opt_extra_conditions :=  
	   V.BinOp(
             V.BITOR,
             V.BinOp(V.EQ,var_type,V.Constant(V.Int(V.REG_8,1L))),
             V.BinOp(V.LT,var_val,V.Constant(V.Int(V.REG_64,out_nargs))))
			       :: !opt_extra_conditions;


	 get_ite_expr var_type V.EQ V.REG_8 1L var_val 
	   (get_ite_expr var_type V.EQ V.REG_8 0L ite_arg_expr
	    ( (* Float widening cast operation on ite_arg_expr *)
	      get_ite_ftypeconv_expr ite_arg_expr
	    )
	   )
       )
      )
    in
    (*Printf.printf "setting arg=%s\n" (V.exp_to_string arg);*)
    symbolic_args := arg :: !symbolic_args;
    if n > 0 then main_loop (n-1); 
  in
  if in_nargs > 0L then  (
    main_loop ((Int64.to_int in_nargs)-1);
    List.iteri (fun index expr ->
	fm#set_reg_symbolic (List.nth arg_regs index) expr;) !symbolic_args;
  )

(* Floating point type conversion adaptor code ends here *)



(* Return value type conversion adaptor *)

let rec get_len_expr fm base_addr pos max_depth =
  (*Printf.printf 
    "get_len_expr pos = %Ld base_addr = %Lx\n" 
    pos base_addr;*)
  let b = (fm#load_byte_symbolic (Int64.add base_addr pos)) in
  if pos < max_depth then
    get_ite_expr b V.EQ V.REG_8 0L 
      (V.Constant(V.Int(V.REG_64,0L)))
      (V.BinOp(V.PLUS,V.Constant(V.Int(V.REG_64,1L)),
	       (get_len_expr fm base_addr (Int64.succ pos) max_depth)))
  else
    get_ite_expr b V.EQ V.REG_8 0L
      (V.Constant(V.Int(V.REG_64,0L)))
      (V.Constant(V.Int(V.REG_64,1L)))

let rec get_ite_saved_arg_expr fm arg_idx idx_type saved_args_list n =
  if n = 1L
  then (List.nth saved_args_list 0) 
  else get_ite_expr arg_idx V.EQ idx_type (Int64.sub n 1L) 
         (List.nth saved_args_list ((Int64.to_int n) - 1))
         (get_ite_saved_arg_expr fm arg_idx idx_type saved_args_list (Int64.sub n 1L))

(* 
   type = 0 -> leave the return value unchanged, ret_val ignored
   type = 1 -> constant in ret_val
   type = 11 -> 32-to-64 bit sign extension on inner function arg in ret_val
   type = 12 -> 32-to-64 bit zero extension on inner function arg in ret_val
   type = 21 -> 16-to-64 bit sign extension on inner function arg in ret_val
   type = 22 -> 16-to-64 bit zero extension on inner function arg in ret_val
   type = 31 -> 8-to-64 bit sign extension on inner function arg in ret_val
   type = 32 -> 8-to-64 bit zero extension on inner function arg in ret_val
   type = 41 -> 1-to-64 bit sign extension on inner function arg in ret_val
   type = 42 -> 1-to-64 bit zero extension on inner function arg in ret_val
   type = 51 -> 32-to-64 bit sign extension on return_arg, ret_val ignored
   type = 52 -> 32-to-64 bit zero extension on return_arg, ret_val ignored
   type = 53 -> 64-to-1 bit ITE operation on return_arg, ret_val ignored
   type = 61 -> 16-to-64 bit sign extension on return_arg, ret_val ignored
   type = 62 -> 16-to-64 bit zero extension on return_arg, ret_val ignored
   type = 71 -> 8-to-64 bit sign extension on return_arg, ret_val ignored
   type = 72 -> 8-to-64 bit zero extension on return_arg, ret_val ignored
   type = 81 -> 1-to-64 bit sign extension on return_arg, ret_val ignored
   type = 82 -> 1-to-64 bit zero extension on return_arg, ret_val ignored
*)

let ret_typeconv_adaptor fm in_nargs =
  Printf.printf "Starting return-typeconv adaptor\n";
  let return_arg = fm#get_reg_symbolic 
    (match !opt_arch with
    | X64 -> R_RAX
    | ARM -> R0
    | _ -> failwith "unsupported return register for architecture") in
  let (size, vine_size) = 
    match !opt_arch with 
    | X64 -> (64, V.REG_64)
    | ARM -> (32, V.REG_32)
    | _ -> failwith "argregs unsupported for architecture"
  in
  let saved_args_list = fm#get_saved_arg_regs () in
  assert((List.length saved_args_list) = (Int64.to_int in_nargs));
  let ret_val = (fm#get_fresh_symbolic ("ret_val") size) in
  let ret_type = (fm#get_fresh_symbolic ("ret_type") 8) in
  (* TODO: try using other return argument registers like XMM0 *)
  let type_51_expr = (get_typeconv_expr return_arg V.REG_32 V.CAST_SIGNED) in
  let type_52_expr = (get_typeconv_expr return_arg V.REG_32 V.CAST_UNSIGNED) in
  let type_53_expr = (get_ite_expr return_arg V.EQ vine_size 0L 
			       (V.Constant(V.Int(vine_size,0L))) 
			       (V.Constant(V.Int(vine_size,1L)))) in
  let type_61_expr = (get_typeconv_expr return_arg V.REG_16 V.CAST_SIGNED) in
  let type_62_expr = (get_typeconv_expr return_arg V.REG_16 V.CAST_UNSIGNED) in
  let type_71_expr = (get_typeconv_expr return_arg V.REG_8 V.CAST_SIGNED) in
  let type_72_expr = (get_typeconv_expr return_arg V.REG_8 V.CAST_UNSIGNED) in
  let type_81_expr = (get_typeconv_expr return_arg V.REG_1 V.CAST_SIGNED) in
  let type_82_expr = (get_typeconv_expr return_arg V.REG_1 V.CAST_UNSIGNED) in
    
  let arg =  
    (if in_nargs = 0L then (
      (*opt_extra_conditions := 
	V.BinOp(V.BITOR, 
		V.BinOp(V.LE,ret_type,V.Constant(V.Int(V.REG_8,1L))),
		V.BinOp(V.GE,ret_type,V.Constant(V.Int(V.REG_8,51L))))
			    :: !opt_extra_conditions;*)
      get_ite_expr ret_type V.EQ V.REG_8 0L return_arg
       (get_ite_expr ret_type V.EQ V.REG_8 1L ret_val
        (get_ite_expr ret_type V.EQ V.REG_8 51L type_51_expr
         (get_ite_expr ret_type V.EQ V.REG_8 52L type_52_expr
          (get_ite_expr ret_type V.EQ V.REG_8 53L type_53_expr
           (get_ite_expr ret_type V.EQ V.REG_8 61L type_61_expr
            (get_ite_expr ret_type V.EQ V.REG_8 62L type_62_expr
             (get_ite_expr ret_type V.EQ V.REG_8 71L type_71_expr
              (get_ite_expr ret_type V.EQ V.REG_8 72L type_72_expr
               (get_ite_expr ret_type V.EQ V.REG_8 81L type_81_expr 
                 type_82_expr)
	      ))))))))
    ) 
    else ( 
      let ite_saved_arg_expr = 
	(get_ite_saved_arg_expr fm ret_val vine_size saved_args_list in_nargs) in
      let type_11_expr = (get_typeconv_expr ite_saved_arg_expr V.REG_32 V.CAST_SIGNED) in
      let type_12_expr = (get_typeconv_expr ite_saved_arg_expr V.REG_32 V.CAST_UNSIGNED) in
      let type_21_expr = (get_typeconv_expr ite_saved_arg_expr V.REG_16 V.CAST_SIGNED) in
      let type_22_expr = (get_typeconv_expr ite_saved_arg_expr V.REG_16 V.CAST_UNSIGNED) in
      let type_31_expr = (get_typeconv_expr ite_saved_arg_expr V.REG_8 V.CAST_SIGNED) in
      let type_32_expr = (get_typeconv_expr ite_saved_arg_expr V.REG_8 V.CAST_UNSIGNED) in
      let type_41_expr = (get_typeconv_expr ite_saved_arg_expr V.REG_1 V.CAST_SIGNED) in
      let type_42_expr = (get_typeconv_expr ite_saved_arg_expr V.REG_1 V.CAST_UNSIGNED) in
      (* these conditions should be getting added in exec_fuzzloop before symbolic_init 
	opt_extra_conditions :=  
	V.BinOp(
          V.BITOR,
          V.BinOp(V.EQ,ret_type,V.Constant(V.Int(V.REG_8,1L))),
          V.BinOp(V.LT,ret_val,V.Constant(V.Int(V.REG_64,in_nargs))))
			    :: !opt_extra_conditions; *)
      get_ite_expr ret_type V.EQ V.REG_8 0L return_arg
	(get_ite_expr ret_type V.EQ V.REG_8 1L ret_val
	 (get_ite_expr ret_type V.EQ V.REG_8 11L type_11_expr
	  (get_ite_expr ret_type V.EQ V.REG_8 12L type_12_expr
           (get_ite_expr ret_type V.EQ V.REG_8 21L type_21_expr
            (get_ite_expr ret_type V.EQ V.REG_8 22L type_22_expr
             (get_ite_expr ret_type V.EQ V.REG_8 31L type_31_expr
              (get_ite_expr ret_type V.EQ V.REG_8 32L type_32_expr
               (get_ite_expr ret_type V.EQ V.REG_8 41L type_41_expr
                (get_ite_expr ret_type V.EQ V.REG_8 42L type_42_expr
                 (get_ite_expr ret_type V.EQ V.REG_8 51L type_51_expr
                  (get_ite_expr ret_type V.EQ V.REG_8 52L type_52_expr
                   (get_ite_expr ret_type V.EQ V.REG_8 53L type_53_expr
                    (get_ite_expr ret_type V.EQ V.REG_8 61L type_61_expr
                     (get_ite_expr ret_type V.EQ V.REG_8 62L type_62_expr
                      (get_ite_expr ret_type V.EQ V.REG_8 71L type_71_expr
                       (get_ite_expr ret_type V.EQ V.REG_8 72L type_72_expr
                        (get_ite_expr ret_type V.EQ V.REG_8 81L type_81_expr 
                          type_82_expr)
			  ))))))))))))))))
	)
    )
  in
  (*Printf.printf "setting return arg=%s\n" (V.exp_to_string arg);*)
  fm#reset_saved_arg_regs;
  fm#set_reg_symbolic ( match !opt_arch with
  | X64 -> R_RAX
  | ARM -> R0
  | _ -> failwith "unsupported architecture for ret_typeconv adaptor") 
    (V.Cast(V.CAST_LOW, V.REG_32, arg))
  
(* Return value type conversion adaptor code ends here *)


(*
   type = 0 -> leave the return value unchanged, ret_val ignored
   type = 1 -> constant in ret_val
   type = 2 -> length of normal return value
   type = 3 -> copy of an argument, ret_val counts args from zero
   type = 4 -> length of an argument, ret_val counts args from zero TODO
*)

let ret_simplelen_adaptor fm in_nargs =
  (*Printf.printf "Starting return-simplelen adaptor\n";*)
  assert(in_nargs <> 0L);
  let saved_args_list = fm#get_saved_arg_regs () in
    assert((List.length saved_args_list) = (Int64.to_int in_nargs));
    let ret_val = fm#get_fresh_symbolic "ret_val" 64 in
    let ret_type = fm#get_fresh_symbolic "ret_type" 8 in
    let return_arg = fm#get_reg_symbolic R_RAX in
    let ite_saved_arg_expr =
      get_ite_saved_arg_expr fm ret_val V.REG_64 saved_args_list in_nargs in
    let return_base_addr =
      try
	fm#get_long_var R_RAX
      with NotConcrete(_) -> 0L
    in
    let max_depth = 100L in
    let ret_len_expr =
      (if return_base_addr <> 0L then
	 get_len_expr fm return_base_addr 0L max_depth
       else
	 V.Constant(V.Int(V.REG_64, 0L))) in
    let arg =
      (get_ite_expr ret_type V.EQ V.REG_8 0L return_arg
	 (get_ite_expr ret_type V.EQ V.REG_8 1L ret_val
	    (get_ite_expr ret_type V.EQ V.REG_8 2L ret_len_expr
	       (* get_ite_expr ret_type V.EQ V.REG_8 3L*) ite_saved_arg_expr
	    )))
    in
    opt_extra_conditions :=
      V.BinOp(
	V.BITOR,
	V.BinOp(V.EQ,ret_type,V.Constant(V.Int(V.REG_8,1L))),
	V.BinOp(V.LT,ret_val,V.Constant(V.Int(V.REG_64,in_nargs))))
    :: !opt_extra_conditions;
    fm#reset_saved_arg_regs;
    (*Printf.printf "setting return arg=%s\n" (V.exp_to_string arg);*)
    fm#set_reg_symbolic R_RAX arg

(* structure adaptor for concretely-addressed memory, 
   similar implementaton in SRFM for symbolic regions *) 

(*
  target structure field key for 2 fields
  f_type = 0x011 -> 0 to 1 of concretely-addressed/symbolically-addressed memory, sign-extend to 32 bit
  f_type = 0x010 -> 0 to 1 of concretely-addressed/symbolically-addressed memory, zero-extend to 32 bit
  f_type = 0x021 -> 0 to 2 sign-extend to 32 bit
  f_type = 0x020 -> 0 to 2 zero-extend to 32 bit
  f_type = 0x041 -> 0 to 4 sign-extend to 32 bit
  f_type = 0x040 -> 0 to 4 zero-extend to 32 bit
  f_type = 0x081 -> 0 to 8 low 32 bits of 64-bit value
  
  f_type = 0x121 -> 1 to 2 sign-extend to 32 bit
  f_type = 0x120 -> 1 to 2 zero-extend to 32 bit

  f_type = 0x231 -> 2 to 3 sign-extend to 32 bit
  f_type = 0x230 -> 2 to 3 zero-extend to 32 bit
  f_type = 0x241 -> 2 to 4 sign-extend to 32 bit
  f_type = 0x240 -> 2 to 4 zero-extend to 32 bit

  f_type = 0x451 -> 4 to 5 sign-extend to 32 bit
  f_type = 0x450 -> 4 to 5 zero-extend to 32 bit
  f_type = 0x461 -> 4 to 6 sign-extend to 32 bit
  f_type = 0x460 -> 4 to 6 zero-extend to 32 bit
  f_type = 0x481 -> 4 to 8 sign-extend to 32 bit
  f_type = 0x480 -> 4 to 8 zero-extend to 32 bit

  f_type = 0x891 -> 8 to 9 sign-extend to 32 bit
  f_type = 0x890 -> 8 to 9 zero-extend to 32 bit
  f_type = 0x8a1 -> 8 to 10 sign-extend to 32 bit
  f_type = 0x8a0 -> 8 to 10 zero-extend to 32 bit
  f_type = 0x8c1 -> 8 to 12 sign-extend to 32 bit
  f_type = 0x8c0 -> 8 to 12 zero-extend to 32 bit
  f_type = none-of-the-above -> 8 to 16 low 32 bits of 64-bit value

*)

let upcast expr _extend_op end_sz =
  match _extend_op with 
  | (Some extend_op) ->  
    (match end_sz with
    | 8  -> V.Cast(extend_op, V.REG_8 , expr)
    | 16 -> V.Cast(extend_op, V.REG_16, expr)
    | 32 -> V.Cast(extend_op, V.REG_32, expr)
    | 64 -> V.Cast(extend_op, V.REG_64, expr)
    | _ -> failwith "unsupported upcast end size")
  | None -> expr

let from_concrete v sz = 
  match sz with 
  | 8 -> assert(v >= -128 && v <= 0xff);
    V.Constant(V.Int(V.REG_8,  (Int64.of_int (v land 0xff))))
  | 16 -> assert(v >= -65536 && v <= 0xffff);
    V.Constant(V.Int(V.REG_16, (Int64.of_int (v land 0xffff))))
  | 32 -> V.Constant(V.Int(V.REG_32, (Int64.logand (Int64.of_int v) 0xffffffffL)))
  | 64 -> V.Constant(V.Int(V.REG_64, (Int64.of_int v)))
  | _ -> failwith "unsupported size passed to SRFM#from_concrete"

(*
  - f1_tot_sz = f1_n * f1_sz
  - f2_tot_sz = f2_n * f2_sz
  - f3_tot_sz = f3_n * f3_sz
  - f1_p  = (- f1_tot_sz) BITAND (f2_sz-1)
  - f2_p = (- f2_tot_sz) BITAND (f3_sz-1)
  - f3_p = 0
  - f1_start = 0
  - f2_start = f1_start + f1_tot_sz + f1_p
  - f3_start = f2_start + f2_tot_sz + f2_p
*)
let t_array_field_ranges_l' = ref []
let i_array_field_ranges_l' = ref []
let i_byte_arr' = ref (Array.make 0 (ref [])) 
let i_n_arr' = ref (Array.make 0 (ref [])) 
let ranges_by_field_num = ref (Array.make 0 (ref []))
let create_field_ranges_l fm =
  (* Since we number fields from 1, 
     start array_offsets_l_h with a null entry *)
  let simplify e = 
    if !opt_split_target_formulas = true then fm#simplify_exp e else e in
  let (t_n_fields, i_n_fields, max_size) = !opt_struct_adaptor_params in
  let array_offsets_l_h = ref [(Hashtbl.create 0)] in 
  
  (* for i = 1 to n_fields do
    let f_sz_str = ("f"^(Printf.sprintf "%d" i)^"_size") in
    let f_n_str  = ("f"^(Printf.sprintf "%d" i)^"_n") in 
    let f_tot_sz_str = ("f"^(Printf.sprintf "%d" i)^"_tot_sz") in 
    let f_p_str = ("f"^(Printf.sprintf "%d" i)^"_p") in 
    let f_start_str  = ("f"^(Printf.sprintf "%d" i)^"_start") in 
    let f_sz = fm#get_fresh_symbolic f_sz_str 16 in
    let f_n  = fm#get_fresh_symbolic f_n_str 16 in
    let f_start  = fm#get_fresh_symbolic f_start_str 16 in
    let f_p = fm#get_fresh_symbolic f_p_str 16 in
    let f_tot_sz = fm#get_fresh_symbolic f_tot_sz_str 16 in
    
    fm#add_to_path_cond (V.BinOp(V.EQ, f_tot_sz, V.BinOp(V.TIMES, f_sz, f_n)));
    
    (* f1_p  = (- f1_tot_sz) BITAND (f2_sz-1), except for last field *)
    if i < n_fields then (
      let f_sz_str' = ("f"^(Printf.sprintf "%d" (i+1))^"_size") in
      let f_sz' = fm#get_fresh_symbolic f_sz_str' 16 in
      fm#add_to_path_cond 
	(V.BinOp(V.EQ, f_p, 
		 V.BinOp(V.BITAND, 
			 V.BinOp(V.MINUS, V.Constant(V.Int(V.REG_16, 0L)),
				 f_tot_sz),
			 V.BinOp(V.MINUS, f_sz', V.Constant(V.Int(V.REG_16, 1L)))
		 )));
    ) else (
      fm#add_to_path_cond (V.BinOp(V.EQ, f_p, V.Constant(V.Int(V.REG_16, 0L))));
    );

    (* f2_start = f1_start + f1_tot_sz + f1_p, except for first field *)
    if i > 1 then (
      let f_tot_sz_str' = ("f"^(Printf.sprintf "%d" (i+1))^"_tot_sz") in 
      let f_p_str' = ("f"^(Printf.sprintf "%d" (i+1))^"_p") in 
      let f_start_str'  = ("f"^(Printf.sprintf "%d" (i+1))^"_start") in 
      let f_start'  = fm#get_fresh_symbolic f_start_str' 16 in
      let f_p' = fm#get_fresh_symbolic f_p_str' 16 in
      let f_tot_sz' = fm#get_fresh_symbolic f_tot_sz_str' 16 in
      fm#add_to_path_cond 
	(V.BinOp(V.EQ, f_start, 
		 V.BinOp(V.PLUS, f_start', 
			 V.BinOp(V.PLUS, f_tot_sz', f_p'))));
    ) else (
      fm#add_to_path_cond 
	(V.BinOp(V.EQ, f_start, V.Constant(V.Int(V.REG_16, 0L))));
    );

  done; (* end for i = 1 to n_fields *) *)
  
  let get_array_field_ranges_l field_num start_byte prev_cond n_fields  =
    let get_ent f_sz_t =
      if n_fields = i_n_fields then (
	let f_sz_str = ("f"^(Printf.sprintf "%d" field_num)^"_size") in
	let f_n_str  = ("f"^(Printf.sprintf "%d" field_num)^"_n") in 
	let field_sz = 
	  if not !opt_adaptor_search_mode then 
	    Hashtbl.find adaptor_vals f_sz_str
	  else fm#get_fresh_symbolic f_sz_str 16 in
	let field_n = 
	  if not !opt_adaptor_search_mode then 
	    Hashtbl.find adaptor_vals f_n_str
	  else fm#get_fresh_symbolic f_n_str 16 in
	let new_s_b = (((start_byte+f_sz_t-1)/f_sz_t)*f_sz_t) in
	let num_bytes_remaining = 
	  (max_size - new_s_b - (n_fields - field_num)) in
	let max_n = (num_bytes_remaining/f_sz_t) in
	(* considering number of array entries to be powers of 2 *)
	let n = ref 1 in 
	while !n <= max_n do
	  let end_byte = new_s_b + (!n)*f_sz_t - 1 in
	  let cond =
	    V.BinOp(V.BITAND, prev_cond,
		    V.BinOp(V.BITAND, 
			    V.BinOp(V.EQ, field_sz, (from_concrete f_sz_t 16)),
			    V.BinOp(V.EQ, field_n,  (from_concrete !n 16)))) in
	  let cond' = simplify (
	    if Hashtbl.mem (List.nth !array_offsets_l_h field_num) 
	      (field_num, new_s_b, end_byte, !n, f_sz_t) = true then (
		let this_cond = Hashtbl.find (List.nth !array_offsets_l_h field_num) 
		  (field_num, new_s_b, end_byte, !n, f_sz_t) in
		V.BinOp(V.BITOR, this_cond, cond)
	       ) else cond ) 
	  in
	  Hashtbl.replace (List.nth !array_offsets_l_h field_num) 
	    (field_num, new_s_b, end_byte, !n, f_sz_t) cond';
	  n := !n lsl 1;
	done; ) 
      else if n_fields = t_n_fields then (
	let cond' = V.Constant(V.Int(V.REG_16, 1L)) in
	let new_s_b = (((start_byte+f_sz_t-1)/f_sz_t)*f_sz_t) in
	let num_bytes_remaining = 
	  (max_size - new_s_b - (n_fields - field_num)) in
	let max_n = (num_bytes_remaining/f_sz_t) in
	(* considering number of array entries to be powers of 2 *)
	let n = ref 1 in 
	while !n <= max_n do
	  let end_byte = new_s_b + (!n)*f_sz_t - 1 in
	  Hashtbl.replace (List.nth !array_offsets_l_h field_num) 
	    (field_num, new_s_b, end_byte, !n, f_sz_t) cond';
	  n := !n lsl 1;
	done;
      ) else failwith "n_fields is not i_n_fields or t_n_fields"
    in
    get_ent 1; get_ent 2; get_ent 4; get_ent 8;
  in
  
  let rec get_array_offsets_l field n_fields  = 
    match field with
    | 1 -> 
      get_array_field_ranges_l 1 0 (V.Constant(V.Int(V.REG_1, 1L))) n_fields ;
    | k -> 
      get_array_offsets_l (k-1) n_fields ;
      let h = (List.nth !array_offsets_l_h (k-1)) in
      Hashtbl.iter ( fun (field_num, _, end_byte, _, _) prev_cond  ->
	assert(field_num = (k-1));
	get_array_field_ranges_l k (end_byte+1) prev_cond n_fields ; 
	Printf.printf "SRFM#field=%d Hashtbl.len = %d\n" k
	  (Hashtbl.length (List.nth !array_offsets_l_h k));
      ) h;
  in

  let cmp_arr (field1, start1, end1, n1, f_sz1, _) (field2, start2, end2, n2, f_sz2, _) =
    if field1 > field2 then 1 else if field1 < field2 then -1 else (
      if start1 > start2 then 1 else if start1 < start2 then -1 else (
	if end1 > end2 then 1 else if end1 < end2 then -1 else (
	  if n1 > n2 then 1 else if n1 < n2 then -1 else (
	    if f_sz1 > f_sz2 then 1 else if f_sz1 < f_sz2 then -1 else 0
	  )
	)
      )
    )
  in
  
  let create_array_field_ranges_l n_fields = 
    array_offsets_l_h := [];
    for i = 1 to n_fields+1 do
      array_offsets_l_h := (Hashtbl.create 1000) :: !array_offsets_l_h;
    done;
    get_array_offsets_l n_fields n_fields ;
    if !opt_time_stats then
      (Printf.printf "get_array_offsets_l done...";
       flush stdout);
    let tmp_arr_off_l = ref [] in
    for i = 1 to n_fields do
      let h = (List.nth !array_offsets_l_h i) in
      Hashtbl.iter (fun (f,s,e,n,sz) c -> 
	tmp_arr_off_l := (f,s,e,n,sz,c) :: !tmp_arr_off_l;) h; 
    done;
    
    if !opt_time_stats then
      (Printf.printf "field ranges...";
       flush stdout);
    (List.sort cmp_arr !tmp_arr_off_l)
  in
  t_array_field_ranges_l' := create_array_field_ranges_l t_n_fields;
  i_array_field_ranges_l' := create_array_field_ranges_l i_n_fields;
  if !opt_trace_struct_adaptor = true then (
    Printf.printf "SRFM#i_array_field_ranges_l'.length = %d\n" (List.length !i_array_field_ranges_l');
  );
  if !opt_trace_struct_adaptor = true then (
    List.iteri ( fun ind (field_num, start_b, end_b, n, sz, cond) ->
      Printf.printf "i_array_field_ranges_l'[%d]= (%d, %d, %d, %d, %d, %s)\n"
	ind field_num start_b end_b n sz (V.exp_to_string cond);
    ) !i_array_field_ranges_l';
  );

  (* Maintaining an index on field ranges by byte position *)
  for i = 1 to max_size do
    i_byte_arr' := Array.append !i_byte_arr' (Array.make 1 (ref []));
  done;

  let rec populate_i_byte l = 
    match l with
    | (_, s, e, _, _, _)::tail -> 
      for i = s to e do
	((!i_byte_arr').(i)) := (List.hd l) :: !((!i_byte_arr').(i));
      done;
      populate_i_byte tail
    | [] -> ()
  in
  populate_i_byte !i_array_field_ranges_l';

  let i_n_arr_h = ref (Array.make 0 (Hashtbl.create 0)) in
  for i = 0 to max_size do
    (* i_n_arr' := Array.append !i_n_arr' (Array.make 1 (ref [])); *)
    i_n_arr_h := Array.append !i_n_arr_h (Array.make 1 (Hashtbl.create (max_size/2)));
  done;
 
  let rec populate_i_n l =
    match l with
    | (_, s, e, n, sz, _)::tail ->
      (* ((!i_n_arr').(n)) := (s,e,n,sz) :: !((!i_n_arr').(n)); *)
      Hashtbl.replace ((!i_n_arr_h).(n)) (s,e,n,sz) ();
      (* ((!i_n_arr').(n)) := (List.hd l) :: !((!i_n_arr').(n)); *)
      populate_i_n tail
    | [] -> ()
  in 
  populate_i_n !t_array_field_ranges_l';

  if !opt_trace_struct_adaptor = true then (
    for i=0 to max_size-1 do
      Printf.printf "i_byte_arr': for byte %d: \n" i;
      let l = !((!i_byte_arr').(i)) in
      for j=0 to (List.length l)-1 do
	let (_, s, e, _, _, _) = (List.nth l j) in
	Printf.printf "(%d, %d), " s e;
      done;
      Printf.printf "\n";
    done;
  );
  
  Printf.printf "i_byte_arr list lengths = \n";
  for i=0 to max_size-1 do
    Printf.printf "%d "(List.length !((!i_byte_arr').(i)));
  done;
  Printf.printf "\n\n";

  Printf.printf "i_n_arr_h Hashtbl lengths = \n";
  for i=0 to max_size do
    Printf.printf "%d "(Hashtbl.length ((!i_n_arr_h).(i))); 
  done;
  Printf.printf "\n\n";
 
  for i=0 to max_size do
    let l = (Hashtbl.fold (fun k () ul -> k::ul) ((!i_n_arr_h).(i)) []) in 
    i_n_arr' := Array.append !i_n_arr' (Array.make 1 (ref l));
  done;

  (* Creating an array of lists populated with ranges for each field 
     to setup side-conditions in exec_fuzzloop *)
  for i = 0 to i_n_fields do
    ranges_by_field_num := Array.append !ranges_by_field_num (Array.make 1 (ref []));
  done;
  List.iter (
    fun (f_num, s, e, _, sz, _) ->
      (!ranges_by_field_num).(f_num) := (Int64.of_int ((s lsl 32)+(e lsl 16)+1)) 
      :: !((!ranges_by_field_num).(f_num));
      if sz != 8 then
	(!ranges_by_field_num).(f_num) := (Int64.of_int ((s lsl 32)+(e lsl 16)+0)) 
	:: !((!ranges_by_field_num).(f_num));
  ) !i_array_field_ranges_l';

  if !opt_trace_struct_adaptor = true then (
    for i=0 to max_size do
      Printf.printf "i_n_arr': for entries %d: \n" i;
      let l = !((!i_n_arr').(i)) in
      for j=0 to (List.length l)-1 do
	let (s, e, n, sz) = (List.nth l j) in
	Printf.printf "(%d, %d, %d, %d), " s e n sz;
      done;
      Printf.printf "\n";
    done;
  )


let struct_adaptor (fm:fragment_machine) = 
  let from_concrete v sz = 
    match sz with 
    | 8 -> assert(v >= -128 && v <= 0xff);
      V.Constant(V.Int(V.REG_8,  (Int64.of_int (v land 0xff))))
    | 16 -> assert(v >= -65536 && v <= 0xffff);
      V.Constant(V.Int(V.REG_16, (Int64.of_int (v land 0xffff))))
    | 32 -> V.Constant(V.Int(V.REG_32, (Int64.logand (Int64.of_int v) 0xffffffffL)))
    | 64 -> V.Constant(V.Int(V.REG_64, (Int64.of_int v)))
    | _ -> failwith "unsupported size passed to AS#from_concrete"
  in
  let get_byte expr pos =
    V.Cast(V.CAST_LOW, V.REG_8, 
	   V.BinOp(V.RSHIFT, expr, (from_concrete (pos*8) 8)))
  in
  (* This simplifies formulas and introduces t-variables for comple
     sub-expressions. Doing this generally speeds things up, but it
     may make debugging the formulas less convenient, so you can disable
     it by make "simplify" be the identity function. *)
  let simplify e = fm#simplify_exp e in
  (* let simplify e = e in *)

  let start_time = Sys.time () in
  if (List.length !opt_synth_struct_adaptor) <> 0 then (
    if !opt_trace_struct_adaptor = true then
      Printf.printf "Starting structure adaptor\n";
    if !opt_time_stats then
      (Printf.printf "Generating structure adaptor formulas...";
       flush stdout);
    List.iteri ( fun addr_list_ind addr -> 
      if !opt_time_stats then
	(Printf.printf "(0x%08Lx)..." addr;
	 flush stdout);
      if (Int64.abs (fix_s32 addr)) > 4096L then (
	let (t_n_fields, i_n_fields, max_size) = !opt_struct_adaptor_params in

(* Commenting out for field_ranges_l starts here *)
(*	let get_array_field_ranges_l field_num start_byte =
	  let get_ent f_sz_t =
	    let ret_offsets_l = ref [] in
	    let f_sz_str = ("f"^(Printf.sprintf "%d" field_num)^"_size") in
	    let f_n_str  = ("f"^(Printf.sprintf "%d" field_num)^"_n") in 
	    let field_sz = fm#get_fresh_symbolic f_sz_str 16 in
	    let field_n  = fm#get_fresh_symbolic f_n_str 16 in
	    let new_s_b = (((start_byte+f_sz_t-1)/f_sz_t)*f_sz_t) in
	    let num_bytes_remaining = 
	      (max_size - new_s_b - (n_fields - field_num)) in
	    let max_n = (num_bytes_remaining/f_sz_t) in
	    for n = 1 to max_n do
	      let end_byte = new_s_b + n*f_sz_t - 1 in
	      let cond = 
		V.BinOp(V.BITAND, 
			V.BinOp(V.EQ, field_sz, (from_concrete f_sz_t 16)),
			V.BinOp(V.EQ, field_n,  (from_concrete n 16))) in
	      ret_offsets_l := (field_num, new_s_b, end_byte, n, f_sz_t, cond) 
	      :: !ret_offsets_l; 
	    done;
	    !ret_offsets_l
	  in
	  (get_ent 1) @ (get_ent 2) @ (get_ent 4) @ (get_ent 8)
	in
	let rec get_array_offsets_l field = 
	  match field with
	  | 1 -> get_array_field_ranges_l 1 0 
	  | k -> 
	    let ret_offsets_l = ref [] in
	    let offsets_l = get_array_offsets_l (k-1) in
	    List.iter ( fun (field_num, _, end_byte, _, _, cond) ->
	      if field_num = k-1 then (
		List.iter ( fun (field_num, start_b, end_b, n, f_sz, this_field_cond) ->
		  let cond' = V.BinOp(V.BITAND, cond, this_field_cond) in
		  let cond' = simplify cond' in
		  ret_offsets_l := (field_num, start_b, end_b, n, f_sz, cond') 
		  :: !ret_offsets_l;
		) (get_array_field_ranges_l k (end_byte+1)););
	    ) offsets_l;
	    Printf.printf "AS#ret_offsets_l.len = %d offsets_l.len = %d\n" 
	      (List.length !ret_offsets_l) (List.length offsets_l);
	    (* (!ret_offsets_l @ offsets_l) *)
	    (List.rev_append !ret_offsets_l offsets_l)
	in

	let cmp_arr (field1,start1,end1, n1, f_sz1, _) (field2, start2, end2, n2, f_sz2, _) =
	  if field1 > field2 then 1 else if field1 < field2 then -1 else (
	    if start1 > start2 then 1 else if start1 < start2 then -1 else (
	      if end1 > end2 then 1 else if end1 < end2 then -1 else (
		if n1 > n2 then 1 else if n1 < n2 then -1 else (
		  if f_sz1 > f_sz2 then 1 else if f_sz1 < f_sz2 then -1 else 0
		)
	      )
	    )
	  )
	in
	let tmp_l = ref [] in
	let rec merge_same_field_ranges l =
	  match l with
	  | [] -> ()
	  | [a] -> tmp_l := a :: !tmp_l;()
	  | (field1, start1, end1, n1, f_sz1, cond1)::t ->
	    let same_field_range = ref true in
	    let cond = ref cond1 in
	    let tail = ref t in
	    while !same_field_range do
	      match !tail with
	      | [] -> same_field_range:= false;
	      | (field2, start2, end2, n2, f_sz2, cond2)::t2 ->
		if (field1=field2) && (start1=start2) && (end1=end2) && (n1=n2) 
		  && (f_sz1=f_sz2) then (
		    assert(cond1 <> cond2);
		    cond := simplify (V.BinOp(V.BITOR, !cond, cond2));
		    tail := t2;
		  ) 
		else 
		  same_field_range := false; 
	    done;
	    tmp_l := (field1, start1, end1, n1, f_sz1, !cond) :: !tmp_l;
	    (merge_same_field_ranges !tail)
	in
	let unique = Vine_util.list_unique in
	if !opt_time_stats then
	  (Printf.printf "field ranges...";
	   flush stdout);
	merge_same_field_ranges (List.sort cmp_arr 
				   (unique (get_array_offsets_l n_fields)));
	
	let array_field_ranges_l = (List.rev !tmp_l) in *)
(* Commenting out for field_ranges_l ends here *)

(*	if !opt_trace_struct_adaptor = true then
	  Printf.printf "AS#array_field_ranges_l.length = %d\n" (List.length array_field_ranges_l);
	if !opt_trace_struct_adaptor = true then
	  List.iteri ( fun ind (field_num, start_b, end_b, _, _, cond) ->
	    Printf.printf "array_field_ranges_l[%d]= (%d, %x, %x, %s)\n"
	      ind field_num start_b end_b (V.exp_to_string cond);
	  ) array_field_ranges_l;

	let i_byte_arr = ref (Array.make 0 (ref [])) in
	for i = 1 to max_size do
	  i_byte_arr := Array.append !i_byte_arr (Array.make 1 (ref []));
	done;
	
	let rec populate_i_byte l = 
	  match l with
	  | (_, s, e, _, _, _)::tail -> 
	    for i = s to e do
	      ((!i_byte_arr).(i)) := (List.hd l) :: !((!i_byte_arr).(i));
	    done;
	    populate_i_byte tail
	  | [] -> ()
	in
	populate_i_byte array_field_ranges_l;

	let i_n_arr = ref (Array.make 0 (ref [])) in
	for i = 0 to max_size do
	  i_n_arr := Array.append !i_n_arr (Array.make 1 (ref []));
	done;
	let rec populate_i_n l =
	  match l with
	  | (_, _, _, n, sz, _)::tail ->
	    ((!i_n_arr).(n)) := (List.hd l) :: !((!i_n_arr).(n));
	      populate_i_n tail
	  | [] -> ()
	in 
	populate_i_n array_field_ranges_l;
	
	if !opt_trace_struct_adaptor = true then (
	  for i=0 to max_size-1 do
	    Printf.printf "for byte %d: \n" i;
	    let l = !((!i_byte_arr).(i)) in
	    for j=0 to (List.length l)-1 do
	      let (_, s, e, _, _, _) = (List.nth l j) in
	      Printf.printf "(%d, %d), " s e;
	    done;
	    Printf.printf "\n";
	  done;
	);

	if !opt_trace_struct_adaptor = true then (
	  for i=0 to max_size do
	    Printf.printf "i_n_arr: for entries %d: \n" i;
	    let l = !((!i_n_arr).(i)) in
	    for j=0 to (List.length l)-1 do
	      let (_, s, e, _, _, _) = (List.nth l j) in
	      Printf.printf "(%d, %d), " s e;
	    done;
	    Printf.printf "\n";
	    done;
	);
*)
	
	let rec get_arr_t_field_expr field_num this_array_field_ranges_l 
	    ai_byte ai_f_sz ai_n =
	  (* Assume ai_n equals target_n for now *)
	  let get_ai_byte_expr target_n target_sz start_addr ex_op =
	    let cast_op =
	      if target_sz < ai_f_sz then 
		if ex_op = 1 then (Some V.CAST_SIGNED) 
		else (Some V.CAST_UNSIGNED)
	      else if target_sz > ai_f_sz then (Some V.CAST_LOW)
	      else None
	    in
	    (* translate ai_byte to a t_byte by using ai_f_sz and t_sz *)
	    let ai_q = ai_byte/ai_f_sz in
	    let ai_r = ai_byte mod ai_f_sz in
	    let tmp_addr = Int64.add start_addr (Int64.of_int (ai_q*target_sz)) in
	    let ai_entry = 
		upcast (fm#load_sym tmp_addr (target_sz*8)) cast_op (ai_f_sz*8) 
	    in 
	    get_byte ai_entry ai_r
	  in
	  match this_array_field_ranges_l with
	  | [] -> failwith "AS#get_arr_t_field_expr ran out of this_array_field_ranges_l"
	  | [(start_byte, end_byte, n, f_sz)] -> 
	    assert(n = ai_n);
	    let start_addr = (Int64.add addr (Int64.of_int start_byte)) in
	    get_ai_byte_expr n f_sz start_addr 1
	  | (start_byte, end_byte, n, f_sz)::tail ->
	    assert(n = ai_n);
	    let start_addr = (Int64.add addr (Int64.of_int start_byte)) in
	    let is_extend_req = (f_sz - 8) in
	    if is_extend_req <> 0 then (
	      let sign_extend_val = Int64.of_int ((start_byte lsl 32)+(end_byte lsl 16)+1) in 
	      let zero_extend_val = Int64.of_int ((start_byte lsl 32)+(end_byte lsl 16)+0) in 
	      if (n = ai_n) then (
		  let f_type_str = "f"^(Printf.sprintf "%d" field_num)^"_type" in
		  let f_type = fm#get_fresh_symbolic f_type_str 64 in
		  let sign_extend_expr = get_ai_byte_expr n f_sz start_addr 1 in
		  let zero_extend_expr = get_ai_byte_expr n f_sz start_addr 0 in
		  
		  let else_expr =
		    simplify
		      (get_arr_t_field_expr field_num tail
			 ai_byte ai_f_sz ai_n ) in
		  
		  get_ite_expr f_type V.EQ V.REG_64 sign_extend_val sign_extend_expr 
		    (get_ite_expr f_type V.EQ V.REG_64 zero_extend_val zero_extend_expr
		       else_expr )
		  ) else (
		  simplify (get_arr_t_field_expr field_num tail
			      ai_byte ai_f_sz ai_n )
		  )
	    ) else (
	      let sign_extend_val = Int64.of_int ((start_byte lsl 32)+(end_byte lsl 16)+1) in 
	      if (ai_n = n) then (
		let f_type_str = "f"^(Printf.sprintf "%d" field_num)^"_type" in
		let f_type = fm#get_fresh_symbolic f_type_str 64 in
		let sign_extend_expr = get_ai_byte_expr n f_sz start_addr 1 in

		let else_expr =
		  simplify
		    (get_arr_t_field_expr field_num tail
		       ai_byte ai_f_sz ai_n ) in
		
		get_ite_expr f_type V.EQ V.REG_64 sign_extend_val sign_extend_expr 
		  else_expr
	      ) else (
		  simplify (get_arr_t_field_expr field_num tail
			      ai_byte ai_f_sz ai_n )
	      )
	    )
	in
	let field_exprs = Hashtbl.create 1001 in
	let t_field_h = Hashtbl.create 1000 in
	let rec get_arr_ite_ai_byte_expr this_array_field_ranges_l i_byte = 
	  (* i_byte = interesting_byte *)
	  match this_array_field_ranges_l with
	  | [] -> from_concrete 0 8
	  | (field, start_byte, end_byte, ai_n, ai_f_sz, cond)::tail ->
	    if (i_byte >= start_byte) && (i_byte <= end_byte) then (
	      let field_size_temp_str = "arr_as_t_field_"^
		(Printf.sprintf "%d_n%d_sz%d_b%d_%d" field ai_n ai_f_sz 
		   (i_byte-start_byte) addr_list_ind)
	      in
	      let field_size_temp = fm#get_fresh_symbolic field_size_temp_str 8 in

	      let q_exp = 
		(try
                   Hashtbl.find field_exprs field_size_temp_str
                 with Not_found ->
                   let new_q_exp =
		     V.BinOp(V.EQ, field_size_temp,
			     (get_arr_t_field_expr field 
				(List.rev !((!i_n_arr').(ai_n))) (* array_field_ranges_l *)
				(i_byte-start_byte) ai_f_sz ai_n )) in
		     Hashtbl.replace field_exprs field_size_temp_str new_q_exp;
		     fm#add_to_path_cond new_q_exp;
		     new_q_exp)
	      in

	      if !opt_trace_struct_adaptor = true then
		Hashtbl.replace t_field_h field_size_temp q_exp;
	      
	      V.Ite(cond, field_size_temp, 
		    (get_arr_ite_ai_byte_expr tail i_byte ))
	    ) else (
	      get_arr_ite_ai_byte_expr tail i_byte 
	    )
	in
	if !opt_time_stats then
	  (Printf.printf "byte expressions...";
	   flush stdout);
	let byte_expr_l = ref [] in 
	for i=0 to (max_size-1) do 
	  let byte_expr = (get_arr_ite_ai_byte_expr (List.rev !((!i_byte_arr').(i))) i) in
	  let byte_expr_sym_str = "arr_ai_byte_"^(Printf.sprintf "%d_%d" i addr_list_ind) in
	  let byte_expr_sym = fm#get_fresh_symbolic byte_expr_sym_str 8 in
	  let q_exp = V.BinOp(V.EQ, byte_expr_sym, byte_expr) in
	  if !opt_trace_struct_adaptor = true then
	    Printf.printf "AS#get_arr_ite_ai_byte_expr for byte %d: %s\n\n" i
	      (V.exp_to_string q_exp);
	  fm#add_to_path_cond q_exp; 
	  byte_expr_l := byte_expr_sym :: !byte_expr_l;
	done;
	byte_expr_l := (List.rev !byte_expr_l);

	if !opt_trace_struct_adaptor = true then
	  Hashtbl.iter (fun key value ->
	    Printf.printf "AS#apply_struct_adaptor t_field_h[%s] = %s\n" 
	      (V.exp_to_string key) (V.exp_to_string value);
	  ) t_field_h; 
	
	for i=0 to (max_size-1) do
	  fm#store_sym (Int64.add addr (Int64.of_int i)) 8 (List.nth !byte_expr_l i);
	done;
	
      );
      
    ) !opt_synth_struct_adaptor;
  );
  if !opt_time_stats then
    (Printf.printf "AS#ready to apply (%f sec).\n" (Sys.time () -. start_time);
     flush stdout);
  fm#sym_region_struct_adaptor;
