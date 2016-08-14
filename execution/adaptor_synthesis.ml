(* Extra file with helper code for adaptor synthesis. The functions 
   defined here are used in exec_fuzzloop.ml and exec_runloop.ml *)

module V = Vine;;

open Fragment_machine;;
open Exec_options;;
open Exec_exceptions;;
open Exec_utils;;

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
      let node_type = fm#get_fresh_symbolic (var ^ "_type_" ^ base) 8 in
      let node_val = fm#get_fresh_symbolic (var ^ "_val_" ^ base) 
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
    let node_type = fm#get_fresh_symbolic (var_name ^ "_type_" ^ base) 8 in
    let node_val = fm#get_fresh_symbolic (var_name ^ "_val_" ^ base)
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
      let node_type = fm#get_fresh_symbolic (var_name ^ "_type_" ^ base) 8 in
      let node_val = fm#get_fresh_symbolic (var_name ^ "_val_" ^ base)
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
let int_arith_depth = 3
(* 32 or 64-bit values (int vs. long int) *)
let int_val_type = V.REG_32
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
let int_restrict_constant_range = None
let int_restrict_constant_list = None
(* restrict the input and output of the adaptor (input restrictions reflect
   f1 preconditions and output restrictions reflect f2 preconditions)
   int_restrict_X_range should be 'None' or 'Some (lower, upper)' and 
   int_restrict_X_list should be 'None' or 'Some [v1; v2; ...; vn]' (NOTE:
   this list must contain zero if used) *)
let int_restrict_input_range = None
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
  let arg_regs = [R_RDI;R_RSI;R_RDX;R_RCX;R_R8;R_R9] in
  let symbolic_args = ref [] in
  let rec main_loop n =
    let var_name = String.make 1 (Char.chr ((Char.code 'a') + n)) in
    let var_val = fm#get_fresh_symbolic (var_name^"_val") 64 in
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
	 (*opt_extra_conditions :=  
	   V.BinOp(
             V.BITOR,
             V.BinOp(V.EQ,var_is_const,V.Constant(V.Int(V.REG_1,1L))),
             V.BinOp(V.LT,var_val,V.Constant(V.Int(V.REG_64,out_nargs))))
	 :: !opt_extra_conditions;*)
	 get_ite_expr var_is_const V.NEQ V.REG_1 0L  
	   var_val (get_ite_arg_expr fm var_val V.REG_64 arg_regs out_nargs))) in
    (* Printf.printf "setting arg=%s\n" (V.exp_to_string arg); *)
    symbolic_args := arg :: !symbolic_args;
    if n > 0 then main_loop (n-1); 
  in
  if in_nargs > 0L then  (
    main_loop ((Int64.to_int in_nargs)-1);
    List.iteri (fun index expr ->
	fm#set_reg_symbolic (List.nth arg_regs index) expr;) !symbolic_args;
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
  V.Cast(extend_op, V.REG_64, 
	 (V.Cast(V.CAST_LOW, src_type, src_operand))
  )

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
  let arg_regs = [R_RDI;R_RSI;R_RDX;R_RCX;R_R8;R_R9] in
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
  let saved_args_list = fm#get_saved_arg_regs () in
  assert((List.length saved_args_list) = (Int64.to_int in_nargs));
  let ret_val = (fm#get_fresh_symbolic ("ret_val") 64) in
  let ret_type = (fm#get_fresh_symbolic ("ret_type") 8) in
  (* TODO: try using other return argument registers like XMM0 *)
  let return_arg = fm#get_reg_symbolic R_RAX in
  let type_51_expr = (get_typeconv_expr return_arg V.REG_32 V.CAST_SIGNED) in
  let type_52_expr = (get_typeconv_expr return_arg V.REG_32 V.CAST_UNSIGNED) in
  let type_53_expr = (get_ite_expr return_arg V.EQ V.REG_64 0L 
			       (V.Constant(V.Int(V.REG_64,0L))) 
			       (V.Constant(V.Int(V.REG_64,1L)))) in
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
	(get_ite_saved_arg_expr fm ret_val V.REG_64 saved_args_list in_nargs) in
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
  fm#set_reg_symbolic R_RAX arg
  
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
  f1_type = 011 -> 0 to 1 of concretely-addressed/symbolically-addressed memory, sign-extend to 32 bit
  f1_type = 010 -> 0 to 1 of concretely-addressed/symbolically-addressed memory, zero-extend to 32 bit
  f1_type = 021 -> 0 to 2 sign-extend to 32 bit
  f1_type = 020 -> 0 to 2 zero-extend to 32 bit
  f1_type = 041 -> 0 to 4 sign-extend to 32 bit
  f1_type = 040 -> 0 to 4 zero-extend to 32 bit
  f1_type = 08  -> 0 to 8 low 32 bits of 64-bit value
  
  f2_type = 111 -> 1 to 2 sign-extend to 32 bit
  f2_type = 110 -> 1 to 2 zero-extend to 32 bit
  f2_type = 121 -> 1 to 3 sign-extend to 32 bit
  f2_type = 120 -> 1 to 3 zero-extend to 32 bit

  f2_type = 211 -> 2 to 3 sign-extend to 32 bit
  f2_type = 210 -> 2 to 3 zero-extend to 32 bit
  f2_type = 221 -> 2 to 4 sign-extend to 32 bit
  f2_type = 220 -> 2 to 4 zero-extend to 32 bit

  f2_type = 411 -> 4 to 5 sign-extend to 32 bit
  f2_type = 410 -> 4 to 5 zero-extend to 32 bit
  f2_type = 421 -> 4 to 6 sign-extend to 32 bit
  f2_type = 420 -> 4 to 6 zero-extend to 32 bit
  f2_type = 441 -> 4 to 8 sign-extend to 32 bit
  f2_type = 440 -> 4 to 8 zero-extend to 32 bit
  f2_type = 48  -> 4 to 12 low 32 bits of 64-bit value

  f2_type = 811 -> 8 to 9 sign-extend to 32 bit
  f2_type = 810 -> 8 to 9 zero-extend to 32 bit
  f2_type = 821 -> 8 to 10 sign-extend to 32 bit
  f2_type = 820 -> 8 to 10 zero-extend to 32 bit
  f2_type = 841 -> 8 to 12 sign-extend to 32 bit
  f2_type = 840 -> 8 to 12 zero-extend to 32 bit
  f2_type = 88  -> 8 to 16 low 32 bits of 64-bit value

*)

let upcast expr extend_op end_sz =
  match end_sz with
  | 32 -> V.Cast(extend_op, V.REG_32, expr)
  | 64 -> V.Cast(extend_op, V.REG_64, expr)
  | _ -> failwith "unsupported upcast end size"

let struct_adaptor fm = 
  if (List.length !opt_synth_struct_adaptor) <> 0 then (
    Printf.printf "Starting structure adaptor\n";
    let (addr1, addr2, addr3, addr4, addr5, addr6, addr7, addr8, addr9, addr10) = 
      (List.hd !opt_synth_struct_adaptor) in
    let addr_list = [addr1; addr2; addr3; addr4; addr5; 
		     addr6; addr7; addr8; addr9; addr10] in
    List.iter ( fun addr -> 
      if (Int64.abs (fix_s32 addr)) > 4096L then (
	let f1_type = fm#get_fresh_symbolic "f1_type" 8 in
	let f2_type = fm#get_fresh_symbolic "f2_type" 8 in
	let addr_1 = (Int64.add addr 1L) in
	let addr_2 = (Int64.add addr 2L) in
	let addr_4 = (Int64.add addr 4L) in
	let addr_8 = (Int64.add addr 8L) in
	
	let f1_val_0_1_1  = upcast (fm#load_sym addr 8 ) V.CAST_SIGNED   32 in
	let f1_val_0_1_0  = upcast (fm#load_sym addr 8 ) V.CAST_UNSIGNED 32 in
	let f1_val_0_2_1  = upcast (fm#load_sym addr 16) V.CAST_SIGNED   32 in
	let f1_val_0_2_0  = upcast (fm#load_sym addr 16) V.CAST_UNSIGNED 32 in
	let f1_val_0_4_1  = upcast (fm#load_sym addr 32) V.CAST_SIGNED   32 in
	let f1_val_0_4_0  = upcast (fm#load_sym addr 32) V.CAST_UNSIGNED 32 in
	let f1_val_0_8    = upcast (fm#load_sym addr 64) V.CAST_LOW      32 in

	let f2_val_1_1_1  = upcast (fm#load_sym addr_1 8 ) V.CAST_SIGNED   32 in
	let f2_val_1_1_0  = upcast (fm#load_sym addr_1 8 ) V.CAST_UNSIGNED 32 in
	let f2_val_1_2_1  = upcast (fm#load_sym addr_1 16) V.CAST_SIGNED   32 in
	let f2_val_1_2_0  = upcast (fm#load_sym addr_1 16) V.CAST_UNSIGNED 32 in
	
	let f2_val_2_1_1  = upcast (fm#load_sym addr_2 8 ) V.CAST_SIGNED   32 in
	let f2_val_2_1_0  = upcast (fm#load_sym addr_2 8 ) V.CAST_UNSIGNED 32 in
	let f2_val_2_2_1  = upcast (fm#load_sym addr_2 16) V.CAST_SIGNED   32 in
	let f2_val_2_2_0  = upcast (fm#load_sym addr_2 16) V.CAST_UNSIGNED 32 in
	
	let f2_val_4_1_1  = upcast (fm#load_sym addr_4 8 ) V.CAST_SIGNED   32 in
	let f2_val_4_1_0  = upcast (fm#load_sym addr_4 8 ) V.CAST_UNSIGNED 32 in
	let f2_val_4_2_1  = upcast (fm#load_sym addr_4 16) V.CAST_SIGNED   32 in
	let f2_val_4_2_0  = upcast (fm#load_sym addr_4 16) V.CAST_UNSIGNED 32 in
	let f2_val_4_4_1  = upcast (fm#load_sym addr_4 32) V.CAST_SIGNED   32 in
	let f2_val_4_4_0  = upcast (fm#load_sym addr_4 32) V.CAST_UNSIGNED 32 in
	let f2_val_4_8    = upcast (fm#load_sym addr_4 64) V.CAST_LOW      32 in

	let f2_val_8_1_1  = upcast (fm#load_sym addr_8 8 ) V.CAST_SIGNED   32 in
	let f2_val_8_1_0  = upcast (fm#load_sym addr_8 8 ) V.CAST_UNSIGNED 32 in
	let f2_val_8_2_1  = upcast (fm#load_sym addr_8 16) V.CAST_SIGNED   32 in
	let f2_val_8_2_0  = upcast (fm#load_sym addr_8 16) V.CAST_UNSIGNED 32 in
	let f2_val_8_4_1  = upcast (fm#load_sym addr_8 32) V.CAST_SIGNED   32 in
	let f2_val_8_4_0  = upcast (fm#load_sym addr_8 32) V.CAST_UNSIGNED 32 in
	let f2_val_8_8    = upcast (fm#load_sym addr_8 64) V.CAST_LOW      32 in

	let field1_expr = 
           get_ite_expr f1_type V.EQ V.REG_8 11L f1_val_0_1_1 
          (get_ite_expr f1_type V.EQ V.REG_8 10L f1_val_0_1_0 
          (get_ite_expr f1_type V.EQ V.REG_8 21L f1_val_0_2_1 
          (get_ite_expr f1_type V.EQ V.REG_8 20L f1_val_0_2_0 
	  (get_ite_expr f1_type V.EQ V.REG_8 41L f1_val_0_4_1 
          (get_ite_expr f1_type V.EQ V.REG_8 40L f1_val_0_4_0 
          (get_ite_expr f1_type V.EQ V.REG_8 8L f1_val_0_8
          (get_ite_expr f1_type V.EQ V.REG_8 111L f2_val_1_1_1
          (get_ite_expr f1_type V.EQ V.REG_8 110L f2_val_1_1_0
          (get_ite_expr f1_type V.EQ V.REG_8 121L f2_val_1_2_1
          (get_ite_expr f1_type V.EQ V.REG_8 120L f2_val_1_2_0
          (get_ite_expr f1_type V.EQ V.REG_8 211L f2_val_2_1_1
          (get_ite_expr f1_type V.EQ V.REG_8 210L f2_val_2_1_0
          (get_ite_expr f1_type V.EQ V.REG_8 221L f2_val_2_2_1
          (get_ite_expr f1_type V.EQ V.REG_8 220L f2_val_2_2_0
          (get_ite_expr f1_type V.EQ V.REG_8 411L f2_val_4_1_1
          (get_ite_expr f1_type V.EQ V.REG_8 410L f2_val_4_1_0
          (get_ite_expr f1_type V.EQ V.REG_8 421L f2_val_4_2_1
          (get_ite_expr f1_type V.EQ V.REG_8 420L f2_val_4_2_0
          (get_ite_expr f1_type V.EQ V.REG_8 441L f2_val_4_4_1
          (get_ite_expr f1_type V.EQ V.REG_8 440L f2_val_4_4_0
          (get_ite_expr f1_type V.EQ V.REG_8 48L f2_val_4_8
          (get_ite_expr f1_type V.EQ V.REG_8 811L f2_val_8_1_1
          (get_ite_expr f1_type V.EQ V.REG_8 810L f2_val_8_1_0
          (get_ite_expr f1_type V.EQ V.REG_8 821L f2_val_8_2_1
          (get_ite_expr f1_type V.EQ V.REG_8 820L f2_val_8_2_0
          (get_ite_expr f1_type V.EQ V.REG_8 841L f2_val_8_4_1 
          (get_ite_expr f1_type V.EQ V.REG_8 840L f2_val_8_4_0 
          f2_val_8_8 )))))))))))))))))))))))))))
	in
	let field2_expr = 
           get_ite_expr f2_type V.EQ V.REG_8 11L f1_val_0_1_1 
          (get_ite_expr f2_type V.EQ V.REG_8 10L f1_val_0_1_0 
          (get_ite_expr f2_type V.EQ V.REG_8 21L f1_val_0_2_1 
          (get_ite_expr f2_type V.EQ V.REG_8 20L f1_val_0_2_0 
	  (get_ite_expr f2_type V.EQ V.REG_8 41L f1_val_0_4_1 
          (get_ite_expr f2_type V.EQ V.REG_8 40L f1_val_0_4_0 
          (get_ite_expr f2_type V.EQ V.REG_8 8L f1_val_0_8
          (get_ite_expr f2_type V.EQ V.REG_8 111L f2_val_1_1_1
          (get_ite_expr f2_type V.EQ V.REG_8 110L f2_val_1_1_0
          (get_ite_expr f2_type V.EQ V.REG_8 121L f2_val_1_2_1
          (get_ite_expr f2_type V.EQ V.REG_8 120L f2_val_1_2_0
          (get_ite_expr f2_type V.EQ V.REG_8 211L f2_val_2_1_1
          (get_ite_expr f2_type V.EQ V.REG_8 210L f2_val_2_1_0
          (get_ite_expr f2_type V.EQ V.REG_8 221L f2_val_2_2_1
          (get_ite_expr f2_type V.EQ V.REG_8 220L f2_val_2_2_0
          (get_ite_expr f2_type V.EQ V.REG_8 411L f2_val_4_1_1
          (get_ite_expr f2_type V.EQ V.REG_8 410L f2_val_4_1_0
          (get_ite_expr f2_type V.EQ V.REG_8 421L f2_val_4_2_1
          (get_ite_expr f2_type V.EQ V.REG_8 420L f2_val_4_2_0
          (get_ite_expr f2_type V.EQ V.REG_8 441L f2_val_4_4_1
          (get_ite_expr f2_type V.EQ V.REG_8 440L f2_val_4_4_0
          (get_ite_expr f2_type V.EQ V.REG_8 48L f2_val_4_8
          (get_ite_expr f2_type V.EQ V.REG_8 811L f2_val_8_1_1
          (get_ite_expr f2_type V.EQ V.REG_8 810L f2_val_8_1_0
          (get_ite_expr f2_type V.EQ V.REG_8 821L f2_val_8_2_1
          (get_ite_expr f2_type V.EQ V.REG_8 820L f2_val_8_2_0
          (get_ite_expr f2_type V.EQ V.REG_8 841L f2_val_8_4_1 
          (get_ite_expr f2_type V.EQ V.REG_8 840L f2_val_8_4_0 
          f2_val_8_8 )))))))))))))))))))))))))))
	in
	fm#store_sym addr 32 field1_expr;
	fm#store_sym (Int64.add addr 4L) 32 field2_expr;
      );
      
    ) addr_list;
    fm#apply_struct_adaptor ();
    
  );
