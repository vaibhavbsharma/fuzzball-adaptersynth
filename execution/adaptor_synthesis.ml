(* Extra file with helper code for adaptor synthesis. The functions 
   defined here are used in exec_fuzzloop.ml and exec_runloop.ml *)

module V = Vine;;

open Fragment_machine;;
open Exec_options;;
open Exec_exceptions;;

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
| v'::[] -> 
    V.BinOp(V.BITOR, 
            V.BinOp(V.EQ, v, V.Constant(V.Int(v_type, v'))),
            V.BinOp(V.EQ, v, V.Constant(V.Int(v_type, 0L))))
| v'::t -> 
    V.BinOp(V.BITOR, 
            V.BinOp(V.EQ, v, V.Constant(V.Int(v_type, v'))),
            specify_vals v v_type t)

(* build an arithmetic expression tree; this function is a little messy because 
   it takes so many arguments, but it's useful to reuse code between the integer 
   and floating point adaptor code *)
let get_arithmetic_expr fm var arg_regs val_type out_nargs get_oper_expr depth =
  let rec build_tree d base =
    if d <= 0 then failwith "Bad tree depth for arithmetic adaptor"
    else 
      let node_type = fm#get_fresh_symbolic (var ^ "_type_" ^ base) 8 in
      let node_val = fm#get_fresh_symbolic (var ^ "_val_" ^ base) 
                       (if val_type = V.REG_32 then 32 else 64) in
      if d = 1 
      then get_ite_expr node_type V.EQ V.REG_8 0L 
             node_val 
             (let reg_expr = get_ite_arg_expr fm node_val val_type arg_regs out_nargs in
              if val_type = V.REG_32 
              then V.Cast(V.CAST_LOW, V.REG_32, reg_expr)
              else reg_expr)
      else
        let left_expr = build_tree (d-1) (base ^ "0") in
        let right_expr = build_tree (d-1) (base ^ "1") in
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
               or be one of the specified values *)
          synth_extra_conditions := 
            (V.BinOp(V.LE, node_type, V.Constant(V.Int(V.REG_8, 1L)))) ::
            (V.BinOp(
               V.BITOR,
               V.BinOp(V.NEQ, node_type, V.Constant(V.Int(V.REG_8, 1L))),
               V.BinOp(V.LT, node_val, V.Constant(V.Int(val_type, out_nargs))))) :: 
            (restrict_const_node node_type node_val) ::
            !synth_extra_conditions
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
               in the right subtree must be zero *)
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
            !synth_extra_conditions;
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
   V.NEG; V.NOT *)
let int_binops = [V.PLUS; V.BITAND; V.BITOR; V.XOR; V.LSHIFT; V.RSHIFT; V.ARSHIFT]
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
let int_restrict_output_range = None (* TODO *)
let int_restrict_output_list = None (* TODO *)

(* creates symbolic variables representing the adaptor function and encodes
   the rules for applying the adaptor function; this function is called in 
   exec_runloop *)
let arithmetic_int_adaptor fm out_nargs in_nargs =
  (* argument registers -- assumes x86-64 *)
  let arg_regs = [R_RDI;R_RSI;R_RDX;R_RCX;R_R8;R_R9] in
  (* operators that require special handling *)
  let special_type1 = [V.DIVIDE; V.SDIVIDE; V.MOD; V.SMOD] in
  let special_type2 = [V.LSHIFT; V.RSHIFT; V.ARSHIFT] in
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
            if (List.mem binop special_type1)
            then (* accounts for div. by zero *)
              V.BinOp(
                binop, l, 
                get_ite_expr r V.EQ int_val_type 0L 
                  (V.Constant(V.Int(int_val_type, 1L))) r)
            else 
              if (List.mem binop special_type2)
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
  (* we store symbolic expressions representing adaptors in a list and then 
     later call set_reg_symbolic on each expression in that list *)
  let symbolic_exprs = ref [] in
  let rec get_exprs n =
    let var_name = String.make 1 (Char.chr ((Char.code 'a') + n)) in
    symbolic_exprs :=
      (get_arithmetic_expr fm var_name arg_regs int_val_type out_nargs 
         get_oper_expr int_arith_depth) :: !symbolic_exprs;
    if n > 0 then get_exprs (n-1) else () in
  (get_exprs ((Int64.to_int in_nargs) - 1);
   List.iteri 
     (fun idx expr ->
        fm#set_reg_symbolic (List.nth arg_regs idx) expr) !symbolic_exprs)
  

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
  (* restrict input to the adaptor *)
  let restrict_input input =
    match int_restrict_input_range with
    | None -> 
        (match int_restrict_input_list with
         | None -> V.exp_true
         | Some l -> specify_vals input int_val_type l)
    | Some (lower, upper) -> 
        restrict_range input int_val_type lower upper in
  (* restrict the generated counterexamples *)
  let _ = synth_extra_conditions := 
    (restrict_input var) :: !synth_extra_conditions in
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
  let arg_regs = [R_YMM0_0; R_YMM1_0; R_YMM2_0; R_YMM3_0] in
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
         get_oper_expr float_arith_depth) :: !symbolic_exprs;
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
	opt_extra_conditions :=  
             V.BinOp(V.EQ,var_is_const,V.Constant(V.Int(V.REG_1,1L)))
	 :: !opt_extra_conditions;
	var_val
       ) 
       else ( 
	 opt_extra_conditions :=  
	   V.BinOp(
             V.BITOR,
             V.BinOp(V.EQ,var_is_const,V.Constant(V.Int(V.REG_1,1L))),
             V.BinOp(V.LT,var_val,V.Constant(V.Int(V.REG_64,out_nargs))))
	 :: !opt_extra_conditions;
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

let get_ite_ftypeconv_expr fm arg_idx idx_type regs n =
  V.FCast(V.CAST_FWIDEN, Vine_util.ROUND_NEAREST, V.REG_64, 
	 V.Cast(V.CAST_LOW, V.REG_32, 
		(get_ite_arg_expr fm arg_idx idx_type regs n)
	 )
  ) 

(*
  type = 0 -> use outer function arg in val
  type = 1 -> replace the inner function argument with a constant in val
  type = 2 -> sign-extend the low 32-bits of the outer function arg in val
  type > 2 -> fwiden the low 32-bits of the outer function arg in val(in-progress)
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
	opt_extra_conditions :=  
             V.BinOp(V.EQ,var_type,V.Constant(V.Int(V.REG_8,1L)))
	 :: !opt_extra_conditions;
	var_val
       ) 
       else ( 
	 opt_extra_conditions :=  
	   V.BinOp(
             V.BITOR,
             V.BinOp(V.EQ,var_type,V.Constant(V.Int(V.REG_8,1L))),
             V.BinOp(V.LT,var_val,V.Constant(V.Int(V.REG_64,out_nargs))))
	 :: !opt_extra_conditions;
	 get_ite_expr var_type V.EQ V.REG_8 1L var_val 
	   (get_ite_expr var_type V.EQ V.REG_8 0L 
	      (get_ite_arg_expr fm var_val V.REG_64 arg_regs out_nargs)
	      (get_ite_typeconv_expr fm var_val V.REG_64 arg_regs out_nargs)
	      (*(get_ite_expr var_type V.EQ V.REG_8 2L
		 (get_ite_typeconv_expr fm var_val V.REG_64 arg_regs out_nargs)
		 (get_ite_ftypeconv_expr fm var_val V.REG_64 f_arg_regs out_nargs)
	      )*)
	   )
       )
      )
    in
    Printf.printf "setting arg=%s\n" (V.exp_to_string arg);
    symbolic_args := arg :: !symbolic_args;
    if n > 0 then main_loop (n-1); 
  in
  if in_nargs > 0L then  (
    main_loop ((Int64.to_int in_nargs)-1);
    List.iteri (fun index expr ->
	fm#set_reg_symbolic (List.nth arg_regs index) expr;) !symbolic_args;
  )

(* Type conversion adaptor code ends here *)



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

let ret_typeconv_adaptor fm in_nargs =
  Printf.printf "Starting return-typeconv adaptor\n";
  let saved_args_list = fm#get_saved_arg_regs () in
  assert((List.length saved_args_list) = (Int64.to_int in_nargs));
  let ret_val = (fm#get_fresh_symbolic ("ret_val") 64) in
  let ret_type = (fm#get_fresh_symbolic ("ret_type") 8) in
  (* TODO: try using other return argument registers like XMM0 *)
  let return_arg = fm#get_reg_symbolic R_RAX in
  (*let return_base_addr =
  try 
     fm#get_long_var R_RAX
  with NotConcrete(_) -> 0L 
  in
  let max_depth = 4L in*)
  let arg =  
    if in_nargs = 0L then (
      opt_extra_conditions :=  
        V.BinOp(V.LT,ret_type,V.Constant(V.Int(V.REG_8,3L)))
			    :: !opt_extra_conditions;
      get_ite_expr ret_type V.EQ V.REG_8 0L return_arg 
	(get_ite_expr ret_type V.EQ V.REG_8 1L ret_val
	   (V.Cast(V.CAST_SIGNED, V.REG_64, 
		   (V.Cast(V.CAST_LOW, V.REG_32, return_arg))
	    ))
	)
    ) 
(* 
   type = 0 -> leave the return value unchanged, ret_val ignored
   type = 1 -> constant in ret_val
   type = 2 -> apply a 64-to-32 bit narrowing operation on the return value, ret_val ignored
   type = 3 -> make the return value be one of the inner function arguments in ret_val
   Not implementing the below types for now
   type = 4 -> apply a 64-to-32 bit narrowing operation on one of the 
   inner function arguments in ret_val
*)
    else ( 
      opt_extra_conditions :=  
	V.BinOp(
          V.BITOR,
          V.BinOp(V.EQ,ret_type,V.Constant(V.Int(V.REG_8,1L))),
          V.BinOp(V.LT,ret_val,V.Constant(V.Int(V.REG_64,in_nargs))))
			    :: !opt_extra_conditions;
      get_ite_expr ret_type V.EQ V.REG_8 0L return_arg 
	(get_ite_expr ret_type V.EQ V.REG_8 1L ret_val
	   (get_ite_expr ret_type V.EQ V.REG_8 2L 
	      (V.Cast(V.CAST_SIGNED, V.REG_64, 
		      (V.Cast(V.CAST_LOW, V.REG_32, return_arg))
	       )
	      )
	      (get_ite_saved_arg_expr fm ret_val V.REG_64 saved_args_list in_nargs)   
	      (*(if return_base_addr <> 0L then
		(get_ite_expr ret_type V.EQ V.REG_8 3L
		(get_ite_saved_arg_expr fm ret_val V.REG_64 saved_args_list in_nargs)
		   (get_len_expr fm return_base_addr 0L max_depth)
		)
	      else 
		(get_ite_saved_arg_expr fm ret_val V.REG_64 saved_args_list in_nargs))*)
	   )
	)
    )
  in
  Printf.printf "setting return arg=%s\n" (V.exp_to_string arg);
  fm#set_reg_symbolic R_RAX arg;
  
(* Return value type conversion adaptor code ends here *)
  
