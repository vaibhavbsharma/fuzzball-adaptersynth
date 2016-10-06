(*
  Copyright (C) BitBlaze, 2009-2013, and copyright (C) 2010 Ensighta
  Security Inc.  All rights reserved.
*)

module V = Vine;;

open Exec_domain;;
open Exec_utils;;
open Exec_exceptions;;
open Exec_options;;
open Frag_simplify;;
open Formula_manager;;
open Query_engine;;
open Granular_memory;;
open Fragment_machine;;
open Decision_tree;;
open Sym_path_frag_machine;;
open Vine_util;;

module SymRegionFragMachineFunctor =
  functor (D : DOMAIN) ->
struct
  module FormMan = FormulaManagerFunctor(D)
  module GM = GranularMemoryFunctor(D)
  module SPFM = SymPathFragMachineFunctor(D)

  let reg_addr () = match !opt_arch with
    | (X86|ARM) -> V.REG_32
    | X64 -> V.REG_64

  let addr_const addr = V.Constant(V.Int(reg_addr(), addr))

  (* Sign extend a typed constant to a 64-bit constant *)
  let fix_s ty v =
    match ty with
      | V.REG_1 -> fix_s1 v
      | V.REG_8 -> fix_s8 v
      | V.REG_16 -> fix_s16 v
      | V.REG_32 -> fix_s32 v
      | V.REG_64 -> v
      | _ -> failwith "Bad type in fix_s"

  let is_high_mask ty v =
    let is_power_of_2_or_zero x =
      Int64.logand x (Int64.pred x) = 0L
    in
      is_power_of_2_or_zero (Int64.succ (Int64.lognot (fix_s ty v)))

  let floor_log2 i =
    let rec loop = function
      | 0L -> -1
      | 1L -> 0
      | 2L|3L -> 1
      | 4L|5L|6L|7L -> 2
      | i when i < 16L -> 2 + loop(Int64.shift_right_logical i 2)
      | i when i < 256L -> 4 + loop(Int64.shift_right_logical i 4)
      | i when i < 65536L -> 8 + loop(Int64.shift_right_logical i 8)
      | i when i < 0x100000000L -> 16 + loop(Int64.shift_right_logical i 16)
      | _ -> 32 + loop(Int64.shift_right_logical i 32)
    in
      loop i

  (* Conservatively anayze the smallest number of non-zero
     least-significant bits into which a value will fit. This is a fairly
     quick way to tell if an expression could be an index, or to give a
     bound on the size of a table. *)
  let narrow_bitwidth form_man e =
    let combine wd res = min wd res in
    let f loop e =
      match e with
	| V.Constant(V.Int(ty, v)) -> 1 + floor_log2 v
	| V.BinOp(V.BITAND, e1, e2) -> min (loop e1) (loop e2)
	| V.BinOp(V.BITOR, e1, e2) -> max (loop e1) (loop e2)
	| V.BinOp(V.XOR, e1, e2) -> max (loop e1) (loop e2)
	| V.BinOp(V.PLUS, e1, e2) -> 1 + (max (loop e1) (loop e2))
	| V.BinOp(V.TIMES, e1, e2) -> (loop e1) + (loop e2)
	| V.BinOp(V.MOD, e1, e2) -> min (loop e1) (loop e2)
	| V.Cast(V.CAST_UNSIGNED, V.REG_64, e1)
	  -> min 64 (loop e1)
	| V.Cast((V.CAST_UNSIGNED|V.CAST_LOW), V.REG_32, e1)
	  -> min 32 (loop e1)
	| V.Cast((V.CAST_UNSIGNED|V.CAST_LOW), V.REG_16, e1)
	  -> min 16 (loop e1)
	| V.Cast((V.CAST_UNSIGNED|V.CAST_LOW), V.REG_8, e1)
	  -> min 8  (loop e1)
	| V.Cast((V.CAST_UNSIGNED|V.CAST_LOW), V.REG_1, e1)
	  -> min 1  (loop e1)
	| V.Cast(V.CAST_SIGNED, V.REG_32, e1) -> 32
	| V.Cast(V.CAST_SIGNED, V.REG_16, e1) -> 16
	| V.Cast(V.CAST_SIGNED, V.REG_8,  e1) -> 8
	| V.Cast(V.CAST_SIGNED, V.REG_1,  e1) -> 1
        (* High casts could be improved by treating like an RSHIFT *)
	| V.Cast(V.CAST_HIGH, V.REG_32, e1) -> 32
	| V.Cast(V.CAST_HIGH, V.REG_16, e1) -> 16
	| V.Cast(V.CAST_HIGH, V.REG_8,  e1) -> 8
	| V.Cast(V.CAST_HIGH, V.REG_1,  e1) -> 1
	| V.Cast(_, _, _) ->
	    V.bits_of_width (Vine_typecheck.infer_type_fast e)
	| V.Lval(V.Mem(_, _, V.REG_8))  ->  8
	| V.Lval(V.Mem(_, _, V.REG_16)) -> 16
	| V.Lval(V.Mem(_, _, V.REG_32)) -> 32
	| V.Lval(V.Mem(_, _, _))
	| V.Lval(V.Temp(_)) ->
	    V.bits_of_width (Vine_typecheck.infer_type_fast e)
	| V.BinOp((V.EQ|V.NEQ|V.LT|V.LE|V.SLT|V.SLE), _, _) -> 1
	| V.BinOp(V.LSHIFT, e1, V.Constant(V.Int(_, v))) ->
	    (loop e1) + (Int64.to_int v)
	| V.BinOp(_, _, _) ->
	    V.bits_of_width (Vine_typecheck.infer_type_fast e)
	| V.Ite(_, te, fe) -> max (loop te) (loop fe)
	| V.UnOp(_)
	| V.Let(_, _, _)
	| V.Name(_)
	| V.FBinOp(_, _, _, _)
	| V.FUnOp(_, _, _)
	| V.FCast(_, _, _, _) ->
	    V.bits_of_width (Vine_typecheck.infer_type_fast e)
	| V.Constant(V.Str(_)) ->
	    failwith "Unhandled string in narrow_bitwidth"
	| V.Unknown(_) ->
	    failwith "Unhandled unknown in narrow_bitwidth"
    in
    let f_traced loop e =
      Printf.printf "Narrow bitwidth of %s:\n" (V.exp_to_string e);
      let i = f loop e in
	Printf.printf "Narrow bitwidth of %s is %d\n" (V.exp_to_string e) i;
	i
    in
      FormMan.map_expr_temp form_man e (if false then f_traced else f) combine

  (* Similar to narrow_bitwidth, but count negative numbers of small
     absolute value (i.e. with many leading 1s) as narrow as well. I
     can't decide whether this would work better as a single function
     with a flag: some of the cases are similar, but others aren't. *)
  let narrow_bitwidth_signed form_man e =
    let combine wd res = min wd res in
    let f loop = function
      | V.Constant(V.Int(ty, v)) ->
	  min (1 + floor_log2 v)
	    (1 + floor_log2 (Int64.neg (fix_s ty v)))
      | V.BinOp(V.BITAND, e1, e2) -> max (loop e1) (loop e2)
      | V.BinOp(V.BITOR, e1, e2) -> max (loop e1) (loop e2)
      | V.BinOp(V.XOR, e1, e2) -> max (loop e1) (loop e2)
      | V.BinOp(V.PLUS, e1, e2) -> 1 + (max (loop e1) (loop e2))
      | V.BinOp(V.TIMES, e1, e2) -> (loop e1) + (loop e2)
      | V.BinOp(V.MOD, e1, e2) -> min (loop e1) (loop e2)
      | V.BinOp(V.SMOD, e1, e2) -> min (loop e1) (loop e2)
      | V.Cast((V.CAST_UNSIGNED|V.CAST_SIGNED), V.REG_64, e1)
	-> min 64 (loop e1)
      | V.Cast((V.CAST_UNSIGNED|V.CAST_LOW|V.CAST_SIGNED), V.REG_32, e1)
	-> min 32 (loop e1)
      | V.Cast((V.CAST_UNSIGNED|V.CAST_LOW|V.CAST_SIGNED), V.REG_16, e1)
	-> min 16 (loop e1)
      | V.Cast((V.CAST_UNSIGNED|V.CAST_LOW|V.CAST_SIGNED), V.REG_8, e1)
	-> min 8  (loop e1)
      | V.Cast((V.CAST_UNSIGNED|V.CAST_LOW|V.CAST_SIGNED), V.REG_1, e1)
	-> min 1  (loop e1)
      | V.Cast(_, V.REG_32, _) -> 32
      | V.Cast(_, V.REG_16, _) -> 16
      | V.Cast(_, V.REG_8, _) -> 8
      | V.Cast(_, V.REG_1, _) -> 1
      | V.Cast(_, _, _) ->
	  V.bits_of_width (Vine_typecheck.infer_type_fast e)
      | V.Lval(V.Mem(_, _, V.REG_8))  ->  8
      | V.Lval(V.Mem(_, _, V.REG_16)) -> 16
      | V.Lval(V.Mem(_, _, V.REG_32)) -> 32
      | V.Lval(V.Mem(_, _, _))
      | V.Lval(V.Temp(_)) ->
	  V.bits_of_width (Vine_typecheck.infer_type_fast e)
      | V.BinOp((V.EQ|V.NEQ|V.LT|V.LE|V.SLT|V.SLE), _, _) -> 1
      | V.BinOp(V.LSHIFT, e1, V.Constant(V.Int(_, v))) ->
	  (loop e1) + (Int64.to_int v)
      | V.BinOp(_, _, _) ->
	  V.bits_of_width (Vine_typecheck.infer_type_fast e)
      | V.Ite(_, te, fe) -> max (loop te) (loop fe)
      | V.UnOp(_)
      | V.Let(_, _, _)
      | V.Name(_)
      | V.FBinOp(_, _, _, _)
      | V.FUnOp(_, _, _)
      | V.FCast(_, _, _, _) ->
	  V.bits_of_width (Vine_typecheck.infer_type_fast e)
      | V.Constant(V.Str(_)) ->
	  failwith "Unhandled string in narrow_bitwidth_signed"
      | V.Unknown(_) ->
	  failwith "Unhandled unknown in narrow_bitwidth_signed"
    in
      FormMan.map_expr_temp form_man e f combine

  let narrow_bitwidth_cutoff () =
    match (!opt_narrow_bitwidth_cutoff, (reg_addr ())) with
      | ((Some i), _) -> i
      | (_, V.REG_32) -> 23
      | (_, V.REG_64) -> 40
      | (_, _) -> 23

  let ctz i =
    let rec loop = function
      | 0L -> 64
      | i when Int64.logand i 1L = 1L -> 0
      | i when Int64.logand i 0xffffffffL = 0L ->
	  32 + loop (Int64.shift_right i 32)
      | i when Int64.logand i 0xffffL = 0L ->
	  16 + loop (Int64.shift_right i 16)
      | i when Int64.logand i 0xffL = 0L -> 8  + loop (Int64.shift_right i  8)
      | i when Int64.logand i  0xfL = 0L -> 4  + loop (Int64.shift_right i  4)
      | i when Int64.logand i    3L = 0L -> 2  + loop (Int64.shift_right i  2)
      | i when Int64.logand i    1L = 0L -> 1  + loop (Int64.shift_right i  1)
      | _ -> failwith "Unexpected else case in ctz"
    in
      loop i

  let bitshift form_man e =
    let combine wd res = min wd res in
    let f loop e =
      match e with
	| V.Constant(V.Int(ty, v)) -> ctz v
	| V.BinOp(V.BITAND, e1, e2) -> max (loop e1) (loop e2)
	| V.BinOp(V.BITOR, e1, e2) -> min (loop e1) (loop e2)
	| V.BinOp(V.LSHIFT, e1, V.Constant(V.Int(_, v))) ->
	    (loop e1) + (Int64.to_int v)
	| V.BinOp(V.TIMES, e1, e2) -> (loop e1) + (loop e2)
	| V.BinOp(V.PLUS, e1, e2) -> min (loop e1) (loop e2)
	| V.Cast(_, V.REG_32, e1) -> min 32 (loop e1)
	| V.Cast(_, V.REG_16, e1) -> min 16 (loop e1)
	| V.Cast(_, V.REG_8, e1)  -> min 8  (loop e1)
	| V.Cast(_, V.REG_1, e1)  -> min 1  (loop e1)
	| V.Ite(_, te, fe) -> min (loop te) (loop fe)
	| _ -> 0
    in
      FormMan.map_expr_temp form_man e f combine

  (* OCaml's standard library has this for big ints but not regular ones *)
  let rec gcd a b =
    match (a, b) with
      | (0, b) -> b
      | (a, 0) -> a
      | (a, b) when a > b -> gcd b (a mod b)
      | _ -> gcd a (b mod a)

  let stride form_man e =
    let combine wd res = res in
    let rec f loop e =
      match e with
	| V.BinOp((V.PLUS|V.MINUS), e1, e2) -> gcd (loop e1) (loop e2)
	| V.BinOp(V.TIMES, e1, e2) -> (loop e1) * (loop e2)
	| V.BinOp(V.LSHIFT, e1, V.Constant(V.Int(_, v)))
	    when v < 0x3fffffffL
	      -> (loop e1) lsl (Int64.to_int v)
	| V.Constant(V.Int(_, k))
	    when k < 0x3fffffffL
	      -> Int64.to_int k
	| e -> 1 lsl (bitshift form_man e)
    in
      FormMan.map_expr_temp form_man e f combine

  let map_n fn n =
    let l = ref [] in
      for i = n downto 0 do
	l := (fn i) :: !l
      done;
      !l

  let split_terms e form_man =
    (*Printf.printf "split_terms e = %s\n" (V.exp_to_string e);*)
    (* x | y = x - (x & m) + ((x & m) | y)
       where m is a bitmask >= y. *)
    let split_or loop e_wide e_narrow narrow_wd =
      assert(narrow_wd >= 0); (* x & 0 should have been optimized away *)
      let mask = Int64.pred (Int64.shift_left 1L narrow_wd) in
      let ty_y = Vine_typecheck.infer_type None e_narrow in
      let masked = V.BinOp(V.BITAND, e_wide,
			   V.Constant(V.Int(ty_y, mask))) in
	(loop e_wide) @
	  [V.UnOp(V.NEG, masked);
	   V.BinOp(V.BITOR, masked, e_narrow)]
    in
    let rec loop e =
      (*Printf.printf "    split_terms inside loop e = %s\n" (V.exp_to_string e);*)
      match e with
	| V.BinOp(V.PLUS, e1, e2) -> (loop e1) @ (loop e2)
	| V.Ite(cond, V.BinOp(V.PLUS, e1, e2), V.BinOp(V.PLUS, e1', e3))
	    when e1 = e1' ->
	    (loop e1) @ (loop (V.Ite(cond, e2, e3)))
	| V.Ite(cond, V.BinOp(V.PLUS, e1, e2), V.BinOp(V.PLUS, e3, e2'))
	    when e2 = e2' ->
	    (loop (V.Ite(cond, e1, e3))) @ (loop e2)
	| V.BinOp(V.BITAND, e, V.Constant(V.Int(ty, v)))
	    when is_high_mask ty v ->
	    (* x & 0xfffffff0 = x - (x & 0xf), etc. *)
	    (loop e) @
	      (loop
		 (V.UnOp(V.NEG,
			 V.BinOp(V.BITAND, e,
				 V.UnOp(V.NOT, V.Constant(V.Int(ty, v)))))))
	| V.BinOp(V.BITOR, e1, V.BinOp(V.BITOR, e2, e3))
	| V.BinOp(V.BITOR, V.BinOp(V.BITOR, e1, e2), e3)
	    ->
	    let w1 = narrow_bitwidth form_man e1 and
		w2 = narrow_bitwidth form_man e2 and
		w3 = narrow_bitwidth form_man e3 in
	      if min w1 (min w2 w3) <= 8 then
		(if w1 <= w2 && w1 <= w3 then
		   split_or loop (V.BinOp(V.BITOR, e2, e3)) e1 w1
		 else if w2 <= w1 && w2 <= w3 then
		   split_or loop (V.BinOp(V.BITOR, e1, e3)) e2 w2
		 else
		   (assert(w3 <= w1 && w3 <= w2);
		    split_or loop (V.BinOp(V.BITOR, e1, e2)) e3 w3))
	      else
		[e]
	| V.BinOp(V.BITOR, e1, e2) ->
	    let w1 = narrow_bitwidth form_man e1 and
		w2 = narrow_bitwidth form_man e2 in
(* 	      Printf.printf "In %s (OR) %s, widths are %d and %d\n" *)
(* 		(V.exp_to_string e1) (V.exp_to_string e2) w1 w2; *)
	      if min w1 w2 <= 8 then
		(if w1 < w2 then
		   split_or loop e2 e1 w1
		 else
		   split_or loop e1 e2 w2)
	      else
		[e] 
	| V.Lval(V.Temp(var)) ->
	    FormMan.if_expr_temp form_man var
	      (fun e' -> loop e') [e] (fun v -> ())
	| e -> [e]
    in
      loop e

  type term_kind = | ConstantBase of int64
		   | ConstantOffset of int64
		   | ExprOffset of V.exp
		   | AmbiguousExpr of V.exp
		   | Symbol of V.exp

  let rec classify_term form_man e =
    match e with
      | V.Constant(V.Int(V.REG_32, off))
	  when (Int64.abs (fix_s32 off)) < 0x4000L
	    -> ConstantOffset(off)
      | V.Constant(V.Int(V.REG_64, off))
	  when (Int64.abs off) < 0x4000L
	    -> ConstantOffset(off)
      | V.Constant(V.Int(V.REG_32, off)) when (fix_s32 off) > 0x8000000L
	  -> ConstantBase(off)
      | V.Constant(V.Int(V.REG_32, off))
	  when off >= 0xc0000000L && off < 0xe1000000L (* Linux kernel *)
	  -> ConstantBase(off)
      | V.Constant(V.Int(V.REG_32, off))
	  when off >= 0x80800000L && off < 0x88000000L (* ReactOS kernel *)
	  -> ConstantBase(off)
      | V.Constant(V.Int(V.REG_32, off))
	  when off >= 0x82800000L && off < 0x94000000L (* Windows 7 kernel *)
	  -> ConstantBase(off)
      | V.Constant(V.Int(V.REG_32, off))
	  when off >= 0xf88f0000L && off < 0xf88fffffL
	    (* ReactOS kernel stack *)
	  -> ConstantBase(off)
      | V.Constant(V.Int(V.REG_32, off))
	  when off >= 0x9b200000L && off < 0x9b300000L
	    (* Windows 7 kernel stack *)
	  -> ConstantBase(off)
      | V.Constant(V.Int(V.REG_32, off))
	  when off >= 0xff400000L && off < 0xffc00000L
	    (* Windows 7 kernel something *)
	  -> ConstantBase(off)
      | V.Constant(V.Int(V.REG_32, off))
	  when off >= 0x7ff00000L && off < 0x80000000L
	    (* Windows 7 shared user/kernel something *)
	  -> ConstantBase(off)
      | V.Constant(V.Int(V.REG_32, off))
	  when off >= 0x80000000L && off < 0xffffffffL
	    (* XXX let Windows 7 wander over the whole top half *)
	  -> ConstantBase(off)
      | V.Constant(V.Int((V.REG_32|V.REG_64), off))
	    (* XXX -random-memory can produce any value at all *)
	  -> ConstantBase(off)
      | V.UnOp(V.NEG, _) -> ExprOffset(e)
      | V.BinOp(V.LSHIFT, _, V.Constant(V.Int(V.REG_8, (1L|2L|3L|4L|5L))))
	  -> ExprOffset(e)
      | V.BinOp(V.TIMES, _, _)
	  -> ExprOffset(e)
      | e when (narrow_bitwidth form_man e)
	  < (narrow_bitwidth_cutoff ())
	  -> ExprOffset(e)
      | e when (narrow_bitwidth_signed form_man e)
	  < (narrow_bitwidth_cutoff ())
	  -> ExprOffset(e)
      | V.BinOp(V.ARSHIFT, _, _)
	  -> ExprOffset(e)
      | V.BinOp(V.RSHIFT, _, _)
	  -> ExprOffset(e)
      | V.BinOp(V.LSHIFT, _, _)
	  -> ExprOffset(e)
      | V.BinOp(V.BITOR, 
		V.BinOp(V.BITAND, V.Cast(V.CAST_SIGNED, _, _), x),
		V.BinOp(V.BITAND, V.UnOp(V.NOT, V.Cast(V.CAST_SIGNED, _, _)),
			y))
      | V.BinOp(V.BITOR, 
		V.BinOp(V.BITAND, x, V.Cast(V.CAST_SIGNED, _, _)),
		V.BinOp(V.BITAND, V.UnOp(V.NOT, V.Cast(V.CAST_SIGNED, _, _)),
			y))
      | V.BinOp(V.BITOR, 
		V.BinOp(V.BITAND, V.Cast(V.CAST_SIGNED, _, _), x),
		V.BinOp(V.BITAND, y,
			V.UnOp(V.NOT, V.Cast(V.CAST_SIGNED, _, _))))
      | V.BinOp(V.BITOR, 
		V.BinOp(V.BITAND, x, V.Cast(V.CAST_SIGNED, _, _)),
		V.BinOp(V.BITAND, y,
			V.UnOp(V.NOT, V.Cast(V.CAST_SIGNED, _, _))))
      | V.Ite(_, x, y)
	->
	  (* ITE expression "_ ? x : y" *)
	  (match (classify_term form_man x), (classify_term form_man y) with
	     | (ExprOffset(_)|ConstantOffset(_)),
	       (ExprOffset(_)|ConstantOffset(_)) ->
	       ExprOffset(e)
	     | _ -> 
	       AmbiguousExpr(e)
	  )
      (* Similar pattern where we don't have the sign extend, but
	 we do have something and its negation *)
      | V.BinOp(V.BITOR,
		V.BinOp(V.BITAND, c1, x),
		V.BinOp(V.BITAND, V.UnOp(V.NOT, c2), y))
	  when c1 = c2
	->
	  (* ITE expression "_ ? x : y" *)
	  (match (classify_term form_man x), (classify_term form_man y) with
	     | (ExprOffset(_)|ConstantOffset(_)),
	       (ExprOffset(_)|ConstantOffset(_)) ->
		 ExprOffset(e)
	     | _ -> 
	       AmbiguousExpr(e)
	  )
      (* Occurs as an optimization of bitwise ITE: *)
      | V.BinOp(V.BITAND, x, V.UnOp(V.NOT, V.Cast(V.CAST_SIGNED, _, _)))
      | V.BinOp(V.BITAND, V.UnOp(V.NOT, V.Cast(V.CAST_SIGNED, _, _)), x)
      | V.BinOp(V.BITAND, x, V.Cast(V.CAST_SIGNED, _, _))
      | V.BinOp(V.BITAND, V.Cast(V.CAST_SIGNED, _, _), x) ->
	  (match (classify_term form_man x) with
	     | (ExprOffset(_)|ConstantOffset(_)) -> ExprOffset(e)
	     | _ -> AmbiguousExpr(e)
	  )

      (* AND with negation of a small value used for rounding *)
      | V.BinOp(V.BITAND, x, V.Constant(V.Int(V.REG_32, off)))
	  when (fix_u32 off) >= 0xffffff00L
	    ->
	  (classify_term form_man x)
      | V.BinOp(V.BITAND, x, V.Constant(V.Int(V.REG_64, off)))
	  when off >= 0xffffffffffffff00L
	    ->
	  (classify_term form_man x)

      (* Addition inside another operation (top-level addition should
	 be handled by split_terms) *)
      | V.BinOp(V.PLUS, e1, e2)
	->
	  (match (classify_term form_man e1), (classify_term form_man e2) with
	     | (ExprOffset(_)|ConstantOffset(_)),
	       (ExprOffset(_)|ConstantOffset(_)) -> ExprOffset(e)
	     | _,_ -> AmbiguousExpr(e))

      | V.BinOp(V.XOR, e1, e2)
	->
	  (match (classify_term form_man e1), (classify_term form_man e2) with
	     | (ExprOffset(_)|ConstantOffset(_)),
	       (ExprOffset(_)|ConstantOffset(_)) -> ExprOffset(e)
	     | _,_ -> AmbiguousExpr(e))

(*       | V.BinOp(V.BITAND, _, _) *)
(*       | V.BinOp(V.BITOR, _, _) (* XXX happens in Windows 7, don't know why *) *)
(* 	  -> ExprOffset(e) *)
      | V.Cast(V.CAST_SIGNED, _, _) -> ExprOffset(e)
      | V.Lval(_) -> Symbol(e)
      | _ -> if (!opt_fail_offset_heuristic) then (
	  failwith ("Strange term "^(V.exp_to_string e)^" in address")
	) else ExprOffset(e)
	  
  let classify_terms e form_man =
    let l = List.map (classify_term form_man) (split_terms e form_man) in
    let (cbases, coffs, eoffs, ambig, syms) =
      (ref [], ref [], ref [], ref [], ref []) in
      List.iter
	(function
	   | ConstantBase(o) ->  cbases := o :: !cbases
	   | ConstantOffset(o) -> coffs := o :: !coffs
	   | ExprOffset(e) ->     eoffs := e :: !eoffs
	   | AmbiguousExpr(e) ->  ambig := e :: !ambig
	   | Symbol(v) ->          syms := v :: !syms)
	l;
      (!cbases, !coffs, !eoffs, !ambig, !syms)

  let select_one l rand_func =
    let split_list l =
      let a = Array.of_list l in
      let len = Array.length a in 
      let k = len / 2 in
	((Array.to_list (Array.sub a 0 k)),
	 (Array.to_list (Array.sub a k (len - k))))
    in
    let rec loop l =
      match l with
	| [] -> failwith "Empty list in select_one"
	| [a] -> (a, [])
	| [a; b] -> if rand_func () then (a, [b]) else (b, [a])
	| l -> let (h1, h2) = split_list l in
	    if rand_func () then
	      let (e, h1r) = loop h1 in
		(e, h1r @ h2)
	    else
	      let (e, h2r) = loop h2 in
		(e, h1 @ h2r)
    in
      loop l

  let sum_list l = 
    match l with 
      | [] -> addr_const 0L
      | [a] -> a
      | e :: r -> List.fold_left (fun a b -> V.BinOp(V.PLUS, a, b))
	  e r

  class sym_region_frag_machine (dt:decision_tree) = object(self)
    inherit SPFM.sym_path_frag_machine dt as spfm

    val mutable regions : GM.granular_snapshot_memory list = []
    val mutable region_conc_addr_h = Hashtbl.create 101
    val mutable sym_input_region_l = []
    val region_vals = Hashtbl.create 101

    (* per execution path (region expression != 0) query is maintained in
       region_val_queried *)
    val region_val_queried = Hashtbl.create 101
    
    (* per execution path region expression to region number mapping is 
       maintained in region_vals_per_path *)
    val region_vals_per_path = Hashtbl.create 101
    val mutable have_snap = false
    val mutable f1_hash_list : (((int64, GM.gran64) Hashtbl.t) list )= []
    val mutable f2_hash_list : (((int64, GM.gran64) Hashtbl.t) list )= []

    val mutable location_id = 0L

    method set_eip i =
      location_id <- i;
      spfm#set_eip i

    (* eip hook to track change in region contents as execution proceeds *)
    method private print_region r_num = 
      try
	let tmp_val = (List.nth regions r_num)#load_long 0L in
	Printf.printf "SRFM#print_reg regions[%d][0] = %s\n" 
	  r_num (D.to_string_64 tmp_val)
      with Failure("nth") -> 
	Printf.printf "SRFM#print_reg regions.length = %d\n" 
	  (List.length regions);
	
    method start_symbolic =
      spfm#start_symbolic ;
      (* self#add_extra_eip_hook (fun fm _ -> self#print_reg 15 );  *)
	
    val sink_mem = new GM.granular_sink_memory

    method private region r =
      match r with
	| None -> (sink_mem :> (GM.granular_memory))
	| Some 0 -> (mem :> (GM.granular_memory))
	| Some r_num -> ((List.nth regions (r_num - 1)) :> GM.granular_memory)

    method private region_load r size addr =
      let (mem, conc_addr) = 
	match r with
	| None -> ((sink_mem :> (GM.granular_memory)), 0L)
	| Some 0 -> ((mem :> (GM.granular_memory)), 0L)
	| Some r_num -> 
	  let conc_addr = 
	    if Hashtbl.mem region_conc_addr_h r_num then
	      Hashtbl.find region_conc_addr_h r_num 
	    else 0L 
	  in
	  if conc_addr = 0L then ((self#region r), 0L) 
	  else ((self#region (Some 0)), conc_addr) 
      in
      let new_addr = (Int64.add conc_addr addr) in
      match size with
      | 8 -> mem#load_byte new_addr
      | 16 -> mem#load_short new_addr
      | 32 -> mem#load_word new_addr
      | 64 -> mem#load_long new_addr
      | _ -> failwith "wrong size passed to region_load"

    method private region_store r size addr value =
      let (mem, conc_addr) = 
	match r with
	| None -> ((sink_mem :> (GM.granular_memory)), 0L)
	| Some 0 -> ((mem :> (GM.granular_memory)), 0L)
	| Some r_num -> 
	  let conc_addr = 
	    if Hashtbl.mem region_conc_addr_h r_num then 
	      Hashtbl.find region_conc_addr_h r_num 
	    else 0L 
	  in
	  if conc_addr = 0L then ((self#region r), 0L) 
	  else ((self#region (Some 0)), conc_addr) 
      in
      let new_addr = (Int64.add conc_addr addr) in
      match size with
      | 8 -> mem#store_byte new_addr value
      | 16 -> mem#store_short new_addr value
      | 32 -> mem#store_word new_addr value
      | 64 -> mem#store_long new_addr value
      | _ -> failwith "wrong size password to region_store"

    method make_f1_sym_snap =
      if !opt_trace_mem_snapshots then
	Printf.printf "SRFM#make_sym_snap called\n";
      List.iter (fun m -> m#make_snap ();) regions;
      have_snap <- true;
      ()
	
    method save_f1_sym_se =
      List.iteri (fun ind ele -> 
	let f1_hash = Hashtbl.copy (ele#get_mem) in
	f1_hash_list <- f1_hash_list @ [f1_hash];
      ) regions;
      
      if !opt_trace_mem_snapshots then
	Printf.printf "SRFM#save_sym_se saving f1_hash_list.length = %d\n"
	  (List.length f1_hash_list);
      ()

    method make_f2_sym_snap =
      if !opt_trace_mem_snapshots then
	Printf.printf "SRFM#make_f2_sym_snap called\n";
      List.iter (fun m -> 
	if (m#get_snap ()) = false then
	  failwith "unsnapped region being reset, panic!";
	m#reset ();) regions;
      have_snap <- false;
      ()

    method compare_sym_se =
      if !opt_trace_mem_snapshots then
	Printf.printf "SRFM#compare_sym_se called len(f1_h_l) = %d len(f2_h_l)=%d\n"
	  (List.length f1_hash_list) (List.length f2_hash_list);
      List.iteri (fun ind ele -> 
	let f2_hash = Hashtbl.copy (ele#get_mem) in
	f2_hash_list <- f2_hash_list @ [f2_hash];
      ) regions;

      let inequiv = ref 0 in
      let f2_hash_list_len = List.length f2_hash_list in
      let f1_hash_list_len = List.length f1_hash_list in
      if !opt_trace_mem_snapshots = true then
	Printf.printf "f1_hash_list_len = %d f2_hash_list_len = %d\n"
	  f1_hash_list_len f2_hash_list_len;
      if f1_hash_list_len <> 0 || f2_hash_list_len <> 0 then (
	(* Compare each of f1's symbolic region writes with f2 *)
	List.iteri ( fun ind ele ->
	  (* If region has concrete address then fragment_machine#compare_conc_se
	     will do the side-effect equivalence checking for this region *)
	  if (Hashtbl.mem region_conc_addr_h (ind+1)) = false then (
	    if ind >= f2_hash_list_len then 
	      failwith "region list became smaller after f2, panic!"
	    else (
	      Hashtbl.iter ( fun addr chunk ->
	      (List.nth regions ind)#set_mem (List.nth f1_hash_list ind);
		let f1_exp = (List.nth regions ind)#load_long addr in
		(List.nth regions ind)#set_mem (List.nth f2_hash_list ind);
		let f2_exp = (List.nth regions ind)#load_long addr in
		if !opt_trace_mem_snapshots = true then
		  Printf.printf "SRFM#compare_sym_se region = %d addr = %Ld f1_exp = %s f2_exp = %s\n"
		    ind addr (D.to_string_64 f1_exp) (D.to_string_64 f2_exp);
		self#query_exp (D.to_symbolic_64 f1_exp) (D.to_symbolic_64 f2_exp);
	      ) ele;
	    ));
	) f1_hash_list;
	
	(* Compare each of f2's symbolic region writes with f1 *)
	List.iteri ( fun ind ele ->
	  (* If region has concrete address then fragment_machine#compare_conc_se
	     will do the side-effect equivalence checking for this region *)
	  if (Hashtbl.mem region_conc_addr_h (ind+1)) = false then (
	    if (ind >= f1_hash_list_len) && ((Hashtbl.length ele) <> 0) then 
	      inequiv := 1
	    else (
	      Hashtbl.iter ( fun addr chunk ->
		let f2_exp = (List.nth regions ind)#load_long addr in
		(List.nth regions ind)#set_mem (List.nth f1_hash_list ind);
		let f1_exp = (List.nth regions ind)#load_long addr in
		(List.nth regions ind)#set_mem (List.nth f2_hash_list ind);
		if !opt_trace_mem_snapshots = true then
		  Printf.printf "SRFM#compare_sym_se region = %d addr = %Ld f1_exp = %s f2_exp = %s\n"
		    ind addr (D.to_string_64 f1_exp) (D.to_string_64 f2_exp);
		self#query_exp (D.to_symbolic_64 f1_exp) (D.to_symbolic_64 f2_exp);
	      ) ele;
	    ));
	) f2_hash_list;
	
	if !inequiv = 1 then
	  if !opt_trace_mem_snapshots = true then
	    (Printf.printf "SRFM#compare_sym_se inequivalent side-effects in symbolic regions\n";
	     raise DisqualifiedPath;);
      );
      List.iter (fun m -> m#reset ();) regions;
      f1_hash_list <- [];
      f2_hash_list <- [];
      ()
	
    (* Check if two expressions are syntactically or semantically equal,
       disqualify the path if not *)
    method private query_exp exp1 exp2 =
      if exp1 = exp2 then
	(if !opt_trace_mem_snapshots = true then
	    Printf.printf "equal side-effects %s = %s\n"
	      (V.exp_to_string exp1) 
	      (V.exp_to_string exp2);)
      else (
	let q_exp = V.BinOp(V.EQ, exp1, exp2) in
	let (b,_) = (self#query_condition q_exp (Some true) 0x6df0) in
	if b = false then (
	  if !opt_trace_mem_snapshots = true then
	    Printf.printf "inequivalent symbolic region side-effects %s!=\n%s\n" 
	      (V.exp_to_string exp1) (V.exp_to_string exp2);
	  raise DisqualifiedPath;
	)
	else (
	  if !opt_trace_mem_snapshots = true then
	    Printf.printf "equivalent side-effects %s=\n%s"
	      (V.exp_to_string exp1) (V.exp_to_string exp2);
	)
      )

    method private fresh_region =
      let new_idx = 1 + List.length regions in
      let region = (new GM.granular_snapshot_memory 
		      (new GM.granular_hash_memory) 
		      (new GM.granular_hash_memory)) and
	  name = "region_" ^ (string_of_int new_idx) in
      regions <- regions @ [region];
      (match (!opt_region_limit, !opt_zero_memory) with
	 | (Some lim, _) ->
	     spfm#on_missing_symbol_m_lim (region :> GM.granular_memory)
	       name lim
	 | (_, true) ->
	     spfm#on_missing_zero_m (region :> GM.granular_memory)
	 | _ ->
	     spfm#on_missing_symbol_m (region :> GM.granular_memory) name);
      if have_snap = true then region#make_snap ();
      new_idx

    method private region_for e =
      (* We dont allow a region-creating expression to be set to NULL 
	 on this execution path while limiting this query to only once
	 per execution path *)
      (try 
	 let _ = Hashtbl.find region_val_queried e in
	 if !opt_trace_regions then
	   Printf.printf "SRFM#region_for found in region_val_queried expr = %s\n"
	     (V.exp_to_string e);
       with Not_found ->
	 let (b_is_regexp_null,_) = self#query_condition 
	   (V.BinOp(V.NEQ, e, V.Constant(V.Int(V.REG_64, 0L))))
	   (Some true) 0x6d01 in
	 if !opt_trace_regions then
	   Printf.printf "SRFM#region_for took branch %b in Not_found case expr = %s\n" 
	     b_is_regexp_null (V.exp_to_string e);
	 Hashtbl.replace region_val_queried e 1;
	 if b_is_regexp_null <> true then raise NullDereference;
      );
      
      try
	let ret = Hashtbl.find region_vals_per_path e in
	if !opt_trace_regions then
	  Printf.printf "SRFM#region_for found region number in region_vals, ret = %d expr = %s\n" 
	    ret (V.exp_to_string e);
	ret
      with Not_found ->
	(* Try to eagerly concretize this address expression if it is a ITE expression *)
	let const = ref [] in
	let rec loop e =
	  match e with
	  | V.BinOp(op, e1, e2) -> V.BinOp(op, e1, e2)
	  | V.Constant(V.Int(V.REG_64, _const)) -> 
	    if (Int64.abs (fix_s32 _const)) > 4096L then
	      const := !const @ [_const];
	    V.Constant(V.Int(V.REG_64, _const))
	  | V.Ite(ce, te, fe) ->
	    V.Ite((loop ce), (loop te), (loop fe))
	  | _ -> e
	in
	let conc_addr = ref 0L in
	let _ = loop e in
	List.iter ( fun _conc_addr -> 
	  let exp = V.BinOp(V.EQ, e, V.Constant(V.Int(V.REG_64, _conc_addr))) in
	  let (b,_) = self#query_condition exp (Some true) 0x6dfe in
	  if b = true then ( (* save this region's concrete value *)
	    if !opt_trace_regions then
	      Printf.printf "SRFM#region_for using concrete address %Lx for %s\n"
		_conc_addr (V.exp_to_string e);
	    conc_addr := _conc_addr; )
	  else ( 
	    if !opt_trace_regions then
	      Printf.printf "SRFM#region_for not using concrete address %Lx for %s\n"
		_conc_addr (V.exp_to_string e);
	  )
	) !const;

	(* adaptor symbolic formula fix: equivalent adaptor formulae should use 
	   same region, if e is equivalent to an expression already in 
	   seen in this execution path then reuse that region *)
	let new_rnum = ref 0 in
	if !opt_trace_regions = true then
	  Printf.printf "SRFM#region_for regions seen in this path = %d\n"
	    (Hashtbl.length region_vals_per_path);
	Hashtbl.iter (fun reg_exp region -> 
	  let exp = V.BinOp(V.EQ, reg_exp, e) in
	  let (b,_) = (self#query_condition exp (Some false) 0x6d02) in
	  if b = true then (
	    if !opt_trace_regions then
	      Printf.printf "SRFM#region_for satisfied expr = %s\n"
		(V.exp_to_string exp);
	    new_rnum := region;)
	) region_vals_per_path;
	let is_sym_input_region_l = ref false in
	let new_region =
	  if !new_rnum <> 0 then !new_rnum 
	  else if Hashtbl.mem region_vals e then Hashtbl.find region_vals e 
	  else ( 
	    let rnum' = self#fresh_region in
	    Hashtbl.replace region_vals e rnum';
	    rnum'
	  )
	in
	if !opt_adaptor_search_mode = false then (
	  match e with
	  | V.Lval(V.Temp((i,s,ty))) when 
	      (((String.length s) = 1) && ((Char.code s.[0]) - (Char.code 'a') < 6)) -> 
	    (Printf.printf "found symbolic input(%s) as address \n" s;
	     is_sym_input_region_l := true;)
	  | _ -> ());
	Hashtbl.replace region_vals_per_path e new_region;
	Hashtbl.replace region_conc_addr_h new_region !conc_addr;
	if !is_sym_input_region_l = true then
	  sym_input_region_l <- sym_input_region_l @ [new_region];
	if !opt_trace_regions then
	  Printf.printf "Address %s is region %d\n"
	    (V.exp_to_string e) new_region;
	new_region

    method private is_region_base e =
      Hashtbl.mem region_vals e

    val mutable sink_regions = []

    method private add_sink_region (e:Vine.exp) (size:int64) =
      self#on_missing_symbol_m sink_mem "sink";
      sink_regions <- ((self#region_for e), size) :: sink_regions

    method private choose_conc_offset_uniform ty e ident =
      let byte x = V.Constant(V.Int(V.REG_8, (Int64.of_int x))) in
      let bits = ref 0L in
	self#restore_path_cond
	  (fun () ->
	     if ty = V.REG_1 then
	       (* This special case avoids shifting REG_1s, which appears
		  to be legal in Vine IR but tickles bugs in multiple of
		  our solver backends. *)		  
	       let bit = self#extend_pc_random e false ident in
		 bits := (if bit then 1L else 0L)
	     else
	       for b = (V.bits_of_width ty) - 1 downto 0 do
		 let bit = self#extend_pc_random
		   (V.Cast(V.CAST_LOW, V.REG_1,
			   (V.BinOp(V.ARSHIFT, e,
				    (byte b))))) false (ident + b)
		 in
		   bits := (Int64.logor (Int64.shift_left !bits 1)
			      (if bit then 1L else 0L));
	       done);
	!bits

    method private choose_conc_offset_biased ty e ident =
      let const x = V.Constant(V.Int(ty, x)) in
      let rec try_list l =
	match l with
	  | [] -> self#choose_conc_offset_uniform ty e ident
	  | v :: r ->
	      if self#extend_pc_random (V.BinOp(V.EQ, e, (const v))) false
		(ident + 0x80 + (Int64.to_int v)) then
		  v
	      else
		try_list r
      in
      let bits = ref 0L in
	self#restore_path_cond
	  (fun () ->
	     bits := try_list
	       [0L; 1L; 2L; 4L; 8L; 16L; 32L; 64L; -1L; -2L; -4L; -8L]);
	!bits

    val mutable concrete_cache = Hashtbl.create 101

    method private choose_conc_offset_cached ty e ident =
      let const x = V.Constant(V.Int(ty, x)) in
      let (bits, verb) = 
	if Hashtbl.mem concrete_cache e then
	  (Hashtbl.find concrete_cache e, "Reused")
	else
	  (let bits = 
	     (* match self#query_unique_value e ty with
	       | Some v -> v
	       | None -> *)
		   match !opt_offset_strategy with
		     | UniformStrat -> self#choose_conc_offset_uniform ty e
			 ident
		     | BiasedSmallStrat -> self#choose_conc_offset_biased ty e
			 ident
	   in
	     Hashtbl.replace concrete_cache e bits;
	     (bits, "Picked")) in
	if !opt_trace_sym_addrs then
	  Printf.printf "%s concrete value 0x%Lx for %s\n"
	    verb bits (V.exp_to_string e);
	if !opt_track_sym_usage then
	  form_man#check_sym_usage e "concretized value"
	    false self#query_relevance;
	self#add_to_path_cond (V.BinOp(V.EQ, e, (const bits)));
	bits

    method private concretize_inner ty e ident =
      match e with 
	| V.Cast((V.CAST_UNSIGNED|V.CAST_SIGNED) as ckind, cty, e2) ->
	    if cty <> ty then
	      Printf.printf "Cast type is not %s in concretize_inner of %s\n"
		(V.type_to_string ty) (V.exp_to_string e);
	    assert(cty = ty);
	    let ty2 = Vine_typecheck.infer_type None e2 in
	    let bits = self#choose_conc_offset_cached ty2 e2 ident in
	    let expand =
	      match (ckind, ty2) with
		| (V.CAST_UNSIGNED, V.REG_32) -> fix_u32
		| (V.CAST_UNSIGNED, V.REG_16) -> fix_u16
		| (V.CAST_UNSIGNED, V.REG_8)  -> fix_u8
		| (V.CAST_UNSIGNED, V.REG_1)  -> fix_u1
		| (V.CAST_SIGNED,   V.REG_32) -> fix_s32
		| (V.CAST_SIGNED,   V.REG_16) -> fix_s16
		| (V.CAST_SIGNED,   V.REG_8)  -> fix_s8
		| (V.CAST_SIGNED,   V.REG_1)  -> fix_s1
		| _ -> failwith "unhandled cast kind in concretize_inner"
	    in
	      expand bits
	| _ -> self#choose_conc_offset_cached ty e ident

    method private concretize ty e ident =
      dt#start_new_query;
      let v = self#concretize_inner ty e ident in
	dt#count_query;
	v

    val mutable sink_read_count = 0L

    method private check_cond cond_e ident =
      dt#start_new_query_binary;
      let choices = ref None in 
	self#restore_path_cond
	  (fun () ->
	     let b = self#extend_pc_random cond_e false ident in
	       choices := dt#check_last_choices;
	       dt#count_query;
	       ignore(b));
	!choices

    method private region_expr e ident =
      if !opt_check_for_null then
	(match
	   self#check_cond (V.BinOp(V.EQ, e, addr_const 0L))
	     (0x3100 + self#get_stmt_num)
	 with
	   | Some true -> Printf.printf "Can be null.\n"
	   | Some false -> Printf.printf "Cannot be null.\n"
	   | None -> Printf.printf "Can be null or non-null\n";
	       infl_man#maybe_measure_influence_deref e);
      let (cbases, coffs, eoffs, ambig, syms) = classify_terms e form_man in
      let eoffs = List.map simplify_fp eoffs in
	if !opt_trace_sym_addr_details then
	  (Printf.printf "Concrete base terms: %s\n"
	     (String.concat " "
		(List.map (Printf.sprintf "0x%08Lx") cbases));
	   Printf.printf "Concrete offset terms: %s\n"
	     (String.concat " "
		(List.map (Printf.sprintf "0x%08Lx") coffs));
	   Printf.printf "Offset expression terms: %s\n"
	     (String.concat " "
		(List.map V.exp_to_string eoffs));
	   Printf.printf "Ambiguous expression terms: %s\n"
	     (String.concat " "
		(List.map V.exp_to_string ambig));
	   Printf.printf "Ambiguous symbol terms: %s\n"
	     (String.concat " "
		(List.map V.exp_to_string syms)));
	let cbase = List.fold_left Int64.add 0L cbases in
	let (base, off_syms) = match (cbase, syms, ambig) with
	  | (0L, [], []) -> raise NullDereference
	  (* adaptor expressions are classified as AmbiguousExpr, but they can
	     still be region expressions *)
	  | (0L, [], [e]) -> (Some(self#region_for e), [])
	  | (0L, [], el) -> (Some 0, el) (* TODO: Pick one element from el *)
	  | (0L, [v], _) -> (Some(self#region_for v), ambig)
	  | (0L, vl, _) ->
	      let (bvar, rest_vars) =
		(* We used to have logic here that checked whether one
		   of the symbols was known to have already been used as
		   a region base, and if so selected it. But the set of
		   region base variables expands during a run, so this
		   lead to decision tree inconsistencies. If we wanted
		   this heuristic, we need to do something more
		   complicated like always choose from among the same
		   set, but with preferences based on seen regions. For
		   now, omit that logic and always choose randomly from
		   among all the possibilties.  *)
		dt#start_new_query;
		let split_count = ref (-1) in
		  select_one vl
		    (fun () ->
		       split_count := !split_count + 1;
		       self#random_case_split !opt_trace_decisions
			 (!split_count + 0x100 + ident))
	      in
	      dt#count_query;
		if !opt_trace_sym_addrs then
		  Printf.printf "Choosing %s as the base address\n"
		    (V.exp_to_string bvar);
		(Some(self#region_for bvar), rest_vars @ ambig)
	  | (off, vl, _) ->
	      (Some 0, vl @ ambig)
	in
	let (region, offset) =
	  (match base with
	     | Some r
		 when List.exists (fun (r', _) -> r = r') sink_regions ->
		 let (r', size) =
		   List.find (fun (r', _) -> r = r') sink_regions in
		   Printf.printf "Ignoring access to sink region\n";
		   (let sat_dir = ref false in
		      self#restore_path_cond
			(fun () ->
			   sat_dir := self#extend_pc_random
			     (V.BinOp(V.LT, e, addr_const size))
			     false (ident + 0x600));
		      if !sat_dir = true then
			Printf.printf "Can be in bounds.\n"
		      else
			Printf.printf "Can be out of bounds.\n");
		   sink_read_count <- Int64.add sink_read_count 0x10L;
		   (None, sink_read_count)
	     | _ ->
		 let coff = List.fold_left Int64.add 0L coffs in
		 let offset = Int64.add (Int64.add cbase coff)
		   (match (eoffs, off_syms) with
		      | ([], []) -> 0L
		      | (el, vel) -> 
			dt#start_new_query;
			  (self#concretize_inner (reg_addr())
			     (simplify_fp (sum_list (el @ vel))))
			    (ident + 0x200)) in
		   dt#count_query;
		   (base, (fix_u32 offset)))
	in
	  (region, offset)

    method private eval_addr_exp_region_conc_path e ident =
      let term_is_known_base = function
	| V.Lval(V.Temp(var)) -> form_man#known_region_base var
	| _ -> false
      in
      let terms = split_terms e form_man in
      let (known_bases, rest) =
	List.partition term_is_known_base terms in
	match known_bases with
	  | [] ->
	      let a = form_man#eval_expr e in
		if !opt_trace_sym_addrs then
		  Printf.printf "Computed concrete value 0x%08Lx\n" a;
		if !opt_solve_path_conditions then
		  (let cond = V.BinOp(V.EQ, e, addr_const a)
		   in
		   let sat = self#extend_pc_known cond false ident true in
		     assert(sat));
		(Some 0, a)
	  | [V.Lval(V.Temp(var)) as vexp] ->
	      let sum = sum_list rest in
	      let a = form_man#eval_expr sum in
	      let a_const = addr_const a in
		if !opt_trace_sym_addrs then
		  Printf.printf
		    "Computed concrete offset %s + 0x%08Lx\n" 
		    (V.var_to_string var) a;
		if !opt_solve_path_conditions && 
		  (sum <> a_const)
		then
		  (let cond = V.BinOp(V.EQ, sum, a_const) in
		   let sat = self#extend_pc_known cond false
		     (ident + 0x400) true
		   in
		     assert(sat));
		(Some(self#region_for vexp), a)
	  | [_] -> failwith "known_base invariant failure"
	  | _ -> failwith "multiple bases"

    method eval_addr_exp_region exp ident =
      let (to_concrete, to_symbolic) = match !opt_arch with
	| (X86|ARM) -> (D.to_concrete_32, D.to_symbolic_32)
	| X64       -> (D.to_concrete_64, D.to_symbolic_64)
      in
      let v = self#eval_int_exp_simplify exp in
	try
	  (Some 0, to_concrete v)
	with NotConcrete _ ->
	  let e = to_symbolic v in
	  let eip = self#get_eip in
	    if !opt_trace_sym_addrs then
	      Printf.printf "Symbolic address %s @ (0x%Lx)\n"
		(V.exp_to_string e) eip;
	    if !opt_track_sym_usage then
	      form_man#check_sym_usage e "symbolic address"
		false self#query_relevance;
	    if !opt_concrete_path then
	      self#eval_addr_exp_region_conc_path e ident
	    else
	      self#region_expr e ident
		  
    (* Because we override handle_{load,store}, this should only be
       called for jumps. *)
    method eval_addr_exp exp =
      let (r, addr) = self#eval_addr_exp_region exp 0xa000 in
	match r with
	  | Some 0 -> addr
	  | Some r_num ->
	      if !opt_trace_stopping then
		(Printf.printf "Unsupported jump into symbolic region %d\n"
		   r_num;
                 if !opt_trace_end_jump = (Some self#get_eip) then
                   let e = D.to_symbolic_32 (self#eval_int_exp_simplify exp) in
                   let (cbases, coffs, eoffs, ambig, syms) =
                     classify_terms e form_man in
	             if cbases = [] && coffs = [] && eoffs = [] &&
                       ambig = [] && syms != [] then
                       Printf.printf "Completely symbolic load\n");
	      raise SymbolicJump
	  | None ->
	      if !opt_trace_stopping then
		Printf.printf "Unsupported jump into sink region\n";
	      raise SymbolicJump

    method private register_num reg =
      match reg with
	| R_RAX | R_EAX | R0 -> 0
	| R_RBX | R_EBX | R1 -> 1
	| R_RCX | R_ECX | R2 -> 2
	| R_RDX | R_EDX | R3 -> 3
	| R_RSI | R_ESI | R4 -> 4
	| R_RDI | R_EDI | R5 -> 5
	| R_RBP | R_EBP | R6 -> 6
	| R_RSP | R_ESP | R7 -> 7
	| R_R8  | R8  ->  8
	| R_R9  | R9  ->  9
	| R_R10 | R10 -> 10
	| R_R11 | R11 -> 11
	| R_R12 | R12 -> 12
	| R_R13 | R13 -> 13
	| R_R14 | R14 -> 14
	| R_R15 | R15 -> 15
	| _ -> 15

    method get_word_var_concretize reg do_influence name : int64 =
      let v = self#get_int_var (Hashtbl.find reg_to_var reg) in
      try (D.to_concrete_32 v)
      with NotConcrete _ ->
	let e = D.to_symbolic_32 v in
	  if do_influence then 
	    (Printf.printf "Measuring symbolic %s influence..." name;
	     infl_man#measure_point_influence name e);
	  self#concretize V.REG_32 e (0x5000 + 0x100 * (self#register_num reg))

    method get_long_var_concretize reg do_influence name : int64 =
      let v = self#get_int_var (Hashtbl.find reg_to_var reg) in
      try (D.to_concrete_64 v)
      with NotConcrete _ ->
	let e = D.to_symbolic_64 v in
	  if do_influence then
	    (Printf.printf "Measuring symbolic %s influence..." name;
	     infl_man#measure_point_influence name e);
	  self#concretize V.REG_64 e (0x5000 + 0x100 * (self#register_num reg))

    method load_long_concretize addr do_influence name =
      let v = self#load_long addr in
      try (D.to_concrete_64 v)
      with NotConcrete _ ->
	let e = D.to_symbolic_64 v in
	  if do_influence then
	    (Printf.printf "Measuring symbolic %s influence..." name;
	     infl_man#measure_point_influence name e);
	  self#concretize V.REG_64 e 0x6800

    method load_word_concretize addr do_influence name =
      let v = self#load_word addr in
      try (D.to_concrete_32 v)
      with NotConcrete _ ->
	let e = D.to_symbolic_32 v in
	  if do_influence then 
	    (Printf.printf "Measuring symbolic %s influence..." name;
	     infl_man#measure_point_influence name e);
	  self#concretize V.REG_32 e 0x6400

    method load_short_concretize addr do_influence name =
      let v = self#load_short addr in
      try (D.to_concrete_16 v)
      with NotConcrete _ ->
	let e = D.to_symbolic_16 v in
	  if do_influence then 
	    (Printf.printf "Measuring symbolic %s influence..." name;
	     infl_man#measure_point_influence name e);
	  Int64.to_int (self#concretize V.REG_16 e 0x6200)

    method load_byte_concretize addr do_influence name =
      let v = self#load_byte addr in
      try (D.to_concrete_8 v)
      with NotConcrete _ ->
	let e = D.to_symbolic_8 v in
	  if do_influence then 
	    (Printf.printf "Measuring symbolic %s influence..." name;
	     infl_man#measure_point_influence name e);
	  Int64.to_int (self#concretize V.REG_8 e 0x6100)

    method private maybe_concretize_binop op v1 v2 ty1 ty2 =
      let conc t v =
	match t with
	  | V.REG_1 ->
	      (try ignore(D.to_concrete_1 v); v
	       with NotConcrete _ ->
		 (D.from_concrete_1
		    (Int64.to_int
		       (self#concretize t (D.to_symbolic_1 v) 0x6b00))))
	  | V.REG_8 ->
	      (try ignore(D.to_concrete_8 v); v
	       with NotConcrete _ ->
		 (D.from_concrete_8
		    (Int64.to_int
		       (self#concretize t (D.to_symbolic_8 v) 0x6b00))))
	  | V.REG_16 ->
	      (try ignore(D.to_concrete_16 v); v
	       with NotConcrete _ ->
		 (D.from_concrete_16
		    (Int64.to_int
		       (self#concretize t (D.to_symbolic_16 v) 0x6b00))))
	  | V.REG_32 ->
	      (try ignore(D.to_concrete_32 v); v
	       with NotConcrete _ ->
		 (D.from_concrete_32
		    (self#concretize t (D.to_symbolic_32 v) 0x6b00)))
	  | V.REG_64 ->
	      (try ignore(D.to_concrete_64 v); v
	       with NotConcrete _ ->
		 (D.from_concrete_64
		    (self#concretize t (D.to_symbolic_64 v) 0x6b00)))
	  | _ -> failwith "Bad type in maybe_concretize_binop"
      in
	match op with
	  | V.DIVIDE | V.SDIVIDE | V.MOD | V.SMOD 
		when !opt_concretize_divisors
	      -> (v1, (conc ty2 v2))
	  | _ -> (v1, v2)

    method private store_byte_region  r addr b =
      self#region_store r 8 addr b
    method private store_short_region r addr s =
      self#region_store r 16 addr s
    method private store_word_region  r addr w =
      self#region_store r 32 addr w
    method private store_long_region  r addr l =
      self#region_store r 64 addr l

    method private load_byte_region  r addr = self#region_load r 8 addr
    method private load_short_region r addr = self#region_load r 16 addr
    method private load_word_region  r addr = self#region_load r 32 addr
    method private load_long_region  r addr = self#region_load r 64 addr

    method private query_valid e =
      let (is_sat, _) = 
	self#query_with_path_cond (V.UnOp(V.NOT, e)) false
      in
	not is_sat

    method private query_bitwidth e ty =
      let rec loop min max =
	assert(min <= max);
	if min = max then
	  min
	else
	  let mid = (min + max) / 2 in
	  let mask = Int64.shift_right_logical (-1L) (64-mid) in
	  let cond_e = V.BinOp(V.LE, e, V.Constant(V.Int(ty, mask))) in
	  let in_bounds = self#query_valid cond_e in
	    if !opt_trace_tables then
	      Printf.printf "(%s) < 2**%d: %s\n" (V.exp_to_string e) mid
		(if in_bounds then "valid" else "invalid");
	    if in_bounds then
	      loop min mid
	    else
	      loop (mid + 1) max
      in
      let max_wd = V.bits_of_width ty in
      let wd = loop 0 max_wd in
	if !opt_trace_tables then
	  Printf.printf "Bit width based on queries is %d\n" wd;
	wd

    val bitwidth_cache = Hashtbl.create 101
    val bitwidth_offset_cache = Hashtbl.create 101

    method private decide_wd op_name off_exp cloc = 
      let fast_wd = narrow_bitwidth form_man off_exp in
      let compute_wd off_exp =
	if !opt_table_limit = 0 then
	  None
	else if fast_wd > !opt_table_limit then
	  let slow_wd = self#query_bitwidth off_exp (reg_addr()) in
	    assert(slow_wd <= fast_wd);
	    if slow_wd > !opt_table_limit then
	      (if !opt_trace_tables then
		 Printf.printf
		   ("%s with base %08Lx, offset %s of size 2**%d "
		    ^^ "is not a table\n")
		   op_name cloc (V.exp_to_string off_exp) slow_wd;
	       None)
	    else
	      Some slow_wd
	else
	  Some fast_wd
      in
	if fast_wd = 0 then
	  None
	else
	  let key = (off_exp, dt#get_hist_str) in
	    try
	      let wd = Hashtbl.find bitwidth_cache key in
		if !opt_trace_tables then
		  Printf.printf "Reusing cached width %d for %s at [%s]\n%!"
		    (match wd with Some w -> w | None -> -1)
		    (V.exp_to_string off_exp) dt#get_hist_str;
		wd
	    with Not_found ->
	      let wd = match compute_wd off_exp 
		with Some 0 -> None
		| wd' -> wd'
	      in
		Hashtbl.replace bitwidth_cache key wd;
	        wd

    method private decide_offset_wd off_exp = 
      let fast_wd = narrow_bitwidth form_man off_exp in
      let compute_wd off_exp =
	if !opt_offset_limit = 0 then
	  (if !opt_trace_offset_limit then
	     Printf.printf "opt_offset_limit = 0\n";
	  Some 0)
	else if fast_wd > !opt_offset_limit then
	  let slow_wd = self#query_bitwidth off_exp (reg_addr()) in
	    assert(slow_wd <= fast_wd);
	    if slow_wd > !opt_offset_limit then
	      (if !opt_trace_offset_limit then
		 Printf.printf "Bits too large: %d\n" slow_wd;
	      None)
	    else
	      (if !opt_trace_offset_limit then
		 Printf.printf "Bits small enough: %d\n" slow_wd;
	      Some slow_wd)
	else
	  (if !opt_trace_offset_limit then
	     Printf.printf "Bits small enough: %d\n" fast_wd;
	  Some fast_wd)
      in
        if fast_wd = 0 then
	  (if !opt_trace_offset_limit then
	     Printf.printf "fast_wd = 0\n";
	  Some 0)
	else
	  let key = (off_exp, dt#get_hist_str) in
	    try
	      let wd = Hashtbl.find bitwidth_offset_cache key in
	        if !opt_trace_offset_limit then	
		  (match wd with
		    | Some ubxd_wd -> Printf.printf
		        "Loading small enough width: %d\n" ubxd_wd
		    | None -> Printf.printf "Loading too large width\n");
	        wd
	    with Not_found ->
	      let wd = compute_wd off_exp in
		Hashtbl.replace bitwidth_offset_cache key wd;
		wd
		    
    method private query_maxval e ty =
      let midpoint a b =
	let half_rounded x =
	  let half = Int64.shift_right_logical x 1 in
	    if Int64.logand x 1L = 0L then
	      half
	    else
	      Int64.add half 0L
	in
	let sz = Int64.sub b a in
	let hf_sz = half_rounded sz in
	let mid = Int64.add a hf_sz in
	assert(Vine_util.int64_ucompare a mid <= 0);
	assert(Vine_util.int64_ucompare mid b <= 0);
	mid
      in
      let rec loop min max =
	assert((int64_ucompare min max) <= 0);
	if min = max then
	  min
	else
	  let mid = 
	    if min = 0L && (int64_ucompare max 0x1000L) > 0 then
	      int64_udiv max 256L (* reduce size faster to start *)
	    else
	      midpoint min max
	  in
	  assert((int64_ucompare min mid) <= 0);
	  assert((int64_ucompare mid max) <= 0);
	  let cond_e = V.BinOp(V.LE, e, V.Constant(V.Int(ty, mid))) in
	  let in_bounds = self#query_valid cond_e in
	    if !opt_trace_tables then
	      Printf.printf "(%s) < %Ld: %s\n" (V.exp_to_string e) mid
		(if in_bounds then "valid" else "invalid");
	    if in_bounds then
	      loop min mid
	    else
	      loop (Int64.succ mid) max
      in
      let wd = narrow_bitwidth form_man e in
      let max_limit = Int64.shift_right_logical (-1L) (64-wd)
      in
      let limit = loop 0L max_limit in
	if !opt_trace_tables then
	  Printf.printf "Largest value based on queries is %Lu\n" limit;
	limit

    val maxval_cache = Hashtbl.create 101
    val maxval_offset_cache = Hashtbl.create 101
    val used_addr_cache = Hashtbl.create 101
    val dummy_vars_cache = Hashtbl.create 101
    val mutable dummy_counter = 0

    method private decide_maxval op_name off_exp cloc =
      let compute_maxval off_exp =
	if !opt_table_limit = 0 then
	  None
	else
	  let maxval = self#query_maxval off_exp (reg_addr()) in
	    if maxval > Int64.shift_left 1L !opt_table_limit then
	      (if !opt_trace_tables then
		 Printf.printf
		   ("%s with base %08Lx, offset %s of size %Ld "
		    ^^ "is not a table\n")
		   op_name cloc (V.exp_to_string off_exp) maxval;
	       None)
	    else
	      Some maxval
      in
	match off_exp with
	  | V.Constant(V.Int(_, 0L)) -> None
	  | V.Constant(V.Int(_, v)) -> Some v
	  | _ ->
	      let key = (off_exp, dt#get_hist_str) in
		try
		  let limit = Hashtbl.find maxval_cache key in
		    if !opt_trace_tables then
		      Printf.printf ("Reusing cached maxval %Ld "
				     ^^ "for %s at [%s]\n")
			(match limit with Some l -> l | None -> -1L)
			(V.exp_to_string off_exp) dt#get_hist_str;
		    limit
		with Not_found ->
		  let limit = compute_maxval off_exp in
		    Hashtbl.replace maxval_cache key limit;
		    limit

    method private decide_offset_maxval off_exp =
      let compute_maxval off_exp =
	if !opt_offset_limit = 0 then
	  Some 0L
	else
	  let maxval = self#query_maxval off_exp (reg_addr()) in
	    if maxval > Int64.shift_left 1L !opt_offset_limit then
	      None
	    else
	      Some maxval
      in
	match off_exp with
	  | V.Constant(V.Int(_, v)) -> Some v
	  | _ ->
	      let key = (off_exp, dt#get_hist_str) in
		try
		  let limit = Hashtbl.find maxval_offset_cache key in
		    limit
		with Not_found ->
		  let limit = compute_maxval off_exp in
		    Hashtbl.replace maxval_offset_cache key limit;
		    limit
		      
    method private table_load cloc off_exp wd ty =
      let stride = stride form_man off_exp in
      let shift = floor_log2 (Int64.of_int stride) in
      let idx_wd = wd - shift in
      let num_ents = 1 lsl idx_wd in
      let idx_exp =
	if stride = (1 lsl shift) then
	  let shift_amt = V.Constant(V.Int(V.REG_8, (Int64.of_int shift))) in
	    V.BinOp(V.RSHIFT, off_exp, shift_amt)
	else
	  let stride_amt = addr_const (Int64.of_int stride) in
	    V.BinOp(V.DIVIDE, off_exp, stride_amt)
      in
      let load_ent addr = match ty with
	| V.REG_8  -> form_man#simplify8
	  (self#region_load (Some 0) 8 addr)
	| V.REG_16 -> form_man#simplify16
	  (self#region_load (Some 0) 16 addr)
	| V.REG_32 -> form_man#simplify32
	  (self#region_load (Some 0) 32 addr)
	| V.REG_64 -> form_man#simplify64
	  (self#region_load (Some 0) 64 addr)
	| _ -> failwith "Unexpected type in table_load"
      in
      let table = map_n
	(fun i -> load_ent (Int64.add cloc (Int64.of_int (i * stride))))
	(num_ents - 1)
      in
        if !opt_trace_tables then
	  Printf.printf "Load with base %08Lx, size 2**%d, stride %d, idx_exp %s"
	    cloc idx_wd stride (V.exp_to_string idx_exp);
        Some (form_man#make_table_lookup table idx_exp idx_wd ty)

    method private concretize_once_and_load addr_e ty =
      let load_sym_ent addr =
	try
	  Hashtbl.find dummy_vars_cache (addr, ty)
	with Not_found ->
	  let var = match ty with
	    | V.REG_8 -> form_man#fresh_symbolic_8
	        ("dummy" ^ string_of_int dummy_counter)
	    | V.REG_16 -> form_man#fresh_symbolic_16
	        ("dummy" ^ string_of_int dummy_counter)
	    | V.REG_32 -> form_man#fresh_symbolic_32
	        ("dummy" ^ string_of_int dummy_counter)
	    | V.REG_64 -> form_man#fresh_symbolic_64
	        ("dummy" ^ string_of_int dummy_counter)
	    | _ -> failwith "Unsupported memory type"
	  in
	    dummy_counter <- dummy_counter + 1;
	    Hashtbl.replace dummy_vars_cache (addr, ty) var;
	    var
      in
      let load_ent addr = match ty with
	| V.REG_8  -> form_man#simplify8
	  (self#region_load (Some 0) 8 addr)
	| V.REG_16 -> form_man#simplify16
	  (self#region_load (Some 0) 16 addr)
	| V.REG_32 -> form_man#simplify32
	  (self#region_load (Some 0) 32 addr)
	| V.REG_64 -> form_man#simplify64
	  (self#region_load (Some 0) 64 addr)
	| _ -> failwith "Unexpected type in concretize_once_and_load"
      in
      let taut = V.BinOp(V.EQ, addr_e, addr_e) in
      let (is_sat, ce) = self#query_with_path_cond taut false in
        assert(is_sat);
        let addr = form_man#eval_expr_from_ce ce addr_e in
        let cond = V.BinOp(V.EQ, addr_e, (addr_const addr)) in
	let value =
	  if Hashtbl.mem used_addr_cache addr then
	    load_ent addr
	  else
	    load_sym_ent addr
	in
	  if !opt_trace_offset_limit then
	    Printf.printf "Concretized load once to 0x%08Lx\n" addr;
	  self#add_to_path_cond cond;
	  Some value

    method private maybe_table_or_concrete_load addr_e ty =
      let e = D.to_symbolic_32 (self#eval_int_exp_simplify addr_e) in
      let (cbases, coffs, eoffs, ambig, syms) = classify_terms e form_man in
      let cbase = List.fold_left Int64.add 0L cbases in
      let cloc = Int64.add cbase (List.fold_left Int64.add 0L coffs) in
      let off_exp = sum_list (eoffs @ ambig @ syms) in
        match (self#decide_offset_wd off_exp, !opt_trace_end_jump) with
          | (None, Some jump_addr) when jump_addr = self#get_eip ->
	      if cbases = [] && coffs = [] && eoffs = [] && ambig = [] &&
	        syms != [] then
	        Printf.printf "Completely symbolic load\n";
	      raise SymbolicJump
	  | (None, _) ->
	      self#concretize_once_and_load addr_e ty
	  | _ ->
        if cbase = 0L then
	  None
	else 
	  match self#decide_wd "Load" off_exp cloc with
	    | None -> None
	    | Some wd -> self#table_load cloc off_exp wd ty

    method private get_esp_conc_base =
      let (reg, ty) = match !opt_arch with
	| X86 -> (R_ESP, V.REG_32)
	| X64 -> (R_RSP, V.REG_64)
	| ARM -> (R13, V.REG_32)
      in
      let e = match ty with
	| V.REG_32 -> D.to_symbolic_32 (self#get_word_var_d reg)
	| V.REG_64 -> D.to_symbolic_64 (self#get_long_var_d reg)
	| _ -> failwith "Unexpected SP type in get_esp_conc_base"
      in
      let (cbases, _, _, _, _) = classify_terms e form_man in
      let cbase = List.fold_left Int64.add 0L cbases in
	cbase

    method private handle_load addr_e ty =
      if !opt_trace_offset_limit then
	Printf.printf "Loading from... %s\n" (V.exp_to_string addr_e);
      match self#maybe_table_or_concrete_load addr_e ty with
        | Some v -> (v, ty)
        | None ->
      let (r, addr) = self#eval_addr_exp_region addr_e 0x8000 in
      let v =
	(match ty with
	   | V.REG_8  -> form_man#simplify8  (self#load_byte_region  r addr)
	   | V.REG_16 -> form_man#simplify16 (self#load_short_region r addr)
	   | V.REG_32 -> form_man#simplify32 (self#load_word_region  r addr)
	   | V.REG_64 -> form_man#simplify64 (self#load_long_region  r addr)
	   | _ -> failwith "Unsupported memory type") in
	(if !opt_trace_loads then
	  (if !opt_trace_eval then
	       Printf.printf "    "; (* indent to match other details *)
	   Printf.printf "Load from %s "
	     (match r with
		| None -> "sink"
		| Some 0 -> "conc. mem"
		| Some r_num -> "region " ^ (string_of_int r_num));
	   Printf.printf "%08Lx = %s" addr (D.to_string_32 v);
	   (if !opt_use_tags then
	      Printf.printf " (%Ld @ %08Lx)" (D.get_tag v) location_id);
	   Printf.printf "\n"));
	if !opt_track_sym_usage then
	  (let stack_off = Int64.sub addr self#get_esp_conc_base in
	   let is_stack = stack_off >= -128L && stack_off <= 0x100000L in
	     form_man#check_sym_usage_d v ty "loaded value"
	       is_stack self#query_relevance);
	if r = Some 0 && (Int64.abs (fix_s32 addr)) < 4096L then
	  raise NullDereference;
	(v, ty)

    method private push_cond_prefer_true cond_v ident =
      try
	if (D.to_concrete_1 cond_v) = 1 then
	  (true, Some true)
	else
	  (false, Some false)
      with
	  NotConcrete _ ->
	    let e = D.to_symbolic_1 cond_v in
	      (dt#start_new_query_binary;
	       let b = self#extend_pc_pref e true ident true in
	       let choices = dt#check_last_choices in
		 dt#count_query;
		 (b, choices))

    method private target_region_length =
      if !opt_target_region_formulas <> [] then
	List.length !opt_target_region_formulas
      else
	String.length !opt_target_region_string

    method private target_region_byte off =
      if !opt_target_region_formulas <> [] then
	let e = List.nth !opt_target_region_formulas off in
	  ((D.from_symbolic e), (V.exp_to_string e))
      else
	let c = (!opt_target_region_string).[off] in
	  ((D.from_concrete_8 (Char.code c)),
	   (Char.escaped c))

    method private target_store_condition addr from value ty =
      let offset = Int64.to_int (Int64.sub addr from) and
	  limit_pos = Int64.add from (Int64.of_int self#target_region_length)
      in
      let in_range addr size =
	addr >= from && (Int64.add addr (Int64.of_int (size - 1))) < limit_pos
      in
      let byte_cond off v =
	let (c_v, c_str) = self#target_region_byte off in
	  if !opt_trace_target then
	    Printf.printf
	      "Store to target string offset %d: %s (vs '%s'):\n"
	      off (D.to_string_8 v) c_str;
	  D.eq8 v c_v
      in
(*       let word_cond off v = *)
(* 	let c0 = (!opt_target_region_string).[off] and *)
(* 	    c1 = (!opt_target_region_string).[off + 1] and *)
(* 	    c2 = (!opt_target_region_string).[off + 2] and *)
(* 	    c3 = (!opt_target_region_string).[off + 3] *)
(* 	in *)
(* 	let s0 = (Char.code c0) lor ((Char.code c1) lsl 8) and *)
(* 	    s2 = (Char.code c2) lor ((Char.code c3) lsl 8) *)
(* 	in *)
(* 	let w = Int64.logor (Int64.of_int s0) *)
(* 	  (Int64.shift_left (Int64.of_int s2) 16) *)
(* 	in *)
(* 	  if !opt_trace_target then *)
(* 	    Printf.printf *)
(* 	      "Store to target string offset %d: %s (vs 0x%08Lx): " *)
(* 	      off (D.to_string_32 v) w; *)
(* 	  D.eq32 v (D.from_concrete_32 w) *)
(*       in *)
	(* Ick, there are a lot of cases here, and we're only handling
	   end and not beginning overlaps. In the future, consider
	   rewriting to always treating each byte separately. *)
	match ty with
	  | V.REG_8 when in_range addr 1 ->
	      Some (offset, (byte_cond offset value), 1)
	  | V.REG_16 when in_range addr 2 ->
	      (* Fully in-bounds short store *)
	      let v0 = form_man#simplify8 (D.extract_8_from_16 value 0) and
		  v1 = form_man#simplify8 (D.extract_8_from_16 value 1)
	      in
	      let cond0 = byte_cond offset v0 and
		  cond1 = byte_cond (offset + 1) v1 in
		Some (offset, (D.bitand1 cond0 cond1), 2)
	  | V.REG_16 when in_range addr 1 ->
	      (* Partial end-overlap short store *)
	      let v0 = form_man#simplify8 (D.extract_8_from_16 value 0) in
	      let cond0 = byte_cond offset v0 in
		Some (offset, cond0, 1)
	  | V.REG_32 when in_range addr 4 ->
	      (* Fully in-bounds word store *)
	      (* Some (offset, (word_cond offset value), 4) *)
	      let v0 = form_man#simplify8 (D.extract_8_from_32 value 0) and
		  v1 = form_man#simplify8 (D.extract_8_from_32 value 1) and
		  v2 = form_man#simplify8 (D.extract_8_from_32 value 2) and
		  v3 = form_man#simplify8 (D.extract_8_from_32 value 3) in
	      let cond0 = byte_cond offset v0 and
		  cond1 = byte_cond (offset + 1) v1 and
		  cond2 = byte_cond (offset + 2) v2 and
		  cond3 = byte_cond (offset + 3) v3 in
		Some (offset, (D.bitand1 (D.bitand1 cond0 cond1)
				 (D.bitand1 cond2 cond3)), 4)
	  | V.REG_32 when in_range addr 3 ->
	      (* Word store end-overlap, 3 bytes in bounds *)
	      let v0 = form_man#simplify8 (D.extract_8_from_32 value 0) and
		  v1 = form_man#simplify8 (D.extract_8_from_32 value 1) and
		  v2 = form_man#simplify8 (D.extract_8_from_32 value 2) in
	      let cond0 = byte_cond offset v0 and
		  cond1 = byte_cond (offset + 1) v1 and
		  cond2 = byte_cond (offset + 2) v2 in
		Some (offset, (D.bitand1 cond0 (D.bitand1 cond1 cond2)), 3)
	  | V.REG_32 when in_range addr 2 ->
	      (* Word store end-overlap, 2 bytes in bounds *)
	      let v0 = form_man#simplify8 (D.extract_8_from_32 value 0) and
		  v1 = form_man#simplify8 (D.extract_8_from_32 value 1) in
	      let cond0 = byte_cond offset v0 and
		  cond1 = byte_cond (offset + 1) v1 in
		Some (offset, (D.bitand1 cond0 cond1), 2)
	  | V.REG_32 when in_range addr 1 ->
	      (* Word store end-overlap, 1 byte in bounds *)
	      let v0 = form_man#simplify8 (D.extract_8_from_32 value 0) in
	      let cond0 = byte_cond offset v0 in
		Some (offset, cond0, 1)
	  | _ -> None

    method private target_solve cond_v ident =
      let (b, choices) = self#push_cond_prefer_true cond_v ident in
	if !opt_trace_target then
	  Printf.printf "%s, %b\n"
	    (match choices with
	       | Some true -> "known equal"
	       | Some false -> "known mismatch"
	       | None -> "possible") b;
	if not b then
	  (dt#set_heur 0;
	   self#unfinish_fuzz "Target match failure";
	   if not !opt_target_no_prune then
	     raise DisqualifiedPath);
	true

    method private target_solve_single offset cond_v wd =
      if self#target_solve cond_v 0x9300 then
	((if !opt_target_guidance <> 0.0 then
	    let depth = self#input_depth in
	    let score = if depth = 0 then offset else
	      (100000 * (offset + 1) / depth) + offset
	    in
	      if !opt_trace_guidance then
		Printf.printf
		  "Achieved score %d with offset %d and depth %d\n"
		  score offset depth;
	      dt#set_heur score);
	 if !opt_finish_on_target_match &&
	   offset = (self#target_region_length) - wd
	 then
	   self#finish_fuzz "store to final target offset")

    method private table_check_full_match all_match cloc maxval =
      if !opt_trace_target then
	Printf.printf "Checking for full match: ";
      match
	self#push_cond_prefer_true (D.from_symbolic all_match) 0x9130
      with
	| (_, Some true) ->
	    if !opt_trace_target then
	      Printf.printf "Must match.\n";
	    (match (!opt_finish_on_target_match, !opt_target_region_start) with
		 (true, Some addr)
		   when addr = cloc &&
		     self#target_region_length = (Int64.to_int maxval) + 1 ->
		       self#finish_fuzz "target full match"
	       | _ -> ())
	| (_, Some false) ->
	    if !opt_trace_target then
	      Printf.printf "Cannot match.\n"
	| (_, None) ->
	    if !opt_trace_target then
	      Printf.printf "Can match.\n";
	    if !opt_finish_on_target_match then
	      self#finish_fuzz "target full match"

    method private table_store cloc off_exp e maxval ty value =
      let load_ent addr = match ty with
	| V.REG_8  -> form_man#simplify8
	  (self#region_load (Some 0) 8 addr) 
	| V.REG_16 -> form_man#simplify16
	  (self#region_load (Some 0) 16 addr) 
	| V.REG_32 -> form_man#simplify32
	  (self#region_load (Some 0) 32 addr) 
	| V.REG_64 -> form_man#simplify64
	  (self#region_load (Some 0) 64 addr) 
	| _ -> failwith "Unexpected type in table_store" 
      in
      let store_ent addr v = match ty with
	| V.REG_8  ->self#region_store (Some 0) 8 addr v
	| V.REG_16 ->self#region_store (Some 0) 16 addr v
	| V.REG_32 ->self#region_store (Some 0) 32 addr v
	| V.REG_64 ->self#region_store (Some 0) 64 addr v
	| _ -> failwith "Unexpected store type in table_store"
      in
      let stride = stride form_man off_exp in
      let stride64 = Int64.of_int stride in
      let num_ents64 = Int64.div (Int64.succ maxval) stride64 in
      let num_ents = Int64.to_int num_ents64 in
      let target_conds = ref [] in
        for i = 0 to num_ents - 1 do
	  let addr = Int64.add cloc (Int64.of_int (i * stride)) in
	  let old_v = load_ent addr in
	  let cond_e = (V.BinOp(V.EQ, e, addr_const addr)) in
	  let cond_v = D.from_symbolic cond_e in
	  let ite_v = form_man#make_ite cond_v ty value old_v in
	    store_ent addr ite_v;
	    (match (self#started_symbolic, !opt_target_region_start) with
	      | (true, Some from) ->			 
	          (match self#target_store_condition addr from ite_v ty with
		    | Some (offset, hit_cond, wd) ->
		        target_conds := (D.to_symbolic_1 hit_cond)
		          :: !target_conds
		    | None -> ())
	      | _ -> ())
        done;
        if !opt_trace_tables then
	  Printf.printf
	    "Store with base %08Lx, size %d, stride %d %s"
	    cloc num_ents stride "has symbolic address\n";
	(if !target_conds <> [] then
	   let any_match = disjoin !target_conds and
	     all_match = conjoin !target_conds in
	   if !opt_trace_target then
	     Printf.printf "Checking for any match to target: ";
	   ignore(self#target_solve (D.from_symbolic any_match) 0x9320);
	   self#table_check_full_match all_match cloc maxval);
	true

    method private concretize_once_and_store addr_e ty value =
      let store_ent addr v = match ty with
	| V.REG_8  ->self#region_store (Some 0) 8 addr v
	| V.REG_16 ->self#region_store (Some 0) 16 addr v
	| V.REG_32 ->self#region_store (Some 0) 32 addr v
	| V.REG_64 ->self#region_store (Some 0) 64 addr v
	| _ -> failwith "Unexpected store type in concretize_once_and_store"
      in
      let taut = V.BinOp(V.EQ, addr_e, addr_e) in
      let (is_sat, ce) = self#query_with_path_cond taut false in
        assert(is_sat);
        let addr = form_man#eval_expr_from_ce ce addr_e in
        let cond = V.BinOp(V.EQ, addr_e, addr_const addr) in
	  if !opt_trace_offset_limit then
	    Printf.printf "Concretized store once to 0x%08Lx\n" addr;
          store_ent addr value;
	  Hashtbl.replace used_addr_cache addr true;
	  self#add_to_path_cond cond;
	  true

    method private maybe_table_or_concrete_store addr_e ty value =
      let e = D.to_symbolic_32 (self#eval_int_exp_simplify addr_e) in
      let (cbases, coffs, eoffs, ambig, syms) = classify_terms e form_man in
      let cbase = List.fold_left Int64.add 0L cbases in
      let cloc = Int64.add cbase (List.fold_left Int64.add 0L coffs) in
      let off_exp = sum_list (eoffs @ ambig @ syms) in
        match self#decide_offset_maxval off_exp with
          | None -> self#concretize_once_and_store addr_e ty value
          | Some _ ->
	if cbase = 0L then
	  false
	else
	  match self#decide_maxval "Store" off_exp cloc with
	    | None -> false
	    | Some maxval -> self#table_store cloc off_exp e maxval ty value
	  
    method private handle_store addr_e ty rhs_e =
      if !opt_trace_offset_limit then
	Printf.printf "Storing to... %s\n" (V.exp_to_string addr_e);
      let value = self#eval_int_exp_simplify rhs_e in
      if (!opt_no_table_store) ||
	not (self#maybe_table_or_concrete_store addr_e ty value)
      then
      let (r, addr) = self#eval_addr_exp_region addr_e 0x9000 in
	if r = Some 0 && (Int64.abs (fix_s32 addr)) < 4096L then
	  raise NullDereference;
	if !opt_trace_stores then
	  if not (ty = V.REG_8 && r = None) then
	    (if !opt_trace_eval then
	       Printf.printf "    "; (* indent to match other details *)
	     Printf.printf "Store to %s "
	       (match r with
		  | None -> "sink"
		  | Some 0 -> "conc. mem"
		  | Some r_num -> "region " ^ (string_of_int r_num));
	     Printf.printf "%08Lx = %s" addr (D.to_string_32 value);
	     (if !opt_use_tags then
		Printf.printf " (%Ld @ %08Lx)" (D.get_tag value) location_id);
	     Printf.printf "\n");
	if !opt_check_store_sequence = true then (  
	  if (self#get_in_f1_range ()) = true then (
	    (*Printf.printf "SRFM#handle_store: mem store in f1 at %08Lx\n" addr;*)
	    self#add_f1_store addr;
	  ) else if (self#get_in_f2_range ()) = true then (
	    (*Printf.printf "SRFM#handle_store: mem store in f2 at %08Lx\n" addr;*)
	    self#add_f2_store addr;
	  );
	);
	if !opt_track_sym_usage then
	  (let stack_off = Int64.sub addr self#get_esp_conc_base in
	   let is_stack = stack_off >= -128L && stack_off <= 0x100000L in
	     form_man#check_sym_usage_d value ty "stored value"
	       is_stack self#query_relevance);
	(match (self#started_symbolic, !opt_target_region_start, r) with
	   | (true, Some from, Some 0) ->
	       (match self#target_store_condition addr from value ty with
		  | Some (offset, cond_v, wd) ->
		      self#target_solve_single offset cond_v wd
		  | None -> ())
	   | _ -> ());
	(match ty with
	   | V.REG_8 -> self#store_byte_region r addr value
	   | V.REG_16 -> self#store_short_region r addr value
	   | V.REG_32 -> self#store_word_region r addr value
	   | V.REG_64 -> self#store_long_region r addr value
	   | _ -> failwith "Unsupported type in memory move")

    method concretize_misc =
      if !opt_arch = X86 then
	let var = Hashtbl.find reg_to_var R_DFLAG in
	let d = self#get_int_var var in
	  try ignore(D.to_concrete_32 d)
	  with NotConcrete _ ->
	    let e = D.to_symbolic_32 d in
	      if e <> V.Unknown("uninit") then
		self#set_int_var var
		  (D.from_concrete_32 
		     (self#concretize V.REG_32 e 0x6a00))

    method make_sink_region varname size =
      self#add_sink_region
	(D.to_symbolic_32 (form_man#fresh_symbolic_32 varname)) size

    val mutable gdt_base_var = D.uninit
    val mutable ldt_base_var = D.uninit

    method make_x86_segtables_symbolic =
      let reg r v =
	self#set_int_var (Hashtbl.find reg_to_var r) v
      in
	gdt_base_var <- form_man#fresh_region_base "GDT";
	ldt_base_var <- form_man#fresh_region_base "LDT";
	reg R_GDT gdt_base_var;
	reg R_LDT ldt_base_var

    method store_word_special_region which addr v =
      let vexp = match which with
	| R_GDT -> D.to_symbolic_32 gdt_base_var
	| R_LDT -> D.to_symbolic_32 ldt_base_var
	| _ -> failwith "Unknown special region"
      in
      let region = self#region_for vexp in
	self#store_word_region (Some region) addr (D.from_concrete_32 v)

    method reset () =
      if !opt_trace_mem_snapshots = true then
	Printf.printf "SRFM#reset called\n";
      spfm#reset ();
      if !opt_trace_mem_snapshots = true then
	Printf.printf "SRFM#reset clearing regions\n";
      List.iter (fun gm -> gm#clear ()) regions;
      if !opt_trace_mem_snapshots = true then
	Printf.printf "SRFM#reset cleared regions\n";
      Hashtbl.clear region_val_queried;
      Hashtbl.clear region_vals_per_path;
      Hashtbl.clear region_conc_addr_h;
      sym_input_region_l <- [];
      f1_hash_list <- [];
      f2_hash_list <- [];
      Hashtbl.clear concrete_cache

    method apply_struct_adaptor () = 
      let else_sym_ind = ref 0 in
      let upcast expr extend_op end_sz =
	match end_sz with
	| 8  -> V.Cast(extend_op, V.REG_8 , expr)
	| 16 -> V.Cast(extend_op, V.REG_16, expr)
	| 32 -> V.Cast(extend_op, V.REG_32, expr)
	| 64 -> V.Cast(extend_op, V.REG_64, expr)
	| _ -> failwith "unsupported upcast end size"
      in
      let from_concrete v sz = 
	match sz with 
	| 8 -> assert(v >= -128 && v <= 0xff);
	  V.Constant(V.Int(V.REG_8,  (Int64.of_int (v land 0xff))))
	| 16 -> assert(v >= -65536 && v <= 0xffff);
	  V.Constant(V.Int(V.REG_16, (Int64.of_int (v land 0xffff))))
	| 32 -> V.Constant(V.Int(V.REG_32, (Int64.logand (Int64.of_int v) 0xffffffffL)))
	| 64 -> V.Constant(V.Int(V.REG_64, (Int64.of_int v)))
	| _ -> failwith "unsupported size passed to SRFM#from_concrete"
      in
      let to_sym_op exp sz = 
	match sz with
	| 8 ->  ( D.to_symbolic_8  exp) 
	| 16 -> ( D.to_symbolic_16 exp) 
	| 32 -> ( D.to_symbolic_32 exp) 
	| 64 -> ( D.to_symbolic_64 exp) 
	| _ -> failwith "unhandled target size in SRFM#apply_struct_adaptor"
      in
      let get_byte expr pos =
	V.Cast(V.CAST_LOW, V.REG_8, 
	       V.BinOp(V.RSHIFT, expr, (from_concrete (pos*8) 8)))
      in
      let unique = Vine_util.list_unique in
      (* This simplifies formulas and introduces t-variables for
	 comple sub-expressions. Doing this generally speeds things up,
	 but it may make debugging the formulas less convenient, so you
	 can disable it by make "simplify" be the identity function. *)
      let simplify e = spfm#simplify_exp e in
      (* let simplify e = e in *)

      if !opt_trace_struct_adaptor = true then
	Printf.printf "SRFM#apply_struct_adaptor starting...\n";
      if !opt_adaptor_search_mode = false then	
	let get_ite_expr arg op const_type const then_val else_val = 
	  V.Ite(V.BinOp(op, arg, V.Constant(V.Int(const_type, const))),
		then_val,
		else_val)
	in
	List.iteri ( fun sym_input_region_l_ind rnum ->
	  let (n_fields, max_size) = !opt_struct_adaptor_params in

	  let get_array_field_ranges_l field_num start_byte =
	    let get_ent f_sz_t =
	      let ret_offsets_l = ref [] in
	      let f_sz_str = ("field"^(Printf.sprintf "%d" field_num)^"_size") in
	      let f_n_str  = ("field"^(Printf.sprintf "%d" field_num)^"_n") in 
	      let field_sz = spfm#get_fresh_symbolic f_sz_str 16 in
	      let field_n  = spfm#get_fresh_symbolic f_n_str 16 in
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
		ret_offsets_l := !ret_offsets_l @ 
		  [(field_num, new_s_b, end_byte, n, f_sz_t, cond)];
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
		    ret_offsets_l := !ret_offsets_l @ 
		      [(field_num, start_b, end_b, n, f_sz, cond')]
		  ) (get_array_field_ranges_l k (end_byte+1)););
	      ) offsets_l;
	      (!ret_offsets_l @ offsets_l)
	  in
	  let t_field_h = Hashtbl.create 100 in

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
	    | [a] -> tmp_l := !tmp_l @ [a];()
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
	      tmp_l := !tmp_l @ [(field1, start1, end1, n1, f_sz1, !cond)];
	      (merge_same_field_ranges !tail)
	  in
	  merge_same_field_ranges (List.sort cmp_arr 
				     (unique (get_array_offsets_l n_fields)));
	  
	  let array_field_ranges_l = !tmp_l in
	  if !opt_trace_struct_adaptor = true then
	    Printf.printf "SRFM#array_field_ranges_l.length = %d\n" (List.length array_field_ranges_l);
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
		((!i_byte_arr).(i)) := !((!i_byte_arr).(i)) @ [(List.hd l)];
	      done;
	      populate_i_byte tail
	    | [] -> ()
	  in
	  populate_i_byte array_field_ranges_l;

	  if !opt_trace_struct_adaptor = true then (
	    for i=0 to max_size-1 do
	      Printf.printf "i_byte_arr: for byte %d: \n" i;
	      let l = !((!i_byte_arr).(i)) in
	      for j=0 to (List.length l)-1 do
		let (_, s, e, _, _, _) = (List.nth l j) in
		Printf.printf "(%d, %d), " s e;
	      done;
	      Printf.printf "\n";
	    done;
	  );
	  
	  let rec get_arr_t_field_expr field_num this_array_field_ranges_l 
	      f_type_val_list ai_byte ai_f_sz ai_n cur_depth =
	  (* Assume ai_n equals target_n for now *)
	    let get_ai_byte_expr target_n target_sz start_addr ex_op =
	      let cast_op =
		if target_sz <= ai_f_sz then 
		  if ex_op = 1 then V.CAST_SIGNED 
		  else V.CAST_UNSIGNED
		else V.CAST_LOW
	      in
	    (* translate ai_byte to a t_byte by using ai_f_sz and t_sz *)
	      let ai_q = ai_byte/ai_f_sz in
	      let ai_r = ai_byte mod ai_f_sz in
	      let tmp_addr = Int64.add start_addr (Int64.of_int (ai_q*target_sz)) in
	      let ai_entry = upcast 
		(to_sym_op (self#region_load (Some rnum) (target_sz*8) tmp_addr) (target_sz*8)) 
		cast_op (ai_f_sz*8) 
	      in 
	      get_byte ai_entry ai_r
	    in
	    let addr = 0L in
	    match this_array_field_ranges_l with
	    | [] -> failwith "SRFM#get_arr_t_field_expr ran out of this_array_field_ranges_l"
	    | [(_, start_byte, end_byte, n, f_sz, _)] -> 
	      let start_addr = (Int64.add addr (Int64.of_int start_byte)) in
	      get_ai_byte_expr n f_sz start_addr 1
	    | (_, start_byte, end_byte, n, f_sz, _)::tail ->
	      let start_addr = (Int64.add addr (Int64.of_int start_byte)) in
	      let is_extend_req = (f_sz - 8) in
	      if is_extend_req <> 0 then (
		let sign_extend_val = Int64.of_int ((start_byte lsl 32)+(end_byte lsl 16)+1) in 
		let zero_extend_val = Int64.of_int ((start_byte lsl 32)+(end_byte lsl 16)+0) in 
		if ((List.mem sign_extend_val f_type_val_list) = false) && 
		  ((List.mem zero_extend_val f_type_val_list) = false) &&
		  (n = ai_n) then (
		    let f_type_str = "f"^(Printf.sprintf "%d" field_num)^"_type" in
		    let f_type = spfm#get_fresh_symbolic f_type_str 64 in
		    let sign_extend_expr = get_ai_byte_expr n f_sz start_addr 1 in
		    let zero_extend_expr = get_ai_byte_expr n f_sz start_addr 0 in

		    let else_depth = 
		      if !opt_split_target_formulas = true then (
			if cur_depth >= 8 then 0 else cur_depth+2 )
		      else 0
		    in
		    let else_expr = 
		      simplify
			(get_arr_t_field_expr field_num tail
			   (f_type_val_list @ [sign_extend_val] @ [zero_extend_val])
			   ai_byte ai_f_sz ai_n else_depth) in
		    let final_else_expr = 
		      if cur_depth >= 8 then (
			let else_sym_str = Printf.sprintf "else_%d_%d_%d_%d_%d_%d" 
			  field_num start_byte end_byte n f_sz !else_sym_ind in
			let else_sym = spfm#get_fresh_symbolic else_sym_str 8 in
			else_sym_ind := !else_sym_ind + 1;
			spfm#add_to_path_cond (V.BinOp(V.EQ, else_sym, else_expr));
			else_sym
		      ) else ( else_expr ) in
		    
		    get_ite_expr f_type V.EQ V.REG_64 sign_extend_val sign_extend_expr 
		      (get_ite_expr f_type V.EQ V.REG_64 zero_extend_val zero_extend_expr
			 final_else_expr )
		   ) else (
		    simplify (get_arr_t_field_expr field_num tail
				f_type_val_list ai_byte ai_f_sz ai_n cur_depth)
		   )
	      ) else (
		let sign_extend_val = Int64.of_int ((start_byte lsl 32)+(end_byte lsl 16)+1) in 
		if ((List.mem sign_extend_val f_type_val_list) = false) &&
		  (ai_n = n) then (
		    let f_type_str = "f"^(Printf.sprintf "%d" field_num)^"_type" in
		    let f_type = spfm#get_fresh_symbolic f_type_str 64 in
		    let sign_extend_expr = get_ai_byte_expr n f_sz start_addr 1 in
		    let else_depth = 
		      if !opt_split_target_formulas = true then (
			if cur_depth >= 8 then 0 else cur_depth+2 )
		      else 0
		    in
		    let else_expr = 
		      simplify (get_arr_t_field_expr field_num tail
				  (f_type_val_list @ [sign_extend_val])
				  ai_byte ai_f_sz ai_n else_depth) in
		    let final_else_expr = 
		      if cur_depth >= 8 then (
			let else_sym_str = Printf.sprintf "else_%d_%d_%d_%d_%d_%d" 
			  field_num start_byte end_byte n f_sz !else_sym_ind in
			let else_sym = spfm#get_fresh_symbolic else_sym_str 8 in
			else_sym_ind := !else_sym_ind + 1;
			spfm#add_to_path_cond (V.BinOp(V.EQ, else_sym, else_expr));
			else_sym
		      ) else ( else_expr ) in

		    get_ite_expr f_type V.EQ V.REG_64 sign_extend_val sign_extend_expr 
		      final_else_expr
		   ) else (
		    simplify (get_arr_t_field_expr field_num tail
				f_type_val_list ai_byte ai_f_sz ai_n cur_depth)
		   )
	      )
	  in
	  let field_exprs = Hashtbl.create 1001 in
	  let rec get_arr_ite_ai_byte_expr this_array_field_ranges_l i_byte =
	    (* i_byte = interesting_byte *)
	    match this_array_field_ranges_l with
	    | [] -> from_concrete 0 8
	    | (field, start_byte, end_byte, ai_n, ai_f_sz, cond)::tail ->
	      if (i_byte >= start_byte) && (i_byte <= end_byte) then (
		let field_size_temp_str = "arr_srfm_t_field_"^
		  (Printf.sprintf "%d_n%d_sz%d_b%d_%d" field ai_n ai_f_sz 
		     (i_byte-start_byte) sym_input_region_l_ind)
		in
		let field_size_temp = spfm#get_fresh_symbolic field_size_temp_str 8 in
		let q_exp = 
		  (try
		     Hashtbl.find field_exprs field_size_temp_str
		   with Not_found ->
		     let new_q_exp =
		       V.BinOp(V.EQ, field_size_temp,
			       (get_arr_t_field_expr field array_field_ranges_l []
				  (i_byte-start_byte) ai_f_sz ai_n 0)) in
		       Hashtbl.replace field_exprs field_size_temp_str new_q_exp;
		       spfm#add_to_path_cond new_q_exp;
		       new_q_exp)
		in
		
		if !opt_trace_struct_adaptor = true then 
		  Hashtbl.replace t_field_h field_size_temp q_exp;
		
		V.Ite(cond, field_size_temp, (get_arr_ite_ai_byte_expr tail i_byte))
	      ) else (
		get_arr_ite_ai_byte_expr tail i_byte
	      )
	  in
	  
	  let byte_expr_l = ref [] in
	  for i=0 to (max_size-1) do 
	    let byte_expr = (get_arr_ite_ai_byte_expr (!((!i_byte_arr).(i))) i) in
	    let byte_expr_sym_str = "arr_ai_byte_"^(Printf.sprintf "%d_%d" i sym_input_region_l_ind) in
	    let byte_expr_sym = spfm#get_fresh_symbolic byte_expr_sym_str 8 in
	    let q_exp = V.BinOp(V.EQ, byte_expr_sym, byte_expr) in
	    if !opt_trace_struct_adaptor = true then 
	      Printf.printf "SRFM#get_arr_ite_ai_byte_expr for byte %d: %s\n\n" i
		(V.exp_to_string q_exp);
	    spfm#add_to_path_cond q_exp; 
	    byte_expr_l := !byte_expr_l @ [(D.from_symbolic byte_expr_sym)];
	  done;

	if !opt_trace_struct_adaptor = true then 
	  Hashtbl.iter (fun key value ->
	    Printf.printf "SRFM#apply_struct_adaptor t_field_h[%s] = %s\n" 
	      (V.exp_to_string key) (V.exp_to_string value);
	  ) t_field_h; 
	
	  
	  for i=0 to (max_size-1) do
	    self#region_store (Some rnum) 8 (Int64.of_int i) (List.nth !byte_expr_l i);
	  done;
	  
	) sym_input_region_l;

  end
    
end
    
