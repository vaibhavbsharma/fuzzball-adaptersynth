(*
  Copyright (C) BitBlaze, 2009-2013, and copyright (C) 2010 Ensighta
  Security Inc.  All rights reserved.
*)

module V = Vine;;

open Exec_domain;;
open Exec_exceptions;;
open Exec_utils;;
open Exec_options;;
open Formula_manager;;
open Query_engine;;
open Stpvc_engine;;
open Stp_external_engine;;
open Concrete_memory;;
open Granular_memory;;

let bool64 f = fun a b -> if (f a b) then 1L else 0L

(* Like String.trim, but compatible with OCaml 3.12 *)
let str_trim s =
  let is_space = function
    | ' ' | '\012' | '\n' | '\r' | '\t' -> true
    | _ -> false
  in
  let len = String.length s in
  let i = ref 0 in
  while !i < len && is_space s.[!i] do incr i done;
  let j = ref (len - 1) in
  while !j >= !i && is_space s.[!j] do decr j done;
  if !i = 0 && !j = len - 1 then
    s
  else if !j >= !i then
    String.sub s !i (!j - !i + 1)
  else
    ""

(* It's a bit inefficient to use the pretty-printer when the whole
   point is that we don't want extra whitespace. *)
let stmt_to_string_compact st =
  str_trim (V.stmt_to_string st)

let move_hash src dest =
  V.VarHash.clear dest;
  V.VarHash.iter (fun a b -> V.VarHash.add dest a b) src

let skip_strings =
  (let h = Hashtbl.create 2 in
     Hashtbl.replace h "NoOp" ();
     Hashtbl.replace h "x86g_use_seg_selector" ();
     Hashtbl.replace h "Skipped: AbiHint" ();
     h)

(* The interface for Vine to give us the disassembly of an instruction
   is to put it in a comment, but it uses comments for other things as
   well. So this code tries to filter out all the things that are not
   instruction disassemblies. It would be cleaner to have a special
   syntax. *)
let comment_is_insn s =
  (not (Hashtbl.mem skip_strings s))
  && ((String.length s < 13) || (String.sub s 0 13) <> "eflags thunk:")

    
class virtual special_handler = object(self)
  method virtual handle_special : string -> V.stmt list option
  method virtual make_snap : unit
  method virtual reset : unit
  method virtual make_f1_snap : unit
  method virtual reset_f1_snap : unit
  method virtual make_f2_snap : unit
  method virtual reset_f2_snap : unit
end

type register_name = 
  (* VEX generic *)
  | R_CC_OP | R_CC_DEP1 | R_CC_DEP2 | R_CC_NDEP
  | R_IP_AT_SYSCALL | R_EMWARN | R_EMNOTE
  (* Common to x86, x64, and ARM: *)
  | R_CF | R_ZF
  (* Common to x86 and x64: *)
  | R_PF | R_AF | R_SF | R_OF
  | R_DFLAG | R_IDFLAG | R_ACFLAG
  | R_CS | R_DS| R_ES | R_FS | R_GS | R_SS
  | R_FTOP | R_FPROUND | R_FC3210 | R_SSEROUND 
  (* x87 FP, currently only supported on x86: *)
  | R_FPREG0 | R_FPREG1 | R_FPREG2 | R_FPREG3
  | R_FPREG4 | R_FPREG5 | R_FPREG6 | R_FPREG7
  | R_FPTAG0 | R_FPTAG1 | R_FPTAG2 | R_FPTAG3
  | R_FPTAG4 | R_FPTAG5 | R_FPTAG6 | R_FPTAG7
  (* SSE, 32-bit-x86-style 128 bit: *)
  | R_XMM0L | R_XMM0H | R_XMM1L | R_XMM1H | R_XMM2L | R_XMM2H
  | R_XMM3L | R_XMM3H | R_XMM4L | R_XMM4H | R_XMM5L | R_XMM5H
  | R_XMM6L | R_XMM6H | R_XMM7L | R_XMM7H
  (* x86 *)
  | R_EBP | R_ESP | R_ESI | R_EDI | R_EIP | R_EAX | R_EBX | R_ECX | R_EDX
  | EFLAGSREST | R_LDT | R_GDT 
  (* x64 *)
  | R_RBP | R_RSP | R_RSI | R_RDI | R_RIP | R_RAX | R_RBX | R_RCX | R_RDX
  | R_R8 | R_R9 | R_R10 | R_R11 | R_R12 | R_R13 | R_R14 | R_R15
  | R_RFLAGSREST
  | R_FS_BASE | R_GS_BASE
  (* SSE, x64-style expanded: *)
  | R_YMM0_0 | R_YMM0_1 | R_YMM0_2 | R_YMM0_3
  | R_YMM1_0 | R_YMM1_1 | R_YMM1_2 | R_YMM1_3
  | R_YMM2_0 | R_YMM2_1 | R_YMM2_2 | R_YMM2_3
  | R_YMM3_0 | R_YMM3_1 | R_YMM3_2 | R_YMM3_3
  | R_YMM4_0 | R_YMM4_1 | R_YMM4_2 | R_YMM4_3
  | R_YMM5_0 | R_YMM5_1 | R_YMM5_2 | R_YMM5_3
  | R_YMM6_0 | R_YMM6_1 | R_YMM6_2 | R_YMM6_3
  | R_YMM7_0 | R_YMM7_1 | R_YMM7_2 | R_YMM7_3
  | R_YMM8_0 | R_YMM8_1 | R_YMM8_2 | R_YMM8_3
  | R_YMM9_0 | R_YMM9_1 | R_YMM9_2 | R_YMM9_3
  | R_YMM10_0 | R_YMM10_1 | R_YMM10_2 | R_YMM10_3
  | R_YMM11_0 | R_YMM11_1 | R_YMM11_2 | R_YMM11_3
  | R_YMM12_0 | R_YMM12_1 | R_YMM12_2 | R_YMM12_3
  | R_YMM13_0 | R_YMM13_1 | R_YMM13_2 | R_YMM13_3
  | R_YMM14_0 | R_YMM14_1 | R_YMM14_2 | R_YMM14_3
  | R_YMM15_0 | R_YMM15_1 | R_YMM15_2 | R_YMM15_3
  (* ARM *)
  | R0 | R1 |  R2 |  R3 |  R4 |  R5 |  R6 |  R7
  | R8 | R9 | R10 | R11 | R12 | R13 | R14 | R15 | R15T
  |  R_D0 |  R_D1 |  R_D2 |  R_D3 |  R_D4 |  R_D5 |  R_D6 |  R_D7
  |  R_D8 |  R_D9 | R_D10 | R_D11 | R_D12 | R_D13 | R_D14 | R_D15
  | R_D16 | R_D17 | R_D18 | R_D19 | R_D20 | R_D21 | R_D22 | R_D23
  | R_D24 | R_D25 | R_D26 | R_D27 | R_D28 | R_D29 | R_D30 | R_D31
  | R_CC | R_NF | R_VF
  | R_QFLAG32 | R_GEFLAG0 | R_GEFLAG1 | R_GEFLAG2 | R_GEFLAG3
  | R_TISTART | R_TILEN | R_NRADDR
  | R_FPSCR | R_TPIDRURO | R_ITSTATE

let reg_to_regstr reg = match reg with
  | R_EBP -> "R_EBP" | R_ESP -> "R_ESP" | R_ESI -> "R_ESI"
  | R_EDI -> "R_EDI" | R_EIP -> "R_EIP" | R_EAX -> "R_EAX" | R_EBX -> "R_EBX"
  | R_ECX -> "R_ECX" | R_EDX -> "R_EDX"
  | R_RBP -> "R_RBP" | R_RSP -> "R_RSP" | R_RSI -> "R_RSI"
  | R_RDI -> "R_RDI" | R_RIP -> "R_RIP" | R_RAX -> "R_RAX" | R_RBX -> "R_EBX"
  | R_RCX -> "R_RCX" | R_RDX -> "R_RDX"
  | R_R8 -> "R_R8" | R_R9 -> "R_R9" | R_R10 -> "R_R10" | R_R11 -> "R_R11"
  | R_R12 -> "R_R12" | R_R13 -> "R_R13" | R_R14 -> "R_R14" | R_R15 -> "R_R15"
  | R_RFLAGSREST -> "R_RFLAGSREST"
  | R_FS_BASE -> "R_FS_BASE" | R_GS_BASE -> "R_GS_BASE"
  | EFLAGSREST -> "EFLAGSREST" | R_CF -> "R_CF" | R_PF -> "R_PF"
  | R_AF -> "R_AF"| R_ZF -> "R_ZF" | R_SF -> "R_SF" | R_OF -> "R_OF"
  | R_CC_OP -> "R_CC_OP" | R_CC_DEP1 -> "R_CC_DEP1"
  | R_CC_DEP2 -> "R_CC_DEP2" | R_CC_NDEP -> "R_CC_NDEP"
  | R_DFLAG -> "R_DFLAG" | R_IDFLAG -> "R_IDFLAG" | R_ACFLAG -> "R_ACFLAG"
  | R_EMWARN -> "R_EMWARN" | R_EMNOTE -> "R_EMNOTE"
  | R_LDT -> "R_LDT" | R_GDT -> "R_GDT" | R_CS -> "R_CS" | R_DS -> "R_DS"
  | R_ES -> "R_ES" | R_FS -> "R_FS" | R_GS -> "R_GS"| R_SS -> "R_SS"
  | R_FTOP -> "R_FTOP" | R_FPROUND -> "R_FPROUND" | R_FC3210  -> "R_FC3210"
  | R_FPREG0 -> "R_FPREG0" | R_FPREG1 -> "R_FPREG1"
  | R_FPREG2 -> "R_FPREG2" | R_FPREG3 -> "R_FPREG3"
  | R_FPREG4 -> "R_FPREG4" | R_FPREG5 -> "R_FPREG5"
  | R_FPREG6 -> "R_FPREG6" | R_FPREG7 -> "R_FPREG7"
  | R_FPTAG0 -> "R_FPTAG0" | R_FPTAG1 -> "R_FPTAG1"
  | R_FPTAG2 -> "R_FPTAG2" | R_FPTAG3 -> "R_FPTAG3"
  | R_FPTAG4 -> "R_FPTAG4" | R_FPTAG5 -> "R_FPTAG5"
  | R_FPTAG6 -> "R_FPTAG6" | R_FPTAG7 -> "R_FPTAG7"
  | R_SSEROUND -> "R_SSEROUND" | R_IP_AT_SYSCALL -> "R_IP_AT_SYSCALL"
  | R_XMM0L -> "R_XMM0L" | R_XMM0H -> "R_XMM0H"
  | R_XMM1L -> "R_XMM1L" | R_XMM1H -> "R_XMM1H"
  | R_XMM2L -> "R_XMM2L" | R_XMM2H -> "R_XMM2H"
  | R_XMM3L -> "R_XMM3L" | R_XMM3H -> "R_XMM3H"
  | R_XMM4L -> "R_XMM4L" | R_XMM4H -> "R_XMM4H"
  | R_XMM5L -> "R_XMM5L" | R_XMM5H -> "R_XMM5H"
  | R_XMM6L -> "R_XMM6L" | R_XMM6H -> "R_XMM6H"
  | R_XMM7L -> "R_XMM7L" | R_XMM7H -> "R_XMM7H"
  | R_YMM0_0 -> "R_YMM0_0" | R_YMM0_1 -> "R_YMM0_1"
  | R_YMM0_2 -> "R_YMM0_2" | R_YMM0_3 -> "R_YMM0_3"
  | R_YMM1_0 -> "R_YMM1_0" | R_YMM1_1 -> "R_YMM1_1"
  | R_YMM1_2 -> "R_YMM1_2" | R_YMM1_3 -> "R_YMM1_3"
  | R_YMM2_0 -> "R_YMM2_0" | R_YMM2_1 -> "R_YMM2_1"
  | R_YMM2_2 -> "R_YMM2_2" | R_YMM2_3 -> "R_YMM2_3"
  | R_YMM3_0 -> "R_YMM3_0" | R_YMM3_1 -> "R_YMM3_1"
  | R_YMM3_2 -> "R_YMM3_2" | R_YMM3_3 -> "R_YMM3_3"
  | R_YMM4_0 -> "R_YMM4_0" | R_YMM4_1 -> "R_YMM4_1"
  | R_YMM4_2 -> "R_YMM4_2" | R_YMM4_3 -> "R_YMM4_3"
  | R_YMM5_0 -> "R_YMM5_0" | R_YMM5_1 -> "R_YMM5_1"
  | R_YMM5_2 -> "R_YMM5_2" | R_YMM5_3 -> "R_YMM5_3"
  | R_YMM6_0 -> "R_YMM6_0" | R_YMM6_1 -> "R_YMM6_1"
  | R_YMM6_2 -> "R_YMM6_2" | R_YMM6_3 -> "R_YMM6_3"
  | R_YMM7_0 -> "R_YMM7_0" | R_YMM7_1 -> "R_YMM7_1"
  | R_YMM7_2 -> "R_YMM7_2" | R_YMM7_3 -> "R_YMM7_3"
  | R_YMM8_0 -> "R_YMM8_0" | R_YMM8_1 -> "R_YMM8_1"
  | R_YMM8_2 -> "R_YMM8_2" | R_YMM8_3 -> "R_YMM8_3"
  | R_YMM9_0 -> "R_YMM9_0" | R_YMM9_1 -> "R_YMM9_1"
  | R_YMM9_2 -> "R_YMM9_2" | R_YMM9_3 -> "R_YMM9_3"
  | R_YMM10_0 -> "R_YMM10_0" | R_YMM10_1 -> "R_YMM10_1"
  | R_YMM10_2 -> "R_YMM10_2" | R_YMM10_3 -> "R_YMM10_3"
  | R_YMM11_0 -> "R_YMM11_0" | R_YMM11_1 -> "R_YMM11_1"
  | R_YMM11_2 -> "R_YMM11_2" | R_YMM11_3 -> "R_YMM11_3"
  | R_YMM12_0 -> "R_YMM12_0" | R_YMM12_1 -> "R_YMM12_1"
  | R_YMM12_2 -> "R_YMM12_2" | R_YMM12_3 -> "R_YMM12_3"
  | R_YMM13_0 -> "R_YMM13_0" | R_YMM13_1 -> "R_YMM13_1"
  | R_YMM13_2 -> "R_YMM13_2" | R_YMM13_3 -> "R_YMM13_3"
  | R_YMM14_0 -> "R_YMM14_0" | R_YMM14_1 -> "R_YMM14_1"
  | R_YMM14_2 -> "R_YMM14_2" | R_YMM14_3 -> "R_YMM14_3"
  | R_YMM15_0 -> "R_YMM15_0" | R_YMM15_1 -> "R_YMM15_1"
  | R_YMM15_2 -> "R_YMM15_2" | R_YMM15_3 -> "R_YMM15_3"
  | R0  ->  "R0" | R1  ->  "R1" |  R2 ->  "R2" | R3  -> "R3"
  | R4  ->  "R4" | R5  ->  "R5" |  R6 ->  "R6" | R7  -> "R7"
  | R8  ->  "R8" | R9  ->  "R9" | R10 -> "R10" | R11 -> "R11"
  | R12 -> "R12" | R13 -> "R13" | R14 -> "R14" | R15 -> "R15"
  | R15T -> "R15T"
  | R_D0  -> "R_D0"  | R_D1  -> "R_D1"  | R_D2  -> "R_D2"  | R_D3  ->  "R_D3"
  | R_D4  -> "R_D4"  | R_D5  -> "R_D5"  | R_D6  -> "R_D6"  | R_D7  ->  "R_D7"
  | R_D8  -> "R_D8"  | R_D9  -> "R_D9"  | R_D10 -> "R_D10" | R_D11 -> "R_D11"
  | R_D12 -> "R_D12" | R_D13 -> "R_D13" | R_D14 -> "R_D14" | R_D15 -> "R_D15"
  | R_D16 -> "R_D16" | R_D17 -> "R_D17" | R_D18 -> "R_D18" | R_D19 -> "R_D19"
  | R_D20 -> "R_D20" | R_D21 -> "R_D21" | R_D22 -> "R_D22" | R_D23 -> "R_D23"
  | R_D24 -> "R_D24" | R_D25 -> "R_D25" | R_D26 -> "R_D26" | R_D27 -> "R_D27"
  | R_D28 -> "R_D28" | R_D29 -> "R_D29" | R_D30 -> "R_D30" | R_D31 -> "R_D31"
  | R_CC -> "R_CC" | R_NF -> "R_NF" | R_VF -> "R_VF" | R_QFLAG32 -> "R_QFLAG32"
  | R_GEFLAG0 -> "R_GEFLAG0" | R_GEFLAG1 -> "R_GEFLAG1"
  | R_GEFLAG2 -> "R_GEFLAG2" | R_GEFLAG3 -> "R_GEFLAG3"
  | R_TISTART -> "R_TISTART" | R_TILEN -> "R_TILEN"
  | R_NRADDR -> "R_NRADDR"
  | R_FPSCR -> "R_FPSCR" | R_TPIDRURO -> "R_TPIDRURO"
  | R_ITSTATE -> "R_ITSTATE"

let regstr_to_reg s = match s with
  | "R_EBP" -> R_EBP | "R_ESP" -> R_ESP | "R_ESI" -> R_ESI
  | "R_EDI" -> R_EDI | "R_EIP" -> R_EIP | "R_EAX" -> R_EAX | "R_EBX" -> R_EBX
  | "R_ECX" -> R_ECX | "R_EDX" -> R_EDX
  | "R_RBP" -> R_RBP | "R_RSP" -> R_RSP | "R_RSI" -> R_RSI
  | "R_RDI" -> R_RDI | "R_RIP" -> R_RIP | "R_RAX" -> R_RAX | "R_RBX" -> R_RBX
  | "R_RCX" -> R_RCX | "R_RDX" -> R_RDX
  | "R_R8" -> R_R8 | "R_R9" -> R_R9 | "R_R10" -> R_R10 | "R_R11" -> R_R11
  | "R_R12" -> R_R12 | "R_R13" -> R_R13 | "R_R14" -> R_R14 | "R_R15" -> R_R15
  | "R_RFLAGSREST" -> R_RFLAGSREST
  | "R_FS_BASE" -> R_FS_BASE | "R_GS_BASE" -> R_GS_BASE
  | "EFLAGSREST" -> EFLAGSREST | "R_CF" -> R_CF | "R_PF" -> R_PF
  | "R_AF" -> R_AF| "R_ZF" -> R_ZF | "R_SF" -> R_SF | "R_OF" -> R_OF
  | "R_CC_OP" -> R_CC_OP | "R_CC_DEP1" -> R_CC_DEP1
  | "R_CC_DEP2" -> R_CC_DEP2 | "R_CC_NDEP" -> R_CC_NDEP
  | "R_DFLAG" -> R_DFLAG | "R_IDFLAG" -> R_IDFLAG | "R_ACFLAG" -> R_ACFLAG
  | "R_EMWARN" -> R_EMWARN | "R_EMNOTE" -> R_EMNOTE
  | "R_LDT" -> R_LDT | "R_GDT" -> R_GDT | "R_CS" -> R_CS | "R_DS" -> R_DS
  | "R_ES" -> R_ES | "R_FS" -> R_FS | "R_GS" -> R_GS| "R_SS" -> R_SS
  | "R_FTOP" -> R_FTOP | "R_FPROUND" -> R_FPROUND | "R_FC3210"  -> R_FC3210
  | "R_FPREG0" -> R_FPREG0 | "R_FPREG1" -> R_FPREG1
  | "R_FPREG2" -> R_FPREG2 | "R_FPREG3" -> R_FPREG3
  | "R_FPREG4" -> R_FPREG4 | "R_FPREG5" -> R_FPREG5
  | "R_FPREG6" -> R_FPREG6 | "R_FPREG7" -> R_FPREG7
  | "R_FPTAG0" -> R_FPTAG0 | "R_FPTAG1" -> R_FPTAG1
  | "R_FPTAG2" -> R_FPTAG2 | "R_FPTAG3" -> R_FPTAG3
  | "R_FPTAG4" -> R_FPTAG4 | "R_FPTAG5" -> R_FPTAG5
  | "R_FPTAG6" -> R_FPTAG6 | "R_FPTAG7" -> R_FPTAG7
  | "R_SSEROUND" -> R_SSEROUND | "R_IP_AT_SYSCALL" -> R_IP_AT_SYSCALL
  | "R_XMM0L" -> R_XMM0L | "R_XMM0H" -> R_XMM0H
  | "R_XMM1L" -> R_XMM1L | "R_XMM1H" -> R_XMM1H
  | "R_XMM2L" -> R_XMM2L | "R_XMM2H" -> R_XMM2H
  | "R_XMM3L" -> R_XMM3L | "R_XMM3H" -> R_XMM3H
  | "R_XMM4L" -> R_XMM4L | "R_XMM4H" -> R_XMM4H
  | "R_XMM5L" -> R_XMM5L | "R_XMM5H" -> R_XMM5H
  | "R_XMM6L" -> R_XMM6L | "R_XMM6H" -> R_XMM6H
  | "R_XMM7L" -> R_XMM7L | "R_XMM7H" -> R_XMM7H
  | "R_YMM0_0" -> R_YMM0_0 | "R_YMM0_1" -> R_YMM0_1
  | "R_YMM0_2" -> R_YMM0_2 | "R_YMM0_3" -> R_YMM0_3
  | "R_YMM1_0" -> R_YMM1_0 | "R_YMM1_1" -> R_YMM1_1
  | "R_YMM1_2" -> R_YMM1_2 | "R_YMM1_3" -> R_YMM1_3
  | "R_YMM2_0" -> R_YMM2_0 | "R_YMM2_1" -> R_YMM2_1
  | "R_YMM2_2" -> R_YMM2_2 | "R_YMM2_3" -> R_YMM2_3
  | "R_YMM3_0" -> R_YMM3_0 | "R_YMM3_1" -> R_YMM3_1
  | "R_YMM3_2" -> R_YMM3_2 | "R_YMM3_3" -> R_YMM3_3
  | "R_YMM4_0" -> R_YMM4_0 | "R_YMM4_1" -> R_YMM4_1
  | "R_YMM4_2" -> R_YMM4_2 | "R_YMM4_3" -> R_YMM4_3
  | "R_YMM5_0" -> R_YMM5_0 | "R_YMM5_1" -> R_YMM5_1
  | "R_YMM5_2" -> R_YMM5_2 | "R_YMM5_3" -> R_YMM5_3
  | "R_YMM6_0" -> R_YMM6_0 | "R_YMM6_1" -> R_YMM6_1
  | "R_YMM6_2" -> R_YMM6_2 | "R_YMM6_3" -> R_YMM6_3
  | "R_YMM7_0" -> R_YMM7_0 | "R_YMM7_1" -> R_YMM7_1
  | "R_YMM7_2" -> R_YMM7_2 | "R_YMM7_3" -> R_YMM7_3
  | "R_YMM8_0" -> R_YMM8_0 | "R_YMM8_1" -> R_YMM8_1
  | "R_YMM8_2" -> R_YMM8_2 | "R_YMM8_3" -> R_YMM8_3
  | "R_YMM9_0" -> R_YMM9_0 | "R_YMM9_1" -> R_YMM9_1
  | "R_YMM9_2" -> R_YMM9_2 | "R_YMM9_3" -> R_YMM9_3
  | "R_YMM10_0" -> R_YMM10_0 | "R_YMM10_1" -> R_YMM10_1
  | "R_YMM10_2" -> R_YMM10_2 | "R_YMM10_3" -> R_YMM10_3
  | "R_YMM11_0" -> R_YMM11_0 | "R_YMM11_1" -> R_YMM11_1
  | "R_YMM11_2" -> R_YMM11_2 | "R_YMM11_3" -> R_YMM11_3
  | "R_YMM12_0" -> R_YMM12_0 | "R_YMM12_1" -> R_YMM12_1
  | "R_YMM12_2" -> R_YMM12_2 | "R_YMM12_3" -> R_YMM12_3
  | "R_YMM13_0" -> R_YMM13_0 | "R_YMM13_1" -> R_YMM13_1
  | "R_YMM13_2" -> R_YMM13_2 | "R_YMM13_3" -> R_YMM13_3
  | "R_YMM14_0" -> R_YMM14_0 | "R_YMM14_1" -> R_YMM14_1
  | "R_YMM14_2" -> R_YMM14_2 | "R_YMM14_3" -> R_YMM14_3
  | "R_YMM15_0" -> R_YMM15_0 | "R_YMM15_1" -> R_YMM15_1
  | "R_YMM15_2" -> R_YMM15_2 | "R_YMM15_3" -> R_YMM15_3
  | "R0"  ->  R0 | "R1"  ->  R1 |  "R2" ->  R2 | "R3"  -> R3
  | "R4"  ->  R4 | "R5"  ->  R5 |  "R6" ->  R6 | "R7"  -> R7
  | "R8"  ->  R8 | "R9"  ->  R9 | "R10" -> R10 | "R11" -> R11
  | "R12" -> R12 | "R13" -> R13 | "R14" -> R14 | "R15" -> R15
  | "R15T" -> R15T
  | "R_D0"  -> R_D0  | "R_D1"  -> R_D1  | "R_D2"  -> R_D2  | "R_D3"  -> R_D3
  | "R_D4"  -> R_D4  | "R_D5"  -> R_D5  | "R_D6"  -> R_D6  | "R_D7"  -> R_D7
  | "R_D8"  -> R_D8  | "R_D9"  -> R_D9  | "R_D10" -> R_D10 | "R_D11" -> R_D11
  | "R_D12" -> R_D12 | "R_D13" -> R_D13 | "R_D14" -> R_D14 | "R_D15" -> R_D15
  | "R_D16" -> R_D16 | "R_D17" -> R_D17 | "R_D18" -> R_D18 | "R_D19" -> R_D19
  | "R_D20" -> R_D20 | "R_D21" -> R_D21 | "R_D22" -> R_D22 | "R_D23" -> R_D23
  | "R_D24" -> R_D24 | "R_D25" -> R_D25 | "R_D26" -> R_D26 | "R_D27" -> R_D27
  | "R_D28" -> R_D28 | "R_D29" -> R_D29 | "R_D30" -> R_D30 | "R_D31" -> R_D31
  | "R_CC" -> R_CC | "R_NF" -> R_NF | "R_VF" -> R_VF | "R_QFLAG32" -> R_QFLAG32
  | "R_GEFLAG0" -> R_GEFLAG0 | "R_GEFLAG1" -> R_GEFLAG1
  | "R_GEFLAG2" -> R_GEFLAG2 | "R_GEFLAG3" -> R_GEFLAG3
  | "R_TISTART" -> R_TISTART | "R_TILEN" -> R_TILEN
  | "R_NRADDR" -> R_NRADDR
  | "R_FPSCR" -> R_FPSCR | "R_TPIDRURO" -> R_TPIDRURO
  | "R_ITSTATE" -> R_ITSTATE
  | _ -> failwith ("Unrecognized register name " ^ s)

class virtual fragment_machine = object
  method virtual init_prog : Vine.program -> unit
  method virtual set_frag : Vine.program -> unit
  method virtual concretize_misc : unit
  method virtual add_extra_eip_hook :
      (fragment_machine -> int64 -> unit) -> unit
  method virtual add_range_opt : string -> bool ref -> unit
  method virtual eip_hook : int64 -> unit
  method virtual get_eip : int64
  method virtual set_eip : int64 -> unit
  method virtual run_eip_hooks : unit
  method virtual get_esp : int64
  method virtual jump_hook : string -> int64 -> int64 -> unit
  method virtual run_jump_hooks : string -> int64 -> int64 -> unit
  
  method virtual set_cjmp_heuristic :
    (int64 -> int64 -> int64 -> float -> bool option -> bool option) -> unit

  method virtual on_missing_zero : unit
  method virtual on_missing_random : unit
  method virtual on_missing_symbol : unit

  method virtual make_regs_zero : unit
  method virtual make_regs_symbolic : unit
  method virtual load_x86_user_regs : Temu_state.userRegs -> unit
  method virtual print_regs : unit
  method virtual print_syscall_regs : unit
  method virtual printable_word_reg : register_name -> string
  method virtual printable_long_reg : register_name -> string

  method virtual store_byte_conc  : int64 -> int   -> unit
  method virtual store_short_conc : int64 -> int   -> unit
  method virtual store_word_conc  : int64 -> int64 -> unit
  method virtual store_long_conc  : int64 -> int64 -> unit

  method virtual load_sym : int64 -> int -> Vine.exp
  method virtual store_sym : int64 -> int -> Vine.exp -> unit
  
  method virtual store_page_conc  : int64 -> string -> unit

  method virtual load_byte_conc  : int64 -> int
  method virtual load_short_conc : int64 -> int
  method virtual load_word_conc  : int64 -> int64
  method virtual load_long_conc  : int64 -> int64

  method virtual load_byte_concolic  : int64 -> int
  method virtual load_byte_symbolic  : int64 -> Vine.exp
  method virtual load_word_symbolic  : int64 -> Vine.exp
  method virtual store_byte_symbolic  : int64 -> Vine.exp -> unit
  method virtual store_word_symbolic  : int64 -> Vine.exp -> unit
  method virtual load_short_concolic : int64 -> int
  method virtual load_word_concolic  : int64 -> int64
  method virtual load_long_concolic  : int64 -> int64

  method virtual started_symbolic : bool
  method virtual maybe_start_symbolic : (unit -> unit) -> unit
  method virtual start_symbolic : unit

  method virtual finish_fuzz : string -> unit
  method virtual unfinish_fuzz : string -> unit
  method virtual finish_reasons : string list

  method virtual make_snap : unit -> unit
  method virtual reset : unit -> unit
  method virtual read_repair_frag_inputs : unit
  method virtual read_invalid_repair_frag_inputs : unit
  method virtual read_wrong_adapters: unit
  method virtual get_repair_tests_processed : int
  method virtual inc_repair_tests_processed : int
  method virtual get_invalid_repair_tests_processed : int
  method virtual inc_invalid_repair_tests_processed : int
  method virtual get_adapter_search_mode_stdin_fd : Unix.file_descr
  method virtual conc_mem_struct_adapter: bool -> unit
  method virtual sym_region_struct_adapter: unit

  method virtual add_special_handler : special_handler -> unit

  method virtual get_bit_var   : register_name -> int
  method virtual get_byte_var  : register_name -> int
  method virtual get_short_var : register_name -> int
  method virtual get_word_var  : register_name -> int64
  method virtual get_long_var  : register_name -> int64

  method virtual get_bit_var_concolic   : register_name -> int
  method virtual get_byte_var_concolic  : register_name -> int
  method virtual get_short_var_concolic : register_name -> int
  method virtual get_word_var_concolic  : register_name -> int64
  method virtual get_long_var_concolic  : register_name -> int64

  method virtual set_bit_var   : register_name -> int   -> unit
  method virtual set_byte_var  : register_name -> int   -> unit
  method virtual set_short_var : register_name -> int   -> unit
  method virtual set_word_var  : register_name -> int64 -> unit
  method virtual set_long_var  : register_name -> int64 -> unit

  method virtual set_word_var_low_short   : register_name -> int -> unit
  method virtual set_word_var_low_byte    : register_name -> int -> unit
  method virtual set_word_var_second_byte : register_name -> int -> unit

  method virtual set_word_reg_symbolic : register_name -> string -> unit
  method virtual set_word_reg_concolic :
    register_name -> string -> int64 -> unit
  method virtual set_word_reg_fresh_symbolic : register_name -> string
    -> string
  method virtual set_reg_fresh_region : register_name -> string -> unit

  method virtual get_fresh_symbolic : string -> int -> Vine.exp
  method virtual get_reg_symbolic : register_name -> Vine.exp
  method virtual query_exp : Vine.exp -> Vine.exp -> unit
  method virtual simplify_exp : Vine.exp -> Vine.exp
  method virtual save_args : int64 -> unit
  method virtual get_saved_args : unit -> Vine.exp list
  method virtual reset_saved_args : unit
  method virtual add_adapted_addr: int64 -> unit
  method virtual set_reg_symbolic : register_name -> Vine.exp -> unit
  method virtual make_f1_sym_snap : unit 
  method virtual make_f1_conc_snap : unit 
  method virtual save_f1_sym_se : unit
  method virtual save_f1_conc_se : unit
  method virtual make_f2_sym_snap : unit
  method virtual make_f2_conc_snap : unit
  method virtual compare_sym_se : unit
  method virtual compare_conc_se : unit
  method virtual make_f1_special_handlers_snap : unit
  method virtual reset_f1_special_handlers_snap : unit
  method virtual make_f2_special_handlers_snap : unit
  method virtual reset_f2_special_handlers_snap : unit
  method virtual make_table_lookup : (Vine.exp list) -> Vine.exp -> int -> Vine.typ -> Vine.exp
 
  method virtual add_f1_store : int64 -> unit
  method virtual add_f2_store : int64 -> unit
  method virtual match_writes : unit -> bool
 
  method virtual set_long_reg_symbolic : register_name -> string -> unit
  method virtual set_long_reg_fresh_symbolic : register_name -> string
    -> string

  method virtual run_sl : (string -> bool) -> Vine.stmt list -> string
		  
  method virtual run : unit -> string
  method virtual run_to_jump : unit -> string
  method virtual fake_call_to_from : int64 -> int64 -> Vine.stmt list
  method virtual disasm_insn_at : int64 -> string

  method virtual measure_mem_size : int * int * int
  method virtual measure_form_man_size : int * int
  method virtual measure_dt_size : int
  method virtual measure_size : int * int

  method virtual store_byte_idx : int64 -> int -> int -> unit

  method virtual store_str : int64 -> int64 -> string -> unit

  method virtual make_symbolic_region : int64 -> int -> string -> int -> unit
  method virtual make_fresh_symbolic_region : int64 -> int -> unit

  method virtual store_symbolic_cstr : int64 -> int -> bool -> bool -> unit
  method virtual store_concolic_cstr : int64 -> string -> bool -> unit
  method virtual store_concolic_name_str :
                   int64 -> string -> string -> int -> unit

  method virtual store_symbolic_wcstr : int64 -> int -> unit

  method virtual store_symbolic_byte  : int64 -> string -> unit
  method virtual store_symbolic_short : int64 -> string -> unit
  method virtual store_symbolic_word  : int64 -> string -> unit
  method virtual store_symbolic_long  : int64 -> string -> unit

  method virtual store_concolic_mem_byte :
    int64 -> string -> int64 -> int -> unit

  method virtual store_concolic_byte  : int64 -> string -> int   -> unit
  method virtual store_concolic_short : int64 -> string -> int   -> unit
  method virtual store_concolic_word  : int64 -> string -> int64 -> unit
  method virtual store_concolic_long  : int64 -> string -> int64 -> unit

  method virtual set_reg_conc_bytes : register_name 
    -> (int option array) -> unit
  method virtual set_reg_concolic_mem_bytes : register_name 
    -> ((string * int64 * int) option array) -> unit

  method virtual store_concolic_exp : int64 -> V.exp ->
    (string * int) list -> (string * int) list ->
    (string * int64) list -> (string * int64) list -> unit
  method virtual set_word_reg_concolic_exp : register_name -> V.exp ->
    (string * int) list -> (string * int) list ->
    (string * int64) list -> (string * int64) list -> unit

  method virtual mem_byte_has_loop_var  : int64 -> bool
  method virtual mem_short_has_loop_var : int64 -> bool
  method virtual mem_word_has_loop_var  : int64 -> bool
  method virtual mem_long_has_loop_var  : int64 -> bool
  method virtual word_reg_has_loop_var : register_name -> bool

  method virtual parse_symbolic_expr : string -> Vine.exp

  method virtual store_cstr : int64 -> int64 -> string -> unit

  method virtual read_buf : int64 -> int -> char array

  method virtual read_cstr : int64 -> string

  method virtual zero_fill : int64 -> int -> unit

  method virtual print_backtrace : unit

  method virtual eval_expr_to_int64 : Vine.exp -> int64
      
  method virtual eval_expr_to_symbolic_expr : Vine.exp -> Vine.exp

  method virtual watchpoint : unit

  method virtual mem_val_as_string : int64 -> Vine.typ -> string

  method virtual get_path_cond : Vine.exp list

  method virtual set_query_engine : Query_engine.query_engine -> unit

  method virtual query_with_path_cond : Vine.exp -> bool
    -> (bool * Query_engine.sat_assign)

  method virtual query_condition : Vine.exp -> bool option -> int -> (bool * bool option) 
  method virtual query_unique_value : Vine.exp -> Vine.typ -> int64 option
  method virtual add_to_path_cond : Vine.exp -> unit

  method virtual match_input_var : string -> int option

  method virtual print_tree : out_channel -> unit

  method virtual set_iter_seed : int -> unit

  method virtual random_byte : int

  method virtual finish_path : bool

  method virtual after_exploration : unit

  method virtual make_x86_segtables_symbolic : unit
  method virtual store_word_special_region :
    register_name -> int64 -> int64 -> unit

  method virtual get_word_var_concretize :
    register_name -> bool -> string -> int64

  method virtual get_long_var_concretize :
    register_name -> bool -> string -> int64

  method virtual load_byte_concretize  : int64 -> bool -> string -> int
  method virtual load_short_concretize : int64 -> bool -> string -> int
  method virtual load_word_concretize  : int64 -> bool -> string -> int64
  method virtual load_long_concretize  : int64 -> bool -> string -> int64

  method virtual make_sink_region : string -> int64 -> unit
 
  method virtual get_in_f1_range: unit -> bool
  method virtual get_in_f2_range: unit -> bool
  method virtual add_f1_syscall_with_args: int -> Vine.exp list -> unit
  method virtual check_f2_syscall: int -> bool
  method virtual check_f2_syscall_args: Vine.exp list -> int -> bool
  method virtual match_syscalls: unit -> bool
  method virtual reset_syscalls: unit
  method virtual reset_struct_counts: unit 

  method virtual restrict_symbolic_expr : 
    register_name list -> int -> (Vine.exp -> Vine.exp) -> unit
  
  method virtual check_adapter_condition : Vine.exp -> unit

end

module FragmentMachineFunctor =
  functor (D : DOMAIN) ->
struct
  module GM = GranularMemoryFunctor(D)
  module FormMan = FormulaManagerFunctor(D)

  let change_some_short_bytes form_man d bytes construct =
    assert(Array.length bytes = 2);
    let select old = function
      | None -> old
      | Some x -> construct x
    in
    let o0 = D.extract_8_from_16 d 0 and
	o1 = D.extract_8_from_16 d 1 in
    let b0 = select o0 bytes.(0) and
	b1 = select o1 bytes.(1) in
      form_man#simplify16 (D.reassemble16 b0 b1)

  let change_some_word_bytes form_man d bytes construct =
    assert(Array.length bytes = 4);
    let select old = function
      | None -> old
      | Some x -> construct x
    in
    let o0 = D.extract_8_from_32 d 0 and
	o1 = D.extract_8_from_32 d 1 and
	o2 = D.extract_8_from_32 d 2 and
	o3 = D.extract_8_from_32 d 3 in
    let b0 = select o0 bytes.(0) and
	b1 = select o1 bytes.(1) and
	b2 = select o2 bytes.(2) and
	b3 = select o3 bytes.(3) in
      form_man#simplify32
	(D.reassemble32 (D.reassemble16 b0 b1) (D.reassemble16 b2 b3))

  let change_some_long_bytes form_man d bytes construct =
    assert(Array.length bytes = 8);
    let select old = function
      | None -> old
      | Some x -> construct x
    in
    let o0 = D.extract_8_from_32 d 0 and
	o1 = D.extract_8_from_32 d 1 and
	o2 = D.extract_8_from_32 d 2 and
	o3 = D.extract_8_from_32 d 3 and
	o4 = D.extract_8_from_32 d 4 and
	o5 = D.extract_8_from_32 d 5 and
	o6 = D.extract_8_from_32 d 6 and
	o7 = D.extract_8_from_32 d 7 in
    let b0 = select o0 bytes.(0) and
	b1 = select o1 bytes.(1) and
	b2 = select o2 bytes.(2) and
	b3 = select o3 bytes.(3) and
	b4 = select o4 bytes.(4) and
	b5 = select o5 bytes.(5) and
	b6 = select o6 bytes.(6) and
	b7 = select o7 bytes.(7) in
      form_man#simplify64
	(D.reassemble64
	   (D.reassemble32 (D.reassemble16 b0 b1) (D.reassemble16 b2 b3))
	   (D.reassemble32 (D.reassemble16 b4 b5) (D.reassemble16 b6 b7)))

  class frag_machine = object(self)
      
    val mem = (new GM.granular_second_snapshot_memory
		 (new GM.granular_snapshot_memory
		    (new GM.concrete_maybe_adapter_memory
		       (new string_maybe_memory))
		    (new GM.granular_hash_memory))
		 (new GM.granular_snapshot_memory
		    (new GM.granular_hash_memory)
		    (new GM.granular_hash_memory)))

    val reg_store = V.VarHash.create 100
    val reg_to_var = Hashtbl.create 100
    
    val form_man = new FormMan.formula_manager
    method get_form_man = form_man
    
    val mutable in_f1_range = false
    val mutable in_f2_range = false
    val mutable f1_syscalls:(int list) = []
    val mutable f2_syscalls_num = 0
    val mutable f1_syscalls_args:(Vine.exp list) = []
    val mutable f2_syscalls_arg_num = 0
 
    val mutable saved_args:(Vine.exp list) = []
    val mutable adapted_arg_addrs:(int64 list) = []

    val mutable saved_f1_rsp = 0L
    val mutable saved_f2_rsp = 0L
    val mutable f1_write_addr_l:(int64 list) = []
    val mutable f2_write_addr_l:(int64 list) = []

    val mutable f1_se = new GM.granular_hash_memory 
    val mutable f1_hash : ( (int64, GM.gran64) Hashtbl.t) = Hashtbl.create 0
    val mutable f2_se = new GM.granular_hash_memory

    (* return register value saved for f1, f2. Used only for repair *)
    val mutable f1_ret_reg_val:(Vine.exp option ref) = ref None 
    val mutable f2_ret_reg_val:(Vine.exp option ref) = ref None
    val mutable num_repair_tests_processed:(int ref) = ref 0
    val mutable num_invalid_repair_tests_processed:(int ref) = ref 0
    val mutable repair_frag_inputs:(int list list) = []
    val mutable invalid_repair_frag_inputs:(int list list) = []
    val mutable stdin_redirect_fd:(Unix.file_descr option ref) = ref None
    val mutable e_o_f1_count = ref 0
    val mutable f2_init_count = ref 0

    method add_adapted_addr addr =
      adapted_arg_addrs <- adapted_arg_addrs @ [addr]
	
    method add_f1_store addr = 
      if (self#is_nonlocal_addr saved_f1_rsp addr) = true then
	( if !opt_trace_stores then
	    Printf.printf "FM#add_f1_store: %08Lx outside local scope(%08Lx)\n" 
	      addr saved_f1_rsp;
	  f1_write_addr_l <- f1_write_addr_l @ [addr] ;
	);
      ()

    method private is_nonlocal_addr rsp addr =
      if List.mem addr adapted_arg_addrs then false
	else (
      if (rsp <= addr) || ((addr <= 0x60000000L) && (addr >= 0x00700000L)) then
	true 
      else false)
	
    method add_f2_store addr = 
      if (self#is_nonlocal_addr saved_f2_rsp addr) = true then
	( if !opt_trace_stores then
	    Printf.printf "FM#add_f2_store: %08Lx outside local scope(%08Lx)\n" 
	      addr saved_f2_rsp;
	 if ((List.length f1_write_addr_l) > (List.length f2_write_addr_l)) &&
	   ((List.nth f1_write_addr_l (List.length f2_write_addr_l)) = addr) then
	   (f2_write_addr_l <- f2_write_addr_l @ [addr] ;)
	 else (
	   raise DisqualifiedPath;
	 )
	);
      ()
	
    method match_writes () = 
      (List.length f1_write_addr_l) = (List.length f2_write_addr_l)

    method save_args nargs =
      if !opt_trace_repair || !opt_trace_adapter then (Printf.printf "repair: saving %Ld args\n" nargs; flush(stdout););
      let args = match (!opt_arch,!opt_fragments) with
	| (X64,false) -> [R_RDI;R_RSI;R_RDX;R_RCX;R_R8;R_R9] 
	| (ARM,false) -> [R0; R1; R2; R3;]
	| (ARM,true) -> [R0; R1; R2; R3; R4; R5; R6; R7; R8; R9; R10; R11; R12]
	| (X86,false) -> (* arguments are loaded from the stack *)
	   let args_base_addr = Int64.add (self#get_word_var R_ESP)
	     (if !opt_repair_frag_start = Int64.minus_one then 4L else 0L)  in
	   for i = 0 to (Int64.to_int nargs)-1 do
	     saved_args <- saved_args @
	       [(D.to_symbolic_64 (mem#load_word (Int64.add args_base_addr (Int64.of_int (i*4)))))];
	   done;
	  []
	| _ -> failwith "unsupported architecture for save_args";
      in
      if (List.length saved_args) = 0 then (
	for i = 0 to (Int64.to_int nargs)-1 do
	  saved_args <- saved_args @ [(self#get_reg_symbolic (List.nth args i))];
	done
      );
      if !opt_trace_repair || !opt_trace_adapter then (
	Printf.printf "repair: saved %d args\n" (List.length saved_args); flush(stdout););
   
    method get_saved_args () = saved_args

    method reset_saved_args = 
      saved_args <- [];

    method get_in_f1_range () = in_f1_range 
    
    method get_in_f2_range () = in_f2_range
    
    method add_f1_syscall_with_args syscall_num arg_list = 
      f1_syscalls <- f1_syscalls@[syscall_num] ;
      f1_syscalls_args <- f1_syscalls_args@arg_list;
    
    method check_f2_syscall syscall_num = 
      f2_syscalls_num <- 1 + f2_syscalls_num;
      if ((List.length f1_syscalls) >= f2_syscalls_num) &&
	(List.nth f1_syscalls (f2_syscalls_num-1)) = syscall_num then
	true
      else false
	
    (* returns true if f2 syscall args diverge from f1 *)
    method check_f2_syscall_args arg_list syscall_num=
      let start_ind = f2_syscalls_arg_num in
      let end_ind = (f2_syscalls_arg_num + (List.length arg_list)) in
      let ret = 
	if ((List.length f1_syscalls_args) >= end_ind) then
	  (
	    let is_diverge = ref false in
	    for i = start_ind to (end_ind-1) do
	      let arg1_exp = (D.to_symbolic_64 (
		form_man#simplify64 (D.from_symbolic (
		  List.nth f1_syscalls_args i)))) in
	      let arg2_exp = (D.to_symbolic_64 (
		form_man#simplify64 (D.from_symbolic (
		  List.nth arg_list (i-start_ind))))) in
	      if !opt_trace_syscalls then
		Printf.printf "f1_arg_exp = %s f2_arg_exp = %s\n" 
		  (V.exp_to_string arg1_exp)
		  (V.exp_to_string arg2_exp);
	      let exp = 
		(* wait4 syscall uses only the low 32 bits of its 1st and 3rd argument*)
		if (syscall_num = 61) && ((i = start_ind) || (i = start_ind+2))then (
		  V.BinOp(V.NEQ, 
			  V.Cast(V.CAST_SIGNED, V.REG_64, V.Cast(V.CAST_LOW, V.REG_32, arg1_exp)), 
			  V.Cast(V.CAST_SIGNED, V.REG_64, V.Cast(V.CAST_LOW, V.REG_32, arg2_exp)))) 
		else ( V.BinOp(V.NEQ, arg1_exp, arg2_exp))
	      in
	      let preferred_dir = not !opt_adapter_search_mode in
	      let (b,choices) = (self#query_condition exp (Some preferred_dir) (0x6d00+i*10)) in
	      let choices_str = 
		(match choices with
		| Some true -> "is true"
		| Some false -> "is false"
		| None -> "can be true or false")
	      in
	      if !opt_trace_syscalls then
		Printf.printf "chose branch %B with choices %s\n" b choices_str;
	      if b = true then (
		is_diverge := true;
		Printf.printf "diverged on syscall(%d) arg%d %s vs %s\n" syscall_num i 
		  (V.exp_to_string arg1_exp) 
		  (V.exp_to_string arg2_exp);
	      )
	    done;
	    !is_diverge
	  )
	else (
	  false
	) 
      in
      f2_syscalls_arg_num <- f2_syscalls_arg_num + (List.length arg_list);
      (* if ret = false then adapter_score := !adapter_score + 1; *)
      ret

    method match_syscalls () =
      if !opt_dont_compare_syscalls then true else (
	if ((List.length f1_syscalls) <> f2_syscalls_num) then
	  false
	else true)

    method reset_syscalls = 
      f1_syscalls <- [];
      f2_syscalls_num <- 0;
      f1_syscalls_args <- [];
      f2_syscalls_arg_num <- 0;
      f1_write_addr_l <- [];
      f2_write_addr_l <- [];
 
    val temps = V.VarHash.create 100
    val mutable mem_var = V.newvar "mem" (V.TMem(V.REG_32, V.Little))
    val mutable frag = ([], [])
    val mutable insns = []

    method restrict_symbolic_expr args i restriction =
      let expr = self#get_reg_symbolic (List.nth args i)
                 (*D.to_symbolic_64 
                   (form_man#simplify64 
                     (D.from_symbolic (List.nth args i)))*) in
      let (b, choices) = self#query_condition (restriction expr) (Some true) (0x6d00+i*10) in
      (let str = match choices with
		         | Some true -> "is true"
		         | Some false -> "is false"
		         | None -> "can be true or false"
	   in Printf.printf "chose branch %B with choices %s\n" b str;
       if b then () 
       else (raise DisqualifiedPath))
	
    method check_adapter_condition expr =
      (* TODO this function is still in progress *)
      let (b, choices) = self#query_condition expr (Some true) (0x6d00) in 
      ((*let str = match choices with
		         | Some true -> "is true)"
		         | Some false -> "is false)"
		         | None -> "can be true or false)"
	   in Printf.printf "chose branch %B (with choice: %s\n" b str;*)
       if b then () 
       else (Printf.printf "fragment_machine: adapter violates restriction, raising DisqualifiedPath\n";
             raise DisqualifiedPath)) 
    
    method set_reg_symbolic reg symb_var =
      self#set_int_var (Hashtbl.find reg_to_var reg)
        (D.from_symbolic symb_var);    
      
    method make_f1_sym_snap = 
      (* this method is implemented in SRFM *)
      if !opt_trace_mem_snapshots = true then
	Printf.printf "FM#make_f1_sym_snap called\n";
      ()

    method private save_f1_ret_reg =
      f1_ret_reg_val := Some (self#get_reg_symbolic
	(match !opt_arch with
	| X64 -> R_RAX
	| ARM -> R0
	| X86 -> R_EAX))


    method private save_f2_ret_reg =
      f2_ret_reg_val := Some (self#get_reg_symbolic
	(match !opt_arch with
	| X64 -> R_RAX
	| ARM -> R0
	| X86 -> R_EAX))

    method private compare_ret_reg_vals =
      assert(not !opt_verify_adapter);
      match (!f1_ret_reg_val, !f2_ret_reg_val) with
      | (Some e1, Some e2) ->
	 if !opt_trace_repair then (
	   Printf.printf "repair: f1_ret_reg_val = %s, f2_ret_reg_val = %s\n"
	     (V.exp_to_string e1) (V.exp_to_string e2);
	   flush(stdout););
	let (b, _) = self#query_condition (V.BinOp(V.EQ, e1, e2)) (Some !opt_adapter_search_mode) 0x6e00 in
	b
      | (None, None) -> true
      | _ -> false

    method private compare_f2_syscall_num =
      if !opt_trace_repair then (
	Printf.printf "f1 made %d syscalls, f2 made %d syscalls\n" (List.length f1_syscalls) f2_syscalls_num;
	flush(stdout););
      (List.length f1_syscalls) = f2_syscalls_num
	
    method save_f1_sym_se = 
      (* this method is implemented in SRFM *)
      if !opt_trace_mem_snapshots = true then
	Printf.printf "FM#save_f1_sym_se called\n";
      ()
    
    method make_f2_sym_snap = 
      (* this method is implemented in SRFM *)
      if !opt_trace_mem_snapshots = true then
	Printf.printf "FM#make_f2_sym_snap called\n";
      ()
	
    method compare_sym_se =
      (* this method is implemented in SRFM *)
      if !opt_trace_mem_snapshots = true then
	Printf.printf "FM#compare_sym_se called\n";
      ()
   
    method make_f1_conc_snap = 
      if !opt_trace_mem_snapshots = true then
	Printf.printf "FM#make_f1_conc_snap called\n";
      mem#make_snap ();
      ()

    method save_f1_conc_se = 
      if !opt_trace_mem_snapshots = true then
	Printf.printf "FM#save_f1_conc_se called\n";
      self#conc_mem_struct_adapter true;
      f1_se <- mem#get_level4;
      f1_hash <- Hashtbl.copy f1_se#get_mem;
      mem#reset4_3 ();
      ()

    method make_f2_conc_snap = 
      (* reset back to level 3 already completed in save_f1_conc_se *)
      if !opt_trace_mem_snapshots = true then
	Printf.printf "FM#make_f2_conc_snap called\n";
      mem#make_snap ();
      ()

    method compare_conc_se =
      (* compare side-effects on concrete memory between f1 and f2 *)
      if !opt_trace_mem_snapshots = true then
	Printf.printf "FM#compare_conc_se called\n";
      f2_se <- mem#get_level4;
      let f2_hash = (f2_se#get_mem) in
      let f1_nonlocal_se = Hashtbl.create 0 in
      let f2_nonlocal_se = Hashtbl.create 0 in
      Hashtbl.iter (fun addr chunk ->
	let (exp1, _) = GM.gran64_get_long chunk (f1_se#get_missing) addr in
	let exp = D.to_symbolic_64 exp1 in
	if (self#is_nonlocal_addr saved_f1_rsp addr) = true then
	  (if !opt_trace_mem_snapshots = true then
	      Printf.printf "In f1, addr = %Lx, rsp = %Lx was non-local side-effect\n" 
		addr saved_f1_rsp;
	   Hashtbl.replace f1_nonlocal_se addr exp;)
      ) f1_hash;
      Hashtbl.iter (fun addr chunk ->
	let (exp1, _) = GM.gran64_get_long chunk (f2_se#get_missing) addr in
	let exp = D.to_symbolic_64 exp1 in
	if (self#is_nonlocal_addr saved_f2_rsp addr) = true then
	  (if !opt_trace_mem_snapshots = true then
	      Printf.printf "In f2, addr = %Lx, rsp = %Lx was non-local side-effect\n" 
		addr saved_f2_rsp;
	   Hashtbl.replace f2_nonlocal_se addr exp;)
      ) f2_hash;
      
      (* Check for non-local memory side-effects equivalence here *)
      if f1_nonlocal_se = f2_nonlocal_se then
	(if !opt_trace_mem_snapshots = true then
	  Printf.printf "all side-effects were equal\n";)
      else 
      (
      (* Iterate through f1_nonlocal_se, f2_nonlocal_se and check for equivalence *)
	Hashtbl.iter ( fun addr f1_exp ->
	  let f2_exp =
	  try 
	    Hashtbl.find f2_nonlocal_se addr
	  with Not_found -> (* f1 wrote to an address that f2 did not *)
	    D.to_symbolic_64 (mem#load_long addr) in
	  if !opt_trace_mem_snapshots = true then (
	    Printf.printf "addr = %Lx f1_exp = %s f2_exp = %s\n"
	      addr (V.exp_to_string f1_exp) (V.exp_to_string f2_exp);
	    flush(stdout);
	  );
	  self#query_exp f1_exp f2_exp;
	) f1_nonlocal_se;
	Hashtbl.iter ( fun addr f2_exp -> 
	  (* Check if f2 wrote to an address that f1 did not *)
	  try 
	    ignore(Hashtbl.find f1_nonlocal_se addr)
	  with Not_found ->
	    (* is this correct ? wont this mem#load_long give us the same expr
	       that is f2's non-local side-effect *)
	    if f2_exp <> V.Constant(V.Int(V.REG_64, 0L)) then (
	      if !opt_trace_mem_snapshots = true then
		Printf.printf "addr = %Lx f2_exp = %s, f2 wrote to an address, f1 did not\n"
		  addr (V.exp_to_string f2_exp);
	      raise DisqualifiedPath;
	    );
	) f2_nonlocal_se;
      );
      mem#reset4_3 ();
      saved_f1_rsp <- 0L;
      saved_f2_rsp <- 0L;
      ()
	
    (* Check if two expressions are syntactically or semantically equal,
       disqualify the path if not *)
    method query_exp exp1 exp2 =
      if exp1 = exp2 then
	(if !opt_trace_mem_snapshots = true then
	    Printf.printf "equal side-effects %s = %s\n"
	      (V.exp_to_string exp1) 
	      (V.exp_to_string exp2);
	 (* adapter_score := !adapter_score + 1; *)
	)
      else (
	let q_exp = V.BinOp(V.EQ, exp1, exp2) in
	let (b,_) = (self#query_condition q_exp (Some true) 0x6df0) in
	if b = false then (
	  if !opt_trace_mem_snapshots = true then
	    Printf.printf "inequivalent side-effects %s!=\n%s\n" 
	      (V.exp_to_string exp1) (V.exp_to_string exp2);
	  raise DisqualifiedPath;
	)
	else (
	  if !opt_trace_mem_snapshots = true then
	    Printf.printf "equivalent side-effects %s=\n%s"
	      (V.exp_to_string exp1) (V.exp_to_string exp2);
	  (* adapter_score := !adapter_score + 1; *)
	)
      );
	flush(stdout);

    method simplify_exp e =
      let v = D.from_symbolic e in
	match Vine_typecheck.infer_type_fast e with
	  | V.REG_1  -> D.to_symbolic_1  (form_man#simplify1  v)
	  | V.REG_8  -> D.to_symbolic_8  (form_man#simplify8  v)
	  | V.REG_16 -> D.to_symbolic_16 (form_man#simplify16 v)
	  | V.REG_32 -> D.to_symbolic_32 (form_man#simplify32 v)
	  | V.REG_64 -> D.to_symbolic_64 (form_man#simplify64 v)
	  | _ -> failwith "Bad size in simplify_exp"

    method get_reg_symbolic reg =
      D.to_symbolic_64 (self#get_int_var (Hashtbl.find reg_to_var reg))
    
    method get_fresh_symbolic name size = 
      match size with
        | 1  -> D.to_symbolic_1 (form_man#fresh_symbolic_1 name)
        | 8  -> D.to_symbolic_8 (form_man#fresh_symbolic_8 name)
        | 16 -> D.to_symbolic_16 (form_man#fresh_symbolic_16 name)
        | 32 -> D.to_symbolic_32 (form_man#fresh_symbolic_32 name)
        | 64 -> D.to_symbolic_64 (form_man#fresh_symbolic_64 name)
        | _ -> failwith "Bad size in on_missing_symbol"
    
    method load_byte_symbolic  addr = D.to_symbolic_8 (mem#load_byte addr)

    method load_word_symbolic  addr = D.to_symbolic_32 (mem#load_word addr)
  
    method store_byte_symbolic  addr b = mem#store_byte addr (D.from_symbolic b) 

    method store_word_symbolic  addr w = mem#store_word addr (D.from_symbolic w) 

    method make_table_lookup table_vexp idx_exp idx_wd ty =
      let rec map_vexp_dt_list fn l =
	(if (List.length l) <> 0 then (fn (List.hd l)) :: 
	    (map_vexp_dt_list fn (List.tl l)) 
	 else [])
      in
      let table_dt =  map_vexp_dt_list (fun e -> D.from_symbolic e) table_vexp in
      D.to_symbolic_8 (form_man#make_table_lookup table_dt idx_exp idx_wd ty)

    val mutable snap = (V.VarHash.create 1, V.VarHash.create 1)

    method init_prog (dl, sl) =
      List.iter
	(fun ((n,s,t) as v) ->
	   if s = "mem" then
	     mem_var <- v
	   else
	     (V.VarHash.add reg_store v (D.uninit);
	      Hashtbl.add reg_to_var (regstr_to_reg s) v)) dl;
      self#set_frag (dl, sl);
      let result = self#run () in
	match result with
	  | "fallthrough" -> ()
	  | _ -> failwith "Initial program should fall through"

    val mutable loop_cnt = 0L
    val mutable f2_loop_cnt = 0L
    method get_loop_cnt = loop_cnt

    method set_frag (dl, sl) =
      frag <- (dl, sl);
      V.VarHash.clear temps;
      loop_cnt <- 0L;
      f2_loop_cnt <- 0L;
      self#concretize_misc;
      insns <- sl

    method concretize_misc = ()

    val mutable extra_eip_hooks = []

    method add_extra_eip_hook f =
      extra_eip_hooks <- f :: extra_eip_hooks

    val unique_eips = Hashtbl.create 1001

    val mutable deferred_start_symbolic = None

    val mutable insn_count = 0L

    val range_opts_tbl = Hashtbl.create 2

    method add_range_opt opt_str opt =
      Hashtbl.replace range_opts_tbl opt_str opt	

    method eip_hook eip =
      (* Shouldn't be needed; we instead simplify the registers when
	 writing to them: *)
      (* self#simplify_regs; *)
      (match deferred_start_symbolic with
	 | Some setup ->
	     deferred_start_symbolic <- None;
	     raise (StartSymbolic(eip, setup))
	 | None -> ());
      if !opt_trace_registers then
	self#print_regs;
      if !opt_trace_eip then
	Printf.printf "EIP is 0x%08Lx\n" eip;
      (if !opt_trace_unique_eips then
	 (if Hashtbl.mem unique_eips eip then
	    ()
	  else
	    (Printf.printf "Saw new EIP 0x%08Lx\n" eip;
	     Hashtbl.add unique_eips eip ())));
      (* Libasmir.print_disasm_rawbytes Libasmir.Bfd_arch_i386 eip insn_bytes;
	 print_string "\n"; *)
      List.iter (fun fn -> (fn (self :> fragment_machine) eip))
	extra_eip_hooks;
      List.iter (
	fun (start1,end1,start2,end2) ->
	  if eip = start1 then (
	    saved_f1_rsp <- (match !opt_arch with
	    | ARM -> 0L
	    | X64 -> self#get_long_var R_RSP
	    | X86 -> self#get_word_var R_ESP);
	    in_f1_range <- true;
	    self#make_f1_sym_snap ; 
	    self#make_f1_conc_snap ;  
	    self#make_f1_special_handlers_snap ;
	  )
	  else if eip = end1 then (
	    in_f1_range <- false;
	    self#save_f1_sym_se ;
	    self#save_f1_conc_se ;
	    self#reset_f1_special_handlers_snap ;
	  );
	  if eip = start2 then (
	    saved_f2_rsp <- (match !opt_arch with
	    | ARM -> 0L
	    | X64 -> self#get_long_var R_RSP
	    | X86 -> self#get_word_var R_ESP);
	    in_f2_range <- true;
	    self#make_f2_sym_snap ;
	    self#make_f2_conc_snap ;
	    self#make_f2_special_handlers_snap ;
	  )
	  else if eip = end2 then (
	    in_f2_range <- false;
	    (* use this snippet to disable SE eq chk when using the memsub adapter *)
	    (* let (n_fields, _) = !opt_struct_adapter_params in
	    if n_fields = 0 then (
	      self#compare_sym_se ;
	      self#compare_conc_se ;
	    ) else (
	      mem#reset4_3 ();
	      saved_f1_rsp <- 0L;
	      saved_f2_rsp <- 0L;
	    );*)
	    if !opt_dont_compare_mem_se = false then (
	      self#compare_sym_se ;
	      self#compare_conc_se ;
	      self#reset_f2_special_handlers_snap ;)
	    else (
	      mem#reset4_3 ();
	      saved_f1_rsp <- 0L;
	      saved_f2_rsp <- 0L;
	    )
	  );
      ) !opt_match_syscalls_addr_range;
      let set_in_f2_range b suffix_str =
	in_f2_range <- b;
	let suffix = match suffix_str with
	  | None -> ""
	  | Some _suffix -> _suffix
	in
	if !opt_trace_repair then (
	  Printf.printf "repair: Setting in_f2_range to %B, %s\n" b suffix;
	  flush(stdout);) in
      (match (eip = !opt_repair_frag_start,    (* 1 *)
	      eip = !opt_repair_frag_end,      (* 2 *)
	      in_f1_range,                     (* 3 *)
	      in_f2_range,                     (* 4 *)
	      !opt_verify_adapter,             (* 5 *)
	      !synth_verify_adapter) with      (* 6 *) 
      | (false, false, _, _, _, _) -> ()
      | (true, _, false, false, true, false) -> (* reached frag start, verify_adapter is true *)
	 if !opt_trace_repair then (
	   Printf.printf "repair: Setting in_f2_range = true because verify_adapter is true\n";
	   flush(stdout););
	self#make_f2_special_handlers_snap ;
	in_f1_range <- false; set_in_f2_range true (Some " because verify_adapter is true")
      | (true, _, false, false, false, false) -> (* reached frag start *)
	 if !opt_trace_repair then (
	   Printf.printf "repair: Setting in_f1_range to true\n";
	   flush(stdout););
	in_f1_range <- true;
	if !opt_adapter_search_mode then (self#apply_target_frag_inputs;);
	self#make_f1_sym_snap; 
	self#make_f1_conc_snap;  
	self#make_f1_special_handlers_snap ;
      | (true, _, false, true, false, true) -> (* reached frag start in f2 range in synth-verify mode *)
	 if !opt_trace_repair then (
	   Printf.printf "repair: reached frag start in f2 range in synth-verify mode\n";
	   flush(stdout););
	self#apply_invalid_repair_target_frag_inputs;
      | (_, true, true, false, false, false) -> (* reached frag end in f1 range *)
	 if !opt_trace_repair then (
	   Printf.printf "Setting in_f1_range to false and in_f2_range = true\n";
	   flush(stdout););
	in_f1_range <- false; set_in_f2_range true None;
	self#save_f1_ret_reg ;
	self#save_f1_sym_se ;
	self#save_f1_conc_se ;
	self#reset_f1_special_handlers_snap ;
	self#make_f2_sym_snap ;
	self#make_f2_conc_snap ;
	self#make_f2_special_handlers_snap ;
	if !stdin_redirect_fd <> None then ( (* assuming that no stdin-redirect happened before f1, so we dont need a stack to maintain stdin_redirect_fd *)
	  if !opt_trace_repair then (
	    Printf.printf "repair: closing previous stdin_redirect_fd\n"; flush(stdout););
	  Unix.close (Option.get !stdin_redirect_fd);
	  stdin_redirect_fd := None);
      | (_, true, false, true, _, false) -> (* reached frag end in f2 range *) 
	if not !opt_verify_adapter && not !synth_verify_adapter then (
	  (* no eqchk needed if we only verifying the adapter *)
	  self#save_f2_ret_reg ;
	  if not self#compare_ret_reg_vals || not self#compare_f2_syscall_num then (
	    raise DisqualifiedPath;);
	  if !opt_dont_compare_mem_se = false then (
	    self#compare_sym_se;
	    self#compare_conc_se;
	    self#reset_f2_special_handlers_snap;)
	  else (
	    mem#reset4_3 ();
	    saved_f1_rsp <- 0L;
	    saved_f2_rsp <- 0L;);)
	else if !opt_verify_adapter then ( self#reset_f2_special_handlers_snap;); 
	Printf.printf "Match\n"; flush(stdout);
	if not !opt_adapter_search_mode then raise (SimulatedExit(0L));
	let (_, num_total_tests) = !opt_repair_tests_file in
	let (_, num_invalid_total_tests) = !opt_invalid_repair_tests_file in
	
	if self#get_repair_tests_processed = num_total_tests then (
	  Printf.printf "All functional tests succeeded!\n"; flush(stdout);
	  if self#get_invalid_repair_tests_processed < num_invalid_total_tests then (
	    synth_verify_adapter := true;
	    set_in_f2_range true (Some " to start running verification tests\n")
	  ) else (
	    Printf.printf "All tests succeeded!\n"; flush(stdout);
	    set_in_f2_range false None;
	    raise (SimulatedExit(0L));
	  )
	) else ( set_in_f2_range false None);
	if !stdin_redirect_fd <> None then ( (* assuming that no stdin-redirect happened before f1, so we dont need a stack to maintain stdin_redirect_fd *)
	  if !opt_trace_repair then (
	    Printf.printf "repair: closing previous stdin_redirect_fd\n"; flush(stdout););
	  Unix.close (Option.get !stdin_redirect_fd);
	  stdin_redirect_fd := None);
      | (_, true, false, true, false, true) -> (* reached frag end in f2 range in synth-verify mode*)
	 Printf.printf "Match\n"; flush(stdout);
	let (_, num_total_tests) = !opt_repair_tests_file in
	let (_, num_invalid_total_tests) = !opt_invalid_repair_tests_file in
	assert(self#get_repair_tests_processed >=num_total_tests);
	if self#get_invalid_repair_tests_processed < num_invalid_total_tests then (
	  synth_verify_adapter := true;
	  set_in_f2_range true (Some (Printf.sprintf " to run more verification tests\nrepair: %d of %d verification tests processed\n" self#get_invalid_repair_tests_processed num_invalid_total_tests))
	) else (
	  synth_verify_adapter := false;
	  Printf.printf "All tests succeeded!\n"; flush(stdout);
	  set_in_f2_range false None;
	  raise (SimulatedExit(0L));
	)
      | _ -> ());
	
      let control_range_opts opts_list range_val other_val =
	List.iter (
	  fun (opt_str, eip1, eip2) ->
	    let opt = Hashtbl.find range_opts_tbl opt_str in
	    if eip = eip1 then
	      opt := range_val
	    else if eip = eip2 then 
	      opt := other_val
	) opts_list in
      control_range_opts !opt_turn_opt_off_range false true;
      control_range_opts !opt_turn_opt_on_range true false;
      self#watchpoint

    method reset_struct_counts = 
      e_o_f1_count := 0;
      f2_init_count := 0;
	
    method get_eip =
      match !opt_arch with
	| X86 -> self#get_word_var R_EIP
	| X64 -> self#get_long_var R_RIP
	| ARM -> self#get_word_var R15T

    method set_eip eip =
      match !opt_arch with
	| X86 -> self#set_word_var R_EIP eip
	| X64 -> self#set_long_var R_RIP eip
	| ARM -> self#set_word_var R15T eip

    method run_eip_hooks =
      self#eip_hook (self#get_eip)

    method get_esp =
      match !opt_arch with
	| X86 -> self#get_word_var R_ESP
	| X64 -> self#get_long_var R_RSP
	| ARM -> self#get_word_var R13

    val mutable call_stack = []

    method private trace_callstack last_insn last_eip eip =
      let pop_callstack esp =
	while match call_stack with
	  | (old_esp, _, _, _) :: _ when old_esp < esp -> true
	  | _ -> false do
	      call_stack <- List.tl call_stack
	done
      in
      let get_retaddr esp =
	match !opt_arch with
	  | X86 -> self#load_word_conc esp
	  | X64 -> self#load_long_conc esp
	  | ARM -> self#get_word_var R14
      in
      let size = match !opt_arch with
	| X86 -> 4L
	| X64 -> 8L
	| ARM -> 4L
      in
      let kind =
	match !opt_arch with
	  | X86 | X64 ->
	      let s = last_insn ^ "    " in
		if (String.sub s 0 4) = "call" then
		  "call"
		else if ((String.sub s 0 3) = "ret")
                  || ((String.length s >= 8) &&  ((String.sub s 0 8) = "repz ret"))
                then
		  "return"
		else if (String.sub s 0 3) = "jmp" then
		  "unconditional jump"
		else if (String.sub s 0 1) = "j" then
		  "conditional jump"
		else
		  "not a jump"
	  | ARM ->
	      (* TODO: add similar parsing for ARM mnemonics *)
	      "not a jump"
      in
	match kind with
	  | "call" ->
	      let esp = self#get_esp in
	      let depth = List.length call_stack and
		  ret_addr = get_retaddr esp
	      in
		for i = 0 to depth - 1 do Printf.printf " " done;
		Printf.printf
		  "Call from 0x%08Lx to 0x%08Lx (return to 0x%08Lx)\n"
		  last_eip eip ret_addr;
		call_stack <- (esp, last_eip, eip, ret_addr) :: call_stack;
	  | "return" ->
	      let esp = self#get_esp in
		pop_callstack (Int64.sub esp size);
		let depth = List.length call_stack in
		  for i = 0 to depth - 2 do Printf.printf " " done;
		  Printf.printf "Return from 0x%08Lx to 0x%08Lx\n"
		    last_eip eip;
		  pop_callstack esp;
	  | _ -> ()

    method jump_hook last_insn last_eip eip =
      if !opt_trace_callstack then
	self#trace_callstack last_insn last_eip eip

    method run_jump_hooks last_insn last_eip eip =
      self#jump_hook last_insn last_eip eip

    method set_cjmp_heuristic
      (func:(int64 -> int64 -> int64 -> float -> bool option -> bool option))
      = ()

    method private on_missing_zero_m (m:GM.granular_memory) =
      m#on_missing
	(fun size _ -> match size with
	   | 8  -> D.from_concrete_8  0
	   | 16 -> D.from_concrete_16 0
	   | 32 -> D.from_concrete_32 0L
	   | 64 -> D.from_concrete_64 0L
	   | _ -> failwith "Bad size in on_missing_zero")

    method on_missing_zero =
      self#on_missing_zero_m (mem :> GM.granular_memory)

    method private on_missing_symbol_m (m:GM.granular_memory) name =
      m#on_missing
	(fun size addr -> 
	  match size with
	  | 8  -> form_man#fresh_symbolic_mem_8  name addr
	  | 16 -> form_man#fresh_symbolic_mem_16 name addr
	  | 32 -> form_man#fresh_symbolic_mem_32 name addr
	  | 64 -> form_man#fresh_symbolic_mem_64 name addr
	  | _ -> failwith "Bad size in on_missing_symbol")
	
    method private on_missing_symbol_m_lim (m:GM.granular_memory) name lim =
      let contains s1 s2 =
	let re = Str.regexp_string s2
	in
        try ignore (Str.search_forward re s1 0); true
        with Not_found -> false
      in
      m#on_missing
	(fun size addr -> 
	  let ret_sym = ref false in
	  let is_region = ref false in
	  if (addr<0L) || (addr>=lim) then 
	    ret_sym := true;
	  if (contains name "region_") = true then is_region := true;
	  match (!is_region, !ret_sym, size) with
	  | (true, false, 8)  -> form_man#fresh_symbolic_mem_8  name addr
	  | (true, false, 16) -> form_man#fresh_symbolic_mem_16 name addr
	  | (true, false, 32) -> form_man#fresh_symbolic_mem_32 name addr
	  | (true, false, 64) -> form_man#fresh_symbolic_mem_64 name addr
	  | (true, false,_) -> 
	    failwith "Bad size in on_missing_symbol_m_lim inside region limit"
	  | (true, true, 8) -> D.from_concrete_8  0
	  | (true, true, 16) -> D.from_concrete_16 0
	  | (true, true, 32) -> D.from_concrete_32 0L
	  | (true, true, 64) -> D.from_concrete_64 0L
	  | (true, true, _) -> 
	    failwith "Bad size in on_missing_symbol_m_lim outside region limit"
	  | (false, _, _) ->
	    failwith "on_missing_symbol_m_lim called on non-region memory"
	)
	
    method on_missing_symbol =
      self#on_missing_symbol_m (mem :> GM.granular_memory) "mem"

    method private make_x86_regs_zero =
      let reg r v =
	self#set_int_var (Hashtbl.find reg_to_var r) v
      in
	reg R_EAX (D.from_concrete_32 0x00000000L);
	reg R_EBX (D.from_concrete_32 0x00000000L);
	reg R_ECX (D.from_concrete_32 0x00000000L);
	reg R_EDX (D.from_concrete_32 0x00000000L);
	reg R_EBP (D.from_concrete_32 0x00000000L);
	reg R_ESP (D.from_concrete_32 0x00000000L);
	reg R_ESI (D.from_concrete_32 0x00000000L);
	reg R_EDI (D.from_concrete_32 0x00000000L);
	reg R_CS (D.from_concrete_16 0);
	reg R_DS (D.from_concrete_16 0);
	reg R_ES (D.from_concrete_16 0);
	reg R_FS (D.from_concrete_16 0);
	reg R_GS (D.from_concrete_16 0);
	reg R_PF (D.from_concrete_1 0);
	reg R_CF (D.from_concrete_1 0);
	reg R_AF (D.from_concrete_1 0);
	reg R_SF (D.from_concrete_1 0);
	reg R_OF (D.from_concrete_1 0);
	reg R_ZF (D.from_concrete_1 0);
	reg R_FTOP (D.from_concrete_32 0L);
	reg R_FC3210 (D.from_concrete_32 0L);
	reg R_FPREG0 (D.from_concrete_64 0L);
	reg R_FPREG1 (D.from_concrete_64 0L);
	reg R_FPREG2 (D.from_concrete_64 0L);
	reg R_FPREG3 (D.from_concrete_64 0L);
	reg R_FPREG4 (D.from_concrete_64 0L);
	reg R_FPREG5 (D.from_concrete_64 0L);
	reg R_FPREG6 (D.from_concrete_64 0L);
	reg R_FPREG7 (D.from_concrete_64 0L);
	reg R_FPTAG0 (D.from_concrete_8 0);
	reg R_FPTAG1 (D.from_concrete_8 0);
	reg R_FPTAG2 (D.from_concrete_8 0);
	reg R_FPTAG3 (D.from_concrete_8 0);
	reg R_FPTAG4 (D.from_concrete_8 0);
	reg R_FPTAG5 (D.from_concrete_8 0);
	reg R_FPTAG6 (D.from_concrete_8 0);
	reg R_FPTAG7 (D.from_concrete_8 0);
	reg EFLAGSREST (D.from_concrete_32 0L);
	reg R_LDT (D.from_concrete_32 0x00000000L);
	reg R_GDT (D.from_concrete_32 0x00000000L);
	reg R_DFLAG (D.from_concrete_32 1L);
	reg R_IDFLAG (D.from_concrete_32 0L);
	reg R_ACFLAG (D.from_concrete_32 0L);
	reg R_CC_OP   (D.from_concrete_32 0L);
	reg R_CC_DEP1 (D.from_concrete_32 0L);
	reg R_CC_DEP2 (D.from_concrete_32 0L);
	reg R_CC_NDEP (D.from_concrete_32 0L);
	reg R_FPROUND (D.from_concrete_32 0L); (* to nearest *)
	reg R_SSEROUND (D.from_concrete_32 0L); (* to nearest *)
	reg R_XMM0L (D.from_concrete_64 0L);
	reg R_XMM0H (D.from_concrete_64 0L);
	reg R_XMM1L (D.from_concrete_64 0L);
	reg R_XMM1H (D.from_concrete_64 0L);
	reg R_XMM2L (D.from_concrete_64 0L);
	reg R_XMM2H (D.from_concrete_64 0L);
	reg R_XMM3L (D.from_concrete_64 0L);
	reg R_XMM3H (D.from_concrete_64 0L);
	reg R_XMM4L (D.from_concrete_64 0L);
	reg R_XMM4H (D.from_concrete_64 0L);
	reg R_XMM5L (D.from_concrete_64 0L);
	reg R_XMM5H (D.from_concrete_64 0L);
	reg R_XMM6L (D.from_concrete_64 0L);
	reg R_XMM6H (D.from_concrete_64 0L);
	reg R_XMM7L (D.from_concrete_64 0L);
	reg R_XMM7H (D.from_concrete_64 0L);
	()

    method private make_x64_regs_zero =
      let reg r v =
	self#set_int_var (Hashtbl.find reg_to_var r) v
      in
	reg R_RAX (D.from_concrete_64 0x0000000000000000L);
	reg R_RBX (D.from_concrete_64 0x0000000000000000L);
	reg R_RCX (D.from_concrete_64 0x0000000000000000L);
	reg R_RDX (D.from_concrete_64 0x0000000000000000L);
	reg R_RBP (D.from_concrete_64 0x0000000000000000L);
	reg R_RSP (D.from_concrete_64 0x0000000000000000L);
	reg R_RSI (D.from_concrete_64 0x0000000000000000L);
	reg R_RDI (D.from_concrete_64 0x0000000000000000L);
	reg R_R8  (D.from_concrete_64 0x0000000000000000L);
	reg R_R9  (D.from_concrete_64 0x0000000000000000L);
	reg R_R10 (D.from_concrete_64 0x0000000000000000L);
	reg R_R11 (D.from_concrete_64 0x0000000000000000L);
	reg R_R12 (D.from_concrete_64 0x0000000000000000L);
	reg R_R13 (D.from_concrete_64 0x0000000000000000L);
	reg R_R14 (D.from_concrete_64 0x0000000000000000L);
	reg R_R15 (D.from_concrete_64 0x0000000000000000L);
	reg R_FS_BASE (D.from_concrete_64 0x0000000060000000L);
	reg R_GS_BASE (D.from_concrete_64 0x0000000061000000L);
	reg R_PF (D.from_concrete_1 0);
	reg R_CF (D.from_concrete_1 0);
	reg R_AF (D.from_concrete_1 0);
	reg R_SF (D.from_concrete_1 0);
	reg R_OF (D.from_concrete_1 0);
	reg R_ZF (D.from_concrete_1 0);
	reg R_FTOP (D.from_concrete_32 7L);
	reg R_FC3210 (D.from_concrete_32 0L);
	reg R_FPREG0 (D.from_concrete_64 0L);
	reg R_FPREG1 (D.from_concrete_64 0L);
	reg R_FPREG2 (D.from_concrete_64 0L);
	reg R_FPREG3 (D.from_concrete_64 0L);
	reg R_FPREG4 (D.from_concrete_64 0L);
	reg R_FPREG5 (D.from_concrete_64 0L);
	reg R_FPREG6 (D.from_concrete_64 0L);
	reg R_FPREG7 (D.from_concrete_64 0L);
	reg R_FPTAG0 (D.from_concrete_8 0);
	reg R_FPTAG1 (D.from_concrete_8 0);
	reg R_FPTAG2 (D.from_concrete_8 0);
	reg R_FPTAG3 (D.from_concrete_8 0);
	reg R_FPTAG4 (D.from_concrete_8 0);
	reg R_FPTAG5 (D.from_concrete_8 0);
	reg R_FPTAG6 (D.from_concrete_8 0);
	reg R_FPTAG7 (D.from_concrete_8 0);
	reg R_RFLAGSREST (D.from_concrete_64 0L);
	reg R_DFLAG (D.from_concrete_64 1L);
	reg R_IDFLAG (D.from_concrete_64 0L);
	reg R_ACFLAG (D.from_concrete_64 0L);
	reg R_CC_OP   (D.from_concrete_64 0L);
	reg R_CC_DEP1 (D.from_concrete_64 0L);
	reg R_CC_DEP2 (D.from_concrete_64 0L);
	reg R_CC_NDEP (D.from_concrete_64 0L);
	reg R_FPROUND (D.from_concrete_64 0L); (* to nearest *)
	reg R_YMM0_0 (D.from_concrete_64 0L);
	reg R_YMM0_1 (D.from_concrete_64 0L);
	reg R_YMM0_2 (D.from_concrete_64 0L);
	reg R_YMM0_3 (D.from_concrete_64 0L);
	reg R_YMM1_0 (D.from_concrete_64 0L);
	reg R_YMM1_1 (D.from_concrete_64 0L);
	reg R_YMM1_2 (D.from_concrete_64 0L);
	reg R_YMM1_3 (D.from_concrete_64 0L);
	reg R_YMM2_0 (D.from_concrete_64 0L);
	reg R_YMM2_1 (D.from_concrete_64 0L);
	reg R_YMM2_2 (D.from_concrete_64 0L);
	reg R_YMM2_3 (D.from_concrete_64 0L);
	reg R_YMM3_0 (D.from_concrete_64 0L);
	reg R_YMM3_1 (D.from_concrete_64 0L);
	reg R_YMM3_2 (D.from_concrete_64 0L);
	reg R_YMM3_3 (D.from_concrete_64 0L);
	reg R_YMM4_0 (D.from_concrete_64 0L);
	reg R_YMM4_1 (D.from_concrete_64 0L);
	reg R_YMM4_2 (D.from_concrete_64 0L);
	reg R_YMM4_3 (D.from_concrete_64 0L);
	reg R_YMM5_0 (D.from_concrete_64 0L);
	reg R_YMM5_1 (D.from_concrete_64 0L);
	reg R_YMM5_2 (D.from_concrete_64 0L);
	reg R_YMM5_3 (D.from_concrete_64 0L);
	reg R_YMM6_0 (D.from_concrete_64 0L);
	reg R_YMM6_1 (D.from_concrete_64 0L);
	reg R_YMM6_2 (D.from_concrete_64 0L);
	reg R_YMM6_3 (D.from_concrete_64 0L);
	reg R_YMM7_0 (D.from_concrete_64 0L);
	reg R_YMM7_1 (D.from_concrete_64 0L);
	reg R_YMM7_2 (D.from_concrete_64 0L);
	reg R_YMM7_3 (D.from_concrete_64 0L);
	reg R_YMM8_0 (D.from_concrete_64 0L);
	reg R_YMM8_1 (D.from_concrete_64 0L);
	reg R_YMM8_2 (D.from_concrete_64 0L);
	reg R_YMM8_3 (D.from_concrete_64 0L);
	reg R_YMM9_0 (D.from_concrete_64 0L);
	reg R_YMM9_1 (D.from_concrete_64 0L);
	reg R_YMM9_2 (D.from_concrete_64 0L);
	reg R_YMM9_3 (D.from_concrete_64 0L);
	reg R_YMM10_0 (D.from_concrete_64 0L);
	reg R_YMM10_1 (D.from_concrete_64 0L);
	reg R_YMM10_2 (D.from_concrete_64 0L);
	reg R_YMM10_3 (D.from_concrete_64 0L);
	reg R_YMM11_0 (D.from_concrete_64 0L);
	reg R_YMM11_1 (D.from_concrete_64 0L);
	reg R_YMM11_2 (D.from_concrete_64 0L);
	reg R_YMM11_3 (D.from_concrete_64 0L);
	reg R_YMM12_0 (D.from_concrete_64 0L);
	reg R_YMM12_1 (D.from_concrete_64 0L);
	reg R_YMM12_2 (D.from_concrete_64 0L);
	reg R_YMM12_3 (D.from_concrete_64 0L);
	reg R_YMM13_0 (D.from_concrete_64 0L);
	reg R_YMM13_1 (D.from_concrete_64 0L);
	reg R_YMM13_2 (D.from_concrete_64 0L);
	reg R_YMM13_3 (D.from_concrete_64 0L);
	reg R_YMM14_0 (D.from_concrete_64 0L);
	reg R_YMM14_1 (D.from_concrete_64 0L);
	reg R_YMM14_2 (D.from_concrete_64 0L);
	reg R_YMM14_3 (D.from_concrete_64 0L);
	reg R_YMM15_0 (D.from_concrete_64 0L);
	reg R_YMM15_1 (D.from_concrete_64 0L);
	reg R_YMM15_2 (D.from_concrete_64 0L);
	reg R_YMM15_3 (D.from_concrete_64 0L);
	reg R_SSEROUND (D.from_concrete_64 0L); (* to nearest *)
	()

    method private make_arm_regs_zero =
      let reg r v =
	self#set_int_var (Hashtbl.find reg_to_var r) v
      in
	reg R0   (D.from_concrete_32 0x00000000L);
	reg R1   (D.from_concrete_32 0x00000000L);
	reg R2   (D.from_concrete_32 0x00000000L);
	reg R3   (D.from_concrete_32 0x00000000L);
	reg R4   (D.from_concrete_32 0x00000000L);
	reg R5   (D.from_concrete_32 0x00000000L);
	reg R6   (D.from_concrete_32 0x00000000L);
	reg R7   (D.from_concrete_32 0x00000000L);
	reg R8   (D.from_concrete_32 0x00000000L);
	reg R9   (D.from_concrete_32 0x00000000L);
	reg R10  (D.from_concrete_32 0x00000000L);
	reg R11  (D.from_concrete_32 0x00000000L);
	reg R12  (D.from_concrete_32 0x00000000L);
	reg R13  (D.from_concrete_32 0x00000000L);
	reg R14  (D.from_concrete_32 0x00000000L);
	reg R15T (D.from_concrete_32 0x00000000L);
        reg R_D0  (D.from_concrete_64 0x0L);
        reg R_D1  (D.from_concrete_64 0x0L);
        reg R_D2  (D.from_concrete_64 0x0L);
        reg R_D3  (D.from_concrete_64 0x0L);
        reg R_D4  (D.from_concrete_64 0x0L);
        reg R_D5  (D.from_concrete_64 0x0L);
        reg R_D6  (D.from_concrete_64 0x0L);
        reg R_D7  (D.from_concrete_64 0x0L);
        reg R_D8  (D.from_concrete_64 0x0L);
        reg R_D9  (D.from_concrete_64 0x0L);
        reg R_D10 (D.from_concrete_64 0x0L);
        reg R_D11 (D.from_concrete_64 0x0L);
        reg R_D12 (D.from_concrete_64 0x0L);
        reg R_D13 (D.from_concrete_64 0x0L);
        reg R_D14 (D.from_concrete_64 0x0L);
        reg R_D15 (D.from_concrete_64 0x0L);
        reg R_D16 (D.from_concrete_64 0x0L);
        reg R_D17 (D.from_concrete_64 0x0L);
        reg R_D18 (D.from_concrete_64 0x0L);
        reg R_D19 (D.from_concrete_64 0x0L);
        reg R_D20 (D.from_concrete_64 0x0L);
        reg R_D21 (D.from_concrete_64 0x0L);
        reg R_D22 (D.from_concrete_64 0x0L);
        reg R_D23 (D.from_concrete_64 0x0L);
        reg R_D24 (D.from_concrete_64 0x0L);
        reg R_D25 (D.from_concrete_64 0x0L);
        reg R_D26 (D.from_concrete_64 0x0L);
        reg R_D27 (D.from_concrete_64 0x0L);
        reg R_D28 (D.from_concrete_64 0x0L);
        reg R_D29 (D.from_concrete_64 0x0L);
        reg R_D30 (D.from_concrete_64 0x0L);
        reg R_D31 (D.from_concrete_64 0x0L);
	reg R_NF (D.from_concrete_1 0);
	reg R_ZF (D.from_concrete_1 0);
	reg R_CF (D.from_concrete_1 0);
	reg R_VF (D.from_concrete_1 0);
	reg R_ITSTATE (D.from_concrete_32 0x00000000L);
	reg R_TPIDRURO (D.from_concrete_32 0x00000000L);
	reg R_FPSCR (D.from_concrete_32 0x00000000L);
	()

    method make_regs_zero =
      match !opt_arch with
	| X86 -> self#make_x86_regs_zero
	| X64 -> self#make_x64_regs_zero
	| ARM -> self#make_arm_regs_zero

    method private make_x86_regs_symbolic =
      let reg r v =
	self#set_int_var (Hashtbl.find reg_to_var r) v
      in
	reg R_EBP (form_man#fresh_symbolic_32 "initial_ebp");
	reg R_ESP (form_man#fresh_symbolic_32 "initial_esp");
	reg R_ESI (form_man#fresh_symbolic_32 "initial_esi");
	reg R_EDI (form_man#fresh_symbolic_32 "initial_edi");
	reg R_EAX (form_man#fresh_symbolic_32 "initial_eax");
	reg R_EBX (form_man#fresh_symbolic_32 "initial_ebx");
	reg R_ECX (form_man#fresh_symbolic_32 "initial_ecx");
	reg R_EDX (form_man#fresh_symbolic_32 "initial_edx");
	reg R_CS (D.from_concrete_16 0x23);
	reg R_DS (D.from_concrete_16 0x2b);
	reg R_ES (D.from_concrete_16 0x2b);
	reg R_FS (D.from_concrete_16 0x0);
	reg R_GS (D.from_concrete_16 0x63);
	reg R_GDT (D.from_concrete_32 0x60000000L);
	reg R_LDT (D.from_concrete_32 0x61000000L);
	reg R_DFLAG (D.from_concrete_32 1L);
	reg R_ACFLAG (D.from_concrete_32 0L);
	reg R_IDFLAG (D.from_concrete_32 0L);
	reg EFLAGSREST (D.from_concrete_32 0L);
	reg R_PF (D.from_concrete_1 0);
	reg R_CF (D.from_concrete_1 0);
	reg R_AF (D.from_concrete_1 0);
	reg R_SF (D.from_concrete_1 0);
	reg R_OF (D.from_concrete_1 0);
	reg R_ZF (D.from_concrete_1 0);
	reg R_XMM0L (D.from_concrete_64 0L);
	reg R_XMM0H (D.from_concrete_64 0L);
	reg R_XMM1L (D.from_concrete_64 0L);
	reg R_XMM1H (D.from_concrete_64 0L);
	reg R_XMM2L (D.from_concrete_64 0L);
	reg R_XMM2H (D.from_concrete_64 0L);
	reg R_XMM3L (D.from_concrete_64 0L);
	reg R_XMM3H (D.from_concrete_64 0L);
	reg R_XMM4L (D.from_concrete_64 0L);
	reg R_XMM4H (D.from_concrete_64 0L);
	reg R_XMM5L (D.from_concrete_64 0L);
	reg R_XMM5H (D.from_concrete_64 0L);
	reg R_XMM6L (D.from_concrete_64 0L);
	reg R_XMM6H (D.from_concrete_64 0L);
	reg R_XMM7L (D.from_concrete_64 0L);
	reg R_XMM7H (D.from_concrete_64 0L);
	(* reg EFLAGSREST (form_man#fresh_symbolic_32 "initial_eflagsrest");*)
	reg R_FTOP (D.from_concrete_32 0L);
	reg R_FC3210 (D.from_concrete_32 0L);
	reg R_FPREG0 (D.from_concrete_64 0L);
	reg R_FPREG1 (D.from_concrete_64 0L);
	reg R_FPREG2 (D.from_concrete_64 0L);
	reg R_FPREG3 (D.from_concrete_64 0L);
	reg R_FPREG4 (D.from_concrete_64 0L);
	reg R_FPREG5 (D.from_concrete_64 0L);
	reg R_FPREG6 (D.from_concrete_64 0L);
	reg R_FPREG7 (D.from_concrete_64 0L);
	reg R_FPTAG0 (D.from_concrete_8 0);
	reg R_FPTAG1 (D.from_concrete_8 0);
	reg R_FPTAG2 (D.from_concrete_8 0);
	reg R_FPTAG3 (D.from_concrete_8 0);
	reg R_FPTAG4 (D.from_concrete_8 0);
	reg R_FPTAG5 (D.from_concrete_8 0);
	reg R_FPTAG6 (D.from_concrete_8 0);
	reg R_FPTAG7 (D.from_concrete_8 0);
	(* Linux user space CS segment: *)
	self#store_byte_conc 0x60000020L 0xff;
	self#store_byte_conc 0x60000021L 0xff;
	self#store_byte_conc 0x60000022L 0x00;
	self#store_byte_conc 0x60000023L 0x00;
	self#store_byte_conc 0x60000024L 0x00;
	self#store_byte_conc 0x60000025L 0xfb;
	self#store_byte_conc 0x60000026L 0xcf;
	self#store_byte_conc 0x60000027L 0x00;
	(* Linux user space DS/ES segment: *)
	self#store_byte_conc 0x60000028L 0xff;
	self#store_byte_conc 0x60000029L 0xff;
	self#store_byte_conc 0x6000002aL 0x00;
	self#store_byte_conc 0x6000002bL 0x00;
	self#store_byte_conc 0x6000002cL 0x00;
	self#store_byte_conc 0x6000002dL 0xf3;
	self#store_byte_conc 0x6000002eL 0xcf;
	self#store_byte_conc 0x6000002fL 0x00;
	(* Linux user space GS segment: *)
	self#store_byte_conc 0x60000060L 0xff;
	self#store_byte_conc 0x60000061L 0xff;
	self#store_byte_conc 0x60000062L 0x00;
	self#store_byte_conc 0x60000063L 0x00;
	self#store_byte_conc 0x60000064L 0x00;
	self#store_byte_conc 0x60000065L 0xf3;
	self#store_byte_conc 0x60000066L 0xcf;
	self#store_byte_conc 0x60000067L 0x62;
	(* Linux kernel space CS segment: *)
	self#store_byte_conc 0x60000070L 0xff;
	self#store_byte_conc 0x60000071L 0xff;
	self#store_byte_conc 0x60000072L 0x00;
	self#store_byte_conc 0x60000073L 0x00;
	self#store_byte_conc 0x60000074L 0x00;
	self#store_byte_conc 0x60000075L 0xfb;
	self#store_byte_conc 0x60000076L 0xcf;
	self#store_byte_conc 0x60000077L 0x00;
	(* Linux kernel space DS/ES segment: *)
	self#store_byte_conc 0x60000078L 0xff;
	self#store_byte_conc 0x60000079L 0xff;
	self#store_byte_conc 0x6000007aL 0x00;
	self#store_byte_conc 0x6000007bL 0x00;
	self#store_byte_conc 0x6000007cL 0x00;
	self#store_byte_conc 0x6000007dL 0xf3;
	self#store_byte_conc 0x6000007eL 0xcf;
	self#store_byte_conc 0x6000007fL 0x00;
	(* ReactOS kernel space FS segment: *)
(* 	self#store_byte_conc 0x60000030L 0x02; (* limit low *) *)
(* 	self#store_byte_conc 0x60000031L 0x00; (* limit mid *) *)
(* 	self#store_byte_conc 0x60000032L 0x00; (* base low *) *)
(* 	self#store_byte_conc 0x60000033L 0xf0; (* base mid-low *) *)
(* 	self#store_byte_conc 0x60000034L 0xdf; (* base mid-high *) *)
(* 	self#store_byte_conc 0x60000035L 0xf3; (* flags *) *)
(* 	self#store_byte_conc 0x60000036L 0xc0; (* flags, limit high *) *)
(* 	self#store_byte_conc 0x60000037L 0xff; (* base high *) *)
	(* Windows 7 kernel space FS segment: *)
	self#store_byte_conc 0x60000030L 0x04; (* limit low *)
	self#store_byte_conc 0x60000031L 0x00; (* limit mid *)
	self#store_byte_conc 0x60000032L 0x00; (* base low *)
	self#store_byte_conc 0x60000033L 0xec; (* base mid-low *)
	self#store_byte_conc 0x60000034L 0x92; (* base mid-high *)
	self#store_byte_conc 0x60000035L 0xf3; (* flags *)
	self#store_byte_conc 0x60000036L 0xc0; (* flags, limit high *)
	self#store_byte_conc 0x60000037L 0x82; (* base high *)
	(* Windows 7 user space FS segment: *)
	self#store_byte_conc 0x60000038L 0x01; (* limit low *)
	self#store_byte_conc 0x60000039L 0x00; (* limit mid *)
	self#store_byte_conc 0x6000003aL 0x00; (* base low *)
	self#store_byte_conc 0x6000003bL 0xe0; (* base mid-low *)
	self#store_byte_conc 0x6000003cL 0x92; (* base mid-high *)
	self#store_byte_conc 0x6000003dL 0xf3; (* flags *)
	self#store_byte_conc 0x6000003eL 0xfd; (* flags, limit high *)
	self#store_byte_conc 0x6000003fL 0x7f; (* base high *)

    method private make_x64_regs_symbolic =
      let reg r v =
	self#set_int_var (Hashtbl.find reg_to_var r) v
      in
	reg R_RBP (form_man#fresh_symbolic_tracked_64 "initial_rbp");
	reg R_RSP (form_man#fresh_symbolic_tracked_64 "initial_rsp");
	reg R_RSI (form_man#fresh_symbolic_tracked_64 "initial_rsi");
	reg R_RDI (form_man#fresh_symbolic_tracked_64 "initial_rdi");
	reg R_RAX (form_man#fresh_symbolic_tracked_64 "initial_rax");
	reg R_RBX (form_man#fresh_symbolic_tracked_64 "initial_rbx");
	reg R_RCX (form_man#fresh_symbolic_tracked_64 "initial_rcx");
	reg R_RDX (form_man#fresh_symbolic_tracked_64 "initial_rdx");
	reg R_R8  (form_man#fresh_symbolic_tracked_64 "initial_r8");
	reg R_R9  (form_man#fresh_symbolic_tracked_64 "initial_r9");
	reg R_R10 (form_man#fresh_symbolic_tracked_64 "initial_r10");
	reg R_R11 (form_man#fresh_symbolic_tracked_64 "initial_r11");
	reg R_R12 (form_man#fresh_symbolic_tracked_64 "initial_r12");
	reg R_R13 (form_man#fresh_symbolic_tracked_64 "initial_r13");
	reg R_R14 (form_man#fresh_symbolic_tracked_64 "initial_r14");
	reg R_R15 (form_man#fresh_symbolic_tracked_64 "initial_r15");
	reg R_FS_BASE (form_man#fresh_symbolic_tracked_64 "fs_base");
	reg R_GS_BASE (form_man#fresh_symbolic_tracked_64 "gs_base");
	reg R_DFLAG (D.from_concrete_64 1L);
	reg R_ACFLAG (D.from_concrete_64 0L);
	reg R_IDFLAG (D.from_concrete_64 0L);
	reg R_RFLAGSREST (D.from_concrete_64 0L);
	reg R_PF (D.from_concrete_1 0);
	reg R_CF (D.from_concrete_1 0);
	reg R_AF (D.from_concrete_1 0);
	reg R_SF (D.from_concrete_1 0);
	reg R_OF (D.from_concrete_1 0);
	reg R_ZF (D.from_concrete_1 0);
	reg R_YMM0_0 (form_man#fresh_symbolic_64 "initial_ymm0_0");
	reg R_YMM0_1 (form_man#fresh_symbolic_64 "initial_ymm0_1");
	reg R_YMM0_2 (form_man#fresh_symbolic_64 "initial_ymm0_2");
	reg R_YMM0_3 (form_man#fresh_symbolic_64 "initial_ymm0_3");
	reg R_YMM1_0 (form_man#fresh_symbolic_tracked_64 "initial_ymm1_0");
	reg R_YMM1_1 (form_man#fresh_symbolic_tracked_64 "initial_ymm1_1");
	reg R_YMM1_2 (form_man#fresh_symbolic_64 "initial_ymm1_2");
	reg R_YMM1_3 (form_man#fresh_symbolic_64 "initial_ymm1_3");
	reg R_YMM2_0 (form_man#fresh_symbolic_tracked_64 "initial_ymm2_0");
	reg R_YMM2_1 (form_man#fresh_symbolic_tracked_64 "initial_ymm2_1");
	reg R_YMM2_2 (form_man#fresh_symbolic_64 "initial_ymm2_2");
	reg R_YMM2_3 (form_man#fresh_symbolic_64 "initial_ymm2_3");
	reg R_YMM3_0 (form_man#fresh_symbolic_tracked_64 "initial_ymm3_0");
	reg R_YMM3_1 (form_man#fresh_symbolic_tracked_64 "initial_ymm3_1");
	reg R_YMM3_2 (form_man#fresh_symbolic_64 "initial_ymm3_2");
	reg R_YMM3_3 (form_man#fresh_symbolic_64 "initial_ymm3_3");
	reg R_YMM4_0 (form_man#fresh_symbolic_tracked_64 "initial_ymm4_0");
	reg R_YMM4_1 (form_man#fresh_symbolic_tracked_64 "initial_ymm4_1");
	reg R_YMM4_2 (form_man#fresh_symbolic_64 "initial_ymm4_2");
	reg R_YMM4_3 (form_man#fresh_symbolic_64 "initial_ymm4_3");
	reg R_YMM5_0 (form_man#fresh_symbolic_tracked_64 "initial_ymm5_0");
	reg R_YMM5_1 (form_man#fresh_symbolic_tracked_64 "initial_ymm5_1");
	reg R_YMM5_2 (form_man#fresh_symbolic_64 "initial_ymm5_2");
	reg R_YMM5_3 (form_man#fresh_symbolic_64 "initial_ymm5_3");
	reg R_YMM6_0 (form_man#fresh_symbolic_tracked_64 "initial_ymm6_0");
	reg R_YMM6_1 (form_man#fresh_symbolic_tracked_64 "initial_ymm6_1");
	reg R_YMM6_2 (form_man#fresh_symbolic_64 "initial_ymm6_2");
	reg R_YMM6_3 (form_man#fresh_symbolic_64 "initial_ymm6_3");
	reg R_YMM7_0 (form_man#fresh_symbolic_tracked_64 "initial_ymm7_0");
	reg R_YMM7_1 (form_man#fresh_symbolic_tracked_64 "initial_ymm7_1");
	reg R_YMM7_2 (form_man#fresh_symbolic_64 "initial_ymm7_2");
	reg R_YMM7_3 (form_man#fresh_symbolic_64 "initial_ymm7_3");
	reg R_YMM8_0 (form_man#fresh_symbolic_tracked_64 "initial_ymm8_0");
	reg R_YMM8_1 (form_man#fresh_symbolic_tracked_64 "initial_ymm8_1");
	reg R_YMM8_2 (form_man#fresh_symbolic_64 "initial_ymm8_2");
	reg R_YMM8_3 (form_man#fresh_symbolic_64 "initial_ymm8_3");
	reg R_YMM9_0 (form_man#fresh_symbolic_64 "initial_ymm9_0");
	reg R_YMM9_1 (form_man#fresh_symbolic_64 "initial_ymm9_1");
	reg R_YMM9_2 (form_man#fresh_symbolic_64 "initial_ymm9_2");
	reg R_YMM9_3 (form_man#fresh_symbolic_64 "initial_ymm9_3");
	reg R_YMM10_0 (form_man#fresh_symbolic_64 "initial_ymm10_0");
	reg R_YMM10_1 (form_man#fresh_symbolic_64 "initial_ymm10_1");
	reg R_YMM10_2 (form_man#fresh_symbolic_64 "initial_ymm10_2");
	reg R_YMM10_3 (form_man#fresh_symbolic_64 "initial_ymm10_3");
	reg R_YMM11_0 (form_man#fresh_symbolic_64 "initial_ymm11_0");
	reg R_YMM11_1 (form_man#fresh_symbolic_64 "initial_ymm11_1");
	reg R_YMM11_2 (form_man#fresh_symbolic_64 "initial_ymm11_2");
	reg R_YMM11_3 (form_man#fresh_symbolic_64 "initial_ymm11_3");
	reg R_YMM12_0 (form_man#fresh_symbolic_64 "initial_ymm12_0");
	reg R_YMM12_1 (form_man#fresh_symbolic_64 "initial_ymm12_1");
	reg R_YMM12_2 (form_man#fresh_symbolic_64 "initial_ymm12_2");
	reg R_YMM12_3 (form_man#fresh_symbolic_64 "initial_ymm12_3");
	reg R_YMM13_0 (form_man#fresh_symbolic_64 "initial_ymm13_0");
	reg R_YMM13_1 (form_man#fresh_symbolic_64 "initial_ymm13_1");
	reg R_YMM13_2 (form_man#fresh_symbolic_64 "initial_ymm13_2");
	reg R_YMM13_3 (form_man#fresh_symbolic_64 "initial_ymm13_3");
	reg R_YMM14_0 (form_man#fresh_symbolic_64 "initial_ymm14_0");
	reg R_YMM14_1 (form_man#fresh_symbolic_64 "initial_ymm14_1");
	reg R_YMM14_2 (form_man#fresh_symbolic_64 "initial_ymm14_2");
	reg R_YMM14_3 (form_man#fresh_symbolic_64 "initial_ymm14_3");
	reg R_YMM15_0 (form_man#fresh_symbolic_64 "initial_ymm15_0");
	reg R_YMM15_1 (form_man#fresh_symbolic_64 "initial_ymm15_1");
	reg R_YMM15_2 (form_man#fresh_symbolic_64 "initial_ymm15_2");
	reg R_YMM15_3 (form_man#fresh_symbolic_64 "initial_ymm15_3");
	reg R_FTOP (D.from_concrete_32 7L);
	reg R_FC3210 (D.from_concrete_32 0L);
	reg R_FPREG0 (D.from_concrete_64 0L);
	reg R_FPREG1 (D.from_concrete_64 0L);
	reg R_FPREG2 (D.from_concrete_64 0L);
	reg R_FPREG3 (D.from_concrete_64 0L);
	reg R_FPREG4 (D.from_concrete_64 0L);
	reg R_FPREG5 (D.from_concrete_64 0L);
	reg R_FPREG6 (D.from_concrete_64 0L);
	reg R_FPREG7 (D.from_concrete_64 0L);
	reg R_FPTAG0 (D.from_concrete_8 0);
	reg R_FPTAG1 (D.from_concrete_8 0);
	reg R_FPTAG2 (D.from_concrete_8 0);
	reg R_FPTAG3 (D.from_concrete_8 0);
	reg R_FPTAG4 (D.from_concrete_8 0);
	reg R_FPTAG5 (D.from_concrete_8 0);
	reg R_FPTAG6 (D.from_concrete_8 0);
	reg R_FPTAG7 (D.from_concrete_8 0);
	reg R_FPROUND (D.from_concrete_64 0L); (* to nearest *)

    method private make_arm_regs_symbolic =
      let reg r v =
	self#set_int_var (Hashtbl.find reg_to_var r) v
      in
	reg R0   (form_man#fresh_symbolic_32 "initial_r0");
	reg R1   (form_man#fresh_symbolic_32 "initial_r1");
	reg R2   (form_man#fresh_symbolic_32 "initial_r2");
	reg R3   (form_man#fresh_symbolic_32 "initial_r3");
	reg R4   (form_man#fresh_symbolic_32 "initial_r4");
	reg R5   (form_man#fresh_symbolic_32 "initial_r5");
	reg R6   (form_man#fresh_symbolic_32 "initial_r6");
	reg R7   (form_man#fresh_symbolic_32 "initial_r7");
	reg R8   (form_man#fresh_symbolic_32 "initial_r8");
	reg R9   (form_man#fresh_symbolic_32 "initial_r9");
	reg R10  (form_man#fresh_symbolic_32 "initial_r10");
	reg R11  (form_man#fresh_symbolic_32 "initial_r11");
	reg R12  (form_man#fresh_symbolic_32 "initial_r12");
	reg R13  (form_man#fresh_symbolic_32 "initial_r13");
	reg R14  (form_man#fresh_symbolic_32 "initial_r14");
	reg R15T (form_man#fresh_symbolic_32 "initial_r15");
	reg R_NF (form_man#fresh_symbolic_1  "initial_nf");
	reg R_ZF (form_man#fresh_symbolic_1  "initial_zf");
	reg R_CF (form_man#fresh_symbolic_1  "initial_cf");
	reg R_VF (form_man#fresh_symbolic_1  "initial_vf");
	reg R_ITSTATE (form_man#fresh_symbolic_32  "initial_itstate");
	()

    method make_regs_symbolic =
      match !opt_arch with	
	| X86 -> self#make_x86_regs_symbolic
	| X64 -> self#make_x64_regs_symbolic
	| ARM -> self#make_arm_regs_symbolic

    method load_x86_user_regs regs =
      self#set_word_var R_EAX (Int64.of_int32 regs.Temu_state.eax);
      self#set_word_var R_EBX (Int64.of_int32 regs.Temu_state.ebx);
      self#set_word_var R_ECX (Int64.of_int32 regs.Temu_state.ecx);
      self#set_word_var R_EDX (Int64.of_int32 regs.Temu_state.edx);
      self#set_word_var R_ESI (Int64.of_int32 regs.Temu_state.esi);
      self#set_word_var R_EDI (Int64.of_int32 regs.Temu_state.edi);
      self#set_word_var R_ESP (Int64.of_int32 regs.Temu_state.esp);
      self#set_word_var R_EBP (Int64.of_int32 regs.Temu_state.ebp);
      self#set_word_var EFLAGSREST
	(Int64.logand (Int64.of_int32 regs.Temu_state.eflags) 0xfffff72aL);
      (let eflags_i = Int32.to_int regs.Temu_state.eflags in
	 self#set_bit_var R_CF (eflags_i land 1);
	 self#set_bit_var R_PF ((eflags_i lsr 2) land 1);
	 self#set_bit_var R_AF ((eflags_i lsr 4) land 1);
	 self#set_bit_var R_ZF ((eflags_i lsr 6) land 1);
	 self#set_bit_var R_SF ((eflags_i lsr 7) land 1);
	 self#set_bit_var R_OF ((eflags_i lsr 11) land 1));
      self#set_short_var R_CS (Int32.to_int regs.Temu_state.xcs);
      self#set_short_var R_DS (Int32.to_int regs.Temu_state.xds);
      self#set_short_var R_ES (Int32.to_int regs.Temu_state.xes);
      self#set_short_var R_FS (Int32.to_int regs.Temu_state.xfs);
      self#set_short_var R_GS (Int32.to_int regs.Temu_state.xgs);
      self#set_short_var R_SS (Int32.to_int regs.Temu_state.xss)

    method printable_word_reg r =
      D.to_string_32 (self#get_int_var (Hashtbl.find reg_to_var r))

    method printable_long_reg r =
      D.to_string_64 (self#get_int_var (Hashtbl.find reg_to_var r))

    method private print_reg32 str r = 
	Printf.printf "%s: " str;
	Printf.printf "%s\n" (self#printable_word_reg r)
     
    method private print_reg1 str r = 
	Printf.printf "%s: " str;
	Printf.printf "%s\n"
	  (D.to_string_1 
	     (self#get_int_var (Hashtbl.find reg_to_var r)))

    method private print_reg64 str r =
	Printf.printf "%s: " str;
	Printf.printf "%s\n" (self#printable_long_reg r)

    method private print_x87_fpreg idx reg tag =
      let val_d = self#get_int_var (Hashtbl.find reg_to_var reg) in
      let as_float = try
	let f = Int64.float_of_bits (D.to_concrete_64 val_d) in
	  Printf.sprintf " (%.30g)" f;
      with
	| NotConcrete(_) -> ""
      in
	(Printf.printf "FP%d[%s]: %s%s\n" idx
	   (D.to_string_8
	      (self#get_int_var (Hashtbl.find reg_to_var tag)))
	   (D.to_string_64 val_d)) as_float

    method private print_reg128 str rh rl =
      Printf.printf "%s: " str;
      Printf.printf "%s %s\n"
	(D.to_string_64
	   (self#get_int_var (Hashtbl.find reg_to_var rh)))
	(D.to_string_64
	   (self#get_int_var (Hashtbl.find reg_to_var rl)));
	   
	method private print_reg256 str r1 r2 r3 r4 = (* high -> low *)
      Printf.printf "%s: " str;
      Printf.printf "%s %s %s %s\n"
	(D.to_string_64
	   (self#get_int_var (Hashtbl.find reg_to_var r1)))
	(D.to_string_64
	   (self#get_int_var (Hashtbl.find reg_to_var r2)))
	(D.to_string_64
	   (self#get_int_var (Hashtbl.find reg_to_var r3)))
	(D.to_string_64
	   (self#get_int_var (Hashtbl.find reg_to_var r4)));

    method private print_x86_regs =
      self#print_reg32 "%eax" R_EAX;
      self#print_reg32 "%ebx" R_EBX;
      self#print_reg32 "%ecx" R_ECX;
      self#print_reg32 "%edx" R_EDX;
      self#print_reg32 "%esi" R_ESI;
      self#print_reg32 "%edi" R_EDI;
      self#print_reg32 "%esp" R_ESP;
      self#print_reg32 "%ebp" R_EBP;
      self#print_reg1 "CF" R_CF;
      self#print_reg1 "PF" R_PF;
      self#print_reg1 "AF" R_AF;
      self#print_reg1 "ZF" R_ZF;
      self#print_reg1 "SF" R_SF;
      self#print_reg1 "OF" R_OF;
      self#print_reg128 "XMM0" R_XMM0H R_XMM0L;
      self#print_reg128 "XMM1" R_XMM1H R_XMM1L;
      self#print_reg128 "XMM2" R_XMM2H R_XMM2L;
      self#print_reg128 "XMM3" R_XMM3H R_XMM3L;
      self#print_reg128 "XMM4" R_XMM4H R_XMM4L;
      self#print_reg128 "XMM5" R_XMM5H R_XMM5L;
      self#print_reg128 "XMM6" R_XMM6H R_XMM6L;
      self#print_reg128 "XMM7" R_XMM7H R_XMM7L;
      self#print_reg32 "FTOP" R_FTOP;
      self#print_reg32 "FC3210" R_FC3210;
      self#print_x87_fpreg 0 R_FPREG0 R_FPTAG0;
      self#print_x87_fpreg 1 R_FPREG1 R_FPTAG1;
      self#print_x87_fpreg 2 R_FPREG2 R_FPTAG2;
      self#print_x87_fpreg 3 R_FPREG3 R_FPTAG3;
      self#print_x87_fpreg 4 R_FPREG4 R_FPTAG4;
      self#print_x87_fpreg 5 R_FPREG5 R_FPTAG5;
      self#print_x87_fpreg 6 R_FPREG6 R_FPTAG6;
      self#print_x87_fpreg 7 R_FPREG7 R_FPTAG7;
      ()

    method private print_x64_regs =
      self#print_reg64 "%rax" R_RAX;
      self#print_reg64 "%rbx" R_RBX;
      self#print_reg64 "%rcx" R_RCX;
      self#print_reg64 "%rdx" R_RDX;
      self#print_reg64 "%rsi" R_RSI;
      self#print_reg64 "%rdi" R_RDI;
      self#print_reg64 "%rsp" R_RSP;
      self#print_reg64 "%rbp" R_RBP;
      self#print_reg64 "%r8"  R_R8;
      self#print_reg64 "%r9"  R_R9;
      self#print_reg64 "%r10" R_R10;
      self#print_reg64 "%r11" R_R11;
      self#print_reg64 "%r12" R_R12;
      self#print_reg64 "%r13" R_R13;
      self#print_reg64 "%r14" R_R14;
      self#print_reg64 "%r15" R_R15;
      (* Here's how you would print the low 128 bits of the low 8 XMM
         registers, analogous to what we currently do on 32-bit. In
         many cases on x64 though you'd really want to print 16
         registers, and each is really 256 bits, but that would make
         this output even more unwieldy. Leave this disabled for now.
      self#print_reg128 "XMM0" R_YMM0_1 R_YMM0_0;
      self#print_reg128 "XMM1" R_YMM1_1 R_YMM1_0;
      self#print_reg128 "XMM2" R_YMM2_1 R_YMM2_0;
      self#print_reg128 "XMM3" R_YMM3_1 R_YMM3_0;
      self#print_reg128 "XMM4" R_YMM4_1 R_YMM4_0;
      self#print_reg128 "XMM5" R_YMM5_1 R_YMM5_0;
      self#print_reg128 "XMM6" R_YMM6_1 R_YMM6_0;
      self#print_reg128 "XMM7" R_YMM7_1 R_YMM7_0;
       *)
      self#print_reg1 "CF" R_CF;
      self#print_reg1 "PF" R_PF;
      self#print_reg1 "AF" R_AF;
      self#print_reg1 "ZF" R_ZF;
      self#print_reg1 "SF" R_SF;
      self#print_reg1 "OF" R_OF;
      self#print_reg256 "YMM0" R_YMM0_3 R_YMM0_2 R_YMM0_1 R_YMM0_0;
      self#print_reg256 "YMM1" R_YMM1_3 R_YMM1_2 R_YMM1_1 R_YMM1_0;
      self#print_reg256 "YMM2" R_YMM2_3 R_YMM2_2 R_YMM2_1 R_YMM2_0;
      self#print_reg256 "YMM3" R_YMM3_3 R_YMM3_2 R_YMM3_1 R_YMM3_0;
      self#print_reg256 "YMM4" R_YMM4_3 R_YMM4_2 R_YMM4_1 R_YMM4_0;
      self#print_reg256 "YMM5" R_YMM5_3 R_YMM5_2 R_YMM5_1 R_YMM5_0;
      self#print_reg256 "YMM6" R_YMM6_3 R_YMM6_2 R_YMM6_1 R_YMM6_0;
      self#print_reg256 "YMM7" R_YMM7_3 R_YMM7_2 R_YMM7_1 R_YMM7_0;
      self#print_reg256 "YMM8" R_YMM8_3 R_YMM8_2 R_YMM8_1 R_YMM8_0;
      self#print_reg256 "YMM9" R_YMM9_3 R_YMM9_2 R_YMM9_1 R_YMM9_0;
      self#print_reg256 "YMM10" R_YMM10_3 R_YMM10_2 R_YMM10_1 R_YMM10_0;
      self#print_reg256 "YMM11" R_YMM11_3 R_YMM11_2 R_YMM11_1 R_YMM11_0;
      self#print_reg256 "YMM12" R_YMM12_3 R_YMM12_2 R_YMM12_1 R_YMM12_0;
      self#print_reg256 "YMM13" R_YMM13_3 R_YMM13_2 R_YMM13_1 R_YMM13_0;
      self#print_reg256 "YMM14" R_YMM14_3 R_YMM14_2 R_YMM14_1 R_YMM14_0;
      self#print_reg256 "YMM15" R_YMM15_3 R_YMM15_2 R_YMM15_1 R_YMM15_0;

    method private print_arm_regs =
      self#print_reg32 " r0" R0;
      self#print_reg32 " r1" R1;
      self#print_reg32 " r2" R2;
      self#print_reg32 " r3" R3;
      self#print_reg32 " r4" R4;
      self#print_reg32 " r5" R5;
      self#print_reg32 " r6" R6;
      self#print_reg32 " r7" R7;
      self#print_reg32 " r8" R8;
      self#print_reg32 " r9" R9;
      self#print_reg32 "r10" R10;
      self#print_reg32 "r11" R11;
      self#print_reg32 "r12" R12;
      self#print_reg32 " sp" R13;
      self#print_reg32 " lr" R14;
      self#print_reg32 " pc" R15T;
      self#print_reg1 "NF" R_NF;
      self#print_reg1 "ZF" R_ZF;
      self#print_reg1 "CF" R_CF;
      self#print_reg1 "VF" R_VF;
      self#print_reg32 " IT" R_ITSTATE;
      ()

    method print_regs =
      match !opt_arch with	
	| X86 -> self#print_x86_regs
	| X64 -> self#print_x64_regs
	| ARM -> self#print_arm_regs

    method print_syscall_regs =
      match !opt_arch with
	| X86 ->
	    self#print_reg32 "%eax" R_EAX;
	    self#print_reg32 "%ebx" R_EBX;
	    self#print_reg32 "%ecx" R_ECX;
	    self#print_reg32 "%edx" R_EDX;
	    self#print_reg32 "%esi" R_ESI;
	    self#print_reg32 "%edi" R_EDI;
	    self#print_reg32 "%ebp" R_EBP;
	| X64 ->
	    self#print_reg64 "%rax" R_RAX;
	    self#print_reg64 "%rdi" R_RDI;
	    self#print_reg64 "%rsi" R_RSI;
	    self#print_reg64 "%rdx" R_RDX;
	    self#print_reg64 "%r10" R_R10;
	    self#print_reg64 "%r8"  R_R8;
	    self#print_reg64 "%r9"  R_R9;
	| ARM ->
	    self#print_reg32 " r7" R7;
	    self#print_reg32 " r0" R0;
	    self#print_reg32 " r1" R1;
	    self#print_reg32 " r2" R2;
	    self#print_reg32 " r3" R3;
	    self#print_reg32 " r4" R4;
	    self#print_reg32 " r5" R5;
	    self#print_reg32 " r6" R6;

    method private simplify_reg32 r =
      let var = Hashtbl.find reg_to_var r in
	self#set_int_var var (form_man#simplify32 (self#get_int_var var))

    method private simplify_reg1 r =
      let var = Hashtbl.find reg_to_var r in
	self#set_int_var var (form_man#simplify1 (self#get_int_var var))

    method private simplify_reg8 r =
      let var = Hashtbl.find reg_to_var r in
	self#set_int_var var (form_man#simplify8 (self#get_int_var var))

    method private simplify_reg64 r =
      let var = Hashtbl.find reg_to_var r in
	self#set_int_var var (form_man#simplify64 (self#get_int_var var))

    method private simplify_x86_regs =
      self#simplify_reg32 R_EAX;
      self#simplify_reg32 R_EBX;
      self#simplify_reg32 R_ECX;
      self#simplify_reg32 R_EDX;
      self#simplify_reg32 R_ESI;
      self#simplify_reg32 R_EDI;
      self#simplify_reg32 R_ESP;
      self#simplify_reg32 R_EBP;
      self#simplify_reg1 R_CF;
      self#simplify_reg1 R_PF;
      self#simplify_reg1 R_AF;
      self#simplify_reg1 R_ZF;
      self#simplify_reg1 R_SF;
      self#simplify_reg1 R_OF;
      self#simplify_reg64 R_XMM0L; self#simplify_reg64 R_XMM0H;
      self#simplify_reg64 R_XMM1L; self#simplify_reg64 R_XMM1H;
      self#simplify_reg64 R_XMM2L; self#simplify_reg64 R_XMM2H;
      self#simplify_reg64 R_XMM3L; self#simplify_reg64 R_XMM3H;
      self#simplify_reg64 R_XMM4L; self#simplify_reg64 R_XMM4H;
      self#simplify_reg64 R_XMM5L; self#simplify_reg64 R_XMM5H;
      self#simplify_reg64 R_XMM6L; self#simplify_reg64 R_XMM6H;
      self#simplify_reg64 R_XMM7L; self#simplify_reg64 R_XMM7H;
      self#simplify_reg64 R_FPREG0;
      self#simplify_reg64 R_FPREG1;
      self#simplify_reg64 R_FPREG2;
      self#simplify_reg64 R_FPREG3;
      self#simplify_reg64 R_FPREG4;
      self#simplify_reg64 R_FPREG5;
      self#simplify_reg64 R_FPREG6;
      self#simplify_reg64 R_FPREG7;
      self#simplify_reg8 R_FPTAG0;
      self#simplify_reg8 R_FPTAG1;
      self#simplify_reg8 R_FPTAG2;
      self#simplify_reg8 R_FPTAG3;
      self#simplify_reg8 R_FPTAG4;
      self#simplify_reg8 R_FPTAG5;
      self#simplify_reg8 R_FPTAG6;
      self#simplify_reg8 R_FPTAG7;
      ()

    method private simplify_x64_regs =
      self#simplify_reg64 R_RAX;
      self#simplify_reg64 R_RBX;
      self#simplify_reg64 R_RCX;
      self#simplify_reg64 R_RDX;
      self#simplify_reg64 R_RSI;
      self#simplify_reg64 R_RDI;
      self#simplify_reg64 R_RSP;
      self#simplify_reg64 R_RBP;
      self#simplify_reg64 R_R8;
      self#simplify_reg64 R_R9;
      self#simplify_reg64 R_R10;
      self#simplify_reg64 R_R11;
      self#simplify_reg64 R_R12;
      self#simplify_reg64 R_R13;
      self#simplify_reg64 R_R14;
      self#simplify_reg64 R_R15;
      self#simplify_reg1 R_CF;
      self#simplify_reg1 R_PF;
      self#simplify_reg1 R_AF;
      self#simplify_reg1 R_ZF;
      self#simplify_reg1 R_SF;
      self#simplify_reg1 R_OF;
      ()

    method private simplify_arm_regs =
      self#simplify_reg32 R0;
      self#simplify_reg32 R1;
      self#simplify_reg32 R2;
      self#simplify_reg32 R3;
      self#simplify_reg32 R4;
      self#simplify_reg32 R5;
      self#simplify_reg32 R6;
      self#simplify_reg32 R7;
      self#simplify_reg32 R8;
      self#simplify_reg32 R9;
      self#simplify_reg32 R10;
      self#simplify_reg32 R11;
      self#simplify_reg32 R12;
      self#simplify_reg32 R13;
      self#simplify_reg32 R14;
      self#simplify_reg32 R15;
      self#simplify_reg1 R_NF;
      self#simplify_reg1 R_ZF;
      self#simplify_reg1 R_CF;
      self#simplify_reg1 R_VF;
      self#simplify_reg32 R_ITSTATE;
      ()

    method private simplify_regs =
      match !opt_arch with	
	| X86 -> self#simplify_x86_regs
	| X64 -> self#simplify_x64_regs
	| ARM -> self#simplify_arm_regs

    method store_byte  addr b = mem#store_byte  addr b
    method store_short addr s = mem#store_short addr s
    method store_word  addr w = mem#store_word  addr w
    method store_long  addr l = mem#store_long  addr l

    method load_sym addr size = 
      match size with
      | 8 -> D.to_symbolic_8 (mem#load_byte addr)
      | 16 -> D.to_symbolic_16 (mem#load_short addr)
      | 32 -> D.to_symbolic_32 (mem#load_word addr)
      | 64 -> D.to_symbolic_64 (mem#load_long addr)
      | _ -> failwith "Unsupported size in FM#load_sym"

    method store_sym addr size value_s =
      let value = D.from_symbolic value_s in
      match size with
      | 8 -> mem#store_byte addr value
      | 16 -> mem#store_short addr value
      | 32 -> mem#store_word addr value
      | 64 -> mem#store_long addr value
      | _ -> failwith "Unsupported size in FM#store_sym"

    method store_byte_conc  addr b = mem#store_byte addr (D.from_concrete_8 b)
    method store_short_conc addr s = mem#store_short addr(D.from_concrete_16 s)
    method store_word_conc  addr w = mem#store_word addr (D.from_concrete_32 w)
    method store_long_conc  addr l = mem#store_long addr (D.from_concrete_64 l)

    method store_page_conc  addr p = mem#store_page addr p

    method private load_byte  addr = mem#load_byte  addr
    method private load_short addr = mem#load_short addr
    method private load_word  addr = mem#load_word  addr
    method private load_long  addr = mem#load_long  addr

    method load_byte_conc  addr = D.to_concrete_8  (mem#load_byte  addr)
    method load_short_conc addr = D.to_concrete_16 (mem#load_short addr)
    method load_word_conc  addr = D.to_concrete_32 (mem#load_word  addr)
    method load_long_conc  addr = D.to_concrete_64 (mem#load_long  addr)

    method load_byte_concolic  addr =
      form_man#concolic_eval_8  (mem#load_byte  addr)
    method load_short_concolic addr =
      form_man#concolic_eval_16 (mem#load_short addr)
    method load_word_concolic  addr =
      form_man#concolic_eval_32 (mem#load_word  addr)
    method load_long_concolic  addr =
      form_man#concolic_eval_64 (mem#load_long  addr)

    val mutable started_symbolic = false

    method started_symbolic = started_symbolic

    method maybe_start_symbolic setup =
      if not started_symbolic then
	deferred_start_symbolic <- Some setup (* takes effect at end of insn *)
      else
	setup ()

    method start_symbolic =
      (*mem#inner_make_snap ();*)
      mem#make_snap ();
      started_symbolic <- true

    val mutable special_handler_list = ([] : #special_handler list)

    method make_snap () =
      mem#make_snap ();
      snap <- (V.VarHash.copy reg_store, V.VarHash.copy temps);
      List.iter (fun h -> h#make_snap) special_handler_list

    method make_f1_special_handlers_snap =
      if !opt_trace_mem_snapshots = true then
	Printf.printf "FM#make_f1_special_handlers_snap\n";
      List.iter (fun h -> h#make_f1_snap) special_handler_list;
      ()
 
    method reset_f1_special_handlers_snap =
      if !opt_trace_mem_snapshots = true then
	Printf.printf "FM#reset_f1_special_handlers_snap\n";
      List.iter (fun h -> h#reset_f1_snap) special_handler_list;
      ()
 
    method make_f2_special_handlers_snap =
      if !opt_trace_mem_snapshots = true then
	Printf.printf "FM#make_f2_special_handlers_snap\n";
      List.iter (fun h -> h#make_f2_snap) special_handler_list;
      ()
 
    method reset_f2_special_handlers_snap =
      if !opt_trace_mem_snapshots = true then
	Printf.printf "FM#reset_f2_special_handlers_snap\n";
      List.iter (fun h -> h#reset_f2_snap) special_handler_list;
      ()
 
    val mutable fuzz_finish_reasons = []
    val mutable disqualified = false

    method finish_fuzz s =
      if not disqualified then
	(fuzz_finish_reasons <- s :: fuzz_finish_reasons;
	 if !opt_finish_immediately then
	   (Printf.eprintf "Finishing (immediately), %s\n" s;
	    raise FinishNow);
	 if !opt_trace_stopping then (
	   Printf.printf "Final iteration, %s\n" s;
	   flush(stdout););)

    method unfinish_fuzz s =
      fuzz_finish_reasons <- [];
      disqualified <- true;
      if !opt_trace_stopping then
	Printf.printf "Non-finish condition %s\n" s

    method finish_reasons =
      if disqualified then
	[]
      else
	fuzz_finish_reasons

    method reset () =
      if !opt_trace_mem_snapshots = true then
	Printf.printf "FM#reset calling mem#reset()\n";
      mem#reset ();
      (match snap with (r, t) ->
	 move_hash r reg_store;
	 move_hash t temps);
      fuzz_finish_reasons <- [];
      disqualified <- false;
      if (List.length !opt_match_syscalls_addr_range) <> 0 || !opt_repair_frag_start <> 0L then (* we dont provide -match-syscalls-addr-range when doing repair with FuzzBALL *)
	self#reset_syscalls ;
      adapted_arg_addrs <- [];
      in_f1_range <- false;
      in_f2_range <- false;
      num_repair_tests_processed := 0;
      num_invalid_repair_tests_processed := 0;
      synth_verify_adapter := false;
      if !stdin_redirect_fd <> None then (
	if !opt_trace_repair then (
	  Printf.printf "repair: closing previous stdin_redirect_fd\n"; flush(stdout););
	Unix.close (Option.get !stdin_redirect_fd););
      stdin_redirect_fd := None;
      List.iter (fun h -> h#reset) special_handler_list

  method sym_region_struct_adapter = 
    Printf.printf "FM#sym_region_struct_adapter should not have been called\n";
  
  method add_special_handler (h:special_handler) =
      special_handler_list <- h :: special_handler_list

    method handle_special str =
      let rec loop =
	function
	  | h :: rest ->
	      (match h#handle_special str with
		 | (Some sl) as slr -> slr
		 | None -> loop rest)
	  | [] -> None
      in
	loop special_handler_list

    method private get_int_var ((_,vname,ty) as var) =
      try
	let v = V.VarHash.find reg_store var in
	  (* if v = D.uninit then
	     Printf.printf "Warning: read uninitialized register %s\n"
	     vname; *)
	  v
      with
	| Not_found ->
	    (try 
	       V.VarHash.find temps var
	     with
	       | Not_found -> V.pp_var print_string var; 
		   failwith "Unknown variable")

    method get_bit_var_d   reg = self#get_int_var (Hashtbl.find reg_to_var reg)
    method get_byte_var_d  reg = self#get_int_var (Hashtbl.find reg_to_var reg)
    method get_short_var_d reg = self#get_int_var (Hashtbl.find reg_to_var reg)
    method get_word_var_d  reg = self#get_int_var (Hashtbl.find reg_to_var reg)
    method get_long_var_d  reg = self#get_int_var (Hashtbl.find reg_to_var reg)

    method get_bit_var   reg = D.to_concrete_1  (self#get_bit_var_d   reg)
    method get_byte_var  reg = D.to_concrete_8  (self#get_byte_var_d  reg)
    method get_short_var reg = D.to_concrete_16 (self#get_short_var_d reg)
    method get_word_var  reg = D.to_concrete_32 (self#get_word_var_d  reg)
    method get_long_var  reg = D.to_concrete_64 (self#get_long_var_d  reg)

    method get_bit_var_concolic reg =
      form_man#concolic_eval_1 (self#get_int_var (Hashtbl.find reg_to_var reg))

    method get_byte_var_concolic reg =
      form_man#concolic_eval_8 (self#get_int_var (Hashtbl.find reg_to_var reg))

    method get_short_var_concolic reg =
      form_man#concolic_eval_16
	(self#get_int_var (Hashtbl.find reg_to_var reg))

    method get_word_var_concolic reg =
      form_man#concolic_eval_32
	(self#get_int_var (Hashtbl.find reg_to_var reg))

    method get_long_var_concolic reg =
      form_man#concolic_eval_64
	(self#get_int_var (Hashtbl.find reg_to_var reg))

    method private set_int_var ((_,_,ty) as var) value =
      try
	ignore(V.VarHash.find reg_store var);
	V.VarHash.replace reg_store var value
      with
	  Not_found ->
	    V.VarHash.replace temps var value

    method set_bit_var reg v =
      self#set_int_var (Hashtbl.find reg_to_var reg) (D.from_concrete_1 v)

    method set_byte_var reg v =
      self#set_int_var (Hashtbl.find reg_to_var reg) (D.from_concrete_8 v)

    method set_short_var reg v =
      self#set_int_var (Hashtbl.find reg_to_var reg) (D.from_concrete_16 v)

    method set_word_var reg v =
      self#set_int_var (Hashtbl.find reg_to_var reg) (D.from_concrete_32 v)

    method set_long_var reg v =
      self#set_int_var (Hashtbl.find reg_to_var reg) (D.from_concrete_64 v)

    method set_word_var_low_short reg v =
      let var = Hashtbl.find reg_to_var reg in
      let high = D.extract_16_from_32 (self#get_int_var var) 2 in
      let newv = form_man#simplify32
	(D.assemble32 (D.from_concrete_16 v) high)
      in
	self#set_int_var var newv

    method set_word_var_low_byte reg v =
      let var = Hashtbl.find reg_to_var reg in
      let high_s = D.extract_16_from_32 (self#get_int_var var) 2 in
      let second_b = D.extract_8_from_32 (self#get_int_var var) 1 in
      let newv = form_man#simplify32
	(D.assemble32
	   (D.assemble16 (D.from_concrete_8 v) second_b) high_s)
      in
	self#set_int_var var newv

    method set_word_var_second_byte reg v =
      let var = Hashtbl.find reg_to_var reg in
      let high_s = D.extract_16_from_32 (self#get_int_var var) 2 in
      let low_b = D.extract_8_from_32 (self#get_int_var var) 0 in
      let newv = form_man#simplify32
	(D.assemble32
	   (D.assemble16 low_b (D.from_concrete_8 v)) high_s)
      in
	self#set_int_var var newv

    method set_word_reg_symbolic reg s =
      self#set_int_var (Hashtbl.find reg_to_var reg)
	(form_man#fresh_symbolic_32 s);

    method set_long_reg_symbolic reg s =
      self#set_int_var (Hashtbl.find reg_to_var reg)
	(form_man#fresh_symbolic_64 s);

    method set_word_reg_concolic reg s i64 =
      self#set_int_var (Hashtbl.find reg_to_var reg)
	(form_man#make_concolic_32 s i64)

    val mutable symbol_uniq = 0
      
    method set_word_reg_fresh_symbolic reg s =
      let s' = (s ^ "_" ^ (string_of_int symbol_uniq)) in
	self#set_word_reg_symbolic reg s';
	symbol_uniq <- symbol_uniq + 1;
	s' ^ ":reg32_t"

    method set_long_reg_fresh_symbolic reg s : string =
      let s' = (s ^ "_" ^ (string_of_int symbol_uniq)) in
	self#set_long_reg_symbolic reg s';
	symbol_uniq <- symbol_uniq + 1;
	s' ^ ":reg64_t"

    method set_reg_fresh_region reg s =
      let name = s ^ "_" ^ (string_of_int symbol_uniq) in
      (* Make up a fake value for things like null and alignment checks,
	 in case this run is concolic. *)
      let addr = Int64.add 0x70000000L
	(Int64.mul 0x10000L (Int64.of_int symbol_uniq))
      in
	self#set_int_var (Hashtbl.find reg_to_var reg)
	  (form_man#fresh_region_base_concolic name addr);
	symbol_uniq <- symbol_uniq + 1

    (* This relatively simple-looking "handle_load" method is used in
       the concrete-only "vinegrind" tool. In full-fledged FuzzBALL it's
       is overridden by a more complicated version in
       sym_region_frag_machine.ml. *)
    method private handle_load addr_e ty =
      let addr = self#eval_addr_exp addr_e in
      let (v, to_str) =
	(match ty with
	   | V.REG_8  -> (self#load_byte addr,  D.to_string_8)
	   | V.REG_16 -> (self#load_short addr, D.to_string_16)
	   | V.REG_32 -> (self#load_word addr,  D.to_string_32)
	   | V.REG_64 -> (self#load_long addr,  D.to_string_64)
	   | _ -> failwith "Unsupported memory type") in
	(if !opt_trace_loads then
	   (if !opt_trace_eval then
	      Printf.printf "    "; (* indent to match other details *)
	    Printf.printf "Load from conc. mem ";
	    Printf.printf "%08Lx = %s" addr (to_str v);
	    (if !opt_use_tags then
	       Printf.printf " (%Ld @ %08Lx)" (D.get_tag v) (self#get_eip));
	    Printf.printf "\n"));
	if addr >= 0L && addr < 4096L then
	  raise NullDereference;
	(v, ty)

    (* This relatively simple-looking "handle_store" method is used in
       the concrete-only "vinegrind" tool. In full-fledged FuzzBALL it's
       is overridden by a more complicated version in
       sym_region_frag_machine.ml. *)
    method private handle_store addr_e ty rhs_e =
      let addr = self#eval_addr_exp addr_e and
	  value = self#eval_int_exp_simplify rhs_e in
      let (_, to_str) =
	match ty with
	  | V.REG_8  -> (self#store_byte  addr value, D.to_string_8)
	  | V.REG_16 -> (self#store_short addr value, D.to_string_16)
	  | V.REG_32 -> (self#store_word  addr value, D.to_string_32)
	  | V.REG_64 -> (self#store_long  addr value, D.to_string_64)
	  | _ -> failwith "Unsupported type in memory store"
      in
	if !opt_trace_stores then
	  (if !opt_trace_eval then
	     Printf.printf "    "; (* indent to match other details *)
	   Printf.printf "Store to conc. mem ";
	   Printf.printf "%08Lx = %s" addr (to_str value);
	   (if !opt_use_tags then
	      Printf.printf " (%Ld @ %08Lx)" (D.get_tag value) (self#get_eip));
	   Printf.printf "\n");
	if addr >= 0L && addr < 4096L then
	  raise NullDereference

    method private maybe_concretize_binop op v1 v2 ty1 ty2 =
      (v1, v2)

    method private eval_binop op v1 ty1 v2 ty2 =
      let ty = 
	(match op with
	   | V.PLUS | V.MINUS | V.TIMES
	   | V.DIVIDE | V.SDIVIDE | V.MOD | V.SMOD
	   | V.BITAND | V.BITOR | V.XOR
	       -> assert(ty1 = ty2); ty1
	   | V.LSHIFT | V.RSHIFT | V.ARSHIFT
	       -> ty1
	   | V.CONCAT -> assert(ty1 = ty2); V.double_width ty1
	   | V.EQ | V.NEQ | V.LT | V.LE | V.SLT | V.SLE
	       -> assert(ty1 = ty2); V.REG_1) in
      let func =
	(match (op, ty1) with
	   | (V.PLUS, V.REG_1)  -> D.plus1 
	   | (V.PLUS, V.REG_8)  -> D.plus8 
	   | (V.PLUS, V.REG_16) -> D.plus16
	   | (V.PLUS, V.REG_32) -> D.plus32
	   | (V.PLUS, V.REG_64) -> D.plus64
	   | (V.MINUS, V.REG_1)  -> D.minus1 
	   | (V.MINUS, V.REG_8)  -> D.minus8 
	   | (V.MINUS, V.REG_16) -> D.minus16
	   | (V.MINUS, V.REG_32) -> D.minus32
	   | (V.MINUS, V.REG_64) -> D.minus64
	   | (V.TIMES, V.REG_1)  -> D.times1 
	   | (V.TIMES, V.REG_8)  -> D.times8 
	   | (V.TIMES, V.REG_16) -> D.times16
	   | (V.TIMES, V.REG_32) -> D.times32
	   | (V.TIMES, V.REG_64) -> D.times64
	   | (V.DIVIDE, V.REG_1)  -> D.divide1 
	   | (V.DIVIDE, V.REG_8)  -> D.divide8 
	   | (V.DIVIDE, V.REG_16) -> D.divide16
	   | (V.DIVIDE, V.REG_32) -> D.divide32
	   | (V.DIVIDE, V.REG_64) -> D.divide64
	   | (V.SDIVIDE, V.REG_1)  -> D.sdivide1 
	   | (V.SDIVIDE, V.REG_8)  -> D.sdivide8 
	   | (V.SDIVIDE, V.REG_16) -> D.sdivide16
	   | (V.SDIVIDE, V.REG_32) -> D.sdivide32
	   | (V.SDIVIDE, V.REG_64) -> D.sdivide64
	   | (V.MOD, V.REG_1)  -> D.mod1 
	   | (V.MOD, V.REG_8)  -> D.mod8 
	   | (V.MOD, V.REG_16) -> D.mod16
	   | (V.MOD, V.REG_32) -> D.mod32
	   | (V.MOD, V.REG_64) -> D.mod64
	   | (V.SMOD, V.REG_1)  -> D.smod1 
	   | (V.SMOD, V.REG_8)  -> D.smod8 
	   | (V.SMOD, V.REG_16) -> D.smod16
	   | (V.SMOD, V.REG_32) -> D.smod32
	   | (V.SMOD, V.REG_64) -> D.smod64
	   | (V.LSHIFT, V.REG_1)  -> D.lshift1 
	   | (V.LSHIFT, V.REG_8)  -> D.lshift8 
	   | (V.LSHIFT, V.REG_16) -> D.lshift16
	   | (V.LSHIFT, V.REG_32) -> D.lshift32
	   | (V.LSHIFT, V.REG_64) -> D.lshift64
	   | (V.RSHIFT, V.REG_1)  -> D.rshift1 
	   | (V.RSHIFT, V.REG_8)  -> D.rshift8 
	   | (V.RSHIFT, V.REG_16) -> D.rshift16
	   | (V.RSHIFT, V.REG_32) -> D.rshift32
	   | (V.RSHIFT, V.REG_64) -> D.rshift64
	   | (V.ARSHIFT, V.REG_1)  -> D.arshift1 
	   | (V.ARSHIFT, V.REG_8)  -> D.arshift8 
	   | (V.ARSHIFT, V.REG_16) -> D.arshift16
	   | (V.ARSHIFT, V.REG_32) -> D.arshift32
	   | (V.ARSHIFT, V.REG_64) -> D.arshift64
	   | (V.BITAND, V.REG_1)  -> D.bitand1 
	   | (V.BITAND, V.REG_8)  -> D.bitand8 
	   | (V.BITAND, V.REG_16) -> D.bitand16
	   | (V.BITAND, V.REG_32) -> D.bitand32
	   | (V.BITAND, V.REG_64) -> D.bitand64
	   | (V.BITOR, V.REG_1)  -> D.bitor1 
	   | (V.BITOR, V.REG_8)  -> D.bitor8 
	   | (V.BITOR, V.REG_16) -> D.bitor16
	   | (V.BITOR, V.REG_32) -> D.bitor32
	   | (V.BITOR, V.REG_64) -> D.bitor64
	   | (V.XOR, V.REG_1)  -> D.xor1 
	   | (V.XOR, V.REG_8)  -> D.xor8 
	   | (V.XOR, V.REG_16) -> D.xor16
	   | (V.XOR, V.REG_32) -> D.xor32
	   | (V.XOR, V.REG_64) -> D.xor64
	   | (V.CONCAT, V.REG_8)  -> (fun e1 e2 -> D.assemble16 e2 e1)
	   | (V.CONCAT, V.REG_16) -> (fun e1 e2 -> D.assemble16 e2 e1)
	   | (V.CONCAT, V.REG_32) -> (fun e1 e2 -> D.assemble16 e2 e1)
	   | (V.EQ, V.REG_1)  -> D.eq1 
	   | (V.EQ, V.REG_8)  -> D.eq8 
	   | (V.EQ, V.REG_16) -> D.eq16
	   | (V.EQ, V.REG_32) -> D.eq32
	   | (V.EQ, V.REG_64) -> D.eq64
	   | (V.NEQ, V.REG_1)  -> D.neq1 
	   | (V.NEQ, V.REG_8)  -> D.neq8 
	   | (V.NEQ, V.REG_16) -> D.neq16
	   | (V.NEQ, V.REG_32) -> D.neq32
	   | (V.NEQ, V.REG_64) -> D.neq64
	   | (V.LT, V.REG_1)  -> D.lt1 
	   | (V.LT, V.REG_8)  -> D.lt8 
	   | (V.LT, V.REG_16) -> D.lt16
	   | (V.LT, V.REG_32) -> D.lt32
	   | (V.LT, V.REG_64) -> D.lt64
	   | (V.LE, V.REG_1)  -> D.le1 
	   | (V.LE, V.REG_8)  -> D.le8 
	   | (V.LE, V.REG_16) -> D.le16
	   | (V.LE, V.REG_32) -> D.le32
	   | (V.LE, V.REG_64) -> D.le64
	   | (V.SLT, V.REG_1)  -> D.slt1 
	   | (V.SLT, V.REG_8)  -> D.slt8 
	   | (V.SLT, V.REG_16) -> D.slt16
	   | (V.SLT, V.REG_32) -> D.slt32
	   | (V.SLT, V.REG_64) -> D.slt64
	   | (V.SLE, V.REG_1)  -> D.sle1 
	   | (V.SLE, V.REG_8)  -> D.sle8 
	   | (V.SLE, V.REG_16) -> D.sle16
	   | (V.SLE, V.REG_32) -> D.sle32
	   | (V.SLE, V.REG_64) -> D.sle64
	   | _ -> failwith "unexpected binop/type in eval_int_exp_ty")
      in
      let (v1', v2') = self#maybe_concretize_binop op v1 v2 ty1 ty2 in
	(func v1' v2'), ty

    method private eval_fbinop op rm v1 ty1 v2 ty2 =
      let ty =
	(match op with
	   | V.FPLUS | V.FMINUS | V.FTIMES | V.FDIVIDE
	       -> assert(ty1 = ty2); ty1
	   | V.FEQ | V.FNEQ | V.FLT | V.FLE
	       -> assert(ty1 = ty2); V.REG_1) in
      let func =
	(match (op, ty1) with
	   | (V.FPLUS, V.REG_32) -> D.fplus32
	   | (V.FPLUS, V.REG_64) -> D.fplus64
	   | (V.FMINUS, V.REG_32) -> D.fminus32
	   | (V.FMINUS, V.REG_64) -> D.fminus64
	   | (V.FTIMES, V.REG_32) -> D.ftimes32
	   | (V.FTIMES, V.REG_64) -> D.ftimes64
	   | (V.FDIVIDE, V.REG_32) -> D.fdivide32
	   | (V.FDIVIDE, V.REG_64) -> D.fdivide64
	   | (V.FEQ, V.REG_32) -> D.feq32
	   | (V.FEQ, V.REG_64) -> D.feq64
	   | (V.FNEQ, V.REG_32) -> D.fneq32
	   | (V.FNEQ, V.REG_64) -> D.fneq64
	   | (V.FLT, V.REG_32) -> D.flt32
	   | (V.FLT, V.REG_64) -> D.flt64
	   | (V.FLE, V.REG_32) -> D.fle32
	   | (V.FLE, V.REG_64) -> D.fle64
	   | _ -> failwith "unexpected fbinop/type in eval_fbinop")
      in
	(func rm v1 v2), ty

    method private eval_unop op v1 ty1 =
      let result = 
	(match (op, ty1) with
	   | (V.NEG, V.REG_1)  -> D.neg1 v1
	   | (V.NEG, V.REG_8)  -> D.neg8 v1
	   | (V.NEG, V.REG_16) -> D.neg16 v1
	   | (V.NEG, V.REG_32) -> D.neg32 v1
	   | (V.NEG, V.REG_64) -> D.neg64 v1
	   | (V.NOT, V.REG_1)  -> D.not1 v1
	   | (V.NOT, V.REG_8)  -> D.not8 v1
	   | (V.NOT, V.REG_16) -> D.not16 v1
	   | (V.NOT, V.REG_32) -> D.not32 v1
	   | (V.NOT, V.REG_64) -> D.not64 v1
	   | _ -> failwith "unexpected unop/type in eval_int_exp_ty")
      in
	if !opt_trace_eval then
	  Printf.printf "    %s(%s) = %s\n" (V.unop_to_string op)
	    (D.to_string_32 v1) (D.to_string_32 result);
	result, ty1

    method private eval_funop op rm v1 ty1 =
      let result =
	(match (op, ty1) with
	   | (V.FNEG, V.REG_32) -> D.fneg32 rm v1
	   | (V.FNEG, V.REG_64) -> D.fneg64 rm v1
	   | _ -> failwith "unexpected funop/type in eval_funop")
      in
	result, ty1

    method private eval_cast kind ty v1 ty1 =
      let func =
	match (kind, ty1, ty) with
	  | (V.CAST_UNSIGNED, V.REG_1,  V.REG_8)  -> D.cast1u8
	  | (V.CAST_UNSIGNED, V.REG_1,  V.REG_16) -> D.cast1u16
	  | (V.CAST_UNSIGNED, V.REG_1,  V.REG_32) -> D.cast1u32
	  | (V.CAST_UNSIGNED, V.REG_1,  V.REG_64) -> D.cast1u64
	  | (V.CAST_UNSIGNED, V.REG_8,  V.REG_16) -> D.cast8u16
	  | (V.CAST_UNSIGNED, V.REG_8,  V.REG_32) -> D.cast8u32
	  | (V.CAST_UNSIGNED, V.REG_8,  V.REG_64) -> D.cast8u64
	  | (V.CAST_UNSIGNED, V.REG_16, V.REG_32) -> D.cast16u32
	  | (V.CAST_UNSIGNED, V.REG_16, V.REG_64) -> D.cast16u64
	  | (V.CAST_UNSIGNED, V.REG_32, V.REG_64) -> D.cast32u64
	  | (V.CAST_SIGNED, V.REG_1,  V.REG_8)  -> D.cast1s8
	  | (V.CAST_SIGNED, V.REG_1,  V.REG_16) -> D.cast1s16
	  | (V.CAST_SIGNED, V.REG_1,  V.REG_32) -> D.cast1s32
	  | (V.CAST_SIGNED, V.REG_1,  V.REG_64) -> D.cast1s64
	  | (V.CAST_SIGNED, V.REG_8,  V.REG_16) -> D.cast8s16
	  | (V.CAST_SIGNED, V.REG_8,  V.REG_32) -> D.cast8s32
	  | (V.CAST_SIGNED, V.REG_8,  V.REG_64) -> D.cast8s64
	  | (V.CAST_SIGNED, V.REG_16, V.REG_32) -> D.cast16s32
	  | (V.CAST_SIGNED, V.REG_16, V.REG_64) -> D.cast16s64
	  | (V.CAST_SIGNED, V.REG_32, V.REG_64) -> D.cast32s64
	  | (V.CAST_LOW, V.REG_64, V.REG_1)  -> D.cast64l1
	  | (V.CAST_LOW, V.REG_64, V.REG_8)  -> D.cast64l8
	  | (V.CAST_LOW, V.REG_64, V.REG_16) -> D.cast64l16
	  | (V.CAST_LOW, V.REG_64, V.REG_32) -> D.cast64l32
	  | (V.CAST_LOW, V.REG_32, V.REG_1)  -> D.cast32l1
	  | (V.CAST_LOW, V.REG_32, V.REG_8)  -> D.cast32l8
	  | (V.CAST_LOW, V.REG_32, V.REG_16) -> D.cast32l16
	  | (V.CAST_LOW, V.REG_16, V.REG_8)  -> D.cast16l8
	  | (V.CAST_LOW, V.REG_16, V.REG_1)  -> D.cast16l1
	  | (V.CAST_LOW, V.REG_8,  V.REG_1)  -> D.cast8l1
	  | (V.CAST_HIGH, V.REG_64, V.REG_1)  -> D.cast64h1
	  | (V.CAST_HIGH, V.REG_64, V.REG_8)  -> D.cast64h8
	  | (V.CAST_HIGH, V.REG_64, V.REG_16) -> D.cast64h16
	  | (V.CAST_HIGH, V.REG_64, V.REG_32) -> D.cast64h32
	  | (V.CAST_HIGH, V.REG_32, V.REG_1)  -> D.cast32h1
	  | (V.CAST_HIGH, V.REG_32, V.REG_8)  -> D.cast32h8
	  | (V.CAST_HIGH, V.REG_32, V.REG_16) -> D.cast32h16
	  | (V.CAST_HIGH, V.REG_16, V.REG_8)  -> D.cast16h8
	  | (V.CAST_HIGH, V.REG_16, V.REG_1)  -> D.cast16h1
	  | (V.CAST_HIGH, V.REG_8,  V.REG_1)  -> D.cast8h1
	  | _ -> failwith "bad cast kind in eval_int_exp_ty"
      in
	((func v1), ty)

    method private eval_fcast kind rm ty v1 ty1 =
      let func =
	match (kind, ty1, ty) with
	  | (V.CAST_SFLOAT, V.REG_1,  V.REG_32) -> D.float1s32
	  | (V.CAST_SFLOAT, V.REG_8,  V.REG_32) -> D.float8s32
	  | (V.CAST_SFLOAT, V.REG_16, V.REG_32) -> D.float16s32
	  | (V.CAST_SFLOAT, V.REG_32, V.REG_32) -> D.float32s32
	  | (V.CAST_SFLOAT, V.REG_64, V.REG_32) -> D.float64s32
	  | (V.CAST_SFLOAT, V.REG_1,  V.REG_64) -> D.float1s64
	  | (V.CAST_SFLOAT, V.REG_8,  V.REG_64) -> D.float8s64
	  | (V.CAST_SFLOAT, V.REG_16, V.REG_64) -> D.float16s64
	  | (V.CAST_SFLOAT, V.REG_32, V.REG_64) -> D.float32s64
	  | (V.CAST_SFLOAT, V.REG_64, V.REG_64) -> D.float64s64
	  | (V.CAST_UFLOAT, V.REG_1,  V.REG_32) -> D.float1u32
	  | (V.CAST_UFLOAT, V.REG_8,  V.REG_32) -> D.float8u32
	  | (V.CAST_UFLOAT, V.REG_16, V.REG_32) -> D.float16u32
	  | (V.CAST_UFLOAT, V.REG_32, V.REG_32) -> D.float32u32
	  | (V.CAST_UFLOAT, V.REG_64, V.REG_32) -> D.float64u32
	  | (V.CAST_UFLOAT, V.REG_1,  V.REG_64) -> D.float1u64
	  | (V.CAST_UFLOAT, V.REG_8,  V.REG_64) -> D.float8u64
	  | (V.CAST_UFLOAT, V.REG_16, V.REG_64) -> D.float16u64
	  | (V.CAST_UFLOAT, V.REG_32, V.REG_64) -> D.float32u64
	  | (V.CAST_UFLOAT, V.REG_64, V.REG_64) -> D.float64u64
	  | (V.CAST_SFIX, V.REG_32, V.REG_1)  -> D.fix32s1
	  | (V.CAST_SFIX, V.REG_32, V.REG_8)  -> D.fix32s8
	  | (V.CAST_SFIX, V.REG_32, V.REG_16) -> D.fix32s16
	  | (V.CAST_SFIX, V.REG_32, V.REG_32) -> D.fix32s32
	  | (V.CAST_SFIX, V.REG_32, V.REG_64) -> D.fix32s64
	  | (V.CAST_SFIX, V.REG_64, V.REG_1)  -> D.fix64s1
	  | (V.CAST_SFIX, V.REG_64, V.REG_8)  -> D.fix64s8
	  | (V.CAST_SFIX, V.REG_64, V.REG_16) -> D.fix64s16
	  | (V.CAST_SFIX, V.REG_64, V.REG_32) -> D.fix64s32
	  | (V.CAST_SFIX, V.REG_64, V.REG_64) -> D.fix64s64
	  | (V.CAST_UFIX, V.REG_32, V.REG_1)  -> D.fix32u1
	  | (V.CAST_UFIX, V.REG_32, V.REG_8)  -> D.fix32u8
	  | (V.CAST_UFIX, V.REG_32, V.REG_16) -> D.fix32u16
	  | (V.CAST_UFIX, V.REG_32, V.REG_32) -> D.fix32u32
	  | (V.CAST_UFIX, V.REG_32, V.REG_64) -> D.fix32u64
	  | (V.CAST_UFIX, V.REG_64, V.REG_1)  -> D.fix64u1
	  | (V.CAST_UFIX, V.REG_64, V.REG_8)  -> D.fix64u8
	  | (V.CAST_UFIX, V.REG_64, V.REG_16) -> D.fix64u16
	  | (V.CAST_UFIX, V.REG_64, V.REG_32) -> D.fix64u32
	  | (V.CAST_UFIX, V.REG_64, V.REG_64) -> D.fix64u64
	  | (V.CAST_FWIDEN, V.REG_32, V.REG_64) -> D.fwiden32to64
	  | (V.CAST_FNARROW, V.REG_64, V.REG_32) -> D.fnarrow64to32
	  | _ -> failwith "bad fcast kind in eval_fcast"
      in
	((func rm v1), ty)

    method eval_ite v_c v_t v_f ty_t =
      let func =
	match ty_t with
	  | V.REG_1  -> D.ite1
	  | V.REG_8  -> D.ite8
	  | V.REG_16 -> D.ite16
	  | V.REG_32 -> D.ite32
	  | V.REG_64 -> D.ite64
	  | _ -> failwith "unexpeceted type in eval_ite"
      in
	((func v_c v_t v_f), ty_t)

    (* Since we don't make any type distinction between integers and
       floats of the same size, the "eval_int" family of methods all
       include floating point operations in addition to integer
       ones. Perhaps misleading, but the names predated FP support. *)
    method eval_int_exp_ty exp =
      match exp with
	| V.BinOp(op, e1, e2) ->
	    let (v1, ty1) = self#eval_int_exp_ty e1 and
		(v2, ty2) = self#eval_int_exp_ty e2 in
	      self#eval_binop op v1 ty1 v2 ty2
	| V.FBinOp(op, rm, e1, e2) ->
	    let (v1, ty1) = self#eval_int_exp_ty e1 and
		(v2, ty2) = self#eval_int_exp_ty e2 in
	      self#eval_fbinop op rm v1 ty1 v2 ty2
	| V.UnOp(op, e1) ->
	    let (v1, ty1) = self#eval_int_exp_ty e1 in
	      self#eval_unop op v1 ty1
	| V.FUnOp(op, rm, e1) ->
	    let (v1, ty1) = self#eval_int_exp_ty e1 in
	      self#eval_funop op rm v1 ty1
	| V.Constant(V.Int(V.REG_1, i)) ->
	    (D.from_concrete_1 (Int64.to_int i)), V.REG_1
	| V.Constant(V.Int(V.REG_8, i)) ->
	    (D.from_concrete_8 (Int64.to_int i)), V.REG_8
	| V.Constant(V.Int(V.REG_16,i)) -> 
	    (D.from_concrete_16 (Int64.to_int i)),V.REG_16
	| V.Constant(V.Int(V.REG_32,i)) -> (D.from_concrete_32 i),V.REG_32
	| V.Constant(V.Int(V.REG_64,i)) -> (D.from_concrete_64 i),V.REG_64
	| V.Constant(V.Int(_,_)) -> failwith "unexpected integer constant type"
	| V.Lval(V.Temp((_,s,ty) as var)) ->
	    let v = self#get_int_var var in
	      if !opt_trace_eval then
		Printf.printf "    %s is %s\n" s (D.to_string_32 v);
	      (v, ty)
	| V.Lval(V.Mem(memv, idx, ty)) ->
	  self#handle_load idx ty
	| V.Cast(kind, ty, e) ->
	    let (v1, ty1) = self#eval_int_exp_ty e in
	      self#eval_cast kind ty v1 ty1
	| V.FCast(kind, rm, ty, e) ->
	    let (v1, ty1) = self#eval_int_exp_ty e in
	      self#eval_fcast kind rm ty v1 ty1
	| V.Ite(cond, true_e, false_e) ->
           let (v_c, ty_c) = self#eval_int_exp_ty cond in
           (try
              (* short-circuit evaluation if the condition is concrete *)
              let v_c_conc = D.to_concrete_1 v_c in
              if v_c_conc = 1 then
                self#eval_int_exp_ty true_e
              else
                self#eval_int_exp_ty false_e
            with NotConcrete _ ->
              (* symbolic execution evaluates both sides *)
	         let (v_t, ty_t) = self#eval_int_exp_ty true_e and
		     (v_f, ty_f) = self#eval_int_exp_ty false_e in
	         assert(ty_c = V.REG_1);
	         assert(ty_t = ty_f);
	         self#eval_ite v_c v_t v_f ty_t)
	(* XXX move this to something like a special handler: *)
	| V.Unknown("rdtsc") -> ((D.from_concrete_64 1L), V.REG_64) 
	| V.Unknown(_) ->
	    failwith "Unsupported unknown in eval_int_exp_ty"
	| V.Let(_,_,_)
	| V.Name(_)
	| V.Constant(V.Str(_))
	  -> failwith "Unsupported (or non-int) expr type in eval_int_exp_ty"
	    
    method private eval_int_exp exp =
      let (v, _) = self#eval_int_exp_ty exp in
	v

    method private eval_int_exp_simplify_ty exp =
      let (v, ty) = self#eval_int_exp_ty exp in
      let v' =  match (v, ty) with
	| (v, V.REG_1) -> form_man#simplify1 v
	| (v, V.REG_8) -> form_man#simplify8 v
	| (v, V.REG_16) -> form_man#simplify16 v
	| (v, V.REG_32) -> form_man#simplify32 v
	| (v, V.REG_64) -> form_man#simplify64 v
	| _ -> failwith "Unexpected type in eval_int_exp_simplify"
      in
	(v', ty)

    method private eval_int_exp_tempify_ty exp =
      let (v, ty) = self#eval_int_exp_ty exp in
      let v' =  match (v, ty) with
	| (v, V.REG_1) -> form_man#tempify1 v
	| (v, V.REG_8) -> form_man#tempify8 v
	| (v, V.REG_16) -> form_man#tempify16 v
	| (v, V.REG_32) -> form_man#tempify32 v
	| (v, V.REG_64) -> form_man#tempify64 v
	| _ -> failwith "Unexpected type in eval_int_exp_tempify"
      in
	(v', ty)

    method eval_int_exp_simplify exp =
      let (v, _) = self#eval_int_exp_simplify_ty exp in
	v

    method eval_int_exp_tempify exp =
      let (v, _) = self#eval_int_exp_tempify_ty exp in
	v

    method eval_bool_exp exp =
      let v = self#eval_int_exp exp in
	if (D.to_concrete_1 v) = 1 then true else false

    method eval_cjmp exp targ1 targ2 =
      self#eval_bool_exp exp

    method eval_addr_exp exp =
      let v = self#eval_int_exp exp in
	(D.to_concrete_32 v)

    method eval_label_exp e =
      match e with
	| V.Name(lab) -> lab
	| _ ->
	    let addr = self#eval_addr_exp e in
	      Printf.sprintf "pc_0x%Lx" addr

    method jump do_jump lab =
      let rec find_label lab sl =
	match sl with
	  | [] -> None
	  | V.Label(l) :: rest when l = lab -> Some sl
	  | st :: rest -> find_label lab rest 
      in
      loop_cnt <- Int64.succ loop_cnt;
      (if (self#get_in_f2_range ()) then
	f2_loop_cnt <- Int64.succ f2_loop_cnt;);
        (match !opt_iteration_limit_enforced with
	| Some lim -> if loop_cnt > lim then raise TooManyIterations;
	| _ -> ());
	(match !opt_f2_iteration_limit_enforced with
	| Some lim -> if f2_loop_cnt > lim then
	    (Printf.printf "fragment_machine raising TooManyIterations, f2_loop_cnt = %Ld\n" f2_loop_cnt;
	     raise TooManyIterations;);
	| _ -> ());
	let (_, sl) = frag in
	  match find_label lab sl with
	    | None -> lab
	    | Some sl ->
		self#run_sl do_jump sl

    val mutable last_eip = -1L
    val mutable last_insn = "none"
    val mutable saw_jump = false

    val mutable stmt_num = -1
    method private get_stmt_num = stmt_num

    method run_sl do_jump sl =
      let jump lab =
	saw_jump <- true;
	if do_jump lab then
	  self#jump do_jump lab
	else
	  lab
      in
      let rec loop =
	function
	  | [] -> "fallthrough"
	  | st :: rest ->
	     
	      if !opt_trace_stmts then
		(Printf.printf "  %08Lx."
		   (try self#get_eip with NotConcrete(_) -> 0L);
		 (if stmt_num = -1 then
		    Printf.printf "   "
		  else
		    Printf.printf "%03d" stmt_num);
		 Printf.printf " %s\n" (stmt_to_string_compact st));
	      stmt_num <- stmt_num + 1;
	      (match st with
		 | V.Jmp(l) -> jump (self#eval_label_exp l)
		 | V.CJmp(cond, V.Name(l1), V.Name(l2))
		     when
		       ((String.length l1 > 5) &&
			  ((String.sub l1 0 5) = "pc_0x")) ||
			 ((String.length l2 > 5) &&
			    ((String.sub l2 0 5) = "pc_0x")) ->
		     let a1 = try Vine.label_to_addr l1
		     with V.VineError(_) -> self#get_eip and
			 a2 = try Vine.label_to_addr l2
		     with V.VineError(_) -> self#get_eip in
		       if (self#eval_cjmp cond a1 a2) then
			 jump l1
		       else
			 jump l2
		 | V.CJmp(cond, l1, l2) ->
		     let cond_v = self#eval_bool_exp cond in
		       if cond_v then
			 jump (self#eval_label_exp l1)
		       else
			 jump (self#eval_label_exp l2)
		 | V.Move(V.Temp((n,s,t) as v), e) ->
		   let tmp_func e1 = 
		     let rhs = self#eval_int_exp_simplify e1 in
		     let trace_eval () =
		       Printf.printf "    %s <- %s\n" s (D.to_string_32 rhs)
		     in
		     if !opt_trace_eval then
		       trace_eval ()
		     else if !opt_trace_register_updates then
		       if String.sub s 0 1 = "T" then
			 () (* skip updates to temps *)
		       else if String.length s = 4 &&
			      String.sub s 0 2 = "R_" &&
			      String.sub s 3 1 = "F" then
			 () (* skip updates to flags *)
		       else
			 trace_eval ();
		     self#set_int_var v rhs;
		   in
		   (* optimization added in 881a8fc3da52775404121a83ec830165a45847a3 *)		   
		   (match e with
		   | V.Ite(cond, true_e, false_e) ->
		      let (v_c, ty_c) = self#eval_int_exp_ty cond in
		      (try 
			 let v_c_c = D.to_concrete_1 v_c in
			 let other_e = 
			   if v_c_c = 1 then true_e else false_e in
			 (match other_e with
			 | V.Lval(V.Temp(n1, s1, t1)) ->
			    if not (n = n1 && t = t1 && s = s1) then tmp_func e
			 | _ ->  tmp_func e);
		       with NotConcrete _ -> tmp_func e);
		   | _ -> 
		      tmp_func e);
		   loop rest
		 | V.Move(V.Mem(memv, idx_e, ty), rhs_e) ->
		   (match rhs_e with
		   | V.Ite(cond, true_e, false_e) ->
		     let (v_c, ty_c) = self#eval_int_exp_ty cond in
		     (try 
			let v_c_c = D.to_concrete_1 v_c in
			let other_e = 
			  if v_c_c = 1 then true_e else false_e in
			(match other_e with
			| V.Lval(V.Mem(memv_1, idx_e_1, ty_1)) ->
			  if not (idx_e_1 = idx_e && ty = ty_1) then 
			    self#handle_store idx_e ty rhs_e;
			| _ ->  
			  self#handle_store idx_e ty rhs_e;)
		      with NotConcrete _ ->
			self#handle_store idx_e ty rhs_e;)
		   | _ -> 
		     self#handle_store idx_e ty rhs_e;);
		   loop rest
		 | V.Special("VEX decode error") ->
		     raise IllegalInstruction
		 | V.Special(str) ->
		     (match self#handle_special str with
			| Some sl -> 
			    loop (sl @ rest)
			| None ->
			    Printf.printf "Unhandled special %s near 0x%Lx (%s)\n"
			      str (self#get_eip) last_insn;
			    failwith "Unhandled special")
		 | V.Label(l) ->
		     if ((String.length l > 5) && 
			   (String.sub l 0 5) = "pc_0x") then
		       (let eip = Vine.label_to_addr l in
			  self#set_eip eip;
			  (* saw_jump will be set for the fallthrough
			     from one instruction to the next unless it's
			     optimized away (which it won't be when we
			     translate one instruction at a time), so it's
			     an overapproximation. *)
			  if saw_jump then
			    self#run_jump_hooks last_insn last_eip eip;
			  self#run_eip_hooks;
			  stmt_num <- 1;
			  last_eip <- eip;
			  saw_jump <- false);
		     loop rest
		 | V.ExpStmt(e) ->
		     let v = self#eval_int_exp e in
		       ignore(v);
		       loop rest
		 | V.Comment(s) ->
		     if comment_is_insn s then
		       last_insn <- s;
		     loop rest
		 | V.Block(_,_) -> failwith "Block unsupported"
		 | V.Function(_,_,_,_,_) -> failwith "Function unsupported"
		 | V.Return(_) -> failwith "Return unsupported"
		 | V.Call(_,_,_) -> failwith "Call unsupported"
		 | V.Attr(st, _) -> loop (st :: rest)
		 | V.Assert(e) ->
		     let v = self#eval_bool_exp e in
		       assert(v);
		       loop rest
		 | V.Halt(e) ->
		     let v = D.to_concrete_32 (self#eval_int_exp e) in
		       Printf.sprintf "halt_%Ld" v)
      in
	stmt_num <- -1;
	loop sl

    method run () = self#run_sl (fun lab -> true) insns

    method run_to_jump () =
      self#run_sl (fun lab -> (String.sub lab 0 3) <> "pc_") insns

    method fake_call_to_from func_addr ret_addr =
      match !opt_arch with
	| X86 ->
	    let esp = Hashtbl.find reg_to_var R_ESP in
	      [V.Move(V.Temp(esp),
		      V.BinOp(V.MINUS, V.Lval(V.Temp(esp)),
			      V.Constant(V.Int(V.REG_32, 4L))));
	       V.Move(V.Mem(mem_var, V.Lval(V.Temp(esp)), V.REG_32),
		      V.Constant(V.Int(V.REG_32, ret_addr)));
	       V.Jmp(V.Constant(V.Int(V.REG_32, func_addr)))]
	| _ -> failwith "Unsupported arch in fake_call_to_from"

    method disasm_insn_at eip = 
      let bytes = Array.init 16
	(fun i -> Char.chr (self#load_byte_conc
			      (Int64.add eip (Int64.of_int i))))
      in
	Libasmir.sprintf_disasm_rawbytes
	  (libasmir_arch_of_execution_arch !opt_arch)
	  false eip bytes

    method measure_mem_size = mem#measure_size
    method measure_form_man_size = form_man#measure_size
    method measure_dt_size = 0

    method measure_size =
      let measure_add k v n = n + (D.measure_size v) in
	((V.VarHash.fold measure_add reg_store 0),
	 (V.VarHash.fold measure_add temps 0))

    method store_byte_idx base idx b =
      self#store_byte (Int64.add base (Int64.of_int idx)) 
	(D.from_concrete_8 b)

    method store_str base idx str =
      for i = 0 to (String.length str - 1) do
	self#store_byte_idx (Int64.add base idx) i (Char.code str.[i])
      done

    val mutable symbolic_string_id = 0

    method make_symbolic_region base len varname pos =
      for i = 0 to len - 1 do
	let new_pos = pos + i in
	let (regname, size, prefix_size, suffix_size, conc_val) = !opt_input_region_sympresuf in
	if !opt_trace_repair then (
	  Printf.printf "repair: checking input-region, %s, to have concrete value %d at position %d against argument region name, %s\n"
	    regname conc_val new_pos varname; flush(stdout););
	let sym_var = (form_man#fresh_symbolic_mem_8 varname (Int64.of_int (pos + i))) in
	if varname = regname && (new_pos >= prefix_size && new_pos <= size-suffix_size-1) && new_pos < size then (
	  if !opt_trace_repair then (
	    Printf.printf "repair: setting input-region, %s, to have concrete value %d at position %d\n"
	      regname conc_val new_pos; flush(stdout););
	  let conc_exp = V.Constant(V.Int(V.REG_8, (Int64.of_int conc_val))) in
	  self#add_to_path_cond (V.BinOp(V.EQ, conc_exp, (D.to_symbolic_8 sym_var))))
	else if varname = regname && new_pos = (size-1) then (
	  if !opt_trace_repair then (
	    Printf.printf "repair: setting input-region, %s, to have concrete value %d at position %d\n"
	      regname 0 new_pos; flush(stdout););
	  let conc_exp = V.Constant(V.Int(V.REG_8, 0L)) in
	  self#add_to_path_cond (V.BinOp(V.EQ, conc_exp, (D.to_symbolic_8 sym_var))));
	self#store_byte (Int64.add base (Int64.of_int i)) sym_var;
      done

    method make_fresh_symbolic_region base len =
      let varname = "input" ^ (string_of_int symbolic_string_id) in
        symbolic_string_id <- symbolic_string_id + 1;
        self#make_symbolic_region base len varname 0

    method store_symbolic_cstr base len fulllen terminate =
      let varname = "input" ^ (string_of_int symbolic_string_id) ^ "_" in
	symbolic_string_id <- symbolic_string_id + 1;
	for i = 0 to len - 1 do
	  let d = form_man#fresh_symbolic_8 (varname ^ (string_of_int i)) in
	    self#store_byte (Int64.add base (Int64.of_int i)) d;
	    if fulllen then
	      opt_extra_conditions :=
		V.BinOp(V.NEQ, V.Constant(V.Int(V.REG_8, 0L)),
			(D.to_symbolic_8 d))
	      :: !opt_extra_conditions
	done;
	if terminate then
	  self#store_byte_idx base len 0

    method store_concolic_cstr base str terminate =
      let len = String.length str in
      let varname = "input" ^ (string_of_int symbolic_string_id) ^ "_" in
	symbolic_string_id <- symbolic_string_id + 1;
	for i = 0 to len - 1 do
	  self#store_byte (Int64.add base (Int64.of_int i))
	    (form_man#make_concolic_8 (varname ^ (string_of_int i))
	       (Char.code str.[i]))
	done;
	if terminate then
	  self#store_byte_idx base len 0

    method store_concolic_name_str base str varname pos =
      let len = String.length str in
      for i = 0 to len - 1 do
	self#store_byte (Int64.add base (Int64.of_int i))
	  (form_man#make_concolic_8 (varname ^ "_" ^ (string_of_int (pos + i)))
	     (Char.code str.[i]))
      done

    method store_symbolic_wcstr base len =
      let varname = "winput" ^ (string_of_int symbolic_string_id) ^ "_" in
	symbolic_string_id <- symbolic_string_id + 1;
	for i = 0 to len - 1 do
	  self#store_short (Int64.add base (Int64.of_int (2*i)))
	    (form_man#fresh_symbolic_16 (varname ^ (string_of_int i)))
	done;
	self#store_byte_idx base (2*len) 0;
	self#store_byte_idx base (2*len + 1) 0

    method store_symbolic_byte addr varname =
      self#store_byte addr (form_man#fresh_symbolic_8 varname)

    method store_symbolic_short addr varname =
      self#store_short addr (form_man#fresh_symbolic_16 varname)

    method store_symbolic_word addr varname =
      self#store_word addr (form_man#fresh_symbolic_32 varname)

    method store_symbolic_long addr varname =
      self#store_long addr (form_man#fresh_symbolic_64 varname)

    method store_concolic_mem_byte addr varname idx b =
      self#store_byte addr (form_man#make_concolic_mem_8 varname idx b)

    method store_concolic_byte addr varname i =
      self#store_byte addr (form_man#make_concolic_8 varname i)

    method store_concolic_short addr varname i =
      self#store_short addr (form_man#make_concolic_16 varname i)

    method store_concolic_word addr varname i64 =
      self#store_word addr (form_man#make_concolic_32 varname i64)

    method store_concolic_long addr varname i64 =
      self#store_long addr (form_man#make_concolic_64 varname i64)

    method set_reg_conc_bytes reg byte_array =
      let change_func = match Array.length byte_array with
	| 2 -> change_some_short_bytes form_man
	| 4 -> change_some_word_bytes form_man
	| 8 -> change_some_long_bytes form_man
	| _ -> failwith "Unsupported length in set_reg_conc_bytes"
      in
      let var = Hashtbl.find reg_to_var reg in
      let old_d = self#get_int_var var in
      let new_d =
	change_func old_d byte_array (fun b -> D.from_concrete_8 b)
      in
	self#set_int_var var new_d

    method set_reg_concolic_mem_bytes reg byte_array =
      let change_func = match Array.length byte_array with
	| 2 -> change_some_short_bytes form_man
	| 4 -> change_some_word_bytes form_man
	| 8 -> change_some_long_bytes form_man
	| _ -> failwith "Unsupported length in set_reg_concolic_mem_bytes"
      in
      let var = Hashtbl.find reg_to_var reg in
      let old_d = self#get_int_var var in
      let new_d =
	change_func old_d byte_array
	  (fun (s,i,v) -> form_man#make_concolic_mem_8 s i v)
      in
	self#set_int_var var new_d

    method private assemble_concolic_exp exp 
      byte_vars short_vars word_vars long_vars =
      let byte_ds =
	List.map (fun (s, v) -> (s, form_man#make_concolic_8 s v))
	  byte_vars in
      let short_ds =
	List.map (fun (s, v) -> (s, form_man#make_concolic_16 s v))
	  short_vars in
      let word_ds =
	List.map (fun (s, v) -> (s, form_man#make_concolic_32 s v))
	  word_vars in
      let long_ds =
	List.map (fun (s, v) -> (s, form_man#make_concolic_64 s v))
	  long_vars in
      let rec rw_loop e =
	match e with
	  | V.Unknown(s) ->
	      (try
		 (List.assoc s byte_ds, V.REG_8)
 	       with Not_found -> try
		 (List.assoc s short_ds, V.REG_16)
 	       with Not_found -> try
		 (List.assoc s word_ds, V.REG_32)
 	       with Not_found ->
		 (List.assoc s long_ds, V.REG_16))
	  | V.Constant(V.Int(V.REG_1, i)) ->
	      (D.from_concrete_1 (Int64.to_int i)), V.REG_1
	  | V.Constant(V.Int(V.REG_8, i)) ->
	      (D.from_concrete_8 (Int64.to_int i)), V.REG_8
	  | V.Constant(V.Int(V.REG_16,i)) -> 
	      (D.from_concrete_16 (Int64.to_int i)),V.REG_16
	  | V.Constant(V.Int(V.REG_32,i)) -> (D.from_concrete_32 i),V.REG_32
	  | V.Constant(V.Int(V.REG_64,i)) -> (D.from_concrete_64 i),V.REG_64
	  | V.Constant(V.Int(_, _)) ->
	      failwith "Unhandled weird-typed integer constant in concolic_exp"
	  | V.BinOp(op, e1, e2) ->
	      let (v1, ty1) = rw_loop e1 and
		  (v2, ty2) = rw_loop e2 in
		self#eval_binop op v1 ty1 v2 ty2
	  | V.UnOp(op, e1) ->
	      let (v1, ty1) = rw_loop e1 in
		self#eval_unop op v1 ty1
	  | V.Cast(kind, ty, e1) ->
	      let (v1, ty1) = rw_loop e1 in
		self#eval_cast kind ty v1 ty1
	  | V.Ite(ce, te, fe) ->
	    let (v_c, ty_c) = rw_loop ce and
		(v_t, ty_t) = rw_loop te and
		(v_f, ty_f) = rw_loop fe in
	      self#eval_ite v_c v_t v_f ty_t
	  | V.FBinOp(_, _, _, _)
	  | V.FUnOp(_, _, _)
	  | V.FCast(_, _, _, _)
	    -> failwith "FP op unsupported in concolic_exp"
	  | V.Let(_, _, _)
	  | V.Name(_)
	  | V.Lval(_)
	  | V.Constant(V.Str(_))
	    -> failwith "Unhandled expression type in concolic_exp"
      in
	rw_loop exp

    method store_concolic_exp addr exp bv sv wv lv =
      let (d, ty) = self#assemble_concolic_exp exp bv sv wv lv in
	match ty with
	  | V.REG_8  -> self#store_byte  addr d
	  | V.REG_16 -> self#store_short addr d
	  | V.REG_32 -> self#store_word  addr d
	  | V.REG_64 -> self#store_long  addr d
	  | _ -> failwith "Unsupported type in store_conolic_exp"

    method set_word_reg_concolic_exp reg exp bv sv wv lv =
      let (d, _) = self#assemble_concolic_exp exp bv sv wv lv in
	self#set_int_var (Hashtbl.find reg_to_var reg) d

    method mem_byte_has_loop_var addr =
      form_man#has_loop_var (self#load_byte addr)

    method mem_short_has_loop_var addr =
      form_man#has_loop_var (self#load_short addr)

    method mem_word_has_loop_var addr =
      form_man#has_loop_var (self#load_word addr)

    method mem_long_has_loop_var addr =
      form_man#has_loop_var (self#load_long addr)

    method word_reg_has_loop_var reg =
      form_man#has_loop_var
	(self#get_int_var (Hashtbl.find reg_to_var reg))      

    method parse_symbolic_expr str =
      Vine_parser.parse_exp_from_string (form_man#input_dl) str

    method store_cstr base idx str =
      self#store_str base idx str;
      self#store_byte_idx (Int64.add base idx) (String.length str) 0

    method read_buf addr len =
      Array.init len
	(fun i -> Char.chr
	   (D.to_concrete_8 (mem#load_byte (Int64.add addr (Int64.of_int i)))))

    method read_cstr addr =
      let rec bytes_loop i =
	let b = D.to_concrete_8 (mem#load_byte
				   (Int64.add addr (Int64.of_int i)))
	in
	  if b = 0 then [] else b :: bytes_loop (i + 1)
      in
	String.concat ""
	  (List.map (fun b -> String.make 1 (Char.chr b))
	     (bytes_loop 0))

    method zero_fill vaddr n =
      for i = 0 to n - 1 do
	self#store_byte_conc (Int64.add vaddr (Int64.of_int i)) 0
      done

    method print_backtrace =
      let read_addr addr =
	try
	  let v = self#load_word_conc addr in
	    (v, Printf.sprintf "0x%08Lx" v)
	with NotConcrete(s) -> (0L, "<symbolic " ^ (V.exp_to_string s) ^ ">")
      in
      let rec loop ebp =
	let (prev_ebp, prev_ebp_s) = read_addr ebp and
	    (_, ret_addr_s) = read_addr (Int64.add ebp 4L) in
	  Printf.printf "0x%08Lx %s %s\n" ebp prev_ebp_s ret_addr_s;
	  if (prev_ebp <> 0L) then
	    loop prev_ebp
      in
	loop (self#get_word_var R_EBP)

    method private eval_expr_to_string e =
      match self#eval_int_exp_simplify_ty e with
	| (v, V.REG_1) -> D.to_string_1 v
	| (v, V.REG_8) -> D.to_string_8 v
	| (v, V.REG_16) -> D.to_string_16 v
	| (v, V.REG_32) -> D.to_string_32 v
	| (v, V.REG_64) -> D.to_string_64 v
	| _ -> failwith "Unexpected type in eval_expr_to_string"

    method eval_expr_to_int64 e =
      match self#eval_int_exp_ty e with
	| (v, V.REG_1) -> Int64.of_int (D.to_concrete_1 v)
	| (v, V.REG_8) -> Int64.of_int (D.to_concrete_8 v)
	| (v, V.REG_16) -> Int64.of_int (D.to_concrete_16 v)
	| (v, V.REG_32) -> D.to_concrete_32 v
	| (v, V.REG_64) -> D.to_concrete_64 v
	| _ -> failwith "Unexpected type in eval_expr_to_int64"

    method eval_expr_to_symbolic_expr e =
      match self#eval_int_exp_ty e with
	| (v, V.REG_1) -> D.to_symbolic_1 v
	| (v, V.REG_8) -> D.to_symbolic_8 v
	| (v, V.REG_16) -> D.to_symbolic_16 v
	| (v, V.REG_32) -> D.to_symbolic_32 v
	| (v, V.REG_64) -> D.to_symbolic_64 v
	| _ -> failwith "Unexpected type in eval_expr_to_symbolic_expr"

    method watchpoint =
      match !opt_watch_expr with
	| Some e -> Printf.printf "Watched expression %s = %s\n"
	    (match !opt_watch_expr_str with Some s -> s | None -> "???")
	      (self#eval_expr_to_string e)
	| None -> ()

    method mem_val_as_string addr ty =
      match ty with
	| V.REG_8  -> D.to_string_8  (self#load_byte  addr)
	| V.REG_16 -> D.to_string_16 (self#load_short addr)
	| V.REG_32 -> D.to_string_32 (self#load_word  addr)
	| V.REG_64 -> D.to_string_64 (self#load_long  addr)
	| _ -> failwith "Unexpected type in mem_val_as_string"

    method query_with_path_cond (e:Vine.exp) (v:bool)
      : (bool * Query_engine.sat_assign) =
      (false, (Query_engine.ce_from_list []))
    method query_condition (e:Vine.exp) (b:bool option) 
	(i:int) : (bool * bool option) =
      (false,None)
    method query_unique_value (e:Vine.exp) (t:Vine.typ) = None
    method add_to_path_cond (e:Vine.exp) = ()
    method match_input_var (s:string) : int option = None
    method get_path_cond : Vine.exp list = []
    method on_missing_random : unit =
      failwith "FM.on_missing_random: unimplemented"
    method set_query_engine (qe:Query_engine.query_engine) = ()
    method print_tree (oc:out_channel) = ()
    method set_iter_seed (i:int) = ()
    method random_byte = Random.int 256
    method finish_path = false
    method after_exploration = ()
    method make_x86_segtables_symbolic = ()
    method store_word_special_region (r:register_name) (i1:int64) (i2:int64)
      : unit =
      failwith "store_word_special_region needs a symbolic region machine"
    method get_word_var_concretize r (b:bool) (s:string) = self#get_word_var r
    method get_long_var_concretize r (b:bool) (s:string) = self#get_long_var r
    method load_byte_concretize  addr (b:bool) (s:string)
      = self#load_byte_conc addr
    method load_short_concretize addr (b:bool) (s:string)
      = self#load_short_conc addr
    method load_word_concretize  addr (b:bool) (s:string)
      = self#load_word_conc addr
    method load_long_concretize  addr (b:bool) (s:string)
      = self#load_long_conc addr
    method make_sink_region (s:string) (i:int64) = ()

    method read_wrong_adapters =
      (* taken from https://stackoverflow.com/questions/5774934/how-do-i-read-in-lines-from-a-text-file-in-ocaml *)
      let read_file filename =
	let lines = ref [] in
	let chan = open_in filename in
	try
	  while true; do
	    lines := input_line chan :: !lines
	  done; !lines
	with End_of_file ->
	  close_in chan;
	  List.rev !lines
      in
      let wrong_argsub_adapters = ref [] in
      if !opt_wrong_argsub_adapters_file <> "" && !opt_adapter_search_mode then (
	let lines = read_file !opt_wrong_argsub_adapters_file in
	for i = 0 to (List.length lines) - 1 do
	  let line = List.nth lines i in
	  let adapter_str_list = String.split_on_char ',' line in
	  let adapter_int64_list = List.map (fun s -> Int64.of_string s) adapter_str_list in
	  wrong_argsub_adapters := !wrong_argsub_adapters @ [adapter_int64_list];
	done;
      );
      let wrong_ret_adapters = ref [] in
      if !opt_wrong_ret_adapters_file <> "" && !opt_adapter_search_mode then (
	let lines = read_file !opt_wrong_ret_adapters_file in
	for i = 0 to (List.length lines) - 1 do
	  let line = List.nth lines i in
	  let adapter_str_list = String.split_on_char ',' line in
	  let adapter_int64_list = List.map (fun s -> Printf.printf "convert %s to int64\n" s; flush(stdout); Int64.of_string s) adapter_str_list in
	  wrong_ret_adapters := !wrong_ret_adapters @ [adapter_int64_list];
	done;
      );
      assert ((List.length !wrong_argsub_adapters) = (List.length !wrong_ret_adapters)
	     || (List.length !wrong_ret_adapters = 0));
      assert ((List.length !wrong_argsub_adapters) = 0 || !opt_adapter_search_mode); 
      if !opt_trace_repair then (Printf.printf "repair: wrong adapters: "; flush(stdout););
      for i = 0 to (List.length !wrong_argsub_adapters)-1 do
	let wrong_argsub_adapter = List.nth !wrong_argsub_adapters i in
	let wrong_ret_adapter =
	  if (List.length !wrong_ret_adapters) > 0 then
	    List.nth !wrong_ret_adapters i else [] in
	if !opt_trace_repair then (
	  Printf.printf "repair: argsub: ";
	  List.iter (fun i -> Printf.printf "%Ld," i) wrong_argsub_adapter;
	  Printf.printf "\nretvalsub: ";
	  List.iter (fun i -> Printf.printf "%Ld," i) wrong_ret_adapter;
	  Printf.printf "\n";
	  flush(stdout););
	opt_extra_conditions :=
	  V.UnOp(V.NOT, (self#generate_adapter_constraint wrong_argsub_adapter wrong_ret_adapter))
	  :: !opt_extra_conditions;
      done;

    method private generate_adapter_constraint argsub retsub =
      let nargs = match !opt_synth_repair_adapter with
	| Some (_, nargs) -> Int64.to_int nargs
	| None -> 0 in
      let (size, vine_size) = 
	match !opt_arch with 
	| X64 -> (64, V.REG_64)
	| ARM | X86 -> (32, V.REG_32) in
      let rec loop n =
	if n < nargs then (
	let var_name = String.make 1 (Char.chr ((Char.code 'a') + n)) in
	let var_val = self#get_fresh_symbolic (var_name^"_val") size in
	let var_is_const = self#get_fresh_symbolic (var_name^"_is_const") 1 in
	let var_is_const_value = List.nth argsub (2*n) in
	let var_val_value = List.nth argsub (2*n+1) in
	[V.BinOp(V.EQ, var_is_const, V.Constant(V.Int(V.REG_1, var_is_const_value)))]
	@ [V.BinOp(V.EQ, var_val, V.Constant(V.Int(vine_size, var_val_value)))]
	@ loop (n+1)) else [] in
      let argsub_cons = loop 0 in
      let true_cons = (V.Constant(V.Int(V.REG_1, 1L))) in
      let retsub_cons =
	if (List.length retsub) > 0 then (
	  let ret_type = (self#get_fresh_symbolic ("ret_type") 8) in
	  let ret_val = (self#get_fresh_symbolic ("ret_val") size) in
	  let ret_type_value = List.nth retsub 0 in
	  let ret_val_value = List.nth retsub 1 in
	  [V.BinOp(V.EQ, ret_type, V.Constant(V.Int(V.REG_8, ret_type_value)))]
	  @ [V.BinOp(V.EQ, ret_val, V.Constant(V.Int(vine_size, ret_val_value)))])
	else [true_cons] in
      if !opt_trace_repair then (
	Printf.printf "repair: generated %d argsub constraints\n" (List.length argsub_cons);
	Printf.printf "repair: generated %d retsub constraints\n" (List.length retsub_cons); flush(stdout));
      List.fold_left (fun a b -> V.BinOp(V.BITAND, a, b)) true_cons
	(argsub_cons @ retsub_cons)
      
    method read_repair_frag_inputs =
      let (prefix, num_tests) = !opt_repair_tests_file in
      let (_, input_size) = !opt_repair_frag_input in
      if num_tests > 0 then (
	for i = 0 to num_tests-1 do
	  let file_name = prefix ^ (Printf.sprintf "%d" i) in
	  let int_vals = self#read_int_inputs file_name input_size in
	  repair_frag_inputs <- repair_frag_inputs @ [int_vals];
	  if !opt_trace_repair then (
	    Printf.printf "repair: file_name = %s, int_vals =  " file_name;
	    for j = 0 to (List.length int_vals)-1 do
	      Printf.printf "%d, " (List.nth int_vals j);
	    done;
	    Printf.printf "\n";
	    flush(stdout););
	done;
      );

    method read_invalid_repair_frag_inputs =
      let (prefix, num_tests) = !opt_invalid_repair_tests_file in
      let (_, input_size) = !opt_repair_frag_input in
      if num_tests > 0 then (
	for i = 0 to num_tests-1 do
	  let file_name = prefix ^ (Printf.sprintf "%d" i) in
	  let int_vals = self#read_int_inputs file_name input_size in
	  invalid_repair_frag_inputs <- invalid_repair_frag_inputs @ [int_vals];
	  if !opt_trace_repair then (
	    Printf.printf "repair: file_name = %s, int_vals =  " file_name;
	    for j = 0 to (List.length int_vals)-1 do
	      Printf.printf "%d, " (List.nth int_vals j);
	    done;
	    Printf.printf "\n";
	    flush(stdout););
	done;
      );

    method private read_int_inputs file_name input_size =
      let get_bytes_from_file filename len =
	let ch = open_in filename in
	let buf = Buffer.create len in
	(try Buffer.add_channel buf ch len
	 with End_of_file ->
	   failwith (Printf.sprintf "failed to read %d bytes from %s file\n" len filename));
	close_in ch;
	Buffer.to_bytes buf
      in
      let bytes = get_bytes_from_file file_name input_size in
      let rec bytes_to_ints bytes ind =
	if ind < Bytes.length bytes then
	  (int_of_char (Bytes.get bytes ind)) :: (bytes_to_ints bytes (ind+1))
	else [] in
      bytes_to_ints bytes 0
	  
      
    method private apply_target_frag_inputs =
      self#store_test_inputs (List.nth repair_frag_inputs !num_repair_tests_processed)

    method private apply_invalid_repair_target_frag_inputs =
      self#store_test_inputs (List.nth invalid_repair_frag_inputs !num_invalid_repair_tests_processed)

    method private store_test_inputs this_test_inputs =
      let (target_frag_input_addr, num_bytes) = !opt_repair_frag_input in
      assert (num_bytes = List.length this_test_inputs || target_frag_input_addr = 0L);
      for i = 0 to num_bytes-1 do
	let addr = (Int64.add target_frag_input_addr (Int64.of_int i)) in
	let value = (List.nth this_test_inputs i) in
	self#store_byte_conc addr value;
	if !opt_trace_repair then (
	  Printf.printf "repair: Wrote %d byte value to address 0x%08Lx\n" value addr;
	  flush(stdout););
      done;
	
    method get_repair_tests_processed = !num_repair_tests_processed

    method inc_repair_tests_processed =
      if !opt_trace_repair then (
	Printf.printf "repair: Incrementing num_repair_tests_processed from %d to %d\n"
	  !num_repair_tests_processed (!num_repair_tests_processed + 1);
	flush(stdout););
      num_repair_tests_processed := !num_repair_tests_processed + 1;
      let (_, total_repair_tests) = !opt_repair_tests_file in
      if !num_repair_tests_processed < total_repair_tests then (
	if !stdin_redirect_fd <> None then (
	  if !opt_trace_repair then (
	    Printf.printf "repair: closing previous stdin_redirect_fd\n"; flush(stdout););
	  Unix.close (Option.get !stdin_redirect_fd);
	) else (
	  if !opt_trace_repair then (
	    Printf.printf "repair: stdin_redirect_fd was already None\n"; flush(stdout););
	);
	self#open_stdin_redirect_fd;
      );
      !num_repair_tests_processed

    method get_invalid_repair_tests_processed = !num_invalid_repair_tests_processed

    method inc_invalid_repair_tests_processed =
      if !opt_trace_repair then (
	Printf.printf "repair: Incrementing num_invalid_repair_tests_processed from %d to %d\n"
	  !num_invalid_repair_tests_processed (!num_invalid_repair_tests_processed + 1);
	flush(stdout););
      num_invalid_repair_tests_processed := !num_invalid_repair_tests_processed + 1;
      let (_, total_invalid_repair_tests) = !opt_invalid_repair_tests_file in
      if !num_invalid_repair_tests_processed < total_invalid_repair_tests then (
	if !stdin_redirect_fd <> None then (
	  if !opt_trace_repair then (
	    Printf.printf "repair: closing previous stdin_redirect_fd\n"; flush(stdout););
	  Unix.close (Option.get !stdin_redirect_fd);
	) else (
	  if !opt_trace_repair then (
	    Printf.printf "repair: stdin_redirect_fd was already None\n"; flush(stdout););
	);
	self#open_stdin_redirect_fd;
      );
      !num_invalid_repair_tests_processed

    method get_adapter_search_mode_stdin_fd =
      assert(!opt_adapter_search_mode);
      if !opt_trace_repair then (
	Printf.printf "repair: get_adapter_search_mode_stdin_fd called, in-f1-range=%B, in-f2-range=%B\n"
	  in_f1_range in_f2_range; flush(stdout););
      if not (self#get_in_f1_range ()) && not (self#get_in_f2_range ()) then (
	if !opt_trace_repair then (
	  Printf.printf "****warning: repair: get_adapter_search_mode: not in f1 or f2 range in adapter-search-mode, returning fd to /dev/zero****\n";
	  flush(stdout););
	Unix.openfile "/dev/zero" [Unix.O_RDONLY] 0o666)
      else (
	let rec deoptionize_stdin_fd ref_fd = 
	  match ref_fd with
	  | None -> self#open_stdin_redirect_fd;
	    deoptionize_stdin_fd !stdin_redirect_fd
	  | Some fd -> fd in
	deoptionize_stdin_fd !stdin_redirect_fd)
	
    method private open_stdin_redirect_fd =
      assert(!opt_adapter_search_mode);
      let get_file_name (prefix, len) ind = assert(ind < len && ind >= 0);
	prefix ^ (Printf.sprintf "%d" ind) in
      assert(self#get_in_f1_range () || self#get_in_f2_range ());
      stdin_redirect_fd := Some (match (!opt_replace_stdin_with_zero, !opt_adapter_search_mode, !synth_verify_adapter) with
      | (true, _, _) -> failwith "turn off -replace-stdin-with-zero when replacing stdin in -adapter-search-mode" 
      | (false, true, false) ->
	 let file_name = get_file_name !opt_repair_tests_file (self#get_repair_tests_processed) in
	 if !opt_trace_repair then (
	   Printf.printf "repair: setting stdin to read from from file_name = %s\n" file_name; flush(stdout););
	 Unix.openfile file_name [Unix.O_RDONLY] 0o600
      | (false, true, true) ->
	 let file_name = get_file_name !opt_invalid_repair_tests_file (self#get_invalid_repair_tests_processed) in
	 if !opt_trace_repair then (
	   Printf.printf "repair: setting stdin to read from file_name = %s\n" file_name; flush(stdout););
	 Unix.openfile file_name [Unix.O_RDONLY] 0o600
      | (_, false, _) -> failwith "repair: fm#open_stdin_redirect_fd should never be called when adapter-search-mode is turned off");
	
     method conc_mem_struct_adapter end_of_f1 =
      let get_ite_expr arg op const_type const then_val else_val = 
	V.Ite(V.BinOp(op, arg, V.Constant(V.Int(const_type, const))),
              then_val,
              else_val)
      in
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
      in
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
      let simplify e = 
	if !opt_split_target_formulas = true then self#simplify_exp e else e in

      let start_time = Sys.time () in
      let step_str = if end_of_f1 then "eof1" else "sof2" in
      if (List.length !opt_synth_struct_adapter) <> 0 then (
	if !opt_trace_struct_adapter = true then
	  Printf.printf "Starting structure adapter %s\n" step_str;
	if !opt_time_stats then
	  (Printf.printf "Generating structure adapter formulas...";
	   flush stdout);
	let addr_list_ind = if end_of_f1 then !e_o_f1_count else !f2_init_count in
	let addr = List.nth !opt_synth_struct_adapter addr_list_ind in
	let adapter_vals = Hashtbl.copy Adapter_vars.adapter_vals in
	  if !opt_time_stats then
	    (Printf.printf "(0x%08Lx)..." addr;
	     flush stdout);
	  if (Int64.abs (fix_s32 addr)) > 4096L then (
	    let (_, _, max_size) = !opt_struct_adapter_params in
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
		let value = (self#load_sym tmp_addr (target_sz*8)) in
		let ai_entry = 
		  upcast value cast_op (ai_f_sz*8) in 
		(* let m_sym = upcast (self#get_fresh_symbolic 
		  (Printf.sprintf "m%d_arith" field_num) 64) (Some V.CAST_LOW) (ai_f_sz*8) in
		let c_sym = upcast (self#get_fresh_symbolic 
		  (Printf.sprintf "c%d_arith" field_num) 64) (Some V.CAST_LOW) (ai_f_sz*8) in
		let arith_expr = V.BinOp(V.PLUS, 
					 V.BinOp(V.TIMES, m_sym, ai_entry), c_sym) in
		get_byte arith_expr ai_r *)
		get_byte ai_entry ai_r
	      in
	      match this_array_field_ranges_l with
	      | [] -> failwith "AS#get_arr_t_field_expr ran out of this_array_field_ranges_l"
	      | [(start_byte, end_byte, n, f_sz)] -> 
		assert(n = ai_n);
		let start_addr = (Int64.add addr (Int64.of_int start_byte)) in
		let base_expr = get_ai_byte_expr n f_sz start_addr 1 in
		let base_expr_unsigned  = get_ai_byte_expr n f_sz start_addr 0 in
		if !opt_trace_struct_adapter then (
		  Printf.printf "base case for get_arr_t_field_expr (%d, %d, %d, %d) ai_byte = %d\n"
		    start_byte end_byte n f_sz ai_byte;
		  flush(stdout); );
		let f_type_str = "f"^(Printf.sprintf "%d" field_num)^"_type" in
		let f_type = 
		  if not !opt_adapter_search_mode then 
		    Hashtbl.find adapter_vals f_type_str
		  else self#get_fresh_symbolic f_type_str 64 in
		let sign_extend_val = Int64.of_int ((start_byte lsl 32)+(end_byte lsl 16)+1) in 
		let zero_extend_val = Int64.of_int ((start_byte lsl 32)+(end_byte lsl 16)+0) in 
		get_ite_expr f_type V.EQ V.REG_64 sign_extend_val base_expr 
		  (get_ite_expr f_type V.EQ V.REG_64 zero_extend_val base_expr_unsigned
		     (V.Constant(V.Int(V.REG_8, 0L)))) 
		(* base_expr *)
	      | (start_byte, end_byte, n, f_sz)::tail ->
		assert(n = ai_n);
		let start_addr = (Int64.add addr (Int64.of_int start_byte)) in
		let is_extend_req = (f_sz - 8) in
		if is_extend_req <> 0 then (
		  let sign_extend_val = Int64.of_int ((start_byte lsl 32)+(end_byte lsl 16)+1) in 
		  let zero_extend_val = Int64.of_int ((start_byte lsl 32)+(end_byte lsl 16)+0) in 
		  if (n = ai_n) then (
		    let f_type_str = "f"^(Printf.sprintf "%d" field_num)^"_type" in
		    let f_type = 
		      if not !opt_adapter_search_mode then 
			Hashtbl.find adapter_vals f_type_str
		      else self#get_fresh_symbolic f_type_str 64 in
		    let sign_extend_expr = get_ai_byte_expr n f_sz start_addr 1 in
		    let zero_extend_expr = get_ai_byte_expr n f_sz start_addr 0 in
		   
		    let else_expr' = (get_arr_t_field_expr field_num tail
			   ai_byte ai_f_sz ai_n ) in
		    let else_expr = simplify else_expr' in
		    
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
		    let f_type = 
		      if not !opt_adapter_search_mode then 
			Hashtbl.find adapter_vals f_type_str
		      else self#get_fresh_symbolic f_type_str 64 in
		    let sign_extend_expr = get_ai_byte_expr n f_sz start_addr 1 in

		    let else_expr' = (get_arr_t_field_expr field_num tail
			   ai_byte ai_f_sz ai_n ) in
		    let else_expr = simplify else_expr' in
		    
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
	    let i_n_arr = !Adapter_vars.i_n_arr' in
	    let i_byte_arr = !Adapter_vars.i_byte_arr' in
	    let unique_str = if end_of_f1 then "_f1_" else "" in
	    let rec get_arr_ite_ai_byte_expr this_array_field_ranges_l i_byte = 
		(* i_byte = interesting_byte *)
	      match this_array_field_ranges_l with
	      | [] -> from_concrete 0 8
	      | (field, start_byte, end_byte, ai_n, ai_f_sz, cond)::tail ->
		if (i_byte >= start_byte) && (i_byte <= end_byte) then (
		  let field_size_temp_str = "arr_as_t_field_"^
		    (Printf.sprintf "%s%d_n%d_sz%d_b%d_%d" unique_str field ai_n ai_f_sz 
		       (i_byte-start_byte) addr_list_ind)
		  in
		  let field_size_temp = self#get_fresh_symbolic field_size_temp_str 8 in

		  let q_exp = 
		    (try
		       Hashtbl.find field_exprs field_size_temp_str
                     with Not_found ->
		       let new_q_exp =
			 V.BinOp(V.EQ, field_size_temp,
				 (get_arr_t_field_expr field 
				    (List.rev !((i_n_arr).(ai_n))) (* array_field_ranges_l *)
				    (i_byte-start_byte) ai_f_sz ai_n )) in
		       
		       Hashtbl.replace field_exprs field_size_temp_str new_q_exp;
		       self#add_to_path_cond new_q_exp;
		       new_q_exp)
		  in

		  if !opt_trace_struct_adapter = true then
		    Hashtbl.replace t_field_h field_size_temp q_exp;
		  
		  V.Ite(cond, field_size_temp, 
			(get_arr_ite_ai_byte_expr tail i_byte ))
		) else (
		  get_arr_ite_ai_byte_expr tail i_byte 
		)
	    in
	    if !opt_time_stats then
	      (Printf.printf "%s byte expressions..." step_str;
	       flush stdout);

	    (* let upcast expr _extend_op end_sz =
	      match _extend_op with 
	      | (Some extend_op) ->  
		(match end_sz with
		| 8  -> V.Cast(extend_op, V.REG_8 , expr)
		| 16 -> V.Cast(extend_op, V.REG_16, expr)
		| 32 -> V.Cast(extend_op, V.REG_32, expr)
		| 64 -> V.Cast(extend_op, V.REG_64, expr)
		| _ -> failwith "unsupported upcast end size")
	      | None -> expr
	    in  
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
	    let byte_ce_expr_l = ref [] in
	    let get_byte_from_adapter f_num =
	      let str_gen i s = Printf.sprintf "f%d%s" i s in
	      let f_type = match Hashtbl.find adapter_vals (str_gen f_num "_type") with 
		| V.Constant(V.Int(V.REG_64, n)) -> (Int64.to_int n)
		| _ -> 0 in
	      let f_n = match Hashtbl.find adapter_vals (str_gen f_num "_n") with
		| V.Constant(V.Int(V.REG_16, n)) -> (Int64.to_int n)
		| _ -> 0 in
	      let f_size = match Hashtbl.find adapter_vals (str_gen f_num "_size") with 
		| V.Constant(V.Int(V.REG_16, n)) -> (Int64.to_int n)
		| _ -> 0 in
	      let t_s_b = f_type lsr 32 in (* target_start_byte *)
	      let t_e_b = (f_type lsr 16) land 65535 in (* target_end_byte *)
	      let t_size = (t_e_b-t_s_b+1)/f_n in
	      let cast_op = if t_size > f_size then (Some V.CAST_LOW)
		else if (f_type mod 2) = 1 then (Some V.CAST_SIGNED) 
		else if (f_type mod 2) = 0 then (Some V.CAST_UNSIGNED)
		else None in
	      if !opt_trace_struct_adapter then
		Printf.printf "parsing adapter in FM: type=%x n=%d sz=%d t_s=%d t_e=%d\n"
		  f_type f_n f_size t_s_b t_e_b;
	      for byte = 0 to (f_n*f_size)-1 do
		let i_this_entry = byte/f_size in
		let i_this_byte_within_entry = byte mod f_size in
		let t_this_entry = t_size*i_this_entry in
		let t_load_addr = Int64.add addr (Int64.of_int (t_s_b+t_this_entry)) in
		let i_this_entry_val = 
		  upcast (self#load_sym t_load_addr (t_size*8)) cast_op (f_size*8) in
		let byte_val = get_byte i_this_entry_val i_this_byte_within_entry in
		if !opt_trace_struct_adapter then
		  Printf.printf "byte_val = %s\n" (V.exp_to_string byte_val);
		byte_ce_expr_l := byte_val :: !byte_ce_expr_l;
	      done;
	    in
	    if not !opt_adapter_search_mode then (
	      for i = 1 to n_fields do
		get_byte_from_adapter i;
	      done;
	      let sz = List.length !byte_ce_expr_l in
	      for i = sz to (max_size-1) do
		let load_addr = Int64.add addr (Int64.of_int i) in
		let byte_val = self#load_sym load_addr 8 in
		byte_ce_expr_l := byte_val :: !byte_ce_expr_l;
	      done;
	      byte_ce_expr_l := (List.rev !byte_ce_expr_l)); *)
	    let byte_expr_l = ref [] in 
	    for i=0 to (max_size-1) do 
	      let byte_expr = (* if !opt_adapter_search_mode then *)
		(get_arr_ite_ai_byte_expr (List.rev !((i_byte_arr).(i))) i) 
		(* else (List.nth !byte_ce_expr_l i) *)
	      in
	      let byte_expr_sym_str = 
		"arr_ai_byte_"^(Printf.sprintf "%s%d_%d" unique_str i addr_list_ind) in
	      let byte_expr_sym = self#get_fresh_symbolic byte_expr_sym_str 8 in
	      let q_exp = V.BinOp(V.EQ, byte_expr_sym, byte_expr) in
	      if !opt_trace_struct_adapter = true then
		Printf.printf "AS#get_arr_ite_ai_byte_expr for byte %d: %s\n\n" i
		  (V.exp_to_string q_exp);
	      self#add_to_path_cond q_exp;
		(* if this is CE search, check if byte_expr has unique value *)
	      let final_byte_val = 
		if not !opt_adapter_ivc || !opt_adapter_search_mode then
		  byte_expr_sym 
		else (
		  match self#query_unique_value byte_expr_sym V.REG_8 with
		  | Some v ->
		    Printf.printf "%s has unique value %Lx\n" 
		      (V.exp_to_string byte_expr_sym) v;
		    (V.Constant(V.Int(V.REG_8, v)))
		  | None -> 
		    Printf.printf "%s does not have unique value\n" 
		      (V.exp_to_string byte_expr_sym);
		    byte_expr_sym )
	      in
	      byte_expr_l := final_byte_val :: !byte_expr_l;
	    done;
	    byte_expr_l := (List.rev !byte_expr_l);

	    if !opt_trace_struct_adapter = true then
	      Hashtbl.iter (fun key value ->
		Printf.printf "AS#apply_struct_adapter t_field_h[%s] = %s\n" 
		  (V.exp_to_string key) (V.exp_to_string value);
	      ) t_field_h; 
	    
	    for i=0 to (max_size-1) do
	      self#store_sym (Int64.add addr (Int64.of_int i)) 8 (List.nth !byte_expr_l i);
	    done;
	    
	  );
	  if end_of_f1 then e_o_f1_count := !e_o_f1_count + 1
	  else f2_init_count := !f2_init_count + 1;
      );
      if !opt_time_stats then
	(Printf.printf "AS#ready to apply (%f sec). %s\n" (Sys.time () -. start_time) step_str;
	 flush stdout); 

  end
end
