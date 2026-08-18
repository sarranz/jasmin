(* ARMv8A architecture full integration *)
open Arch_decl

module type Armv8a_input = sig
  val call_conv : (Armv8a_decl.register, Arch_utils.empty, Arch_utils.empty, Arm_common.rflag, Arm_common.condt) calling_convention
end

(* Create arch_toIdent for ARMv8A *)
let atoI armv8a_decl =
  let open Prog in
  let mk_var k t s =
    V.mk s (Reg(k,Direct)) (Conv.ty_of_cty (Type.atype_of_ltype t)) L._dummy [] in
  match Arch_extra.MkAToIdent.mk armv8a_decl mk_var with
  | Utils0.Error e ->
      let e = Conv.error_of_cerror (Printer.pp_err ~debug:true) e in
      raise (Utils.HiError e)
  | Utils0.Ok atoI -> atoI

module Armv8a (Lowering_params : Armv8a_input) = struct
  module AD = Armv8a_decl

  type reg = AD.register
  type regx = Arch_utils.empty
  type xreg = Arch_utils.empty
  type nonrec rflag = Arm_common.rflag
  type cond = Arm_common.condt
  type asm_op = Armv8a_instr_decl.armv8a_asm_op
  type extra_op = Armv8a_extra.armv8a_extra_op

  let atoI = atoI AD.armv8a_decl

  let asm_e = Armv8a_extra.armv8a_extra atoI

  let aparams = Armv8a_params.armv8a_params atoI

  let known_implicits = ["NF", "_nf_"; "ZF", "_zf_"; "CF", "_cf_"; "VF", "_vf_"]

  let alloc_stack_need_extra _ = false

  let is_ct_asm_op (o : asm_op) =
    match o with
    | Armv8a_instr_decl.ARMv8A_op ((Armv8a_instr_decl.SDIV | Armv8a_instr_decl.UDIV), _) -> false
    | _ -> true

  let is_ct_asm_extra (_o : extra_op) = true

  let not_saved_stack = []

  let pp_shift_kind fmt = function
    | Shift_kind.SLSL -> ToRocq.pp_bare fmt "SLSL"
    | SLSR -> ToRocq.pp_bare fmt "SLSR"
    | SASR -> ToRocq.pp_bare fmt "SASR"
    | SROR -> ToRocq.pp_bare fmt "SROR"

  let pp_armv8a_options fmt (o : Armv8a_instr_decl.armv8a_options) =
    Format.fprintf fmt "{| has_shift := (%a); opts_size := %a |}"
      (ToRocq.pp_rocq_option pp_shift_kind)
      o.has_shift ToRocq.pp_wsize o.opts_size

  let pp_armv8a_mnemonic fmt (m : Armv8a_instr_decl.armv8a_mnemonic) =
    let open Armv8a_instr_decl in
    match m with
    | ADD -> ToRocq.pp_bare fmt "ADD"
    | ADDS -> ToRocq.pp_bare fmt "ADDS"
    | ADC -> ToRocq.pp_bare fmt "ADC"
    | ADCS -> ToRocq.pp_bare fmt "ADCS"
    | SUB -> ToRocq.pp_bare fmt "SUB"
    | SUBS -> ToRocq.pp_bare fmt "SUBS"
    | NEG -> ToRocq.pp_bare fmt "NEG"
    | MUL -> ToRocq.pp_bare fmt "MUL"
    | MADD -> ToRocq.pp_bare fmt "MADD"
    | MSUB -> ToRocq.pp_bare fmt "MSUB"
    | SDIV -> ToRocq.pp_bare fmt "SDIV"
    | UDIV -> ToRocq.pp_bare fmt "UDIV"
    | AND -> ToRocq.pp_bare fmt "AND"
    | ORR -> ToRocq.pp_bare fmt "ORR"
    | EOR -> ToRocq.pp_bare fmt "EOR"
    | MVN -> ToRocq.pp_bare fmt "MVN"
    | ASR -> ToRocq.pp_bare fmt "ASR"
    | LSL -> ToRocq.pp_bare fmt "LSL"
    | LSR -> ToRocq.pp_bare fmt "LSR"
    | ROR -> ToRocq.pp_bare fmt "ROR"
    | MOV -> ToRocq.pp_bare fmt "MOV"
    | MOVN -> ToRocq.pp_bare fmt "MOVN"
    | MOVZ -> ToRocq.pp_bare fmt "MOVZ"
    | MOVK -> ToRocq.pp_bare fmt "MOVK"
    | ADR -> ToRocq.pp_bare fmt "ADR"
    | SXTB -> ToRocq.pp_bare fmt "SXTB"
    | SXTH -> ToRocq.pp_bare fmt "SXTH"
    | SXTW -> ToRocq.pp_bare fmt "SXTW"
    | UXTB -> ToRocq.pp_bare fmt "UXTB"
    | UXTH -> ToRocq.pp_bare fmt "UXTH"
    | UXTW -> ToRocq.pp_bare fmt "UXTW"
    | CMP -> ToRocq.pp_bare fmt "CMP"
    | TST -> ToRocq.pp_bare fmt "TST"
    | CSEL -> ToRocq.pp_bare fmt "CSEL"
    | LDR -> ToRocq.pp_bare fmt "LDR"
    | LDRB -> ToRocq.pp_bare fmt "LDRB"
    | LDRH -> ToRocq.pp_bare fmt "LDRH"
    | LDRSB -> ToRocq.pp_bare fmt "LDRSB"
    | LDRSH -> ToRocq.pp_bare fmt "LDRSH"
    | LDRSW -> ToRocq.pp_bare fmt "LDRSW"
    | STR -> ToRocq.pp_bare fmt "STR"
    | STRB -> ToRocq.pp_bare fmt "STRB"
    | STRH -> ToRocq.pp_bare fmt "STRH"

  let pp_asm_op_for_rocq fmt (o : asm_op) =
    let (Armv8a_instr_decl.ARMv8A_op (m, opts)) = o in
    Format.fprintf fmt "(ARMv8A_op %a %a)" pp_armv8a_mnemonic m
      pp_armv8a_options opts

  let pp_extra_op_for_rocq fmt (o : extra_op) =
    let open Armv8a_extra in
    match o with
    | Oarmv8a_swap ws -> ToRocq.pp_with_ws fmt "Oarmv8a_swap" ws
    | Oarmv8a_add_large_imm -> ToRocq.pp_bare fmt "Oarmv8a_add_large_imm"
    | Oarmv8a_smart_li ws -> ToRocq.pp_with_ws fmt "Oarmv8a_smart_li" ws

  let pp_asm = Pp_arm_v8a.print_prog

  let callstyle = Arch_full.ByReg { call = Some Armv8a_decl.R30; return = true }

  (* SP must stay 16-byte aligned: SP alignment checking, Arm ARM
     DDI0487M.a, D1.4.10.2 (see also the AAPCS64 stack constraints). *)
  let sp_min_align = Wsize.U128

  (* One X-register store; SIMD (NEON) stores would raise this to u128. *)
  let max_store_size = Wsize.U64

  let internal_call_conv = Armv8a_decl.armv8a_internal_call_conv

  include Lowering_params
end
