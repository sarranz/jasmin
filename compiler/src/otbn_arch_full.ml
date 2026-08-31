open Arch_decl
open Otbn_decl

module type OTBN_input = sig
  val call_conv :
    ( register,
      Arch_utils.empty,
      wide_register,
      rflag,
      condition )
    calling_convention
end

module OTBN_core = struct
  type reg = register
  type regx = Arch_utils.empty
  type xreg = wide_register
  type rflag = Otbn_decl.rflag
  type cond = condition
  type asm_op = Otbn_instr_decl.otbn_op
  type extra_op = Otbn_extra.extra_op

  let arch = Utils.OTBN

  (* TODO_OTBN why is this in x86? *)
  let atoI = X86_arch_full.atoI otbn_decl
  let asm_e = Otbn_extra.otbn_extra atoI
  let aparams = Otbn_params.otbn_params atoI

  (* OTBN has two flag groups (FG0, FG1), each with carry/MSB/LSB/zero flags.
     The keys must match the flag identifiers (flag_to_string in otbn_decl.v),
     which are group-qualified ("CF0", "CF1", ...). *)
  let known_implicits =
    [ ("CF0", "_cf0_"); ("MF0", "_mf0_"); ("LF0", "_lf0_"); ("ZF0", "_zf0_")
    ; ("CF1", "_cf1_"); ("MF1", "_mf1_"); ("LF1", "_lf1_"); ("ZF1", "_zf1_") ]

  let alloc_stack_need_extra sz =
    not (Otbn_params_core.is_arith_small (Conv.cz_of_z sz))

  (* TODO_OTBN: check *)
  let is_ct_asm_op (_o : asm_op) = true

  (* TODO_OTBN: check *)
  let is_ct_asm_extra (_o : extra_op) = true

  (* TODO_OTBN: check *)
  let is_doit_asm_op (_o : asm_op) = true

  (* TODO_OTBN: check *)
  let is_doit_asm_extra (_o : extra_op) = true

end

module OTBN (Input : OTBN_input) :
  Arch_full.Core_arch
    with type reg = register
     and type regx = Arch_utils.empty
     and type xreg = wide_register
     and type rflag = Otbn_decl.rflag
     and type cond = condition
     and type asm_op = Otbn_instr_decl.otbn_op
     and type extra_op = Otbn_extra.extra_op = struct
  include OTBN_core
  include Input

  let not_saved_stack = (Otbn_params.liparams atoI).lip_not_saved_stack
  let pp_asm = Pp_otbn.print_prog

  let callstyle = Arch_full.OnHWStack
  let sp_min_align = Wsize.U8
  let internal_call_conv = Otbn_decl.internal_call_conv
end
