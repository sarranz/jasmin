open Arch_decl
open Acc_decl

module type ACC_input = sig
  val call_conv :
    ( register,
      Arch_utils.empty,
      wide_register,
      rflag,
      condition )
    calling_convention
end

module ACC_core = struct
  type reg = register
  type regx = Arch_utils.empty
  type xreg = wide_register
  type rflag = Acc_decl.rflag
  type cond = condition
  type asm_op = Acc_instr_decl.acc_op
  type extra_op = Acc_extra.extra_op

  let arch = Utils.ACC

  (* TODO_ACC why is this in x86? *)
  let atoI = X86_arch_full.atoI acc_decl
  let asm_e = Acc_extra.acc_extra atoI
  let aparams = Acc_params.acc_params atoI

  (* ACC has two flag groups (FG0, FG1), each with carry/MSB/LSB/zero flags.
     The keys must match the flag identifiers (flag_to_string in acc_decl.v),
     which are group-qualified ("CF0", "CF1", ...). *)
  let known_implicits =
    [ ("CF0", "_cf0_"); ("MF0", "_mf0_"); ("LF0", "_lf0_"); ("ZF0", "_zf0_")
    ; ("CF1", "_cf1_"); ("MF1", "_mf1_"); ("LF1", "_lf1_"); ("ZF1", "_zf1_") ]

  let alloc_stack_need_extra sz =
    not (Acc_params_core.is_arith_small (Conv.cz_of_z sz))

  (* TODO_ACC: check *)
  let is_ct_asm_op (_o : asm_op) = true

  (* TODO_ACC: check *)
  let is_ct_asm_extra (_o : extra_op) = true

  (* TODO_ACC: check *)
  let is_doit_asm_op (_o : asm_op) = true

  (* TODO_ACC: check *)
  let is_doit_asm_extra (_o : extra_op) = true

end

module ACC (Input : ACC_input) :
  Arch_full.Core_arch
    with type reg = register
     and type regx = Arch_utils.empty
     and type xreg = wide_register
     and type rflag = Acc_decl.rflag
     and type cond = condition
     and type asm_op = Acc_instr_decl.acc_op
     and type extra_op = Acc_extra.extra_op = struct
  include ACC_core
  include Input

  let not_saved_stack = (Acc_params.liparams atoI).lip_not_saved_stack
  let pp_asm = Pp_acc.print_prog

  let callstyle = Arch_full.OnHWStack
  let sp_min_align = Wsize.U8

  (* BN.SD stores a full wide (256-bit) register in one instruction. *)
  let max_store_size = Wsize.U256

  let internal_call_conv = Acc_decl.internal_call_conv
end
