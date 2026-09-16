open Jasmin
open SafetyArch
open Acc_decl

(* TODO_ACC all of these are dummies *)

module Acc_safety
    (A :
      Arch_full.Arch
        with type reg = register
         and type regx = Arch_utils.empty
         and type xreg = wide_register
         and type rflag = Acc_decl.rflag
         and type cond = condition
         and type asm_op = Acc_instr_decl.acc_op
         and type extra_op = Acc_extra.extra_op) :
  SafetyArch
    with type reg = Acc_decl.register
     and type regx = Arch_utils.empty
     and type xreg = wide_register
     and type rflag = Acc_decl.rflag
     and type cond = condition
     and type asm_op = Acc_instr_decl.acc_op
     and type extra_op = Acc_extra.extra_op = struct
  include A

  let is_comparison _ = false
  let is_conditional _ _ _ _ = None

  let split_asm_opn n _opn _es =
    (* Default: all outputs are unknown (Top) *)
    List.init n (fun _ -> None)

  let post_opn _opn _lvs _es = []
  let opn_heur _opn _v _es = None
end
