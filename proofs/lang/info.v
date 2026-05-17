From Coq Require Export ZArith.

(* Used only by the ocaml compiler *)
(** A "tag" is a non-empty type, extracted to plain OCaml [int] *)
Module Type TAG.
  Parameter t : Type.
  Parameter witness : t.
End TAG.

Module VarInfo : TAG.
  Definition t := positive.
  Definition witness : t := 1%positive.
End VarInfo.

Definition var_info := VarInfo.t.
Definition dummy_var_info : var_info := VarInfo.witness.

Class InstrInfo (instr_info : Type) : Type :=
  {
    dummy_instr_info : instr_info;
    ii_with_location : instr_info -> instr_info;
    ii_is_inline : instr_info -> bool;
    var_info_of_ii : instr_info -> var_info;
  }.

Definition instr_info_t
  {instr_info : Type} {II : InstrInfo instr_info} : Type :=
  instr_info.

(* [FunInfo] is a typeclass parameterized by the carrier types. Every section
   that needs fun_info introduces
   [Context {instr_info fun_info : Type} {CI : CompilerInfo instr_info fun_info}];
   the implementation supplies the record fields directly. *)
Class FunInfo (instr_info fun_info : Type) : Type :=
  {
    entry_info_of_fun_info : fun_info -> instr_info;
    ret_info_of_fun_info : fun_info -> instr_info;
  }.

Class CompilerInfo (instr_info fun_info : Type) : Type :=
  {
    ci_instr_info :> InstrInfo instr_info;
    ci_fun_info :> FunInfo instr_info fun_info;
  }.

#[global] Existing Instance ci_instr_info.
#[global] Existing Instance ci_fun_info.

(* Used to force typeclass dependency to allow inference. *)
Definition fun_info_t
  {instr_info fun_info : Type}
  {CI : CompilerInfo instr_info fun_info} : Type :=
  fun_info.
