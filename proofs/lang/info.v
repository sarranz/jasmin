From Coq Require Export ZArith.

(* Used only by the ocaml compiler *)
(** A “tag” is a non-empty type, extracted to plain OCaml [int] *)
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

Module Type InstrInfoT <: TAG.
  Include TAG.
  Parameter with_location : t -> t.
  Parameter is_inline : t -> bool.
  Parameter var_info_of_ii : t -> var_info.
End InstrInfoT.

Module InstrInfo : InstrInfoT.
  Definition t := positive.
  Definition witness : t := 1%positive.
  Definition with_location (ii : t) := ii.
  Definition is_inline (_ : t) : bool := false.
  Definition var_info_of_ii (_ : t) : var_info := dummy_var_info.
End InstrInfo.

Definition instr_info := InstrInfo.t.
Definition dummy_instr_info : instr_info := InstrInfo.witness.
Definition ii_with_location (ii : instr_info) : instr_info :=
  InstrInfo.with_location ii.
Definition ii_is_inline (ii : instr_info) : bool := InstrInfo.is_inline ii.
Definition var_info_of_ii (ii : instr_info) : var_info := InstrInfo.var_info_of_ii ii.

(* [FunInfo] used to be a sealed module with a [t : Type] field and two
   [instr_info]-valued projections. It is now a typeclass parameterized by the
   carrier type. Every section that needs to talk about fun_info introduces
   [Context {fun_info : Type} {FI : FunInfo fun_info}]; the implementation
   (currently in [compiler/src/fInfo.ml] for the extracted compiler) supplies
   the record fields directly. *)
Class FunInfo (fun_info : Type) : Type := {
  entry_info_of_fun_info : fun_info -> instr_info;
  ret_info_of_fun_info   : fun_info -> instr_info;
}.

(* Used to force typeclass dependency to allow inference. *)
Definition fun_info_t {fun_info : Type} {FI : FunInfo fun_info} := fun_info.
