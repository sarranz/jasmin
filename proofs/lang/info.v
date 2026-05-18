From Coq Require Export ZArith.
From mathcomp Require Import ssreflect.

Class VarInfo (var_info : Type) : Type :=
  {
    dummy_var_info : var_info;
  }.

(* Used to force typeclass dependency. *)
Definition var_info_t {var_info : Type} {VI : VarInfo var_info} : Type :=
  var_info.

Section IINFO.

Context {var_info : Type} {VI : VarInfo var_info}.

Class InstrInfo (instr_info : Type) : Type :=
  {
    dummy_instr_info : instr_info;
    ii_with_location : instr_info -> instr_info;
    ii_is_inline : instr_info -> bool;
    var_info_of_ii : instr_info -> var_info_t;
  }.

End IINFO.

(* Used to force typeclass dependency. *)
Definition instr_info_t
  {var_info instr_info : Type}
  {VI : VarInfo var_info}
  {II : InstrInfo instr_info} :
  Type :=
  instr_info.

Section FINFO.

Context
  {var_info instr_info : Type}
  {VI : VarInfo var_info}
  {II : InstrInfo instr_info}
.

Class FunInfo (fun_info : Type) : Type :=
  {
    entry_info_of_fun_info : fun_info -> instr_info_t;
    ret_info_of_fun_info : fun_info -> instr_info_t;
  }.

End FINFO.

(* Used to force typeclass dependency. *)
Definition fun_info_t
  {var_info instr_info fun_info : Type}
  {VI : VarInfo var_info}
  {II : InstrInfo instr_info}
  {FI : FunInfo fun_info} :
  Type :=
  fun_info.

Class CompilerInfo (var_info instr_info fun_info : Type) : Type :=
  {
    ci_var_info :> VarInfo var_info;
    ci_instr_info :> InstrInfo instr_info;
    ci_fun_info :> FunInfo fun_info;
  }.

#[global] Existing Instance ci_var_info.
#[global] Existing Instance ci_instr_info.
#[global] Existing Instance ci_fun_info.
