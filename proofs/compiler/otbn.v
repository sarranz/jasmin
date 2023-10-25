From mathcomp Require Import
  all_ssreflect
  all_algebra.

Require Import utils values.
Require Import arch_decl.
Require Import
  otbn_decl
  otbn_instr_decl.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Definition eval_cond
  (get : asm_typed_reg -> values.value)
  (c : condition) :
  exec bool :=
  match c with
  | RVcond is_eq r0 r1 =>
      let getr x := to_word reg_size (get (ARReg x)) in
      Let w0 := getr r0 in
      Let w1 := getr r1 in
      ok (if is_eq then w0 == w1 else w0 != w1)
  | BNcond f => to_bool (get (ABReg f))
  end.

#[export]
Instance otbn :
  asm register register_ext wide_register flag condition otbn_op :=
  {
    eval_cond := eval_cond;
  }.
