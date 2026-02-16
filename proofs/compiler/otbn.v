From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssralg.
From Coq Require Import ZArith.

Require Import utils word.
Require Import
  arch_decl
  arch_utils.
Require Import
  otbn_decl
  otbn_instr_decl.
Require riscv.

Definition eval_cond
  (getr : register -> u32)
  (getf : rflag -> exec bool)
  (c : condition) :
  exec bool :=
  match c with
  | RVcond is_eq r0 r1 =>
      let w0 := riscv.sem_cond_arg getr r0 in
      let w1 := riscv.sem_cond_arg getr r1 in
      ok (if is_eq then w0 == w1 else w0 != w1)
  | BNcond f => getf f
  end.

#[export]
Instance otbn : asm register empty wide_register rflag condition otbn_op :=
  {
    eval_cond := eval_cond;
  }.
