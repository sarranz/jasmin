Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq eqtype.

Require Import
  compiler_util
  expr
  fexpr
  linear
  one_varmap
  register_zeroization
  register_zeroization_utils.
Require Import
  arch_decl
  arch_extra.
Require Import
  riscv_decl
  riscv_extra
  riscv_instr_decl
  riscv_params_common.

Section REGISTER_ZEROIZATION.

Context {atoI : arch_toIdent}.

Definition riscv_zeroize_var
  (err_register : var -> pp_error_loc) (x : var) : cexec fopn_args :=
  if vtype x is aword U32 then ok (RISCVFopn.li (mk_var_i x) 0)
  else Error (err_register x).

Definition riscv_zeroize_flags
  (err_flags : pp_error_loc) (ox : option var) : cexec (seq fopn_args) :=
  if ox is Some _ then ok [::] else Error err_flags.

Definition riscv_rzparams : register_zeroization_params :=
  {|
    rz_cmd_args :=
      fun _ => naive_rz_cmd_args riscv_zeroize_var riscv_zeroize_flags;
  |}.

End REGISTER_ZEROIZATION.
