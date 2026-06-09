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
  arm_decl
  arm_extra
  arm_instr_decl
  arm_params_common.

Section REGISTER_ZEROIZATION.

Context {atoI : arch_toIdent}.

Definition arm_zeroize_var
  (err_register : var -> pp_error_loc) (x : var) : cexec fopn_args :=
  if vtype x is aword U32 then ok (ARMFopn.movi (mk_var_i x) 0)
  else Error (err_register x).

Definition arm_zeroize_flags
  (err_flags : pp_error_loc) (ox : option var) : cexec (seq fopn_args) :=
  if ox is Some x then
    let e := rvar (mk_var_i x) in
    let lflags := [seq LLvar (mk_var_i (to_var f)) | f <- rflags ] in
    ok [:: (lflags, Oarm (ARM_op CMP default_opts), [:: e; e ]) ]
  else Error err_flags.

Definition arm_rzparams : register_zeroization_params :=
  {|
    rz_cmd_args :=
      fun _ => naive_rz_cmd_args arm_zeroize_var arm_zeroize_flags;
  |}.

End REGISTER_ZEROIZATION.
