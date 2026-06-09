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
  x86_decl
  x86_extra
  x86_instr_decl.

Section REGISTER_ZEROIZATION.

Context {atoI : arch_toIdent}.

Definition x86_zeroize_var
  (err_register : var -> pp_error_loc) (x : var) : cexec fopn_args :=
  if vtype x is aword ws then
    let: (op, es) :=
      if (ws <= U64)%CMP then (Ox86 (MOV ws), [:: Rexpr (fconst ws 0)])
      else (Oasm (ExtOp (Oset0 ws)), [::])
    in
    ok ([:: LLvar (mk_var_i x) ], op, es)
  else Error (err_register x).

Definition x86_zeroize_flags
  (err_flags : pp_error_loc) (ox : option var) : cexec (seq fopn_args) :=
  if ox is Some x then
    let e := rvar (mk_var_i x) in
    let lflags := [seq LLvar (mk_var_i (to_var f)) | f <- rflags ] in
    ok [:: (lflags, Ox86 (CMP reg_size), [:: e; e ]) ]
  else Error err_flags.

Definition x86_rzparams : register_zeroization_params :=
  {|
    rz_cmd_args :=
      fun _ => naive_rz_cmd_args x86_zeroize_var x86_zeroize_flags;
  |}.

End REGISTER_ZEROIZATION.
