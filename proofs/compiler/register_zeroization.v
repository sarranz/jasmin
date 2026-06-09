(* Register zeroization.

   This pass zeroizes all registers (normal, extra registers, and flags) at
   the end of export functions.  Architecture-specific code is used. *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From mathcomp Require Import ssreflect ssrfun ssrbool.

Require Import
  expr
  linear
  linear_util
  one_varmap
  sopn
  utils.
Require Import compiler_util.
Require Export register_zeroization_mode.

Module E.

  Definition pass : string := "register zeroization".

  Definition internal_error msg : pp_error_loc :=
    {|
      pel_msg      := msg;
      pel_fn       := None;
      pel_fi       := None;
      pel_ii       := None;
      pel_vi       := None;
      pel_pass     := Some pass;
      pel_internal := true;
    |}.

  Definition cant_zeroize_flags : pp_error_loc :=
    internal_error (pp_s "can't zeroize flags").

  Definition cant_zeroize_register (x : var) : pp_error_loc :=
    internal_error
      (pp_box [:: pp_s "can't zeroize register"; pp_var x]).

  Definition res_has_bool : pp_error_loc :=
    internal_error (pp_s "result has boolean type").

End E.

(* -------------------------------------------------------------------- *)
(* Architecture-specific parameters. *)

Section REGISTER_ZEROIZATION_PARAMS.

Context
  {asm_op : Type}
  {asmop : asmOp asm_op}.

Record register_zeroization_params :=
  {
    (* [rz_cmd_args rzm xs err_flags err_reg] returns zeroization
       instructions for mode [rzm], excluding result variables [xs].
       It is parametric over the one_varmap instance (callee-saved
       set) so that [register_zeroization_params] itself does not
       need to be parametric over the calling convention. *)
    rz_cmd_args :
      forall {ovmi : one_varmap_info},
      rzmode ->
      seq var ->
      pp_error_loc ->
      (var -> pp_error_loc) ->
      cexec (seq fopn_args);
  }.

End REGISTER_ZEROIZATION_PARAMS.

(* -------------------------------------------------------------------- *)
Section WITH_PARAMS.

Context
  {asm_op : Type}
  {asmop : asmOp asm_op}
  {ovmi : one_varmap_info}
  (rzm_of_fn : funname -> rzmode)
  (rzparams  : register_zeroization_params)
.

Definition rz_cmd (rzm : rzmode) (lfd : lfundef) : cexec lcmd :=
  let vars := map v_var (lfd_res lfd) in
  Let _ :=
    assert (all (fun x => ~~ is_abool (vtype x)) vars) E.res_has_bool
  in
  Let args :=
    rz_cmd_args rzparams rzm vars E.cant_zeroize_flags E.cant_zeroize_register
  in
  ok (map (li_of_fopn_args dummy_instr_info) args).

Definition register_zeroization_lfd
  (fn : funname) (lfd : lfundef) : cexec lfundef :=
  if lfd_export lfd then
    Let c := rz_cmd (rzm_of_fn fn) lfd in
    ok (map_lfundef (fun b => b ++ c) lfd)
  else ok lfd.

Definition register_zeroization_lprog (lp : lprog) : cexec lprog :=
  Let fs := map_cflprog_name register_zeroization_lfd (lp_funcs lp) in
  ok
    {|
      lp_rip := lp_rip lp;
      lp_rsp := lp_rsp lp;
      lp_globs := lp_globs lp;
      lp_glob_names := lp_glob_names lp;
      lp_funcs := fs;
    |}.

End WITH_PARAMS.
