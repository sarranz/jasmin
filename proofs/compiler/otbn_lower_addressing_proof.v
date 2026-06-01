(* ** Imports and settings *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.
From mathcomp Require Import ssralg.

Require Import psem psem_facts compiler_util.

Require Import
  arch_decl
  arch_extra
  sem_params_of_arch_extra
  otbn_instr_decl
  otbn_decl
  otbn
  otbn_extra.

Require Export otbn_lower_addressing.

Set SsrOldRewriteGoalsOrder.  (* change Set to Unset when porting the file, then remove the line when requiring MathComp >= 2.6 *)

(* ** proofs
 * -------------------------------------------------------------------- *)

Section WITH_PARAMS.

Context
  {wsw : WithSubWord}
  {dc : DirectCall}
  {atoI : arch_toIdent}
  {syscall_state : Type}
  {sc_sem : syscall_sem syscall_state}.

Context (fresh_reg : string -> atype -> Ident.ident).

Context (p p' : sprog).

Hypothesis ok_p' : lower_addressing_prog fresh_reg p = ok p'.

Context (ev : extra_val_t (progT := progStack)).

Lemma lower_addressing_prog_invariants :
  p.(p_globs) = p'.(p_globs) /\ p.(p_extra) = p'.(p_extra).
Proof.
  move: ok_p'; rewrite /lower_addressing_prog.
  by t_xrbindP=> _ _ <- /=.
Qed.

Lemma lower_addressing_fd_invariants :
  forall fn fd,
  get_fundef p.(p_funcs) fn = Some fd ->
  exists2 fd',
    get_fundef p'.(p_funcs) fn = Some fd' &
    [/\ fd.(f_info) = fd'.(f_info),
        fd.(f_tyin) = fd'.(f_tyin),
        fd.(f_params) = fd'.(f_params),
        fd.(f_tyout) = fd'.(f_tyout),
        fd.(f_res) = fd'.(f_res) &
        fd.(f_extra) = fd'.(f_extra)].
Proof.
  move=> fn fd get_fd.
  move: ok_p'; rewrite /lower_addressing_prog.
  t_xrbindP=> funcs ok_funcs <-.
  have [fd' ok_fd' get_fd'] := get_map_cfprog_gen ok_funcs get_fd.
  exists fd' => //.
  move: ok_fd'; rewrite /lower_addressing_fd.
  by t_xrbindP=> _ _ <- /=.
Qed.

(* TODO_OTBN: prove.  Mirrors [riscv_lower_addressing_proof.lower_addressing_progP].
   The pass replaces a scalar global access [v = [rip + disp]] with the pair
   [tmp = LA (rip + disp); v = [tmp]].  Semantics are preserved: [tmp] is a
   fresh register (checked in [lower_addressing_fd]) holding the same address
   value that [LA] computes, so the subsequent load reads the same cell. *)
Lemma lower_addressing_progP scs mem f va scs' mem' vr:
  sem_call (pT := progStack) p ev scs mem f va scs' mem' vr ->
  sem_call (pT := progStack) p' ev scs mem f va scs' mem' vr.
Proof. Admitted.

Section IT.

Context {E E0: Type -> Type} {wE : with_Error E E0} {rE0 : EventRels E0}.

(* TODO_OTBN: prove.  Interaction-trees counterpart of [lower_addressing_progP],
   mirroring [riscv_lower_addressing_proof.it_lower_addressing_progP]. *)
Lemma it_lower_addressing_progP fn:
  wiequiv_f (scP1 := sCP_stack) (scP2 := sCP_stack)
    p p' ev ev (rpreF (eS:=eq_spec)) fn fn (rpostF (eS:=eq_spec)).
Proof. Admitted.

End IT.

End WITH_PARAMS.
