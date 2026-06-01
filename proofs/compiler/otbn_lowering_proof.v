From mathcomp Require Import ssreflect ssrfun ssrbool eqtype order ssralg.
Import
  Order.POrderTheory
  Order.TotalTheory.
From mathcomp Require Import word_ssrZ.

Require Import
  compiler_util
  expr
  lowering
  lowering_lemmas
  psem
  utils.
Require Import
  arch_extra
  sem_params_of_arch_extra.
Require Import
  otbn_decl
  otbn_extra
  otbn_instr_decl
  otbn_lowering.

Set SsrOldRewriteGoalsOrder.  (* change Set to Unset when porting the file, then remove the line when requiring MathComp >= 2.6 *)

Section PROOF.

Context
  {wsw : WithSubWord}
  {dc : DirectCall}
  {atoI : arch_toIdent}
  {syscall_state : Type}
  {sc_sem : syscall_sem syscall_state}
  {pT : progT}
  {sCP : semCallParams}
  (p : prog)
  (ev : extra_val_t)
  (options : lowering_options)
  (warning : instr_info -> warning_msg -> instr_info)
  (fv : lowering.fresh_vars).

Notation lower_cmd :=
  (lower_cmd
     (fun _ _ _ => lower_i)
     options
     warning
     fv).
Notation lower_prog :=
  (lower_prog
     (fun _ _ _ => lower_i)
     options
     warning
     fv).

Notation p' := (lower_prog p).

(* -------------------------------------------------------------------- *)

Section SEM.

Lemma lower_callP
  (f : funname) scs mem scs' mem' (va vr : seq value) :
  sem_call p ev scs mem f va scs' mem' vr
  -> sem_call (lower_prog p) ev scs mem f va scs' mem' vr.
Proof.
Admitted.

End SEM.

Section IT.

Context {E E0: Type -> Type} {wE : with_Error E E0} {rE0 : EventRels E0}.

Lemma it_lower_callP fn :
  wiequiv_f p p' ev ev (rpreF (eS:= eq_spec)) fn fn (rpostF (eS:=eq_spec)).
Proof.
Admitted.

End IT.

End PROOF.
