(* ** Imports and settings *)
From mathcomp Require Import ssreflect ssrfun ssrbool seq ssralg eqtype.
From Coq Require Import ZArith.

From ITree Require Import Basics ITree ITreeFacts Exception.
Import Basics.Monads.

Require Export utils syscall wsize word type low_memory sem_type values.
Require Import it_sems_core_defs core_logics.
Require Import xrutt xrutt_facts rutt_extras.

Local Open Scope Z_scope.

Import MonadNotation ITreeNotations.
Local Open Scope monad_scope.

Section SourceSysCall.

Context
  {pd: PointerData}
  {syscall_state : Type}
  {E0 E : Type -> Type}
  {wE : with_Error E E0}
  {rE : with_RndEvent syscall_state E}
.

Implicit Types
  (scs : syscall_state)
  (len : Z)
  (vs : values)
.

Definition exec_getrandom_u scs len vs : itree E (syscall_state * values) :=
  iassert (if vs is [:: v] then is_ok (to_arr len v) else false) ErrType ;;
  '(scs', bs) <- trigger (Rnd scs len) ;;
  a <- iresult (WArray.fill len bs) ;;
  Ret (scs', [:: Varr a]).

Definition exec_syscall_u
  scs (m : mem) (o : syscall_t) vs : itree E (syscall_state * mem * values) :=
  match o with
  | RandomBytes ws n =>
      let len := arr_size ws n in
      '(scs', vs') <- exec_getrandom_u scs len vs ;;
      Ret (scs', m, vs')
  end.

Definition sc_res_uincl (r1 r2 : syscall_state * mem * values) : Prop :=
  let '(scs1, m1, vres1) := r1 in
  let '(scs2, m2, vres2) := r2 in
  [/\ scs1 = scs2, m1 = m2 & values_uincl vres1 vres2].

Lemma exec_syscallPu_eutt scs m o vargs vargs' :
  values_uincl vargs vargs' ->
  eutt sc_res_uincl
    (exec_syscall_u scs m o vargs)
    (exec_syscall_u scs m o vargs').
Proof.
rewrite /exec_syscall_u /exec_getrandom_u; case: o => [ws p].
case: vargs vargs' => [|va [|? vargs]] [|va' [|? vargs']] /List_Forall2_inv //=.
- by move=> _; rewrite !bind_throw; apply: eqit_throw.
- move=> [+ _].
  case ha: (to_arr _ va) => [a|e]; last first.
  + move=> /value_uincl_to_arr_err /(_ ha) ->.
    by rewrite !bind_throw; apply: eqit_throw.
  move=> /val_uincl_of_val /(_ ha) [/= a' -> {}ha].
  rewrite !bind_ret_l !bind_bind; apply: eutt_eq_bind => -[scs' bs].
  rewrite !bind_bind; apply: eutt_eq_bind => b.
  by rewrite !bind_ret_l; apply eutt_Ret.
- by move=> [_ /List_Forall2_inv].
- by move=> [_ /List_Forall2_inv].
by move=> _; rewrite !bind_throw; apply: eqit_throw.
Qed.

Lemma exec_syscallPu scs m o vargs vargs' :
  values_uincl vargs vargs' ->
  lxeutt sc_res_uincl
    (exec_syscall_u scs m o vargs)
    (exec_syscall_u scs m o vargs').
Proof using. move=> h; apply: eutt_lxeutt; exact: exec_syscallPu_eutt. Qed.

Definition mem_equiv m1 m2 := stack_stable m1 m2 /\ validw m1 =3 validw m2.

Lemma exec_syscallSu scs m o vargs :
  lutt (fun _ _ => True) (fun _ _ _ => True)
    (fun '(_, m', _) => mem_equiv m m')
    (exec_syscall_u scs m o vargs).
Proof.
case: o => [ws p].
apply: lutt_bind; first exact: lutt_true.
by move=> [??] _; apply/lutt_Ret'.
Qed.

End SourceSysCall.

Section StackSyscall.

Context
  {pd : PointerData}
  {syscall_state : Type}
  {E0 E : Type -> Type}
  {wE : with_Error E E0}
  {rE : with_RndEvent syscall_state E}
.

Implicit Types
  (o : syscall_t)
  (scs : syscall_state)
  (m : mem)
  (p : pointer)
  (len : pointer)
.

Definition sc_sig_s_atype_in o :=
  [seq eval_atype t | t <- (syscall_sig_s o).(scs_tin)].
Definition sc_sig_s_atype_out o :=
  [seq eval_atype t | t <- (syscall_sig_s o).(scs_tout)].
Definition sc_sig_s_atype o :=
  it_sem_prod (E := E)
    (sc_sig_s_atype_in o)
    (syscall_state * mem * sem_tuple (sc_sig_s_atype_out o)).

Lemma syscall_sig_s_noarr o : all is_not_carr (sc_sig_s_atype_in o).
Proof. by case: o. Qed.

Definition exec_getrandom_s_core
  scs m p len : itree E (syscall_state * mem * pointer) :=
  let len := wunsigned len in
  '(scs', bs) <- trigger (Rnd scs len) ;;
  m' <- iresult (fill_mem m p bs) ;;
  Ret (scs', m', p).

Definition sem_syscall
  (o : syscall_t) : syscall_state -> mem -> sc_sig_s_atype o :=
  match o with
  | RandomBytes _ _ => exec_getrandom_s_core
  end.

Definition exec_syscall_s scs m o vs : itree E (syscall_state * mem * values) :=
  '(scs', m', t) <- it_app_sopn _ (sem_syscall o scs m) vs ;;
  Ret (scs', m', list_ltuple t).

Lemma exec_getrandom_s_core_stable scs m p len :
  lutt (fun _ _ => True) (fun _ _ _ => True)
    (fun '(_, m', _) => stack_stable m m')
    (exec_getrandom_s_core scs m p len).
Proof.
apply: lutt_bind; first exact: lutt_true.
move=> [scs' bs] _; apply: (lutt_bind (R := stack_stable m)).
- by apply: lutt_iresult => // m' /fill_mem_stack_stable.
by move=> m' h; apply/lutt_Ret'/h.
Qed.

Lemma exec_getrandom_s_core_validw scs m p len :
  lutt (fun _ _ => True) (fun _ _ _ => True)
    (fun '(_, m', _) => validw m =3 validw m')
    (exec_getrandom_s_core scs m p len).
Proof.
apply: lutt_bind; first exact: lutt_true.
move=> [scs' bs] _; apply: (lutt_bind (R := fun m' => validw m =3 validw m')).
- by apply: lutt_iresult => // m' /fill_mem_validw_eq.
by move=> m' h; apply/lutt_Ret'/h.
Qed.

Lemma exec_syscallPs_eq scs m o vargs vargs' :
  values_uincl vargs vargs' ->
  lxeutt eq (exec_syscall_s scs m o vargs) (exec_syscall_s scs m o vargs').
Proof.
move=> /(vuincl_it_app_sopn _ (syscall_sig_s_noarr o)) h.
apply: xrutt_bind; first exact: h.
by move=> [[scs1 m1] r1] _ <-; apply: xrutt_Ret.
Qed.

Lemma exec_syscallPs scs m o vargs vargs' :
  values_uincl vargs vargs' ->
  lxeutt sc_res_uincl
    (exec_syscall_s scs m o vargs)
    (exec_syscall_s scs m o vargs').
Proof.
move=> u.
apply: xrutt_weaken_v3; last exact: exec_syscallPs_eq u.
by move=> [[??] ?] _ <-.
Qed.

Lemma sem_syscall_equiv o scs m :
  mk_forall_it (fun r => mem_equiv m r.1.2) (sem_syscall o scs m).
Proof.
case: o => ws len /= p len'.
apply: lutt_bind; first exact: lutt_true.
move=> [scs' bs] _; apply: (lutt_bind (R := mem_equiv m)).
- apply: lutt_iresult => // m' hf; split; first exact: fill_mem_stack_stable hf.
  exact: fill_mem_validw_eq hf.
by move=> m' h; apply/lutt_Ret'/h.
Qed.

Lemma exec_syscallSs scs m o vargs :
  lutt (fun _ _ => True) (fun _ _ _ => True)
    (fun '(_, m', _) => mem_equiv m m')
    (exec_syscall_s scs m o vargs).
Proof.
rewrite /exec_syscall_s.
apply: (lutt_bind (R := fun r => mem_equiv m r.1.2)).
- exact/mk_forall_itP/sem_syscall_equiv.
by move=> [[scs' m'] t] h; apply/lutt_Ret'/h.
Qed.

End StackSyscall.
