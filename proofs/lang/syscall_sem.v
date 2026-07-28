(* ** Imports and settings *)
From mathcomp Require Import ssreflect ssrfun ssrbool seq ssralg eqtype.
From Coq Require Import ZArith.

From ITree Require Import Basics ITree ITreeFacts Exception.
Import Basics.Monads.

Require Export utils syscall wsize word type low_memory sem_type values.
Require Import it_sems_core_defs core_logics.

Local Open Scope Z_scope.

Import MonadNotation ITreeNotations.
Local Open Scope monad_scope.

(* move *)
Lemma eqit_throw
  {Err E R1 R2} {H : exceptE Err -< E} (RR : R1 -> R2 -> Prop) b1 b2 (e : Err) :
  eqit RR b1 b2 (throw (H := H) e) (throw e).
Proof. exact: eqit_Vis. Qed.

Lemma lutt_throw
  {Err E T} {H : exceptE Err -< E} PEv PAns (R : T -> Prop) (e : Err) :
  PEv _ (subevent _ (Throw e)) ->
  lutt PEv PAns R (throw (H := H) e).
Proof. by move=> ?; apply: lutt_Vis. Qed.

Lemma lutt_Ret' E PEv PAns T R (r : T) :
  lutt (E := E) PEv PAns R (Ret r) <-> R r.
Proof. by symmetry; apply lutt_Ret. Qed.

Lemma lutt_iresult
  T E0 E
  {wE : with_Error E E0}
  (PEv : prepred E) (PAns : postpred E) R (r : exec T) :
  (forall e, r = Error e -> PEv _ (subevent _ (Throw e))) ->
  (forall x, r = ok x -> R x) ->
  lutt PEv PAns R (iresult r).
Proof.
case: r => [x|e]; last by move=> h _; apply/lutt_throw/h.
by move=> _ h; apply/lutt_Ret'/h.
Qed.

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

Definition chk_one_arr len vs : bool :=
  if vs is [:: v] then is_ok (to_arr len v) else false.

Definition exec_getrandom_u scs len vs : itree E (syscall_state * values) :=
  iassert (chk_one_arr len vs) ErrType ;;
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

Lemma value_uincl_to_arr_err va va' len e :
  value_uincl va va' ->
  to_arr len va = Error e ->
  to_arr len va' = Error e.
Proof.
move=> /value_uinclE.
case: va => [? -> | ? -> | n a | ?? [? [? [-> _]]] |] //.
- by move=> [a' ->]; rewrite /= /WArray.cast; case: ifP.
by move=> [||//|ws] ?; case: va'.
Qed.

Lemma exec_syscallPu scs m o vargs vargs' :
  values_uincl vargs vargs' ->
  eutt
    (fun '(scs1, m1, vres1) '(scs2, m2, vres2) =>
       [/\ scs1 = scs2, m1 = m2 & values_uincl vres1 vres2])
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

Section Section.

Context
  {pd : PointerData}
  {syscall_state : Type}
  {E0 E : Type -> Type}
  {wE : with_Error E E0}
  {rE : with_RndEvent syscall_state E}
.

Definition exec_getrandom_s_core
  (scs : syscall_state) (m : mem) (p : pointer) (len : pointer) :
  itree E (syscall_state * mem * pointer) :=
  let len := wunsigned len in
  '(scs', bs) <- trigger (Rnd scs len) ;;
  m' <- iresult (fill_mem m p bs) ;;
  Ret (scs', m', p).

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

Lemma exec_getrandom_s_core_validw scs m p len rscs rm rp :
  exec_getrandom_s_core scs m p len = ok (rscs, rm, rp) →
  validw m =3 validw rm.
Proof. by rewrite /exec_getrandom_s_core; t_xrbindP => rm' /fill_mem_validw_eq hf ? <- ?. Qed.

Definition sem_syscall (o:syscall_t) :
     syscall_state_t -> mem -> sem_prod (map eval_atype (syscall_sig_s o).(scs_tin)) (exec (syscall_state_t * mem * sem_tuple (map eval_atype (syscall_sig_s o).(scs_tout)))) :=
  match o with
  | RandomBytes _ _ => exec_getrandom_s_core
  end.

Definition exec_syscall_s (scs : syscall_state_t) (m : mem) (o:syscall_t) vs : exec (syscall_state_t * mem * values) :=
  let semi := sem_syscall o in
  Let: (scs', m', t) := app_sopn _ (semi scs m) vs in
  ok (scs', m', list_ltuple t).

Lemma syscall_sig_s_noarr o : all is_not_carr (map eval_atype (syscall_sig_s o).(scs_tin)).
Proof. by case: o. Qed.

Lemma exec_syscallPs_eq scs m o vargs vargs' rscs rm vres :
  exec_syscall_s scs m o vargs = ok (rscs, rm, vres) →
  values_uincl vargs vargs' →
  exec_syscall_s scs m o vargs' = ok (rscs, rm, vres).
Proof.
  rewrite /exec_syscall_s; t_xrbindP => -[[scs' m'] t] happ [<- <- <-] hu.
  by have -> := vuincl_sopn (syscall_sig_s_noarr o) hu happ.
Qed.

Lemma exec_syscallPs scs m o vargs vargs' rscs rm vres :
  exec_syscall_s scs m o vargs = ok (rscs, rm, vres) →
  values_uincl vargs vargs' →
  exists2 vres' : values,
    exec_syscall_s scs m o vargs' = ok (rscs, rm, vres') & values_uincl vres vres'.
Proof.
  move=> h1 h2; rewrite (exec_syscallPs_eq h1 h2).
  by exists vres=> //; apply List_Forall2_refl.
Qed.

Lemma sem_syscall_equiv o scs m :
  mk_forall (fun (rm: (syscall_state_t * mem * _)) => mem_equiv m rm.1.2)
            (sem_syscall o scs m).
Proof.
  case: o => _ws _len /= p len [[scs' rm] t] /= hex; split.
  + by apply: exec_getrandom_s_core_stable hex.
  by apply: exec_getrandom_s_core_validw hex.
Qed.

Lemma exec_syscallSs scs m o vargs rscs rm vres :
  exec_syscall_s scs m o vargs = ok (rscs, rm, vres) →
  mem_equiv m rm.
Proof.
  rewrite /exec_syscall_s; t_xrbindP => -[[scs' m'] t] happ [_ <- _].
  apply (mk_forallP (sem_syscall_equiv o scs m) happ).
Qed.

End Section.
