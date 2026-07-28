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

(* move *)
Lemma xrutt_weaken_v3
  {E1 E2 : Type -> Type} {O1 O2 : Type}
  (EE1 : forall X, E1 X -> bool)
  (EE2 : forall X, E2 X -> bool)
  (REv : forall A B, E1 A -> E2 B -> Prop)
  (RAns : forall A B, E1 A -> A -> E2 B -> B -> Prop)
  (RR RR' : O1 -> O2 -> Prop) t1 t2 :
  (forall o1 o2, RR o1 o2 -> RR' o1 o2) ->
  xrutt EE1 EE2 REv RAns RR t1 t2 ->
  xrutt EE1 EE2 REv RAns RR' t1 t2.
Proof. exact: xrutt_weaken_v2. Qed.

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

Section MOVE.

Definition lxrutt
  {E0l E0r El Er} {wEl : with_Error El E0l} {wEr : with_Error Er E0r} {R1 R2} :
  (forall A B, El A -> Er B -> Prop) ->
  (forall A B, El A -> A -> Er B -> B -> Prop) ->
  (R1 -> R2 -> Prop) -> itree El R1 -> itree Er R2 -> Prop :=
  xrutt (errcutoff (is_error wEl)) nocutoff.

Lemma is_error_Throw {E0 E} {wE : with_Error E E0} e :
  IsCut_ (errcutoff (is_error wE)) void (subevent void (Throw e)).
Proof. by rewrite /errcutoff /is_error mid12. Qed.

Section EQ.
  Context {E0 E} {wE : with_Error E E0}.

  Lemma RPre_eq_refl T (e : E T) : RPre_eq e e.
  Proof. by exists erefl. Qed.

  Lemma Rpost_eqI T (e : E T) t1 t2 :
    RPost_eq e t1 e t2 ->
    t1 = t2.
  Proof. by move=> /(_ erefl) ->. Qed.

  Definition lxeutt
    {R1 R2} (RR : R1 -> R2 -> Prop) : itree E R1 -> itree E R2 -> Prop :=
    lxrutt RPre_eq RPost_eq RR.

End EQ.

Section XRUTT.

  Context
    {E0l E0r El Er} {wEl : with_Error El E0l} {wEr : with_Error Er E0r}
    {R1 R2 : Type}
    (REv : forall A B, El A -> Er B -> Prop)
    (RAns : forall A B, El A -> A -> Er B -> B -> Prop)
    (RR : R1 -> R2 -> Prop)
  .

  Lemma lxrutt_throw e t : lxrutt REv RAns RR (throw e) t.
  Proof. exact/xrutt_CutL/is_error_Throw. Qed.

  Lemma lxrutt_iresult (x1 : exec R1) (x2 : exec R2) :
    (forall v1, x1 = ok v1 -> exists2 v2, x2 = ok v2 & RR v1 v2) ->
    lxrutt REv RAns RR (iresult x1) (iresult x2).
  Proof.
  case: x1 => [v1 | ??]; last exact: lxrutt_throw.
  by move=> /(_ _ erefl) [v2 ->]; apply: xrutt_Ret.
  Qed.

  Lemma lxrutt_iresult_Ret (x1 : exec R1) (v2 : R2) :
    (forall v1, x1 = ok v1 -> RR v1 v2) ->
    lxrutt REv RAns RR (iresult x1) (Ret v2).
  Proof.
    case: x1 => [v1 | ??]; last exact: lxrutt_throw.
    by move=> /(_ _ erefl); apply: xrutt_Ret.
  Qed.

  Lemma lxrutt_bind_iresult T (x1 : exec T) F1 F2 :
    (forall v1, x1 = ok v1 -> lxrutt REv RAns RR (F1 v1) F2) ->
    lxrutt REv RAns RR (v1 <- iresult x1 ;; F1 v1) F2.
  Proof.
  case: x1 => [v1 | ??]; last by rewrite bind_throw; apply: lxrutt_throw.
  by rewrite bind_ret_l => /(_ _ erefl).
  Qed.

End XRUTT.

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

Definition it_sem_prod ts T := sem_prod ts (itree E T).

Definition sys_sig_s_atype_in o :=
  [seq eval_atype t | t <- (syscall_sig_s o).(scs_tin)].
Definition sys_sig_s_atype_out o :=
  [seq eval_atype t | t <- (syscall_sig_s o).(scs_tout)].
Definition sys_sig_s_atype o :=
  it_sem_prod
    (sys_sig_s_atype_in o)
    (syscall_state * mem * sem_tuple (sys_sig_s_atype_out o)).

Lemma syscall_sig_s_noarr o : all is_not_carr (sys_sig_s_atype_in o).
Proof. by case: o. Qed.

Fixpoint it_app_sopn A (ts : seq ctype) : it_sem_prod ts A -> values -> itree E A :=
  match ts return it_sem_prod ts A -> values -> itree E A with
  | [::] => fun (o : itree E A) vs =>
      if vs is [::] then o else throw ErrType
  | t :: ts => fun (o : sem_t t -> it_sem_prod ts A) vs =>
      if vs is v :: vs then
        v' <- iresult (of_val t v) ;;
        it_app_sopn (o v') vs
      else throw ErrType
  end.

#[global] Arguments it_app_sopn {A} ts _ _.

Lemma vuincl_it_app_sopn T ts (op : it_sem_prod ts T) vs vs' :
  all is_not_carr ts ->
  values_uincl vs vs' ->
  lxeutt eq (it_app_sopn ts op vs) (it_app_sopn ts op vs').
Proof.
elim: ts op vs vs' => /= [|t ts ih] op [|v vs] [|v' vs'] + /List_Forall2_inv //.
- move=> _ _; apply: xrutt_refl; first by move=> ?? _ _; apply: RPre_eq_refl.
  by move=> ???? _ _; apply: Rpost_eqI.
- by move=> _ _; apply: lxrutt_throw.
- by move=> _ _; apply: lxrutt_throw.
move=> /andP [] ht hts [/value_uinclE hv hvs].
apply: lxrutt_bind_iresult.
case: t op ht => [|| // | sz] op _ v1 /of_val_typeE.
- by move=> ?; subst; subst; rewrite bind_ret_l; apply: ih hts hvs.
- by move=> ?; subst; subst; rewrite bind_ret_l; apply: ih hts hvs.
move=> /= [? [? [? /word_uincl_truncate h]]]; subst.
move: hv => [? [? [? /h]]]; subst=> /= ->.
by rewrite bind_ret_l; apply: ih hts hvs.
Qed.

Section MkForallIt.

Context (T : Type) (P : T -> Prop).

Definition mk_forall_it (l : seq ctype) : sem_prod l (itree E T) -> Prop :=
  sem_forall (lutt (fun _ _ => True) (fun _ _ _ => True) P) l.

Lemma mk_forall_itP l (f : sem_prod l (itree E T)) vargs :
  mk_forall_it f ->
  lutt (fun _ _ => True) (fun _ _ _ => True) P (it_app_sopn l f vargs).
Proof.
elim: l vargs f => [|t l ih] [|v vs] //= f hall.
- exact: lutt_throw.
- exact: lutt_throw.
apply: lutt_bind; first exact: lutt_true.
by move=> x _; apply: ih.
Qed.

End MkForallIt.

End MOVE.

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

Definition exec_getrandom_s_core
  scs m p len : itree E (syscall_state * mem * pointer) :=
  let len := wunsigned len in
  '(scs', bs) <- trigger (Rnd scs len) ;;
  m' <- iresult (fill_mem m p bs) ;;
  Ret (scs', m', p).

Definition sem_syscall
  (o : syscall_t) : syscall_state -> mem -> sys_sig_s_atype o :=
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
  lxeutt
    (fun '(scs1, m1, vres1) '(scs2, m2, vres2) =>
       [/\ scs1 = scs2, m1 = m2 & values_uincl vres1 vres2])
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
