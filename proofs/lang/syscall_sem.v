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

#[global] Instance with_RndEventE
  {scs : Type}
  {E E0 : Type -> Type}
  {wE : with_Error E E0}
  {rE : with_RndEvent scs E0}
  : with_RndEvent scs E :=
  fun T e => mfun2 (inr1 (rE T e)).

Section SourceSysCall.

Context
  {pd: PointerData}
  {syscall_state : Type}
.

Notation E := (ErrEvent +' RndEvent syscall_state).

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
.

Notation E := (ErrEvent +' RndEvent syscall_state).

Implicit Types
  (o : syscall_t)
  (scs : syscall_state)
  (m : mem)
  (p : pointer)
  (len : pointer)
.

Definition sc_s_atype_in o :=
  [seq eval_atype t | t <- (syscall_sig_s o).(scs_tin)].
Definition sc_s_atype_out o :=
  [seq eval_atype t | t <- (syscall_sig_s o).(scs_tout)].

Lemma syscall_sig_s_noarr o : all is_not_carr (sc_s_atype_in o).
Proof. by case: o. Qed.

(* The semantics of a stack syscall is a three-stage composition: cast the
   argument values to the semantic input type of the syscall, trigger the
   [Rnd] event, and store the answer into memory. The cast and the store
   are deterministic ([exec]); only the trigger is an itree. *)

Definition sem_syscall_cast o (vs : values) :
  exec (sem_tuple (sc_s_atype_in o)) :=
  app_sopn _ (sem_prod_ok _ (sem_prod_tuple (sc_s_atype_in o))) vs.

Definition exec_getrandom_s_core
  scs (args : pointer * pointer) : itree E (syscall_state * seq u8) :=
  trigger (Rnd scs (wunsigned args.2)).

Definition sc_s_trigger o :=
  syscall_state -> sem_tuple (sc_s_atype_in o) ->
    itree E (syscall_state * seq u8).

Definition sem_syscall o : sc_s_trigger o :=
  match o with
  | RandomBytes _ _ => exec_getrandom_s_core
  end.
Arguments sem_syscall : clear implicits.

Definition exec_getrandom_s_store
  m (args : pointer * pointer) (ans : syscall_state * seq u8) :
  exec (syscall_state * mem * pointer) :=
  Let m' := fill_mem m args.1 ans.2 in
  ok (ans.1, m', args.1).

Definition sc_s_store o :=
  mem -> sem_tuple (sc_s_atype_in o) -> syscall_state * seq u8 ->
    exec (syscall_state * mem * sem_tuple (sc_s_atype_out o)).

Definition sem_syscall_store o : sc_s_store o :=
  match o with
  | RandomBytes _ _ => exec_getrandom_s_store
  end.
Arguments sem_syscall_store : clear implicits.

Definition exec_syscall_s scs m o vs : itree E (syscall_state * mem * values) :=
  args <- iresult (sem_syscall_cast o vs) ;;
  ans <- sem_syscall o scs args ;;
  '(scs', m', t) <- iresult (sem_syscall_store o m args ans) ;;
  Ret (scs', m', list_ltuple t).

Lemma sem_syscall_castP o vargs vargs' t :
  values_uincl vargs vargs' ->
  sem_syscall_cast o vargs = ok t ->
  sem_syscall_cast o vargs' = ok t.
Proof. exact: vuincl_sopn (syscall_sig_s_noarr o). Qed.

Lemma sem_syscall_castE ws n vs args :
  sem_syscall_cast (RandomBytes ws n) vs = ok args ->
  exists v1 v2,
    [/\ vs = [:: v1; v2],
        to_word Uptr v1 = ok args.1 &
        to_word Uptr v2 = ok args.2].
Proof.
rewrite /sem_syscall_cast.
case: vs => [|v1 [|v2 [|??]]] /=; t_xrbindP => //.
by move=> w1 hw1 w2 hw2 <-; exists v1, v2.
Qed.

Lemma sem_syscall_storeS o m args ans r :
  sem_syscall_store o m args ans = ok r ->
  mem_equiv m r.1.2.
Proof.
case: o args r => ws n args r /=.
rewrite /exec_getrandom_s_store; t_xrbindP => m' hfill <- /=.
split; first exact: fill_mem_stack_stable hfill.
exact: fill_mem_validw_eq hfill.
Qed.

Lemma exec_syscallPs_eq scs m o vargs vargs' :
  values_uincl vargs vargs' ->
  lxeutt eq (exec_syscall_s scs m o vargs) (exec_syscall_s scs m o vargs').
Proof.
move=> hu; rewrite /exec_syscall_s.
apply: (xrutt_bind (RR := eq)).
- apply: lxrutt_iresult => args h.
  by exists args => //; exact: sem_syscall_castP hu h.
move=> args _ <-.
apply: (xrutt_bind (RR := eq)).
- exact: eutt_lxeutt (reflexivity _).
move=> ans _ <-.
apply: (xrutt_bind (RR := eq)).
- by apply: lxrutt_iresult => r h; exists r.
by move=> [[scs1 m1] t] _ <-; apply: xrutt_Ret.
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

Lemma exec_syscallSs scs m o vargs :
  lutt (fun _ _ => True) (fun _ _ _ => True)
    (fun '(_, m', _) => mem_equiv m m')
    (exec_syscall_s scs m o vargs).
Proof.
rewrite /exec_syscall_s.
apply: lutt_bind; first exact: lutt_true.
move=> args _.
apply: lutt_bind; first exact: lutt_true.
move=> ans _.
apply: (lutt_bind (R := fun r => mem_equiv m r.1.2)).
- by apply: lutt_iresult => // r /sem_syscall_storeS.
by move=> [[scs1 m1] t] h; apply/lutt_Ret'/h.
Qed.

End StackSyscall.

Arguments sem_syscall {pd} {syscall_state} o _ _.
Arguments sem_syscall_store {pd} {syscall_state} o _ _ _.
