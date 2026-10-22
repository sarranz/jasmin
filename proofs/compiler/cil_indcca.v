(* Bridge between the CIL encoding of INDCCA and the intended INDCCA. *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Uniform Inductive Parameters.

From Coq Require Import JMeq.

From mathcomp Require Import
  ssreflect
  ssrbool
  ssralg
  ssrfun
  ssrnum
  ssrnat
  order
.
From mathcomp Require Import
  choice
  constructive_ereal
  distr
  eqtype
  fintype
  order
  reals
  seq
.
Import GRing.Theory.

From ITree Require Import
  Basics
  ITree
  ITreeFacts
  Interp
  InterpFacts
  Rutt
  RuttFacts
  State
  Events.StateFacts
  Subevent
  Interp.TranslateFacts
.

Require Import distr_extra dinterp rutt_extras utils cil.
Require indcca.

#[local] Open Scope order_scope.
#[local] Open Scope ring_scope.

Section MAIN.

Context
  {R : realType}
  {KEMP : KEMParams}
  {advmem : Type}
.

Notation Rnd := (Rnd (R := R)).

Lemma run_state_translate_inr1 {X S : Type} (u : itree Rnd X) (s : S) :
  eutt eq
    (run_state (translate (inr1 : Rnd ~> stateE S +' Rnd) u) s)
    (let* x := u in Ret (s, x)).
Proof.
revert u s; einit; ecofix CIH => u s.
rewrite (itree_eta u); case: (observe u) => [r|u'|Y e k]; rewrite /run_state.
- by rewrite translate_ret interp_state_ret bind_ret_l; reflexivity.
- by rewrite translate_tau interp_state_tau bind_tau; etau.
rewrite translate_vis interp_state_vis bind_vis /case_ /pure_state /=.
rewrite bind_vis; evis => x; rewrite bind_ret_l /=.
eapply euttG_cong_euttge; [exact: tau_euttge | reflexivity |]; ebase.
Qed.

Lemma run_state_bind
  {E : Type -> Type} {A B St : Type}
  (u : itree (stateE St +' E) A)
  (k : A -> itree (stateE St +' E) B)
  (s : St) :
  run_state (let* x := u in k x) s ≅
    let* p := run_state u s in run_state (k p.2) p.1.
Proof. exact: interp_state_bind. Qed.

Lemma run_state_get {E : Type -> Type} {St : Type} (s : St) :
  eutt eq (run_state (get : itree (stateE St +' E) St) s) (Ret (s, s)).
Proof.
rewrite /run_state /get /embed /=; rewrite interp_state_trigger //=.
reflexivity.
Qed.

Lemma run_state_put {E : Type -> Type} {St : Type} (s s' : St) :
  eutt eq (run_state (put s' : itree (stateE St +' E) unit) s) (Ret (s', tt)).
Proof.
rewrite /run_state /put /embed /=; rewrite interp_state_trigger //=.
reflexivity.
Qed.

Lemma run_state_handle_exch
  {I : OracleSystemInterface}
  {O : OracleSystem I}
  (o : No)
  (i : In o)
  (t : trace (O := O)) :
  eutt eq
    (run_state (handle_Exch (O := O) (Exchange o i)) t)
    (let* (r, m') := Oo (O := O) o i (head mi [seq x.2 | x <- t]) in
     Ret (mk (R := R) m' i r :: t, r)).
Proof.
rewrite /handle_Exch /get_Mo /log.
rewrite run_state_bind.
rewrite run_state_bind run_state_get bind_ret_l /= /run_state interp_state_ret.
rewrite bind_ret_l /=.
setoid_rewrite run_state_bind.
rewrite run_state_translate_inr1 bind_bind.
apply: eutt_eq_bind => -[r m'] /=.
rewrite bind_ret_l /=.
rewrite run_state_bind run_state_bind run_state_get bind_ret_l /=.
rewrite run_state_put /run_state bind_ret_l /= interp_state_ret.
reflexivity.
Qed.

Lemma run_state_interp_trigger_exch
  {I : OracleSystemInterface}
  {O : OracleSystem I}
  {T X : Type}
  (e : Exch T)
  (k : T -> itree (Exch +' Rnd) X)
  (t : trace (O := O)) :
  eutt eq
    (run_state
       (interp (case_ (handle_Exch (O := O)) inr_)
          (let* r := trigger e in k r)) t)
    (let* p := run_state (handle_Exch (O := O) e) t in
     run_state (interp (case_ (handle_Exch (O := O)) inr_) (k p.2)) p.1).
Proof.
rewrite interp_bind run_state_bind.
have hit :
  eutt eq
    (interp (case_ (handle_Exch (O := O)) inr_)
       (ITree.trigger (inl1 e : (Exch +' Rnd) T)))
    (handle_Exch (O := O) e).
- by apply: euttge_sub_eutt; apply: interp_trigger.
by rewrite hit /=; reflexivity.
Qed.

Lemma split_after_cat {T : Type} (p : pred T) (s s' : seq T) (x : T) :
  all p s -> ~~ p x -> split_after p (s ++ x :: s') = (s, x :: s').
Proof.
elim: s => [|y s ih] /=; first by move=> _ /negbTE ->.
by move=> /andP[hy hs] hx; rewrite hy (ih hs hx).
Qed.

Lemma is_getchallenge_not_query (x : Xch (I := INDCCA_I)) y :
  is_getchallenge x = Some y -> is_query x = None.
Proof. by case: x => -[] [i r]. Qed.

Lemma is_finalize_not_query (x : Xch (I := INDCCA_I)) y :
  is_finalize x = Some y -> is_query x = None.
Proof. by case: x => -[] [i r]. Qed.

Section CHALLENGER.

Context (K : OracleSystem (R := R) KEM).

(* The intended challenger of a CIL KEM: the oracles of the KEM, with the
   KEM memory as the challenger memory. *)
Definition challenger_of_kem :
  indcca.Challenger (R := R) (pkey := pkey) (skey := skey)
    (ctxt := ctxt) (msg := msg) :=
  {|
    indcca.cmem := K.(Mo);
    indcca.cmi := K.(mi);
    indcca.GenKey := fun m => Oo (O := K) OGenKey tt m;
    indcca.Encap := fun pk m => Oo (O := K) OEncap pk m;
    indcca.Decap := fun sk ct m => Oo (O := K) ODecap (sk, ct) m;
  |}.

(* A decapsulation query of the intended adversary is a [OQuery] exchange. *)
Definition dec_to_exch :
  (indcca.Dec (ctxt := ctxt) (msg := msg) +' Rnd) ~>
  (Exch (I := INDCCA_I) +' Rnd) :=
  fun T e =>
    match e with
    | inl1 d =>
        match d in indcca.Dec T return (Exch (I := INDCCA_I) +' Rnd) T with
        | indcca.Decapsulate c => inl1 (Exchange (I := INDCCA_I) OQuery c)
        end
    | inr1 r => inr1 r
    end.

(* The CIL adversary that runs the two stages of an intended adversary. *)
Definition adv_to_cil
  (A : indcca.Adversary (R := R) (pkey := pkey) (advmem := advmem)
         (ctxt := ctxt) (msg := msg)) :
  Adversary (R := R) (I := INDCCA_I) :=
  {|
    Aa :=
      let* pk := trigger (Exchange (I := INDCCA_I) OInit tt) in
      let* amem := translate dec_to_exch (A.(indcca.Query) pk) in
      let* (ct, mb) := trigger (Exchange (I := INDCCA_I) OGetChallenge tt) in
      let* g := translate dec_to_exch (A.(indcca.Guess) amem pk ct mb) in
      let* _ := trigger (Exchange (I := INDCCA_I) OFinalize g) in
      Ret tt;
  |}.

(* Trace entries that are decapsulation queries. *)
Definition is_query_x (x : Xch (I := INDCCA_I) * _Mo (K := K)) : bool :=
  isSome (is_query x.1).

Definition query_ct (x : Xch (I := INDCCA_I) * _Mo (K := K)) : option ctxt :=
  ssrfun.omap fst (is_query x.1).

(* Invariant between a CIL trace [t] and an intended state [s] (log, memory).
   The fixed suffix [pre] of [t] is the part of the trace that precedes the
   current phase. *)
Definition cil_inv
  (pre : trace (O := INDCCA K))
  (keys : pkey * skey)
  (bit : option bool)
  (t : trace (O := INDCCA K))
  (s : indcca.S (ctxt := ctxt) * K.(Mo)) :
  Prop :=
  exists tq,
    [/\ t = tq ++ pre
      , all is_query_x tq
      , pmap query_ct tq = s.1
      & head _mi [seq x.2 | x <- t] =
          {| mo_keys := Some keys; mo_bit := bit; mo_mem := s.2; |}].

(* Final relation between a CIL trace and the result of the intended game. *)
Definition trace_rel
  (t : trace (O := INDCCA K))
  (r : bool * indcca.trace (ctxt := ctxt)) :
  Prop :=
  let '(bres, (lq, lg, ct)) := r in
  destruct_trace [seq proj_xch e | e <- t] = Some (bres, lq, lg, ct).

Lemma rutt_handle_query
  (pre : trace (O := INDCCA K))
  (pk : pkey)
  (sk : skey)
  (bit : option bool)
  (c : ctxt) :
  rutt_inv (E := Rnd) (cil_inv pre (pk, sk) bit) eq
    (handle_Exch (O := INDCCA K) (Exchange (I := INDCCA_I) OQuery c))
    (indcca.handle_Dec challenger_of_kem sk (indcca.Decapsulate c)).
Proof.
rewrite /handle_Exch /get_Mo /log /indcca.handle_Dec /indcca.log /=.
rewrite /rutt_inv bind_bind.
setoid_rewrite bind_ret_l.
apply: rutt_bind; first exact: rutt_inv_get.
move=> t [l m] [tq [-> hall hpm hhd]] /=.
rewrite hhd /= /_Oo_Query /= translate_bind bind_bind.
apply: (rutt_bind _ _ eq).
- apply:
    (rutt_translate_gen
       (REv := fun A B (e1 : Rnd A) (e2 : Rnd B) =>
                 exists p : A = B, eq_rect A Rnd e1 B p = e2)
       (RAns := fun A B e1 a e2 b => JMeq a b)).
  + done.
  + by move=> A B [X1 mu1] [X2 mu2].
  apply: gen_eutt_rutt; last reflexivity.
  + by move=> u e; exists (erefl u).
  + by move=> u e a b; exact: JMeq_eq.
move=> [r m'] _ <- /=.
rewrite translate_ret bind_ret_l !bind_bind.
apply: rutt_bind; first exact: rutt_inv_get.
move=> t2 [l2 m2] [tq2 [-> hall2 hpm2 hhd2]] /=.
apply: rutt_bind.
- apply: rutt_inv_put.
  exists (
    mk (O := INDCCA K) (o := OQuery)
      (mo_with_mem
         {| mo_keys := Some (pk, sk); mo_bit := bit; mo_mem := m; |} m')
      c r :: tq2).
  split => //=.
  by rewrite hpm2.
move=> _ _ _; exact: rutt_Ret.
Qed.

Lemma eutt_run_state_phase
  {X : Type}
  (pre : trace (O := INDCCA K))
  (pk : pkey)
  (sk : skey)
  (bit : option bool)
  (tA : itree (indcca.Dec (ctxt := ctxt) (msg := msg) +' Rnd) X)
  (t0 : trace (O := INDCCA K))
  (s0 : indcca.S (ctxt := ctxt) * K.(Mo)) :
  cil_inv pre (pk, sk) bit t0 s0 ->
  eutt (RR_run_state (cil_inv pre (pk, sk) bit) eq)
    (run_state
       (interp (case_ (handle_Exch (O := INDCCA K)) inr_)
          (translate dec_to_exch tA)) t0)
    (run_state
       (interp (case_ (indcca.handle_Dec challenger_of_kem sk) inr_) tA) s0).
Proof.
move=> hinv; rewrite interp_translate.
apply: rutt_inv_run_state => //.
apply:
  (rutt_weaken
     (REv := REv_inv (cil_inv pre (pk, sk) bit))
     (RAns := RAns_inv (cil_inv pre (pk, sk) bit))
     (RR := eq)
  ) => //.
apply: rutt_interp_h => T [[c] | r] /=; first exact: rutt_handle_query.
apply: rutt_trigger; first by exists erefl.
move=> v1 v2 /=; exact: JMeq_eq.
Qed.

Lemma destruct_trace_shape
  (fin gc x0 : Xch (I := INDCCA_I) * _Mo (K := K))
  (tg tq : seq (Xch (I := INDCCA_I) * _Mo (K := K)))
  (lq lg : seq ctxt)
  (ct : ctxt)
  (mb : msg)
  (b g : bool) :
  isSome (is_init x0.1) ->
  all is_query_x tq ->
  pmap query_ct tq = lq ->
  is_getchallenge gc.1 = Some (ct, mb) ->
  mo_bit gc.2 = Some b ->
  all is_query_x tg ->
  pmap query_ct tg = lg ->
  is_finalize fin.1 = Some g ->
  destruct_trace
    [seq proj_xch e | e <- fin :: tg ++ gc :: tq ++ [:: x0]] =
    Some (g == b, lq, lg, ct).
Proof.
move=> hi hq hpq hgc hb ht hpt hfin.
have hrev :
  rev (fin :: tg ++ gc :: tq ++ [:: x0]) =
  x0 :: (rev tq ++ gc :: (rev tg ++ [:: fin])).
- rewrite rev_cons rev_cat rev_cons rev_cat /=.
  by rewrite -!cats1 -!catA.
rewrite /destruct_trace -map_rev hrev /= map_cat /= map_cat /= hi /=.
have hn1 : ~~ isSome (is_query (proj_xch gc).1).
- by rewrite /proj_xch /= (is_getchallenge_not_query hgc).
have hn2 : ~~ isSome (is_query (proj_xch fin).1).
- by rewrite /proj_xch /= (is_finalize_not_query hfin).
have hall1 :
  all (fun x : Xch_b => isSome (is_query x.1))
    [seq proj_xch e | e <- rev tq].
- by rewrite all_map all_rev; exact: hq.
have hall2 :
  all (fun x : Xch_b => isSome (is_query x.1))
    [seq proj_xch e | e <- rev tg].
- by rewrite all_map all_rev; exact: ht.
rewrite (split_after_cat _ hall1 hn1) /=.
rewrite hgc hb /=.
rewrite (split_after_cat [::] hall2 hn2) /=.
rewrite hfin /=.
have hpm :
  forall l : seq (Xch (I := INDCCA_I) * _Mo (K := K)),
    pmap (fun x : Xch_b => omap fst (is_query x.1))
      [seq proj_xch e | e <- rev l] = rev (pmap query_ct l).
- elim=> // x l ih; rewrite rev_cons -cats1 map_cat pmap_cat ih /= /query_ct.
  by case: (is_query x.1) => [y|] /=; rewrite ?cats0 // rev_cons cats1.
by rewrite !hpm !revK hpq hpt.
Qed.

Lemma win_trace_rel
  (Q : nat)
  (t : trace (O := INDCCA K))
  (r : bool * indcca.trace (ctxt := ctxt)) :
  trace_rel t r ->
  win (WinningCondition := W Q) t = r.1 && indcca.valid Q r.2.
Proof.
case: r => bres [[lq lg] ct] /= h.
by rewrite /win /= h /=.
Qed.

Lemma eutt_interact_game
  (A : indcca.Adversary (R := R) (pkey := pkey) (advmem := advmem)
         (ctxt := ctxt) (msg := msg)) :
  eutt trace_rel
    (interact (INDCCA K) (adv_to_cil A))
    (indcca.game challenger_of_kem A).
Proof.
rewrite /interact /indcca.game /indcca.interact /=.
(* Init. *)
rewrite
  (run_state_interp_trigger_exch (O := INDCCA K)
     (Exchange (I := INDCCA_I) OInit tt)).
rewrite bind_bind run_state_handle_exch /= bind_bind.
rewrite /_Oo_Init bind_bind.
apply: eutt_eq_bind => -[[pk sk] m'] /=.
rewrite !bind_ret_l /=.
set x0 :=
  mk (O := INDCCA K) (o := OInit)
    {| mo_keys := Some (pk, sk); mo_bit := None; mo_mem := m'; |} tt pk.
have hinv1 : cil_inv [:: x0] (pk, sk) None [:: x0] ([::], m') by exists [::].
(* Query phase. *)
rewrite interp_bind run_state_bind bind_bind.
apply:
  (eutt_clo_bind _
     (UU := RR_run_state (cil_inv [:: x0] (pk, sk) None) eq)).
- exact: eutt_run_state_phase.
move=> [t2 amem1] [[lq m0] amem2] [/= hinv2 <-].
(* GetChallenge. *)
rewrite
  (run_state_interp_trigger_exch (O := INDCCA K)
     (Exchange (I := INDCCA_I) OGetChallenge tt)).
rewrite bind_bind run_state_handle_exch /=.
case: hinv2 => tq [ht2 hall hpm hhd].
rewrite hhd /= /_Oo_GetChallenge /= !bind_bind.
apply: eutt_eq_bind => -[[ct m1] mem'] /=.
rewrite !bind_bind.
apply: eutt_eq_bind => m2.
rewrite !bind_bind.
apply: eutt_eq_bind => b.
rewrite !bind_ret_l /=.
set gc :=
  mk (O := INDCCA K) (o := OGetChallenge) _ tt (ct, if b then m2 else m1).
have hinv3 :
  cil_inv (gc :: t2) (pk, sk) (Some b) (gc :: t2) ([::], mem')
  by exists [::].
(* Guess phase. *)
rewrite interp_bind run_state_bind bind_bind.
apply:
  (eutt_clo_bind _
     (UU := RR_run_state (cil_inv (gc :: t2) (pk, sk) (Some b)) eq)).
- exact: eutt_run_state_phase.
move=> [t4 g1] [[lg m4] g2] [/= hinv4 <-].
(* Finalize. *)
rewrite
  (run_state_interp_trigger_exch (O := INDCCA K)
     (Exchange (I := INDCCA_I) OFinalize g1)).
rewrite bind_bind run_state_handle_exch /= /_Oo_Finalize !bind_ret_l /=.
rewrite /run_state interp_ret interp_state_ret bind_ret_l /=.
case: hinv4 => tg [ht4 hallg hpmg hhd4].
apply eutt_Ret.
rewrite /trace_rel ht4 ht2.
apply:
  (destruct_trace_shape
     (fin := mk (O := INDCCA K) (o := OFinalize) _mi g1 tt)
     (gc := gc) (x0 := x0) (tq := tq) (tg := tg)) => //=.
Qed.

Lemma pwin_adv_to_cil
  (Q : nat)
  (A : indcca.Adversary (R := R) (pkey := pkey) (advmem := advmem)
         (ctxt := ctxt) (msg := msg)) :
  pwin (INDCCA K) (adv_to_cil A) (W Q) =
    \P_[indcca.dgame challenger_of_kem A]
      (fun '(b, t) => b && indcca.valid Q t).
Proof.
rewrite /pwin /dinteract /indcca.dgame.
apply: (eutt_deqX (eutt_interact_game A)).
move=> t [b tr] h /=; exact: win_trace_rel h.
Qed.

Lemma indcca_adv_advantage
  (Q : nat)
  (A : indcca.Adversary (R := R) (pkey := pkey) (advmem := advmem)
         (ctxt := ctxt) (msg := msg)) :
  indcca_adv K Q (adv_to_cil A) = indcca.advantage challenger_of_kem A Q.
Proof.
by rewrite /indcca_adv /indcca.advantage pwin_adv_to_cil.
Qed.

End CHALLENGER.

Lemma indcca_reduction_reduction (K1 K2 : OracleSystem (R := R) KEM) :
  indcca_reduction K1 K2 ->
  indcca.reduction (advmem := advmem)
    (challenger_of_kem K1) (challenger_of_kem K2).
Proof.
move=> h A Q.
rewrite -(indcca_adv_advantage K1) -(indcca_adv_advantage K2).
exact: h.
Qed.

End MAIN.
