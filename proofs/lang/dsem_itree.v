From Coq Require Import ZArith.
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype ssralg.
From mathcomp Require Import choice fintype order seq matrix.
From mathcomp Require Import word_ssrZ word.
From mathcomp.reals Require Import reals.
From mathcomp.experimental_reals Require Import distr.

From ITree Require Import ITree ITreeFacts.

Require Import it_sems_core word utils.
Require distr.

#[local] Open Scope Z.
Local Close Scope vm_scope.

Notation "'let*' p ':=' c1 'in' c2" :=
  (@ITree.bind _ _ _ c1 (fun p => c2))
    (at level 61, p as pattern, c1 at next level, right associativity).

(* ** finType instance for word (from end_to_end.v)
 * -------------------------------------------------------------------- *)

Module WordFinite.
Section S.
Context {ws : wsize}.

Definition enum_word := [seq wrepr ws x | x <- ziota 0 (wbase ws) ].

Lemma word_enumP : Finite.axiom enum_word.
Proof.
move=> b; rewrite count_map (eq_in_count (a2 := pred1 (wunsigned b))).
- rewrite count_ziota; by have [/lezP -> /ltzP /= ->] := wunsigned_range b.
move=> /= x; rewrite in_ziota => /andP [/lezP ? /ltzP ?].
by rewrite -wunsigned_inj' wunsigned_repr_small.
Qed.

#[non_forgetful_inheritance]
HB.instance Definition _ := [Countable of (word ws) by <:].

#[non_forgetful_inheritance]
HB.instance Definition _ := isFinite.Build (word ws) word_enumP.

End S.
End WordFinite.
Export WordFinite.

(* -------------------------------------------------------------------- *)
Section DSEM_ITREE.

Context
  {asm_op : Type}
  {ep : EstateParams unit}
  {spp : SemPexprParams}
  {sip : SemInstrParams asm_op unit}
.

Existing Instance sCP_unit.
Existing Instance nosubword.
Existing Instance indirect_c.
Existing Instance progUnit.

Context {R : realType}.

(* ** Uniform byte sampling: seq-based vs vector-based
 * -------------------------------------------------------------------- *)

Definition Rnd_of_RndEvent : RndEvent unit ~> itree (distr.Rnd (R := R)) :=
  fun _ '(Rnd _ len) =>
    let* bs := unif_rV (Z.to_nat len) in
    Ret (tt, wseq_of_wvec bs).


Section DUNIF_BYTES_VEC.

Let byte : finType := word U8.

(* Convert a row vector of bytes to a sequence *)
Definition rvec_to_seq (n : nat) (v : 'rV[byte]_n) : seq byte :=
  [seq v ord0 i | i <- enum 'I_n].

(* Uniform distribution over byte sequences via vector sampling *)
Definition dunif_bytes_v (n : nat) : {distr (seq byte) / R} :=
  \dlet_(v <- @distr.dunif R 'rV[byte]_n) dunit (rvec_to_seq v).

(* Cons a byte to the front of a row vector *)
Definition rvec_cons (n : nat) (b : byte) (v : 'rV[byte]_n) : 'rV[byte]_n.+1 :=
  \row_(i < n.+1)
    match unlift ord0 i with
    | None => b
    | Some j => v ord0 j
    end.

(* rvec_to_seq distributes over rvec_cons *)
Lemma rvec_to_seq_cons (n : nat) (b : byte) (v : 'rV[byte]_n) :
  rvec_to_seq (rvec_cons b v) = b :: rvec_to_seq v.
Proof.
rewrite /rvec_to_seq /rvec_cons enum_ordSl /= mxE unlift_none.
congr cons; rewrite -map_comp; apply/eq_map => i /=.
by rewrite mxE liftK.
Qed.

(* rvec_to_seq for empty vector *)
Lemma rvec_to_seq_nil (v : 'rV[byte]_0) : rvec_to_seq v = [::].
Proof. by rewrite /rvec_to_seq enum_ord0. Qed.

(* --- Helper lemmas for the main equivalence proof --- *)

(* all_bytes enumerates all byte values *)
(* all_bytes gives the same distribution as the finType uniform on byte *)
Lemma duni_all_bytes :
  duni all_bytes =1 @distr.dunif R byte.
Proof. Admitted.

(* Helper: dlet respects =1 on its components *)
Lemma dlet_eqmu {T U : choiceType} (f : T -> {distr U / R}) (mu nu : {distr T / R}) :
  mu =1 nu -> \dlet_(x <- mu) f x =1 \dlet_(x <- nu) f x.
Proof. by move=> h; apply: eq_in_dlet. Qed.

Lemma dlet_eqf {T U : choiceType} (f g : T -> {distr U / R}) (mu : {distr T / R}) :
  {in dinsupp mu, f =2 g} -> \dlet_(x <- mu) f x =1 \dlet_(x <- mu) g x.
Proof. by move=> h; apply: eq_in_dlet. Qed.

(* Product decomposition: uniform on 'rV[byte]_(n+1) decomposes as
   uniform on byte × uniform on 'rV[byte]_n via rvec_cons *)
Lemma dunif_rvec_decomp (m : nat) :
  @distr.dunif R 'rV[byte]_m.+1 =1
    \dlet_(b <- @distr.dunif R byte)
      \dlet_(v <- @distr.dunif R 'rV[byte]_m)
        dunit (rvec_cons b v).
Proof. Admitted.

(* dweight (total mass) of dunif on a nonempty finType is 1 *)
Lemma dweight_dunif (T : finType) :
  (0 < #|T|)%nat -> \P_[@distr.dunif R T] predT = GRing.one R.
Proof. Admitted.

(* Decomposition of dunif on vectors via rvec_to_seq and rvec_cons *)
Lemma dunif_rvec_seq_decomp (m : nat) :
  \dlet_(w <- @distr.dunif R 'rV[byte]_m.+1) dunit (rvec_to_seq w) =1
    \dlet_(b <- @distr.dunif R byte)
      \dlet_(v <- @distr.dunif R 'rV[byte]_m) dunit (rvec_to_seq (@rvec_cons m b v)).
Proof. Admitted.

Lemma dunif_bytes_eq_v (n : nat) :
  @dunif_bytes R n =1 dunif_bytes_v n.
Proof.
elim: n => [|n ih].
- (* Base case: n = 0 *)
  rewrite /= /dunif_bytes_v => bs.
  (* rvec_to_seq v = [::] for all v : 'rV[byte]_0, so replace by constant *)
  rewrite (dlet_eqf (g := fun _ => @dunit R _ [::])); last first.
    by move=> v _ y; rewrite rvec_to_seq_nil.
  (* dunit [::] bs = dweight mu * dunit [::] bs *)
  rewrite dletC dweight_dunif ?mul1r //.
  by rewrite card_mx muln0 expn0.
- (* Step case: n = S n' *)
  rewrite /= => bs.
  (* Step 1: IH — replace dunif_bytes n by dunif_bytes_v n *)
  rewrite (dlet_eqf (g := fun b =>
    \dlet_(bs' <- dunif_bytes_v n) dunit (b :: bs'))); last first.
    by move=> b _ y; apply: dlet_eqmu; exact: ih.
  (* Step 2: Unfold dunif_bytes_v, use dlet associativity + dlet_unit *)
  rewrite (dlet_eqf (g := fun b =>
    \dlet_(v <- @distr.dunif R 'rV[byte]_n) dunit (b :: rvec_to_seq v))); last first.
    move=> b _ y; rewrite /dunif_bytes_v.
    rewrite __deprecated__dlet_dlet; apply: dlet_eqf => // v _ z.
    by rewrite dlet_unit.
  (* Step 3: b :: rvec_to_seq v = rvec_to_seq (rvec_cons b v) *)
  rewrite (dlet_eqf (g := fun b =>
    \dlet_(v <- @distr.dunif R 'rV[byte]_n) dunit (rvec_to_seq (rvec_cons b v)))); last first.
    by move=> b _ y; apply: dlet_eqf => // v _ z; rewrite rvec_to_seq_cons.
  (* Step 4: Replace duni all_bytes by dunif byte *)
  rewrite (dlet_eqmu _ duni_all_bytes).
  (* Goal: (\dlet_(b <- dunif byte) \dlet_(v <- dunif 'rV[byte]_n)
              dunit (rvec_to_seq (rvec_cons b v))) bs
         = dunif_bytes_v n.+1 bs *)
  (* Step 5: Apply product decomposition *)
  (* dunif_bytes_v (n+1) = \dlet_(w <- dunif 'rV[byte]_(n+1)) dunit (rvec_to_seq w)
     = \dlet_(w <- \dlet_(b <- dunif byte) \dlet_(v <- dunif 'rV[byte]_n)
                     dunit (rvec_cons b v)) dunit (rvec_to_seq w)    [by dunif_rvec_decomp]
     = \dlet_(b <- dunif byte) \dlet_(v <- dunif 'rV[byte]_n)
         dunit (rvec_to_seq (rvec_cons b v))    [by dlet associativity] *)
  symmetry; rewrite /dunif_bytes_v.
  (* Step 5: Product decomposition *)
  have hdecomp := @dunif_rvec_decomp n.
  (* dunif_bytes_v (n+1) = dlet (fun w => dunit (rvec_to_seq w)) (dunif 'rV[byte]_(n+1))
     After decomposition: = dlet ... (dlet ... (dunif byte))
     After flattening: = dlet (fun b => dlet (fun v => dunit (rvec_to_seq (rvec_cons b v))) ...) ... *)
  rewrite /dunif_bytes_v.
  (* Now: (\dlet_(b <- dunif byte) \dlet_(v <- dunif 'rV_n)
             dunit (rvec_to_seq (rvec_cons b v))) bs
         = (\dlet_(w <- dunif 'rV_(n.+1)) dunit (rvec_to_seq w)) bs *)
  (* Step 5: Product decomposition *)
  by rewrite /dunif_bytes_v dunif_rvec_seq_decomp.
Qed.

End DUNIF_BYTES_VEC.

(* ** Event type for unit programs
 * -------------------------------------------------------------------- *)

Let E := ErrEvent +' RndEvent unit.

Local Instance wE_E : with_Error E (RndEvent unit) := FIsoId _.

(* ** Conversion from ITree error result to dfstate
 * -------------------------------------------------------------------- *)

Definition execS_to_dfstate (x : execS fstate) : dfstate :=
  match x with
  | ESok fs => DFSok fs
  | ESerror (e, _) => DFSerr e
  end.

Definition execS_to_dstate (x : execS estate) : dstate :=
  match x with
  | ESok s => DSok s
  | ESerror (e, _) => DSerr e
  end.

(* ** Denotational interpretation of RndEvent ITrees
 *
 * This follows the structure of [dinterp] from compiler/distr.v,
 * interpreting [RndEvent] events using [dunif_bytes] from dpsem.v.
 * -------------------------------------------------------------------- *)

Section DINTERP_E.

Context {T : choiceType}.

Fixpoint dinterp_E' (t : itree' (RndEvent unit) T) (n : nat)
    : {distr T / R} :=
  match n with
  | O => dnull
  | S n' =>
    match t with
    | RetF r => dunit r
    | TauF t => dinterp_E' (observe t) n'
    | VisF _ e k =>
        match e in RndEvent _ A
          return (A -> itree (RndEvent unit) T) -> {distr T / R}
        with
        | Rnd scs len =>
            fun k0 =>
              \dlet_(bytes <- dunif_bytes (Z.to_nat len))
                dinterp_E' (observe (k0 (scs, bytes))) n'
        end k
    end
  end.

Definition dinterp_E (t : itree (RndEvent unit) T) : {distr T / R} :=
  dlim (dinterp_E' (observe t)).

End DINTERP_E.

(* ** Properties of dinterp_E' and dinterp_E
 * -------------------------------------------------------------------- *)

Section DINTERP_E_PROPS.

Context {T : choiceType}.

(* Monotonicity: one step *)
Lemma dinterp_E'_step (t : itree' (RndEvent unit) T) (n : nat) :
  dinterp_E' t n <=1 dinterp_E' t (S n).
Proof.
elim: n t => [|n ih] t x; first exact: lef_dnull.
case: t => [r | t | A e k].
- exact: lexx.
- exact: ih.
- case: e k => scs len k /=.
  by apply: le_in_dlet => /= bytes _ x'; exact: ih.
Qed.

(* Monotonicity: general *)
Lemma dinterp_E'_mono (t : itree' (RndEvent unit) T) (n m : nat) :
  leq n m -> dinterp_E' t n <=1 dinterp_E' t m.
Proof.
elim: m => [|m ihm] h x.
- by rewrite leqn0 in h; move/eqP: h => ->.
- rewrite leq_eqVlt in h; case/orP: h => [/eqP->|h] //.
  rewrite ltnS in h.
  exact: le_trans (ihm h x) (dinterp_E'_step t m x).
Qed.

(* dinterp_E of Ret *)
Lemma dinterp_E_ret (x : T) :
  dinterp_E (Ret x) =1 @dunit R _ x.
Proof.
move=> y; rewrite /dinterp_E.
rewrite -(dlim_bump (fun n => dinterp_E' (observe (Ret x)) n) y) /=.
exact: dlimC.
Qed.

(* dinterp_E of Tau *)
Lemma dinterp_E_tau (t : itree (RndEvent unit) T) :
  dinterp_E (Tau t) =1 dinterp_E t.
Proof.
move=> y; rewrite /dinterp_E.
by rewrite -(dlim_bump (fun n => dinterp_E' (observe (Tau t)) n) y).
Qed.

(* dinterp_E of spin (infinite Tau-loop) is dnull *)
Lemma dinterp_E'_spin (n : nat) :
  dinterp_E' (observe (@ITree.spin (RndEvent unit) T)) n =1 @dnull R T.
Proof. by elim: n => [|n ih] //= x. Qed.

Lemma dinterp_E_spin :
  dinterp_E (@ITree.spin (RndEvent unit) T) =1 @dnull R T.
Proof.
move=> x; rewrite /dinterp_E.
have h : forall n, dinterp_E' (observe ITree.spin) n x = @dnull R T x.
  by move=> n; rewrite dinterp_E'_spin.
rewrite -[RHS](@dlimC R T (@dnull R T) x).
by apply: eq_dlim => n; exact: dinterp_E'_spin.
Qed.

(* dinterp_E of Vis (Rnd) — interchange limit and dlet *)
Lemma dinterp_E_vis_rnd (len : Z)
    (k : unit * seq u8 -> itree (RndEvent unit) T) :
  dinterp_E (Vis (Rnd tt len) k) =1
    \dlet_(bytes <- dunif_bytes (Z.to_nat len))
      dinterp_E (k (tt, bytes)).
Proof.
move=> x; rewrite /dinterp_E.
(* Step 1: shift limit by 1 (dinterp_E' at 0 is dnull, absorbed by dlim) *)
rewrite -(dlim_bump (fun n => dinterp_E' (observe (Vis (Rnd tt len) k)) n) x) /=.
(* Goal: dlim (fun n => \dlet_(bytes <- ...) dinterp_E' (observe (k (tt,bytes))) n) x
       = \dlet_(bytes <- ...) dlim (fun n => dinterp_E' (observe (k (tt,bytes))) n) x *)
apply: __admitted__dlim_let.
by move=> bytes n m hle; exact: dinterp_E'_mono.
Qed.

(* Key lemma: dinterp_E' n is bounded by dinterp_E of a eutt-related tree *)
(* one_way: for each fuel n on the left, there exists fuel m on the right
   such that the n-step approximation of t is bounded by the m-step
   approximation of t'. Follows the pattern of distr.one_way. *)
Lemma one_way (t t' : itree (RndEvent unit) T) :
  eutt eq t t' ->
  forall n, exists m,
    dinterp_E' (observe t) n <=1 dinterp_E' (observe t') m.
Proof.
move=> h n; elim: n t t' h => [|n hind] t t' h.
- by exists 0%nat => x; exact: lef_dnull.
elim/(distr.eqit_ind (E := RndEvent unit) (R := T) (R' := T)): h =>
  [ t_ t'_ r1 r2 -> -> h
  | t_ t'_ ot ot' -> -> h
  | t_ t'_ A e k k' -> -> h
  | t_ ot t'_ -> _ h [m hm]
  | t'_ t_ ot' -> _ h [m hm] ].
- (* Ret/Ret *)
  subst r2; exists 1%nat => /= x; exact: lexx.
- (* Tau/Tau *)
  move: h => /hind [m hle]; by exists (S m).
- (* Vis/Vis *)
  case: e k k' h => scs len k k' h.
  admit.
- (* Tau left *)
  apply/hind/distr.eqitE; exact: h.
- (* Tau right *)
  exists (S m); exact: hm.
Admitted.

(* dinterp_E respects eutt.
   Proof sketch: by one_way in both directions + dlim_ub + transitivity.
   Direction 1: for each n, one_way gives m s.t. dinterp_E' t1 n <=1 dinterp_E' t2 m.
     By dlim_ub, dinterp_E' t2 m <=1 dlim (dinterp_E' t2) = dinterp_E t2.
     So dinterp_E' t1 n <=1 dinterp_E t2. Then leub_dlim gives dinterp_E t1 <=1 dinterp_E t2.
   Direction 2: symmetric via eqit_flip. *)
Lemma dinterp_E_eutt (t1 t2 : itree (RndEvent unit) T) :
  eutt eq t1 t2 -> dinterp_E t1 =1 dinterp_E t2.
Proof. Admitted.

End DINTERP_E_PROPS.

(* ** Bind distribution through dinterp_E
 * -------------------------------------------------------------------- *)

Section DINTERP_E_BIND.

Context {T U : choiceType}.

Lemma dinterp_E_bind (t : itree (RndEvent unit) T)
    (k : T -> itree (RndEvent unit) U) :
  dinterp_E (ITree.bind t k) =1
    \dlet_(x <- dinterp_E t) dinterp_E (k x).
Proof.
Admitted.

End DINTERP_E_BIND.

(* ** dinterp_E composed with interp_Err
 * -------------------------------------------------------------------- *)

(* ** Full pipeline: interp_Err + execS_to_dfstate + dinterp_E
 *
 * Avoids the need for execS to be a choiceType by composing
 * the error handling and distribution interpretation in one step.
 * -------------------------------------------------------------------- *)

Section DINTERP_ERR.

(* Full pipeline for function-level: itree E fstate -> {distr dfstate / R} *)
Definition dinterp_Err_f (t : itree E fstate) : {distr dfstate / R} :=
  dinterp_E (ITree.bind (@interp_Err (RndEvent unit) _ t)
    (fun x => Ret (execS_to_dfstate x))).

(* Full pipeline for command-level: itree E estate -> {distr dstate / R} *)
Definition dinterp_Err_s (t : itree E estate) : {distr dstate / R} :=
  dinterp_E (ITree.bind (@interp_Err (RndEvent unit) _ t)
    (fun x => Ret (execS_to_dstate x))).

(* Ret case for functions *)
Lemma dinterp_Err_f_ret (v : fstate) :
  dinterp_Err_f (Ret v) =1 @dunit R _ (DFSok v).
Proof.
rewrite /dinterp_Err_f.
have h : ITree.bind (@interp_Err (RndEvent unit) _ (Ret v : itree E fstate))
           (fun x => Ret (execS_to_dfstate x)) ≈
         Ret (DFSok v).
  rewrite /interp_Err unfold_interp_exec /= bind_ret_l /=. reflexivity.
by move=> x; rewrite (dinterp_E_eutt h) dinterp_E_ret.
Qed.

(* Ret case for commands *)
Lemma dinterp_Err_s_ret (v : estate) :
  dinterp_Err_s (Ret v) =1 @dunit R _ (DSok v).
Proof.
rewrite /dinterp_Err_s.
have h : ITree.bind (@interp_Err (RndEvent unit) _ (Ret v : itree E estate))
           (fun x => Ret (execS_to_dstate x)) ≈
         Ret (DSok v).
  rewrite /interp_Err unfold_interp_exec /= bind_ret_l /=. reflexivity.
by move=> x; rewrite (dinterp_E_eutt h) dinterp_E_ret.
Qed.

(* iresult decomposition *)
Lemma dinterp_Err_s_iresult (s0 : estate) (r : exec estate) :
  dinterp_Err_s (iresult (E := E) s0 r) =1
    match r with
    | Ok v => @dunit R _ (DSok v)
    | Error e => @dunit R _ (DSerr e)
    end.
Proof.
Admitted.

(* Bind for command level *)
Lemma dinterp_Err_s_bind (t : itree E estate) (k : estate -> itree E estate) :
  dinterp_Err_s (ITree.bind t k) =1
    \dlet_(x <- dinterp_Err_s t)
      match x with
      | DSok v => dinterp_Err_s (k v)
      | DSerr e => @dunit R _ (DSerr e)
      end.
Proof.
Admitted.

End DINTERP_ERR.

(* ** ITree-based denotational semantics
 * -------------------------------------------------------------------- *)

Definition itree_dsem_call (p : uprog) (fn : funname) (fs : fstate)
    : {distr dfstate / R} :=
  let t : itree E fstate := isem_fun (E := E) p tt fn fs in
  let t_err : itree (RndEvent unit) (execS fstate) :=
    interp_Err t in
  let t_df : itree (RndEvent unit) dfstate :=
    ITree.bind t_err (fun x => Ret (execS_to_dfstate x)) in
  dinterp_E t_df.

(* ** Fuel-indexed ITree truncation
 * -------------------------------------------------------------------- *)

Section ISEM_FUN_TRUNC.

Variable (p : uprog).

Fixpoint isem_fun_trunc (n : nat) (fn : funname) (fs : fstate)
    : itree E fstate :=
  match n with
  | O => ITree.spin
  | S n' =>
    let handler : forall T, (recCall +' E) T -> itree E T :=
      fun T e =>
        match e with
        | inl1 rc =>
            match rc in recCall R return itree E R with
            | RecCall _ fn' fs' => isem_fun_trunc n' fn' fs'
            end
        | inr1 e0 => trigger e0
        end in
    interp handler (isem_fun_body p tt fn fs)
  end.

Definition itree_dsem_call_n (n : nat) (fn : funname) (fs : fstate)
    : {distr dfstate / R} :=
  let t := isem_fun_trunc n fn fs in
  let t_err := interp_Err t in
  let t_df := ITree.bind t_err (fun x => Ret (execS_to_dfstate x)) in
  dinterp_E t_df.

End ISEM_FUN_TRUNC.

(* ** Fuel-indexed correspondence: dsem_call_n =1 itree_dsem_call_n
 * -------------------------------------------------------------------- *)

Section FUEL_CORRESPONDENCE.

Variable (p : uprog).

(* Base case: itree_dsem_call_n 0 = dfnone.
   isem_fun_trunc 0 = spin. After interp_Err and bind, still a Tau-loop.
   dinterp_E of a Tau-loop is dnull.
   Proof uses: interp_Err spin ≈ spin, bind spin k ≈ spin (ITree library facts),
   dinterp_E_eutt, dinterp_E_spin. *)
Lemma itree_dsem_call_n_0 (fn : funname) (fs : fstate) :
  itree_dsem_call_n p 0 fn fs =1 dfnone.
Proof. Admitted.

Lemma dsem_call_n_eq_itree (n : nat) (fn : funname) (fs : fstate) :
  dsem_call_n p n fn fs =1 itree_dsem_call_n p n fn fs.
Proof.
elim: n fn fs => [|n ih] fn fs.
- (* n = 0 *)
  by move=> x; rewrite /= /dfnone itree_dsem_call_n_0.
- (* n = S n' *)
  admit.
Admitted.

End FUEL_CORRESPONDENCE.

(* ** Limit characterization: itree_dsem_call = dlim itree_dsem_call_n
 * -------------------------------------------------------------------- *)

Section LIMIT_CHAR.

Variable (p : uprog).

Lemma itree_dsem_call_eq_lim (fn : funname) (fs : fstate) :
  itree_dsem_call p fn fs =1
    @dlim R _ (fun n => itree_dsem_call_n p n fn fs).
Proof.
Admitted.

End LIMIT_CHAR.

(* ** Equivalence with the direct denotational semantics
 * -------------------------------------------------------------------- *)

Theorem dsem_call_eq_itree (p : uprog) (fn : funname) (fs : fstate) :
  dsem_call p fn fs =1 itree_dsem_call p fn fs.
Proof.
move=> x; rewrite itree_dsem_call_eq_lim /dsem_call.
by apply: eq_dlim => n; exact: dsem_call_n_eq_itree.
Qed.

End DSEM_ITREE.
