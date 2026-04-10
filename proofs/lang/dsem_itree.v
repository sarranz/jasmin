(* * ITree-based denotational probabilistic semantics for Jasmin *)

(* ** Imports and settings *)
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype ssralg.
From mathcomp Require Import choice fintype order seq.
From mathcomp.classical Require Import boolp.
From mathcomp.reals Require Import reals.
From mathcomp.experimental_reals Require Import realseq distr.

From ITree Require Import ITree ITreeFacts.

Require Import xseq.
Require Import
  array type expr gen_map warray_ sem_type sem_op_typed
  values varmap expr_facts low_memory syscall_sem psem_defs.
Require Import psem_core it_sems_core it_exec.
Require Import flag_combination sem_params.
Require Import dpsem.

Import Utf8.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope Z_scope.
Local Open Scope seq_scope.
Local Close Scope vm_scope.

Import GRing.Theory Order.Theory.

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

(* dinterp_E respects eutt *)
Lemma dinterp_E_eutt (t1 t2 : itree (RndEvent unit) T) :
  eutt eq t1 t2 -> dinterp_E t1 =1 dinterp_E t2.
Proof.
Admitted.

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
Admitted.

(* Ret case for commands *)
Lemma dinterp_Err_s_ret (v : estate) :
  dinterp_Err_s (Ret v) =1 @dunit R _ (DSok v).
Proof.
Admitted.

(* iresult decomposition *)
Lemma dinterp_Err_s_iresult (s : estate) (r : exec estate) :
  dinterp_Err_s (iresult (E := E) s r) =1
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

Lemma dsem_call_n_eq_itree (n : nat) (fn : funname) (fs : fstate) :
  dsem_call_n p n fn fs =1 itree_dsem_call_n p n fn fs.
Proof.
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
Admitted.

End DSEM_ITREE.
