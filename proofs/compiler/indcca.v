(* Indistinguishability under chosen ciphertext attack (INDCCA). *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Uniform Inductive Parameters.

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
.
Import Monads.

Require Import distr_extra dinterp.

#[local] Open Scope order_scope.
#[local] Open Scope ring_scope.

Notation "'let*' p ':=' c1 'in' c2" :=
  (@ITree.bind _ _ _ c1 (fun p => c2))
  (at level 61, p as pattern, c1 at next level, right associativity).

Notation "x |> f" := (f x) (only parsing, at level 25).

Section MAIN.

Context {R : realType}.

Notation distr := (distr R).
Notation Rnd := (Rnd (R := R)).

Section GAME.

  (* Security games for implicitly rejecting KEMs (penalty style).

     The challenger [(cmem, cmi, GenKey, Encap, Decap)] is stateful. It
     comprises a memory type [cmem] with an initial memory [cmi : cmem], and:
     - A key generation algorithm
       [GenKey : cmem -> itree Rnd ((pkey * skey) * cmem)].
     - An encapsulation algorithm
       [Encap : pkey -> cmem -> itree Rnd ((ctxt * msg) * cmem)].
     - A decapsulation algorithm
       [Decap : skey -> ctxt -> cmem -> itree Rnd (msg * cmem)].
     Each algorithm takes the current memory and returns the updated one.

     The adversary [(Query, Guess)] comprises:
     - A first stage [Query : pkey -> itree (Dec +' Rnd) advmem] that queries
       the decapsulation algorithm and produces an adversary advmem.
     - A second stage
       [Guess : advmem -> pkey -> ctxt -> msg -> itree (Dec +' Rnd) bool]
       that performs a guess and can query the decapsulation algorithm.

     The adversary is allowed to make at most [Q] queries to the decapsulation
     oracle. All queries are logged and answered honestly. The adversary is
     penalized (game returns false) if they query the chosen ciphertext during
     the guess phase.

     The security game is as follows, where the challenger memory [mem] is
     threaded through every call (including the decapsulation queries made
     by the adversary), starting from [cmi]:
         (pk, sk), mem <- GenKey(mem)
         st <- Query[Decap(sk, mem)](pk)
         (ct, m_0), mem <- Encap(pk, mem)
         m_1 <- random message
         b <- random boolean
         g <- Guess[Decap(sk, mem)](st, pk, ct, m_b)
         return (g == b && ct not queried in guess phase
                        && number of queries <= Q) *)

  Context
    {pkey skey advmem : Type}
    {ctxt : choiceType}
    {msg : finType}
  .

  Variant Dec : Type -> Type :=
  | Decapsulate : ctxt -> Dec msg.

  Record Challenger :=
    {
      cmem : Type;
      cmi : cmem;
      GenKey : cmem -> itree Rnd ((pkey * skey) * cmem);
      Encap : pkey -> cmem -> itree Rnd ((ctxt * msg) * cmem);
      Decap : skey -> ctxt -> cmem -> itree Rnd (msg * cmem);
    }.

  (* Adversary can run Encap by themselves because they have [pk]. *)
  Record Adversary :=
    {
      Query : pkey -> itree (Dec +' Rnd) advmem;
      Guess : advmem -> pkey -> ctxt -> msg -> itree (Dec +' Rnd) bool;
    }.

  Context (C : Challenger) (A : Adversary) (Q : nat).

  (* Log for the game.
     It tracks the list of ciphertexts that have been queried. *)
  Definition S : Type := seq ctxt.

  (* Log a decapsulation query and the new challenger memory. *)
  Definition log E `{stateE (S * C.(cmem)) -< E} (c : ctxt) (m : C.(cmem)) :
    itree E unit :=
    let* (l, _) := get in put (c :: l, m).

  (* Handle a decapsulation query from the attacker, given a secret key [sk].
     The query is answered honestly and then logged along with the new
     challenger memory. *)
  Definition handle_Dec (sk : skey) :
    Dec ~> itree (stateE (S * C.(cmem)) +' Rnd) :=
    fun T e =>
      let 'Decapsulate c := e in
      let* (_, m) := get in
      let* (r, m') := translate inr1 (C.(Decap) sk c m) in
      let* _ := log c m' in
      Ret r.

  Definition interact
    (X : Type)
    (A : itree (Dec +' Rnd) X)
    (sk : skey)
    (m : C.(cmem)) :
    itree Rnd ((S * C.(cmem)) * X) :=
    let t := interp (case_ (handle_Dec sk) inr_) A in
    run_state t ([::], m).

  Definition flip : itree Rnd bool := trigger (GetRnd (dunif bool)).
  Definition rnd_msg : itree Rnd msg := trigger (GetRnd (dunif msg)).

  (* The trace records the query and guess phase logs, and the chosen
     ciphertext. *)
  Definition trace : Type := S * S * ctxt.

  Definition game : itree Rnd (bool * trace) :=
    let* ((pk, sk), m) := C.(GenKey) C.(cmi) in
    let* ((lq, m), amem) := interact (A.(Query) pk) sk m in
    let* ((ct, m0), m) := C.(Encap) pk m in
    let* m1 := rnd_msg in
    let* b := flip in
    let mb := if b then m1 else m0 in
    let* ((lg, _), g) := interact (A.(Guess) amem pk ct mb) sk m in
    Ret (g == b, (lq, lg, ct)).

  Definition dgame : distr (bool * trace)%type := dinterp game.

  Definition valid (t : trace) : bool :=
    let '(lq, lg, ct) := t in
    [&& ct \notin lg & (size lq + size lg <= Q)%N ].

  Definition advantage : R :=
    `| \P_[ dgame ] (fun '(b, t) => b && valid t) - 1/2 |.

End GAME.

Arguments Challenger : clear implicits.
Arguments Adversary : clear implicits.

Section REDUCE.

  Context
    {pkey skey advmem : Type}
    {ctxt : choiceType}
    {msg : finType}
  .

  Notation advantage := (@advantage pkey skey advmem ctxt msg).

  (* Every adversary for [C1] can be converted into an adversary for [C2] that
     performs at most the same number of oracle queries and whose advantage is
     at least that of the former's. *)
  Definition reduction C1 C2 :=
    forall A1 Q, advantage C1 A1 Q = advantage C2 A1 Q.

End REDUCE.

End MAIN.
