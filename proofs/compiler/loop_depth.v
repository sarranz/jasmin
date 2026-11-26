(* -------------------------------------------------------------------- *)
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat.
(* ------- *) Require Import expr.
Import Utf8.

(* Syntactic hardware-loop nesting depth of a source ([uprog]) function's
   body: an [FIrepeat] loop nests one level deeper than its enclosing
   body, while an [FIrange] loop (compiled to ordinary control flow, not
   a hardware loop) does not add depth; a function call contributes the
   already-computed loop depth of the callee rather than the caller's
   own recursion. Mirrors [call_depth.v]; see PLAN-acc-loop-impl.md,
   Stage 6. *)

Section ASM_OP.

Context `{asmop : asmOp}.

Fixpoint ldepth_i (call : funname -> nat) (i : instr) {struct i} : nat :=
  let: MkI _ ir := i in ldepth_i_r call ir

with ldepth_i_r (call : funname -> nat) (ir : instr_r) {struct ir} : nat :=
  let fix ldepth_c (c : cmd) {struct c} :=
    if c is i :: c' then maxn (ldepth_i call i) (ldepth_c c') else 0
  in
  match ir with
  | Cassgn _ _ _ _ | Copn _ _ _ _ | Csyscall _ _ _ | Cassert _ => 0
  | Cif    _  c1 c2            => maxn (ldepth_c c1) (ldepth_c c2)
  | Cfor   (FIrepeat _) c      => 1 + ldepth_c c
  | Cfor   (FIrange _ _ _ _) c => ldepth_c c
  | Cwhile _ c1 _ _ c2         => maxn (ldepth_c c1) (ldepth_c c2)
  | Ccall  _ g _               => call g
  end.

Definition ldepth_c (call : funname -> nat) (c : cmd) : nat :=
  foldl (fun acc i => maxn acc (ldepth_i call i)) 0 c.

Fixpoint loop_fun (p : uprog) (fuel : nat) (fn : funname) {struct fuel} : nat :=
  match fuel with
  | 0 => 0
  | fuel'.+1 =>
    if get_fundef (p_funcs p) fn is Some fd then
      ldepth_c (loop_fun p fuel') (f_body fd)
    else 0
  end.

Definition loop_depth (p : uprog) (fn : funname) : nat :=
  loop_fun p (size (p_funcs p)) fn.

(* -------------------------------------------------------------------- *)
(* Facts needed by later stages to relate [ldepth_c] of a command to
   [ldepth_c]/[ldepth_i] of its sub-parts. *)

Lemma foldl_maxn_acc (g : instr -> nat) (c : cmd) (acc : nat) :
  foldl (fun acc i => maxn acc (g i)) acc c
  = maxn acc (foldl (fun acc i => maxn acc (g i)) 0 c).
Proof.
elim: c acc => [ | i c IH] acc /=.
- by rewrite maxn0.
- by rewrite max0n IH (IH (g i)) maxnA.
Qed.

Lemma ldepth_c_cons call i c :
  ldepth_c call (i :: c) = maxn (ldepth_i call i) (ldepth_c call c).
Proof. by rewrite /ldepth_c /= max0n foldl_maxn_acc. Qed.

Lemma ldepth_c_cat call c1 c2 :
  ldepth_c call (c1 ++ c2) = maxn (ldepth_c call c1) (ldepth_c call c2).
Proof.
elim: c1 => [ | i c1 IH] /=.
- by rewrite max0n.
- by rewrite !ldepth_c_cons IH maxnA.
Qed.

(* Bridges the [let fix] copy of [ldepth_c] hidden inside [ldepth_i_r]'s
   body with the top-level [ldepth_c] above, so the sub-command bounds
   below can be stated (and later used) in terms of the latter. *)
Lemma ldepth_c_rec call c :
  (fix ldepth_c (c0 : cmd) : nat :=
     if c0 is i :: c' then maxn (ldepth_i call i) (ldepth_c c') else 0) c
  = ldepth_c call c.
Proof. elim: c => [ | i c IH] //=. by rewrite IH ldepth_c_cons. Qed.

Lemma ldepth_c_if ii call e c1 c2 :
  ldepth_i call (MkI ii (Cif e c1 c2))
  = maxn (ldepth_c call c1) (ldepth_c call c2).
Proof. by rewrite /ldepth_i /ldepth_i_r /= !ldepth_c_rec. Qed.

Lemma ldepth_c_while ii call a c1 e info c2 :
  ldepth_i call (MkI ii (Cwhile a c1 e info c2))
  = maxn (ldepth_c call c1) (ldepth_c call c2).
Proof. by rewrite /ldepth_i /ldepth_i_r /= !ldepth_c_rec. Qed.

Lemma ldepth_c_for ii call fi c :
  ldepth_c call c <= ldepth_i call (MkI ii (Cfor fi c)).
Proof.
rewrite /ldepth_i /ldepth_i_r /=.
by case: fi => [x d elo ehi | e] /=; rewrite ldepth_c_rec ?leqnSn ?leqnn.
Qed.

Lemma ldepth_c_for_repeat ii call e c :
  ldepth_i call (MkI ii (Cfor (FIrepeat e) c)) = (ldepth_c call c).+1.
Proof. by rewrite /ldepth_i /ldepth_i_r /= ldepth_c_rec. Qed.

Lemma ldepth_c_if_l ii call e c1 c2 :
  ldepth_c call c1 <= ldepth_i call (MkI ii (Cif e c1 c2)).
Proof. by rewrite ldepth_c_if leq_maxl. Qed.

Lemma ldepth_c_if_r ii call e c1 c2 :
  ldepth_c call c2 <= ldepth_i call (MkI ii (Cif e c1 c2)).
Proof. by rewrite ldepth_c_if leq_maxr. Qed.

Lemma ldepth_c_while_l ii call a c1 e info c2 :
  ldepth_c call c1 <= ldepth_i call (MkI ii (Cwhile a c1 e info c2)).
Proof. by rewrite ldepth_c_while leq_maxl. Qed.

Lemma ldepth_c_while_r ii call a c1 e info c2 :
  ldepth_c call c2 <= ldepth_i call (MkI ii (Cwhile a c1 e info c2)).
Proof. by rewrite ldepth_c_while leq_maxr. Qed.

End ASM_OP.
