From Coq Require Import Relations.
From mathcomp Require Import
  all_ssreflect
  all_algebra.

Require Import
  fexpr_sem
  label
  linear
  linear_sem
  one_varmap
  psem
  psem_facts.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


(* -------------------------------------------------------------------------- *)
(* Semantics of assembly instructions. *)

(* Rewrite an equality in the context that's related to the execution of
   assembly instructions. *)
#[local]
Ltac t_rewrite_eq :=
  match goal with
  | [ h : sem_rexprs _ _ = _ |- _ ] => rewrite !h /=
  | [ h : sem_rexpr _ _ _ = _ |- _ ] => rewrite !h /=
  | [ h : get_var _ _ = _ |- _ ] => rewrite !h /=
  | [ h : truncate_word _ _ = _ |- _ ] => rewrite !h /=
  | [ h : to_word _ _ = _ |- _ ] => rewrite !h /=
  | [ h : write_lexprs _ _ _ = _ |- _ ] => rewrite !h /=
  | [ h : write_lexpr _ _ _ = _ |- _ ] => rewrite !h /=
  | [ h : write _ _ _ = _ |- _ ] => rewrite !h /=
  end.

(* Most assembly instructions execute as follows:
   1. Unfold instruction execution definitions, e.g. [eval_instr].
   2. Rewrite argument hypotheses, i.e. [sem_pexpr].
   3. Unfold casting definitions in result, e.g. [zero_extend] and
      [pword_of_word].
   4. Rewrite result hypotheses, i.e. [write_lval]. *)
Ltac t_lopn :=
  rewrite /eval_instr /= /sem_sopn /= /exec_sopn /get_gvar /=;
  repeat t_rewrite_eq;
  rewrite /to_estate /= /of_estate /= /with_vm /=;
  rewrite ?zero_extend_u ?pword_of_wordE;
  repeat t_rewrite_eq.


(* -------------------------------------------------------------------------- *)

Section LSEM_INVARIANT.

  (* This lemma models the situation where we insert assembly code derived from
     each element in some list [xs].
     The function [get_lopn] maps elements [x] to assembly code, and [P] is a
     state relation parameterized by [xs] (relating the states before and after
     executing the assembly instructions).
     This lemma simply states that we only need to prove that [P] holds for each
     [x] in [xs]. *)

  Context
    {asm_op syscall_state : Type}
    {ep : EstateParams syscall_state}
    {spp : SemPexprParams}
    {sip : SemInstrParams asm_op syscall_state}
    {ovmi : one_varmap_info}
    (E X : Type)
    (get_lopn : X -> result E (seq lopn_args))
    (P : seq X -> relation estate).

  (* Executing [get_lopn x] succeeds and [P x s s'] holds. *)
  Definition get_lopn_invariant x : Prop :=
    forall lp scs vm m fn pre pos args ii,
      get_lopn x = ok args
      -> let: c := map (li_of_lopn_args ii) args in
         is_linear_of lp fn (pre ++ c ++ pos)
         -> exists scs' vm' m',
              let: s :=
                {|
                  escs := scs;
                  evm := vm;
                  emem := m;
                |}
              in
              let: ls := of_estate s fn (size pre) in
              let: s' :=
                {|
                  escs := scs';
                  evm := vm';
                  emem := m';
                |}
              in
              let: ls' := of_estate s' fn (size pre + size args) in
              lsem lp ls ls' /\ P [:: x ] s s'.

  (* Executing several [get_lopn x]s succeeds and [P xs s s'] holds. *)
  Definition map_get_lopn_invariant xs : Prop :=
    forall lp scs vm m fn pre pos args ii,
      mapM get_lopn xs = ok args
      -> let: lcmd := conc_map (map (li_of_lopn_args ii)) args in
         is_linear_of lp fn (pre ++ lcmd ++ pos)
         -> exists scs' vm' m',
              let: s :=
                {|
                  escs := scs;
                  evm := vm;
                  emem := m;
                |}
              in
              let: ls := of_estate s fn (size pre) in
              let: s' :=
                {|
                  escs := scs';
                  evm := vm';
                  emem := m';
                |}
              in
              let: ls' := of_estate s' fn (size pre + size lcmd) in
              lsem lp ls ls' /\ P xs s s'.

  Context
    (Prefl : reflexive estate (P [::]))
    (Pconcat :
       forall xs ys s0 s1 s2,
         P xs s0 s1
         -> P ys s1 s2
         -> P (xs ++ ys) s0 s2).

  Lemma map_get_lopn_invariantP xs :
    (forall x, List.In x xs -> get_lopn_invariant x)
    -> map_get_lopn_invariant xs.
  Proof.
    move=> h lp scs vm m fn pre pos args ii.
    rewrite /of_estate /=.
    move: scs vm m pre args.
    elim: xs h => [| x xs hind ] /= h scs vm m pre args hxs hbody.

    - move: hxs => [?]; subst args.
      rewrite addn0.
      eexists; eexists; eexists; split; first exact: rt_refl.
      exact: Prefl.

    move: hxs.
    t_xrbindP=> argsx hx argsxs hxs ?; subst args.

    move: hbody.
    rewrite /conc_map /=.
    rewrite -!catA.
    move=> hbody.

    have hinv : get_lopn_invariant x.
    - apply: h. by left.

    have [scs0 [vm0 [m0 [hsem0 hzero0]]]] :=
      hinv lp scs vm m fn _ _ _ _ hx hbody.
    clear hx.

    rewrite catA in hbody.
    have h' :
      forall y, List.In y xs -> get_lopn_invariant y.
    - move=> y hy. apply: h. by right.

    have [scs' [vm' [m' [hsem' hzero']]]] := hind h' scs0 vm0 m0 _ _ hxs hbody.
    clear h hxs h'.

    exists scs', vm', m';
      split;
      last exact: (Pconcat hzero0 hzero').

    apply: (lsem_trans hsem0).
    move: hsem'.
    rewrite /of_estate size_cat /=.
    by rewrite size_cat size_map !addnA.
  Qed.

End LSEM_INVARIANT.

Section LPROG_EXTEND.

  (* This models the behaviour of some passes of the compiler: appending a piece
     of code at the end of a function body. *)

  Definition is_prefix {X} (xs ys : seq X) : Prop :=
    exists zs, ys = xs ++ zs.

  #[local]
  Lemma onth_prefix {X} (xs ys : seq X) n x :
    oseq.onth xs n = Some x
    -> is_prefix xs ys
    -> oseq.onth ys n = Some x.
  Proof.
    move=> hnth [tail htail].
    elim: xs ys n hnth htail => //= x0 xs hi ys n.
    case: n.
    - move=> [?]; subst x0. by move=> ->.
    move=> n hnth -> /=.
    by apply: (hi _ _ hnth).
  Qed.

  Context
    {asm_op syscall_state : Type}
    {ep : EstateParams syscall_state}
    {spp : SemPexprParams}
    {sip : SemInstrParams asm_op syscall_state}
    {ovm_i : one_varmap_info}
    (lp lp' : lprog).

  Definition lprog_extend lp lp' :=
    forall fn lfd,
      get_fundef (lp_funcs lp) fn = Some lfd
      -> exists2 lfd',
           get_fundef (lp_funcs lp') fn = Some lfd'
           & is_prefix (lfd_body lfd) (lfd_body lfd').

  Context (hextend : lprog_extend lp lp').

  #[local]
  Lemma get_fundefP fn lfd :
    get_fundef (lp_funcs lp) fn = Some lfd
    -> exists lfd',
         get_fundef (lp_funcs lp') fn = Some lfd'.
  Proof. move=> h. have [lfd' hlfd' _] := hextend h. by exists lfd'. Qed.

  #[local]
  Lemma find_instrP ls i :
    find_instr lp ls = Some i
    -> find_instr lp' ls = Some i.
  Proof.
    rewrite /find_instr.
    case hlfd: get_fundef => [lfd | //] hget.
    have [lfd' hlfd'] := get_fundefP hlfd.
    rewrite hlfd'.
    have [lfd'' hlfd'' hpre] := hextend hlfd.
    move: hlfd''.
    rewrite hlfd'.
    move=> [?]; subst lfd''.
    by rewrite (onth_prefix hget hpre).
  Qed.

  #[local]
  Lemma get_label_after_pcP s lbl :
    get_label_after_pc lp s = ok lbl
    -> get_label_after_pc lp' s = ok lbl.
  Proof.
    rewrite /get_label_after_pc.
    case hfind: find_instr => [i|//].
    by rewrite (find_instrP hfind).
  Qed.

  #[local]
  Lemma eval_instrP i ls ls' :
    eval_instr lp i ls = ok ls'
    -> eval_instr lp' i ls = ok ls'.
  Proof.
    move: i => [ii i].
    rewrite /eval_instr /=.
    case: i => //=.
  Admitted.

  #[local]
  Lemma lsem1P ls ls' :
    lsem1 lp ls ls'
    -> lsem1 lp' ls ls'.
  Proof.
    rewrite /lsem1 /step /find_instr.
    case hlfd: get_fundef => [lfd | //].
    have [lfd' hlfd'] := get_fundefP hlfd.
    rewrite hlfd'.

    case hpc: oseq.onth => [i | //].
    have -> : oseq.onth (lfd_body lfd') (lpc ls) = Some i.
    - have : find_instr lp' ls = Some i.
      + apply: find_instrP. rewrite /find_instr. by rewrite hlfd.
      rewrite /find_instr.
      case h0: get_fundef => [lfd0 | //].
      move: h0.
      rewrite hlfd'.
      by move=> [->].

    exact: eval_instrP.
  Qed.

  Lemma lprog_extend_lsem ls ls' :
    lsem lp ls ls'
    -> lsem lp' ls ls'.
  Proof.
    move: ls'.
    apply: clos_refl_trans_ind_left; first exact: rt_refl.
    move=> ls0 ls1 hsem hsem' hstep.
    apply: (lsem_step_end hsem').
    apply: lsem1P.
    exact: hstep.
  Qed.

End LPROG_EXTEND.
