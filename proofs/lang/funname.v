(* ** Imports and settings *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.
From Coq Require Import Uint63 Sint63.
From HB Require Import structures.
Require Import strings utils gen_map.

Module FunName.

  Record t := mkFunname
    {
      fn_tag  : int;
      fn_name : string;
    }.

  Definition tag (x : t) : int := fn_tag x.

  Definition eqb (x y : t) : bool :=
    [&& (fn_tag x =? fn_tag y)%uint63
      &  fn_name x == fn_name y ].

  Lemma eq_axiom : Equality.axiom eqb.
  Proof.
    move=> [tx nx] [ty ny]; rewrite /eqb /=; apply: (iffP andP).
    - by case=> /Uint63.eqb_spec /= -> /eqP ->.
    by case=> -> ->; split; rewrite ?Uint63.eqb_refl ?eqxx.
  Qed.

  HB.instance Definition _ := hasDecEq.Build t eq_axiom.
  Definition t_eqType : eqType := t.

  Definition cmp (x y : t) : comparison :=
    Lex (int_cmp (fn_tag x) (fn_tag y))
        (string_cmp (fn_name x) (fn_name y)).

  Lemma cmpO : Cmp cmp.
  Proof.
    constructor=> [x y | y x z c | [tx nx] [ty ny]];
    rewrite /cmp !Lex_lex.
    + by apply: lex_sym; [apply: cmp_sym | apply: cmp_sym].
    + by apply: lex_trans => /=; apply: cmp_ctrans.
    by move=> /lex_eq [] /= /(@cmp_eq _ _ int_cmpO) ->
      /(@cmp_eq _ _ stringO) ->.
  Qed.

  #[global] Existing Instance cmpO.

  Module CmpT.
    Definition t : eqType := t_eqType.
    Definition cmp : t -> t -> comparison := cmp.
    Definition cmpO : Cmp cmp := cmpO.
  End CmpT.

End FunName.

#[global] Canonical funname_eqType := FunName.t_eqType.

Module Mf <: MAP := Mmake FunName.CmpT.
Module Sf := Smake FunName.CmpT.
Module SfP := MSetEqProperties.EqProperties Sf.
Module SfD := MSetDecide.WDecide Sf.

Definition funname := FunName.t.
