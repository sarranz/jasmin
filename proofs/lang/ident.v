(* ** Imports and settings *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.
From Coq Require Import Uint63 Sint63.
From HB Require Import structures.
Require Import strings utils gen_map wsize.

Module Cident.

  Record t := mkCident
    {
      c_tag : int;
      c_name : string;
      c_kind : wsize.v_kind;
    }.

  Definition tag (x : t) : int := c_tag x.
  Definition id_name (x : t) : string := c_name x.
  Definition id_kind (x : t) : wsize.v_kind := c_kind x.

  Definition eqb (x y : t) : bool :=
    [&& (c_tag x =? c_tag y)%uint63
      , c_name x == c_name y
      & c_kind x == c_kind y ].

  Lemma eq_axiom : Equality.axiom eqb.
  Proof.
    move=> [tx nx kx] [ty ny ky]; rewrite /eqb /=; apply: (iffP and3P).
    - by case=> /Uint63.eqb_spec /= -> /eqP -> /eqP ->.
    by case=> -> -> ->; split; rewrite ?Uint63.eqb_refl ?eqxx.
  Qed.

  HB.instance Definition _ := hasDecEq.Build t eq_axiom.
  Definition t_eqType : eqType := t.

  Definition cmp (x y : t) : comparison :=
    Lex (int_cmp (tag x) (tag y))
      (Lex (string_cmp (id_name x) (id_name y))
           (v_kind_cmp (id_kind x) (id_kind y))).

  Lemma cmpO : Cmp cmp.
  Proof.
    constructor=> [x y | y x z c | [tx nx kx] [ty ny ky]];
    rewrite /cmp !Lex_lex.
    + by apply: lex_sym; [apply: cmp_sym | apply: lex_sym; apply: cmp_sym].
    + by apply: lex_trans => /=;
        [apply: cmp_ctrans | apply: lex_trans => /=; apply: cmp_ctrans].
    by move=> /lex_eq [] /= /(@cmp_eq _ _ int_cmpO) ->
      /lex_eq [] /= /(@cmp_eq _ _ stringO) -> /(@cmp_eq _ _ v_kindO) ->.
  Qed.

  #[global] Existing Instance cmpO.

End Cident.

#[global] Canonical ident_eqType := Cident.t_eqType.

Module Type IDENT.
  Definition ident := Cident.t.
  Declare Module Mid : MAP with Definition K.t := Cident.t_eqType.
End IDENT.

Module Ident <: IDENT.

  Definition ident := Cident.t.
  Definition id_name : ident -> string := Cident.id_name.
  Definition id_kind : ident -> wsize.v_kind := Cident.id_kind.

  Module CmpT.
    Definition t : eqType := Cident.t_eqType.
    Definition cmp : t -> t -> comparison := Cident.cmp.
    Definition cmpO : Cmp cmp := Cident.cmpO.
  End CmpT.

  Module Mid <: MAP := Mmake CmpT.

End Ident.
