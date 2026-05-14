(* ** Imports and settings *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.
From Coq Require Import Uint63 Sint63 Utf8.
From HB Require Import structures.
Require Import strings utils gen_map tagged wsize.

(* Concrete ident implementation.
   [Cident.t] is the record type.  [WrapIdent.t] is a transparent alias;
   [Extract Constant ident.WrapIdent.t] overrides the *type* name in every
   OCaml function signature that mentions it, so [Tident.eqb] and
   [Tident.cmp] extract as [CoreIdent.Cident.t -> CoreIdent.Cident.t -> ...].
   [Tident.CmpT] is nested so the extractor does not collapse it to [Cident],
   preserving the [Obj.magic] bridge that [Mmake] needs. *)
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

End Cident.

(* Necessary for extraction *)
Module WrapIdent.
  Definition t := Cident.t.
End WrapIdent.

Module Tident <: TAGGED.

  Definition t := WrapIdent.t.
  Definition tag := Cident.tag.

  Definition t_eqb (x y : t) : bool :=
    [&& (tag x =? tag y)%uint63
      , Cident.id_name x == Cident.id_name y
      & Cident.id_kind x == Cident.id_kind y ].

  Lemma t_eq_axiom : Equality.axiom t_eqb.
  Proof.
    move=> [tx nx kx] [ty ny ky]; rewrite /eqb /=; apply: (iffP and3P).
    - by case=> /Uint63.eqb_spec /= -> /eqP -> /eqP ->.
    by case=> -> -> ->; split; rewrite ?Uint63.eqb_refl ?eqxx.
  Qed.

  Definition cmp (x y : t) : comparison :=
    let id_cmp := int_cmp (tag x) (tag y) in
    let name_cmp := string_cmp (Cident.id_name x) (Cident.id_name y) in
    let kind_cmp := v_kind_cmp (Cident.id_kind x) (Cident.id_kind y) in
    Lex id_cmp (Lex name_cmp kind_cmp).

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

  HB.instance Definition _ := hasDecEq.Build t t_eq_axiom.
  Definition t_eqType : eqType := t.

  Module CmpT.

    Definition t : eqType := t.
    Definition cmp : t -> t -> comparison := cmp.
    Definition cmpO : Cmp cmp := cmpO.

  End CmpT.

  Module Mt : MAP with Definition K.t := CmpT.t := Mmake CmpT.

  Module St  := Smake CmpT.
  Module StP := MSetEqProperties.EqProperties St.
  Module StD := MSetDecide.WDecide St.

End Tident.

#[global] Canonical ident_eqType := Eval compute in Tident.t_eqType.

Module Type IDENT.
  Definition ident := WrapIdent.t.
  Declare Module Mid : MAP with Definition K.t := (WrapIdent.t : eqType).
End IDENT.

Module Ident <: IDENT.

  Definition ident := WrapIdent.t.
  Definition id_name : ident -> string := Cident.id_name.
  Definition id_kind : ident -> wsize.v_kind := Cident.id_kind.

  Module Mid := Tident.Mt.

End Ident.
