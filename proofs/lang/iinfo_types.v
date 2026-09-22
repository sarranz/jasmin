From Coq Require Import ZArith.
From elpi.apps Require Import derive.std.
From HB Require Import structures.
From mathcomp Require Import ssreflect seq eqtype.
From mathcomp Require Import word_ssrZ.

Require Import var utils.

(* A memory region as seen by the stack allocation pass: a whole slot with
   its size in bytes, or, for array slots whose annotations are fine grained,
   one element of the array. *)
Variant ii_slot_info :=
  | SIregion of var & Z    (* the slot and its size in bytes *)
  | SIelem of var & Z & Z. (* the slot, the index of the element and its size *)

Definition ii_slot_info_eqb (x y : ii_slot_info) : bool :=
  match x, y with
  | SIregion s1 n1, SIregion s2 n2 => (s1 == s2) && (n1 == n2)
  | SIelem s1 i1 n1, SIelem s2 i2 n2 => [&& s1 == s2, i1 == i2 & n1 == n2]
  | _, _ => false
  end.

Lemma ii_slot_info_eqb_OK : Equality.axiom ii_slot_info_eqb.
Proof.
move=> [s1 n1|s1 i1 n1] [s2 n2|s2 i2 n2] /=; try by constructor.
- by apply: (iffP andP) => [[/eqP <- /eqP <-]|[<- <-]].
by apply: (iffP and3P) => [[/eqP <- /eqP <- /eqP <-]|[<- <- <-]].
Qed.

HB.instance Definition _ := hasDecEq.Build ii_slot_info ii_slot_info_eqb_OK.

Definition ii_mem_annot : Type := seq ii_slot_info.

Record ii_inst_info := mk_inst
  {
    inst_caller : seq ii_slot_info;
    inst_callee : ii_slot_info;
  }.

Definition ii_inst_info_eqb (x y : ii_inst_info) : bool :=
  [&& x.(inst_caller) == y.(inst_caller) & x.(inst_callee) == y.(inst_callee)].

Lemma ii_inst_info_eqb_OK : Equality.axiom ii_inst_info_eqb.
Proof.
move=> [c1 c2] [c3 c4]; apply: (iffP idP).
- by move=> /andP [/= /eqP <- /eqP <-].
by move=> [<- <-]; rewrite /ii_inst_info_eqb !eqxx.
Qed.

HB.instance Definition _ := hasDecEq.Build ii_inst_info ii_inst_info_eqb_OK.

Definition ii_inst_annot : Type := seq ii_inst_info.
