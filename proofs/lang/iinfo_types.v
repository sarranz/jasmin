From Coq Require Import ZArith.
From elpi.apps Require Import derive.std.
From HB Require Import structures.
From mathcomp Require Import ssreflect seq eqtype.
From mathcomp Require Import word_ssrZ.

Require Import var utils.

Record ii_slot_info := mk_si
  {
    si_name : var;
    si_ofs : Z;
  }.

Definition ii_slot_info_eqb (x y : ii_slot_info) : bool :=
  [&& x.(si_name) == y.(si_name) & x.(si_ofs) == y.(si_ofs)].

Lemma ii_slot_info_eqb_OK : Equality.axiom ii_slot_info_eqb.
Proof.
move=> [n1 o1] [n2 o2]; apply: (iffP idP).
- by move=> /andP [/= /eqP <- /eqP <-].
by move=> [<- <-]; rewrite /ii_slot_info_eqb !eqxx.
Qed.

HB.instance Definition _ := hasDecEq.Build ii_slot_info ii_slot_info_eqb_OK.

Definition ii_mem_annot : Type := seq ii_slot_info.

Record ii_inst_info := mk_inst
  {
    inst_caller : ii_slot_info;
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
