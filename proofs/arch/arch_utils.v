From mathcomp Require Import
  all_ssreflect
  all_algebra.

Require Import
  type
  sem_type
  strings
  utils.
Require Import arch_decl.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* -------------------------------------------------------------------- *)
(* Empty type for architectures that don't have one of the components of the
   declaration. *)

Variant empty : Type :=.

Definition of_empty (X : Type) (x : empty) : X :=
  match x with end.

#[export]
Instance eqTC_empty : eqTypeC empty :=
  {
    beq := of_empty _;
    ceqP := ltac:(done);
  }.

#[export]
Instance finTC_empty : finTypeC empty :=
  {
    cenum := [::];
    cenumP := ltac:(done);
  }.

#[export]
Instance empty_toS t : ToString t empty :=
  {
    category := "empty";
    to_string := of_empty _;
  }.


(* -------------------------------------------------------------------- *)
(* Instruction argument kinds. *)

Section WITH_ARCH.

Context
  {reg regx xreg rflag cond : Type}
  {ad : arch_decl reg regx xreg rflag cond}.

Definition ak_reg_reg : i_args_kinds :=
  [:: [:: [:: CAreg ]; [:: CAreg ] ] ].
Definition ak_reg_imm : i_args_kinds :=
  [:: [:: [:: CAreg ]; [:: CAimm reg_size ] ] ].
Definition ak_reg_imm8 : i_args_kinds :=
  [:: [:: [:: CAreg ]; [:: CAimm U8 ] ] ].
Definition ak_reg_imm16 : i_args_kinds :=
  [:: [:: [:: CAreg ]; [:: CAimm U16 ] ] ].
Definition ak_reg_addr : i_args_kinds :=
  [:: [:: [:: CAreg ]; [:: CAmem true ] ] ].

Definition ak_reg_reg_reg : i_args_kinds :=
  [:: [:: [:: CAreg ]; [:: CAreg ]; [:: CAreg ] ] ].
Definition ak_reg_reg_imm : i_args_kinds :=
  [:: [:: [:: CAreg ]; [:: CAreg ]; [:: CAimm reg_size ] ] ].
Definition ak_reg_reg_imm8 : i_args_kinds :=
  [:: [:: [:: CAreg ]; [:: CAreg ]; [:: CAimm U8 ] ] ].
Definition ak_reg_reg_imm16 : i_args_kinds :=
  [:: [:: [:: CAreg ]; [:: CAreg ]; [:: CAimm U16 ] ] ].

Definition ak_reg_reg_reg_reg : i_args_kinds :=
  [:: [:: [:: CAreg ]; [:: CAreg ]; [:: CAreg ] ; [:: CAreg ] ] ].

End WITH_ARCH.


(* -------------------------------------------------------------------- *)
(* Instruction description transformations. *)

Notation beheadn n xs := (ssrnat.iter n behead xs).
Notation behead1 xs := (beheadn 1 xs). (* Helps inference with [idt_dropn]. *)
Notation behead2 xs := (beheadn 2 xs).
Notation behead3 xs := (beheadn 3 xs).
Notation behead4 xs := (beheadn 4 xs).

#[local]
Lemma size_beheadn {A B} {n : nat} {xs : seq A} {ys : seq B} :
  size xs == size ys ->
  size (beheadn n xs) == size (beheadn n ys).
Proof.
  move=> h.
  elim: n => // n'.
  rewrite !size_behead -!/(beheadn n' _).
  by move=> /eqP <-.
Qed.

#[local]
Lemma all_beheadn {A} {p : A -> bool} {n : nat} {xs : seq A} :
  all p xs ->
  all p (beheadn n xs).
Proof. move=> h. elim: n => // n'. exact: all_behead. Qed.

#[local]
Lemma all2_beheadn
  {A B} {p : A -> B -> bool} {n : nat} {xs : seq A} {ys : seq B} :
  all2 p xs ys ->
  all2 p (beheadn n xs) (beheadn n ys).
Proof. move=> h. elim: n => // n'. exact: all2_behead. Qed.

Definition semi_drop1
  {tin tout} (semi : sem_prod tin (exec (sem_tuple tout))) :
  sem_prod tin (exec (sem_tuple (behead1 tout))) :=
  behead_tuple semi.

Definition semi_drop2
  {tin tout} (semi : sem_prod tin (exec (sem_tuple tout))) :
  sem_prod tin (exec (sem_tuple (behead2 tout))) :=
  behead_tuple (behead_tuple semi).

Definition semi_drop3
  {tin tout} (semi : sem_prod tin (exec (sem_tuple tout))) :
  sem_prod tin (exec (sem_tuple (behead3 tout))) :=
  behead_tuple (behead_tuple (behead_tuple semi)).

Definition semi_drop4
  {tin tout} (semi : sem_prod tin (exec (sem_tuple tout))) :
  sem_prod tin (exec (sem_tuple (behead4 tout))) :=
  behead_tuple (behead_tuple (behead_tuple (behead_tuple semi))).

#[local]
Lemma drop_eq_size {A B} {p} {n : nat} {xs : seq A} {ys : seq B} :
  p && (size xs == size ys) ->
  p && (size (beheadn n xs) == size (beheadn n ys)).
Proof. move=> /andP [-> hsize]. exact: size_beheadn. Qed.

Section WITH_ARCH.

Context
  {reg regx xreg rflag cond : Type}
  {ad : arch_decl reg regx xreg rflag cond}.

Notation idt_dropn semi_dropn :=
  (fun idt =>
     {|
       id_msb_flag := id_msb_flag idt;
       id_tin := id_tin idt;
       id_in := id_in idt;
       id_tout := beheadn _ (id_tout idt);
       id_out := beheadn _ (id_out idt);
       id_semi := semi_dropn (id_semi idt);
       id_nargs := id_nargs idt;
       id_args_kinds := id_args_kinds idt;
       id_eq_size := drop_eq_size (id_eq_size idt);
       id_tin_narr := id_tin_narr idt;
       id_tout_narr := all_beheadn (id_tout_narr idt);
       id_check_dest := all2_beheadn (id_check_dest idt);
       id_str_jas := id_str_jas idt;
       id_safe := id_safe idt;
       id_pp_asm := id_pp_asm idt;
     |}).

Definition idt_drop1 : instr_desc_t -> instr_desc_t := idt_dropn semi_drop1.
Definition idt_drop2 : instr_desc_t -> instr_desc_t := idt_dropn semi_drop2.
Definition idt_drop3 : instr_desc_t -> instr_desc_t := idt_dropn semi_drop3.
Definition idt_drop4 : instr_desc_t -> instr_desc_t := idt_dropn semi_drop4.

(* -------------------------------------------------------------------- *)
(* Shift transformations.
   The following transformation adds a shift argument to an instruction
   and updates the semantics and the rest of the fields accordingly. *)

Section SHIFTED_SEMI.

  Context
    (shift_op : forall ws, word ws -> Z -> exec (word ws))
    {ws : wsize}
    {oT : Type}
    {ty0 ty1 : stype}
  .

  Definition mk_shifted_semi_unop
    (semi : sem_prod [:: sword ws ] (exec oT)) :
    sem_prod [:: sword ws; sword8 ] (exec oT) :=
    fun wx shift_amount =>
      let sham := wunsigned shift_amount in
      Let x := shift_op wx sham in
      semi x.

  Definition mk_shifted_semi_binop_2
    (semi : sem_prod [:: ty0; sword ws ] (exec oT)) :
    sem_prod [:: ty0; sword ws; sword8 ] (exec oT) :=
    fun x wy shift_amount =>
      let sham := wunsigned shift_amount in
      Let y := shift_op wy sham in
      semi x y.

  Definition mk_shifted_semi_terop_2
    (semi : sem_prod [:: ty0; sword ws; ty1 ] (exec oT)) :
    sem_prod [:: ty0; sword ws; ty1; sword8 ] (exec oT) :=
    fun x wy z shift_amount =>
      let sham := wunsigned shift_amount in
      Let y := shift_op wy sham in
      semi x y z.

End SHIFTED_SEMI.

Section SHIFTED_IDT.

  #[local]
  Lemma mk_shifted_eq_size {A B} {x y} {xs0 : seq A} {ys0 : seq B} {p} :
    (size xs0 == size ys0) && p ->
    (size (xs0 ++ [:: x ]) == size (ys0 ++ [:: y ])) && p.
  Proof. rewrite !size_cat => /andP [] /eqP -> ->. by apply/andP. Qed.

  #[local]
  Lemma mk_shifted_tin_narr {A} {p : A -> bool} {x} {xs : seq A} :
    p x ->
    all p xs ->
    all p (xs ++ [:: x ]).
  Proof. by rewrite all_cat /= => -> ->. Qed.

  Definition mk_shifted
    (idt : instr_desc_t)
    (semi : semi_type (id_tin idt ++ [:: sword8 ]) (id_tout idt)) :
    instr_desc_t :=
    {|
      id_msb_flag := MSB_MERGE;
      id_tin := id_tin idt ++ [:: sword8 ];
      id_in := id_in idt ++ [:: E (id_nargs idt) ];
      id_tout := id_tout idt;
      id_out := id_out idt;
      id_semi := semi;
      id_nargs := (id_nargs idt).+1;
      id_args_kinds :=
        map (fun x => x ++ [:: [:: CAimm reg_size] ]) (id_args_kinds idt);
      id_eq_size := mk_shifted_eq_size (id_eq_size idt);
      id_tin_narr :=
        mk_shifted_tin_narr
          (is_true_true : is_not_sarr sword8)
          (id_tin_narr idt);
      id_tout_narr := id_tout_narr idt;
      id_check_dest := id_check_dest idt;
      id_str_jas := id_str_jas idt;
      id_safe := id_safe idt;
      id_pp_asm := id_pp_asm idt;
  |}.

End SHIFTED_IDT.

End WITH_ARCH.
