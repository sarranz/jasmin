From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq eqtype ssralg.

Require Import
  type
  sem_type
  strings
  utils
  values
  word.
Require Import arch_decl.

(* -------------------------------------------------------------------- *)
(* Empty type for architectures that don't have one of the components of the
   declaration. *)

(* TODO_OTBN this should be void *)
Variant empty : Set :=.

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

Definition CAimm_sz sz := CAimm None sz.

Definition ak_reg_imm : i_args_kinds :=
    [:: [:: [:: CAreg ]; [:: CAimm_sz reg_size ] ] ].
Definition ak_reg_imm8 : i_args_kinds :=
  [:: [:: [:: CAreg ]; [:: CAimm_sz U8 ] ] ].
Definition ak_reg_imm16 : i_args_kinds :=
  [:: [:: [:: CAreg ]; [:: CAimm_sz U16 ] ] ].

Definition ak_reg_addr : i_args_kinds :=
  [:: [:: [:: CAreg ]; [:: CAmem true ] ] ].

Definition ak_reg_imm8_imm8 : i_args_kinds :=
  [:: [:: [:: CAreg ]; [:: CAimm_sz U8 ]; [:: CAimm_sz U8 ] ] ].

Definition ak_reg_reg_reg : i_args_kinds :=
    [:: [:: [:: CAreg ]; [:: CAreg ]; [:: CAreg ] ] ].
Definition ak_reg_reg_imm : i_args_kinds :=
    [:: [:: [:: CAreg ]; [:: CAreg ]; [:: CAimm_sz reg_size ] ] ].
Definition ak_reg_reg_imm8 : i_args_kinds :=
  [:: [:: [:: CAreg ]; [:: CAreg ]; [:: CAimm_sz U8 ] ] ].
Definition ak_reg_reg_imm16 : i_args_kinds :=
  [:: [:: [:: CAreg ]; [:: CAreg ]; [:: CAimm_sz U16 ] ] ].
Definition ak_reg_reg_imm8_imm8 : i_args_kinds :=
  [:: [:: [:: CAreg ]; [:: CAreg ]; [:: CAimm_sz U8 ]; [:: CAimm_sz U8 ] ] ].

Definition ak_reg_reg_reg_reg : i_args_kinds :=
  [:: [:: [:: CAreg ]; [:: CAreg ]; [:: CAreg ] ; [:: CAreg ] ] ].

End WITH_ARCH.


(* -------------------------------------------------------------------- *)
(* Convenient notations to define instruction descriptors. *)

Notation sem_lprod_ok tin semi := (sem_prod_ok (map eval_ltype tin) semi).
Notation sem_lprod_ok_error tin semi := (sem_prod_ok_error (tin:=map eval_ltype tin) semi _).
Notation sem_lprod_ok_safe tin semi := (sem_prod_ok_safe (tin:=map eval_ltype tin) semi).


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
Lemma all2_beheadn
  {A B} {p : A -> B -> bool} {n : nat} {xs : seq A} {ys : seq B} :
  all2 p xs ys ->
  all2 p (beheadn n xs) (beheadn n ys).
Proof. move=> h. elim: n => // n'. exact: all2_behead. Qed.

Definition behead_tuple tin tout :
  sem_lprod tin (exec (sem_ltuple tout))
  -> sem_lprod tin (exec (sem_ltuple (behead tout))) :=
  match tout
  return sem_lprod tin (exec (sem_ltuple tout))
         -> sem_lprod tin (exec (sem_ltuple (behead tout)))
  with
  | [::] =>
      fun f => sem_prod_app f (fun x => Let _ := x in ok tt)
  | t :: tout' =>
      match tout'
      return sem_lprod tin (exec (sem_ltuple (t :: tout')))
             -> sem_lprod tin (exec (sem_ltuple tout'))
      with
      | [::] =>
          fun f => sem_prod_app f (fun x => Let _ := x in ok tt)
      | _ =>
          fun f => sem_prod_app f (fun x => Let: (r, p) := x in ok p)
      end
  end.

Definition semi_drop1
  {tin tout} (semi : sem_lprod tin (exec (sem_ltuple tout))) :
  sem_lprod tin (exec (sem_ltuple (behead1 tout))) :=
  behead_tuple semi.

Definition semi_drop2
  {tin tout} (semi : sem_lprod tin (exec (sem_ltuple tout))) :
  sem_lprod tin (exec (sem_ltuple (behead2 tout))) :=
  behead_tuple (behead_tuple semi).

Definition semi_drop3
  {tin tout} (semi : sem_lprod tin (exec (sem_ltuple tout))) :
  sem_lprod tin (exec (sem_ltuple (behead3 tout))) :=
  behead_tuple (behead_tuple (behead_tuple semi)).

Definition semi_drop4
  {tin tout} (semi : sem_lprod tin (exec (sem_ltuple tout))) :
  sem_lprod tin (exec (sem_ltuple (behead4 tout))) :=
  behead_tuple (behead_tuple (behead_tuple (behead_tuple semi))).

Lemma behead_tuple_errty tout (semi : sem_lprod [::] (exec (sem_ltuple tout))) :
  semi <> Error ErrType -> behead_tuple semi <> Error ErrType.
Proof.
  case: semi => [t _ | e h].
  + by rewrite /behead_tuple; case: tout t => //= t1 [ | t2 ts] //= [v1 v2].
  by case: tout h => // t1 [ | t2 ts] //= /[swap] -[->].
Qed.

Lemma behead_tuple_safe tout (semi : sem_lprod [::] (exec (sem_ltuple tout))) :
  (exists t, semi = ok t) -> exists t, behead_tuple semi = ok t.
Proof.
  move=> [t ->] {semi}; case: tout t => /=; eauto.
  move=> t1 [ | t2 ts] /=; eauto.
  move=> [v1 v2]; eauto.
Qed.

Lemma behead_tuple_app1 t ts tout (semi : sem_lprod (t :: ts) (exec (sem_ltuple tout))) (v : sem_lt t) :
  behead_tuple semi v = behead_tuple (semi v).
Proof. by case: (tout) (semi) => // t1 [ | t2 ts_]. Qed.

Lemma semi_drop1_errty tin tout (semi : sem_lprod tin (exec (sem_ltuple tout))) :
  sem_lforall (fun r => r <> Error ErrType) tin semi ->
  sem_lforall (fun r => r <> Error ErrType) tin (semi_drop1 semi).
Proof.
  rewrite /semi_drop1; elim: tin semi => //=.
  + by apply behead_tuple_errty.
  move=> t ts hrec semi h v; rewrite behead_tuple_app1; apply/hrec/h.
Qed.

Lemma semi_drop1_sem_safe tin tout sc (semi : sem_lprod tin (exec (sem_ltuple tout))) :
  values.interp_safe_cond_ty sc semi ->
  values.interp_safe_cond_ty sc (semi_drop1 semi).
Proof.
  rewrite /values.interp_safe_cond_ty /semi_drop1.
  elim: tin (@nil values.value) semi => /= [ | t ts hrec] vs semi.
  + by move=> h /h; apply behead_tuple_safe.
  move=> h v; rewrite behead_tuple_app1; apply/hrec/h.
Qed.

Lemma semi_drop2_errty tin tout (semi : sem_lprod tin (exec (sem_ltuple tout))) :
  sem_lforall (fun r => r <> Error ErrType) tin semi ->
  sem_lforall (fun r => r <> Error ErrType) tin (semi_drop2 semi).
Proof.
  rewrite /semi_drop2; elim: tin semi => //=.
  + by move=> ??; do 2! apply behead_tuple_errty.
  move=> t ts hrec semi h v; rewrite !behead_tuple_app1; apply/hrec/h.
Qed.

Lemma semi_drop2_sem_safe tin tout sc (semi : sem_lprod tin (exec (sem_ltuple tout))) :
  values.interp_safe_cond_ty sc semi ->
  values.interp_safe_cond_ty sc (semi_drop2 semi).
Proof.
  rewrite /values.interp_safe_cond_ty /semi_drop2.
  elim: tin (@nil values.value) semi => /= [ | t ts hrec] vs semi.
  + by move=> h /h h1; do 2! apply behead_tuple_safe.
  move=> h v; rewrite !behead_tuple_app1; apply/hrec/h.
Qed.

Lemma semi_drop3_errty tin tout (semi : sem_lprod tin (exec (sem_ltuple tout))) :
  sem_lforall (fun r => r <> Error ErrType) tin semi ->
  sem_lforall (fun r => r <> Error ErrType) tin (semi_drop3 semi).
Proof.
  rewrite /semi_drop3; elim: tin semi => //=.
  + by move=> ??; do 3! apply behead_tuple_errty.
  move=> t ts hrec semi h v; rewrite !behead_tuple_app1; apply/hrec/h.
Qed.

Lemma semi_drop3_sem_safe tin tout sc (semi : sem_lprod tin (exec (sem_ltuple tout))) :
  values.interp_safe_cond_ty sc semi ->
  values.interp_safe_cond_ty sc (semi_drop3 semi).
Proof.
  rewrite /values.interp_safe_cond_ty /semi_drop3.
  elim: tin (@nil values.value) semi => /= [ | t ts hrec] vs semi.
  + by move=> h /h h1; do 3! apply behead_tuple_safe.
  move=> h v; rewrite !behead_tuple_app1; apply/hrec/h.
Qed.

Lemma semi_drop4_errty tin tout (semi : sem_lprod tin (exec (sem_ltuple tout))) :
  sem_lforall (fun r => r <> Error ErrType) tin semi ->
  sem_lforall (fun r => r <> Error ErrType) tin (semi_drop4 semi).
Proof.
  rewrite /semi_drop4; elim: tin semi => //=.
  + by move=> ??; do 4! apply behead_tuple_errty.
  move=> t ts hrec semi h v; rewrite !behead_tuple_app1; apply/hrec/h.
Qed.

Lemma semi_drop4_sem_safe tin tout sc (semi : sem_lprod tin (exec (sem_ltuple tout))) :
  values.interp_safe_cond_ty sc semi ->
  values.interp_safe_cond_ty sc (semi_drop4 semi).
Proof.
  rewrite /values.interp_safe_cond_ty /semi_drop4.
  elim: tin (@nil values.value) semi => /= [ | t ts hrec] vs semi.
  + by move=> h /h h1; do 4! apply behead_tuple_safe.
  move=> h v; rewrite !behead_tuple_app1; apply/hrec/h.
Qed.

#[local]
Lemma drop_eq_size {A B} {p} {n : nat} {xs : seq A} {ys : seq B} :
  p && (size xs == size ys) ->
  p && (size (beheadn n xs) == size (beheadn n ys)).
Proof. move=> /andP [-> hsize]. exact: size_beheadn. Qed.

Section WITH_ARCH.

Context
  {reg regx xreg rflag cond : Type}
  {ad : arch_decl reg regx xreg rflag cond}.

Notation idt_dropn semi_dropn semi_errtyp semi_safe :=
  (fun idt =>
     {|
       id_valid := id_valid idt;
       id_msb_flag := id_msb_flag idt;
       id_tin := id_tin idt;
       id_in := id_in idt;
       id_tout := beheadn _ (id_tout idt);
       id_out := beheadn _ (id_out idt);
       id_semi := semi_dropn (id_semi idt);
       id_nargs := id_nargs idt;
       id_args_kinds := id_args_kinds idt;
       id_eq_size := drop_eq_size (id_eq_size idt);
       id_check_dest := all2_beheadn (id_check_dest idt);
       id_str_jas := id_str_jas idt;
       id_safe := id_safe idt;
       id_doit := id_doit idt;
       id_pp_asm := id_pp_asm idt;
       id_safe_wf := id_safe_wf idt;
       id_semi_errty := fun (h : id_valid idt) =>
          semi_errtyp (id_tin idt) (id_tout idt) (id_semi idt) (id_semi_errty (i:=idt) h);
       id_semi_safe  := fun (h : id_valid idt) =>
          semi_safe (id_tin idt) (id_tout idt) (id_safe idt) (id_semi idt) (id_semi_safe (i:=idt) h);
     |}).

Definition idt_drop1 : instr_desc_t -> instr_desc_t := idt_dropn semi_drop1 semi_drop1_errty semi_drop1_sem_safe.
Definition idt_drop2 : instr_desc_t -> instr_desc_t := idt_dropn semi_drop2 semi_drop2_errty semi_drop2_sem_safe.
Definition idt_drop3 : instr_desc_t -> instr_desc_t := idt_dropn semi_drop3 semi_drop3_errty semi_drop3_sem_safe.
Definition idt_drop4 : instr_desc_t -> instr_desc_t := idt_dropn semi_drop4 semi_drop4_errty semi_drop4_sem_safe.

Definition rtuple_drop5th
  {t0 t1 t2 t3 t4 : ctype}
  (xs : sem_tuple [:: t0; t1; t2; t3; t4 ]) :=
  let: (:: x0, x1, x2, x3 & x4 ) := xs in
  (:: x0, x1, x2 & x3 ).

Section SHIFTED.

(* -------------------------------------------------------------------- *)
(* Shift transformations.
   Instruction descriptions are defined without optionally shifted registers.
   The following transformation adds a shift argument to an instruction
   and updates the semantics and the rest of the fields accordingly. *)

Context
  (shift_op : forall ws, word ws -> Z -> word ws)
  {ws : wsize}
.

  Section SEMI.

  Context {oT : Type} {ty0 ty1 : ltype}.

  Definition arch_mk_semi1_shifted
    (semi : sem_lprod [:: lword ws ] (exec oT)) :
    sem_lprod [:: lword ws; lword8 ] (exec oT) :=
    fun wn shift_amount =>
      let sham := wunsigned shift_amount in
      semi (shift_op wn sham).

  Definition arch_mk_semi2_2_shifted
    (semi : sem_lprod [:: ty0; lword ws ] (exec oT)) :
    sem_lprod [:: ty0; lword ws; lword8 ] (exec oT) :=
    fun x wy shift_amount =>
      let sham := wunsigned shift_amount in
      semi x (shift_op wy sham).

  Definition arch_mk_semi3_2_shifted
    (semi : sem_lprod [:: ty0; lword ws; ty1 ] (exec oT)) :
    sem_lprod [:: ty0; lword ws; ty1; lword8 ] (exec oT) :=
    fun x wy z shift_amount =>
      let sham := wunsigned shift_amount in
      semi x (shift_op wy sham) z.

  End SEMI.

#[local]
Lemma mk_shifted_eq_size {A B x y p} {xs0 : seq A} {ys0 : seq B} :
  [&& size xs0 == size ys0 & p ] ->
  [&& size (xs0 ++ [:: x ]) == size (ys0 ++ [:: y ]) & p ].
Proof. by rewrite !size_cat /= !addn1 eqSS. Qed.

Lemma mk_semi1_shifted_errty A (semi : sem_lprod [:: lword ws ] (exec A)) :
  sem_lforall (fun r : exec A => r <> Error ErrType) [:: lword ws ] semi ->
  sem_lforall (fun r : exec A => r <> Error ErrType)
         ([:: lword ws ] ++ [:: lword8 ]) (arch_mk_semi1_shifted semi).
Proof. rewrite /arch_mk_semi1_shifted /= => h *; exact: h. Qed.

Lemma mk_semi2_2_shifted_errty A t
  (semi : sem_lprod [:: t; lword ws] (exec A)) :
  sem_lforall (fun r : exec A => r <> Error ErrType) [:: t; lword ws] semi ->
  sem_lforall (fun r : exec A => r <> Error ErrType)
         ([:: t; lword ws] ++ [:: lword8]) (arch_mk_semi2_2_shifted semi).
Proof. rewrite /arch_mk_semi2_2_shifted /= => h *; exact: h. Qed.

Lemma mk_semi3_2_shifted_errty A t1 t2
  (semi : sem_lprod [:: t1; lword ws; t2] (exec A)) :
  sem_lforall (fun r : exec A => r <> Error ErrType) [:: t1; lword ws; t2] semi ->
  sem_lforall (fun r : exec A => r <> Error ErrType)
         ([:: t1; lword ws; t2] ++ [:: lword8]) (arch_mk_semi3_2_shifted semi).
Proof. rewrite /arch_mk_semi3_2_shifted /= => h *; exact: h. Qed.

Lemma mk_semi1_shifted_safe A (semi : sem_lprod [:: lword ws] (exec A)) :
  interp_safe_cond_ty [::] semi ->
  interp_safe_cond_ty [::] (arch_mk_semi1_shifted semi).
Proof. move=> h > _; exact: h. Qed.

Lemma mk_semi2_2_shifted_safe A t (semi : sem_lprod [:: t; lword ws] (exec A)) :
  interp_safe_cond_ty [::] semi ->
  interp_safe_cond_ty [::] (arch_mk_semi2_2_shifted semi).
Proof. move=> h > _; exact: h. Qed.

Lemma mk_semi3_2_shifted_safe A t1 t2
  (semi : sem_lprod [:: t1; lword ws; t2] (exec A)) :
  interp_safe_cond_ty [::] semi ->
  interp_safe_cond_ty [::] (arch_mk_semi3_2_shifted semi).
Proof. move=> h > _; exact: h. Qed.

Lemma safe_wf_cat (tin tin' : seq ltype) sc :
  all (fun sc => sc_needed_args sc <= size tin) sc ->
  all (fun sc => sc_needed_args sc <= size (tin ++ tin')) sc.
Proof.
  apply: sub_all => c h; rewrite size_cat; exact/(leq_trans h)/leq_addr.
Qed.

Definition arch_mk_shifted
  ak (idt : instr_desc_t) semi' semi_errty' semi_safe' : instr_desc_t :=
  {|
    id_msb_flag := MSB_MERGE;
    id_tin := (id_tin idt) ++ [:: lword8 ];
    id_in := (id_in idt) ++ [:: Ea (id_nargs idt) ];
    id_tout := id_tout idt;
    id_out := id_out idt;
    id_semi := semi';
    id_args_kinds := [seq x ++ [:: [:: ak ] ] | x <- id_args_kinds idt ];
    id_nargs := (id_nargs idt).+1;
    id_eq_size := mk_shifted_eq_size (id_eq_size idt);
    id_check_dest := id_check_dest idt;
    id_str_jas := id_str_jas idt;
    id_safe := id_safe idt;
    id_doit := id_doit idt;
    id_pp_asm := id_pp_asm idt;
    id_valid := id_valid idt;
    id_safe_wf := safe_wf_cat _ (id_safe_wf idt);
    id_semi_errty := semi_errty';
    id_semi_safe := semi_safe'
  |}.

End SHIFTED.

End WITH_ARCH.

Arguments arch_mk_shifted {_ _ _ _ _ _}.
