From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq eqtype ssralg.

Require Import
  type
  sem_type
  sopn_semi
  strings
  utils
  values
  word.
Require Import arch_decl.

(* -------------------------------------------------------------------- *)
(* Empty type for architectures that don't have one of the components of the
   declaration. *)

(* TODO_ACC this should be void *)
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
  [:: [:: [:: CAreg ]; [:: CAmem true None ] ] ].

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

(* Drop the first output of a total semantics. *)
Definition behead_tuple_t tin tout :
  sem_lprod tin (sem_ltuple_t tout)
  -> sem_lprod tin (sem_ltuple_t (behead tout)) :=
  match tout
  return sem_lprod tin (sem_ltuple_t tout)
         -> sem_lprod tin (sem_ltuple_t (behead tout))
  with
  | [::] => fun f => sem_prod_app f (fun _ => tt)
  | t :: tout' =>
      match tout'
      return sem_lprod tin (sem_ltuple_t (t :: tout'))
             -> sem_lprod tin (sem_ltuple_t tout')
      with
      | [::] => fun f => sem_prod_app f (fun _ => tt)
      | _ => fun f => sem_prod_app f (fun p => p.2)
      end
  end.

Definition semi_drop1_t
  {tin tout} (f : sem_lprod tin (sem_ltuple_t tout)) :
  sem_lprod tin (sem_ltuple_t (behead1 tout)) :=
  behead_tuple_t f.
Arguments semi_drop1_t {tin tout} f /.

Definition semi_drop2_t
  {tin tout} (f : sem_lprod tin (sem_ltuple_t tout)) :
  sem_lprod tin (sem_ltuple_t (behead2 tout)) :=
  behead_tuple_t (behead_tuple_t f).
Arguments semi_drop2_t {tin tout} f /.

Definition semi_drop3_t
  {tin tout} (f : sem_lprod tin (sem_ltuple_t tout)) :
  sem_lprod tin (sem_ltuple_t (behead3 tout)) :=
  behead_tuple_t (behead_tuple_t (behead_tuple_t f)).
Arguments semi_drop3_t {tin tout} f /.

Definition semi_drop4_t
  {tin tout} (f : sem_lprod tin (sem_ltuple_t tout)) :
  sem_lprod tin (sem_ltuple_t (behead4 tout)) :=
  behead_tuple_t (behead_tuple_t (behead_tuple_t (behead_tuple_t f))).
Arguments semi_drop4_t {tin tout} f /.

#[local]
Lemma drop_eq_size {A B} {p} {n : nat} {xs : seq A} {ys : seq B} :
  p && (size xs == size ys) ->
  p && (size (beheadn n xs) == size (beheadn n ys)).
Proof. move=> /andP [-> hsize]. exact: size_beheadn. Qed.

#[local]
Lemma all_beheadn {A} {p : A -> bool} {n : nat} {xs : seq A} :
  all p xs -> all p (beheadn n xs).
Proof. by move=> h; elim: n => //= n' hn; apply: all_behead hn. Qed.

#[local]
Lemma drop_id_wf {A B} {p} {b : bool} {n : nat} {xs : seq A} {ys : seq B} :
  [&& all p xs, ssrnat.eqn (size xs) (size ys) & b] ->
  [&& all p (beheadn n xs), ssrnat.eqn (size (beheadn n xs)) (size (beheadn n ys)) & b].
Proof.
  move=> /and3P [h1 h2 h3]; rewrite all_beheadn //= h3 andbT.
  by apply/eqnP/eqP; apply: (size_beheadn (n:=n)); apply/eqP; apply/eqnP.
Qed.

Section WITH_ARCH.

Context
  {reg regx xreg rflag cond : Type}
  {ad : arch_decl reg regx xreg rflag cond}.

Notation idt_dropn semi_dropn_t :=
  (fun idt =>
     {|
       id_valid := id_valid idt;
       id_msb_flag := id_msb_flag idt;
       id_tin := id_tin idt;
       id_in := id_in idt;
       id_tout := beheadn _ (id_tout idt);
       id_out := beheadn _ (id_out idt);
       id_semi_total := semi_dropn_t (id_semi_total idt);
       id_nargs := id_nargs idt;
       id_args_kinds := id_args_kinds idt;
       id_eq_size := drop_eq_size (id_eq_size idt);
       id_check_dest := all2_beheadn (id_check_dest idt);
       id_str_jas := id_str_jas idt;
       id_safe := id_safe idt;
       id_err := id_err idt;
       id_init := beheadn _ (id_init idt);
       id_doit := id_doit idt;
       id_pp_asm := id_pp_asm idt;
       id_safe_wf := id_safe_wf idt;
       id_wf := drop_id_wf (id_wf idt);
     |}).

Definition idt_drop1 : instr_desc_t -> instr_desc_t := idt_dropn semi_drop1_t.
Definition idt_drop2 : instr_desc_t -> instr_desc_t := idt_dropn semi_drop2_t.
Definition idt_drop3 : instr_desc_t -> instr_desc_t := idt_dropn semi_drop3_t.
Definition idt_drop4 : instr_desc_t -> instr_desc_t := idt_dropn semi_drop4_t.

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
    (semi : sem_lprod [:: lword ws ] oT) :
    sem_lprod [:: lword ws; lword8 ] oT :=
    fun wn shift_amount =>
      let sham := wunsigned shift_amount in
      semi (shift_op wn sham).

  Definition arch_mk_semi2_2_shifted
    (semi : sem_lprod [:: ty0; lword ws ] oT) :
    sem_lprod [:: ty0; lword ws; lword8 ] oT :=
    fun x wy shift_amount =>
      let sham := wunsigned shift_amount in
      semi x (shift_op wy sham).

  Definition arch_mk_semi3_2_shifted
    (semi : sem_lprod [:: ty0; lword ws; ty1 ] oT) :
    sem_lprod [:: ty0; lword ws; ty1; lword8 ] oT :=
    fun x wy z shift_amount =>
      let sham := wunsigned shift_amount in
      semi x (shift_op wy sham) z.

  End SEMI.

#[local]
Lemma mk_shifted_eq_size {A B x y p} {xs0 : seq A} {ys0 : seq B} :
  [&& size xs0 == size ys0 & p ] ->
  [&& size (xs0 ++ [:: x ]) == size (ys0 ++ [:: y ]) & p ].
Proof. by rewrite !size_cat /= !addn1 eqSS. Qed.

Lemma safe_wf_cat (tin tin' : seq ltype) sc :
  all (fun sc => sc_needed_args sc <= size tin) sc ->
  all (fun sc => sc_needed_args sc <= size (tin ++ tin')) sc.
Proof.
  apply: sub_all => c h; rewrite size_cat; exact/(leq_trans h)/leq_addr.
Qed.

Lemma arch_shifted_wf (idt : instr_desc_t) :
  [&& all (safety_cond_wt (map eval_ltype (id_tin idt ++ [:: lword8 ]))) (id_init idt),
      ssrnat.eqn (size (id_init idt)) (size (id_tout idt))
    & ~~ is_ErrType (id_err idt)].
Proof.
  have /and3P [h1 h2 h3] := id_wf idt.
  by rewrite map_cat (all_safety_cond_wt_cat _ h1) h2 h3.
Qed.

Definition arch_mk_shifted
  ak (idt : instr_desc_t) semi_total' : instr_desc_t :=
  {|
    id_msb_flag := MSB_MERGE;
    id_tin := (id_tin idt) ++ [:: lword8 ];
    id_in := (id_in idt) ++ [:: Ea (id_nargs idt) ];
    id_tout := id_tout idt;
    id_out := id_out idt;
    id_semi_total := semi_total';
    id_args_kinds := [seq x ++ [:: [:: ak ] ] | x <- id_args_kinds idt ];
    id_nargs := (id_nargs idt).+1;
    id_eq_size := mk_shifted_eq_size (id_eq_size idt);
    id_check_dest := id_check_dest idt;
    id_str_jas := id_str_jas idt;
    id_safe := id_safe idt;
    id_err := id_err idt;
    id_init := id_init idt;
    id_doit := id_doit idt;
    id_pp_asm := id_pp_asm idt;
    id_valid := id_valid idt;
    id_safe_wf := safe_wf_cat _ (id_safe_wf idt);
    id_wf := arch_shifted_wf idt;
  |}.

End SHIFTED.

End WITH_ARCH.

Arguments arch_mk_shifted {_ _ _ _ _ _}.
Arguments arch_mk_semi1_shifted shift_op {ws oT} semi /.
Arguments arch_mk_semi2_2_shifted shift_op {ws oT ty0} semi /.
Arguments arch_mk_semi3_2_shifted shift_op {ws oT ty0 ty1} semi /.
