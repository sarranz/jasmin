(* OpenTitan Big Number architecture. *)

From elpi.apps Require Import derive.std.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype fintype ssralg.
From mathcomp Require Import word word_ssrZ.

Require Import otbn_admit.
Require Import
  expr
  flag_combination
  sem_type
  strings
  utils
  wsize.

Require Import
  arch_decl
  arch_utils.

Require riscv_decl.

Definition otbn_reg_size : wsize := U32.
Definition otbn_xreg_size : wsize := U256.

(* -------------------------------------------------------------------------- *)
(* OTBN has 30 general purpose registers: x2, ..., x31.
   Register x0 always reads zero, so we don't include it.
   Register x1 reads the top of the call stack, so we don't include it. *)

#[only(eqbOK)] derive
Variant register : Type :=
| X02 (* Stack pointer by convention. *)
| X03 | X04 | X05 | X06 | X07 | X08 | X09 | X10 | X11 | X12 | X13 | X14 | X15
| X16 | X17 | X18 | X19 | X20 | X21 | X22 | X23 | X24 | X25 | X26 | X27 | X28
| X29 | X30 | X31
.

#[export]
Instance eqTC_register : eqTypeC register := { ceqP := register_eqb_OK; }.

Canonical otbn_register_eqType := @ceqT_eqType _ eqTC_register.

Definition registers :=
  [:: X02; X03; X04; X05; X06; X07; X08; X09; X10; X11; X12; X13; X14; X15; X16
    ; X17; X18; X19; X20; X21; X22; X23; X24; X25; X26; X27; X28; X29; X30; X31
  ].

Lemma register_fin_axiom : Finite.axiom registers.
Proof. by case. Qed.

#[export]
Instance finTC_register : finTypeC register :=
  { cenum := registers; cenumP := register_fin_axiom; }.

Canonical register_finType := @cfinT_finType _ finTC_register.

Definition register_to_string (r : register) : string :=
  match r with
  | X02 => "x2"
  | X03 => "x3"
  | X04 => "x4"
  | X05 => "x5"
  | X06 => "x6"
  | X07 => "x7"
  | X08 => "x8"
  | X09 => "x9"
  | X10 => "x10"
  | X11 => "x11"
  | X12 => "x12"
  | X13 => "x13"
  | X14 => "x14"
  | X15 => "x15"
  | X16 => "x16"
  | X17 => "x17"
  | X18 => "x18"
  | X19 => "x19"
  | X20 => "x20"
  | X21 => "x21"
  | X22 => "x22"
  | X23 => "x23"
  | X24 => "x24"
  | X25 => "x25"
  | X26 => "x26"
  | X27 => "x27"
  | X28 => "x28"
  | X29 => "x29"
  | X30 => "x30"
  | X31 => "x31"
  end.

#[export] Instance reg_toS : ToString (lword otbn_reg_size) register :=
  {|
    category := "register";
    to_string := register_to_string;
  |}.


(* -------------------------------------------------------------------------- *)
(* OTBN has 32 general purpose wide registers: w0, ..., w31. *)

(* OTBN's wide special registers (WSRs) are MOD, RND, URND, ACC and the four
   KEY_S0/1_L/H registers. Only ACC and MOD are modeled here; the other WSRs
   (RND, URND, KEY_S0_L, KEY_S0_H, KEY_S1_L, KEY_S1_H) are ignored for the
   moment. *)

#[only(eqbOK)] derive
Variant wide_register : Type :=
| W00 | W01 | W02 | W03 | W04 | W05 | W06 | W07 | W08 | W09 | W10 | W11 | W12
| W13 | W14 | W15 | W16 | W17 | W18 | W19 | W20 | W21 | W22 | W23 | W24 | W25
| W26 | W27 | W28 | W29 | W30 | W31
| ACC | MOD
.

#[export]
Instance eqTC_wide_register : eqTypeC wide_register :=
  { ceqP := wide_register_eqb_OK; }.

Canonical otbn_wide_register_eqType := @ceqT_eqType _ eqTC_wide_register.

Definition wide_registers : seq wide_register :=
  [:: W00; W01; W02; W03; W04; W05; W06; W07; W08; W09; W10; W11; W12; W13; W14
    ; W15; W16; W17; W18; W19; W20; W21; W22; W23; W24; W25; W26; W27; W28; W29
    ; W30; W31
    ; ACC; MOD (* TODO_OTBN these should be extra registers *)
  ].

Lemma wide_register_fin_axiom : Finite.axiom wide_registers.
Proof. by case. Qed.

#[export]
Instance finTC_wide_register : finTypeC wide_register :=
  { cenum := wide_registers; cenumP := wide_register_fin_axiom; }.

Canonical wide_register_finType := @cfinT_finType _ finTC_wide_register.

Definition wide_register_to_string (w : wide_register) : string :=
  match w with
  | W00 => "w0"
  | W01 => "w1"
  | W02 => "w2"
  | W03 => "w3"
  | W04 => "w4"
  | W05 => "w5"
  | W06 => "w6"
  | W07 => "w7"
  | W08 => "w8"
  | W09 => "w9"
  | W10 => "w10"
  | W11 => "w11"
  | W12 => "w12"
  | W13 => "w13"
  | W14 => "w14"
  | W15 => "w15"
  | W16 => "w16"
  | W17 => "w17"
  | W18 => "w18"
  | W19 => "w19"
  | W20 => "w20"
  | W21 => "w21"
  | W22 => "w22"
  | W23 => "w23"
  | W24 => "w24"
  | W25 => "w25"
  | W26 => "w26"
  | W27 => "w27"
  | W28 => "w28"
  | W29 => "w29"
  | W30 => "w30"
  | W31 => "w31"
  | ACC => "acc"
  | MOD => "mod"
  end.

#[export]
Instance xreg_toS : ToString (lword otbn_xreg_size) wide_register :=
  {| category  := "wide_register"; to_string := wide_register_to_string; |}.

(* -------------------------------------------------------------------------- *)
(* Flags.
   OTBN has two flag groups, [FG0] and [FG1]. *)

#[only(eqbOK)] derive
Variant rflag : Type :=
| CF0 | CF1 (* Carry flag: carry-out on add, borrow on sub (unsigned overflow,
              not signed overflow). *)
| MF0 | MF1 (* Most significant bit. *)
| LF0 | LF1 (* Least significant bit. *)
| ZF0 | ZF1 (* Zero flag. *)
.

#[export]
Instance eqTC_rflag : eqTypeC rflag := { ceqP := rflag_eqb_OK; }.

Canonical rflag_eqType := @ceqT_eqType _ eqTC_rflag.

Definition rflags : seq rflag := [:: CF0; CF1; MF0; MF1; LF0; LF1; ZF0; ZF1 ].

Lemma rflag_fin_axiom : Finite.axiom rflags.
Proof. by case. Qed.

#[export]
Instance finTC_rflag : finTypeC rflag :=
  { cenum := rflags; cenumP := rflag_fin_axiom; }.

Canonical rflag_finType := @cfinT_finType _ finTC_rflag.

Definition flag_to_string (f : rflag) : string :=
  match f with
 | CF0 => "CF0"
 | MF0 => "MF0"
 | LF0 => "LF0"
 | ZF0 => "ZF0"
 | CF1 => "CF1"
 | MF1 => "MF1"
 | LF1 => "LF1"
 | ZF1 => "ZF1"
  end.

#[export]
Instance flag_toS : ToString lbool rflag :=
  { category := "flag"; to_string := flag_to_string; }.


(* -------------------------------------------------------------------------- *)
(* Conditions. *)

#[only(eqbOK)] derive
Variant condition :=
| RVcond of bool & option register & option register
| BNcond of rflag
.

#[export]
Instance eqTC_condition : eqTypeC condition := { ceqP := condition_eqb_OK }.

Canonical condition_eqType := @ceqT_eqType _ eqTC_condition.

(* -------------------------------------------------------------------- *)
(* Flag combinations. *)

(* TODO_OTBN these don't seem to apply? *)
Definition fc_of_cfc (cfc : combine_flags_core) : flag_combination :=
  match cfc with
  | _ => OTBN_ADMIT "not implemented"
  end.

#[global]
Instance otbn_fcp : FlagCombinationParams := { fc_of_cfc := fc_of_cfc; }.

(* -------------------------------------------------------------------------- *)
(* Immediate checkers. *)

Definition check_nbits
  (s : signedness) (n : positive) (ws : wsize) (w : word ws) : bool :=
  let '(lo, hi) := signedness_bounds s n in
  let i := if s is Signed then wsigned w else wunsigned w in
  [&& lo <=? i & i <? hi ]%Z.

Definition check_bn_shift (i : Z) : bool :=
  [&& 0 <=? i, i <=? 248 & i mod 8 == 0]%Z.

Definition check_mulqacc_shift (i : Z) : bool :=
  [&& 0 <=? i, i <=? 192 & i mod 64 == 0]%Z.

Definition otbn_check_CAimm
  (checker : caimm_checker_s) (ws : wsize) (w : word ws) : bool :=
  match checker with
  | CAimmC_none => true
  | CAimmC_otbn_nbits s n => check_nbits s n w
  | CAimmC_otbn_bn_shift => check_bn_shift (wunsigned w)
  | CAimmC_otbn_mulqacc_shift => check_mulqacc_shift (wunsigned w)
  | _ => false
  end.

(* -------------------------------------------------------------------------- *)
(* Architecture declaration. *)

#[export]
Instance otbn_decl : arch_decl register empty wide_register rflag condition :=
  {
    reg_size := U32;
    xreg_size := U256;
    cond_eqC := eqTC_condition;
    toS_r := reg_toS;
    toS_rx := empty_toS lword32;
    toS_x := xreg_toS;
    toS_f := flag_toS;
    reg_size_neq_xreg_size := refl_equal;
    ad_rsp := X02;
    ad_fcp := otbn_fcp;
    check_CAimm := otbn_check_CAimm;
  }.

Definition otbn_call_conv : calling_convention :=
  let callee_saved_registers :=
    [:: X02; X08; X09; X18; X19; X20; X21; X22; X23; X24; X25; X26; X27 ]
  in
  {|
    callee_saved := map ARReg callee_saved_registers;
    callee_saved_not_bool := refl_equal;
    call_reg_args := [:: X10; X11; X12; X13; X14; X15; X16; X17 ];
    call_xreg_args := [:: W00; W01; W02; W03; W04; W05; W06; W07 ];
    call_reg_ret := [:: X10; X11 ];
    call_xreg_ret:= [:: W00; W01 ];
    call_reg_ret_uniq := refl_equal;
  |}.

(* TODO_OTBN double check, add xreg *)
Definition internal_call_conv : internal_calling_convention :=
  {|
    icall_reg :=
      [:: X10; X11; X12; X13; X14; X15; X16; X17; X05; X06; X07; X08; X09; X18
        ; X19; X20; X21; X22; X23; X24; X25; X26; X27; X28; X29; X30; X31 ];
   icall_regx := [::];
   icall_xreg := [::];
   icall_rflag := [::];
  |}.
