(* Asymmetric Crypto Core architecture. *)

From Stdlib Require Import DecimalString.
From elpi.apps Require Import derive.std.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype fintype ssralg.
From mathcomp Require Import word word_ssrZ.

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

(* TODO move *)
Definition string_of_Z (z : Z) : string :=
  NilZero.string_of_int (Z.to_int z).

Definition acc_reg_size : wsize := U32.
Definition acc_xreg_size : wsize := U256.

(* -------------------------------------------------------------------------- *)
(* ACC has 30 general purpose registers: x2, ..., x31.
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

Canonical acc_register_eqType := @ceqT_eqType _ eqTC_register.

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

#[export] Instance reg_toS : ToString (lword acc_reg_size) register :=
  {|
    category := "register";
    to_string := register_to_string;
  |}.


(* -------------------------------------------------------------------------- *)
(* ACC has 32 general purpose wide registers: w0, ..., w31. *)

(* ACC's wide special registers (WSRs) are MOD, RND, URND, ACC, ACCH, the four
   KEY_S0/1_L/H registers and the KMAC registers. Only ACC, ACCH and MOD are
   modeled here ([ACCH] is the high half of the 512-bit accumulator of
   [BN.MULV]); the other WSRs are ignored for the moment. *)

#[only(eqbOK)] derive
Variant wide_register : Type :=
| W00 | W01 | W02 | W03 | W04 | W05 | W06 | W07 | W08 | W09 | W10 | W11 | W12
| W13 | W14 | W15 | W16 | W17 | W18 | W19 | W20 | W21 | W22 | W23 | W24 | W25
| W26 | W27 | W28 | W29 | W30 | W31
| ACC | ACCH | MOD
.

#[export]
Instance eqTC_wide_register : eqTypeC wide_register :=
  { ceqP := wide_register_eqb_OK; }.

Canonical acc_wide_register_eqType := @ceqT_eqType _ eqTC_wide_register.

Definition wide_registers : seq wide_register :=
  [:: W00; W01; W02; W03; W04; W05; W06; W07; W08; W09; W10; W11; W12; W13; W14
    ; W15; W16; W17; W18; W19; W20; W21; W22; W23; W24; W25; W26; W27; W28; W29
    ; W30; W31
    ; ACC; ACCH; MOD (* TODO_ACC these should be extra registers *)
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
  | ACCH => "acch"
  | MOD => "mod"
  end.

#[export]
Instance xreg_toS : ToString (lword acc_xreg_size) wide_register :=
  {| category  := "wide_register"; to_string := wide_register_to_string; |}.

(* -------------------------------------------------------------------------- *)
(* Flags.
   ACC has two flag groups, [FG0] and [FG1]. *)

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

(* [BN_CMP a, b] (or [BN_CMP_FG1]) computes [a - b] and sets the FG0 (resp.
   FG1) flags:
   - [C] (carry/borrow): set on unsigned borrow, i.e. [a <u b].
   - [M] (most significant bit): the sign of the difference [a - b].
   - [L] (least significant bit): unused below.
   - [Z] (zero): set when [a - b] is zero, i.e. [a = b].

   ACC has no overflow flag, so a genuinely signed comparison (one that
   accounts for signed overflow of [a - b]) is not expressible from these
   flags. [M] only tracks the sign of the difference, which coincides with
   the true signed comparison result exactly when [a - b] does not overflow.
   The signed labels below ([<s], [<=s], [>=s], [>s]) are therefore only
   correct under that assumption; there is no frontend check for it.

   label   core      ACC flags   meaning after [BN_CMP a, b]
   ==      CFC_E     Z           a = b
   !=      ~CFC_E    ~Z          a <> b
   <u      CFC_B     C           a <u b                        (exact)
   >=u     ~CFC_B    ~C          a >=u b                       (exact)
   <=u     CFC_BE    C || Z      a <=u b                       (exact)
   >u      ~CFC_BE   ~(C || Z)   a >u b                        (exact)
   <s      CFC_L     M           a <s b   (assumes no signed overflow)
   >=s     ~CFC_L    ~M          a >=s b  (assumes no signed overflow)
   <=s     CFC_LE    M || Z      a <=s b  (assumes no signed overflow)
   >s      ~CFC_LE   ~(M || Z)   a >s b   (assumes no signed overflow)

   The four combine-flag variables [FCVar0..FCVar3] are, in this order, [C],
   [M], [L], [Z] ([FCVar2]/[L] is unused). This order is forced by the typer:
   [tt_lvalues] (compiler/src/pretyping.ml) passes flags to a combine-flags
   label in [arch_info.flagnames] order, filtered to the flags the
   instruction actually sets; that order is [current_cmlz] in
   [acc_instr_decl.v], matching the hardware flag-group bit order
   (C = 0, M = 1, L = 2, Z = 3). *)
Definition fc_of_cfc (cfc : combine_flags_core) : flag_combination :=
  let vcf := FCVar0 in
  let vmf := FCVar1 in
  let vzf := FCVar3 in
  match cfc with
  | CFC_B => vcf
  | CFC_E => vzf
  | CFC_BE => FCOr vcf vzf
  | CFC_L => vmf
  | CFC_LE => FCOr vmf vzf
  end.

#[global]
Instance acc_fcp : FlagCombinationParams := { fc_of_cfc := fc_of_cfc; }.

(* Sanity check: [fc_of_cfc] computes the table above, for every
   [combine_flags] label ([CFC_L]/[FCVar2], i.e. [l], never matters). *)
Lemma cf_xsem_lt_s c m l z :
  cf_xsem negb andb orb eq_op c m l z (CF_LT Signed) = m.
Proof. by []. Qed.

Lemma cf_xsem_lt_u c m l z :
  cf_xsem negb andb orb eq_op c m l z (CF_LT Unsigned) = c.
Proof. by []. Qed.

Lemma cf_xsem_le_s c m l z :
  cf_xsem negb andb orb eq_op c m l z (CF_LE Signed) = m || z.
Proof. by []. Qed.

Lemma cf_xsem_le_u c m l z :
  cf_xsem negb andb orb eq_op c m l z (CF_LE Unsigned) = c || z.
Proof. by []. Qed.

Lemma cf_xsem_eq c m l z :
  cf_xsem negb andb orb eq_op c m l z CF_EQ = z.
Proof. by []. Qed.

Lemma cf_xsem_neq c m l z :
  cf_xsem negb andb orb eq_op c m l z CF_NEQ = ~~ z.
Proof. by []. Qed.

Lemma cf_xsem_ge_s c m l z :
  cf_xsem negb andb orb eq_op c m l z (CF_GE Signed) = ~~ m.
Proof. by []. Qed.

Lemma cf_xsem_ge_u c m l z :
  cf_xsem negb andb orb eq_op c m l z (CF_GE Unsigned) = ~~ c.
Proof. by []. Qed.

Lemma cf_xsem_gt_s c m l z :
  cf_xsem negb andb orb eq_op c m l z (CF_GT Signed) = ~~ (m || z).
Proof. by []. Qed.

Lemma cf_xsem_gt_u c m l z :
  cf_xsem negb andb orb eq_op c m l z (CF_GT Unsigned) = ~~ (c || z).
Proof. by []. Qed.

(* -------------------------------------------------------------------------- *)
(* Immediate checkers. *)

#[only(eqbOK)] derive
Variant acc_caimm_cond :=
  | CAimmC_acc_nbits of signedness & positive
  | CAimmC_acc_bn_shift
  | CAimmC_acc_mulqacc_shift
.

#[ export ]
Instance eqTC_acc_caimm_cond : eqTypeC acc_caimm_cond :=
  { ceqP := acc_caimm_cond_eqb_OK }.

Definition check_nbits
  (s : signedness) (n : positive) (ws : wsize) (w : word ws) : bool :=
  let '(lo, hi) := signedness_bounds s n in
  let i := if s is Signed then wsigned w else wunsigned w in
  [&& lo <=? i & i <? hi ]%Z.

Definition check_bn_shift (i : Z) : bool :=
  [&& 0 <=? i, i <=? 248 & i mod 8 == 0]%Z.

Definition check_mulqacc_shift (i : Z) : bool :=
  [&& 0 <=? i, i <=? 192 & i mod 64 == 0]%Z.

Definition acc_check_CAimm
  (checker : acc_caimm_cond) (ws : wsize) (w : word ws) : bool :=
  match checker with
  | CAimmC_acc_nbits s n => check_nbits s n w
  | CAimmC_acc_bn_shift => check_bn_shift (wunsigned w)
  | CAimmC_acc_mulqacc_shift => check_mulqacc_shift (wunsigned w)
  end.

Definition acc_caimm_cond_pp (checker : acc_caimm_cond) : string :=
  match checker with
  | CAimmC_acc_nbits s n =>
      let '(lo, hi) := signedness_bounds s n in
      concat "" [:: "["; string_of_Z lo; ", "; string_of_Z hi; ")"]
  | CAimmC_acc_bn_shift => "[0, 248] in steps of 8"
  | CAimmC_acc_mulqacc_shift => "[0, 192] in steps of 64"
  end%string.

(* -------------------------------------------------------------------------- *)
(* Architecture declaration. *)

#[export]
Instance acc_decl : arch_decl register empty wide_register rflag condition :=
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
    ad_hwcs_size := Some 8;
    ad_fcp := acc_fcp;
    caimm_cond := acc_caimm_cond;
    caimm_cond_eqC := eqTC_acc_caimm_cond;
    caimm_cond_pp := acc_caimm_cond_pp;
    check_CAimm := acc_check_CAimm;
  }.

Definition acc_call_conv : calling_convention :=
  let callee_saved_registers :=
    [:: X02; X08; X09; X18; X19; X20; X21; X22; X23; X24; X25; X26; X27 ]
  in
  {|
    callee_saved := map ARReg callee_saved_registers;
    callee_saved_not_bool := refl_equal;
    callee_saved_has_rsp := refl_equal;
    call_reg_args := [:: X10; X11; X12; X13; X14; X15; X16; X17 ];
    call_xreg_args := [:: W00; W01; W02; W03; W04; W05; W06; W07 ];
    call_reg_ret := [:: X10; X11 ];
    call_xreg_ret:= [:: W00; W01 ];
    call_reg_ret_uniq := refl_equal;
  |}.

(* TODO_ACC double check, add xreg *)
Definition internal_call_conv : internal_calling_convention :=
  {|
    icall_reg :=
      [:: X10; X11; X12; X13; X14; X15; X16; X17; X05; X06; X07; X08; X09; X18
        ; X19; X20; X21; X22; X23; X24; X25; X26; X27; X28; X29; X30; X31 ];
   icall_regx := [::];
   icall_xreg := [::];
   icall_rflag := [::];
  |}.
