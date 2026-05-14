(* ** Machine word *)

(* ** Imports and settings *)

From elpi.apps Require Import derive.std.
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool seq eqtype fintype.
From Coq Require Import ZArith.
Require Import strings utils.
Import Utf8.
Import word_ssrZ.

(* -------------------------------------------------------------- *)
#[only(eqbOK)] derive
Variant wsize :=
  | U8
  | U16
  | U32
  | U64
  | U128
  | U256.

Definition wsize_size (sz: wsize) : Z :=
  Zpos match sz return positive with
  | U8   => 1
  | U16  => 2
  | U32  => 4
  | U64  => 8
  | U128 => 16
  | U256 => 32
  end.

(* Size in bits of the elements of a vector. *)
#[only(eqbOK)] derive
Variant velem := VE8 | VE16 | VE32 | VE64.

Coercion wsize_of_velem (ve: velem) : wsize :=
  match ve with
  | VE8 => U8
  | VE16 => U16
  | VE32 => U32
  | VE64 => U64
  end.

(* Size in bits of the elements of a pack. *)
#[only(eqbOK)] derive
Variant pelem :=
| PE1 | PE2 | PE4 | PE8 | PE16 | PE32 | PE64 | PE128.

#[only(eqbOK)] derive
Variant signedness :=
  | Signed
  | Unsigned.

(* -------------------------------------------------------------------- *)
HB.instance Definition _ := hasDecEq.Build signedness signedness_eqb_OK.

(* -------------------------------------------------------------------- *)
HB.instance Definition _ := hasDecEq.Build wsize wsize_eqb_OK.

(* We still need the sumbool version *)
Definition wsize_eq_dec := wsize_eqb_OK_sumbool.

Definition wsizes :=
  [:: U8 ; U16 ; U32 ; U64 ; U128 ; U256 ].

Lemma wsize_fin_axiom : Finite.axiom wsizes.
Proof. by case. Qed.

(* ** Comparison
 * -------------------------------------------------------------------- *)
Definition wsize_cmp s s' :=
  match s, s' with
  | U8, U8 => Eq
  | U8, (U16 | U32 | U64 | U128 | U256)  => Lt
  | U16, U8 => Gt
  | U16, U16 => Eq
  | U16, (U32 | U64 | U128 | U256) => Lt
  | U32, (U8 | U16) => Gt
  | U32, U32 => Eq
  | U32, (U64 | U128 | U256) => Lt
  | U64, (U8 | U16 | U32) => Gt
  | U64, U64 => Eq
  | U64, ( U128 | U256) => Lt
  | U128, (U8 | U16 | U32 | U64) => Gt
  | U128, U128 => Eq
  | U128, U256 => Lt
  | U256, (U8 | U16 | U32 | U64 | U128) => Gt
  | U256, U256 => Eq
  end.

#[export]
Instance wsizeO : Cmp wsize_cmp.
Proof.
  constructor.
  + by move=> [] [].
  + by move=> [] [] [] //= ? [].
  by move=> [] [].
Qed.

Lemma wsize_le_U8 s: (U8 <= s)%CMP.
Proof. by case: s. Qed.

Lemma wsize_ge_U256 s: (s <= U256)%CMP.
Proof. by case s. Qed.

#[global]Hint Resolve wsize_le_U8 wsize_ge_U256: core.

(* -------------------------------------------------------------------- *)
Definition size_8_16 sz := (sz <= U16)%CMP.
Definition size_8_32 sz := (sz <= U32)%CMP.
Definition size_8_64 sz := (sz <= U64)%CMP.
Definition size_16_32 sz := ((U16 <= sz) && (sz <= U32))%CMP.
Definition size_16_64 sz := ((U16 ≤ sz) && (sz ≤ U64))%CMP.
Definition size_32_64 sz := ((U32 ≤ sz) && (sz ≤ U64))%CMP.
Definition size_64_128 sz := ((U64 ≤ sz) && (sz ≤ U128))%CMP.
Definition size_128_256 sz := ((U128 ≤ sz) && (sz ≤ U256))%CMP.

Lemma wsize_nle_u64_size_128_256 sz :
  (sz ≤ U64)%CMP = false →
  size_128_256 sz.
Proof. by case: sz. Qed.

(* -------------------------------------------------------------------- *)
(* -------------------------------------------------------------- *)
Definition string_of_wsize (sz: wsize) : string :=
  match sz with
  | U8 => "8"
  | U16 => "16"
  | U32 => "32"
  | U64 => "64"
  | U128 => "128"
  | U256 => "256"
  end.

Definition string_of_ve_sz (ve:velem) (sz:wsize) : string :=
  match ve, sz with
  | VE8, U16 => "2u8"
  | VE8, U32 => "4u8"
  | VE16, U32 => "2u16"
  | VE8, U64 => "8u8"
  | VE16, U64 => "4u16"
  | VE32, U64 => "2u32"
  | VE64, U64 => "1u64"
  | VE8 , U128 => "16u8"
  | VE16, U128 => "8u16"
  | VE32, U128 => "4u32"
  | VE64, U128 => "2u64"
  | VE8 , U256 => "32u8"
  | VE16, U256 => "16u16"
  | VE32, U256 => "8u32"
  | VE64, U256 => "4u64"
  | _,    _    => "ERROR: please repport"
  end.

Definition pp_s (s: string) (_: unit) : string := s.

Definition pp_sz (s: string) (sz: wsize) (_: unit) : string :=
  s ++ "_" ++ string_of_wsize sz.

Definition pp_ve_sz (s: string) (ve: velem) (sz: wsize) (_: unit) : string :=
  s ++ "_" ++ string_of_ve_sz ve sz.

Definition pp_ve_sz_ve_sz (s: string) (ve: velem) (sz: wsize) (ve': velem) (sz': wsize) (_: unit) : string :=
  s ++ "_" ++ string_of_ve_sz ve sz ++ "_" ++ string_of_ve_sz ve' sz'.

Definition pp_sz_sz (s: string) (sign:bool) (sz sz': wsize) (_: unit) : string :=
  s ++ "_u" ++ string_of_wsize sz ++ (if sign then "s" else "u")%string ++ string_of_wsize sz'.

(* -------------------------------------------------------------------- *)
#[only(eqbOK)] derive
Variant reg_kind : Type :=
| Normal
| Extra.

#[only(eqbOK)] derive
Variant writable : Type := Constant | Writable.

#[only(eqbOK)] derive
Variant reference : Type := Direct | Pointer of writable.

#[only(eqbOK)] derive
Variant v_kind :=
| Const            (* global parameter  *)
| Stack of reference (* stack variable    *)
| Reg   of reg_kind * reference (* register variable *)
| Inline           (* inline variable   *)
| Global           (* global (in memory) constant *)
.

HB.instance Definition _ := hasDecEq.Build writable  writable_eqb_OK.
HB.instance Definition _ := hasDecEq.Build reference reference_eqb_OK.
HB.instance Definition _ := hasDecEq.Build v_kind    v_kind_eqb_OK.

Definition reg_kind_cmp (x y : reg_kind) : comparison :=
  match x, y with
  | Normal, Normal => Eq
  | Normal, Extra  => Lt
  | Extra,  Normal => Gt
  | Extra,  Extra  => Eq
  end.

#[global] Instance reg_kindO : Cmp reg_kind_cmp.
Proof.
  constructor.
  + by move=> [] [].
  + by move=> y x z c; case: x; case: y; case: z => //=; move=> [->].
  + by move=> [] [].
Qed.

Definition writable_cmp (x y : writable) : comparison :=
  match x, y with
  | Constant, Constant => Eq
  | Constant, Writable => Lt
  | Writable, Constant => Gt
  | Writable, Writable => Eq
  end.

#[global] Instance writableO : Cmp writable_cmp.
Proof.
  constructor.
  + by move=> [] [].
  + by move=> y x z c; case: x; case: y; case: z => //=; move=> [->].
  + by move=> [] [].
Qed.

Definition reference_cmp (x y : reference) : comparison :=
  match x, y with
  | Direct,    Direct    => Eq
  | Direct,    Pointer _ => Lt
  | Pointer _, Direct    => Gt
  | Pointer a, Pointer b => writable_cmp a b
  end.

#[global] Instance referenceO : Cmp reference_cmp.
Proof.
  constructor.
  + case=> [|a] [|b] //=; apply: cmp_sym.
  + move=> [|wy] [|wx] [|wz] //= c.
    - by move=> [->].
    - by move=> [->].
    - by move=> [->].
    - by apply: ctrans_Lt.
    - by rewrite ctransC; apply: ctrans_Gt.
    - by apply: cmp_ctrans.
  + case=> [|a] [|b] //= /(@cmp_eq _ _ writableO) ->; reflexivity.
Qed.

Definition v_kind_idx (x : v_kind) : nat :=
  match x with
  | Const    => 0
  | Stack _  => 1
  | Reg _    => 2
  | Inline   => 3
  | Global   => 4
  end.

Definition v_kind_cmp (x y : v_kind) : comparison :=
  match x, y with
  | Const,     Const     => Eq
  | Stack a,   Stack b   => reference_cmp a b
  | Reg a,     Reg b     => Lex (reg_kind_cmp a.1 b.1) (reference_cmp a.2 b.2)
  | Inline,    Inline    => Eq
  | Global,    Global    => Eq
  | _, _ => Nat.compare (v_kind_idx x) (v_kind_idx y)
  end.

Lemma v_kind_cmp_eq x y : reflect (x = y) (v_kind_cmp x y == Eq).
Proof.
by apply: (iffP idP) => [/eqP | ->];
  case: x => [|[|[]]|[[] [|[]]]||];
  case: y => [|[|[]]|[[] [|[]]]||].
Qed.

#[global] Instance v_kindO : Cmp v_kind_cmp.
Proof.
split; last by move=> ?? h; apply/v_kind_cmp_eq/eqP/h.
+ case=> [|a|[a1 a2]||] [|b|[b1 b2]||] //=.
  - by apply: cmp_sym.
  by rewrite !Lex_lex; apply: lex_sym; apply: cmp_sym.
move=> y x z c; rewrite /ctrans.
case xy: (v_kind_cmp x y).
+ by move: xy => /eqP /v_kind_cmp_eq -> [<-].
+ case yz: (v_kind_cmp y z) => // -[<-].
  + by move: yz => /eqP /v_kind_cmp_eq <-.
  case: x y z xy yz => [|r1|[k1 r1]||] [|r2|[k2 r2]||] [|r3|[k3 r3]||] //=;
    first exact: cmp_trans.
  by rewrite !Lex_lex; apply/cmp_trans/LexO.
case yz: (v_kind_cmp y z) => // -[<-].
+ by move: yz => /eqP /v_kind_cmp_eq <-.
case: x y z xy yz => [|r1|[k1 r1]||] [|r2|[k2 r2]||] [|r3|[k3 r3]||] //=;
  first exact: cmp_trans.
by rewrite !Lex_lex; apply/cmp_trans/LexO.
Qed.

(* -------------------------------------------------------------------- *)
Variant safe_cond :=
  (* the nth argument must be different from 0 *)
  | NotZero of wsize & nat
  (* this is a division instruction, two words by one word;
    result must fit in an single word, divider should be <> 0 *)
  | X86Division of wsize & signedness
  (* the nth argument (unsigned interpretation, mod 32) must be in the given range *)
  | InRangeMod32 of wsize & Z & Z & nat
  (*  the nth argument (unsigned interpretation) must be in the < z *)
  | ULt of wsize & nat & Z
  (*  the nth argument (unsigned interpretation) must be in the >= z *)
  | UGe of wsize & Z & nat
  (*  the sum of the nth arguments (unsigned interpretation) must be in the <= z *)
  | UaddLe of wsize & nat & nat & Z
  (* the nth argument of is an array ws[p] where all ceil are initialized *)
  | AllInit of wsize & positive & nat
  (* Unsatisfiable safe_cond *)
  | ScFalse.

(* -------------------------------------------------------------------- *)
Class PointerData := {
  Uptr : wsize;
}.

(* -------------------------------------------------------------------- *)
Class MSFsize :=
  {
    msf_size : wsize;
  }.
