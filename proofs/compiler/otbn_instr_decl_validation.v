(* OTBN instruction set -- validation.

   Sanity checks for the OTBN instruction descriptions defined in
   [otbn_instr_decl]: the primitive-string table ([VALIDATION_PRIM]), the
   argument counts of each instruction description ([VALIDATION_ARGS]), and the
   instruction semantics ([VALIDATION_SEM]).

   The semantics test vectors were produced with the ACC reference simulator
   (accsim/sim/insn.py and isa.py). *)

Set Uniform Inductive Parameters.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From elpi.apps Require Import derive.std.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq eqtype fintype.
From mathcomp Require Import ssralg word_ssrZ.

Require Import
  otbn_options
  sem_type
  shift_kind
  strings
  utils
  word.
Require xseq.
Require Import
  values
  sopn
  arch_decl
  arch_utils.
Require Import otbn_decl.
Require Import otbn_instr_decl.

#[local] Open Scope Z.
#[local] Open Scope ring_scope.

(* Sanity check for prim_string. *)
Section VALIDATION_PRIM.
  Import strings.

  Let strings := Eval compute in map fst otbn_prim_string.

  Goal uniq strings. done. Qed.

  Fixpoint str_ends_with (suf s : string) : bool :=
    (s == suf) || if s is String _ s' then str_ends_with suf s' else false.

  Definition bad_suffix s :=
    has
      (fun suf => str_ends_with suf s)
      [:: "_FG0"; "_FG1"; "_L"; "_U" ]%string.

  Goal all [predC bad_suffix] strings.
  done. Qed.

  Let hidden := [:: "LA" ]%string.

  Goal
    forall op,
      let: s := replace_dot (otbn_op_to_string op) in
      xorb (s \in hidden) (s \in strings).
  by move=> [] // [] // [] //. Qed.

End VALIDATION_PRIM.

Section VALIDATION_ARGS.
  Definition aux (seen : seq nat) (x : arg_desc) : seq nat :=
    if x is ADExplicit _ n _
    then if n \notin seen then n :: seen else seen
    else seen.

  Fixpoint count_explicit_arguments_aux
    (seen : seq nat) (xs : seq arg_desc) : nat :=
    match xs with
    | [::] => size seen
    | x :: xs =>
        let seen' := aux seen x in
        count_explicit_arguments_aux seen' xs
    end.

  Definition count_explicit_arguments := count_explicit_arguments_aux [::].

  Goal
    forall op,
      let t := instr_desc_op op in
      all
        (fun x => size x == count_explicit_arguments (id_in t ++ id_out t))
        (id_args_kinds t).
  by move=> [] // [] // []. Qed.

  Goal
    forall op,
      let t := instr_desc_op op in
      id_nargs t = count_explicit_arguments (id_in t ++ id_out t).
  by move=> [] // [] // []. Qed.

End VALIDATION_ARGS.

(* -------------------------------------------------------------------------- *)

Section VALIDATION_SEM.

  Notation test2 op w1 w2 r :=
    (is_ok
       (Let r' := id_semi (desc_otbn_op op) w1 w2 in
        assert (wunsigned r' == wunsigned r) ErrSemUndef)).

  Notation test3 op w1 w2 w3 r :=
    (is_ok
       (Let r' := id_semi (desc_otbn_op op) w1 w2 w3 in
        assert (wunsigned r' == wunsigned r) ErrSemUndef)).

  Goal test3 BN_ADDM
    (wrepr U256 5) (wrepr U256 7) (wrepr U256 100) (wrepr U256 12).
  Proof. by []. Qed.

  Goal test3 BN_SUBM
    (wrepr U256 5) (wrepr U256 7) (wrepr U256 100) (wrepr U256 98).
  Proof. by []. Qed.

  Goal test3 BN_ADDM
    (wrepr U256 0) (wrepr U256 0) (wrepr U256 100) (wrepr U256 0).
  Proof. by []. Qed.

  Goal test2 (RV32 SLL) (wrepr U32 1) (wrepr U32 32) (wrepr U32 1).
  Proof. by []. Qed.

  Goal test2 (RV32 SLL) (wrepr U32 1) (wrepr U32 33) (wrepr U32 2).
  Proof. by []. Qed.

  Goal test2 (RV32 SRL)
    (wrepr U32 4294967295) (wrepr U32 36) (wrepr U32 268435455).
  Proof. by []. Qed.

  Goal test2 (RV32 SRL)
    (wrepr U32 2147483648) (wrepr U32 32) (wrepr U32 2147483648).
  Proof. by []. Qed.

  Goal test2 (RV32 SRA)
    (wrepr U32 2147483648) (wrepr U32 32) (wrepr U32 2147483648).
  Proof. by []. Qed.

  Goal test2 (RV32 SRA)
    (wrepr U32 2147483648) (wrepr U32 33) (wrepr U32 3221225472).
  Proof. by []. Qed.

  Goal test2 (RV32 SLLI) (wrepr U32 1) (wrepr U32 4) (wrepr U32 16).
  Proof. by []. Qed.

  Goal test2 (RV32 SRAI)
    (wrepr U32 2147483648) (wrepr U32 1) (wrepr U32 3221225472).
  Proof. by []. Qed.

  Notation test_so fg wb mf lf zf r x ix y iy acc sham mf' lf' zf' wrd_e acc_e :=
    (is_ok
       (Let res :=
          id_semi (desc_otbn_op (BN_MULQACC_SO fg wb))
            mf lf zf r x ix y iy acc sham
        in
        assert
          [&& res.1 == mf', res.2.1 == lf', res.2.2.1 == zf',
              wunsigned res.2.2.2.1 == wunsigned wrd_e
            & wunsigned res.2.2.2.2 == wunsigned acc_e ]
          ErrSemUndef)).

  Goal test_so FG0 WB_lower false false false
    (wrepr U256 0) (wrepr U256 3) (wrepr U8 0) (wrepr U256 5) (wrepr U8 0)
    (wrepr U256 (Z.shiftl 9 128)%Z) (wrepr U8 0)
    (Some false) (Some true) (Some false)
    (wrepr U256 15) (wrepr U256 9).
  Proof. by []. Qed.

  Goal test_so FG0 WB_upper false false false
    (wrepr U256 0) (wrepr U256 3) (wrepr U8 0) (wrepr U256 5) (wrepr U8 0)
    (wrepr U256 (Z.shiftl 9 128)%Z) (wrepr U8 0)
    (Some false) (Some false) (Some false)
    (wrepr U256 (Z.shiftl 15 128)%Z) (wrepr U256 9).
  Proof. by []. Qed.

  Goal test_so FG0 WB_lower false false false
    (wrepr U256 0) (wrepr U256 1) (wrepr U8 0) (wrepr U256 1) (wrepr U8 0)
    (wrepr U256 1) (wrepr U8 128)
    (Some false) (Some true) (Some false)
    (wrepr U256 1) (wrepr U256 1).
  Proof. by []. Qed.

  Goal test_so FG0 WB_lower false true false
    (wrepr U256 0) (wrepr U256 2) (wrepr U8 0) (wrepr U256 2) (wrepr U8 0)
    (wrepr U256 0) (wrepr U8 192)
    (Some false) (Some false) (Some true)
    (wrepr U256 0) (wrepr U256 (Z.shiftl 1 66)%Z).
  Proof. by []. Qed.

  Goal test_so FG0 WB_upper false true true
    (wrepr U256 0) (wrepr U256 0) (wrepr U8 0) (wrepr U256 0) (wrepr U8 0)
    (wrepr U256 (Z.shiftl 1 127 + Z.shiftl 5 128)%Z) (wrepr U8 0)
    (Some true) (Some true) (Some false)
    (wrepr U256 (Z.shiftl 1 255)%Z) (wrepr U256 5).
  Proof. by []. Qed.

  Notation test_so_z fg wb mf lf zf r x ix y iy sham mf' lf' zf' wrd_e acc_e :=
    (is_ok
       (Let res :=
          id_semi (desc_otbn_op (BN_MULQACC_SO_Z fg wb))
            mf lf zf r x ix y iy sham
        in
        assert
          [&& res.1 == mf', res.2.1 == lf', res.2.2.1 == zf',
              wunsigned res.2.2.2.1 == wunsigned wrd_e
            & wunsigned res.2.2.2.2 == wunsigned acc_e ]
          ErrSemUndef)).

  Goal test_so_z FG0 WB_lower false false false
    (wrepr U256 0) (wrepr U256 (2 + 7 * 2 ^ 64)%Z) (wrepr U8 0)
    (wrepr U256 (5 * 2 ^ 64)%Z) (wrepr U8 1) (wrepr U8 0)
    (Some false) (Some false) (Some false)
    (wrepr U256 10) (wrepr U256 0).
  Proof. by []. Qed.

  Goal test_so_z FG0 WB_upper false false false
    (wrepr U256 0) (wrepr U256 (2 + 7 * 2 ^ 64)%Z) (wrepr U8 1)
    (wrepr U256 (3 + 5 * 2 ^ 64)%Z) (wrepr U8 0) (wrepr U8 0)
    (Some false) (Some false) (Some false)
    (wrepr U256 (Z.shiftl 21 128)%Z) (wrepr U256 0).
  Proof. by []. Qed.

  Goal test_so_z FG0 WB_lower true true true
    (wrepr U256 0) (wrepr U256 3) (wrepr U8 0)
    (wrepr U256 (4 * 2 ^ 64)%Z) (wrepr U8 1) (wrepr U8 64)
    (Some true) (Some false) (Some false)
    (wrepr U256 (Z.shiftl 12 64)%Z) (wrepr U256 0).
  Proof. by []. Qed.

  (* Vector instructions. The expected results below were produced by the
     reference simulator ([insn.py]: BNADDV, BNSUBV, BNSHV). *)
  Notation a32 :=
    (wrepr U256 0x8000000000000007000000000000000500000064ffffffff0000000200000001%Z).
  Notation b32 :=
    (wrepr U256 0x80000000000000030000000000000005000000c800000001000000140000000a%Z).
  Notation a16 :=
    (wrepr U256 0x3000300030003000300030003000380000007000000050064ffff00020001%Z).
  Notation b16 :=
    (wrepr U256 0x10001000100010001000100010001800000030000000500c800010014000a%Z).
  Notation m :=
    (wrepr U256 0x61%Z).

  Goal test2 (BN_ADDV V8S false) a32 b32
    (wrepr U256 0xa000000000000000a0000012c00000000000000160000000b%Z).
  Proof. by []. Qed.

  Goal test3 (BN_ADDV V8S true) a32 b32 m
    (wrepr U256 0xffffff9f0000000a000000000000000a000000cbffffff9f000000160000000b%Z).
  Proof. by []. Qed.

  Goal test2 (BN_ADDV V16H false) a16 b16
    (wrepr U256 0x400040004000400040004000400040000000a0000000a012c00000016000b%Z).
  Proof. by []. Qed.

  Goal test3 (BN_ADDV V16H true) a16 b16 m
    (wrepr U256 0x40004000400040004000400040004ff9f000a0000000a00cbff9f0016000b%Z).
  Proof. by []. Qed.

  Goal test2 (BN_SUBV V8S false) a32 b32
    (wrepr U256 0x40000000000000000ffffff9cfffffffeffffffeefffffff7%Z).
  Proof. by []. Qed.

  Goal test3 (BN_SUBV V8S true) a32 b32 m
    (wrepr U256 0x40000000000000000fffffffdfffffffe0000004f00000058%Z).
  Proof. by []. Qed.

  Goal test2 (BN_SUBV V16H false) a16 b16
    (wrepr U256 0x200020002000200020002000200020000000400000000ff9cfffeffeefff7%Z).
  Proof. by []. Qed.

  Goal test3 (BN_SUBV V16H true) a16 b16 m
    (wrepr U256 0x200020002000200020002000200020000000400000000fffdfffe004f0058%Z).
  Proof. by []. Qed.

  Goal test2 (BN_SHV V8S RS_left) a32 (wrepr U8 3)
    (wrepr U256 0x38000000000000002800000320fffffff80000001000000008%Z).
  Proof. by []. Qed.

  Goal test2 (BN_SHV V8S RS_right) a32 (wrepr U8 5)
    (wrepr U256 0x40000000000000000000000000000000000000307ffffff0000000000000000%Z).
  Proof. by []. Qed.

  Goal test2 (BN_SHV V16H RS_left) a16 (wrepr U8 4)
    (wrepr U256 0x30003000300030003000300030003000000070000000500640fff000200010%Z).
  Proof. by []. Qed.

  Goal test2 (BN_SHV V16H RS_right) a16 (wrepr U8 2)
    (wrepr U256 0x200000010000000100193fff00000000%Z).
  Proof. by []. Qed.

  (* [BN.TRN]: partial transpose. The inputs have distinct 16-bit lanes
     (0..15 and 16..31), so every element width and mode is exercised and the
     interleaving is visible. The expected results were produced by the
     reference simulator ([insn.py]: BNTRN). *)
  Notation ta :=
    (wrepr U256 0xf000e000d000c000b000a0009000800070006000500040003000200010000%Z).
  Notation tb :=
    (wrepr U256 0x1f001e001d001c001b001a0019001800170016001500140013001200110010%Z).

  Goal test2 (BN_TRN T16H TRNMeven) ta tb
    (wrepr U256 0x1e000e001c000c001a000a0018000800160006001400040012000200100000%Z).
  Proof. by []. Qed.

  Goal test2 (BN_TRN T8S TRNMeven) ta tb
    (wrepr U256 0x1d001c000d000c001900180009000800150014000500040011001000010000%Z).
  Proof. by []. Qed.

  Goal test2 (BN_TRN T4D TRNMeven) ta tb
    (wrepr U256 0x1b001a00190018000b000a0009000800130012001100100003000200010000%Z).
  Proof. by []. Qed.

  Goal test2 (BN_TRN T2Q TRNMeven) ta tb
    (wrepr U256 0x17001600150014001300120011001000070006000500040003000200010000%Z).
  Proof. by []. Qed.

  Goal test2 (BN_TRN T16H TRNModd) ta tb
    (wrepr U256 0x1f000f001d000d001b000b0019000900170007001500050013000300110001%Z).
  Proof. by []. Qed.

  Goal test2 (BN_TRN T8S TRNModd) ta tb
    (wrepr U256 0x1f001e000f000e001b001a000b000a00170016000700060013001200030002%Z).
  Proof. by []. Qed.

  Goal test2 (BN_TRN T4D TRNModd) ta tb
    (wrepr U256 0x1f001e001d001c000f000e000d000c00170016001500140007000600050004%Z).
  Proof. by []. Qed.

  Goal test2 (BN_TRN T2Q TRNModd) ta tb
    (wrepr U256 0x1f001e001d001c001b001a00190018000f000e000d000c000b000a00090008%Z).
  Proof. by []. Qed.

  (* ======================================================================= *)
  (* Additional validation vectors, also produced with the ACC reference     *)
  (* simulator (accsim/sim: SLL/SRL/SRA, BNRSHI, BNSHV, BNTRN, BNMULQACC,     *)
  (* BNMULQACCWO).                                                            *)
  (* ======================================================================= *)

  (* Large RV32 shift amounts. The shift register is masked to its low 5 bits
     ([Z.land _ 31], mirroring [insn.py]'s [& 0x1f]), so a shift of 64 acts as
     0, 100 as 4, and 0xffffffff as 31. These make the masking visible. *)
  Goal test2 (RV32 SLL) (wrepr U32 0xdeadbeef) (wrepr U32 64)
    (wrepr U32 0xdeadbeef).
  Proof. by []. Qed.

  Goal test2 (RV32 SLL) (wrepr U32 1) (wrepr U32 0xffffffff)
    (wrepr U32 0x80000000).
  Proof. by []. Qed.

  Goal test2 (RV32 SLL) (wrepr U32 3) (wrepr U32 100) (wrepr U32 0x30).
  Proof. by []. Qed.

  Goal test2 (RV32 SRL) (wrepr U32 0xffffffff) (wrepr U32 64)
    (wrepr U32 0xffffffff).
  Proof. by []. Qed.

  Goal test2 (RV32 SRL) (wrepr U32 0x80000000) (wrepr U32 0xffffffff)
    (wrepr U32 1).
  Proof. by []. Qed.

  Goal test2 (RV32 SRA) (wrepr U32 0x80000000) (wrepr U32 64)
    (wrepr U32 0x80000000).
  Proof. by []. Qed.

  Goal test2 (RV32 SRA) (wrepr U32 0x80000000) (wrepr U32 0xffffffff)
    (wrepr U32 0xffffffff).
  Proof. by []. Qed.

  Goal test2 (RV32 SRA) (wrepr U32 0x40000000) (wrepr U32 100)
    (wrepr U32 0x4000000).
  Proof. by []. Qed.

  (* [BN.RSHI]: right shift of the concatenation {wrs1, wrs2} by the
     immediate. [imm = 0] selects [wrs2] unchanged. *)
  Notation rshi_a :=
    (wrepr U256 0x1111111122222222333333334444444455555555666666667777777788888888%Z).
  Notation rshi_b :=
    (wrepr U256 0x99999999aaaaaaaabbbbbbbbccccccccddddddddeeeeeeeeff00000012345678%Z).

  Goal test3 BN_RSHI rshi_a rshi_b (wrepr U8 0) rshi_b.
  Proof. by []. Qed.

  Goal test3 BN_RSHI rshi_a rshi_b (wrepr U8 4)
    (wrepr U256 0x899999999aaaaaaaabbbbbbbbccccccccddddddddeeeeeeeeff0000001234567%Z).
  Proof. by []. Qed.

  Goal test3 BN_RSHI rshi_a rshi_b (wrepr U8 64)
    (wrepr U256 0x777777778888888899999999aaaaaaaabbbbbbbbccccccccddddddddeeeeeeee%Z).
  Proof. by []. Qed.

  Goal test3 BN_RSHI rshi_a rshi_b (wrepr U8 127)
    (wrepr U256 0xaaaaaaaacccccccceeeeeeef1111111133333333555555557777777799999999%Z).
  Proof. by []. Qed.

  Goal test3 BN_RSHI rshi_a rshi_b (wrepr U8 128)
    (wrepr U256 0x5555555566666666777777778888888899999999aaaaaaaabbbbbbbbcccccccc%Z).
  Proof. by []. Qed.

  Goal test3 BN_RSHI rshi_a rshi_b (wrepr U8 200)
    (wrepr U256 0x2233333333444444445555555566666666777777778888888899999999aaaaaa%Z).
  Proof. by []. Qed.

  Goal test3 BN_RSHI rshi_a rshi_b (wrepr U8 255)
    (wrepr U256 0x22222222444444446666666688888888aaaaaaaacccccccceeeeeeef11111111%Z).
  Proof. by []. Qed.

  (* [BN.SHV]: additional lanewise-shift cases (reusing [a32]/[a16] above).
     [shift = 0] is the identity; for [.16H] a shift may exceed the 16-bit lane
     width. *)
  Goal test2 (BN_SHV V8S RS_left) a32 (wrepr U8 0) a32.
  Proof. by []. Qed.

  Goal test2 (BN_SHV V8S RS_left) a32 (wrepr U8 16)
    (wrepr U256 0x70000000000000005000000640000ffff00000002000000010000%Z).
  Proof. by []. Qed.

  Goal test2 (BN_SHV V8S RS_right) a32 (wrepr U8 31)
    (wrepr U256 0x100000000000000000000000000000000000000010000000000000000%Z).
  Proof. by []. Qed.

  Goal test2 (BN_SHV V16H RS_left) a16 (wrepr U8 12)
    (wrepr U256 0x3000300030003000300030003000300000007000000050004000f00020001000%Z).
  Proof. by []. Qed.

  Goal test2 (BN_SHV V16H RS_right) a16 (wrepr U8 15)
    (wrepr U256 0x10000000000000000000100000000%Z).
  Proof. by []. Qed.

  Goal test2 (BN_SHV V16H RS_right) a16 (wrepr U8 8)
    (wrepr U256 0x80000000000000000000ff00000000%Z).
  Proof. by []. Qed.

  (* [BN.TRN]: additional cases with a byte-counting data pattern, exercising
     every element width and both modes again on different inputs. *)
  Notation trn_a :=
    (wrepr U256 0x0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f20%Z).
  Notation trn_b :=
    (wrepr U256 0xa1a2a3a4a5a6a7a8a9aaabacadaeafb0b1b2b3b4b5b6b7b8b9babbbcbdbebfc0%Z).

  Goal test2 (BN_TRN T8S TRNMeven) trn_a trn_b
    (wrepr U256 0xa5a6a7a805060708adaeafb00d0e0f10b5b6b7b815161718bdbebfc01d1e1f20%Z).
  Proof. by []. Qed.

  Goal test2 (BN_TRN T8S TRNModd) trn_a trn_b
    (wrepr U256 0xa1a2a3a401020304a9aaabac090a0b0cb1b2b3b411121314b9babbbc191a1b1c%Z).
  Proof. by []. Qed.

  Goal test2 (BN_TRN T4D TRNMeven) trn_a trn_b
    (wrepr U256 0xa9aaabacadaeafb0090a0b0c0d0e0f10b9babbbcbdbebfc0191a1b1c1d1e1f20%Z).
  Proof. by []. Qed.

  Goal test2 (BN_TRN T2Q TRNModd) trn_a trn_b
    (wrepr U256 0xa1a2a3a4a5a6a7a8a9aaabacadaeafb00102030405060708090a0b0c0d0e0f10%Z).
  Proof. by []. Qed.

  (* [BN.MULQACC] and its variants. [ix]/[iy] select 64-bit quarter words of
     [wrs1]/[wrs2]; the 128-bit product is shifted left by [sham] (a multiple
     of 64) and added to the accumulator, truncated to 256 bits. *)
  Notation test_mq op x ix y iy acc sham r :=
    (is_ok
       (Let r' := id_semi (desc_otbn_op op) x ix y iy acc sham in
        assert (wunsigned r' == wunsigned r) ErrSemUndef)).

  Notation test_mq_z op x ix y iy sham r :=
    (is_ok
       (Let r' := id_semi (desc_otbn_op op) x ix y iy sham in
        assert (wunsigned r' == wunsigned r) ErrSemUndef)).

  (* [BN.MULQACC]: reads and accumulates into [ACC]. *)
  Goal test_mq BN_MULQACC
    (wrepr U256 3) (wrepr U8 0) (wrepr U256 5) (wrepr U8 0)
    (wrepr U256 0) (wrepr U8 0) (wrepr U256 15).
  Proof. by []. Qed.

  Goal test_mq BN_MULQACC
    (wrepr U256 0x10000000000000002%Z) (wrepr U8 1) (wrepr U256 5) (wrepr U8 0)
    (wrepr U256 0x100) (wrepr U8 64) (wrepr U256 0x50000000000000100%Z).
  Proof. by []. Qed.

  (* The shifted product overflows 256 bits and is truncated. *)
  Goal test_mq BN_MULQACC
    (wrepr U256 0xffffffffffffffff%Z) (wrepr U8 0)
    (wrepr U256 0xffffffffffffffff%Z) (wrepr U8 0)
    (wrepr U256 0) (wrepr U8 192)
    (wrepr U256 0x1000000000000000000000000000000000000000000000000%Z).
  Proof. by []. Qed.

  Goal test_mq BN_MULQACC
    (wrepr U256 0x123456789abcdef%Z) (wrepr U8 0) (wrepr U256 2) (wrepr U8 0)
    (wrepr U256 0xfff) (wrepr U8 0) (wrepr U256 0x2468acf1357abdd%Z).
  Proof. by []. Qed.

  (* [BN.MULQACC.Z]: zeroes the accumulator first. *)
  Goal test_mq_z BN_MULQACC_Z
    (wrepr U256 0x123456789abcdef0%Z) (wrepr U8 0) (wrepr U256 0x10) (wrepr U8 0)
    (wrepr U8 0) (wrepr U256 0x123456789abcdef00%Z).
  Proof. by []. Qed.

  Goal test_mq_z BN_MULQACC_Z
    (wrepr U256 0xaaaaaaaaaaaaaaab0000000000000000%Z) (wrepr U8 1)
    (wrepr U256 0x30000000000000000%Z) (wrepr U8 1) (wrepr U8 128)
    (wrepr U256 0x2000000000000000100000000000000000000000000000000%Z).
  Proof. by []. Qed.

  (* [BN.MULQACC.WO]: full-word writeback to [wrd] (and [ACC]); sets M/L/Z. *)
  Notation test_wo fg x ix y iy acc sham mf' lf' zf' wrd_e acc_e :=
    (is_ok
       (Let res :=
          id_semi (desc_otbn_op (BN_MULQACC_WO fg)) x ix y iy acc sham
        in
        assert
          [&& res.1 == mf', res.2.1 == lf', res.2.2.1 == zf',
              wunsigned res.2.2.2.1 == wunsigned wrd_e
            & wunsigned res.2.2.2.2 == wunsigned acc_e ]
          ErrSemUndef)).

  Notation test_wo_z fg x ix y iy sham mf' lf' zf' wrd_e acc_e :=
    (is_ok
       (Let res :=
          id_semi (desc_otbn_op (BN_MULQACC_WO_Z fg)) x ix y iy sham
        in
        assert
          [&& res.1 == mf', res.2.1 == lf', res.2.2.1 == zf',
              wunsigned res.2.2.2.1 == wunsigned wrd_e
            & wunsigned res.2.2.2.2 == wunsigned acc_e ]
          ErrSemUndef)).

  Goal test_wo FG0
    (wrepr U256 3) (wrepr U8 0) (wrepr U256 5) (wrepr U8 0)
    (wrepr U256 0x10) (wrepr U8 0)
    (Some false) (Some true) (Some false)
    (wrepr U256 0x1f) (wrepr U256 0x1f).
  Proof. by []. Qed.

  (* The truncated result has its top bit set, so M = 1. *)
  Goal test_wo FG0
    (wrepr U256 0xffffffffffffffff%Z) (wrepr U8 0)
    (wrepr U256 0xffffffffffffffff%Z) (wrepr U8 0)
    (wrepr U256 0) (wrepr U8 128)
    (Some true) (Some false) (Some false)
    (wrepr U256 0xfffffffffffffffe000000000000000100000000000000000000000000000000%Z)
    (wrepr U256 0xfffffffffffffffe000000000000000100000000000000000000000000000000%Z).
  Proof. by []. Qed.

  (* A zero result sets Z. *)
  Goal test_wo FG0
    (wrepr U256 0) (wrepr U8 0) (wrepr U256 0x1234) (wrepr U8 0)
    (wrepr U256 0) (wrepr U8 0)
    (Some false) (Some false) (Some true)
    (wrepr U256 0) (wrepr U256 0).
  Proof. by []. Qed.

  (* [BN.MULQACC.WO.Z]: as above but zeroes the accumulator first. *)
  Goal test_wo_z FG0
    (wrepr U256 0x123456789abcdef0%Z) (wrepr U8 0) (wrepr U256 0x10) (wrepr U8 0)
    (wrepr U8 0)
    (Some false) (Some false) (Some false)
    (wrepr U256 0x123456789abcdef00%Z) (wrepr U256 0x123456789abcdef00%Z).
  Proof. by []. Qed.

  Goal test_wo_z FG0
    (wrepr U256 0) (wrepr U8 0) (wrepr U256 0) (wrepr U8 0) (wrepr U8 0)
    (Some false) (Some false) (Some true)
    (wrepr U256 0) (wrepr U256 0).
  Proof. by []. Qed.

  (* [BN_LID]: loads a 256-bit word from memory into the wide register whose
     index matches the first argument. *)

  (* Success: first arg equals the instruction's register index. *)
  Goal is_ok (id_semi (desc_otbn_op (BN_LID 5)) (wrepr U32 5) (wrepr U256 42)).
  Proof. by []. Qed.

  Goal is_ok (id_semi (desc_otbn_op (BN_LID 0)) (wrepr U32 0) (wrepr U256 0)).
  Proof. by []. Qed.

  Goal is_ok (id_semi (desc_otbn_op (BN_LID 31)) (wrepr U32 31) (wrepr U256 0xdeadbeef)).
  Proof. by []. Qed.

  (* Failure: first arg does not match the instruction's register index. *)
  Goal ~is_ok (id_semi (desc_otbn_op (BN_LID 5)) (wrepr U32 6) (wrepr U256 42)).
  Proof. by []. Qed.

  Goal ~is_ok (id_semi (desc_otbn_op (BN_LID 0)) (wrepr U32 1) (wrepr U256 0)).
  Proof. by []. Qed.

  Goal ~is_ok (id_semi (desc_otbn_op (BN_LID 31)) (wrepr U32 0) (wrepr U256 0)).
  Proof. by []. Qed.

End VALIDATION_SEM.
