(* OTBN instruction set *)

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

#[local] Open Scope Z.
#[local] Open Scope ring_scope.

Module E.
  Definition no_semantics : error := ErrSemUndef.
End E.

(* TODO_OTBN
   This is because we can't parse BN.ADD so we do BN_ADD.
   Can we avoid this? *)
Section ASCII.
  Import Ascii.

  #[local] Open Scope char_scope.

  Fixpoint replace_dot (s : string) : string :=
    match s with
    | EmptyString => EmptyString
    | String c s =>
        let c' := if c == "." then "_" else c in
        String c' (replace_dot s)
    end.

End ASCII.

Section PRIM.

Context {asm_op : Type}.

Let err s : result string asm_op :=
  Error ("invalid OTBN suffix, expected " ++ s)%string.

Definition is_prim_otbn_none (s : prim_otbn_suffix) : bool :=
  if s is {| otbn_suff_fg := None; otbn_suff_wb := None; |} then true
  else false.

Definition is_prim_otbn_suff_ws (s : prim_otbn_suffix) : option wsize :=
  if s is {| otbn_suff_ws := ows; otbn_suff_fg := None; otbn_suff_wb := None; |}
  then Some (odflt reg_size ows)
  else None.

Definition is_prim_otbn_suff_fg (s : prim_otbn_suffix) : option bn_flag_group :=
  if s is {| otbn_suff_ws := None; otbn_suff_fg := ofg; otbn_suff_wb := None; |}
  then Some (odflt FG0 ofg)
  else None.

Definition is_prim_otbn_suff_wb
  (s : prim_otbn_suffix) : option (bn_flag_group * bn_halfword_writeback) :=
  if s is
    {| otbn_suff_ws := None; otbn_suff_fg := ofg; otbn_suff_wb := Some wb; |}
  then Some (odflt FG0 ofg, wb)
  else None.

Definition prim_otbn_none op :=
  PrimOTBN (fun s => if is_prim_otbn_none s then ok op else err "no suffix").

Definition prim_otbn_ws f :=
  PrimOTBN (fun s =>
    if is_prim_otbn_suff_ws s is Some ws then ok (f ws)
    else err "only an optional word size"
  ).

Definition prim_otbn_fg f :=
  PrimOTBN (fun s =>
    if is_prim_otbn_suff_fg s is Some fg then ok (f fg)
    else err "only an optional flag group"
  ).

Definition prim_otbn_mulqacc_so f :=
  PrimOTBN (fun s =>
    if is_prim_otbn_suff_wb s is Some (fg, wb) then ok (f fg wb)
    else err "a writeback and an optional flag group"
  ).

End PRIM.

(* -------------------------------------------------------------------------- *)
(* 32-bit operations. *)

#[only(eqbOK)] derive
Variant rv_mnemonic : Type :=
| ADD  (* Addition. *)
| ADDI (* Addition (immediate). *)
| SUB  (* Subtraction. *)

| AND  (* Bitwise AND. *)
| ANDI (* Bitwise AND (immediate). *)
| OR   (* Bitwise OR. *)
| ORI  (* Bitwise OR (immediate). *)
| XOR  (* Bitwise XOR. *)
| XORI (* Bitwise XOR (immediate). *)

| SLL  (* Logical left shift. *)
| SLLI (* Logical left shift (immediate). *)
| SRL  (* Logical right shift. *)
| SRLI (* Logical right shift (immediate). *)
| SRA  (* Arithmetic right shift. *)
| SRAI (* Arithmetic right shift (immediate). *)

| LUI  (* Load upper immediate. *)

| LW  (* Load word. *)
| SW  (* Store word. *)

| LI  (* Load 32 bit immediate. *)
| LA  (* Load address. *)

| NOP

(* TODO_OTBN missing CSRRS *)
.

#[export]
Instance eqTC_rv_mnemonic : eqTypeC rv_mnemonic :=
  { ceqP := rv_mnemonic_eqb_OK; }.

Canonical rv_mnemonic_eqType := ceqT_eqType (ceqT := eqTC_rv_mnemonic).

Definition rv_mnemonics : seq rv_mnemonic :=
  [:: ADD; ADDI; SUB; AND; ANDI; OR; ORI; XOR; XORI; SLL; SLLI; SRL; SRLI; SRA
    ; SRAI; LUI; LW; SW; LI; LA; NOP
  ].

Lemma rv_mnemonic_fin_axiom : Finite.axiom rv_mnemonics.
Proof. by case. Qed.

#[export]
Instance finTC_rv_mnemonic : finTypeC rv_mnemonic :=
  { cenumP := rv_mnemonic_fin_axiom; }.

Definition rv_mnemonic_to_string (mn : rv_mnemonic) : string :=
  match mn with
  | ADD => "ADD"
  | ADDI => "ADDI"
  | SUB => "SUB"
  | AND => "AND"
  | ANDI => "ANDI"
  | OR => "OR"
  | ORI => "ORI"
  | XOR => "XOR"
  | XORI => "XORI"
  | SLL => "SLL"
  | SLLI => "SLLI"
  | SRL => "SRL"
  | SRLI => "SRLI"
  | SRA => "SRA"
  | SRAI => "SRAI"
  | LUI => "LUI"
  | LW => "LW"
  | SW => "SW"
  | LI => "LI"
  | LA => "LA"
  | NOP => "NOP"
  end.

(* -------------------------------------------------------------------------- *)
(* Basic big number arithmetic.
   All these set one of the flag groups and take an optional shift. *)

#[only(eqbOK)] derive
Variant bn_basic_mnemonic :=
| BN_ADD   (* Add. *)
| BN_ADDC  (* Add with carry. *)
| BN_SUB   (* Subtract. *)
| BN_SUBB  (* Subtract with borrow. *)

| BN_AND  (* Bitwise AND. *)
| BN_OR   (* Bitwise OR. *)
| BN_NOT  (* Bitwise NOT. *)
| BN_XOR  (* Bitwise XOR. *)

| BN_CMP   (* Compare. *)
| BN_CMPB  (* Compare with borrow. *)
.

#[export]
Instance eqTC_bn_basic_mnemonic : eqTypeC bn_basic_mnemonic :=
  { ceqP := bn_basic_mnemonic_eqb_OK; }.

Canonical bn_basic_mnemonic_eqType :=
  ceqT_eqType (ceqT := eqTC_bn_basic_mnemonic).

Definition bn_basic_mnemonics : seq bn_basic_mnemonic :=
  [:: BN_ADD; BN_ADDC; BN_SUB; BN_SUBB; BN_AND; BN_OR; BN_NOT; BN_XOR; BN_CMP
    ; BN_CMPB
  ].

Lemma bn_basic_mnemonic_fin_axiom : Finite.axiom bn_basic_mnemonics.
Proof. by case. Qed.

#[export]
Instance finTC_bn_basic_mnemonic : finTypeC bn_basic_mnemonic :=
  { cenumP := bn_basic_mnemonic_fin_axiom; }.

Definition bn_basic_mnemonic_to_string (mn : bn_basic_mnemonic) : string :=
  match mn with
  | BN_ADD => "BN.ADD"
  | BN_ADDC => "BN.ADDC"
  | BN_SUB => "BN.SUB"
  | BN_SUBB => "BN.SUBB"
  | BN_AND => "BN.AND"
  | BN_OR => "BN.OR"
  | BN_NOT => "BN.NOT"
  | BN_XOR => "BN.XOR"
  | BN_CMP => "BN.CMP"
  | BN_CMPB => "BN.CMPB"
  end.

#[only(eqbOK)] derive
Variant otbn_op : Type :=
| RV32 of rv_mnemonic
| BN_basic of bn_basic_mnemonic & bn_flag_group
| BN_basic_shift of bn_basic_mnemonic & bn_flag_group & bn_register_shift

| BN_ADDI of bn_flag_group  (* Add immediate. *)
| BN_SUBI of bn_flag_group  (* Subtract immediate. *)

| BN_MOV                   (* Copy content between wide registers. *)
| BN_RSHI                  (* Concatenate and right shift immediate. *)
| BN_SEL of bn_flag_group  (* Flag Select. *)

| BN_ADDM  (* Pseudo-modulo add. *)
| BN_SUBM  (* Pseudo-modulo subtraction. *)

(* Quarter-word multiply and accumulate. *)
(* TODO_OTBN we should parameterize these by the quarterword selectors, such
   that they take two arguments fewer. We should then add an operator that takes
   a subword and define an extra op
       BN_MULQACC(x[u64 i], y[u64 j], shift)
   and compile it to the parameterized ones
       BN_MULQACC_i_j(x, y, shift). *)
| BN_MULQACC
| BN_MULQACC_Z (* Zero the accumulator first. *)

(* Quarter-word multiply and accumulate with full-word writeback. *)
| BN_MULQACC_WO of bn_flag_group
| BN_MULQACC_WO_Z of bn_flag_group

(* Quarter-word multiply and accumulate with half-word writeback. *)
| BN_MULQACC_SO of bn_flag_group & bn_halfword_writeback
| BN_MULQACC_SO_Z of bn_flag_group & bn_halfword_writeback

(* Wrappers for WSRR and WSRW. *)
| BN_ACCR  (* Read from ACC register to wide register. *)
| BN_ACCW  (* Write from wide register to ACC register. *)
| BN_MODR  (* Read from MOD register to wide register. *)
| BN_MODW  (* Write from wide register to MOD register. *)

(* Indirect indexing. *)
| BN_LID
| BN_SID
.

#[export]
Instance eqTC_otbn_op : eqTypeC otbn_op := { ceqP := otbn_op_eqb_OK; }.

Canonical otbn_op_eqType := ceqT_eqType (ceqT := eqTC_otbn_op).

Definition otbn_op_to_string (op : otbn_op) : string :=
  match op with
  | RV32 mn => rv_mnemonic_to_string mn
  | BN_basic mn _ => bn_basic_mnemonic_to_string mn
  | BN_basic_shift mn _ _ => bn_basic_mnemonic_to_string mn
  | BN_ADDI _ => "BN.ADDI"
  | BN_SUBI _ => "BN.SUBI"
  | BN_MOV => "BN.MOV"
  | BN_RSHI => "BN.RSHI"
  | BN_SEL _ => "BN.SEL"
  | BN_ADDM => "BN.ADDM"
  | BN_SUBM => "BN.SUBM"
  | BN_MULQACC => "BN.MULQACC"
  | BN_MULQACC_Z => "BN.MULQACC.Z"
  | BN_MULQACC_WO _ => "BN.MULQACC.WO"
  | BN_MULQACC_WO_Z _ => "BN.MULQACC.WO.Z"
  | BN_MULQACC_SO _ _ => "BN.MULQACC.SO"
  | BN_MULQACC_SO_Z _ _ => "BN.MULQACC.SO.Z"
  | BN_ACCR => "BN.ACCR"
  | BN_ACCW => "BN.ACCW"
  | BN_MODR => "BN.MODR"
  | BN_MODW => "BN.MODW"
  | BN_LID => "BN.LID"
  | BN_SID => "BN.SID"
  end.

(* -------------------------------------------------------------------------- *)
(* Instruction descriptions. *)

Section I_ARGS_KINDS.

  Definition ak_u2 := CAimm (CAimmC_otbn_nbits Unsigned 2) U8.
  Definition ak_u8 := CAimm (CAimmC_otbn_nbits Unsigned 8) U8.
  Definition ak_u10 := CAimm (CAimmC_otbn_nbits Unsigned 10) U32.
  Definition ak_s12 := CAimm (CAimmC_otbn_nbits Signed 12) U32.
  Definition ak_bn_shift := CAimm CAimmC_otbn_bn_shift U8.

  Let xreg := [:: CAxmm ].
  Let imm_u8 := [:: ak_u8 ].
  Let imm_u10 := [:: ak_u10 ].
  Let imm_s12 := [:: ak_s12 ].

  (* Quarter word *)
  Let imm_q := [:: ak_u2 ].
  Let imm_bn_shift := [:: ak_bn_shift ].
  Let imm_mulqacc_shift := [:: CAimm CAimmC_otbn_mulqacc_shift U8 ].

  Definition ak_xreg : i_args_kinds :=
    [:: [:: xreg ] ].

  Definition ak_xreg_xreg : i_args_kinds :=
    [:: [:: xreg; xreg ] ].

  Definition ak_xreg_xreg_xreg : i_args_kinds :=
    [:: [:: xreg; xreg; xreg ] ].

  Definition ak_xreg_xreg_imm10 : i_args_kinds :=
    [:: [:: xreg; xreg; imm_u10 ] ].

  Definition ak_xreg_xreg_xreg_bool : i_args_kinds :=
    [:: [:: xreg; xreg; xreg; [:: CAcond ] ] ].

  Definition ak_xreg_xreg_xreg_shift : i_args_kinds :=
    [:: [:: xreg; xreg; xreg; imm_u8 ] ].

  Definition ak_xreg_q_xreg_q_shift : i_args_kinds :=
    [:: [:: xreg; imm_q; xreg; imm_q; imm_mulqacc_shift ] ].

  Definition ak_xreg_xreg_q_xreg_q_shift : i_args_kinds :=
    [:: [:: xreg; xreg; imm_q; xreg; imm_q; imm_mulqacc_shift ] ].

  Definition ak_reg_mem : i_args_kinds :=
    [:: [:: [:: CAreg ]; [:: CAmem true ] ]].

  Definition ak_reg_xreg : i_args_kinds :=
    [:: [:: [:: CAreg ]; [:: CAxmm ] ]].

End I_ARGS_KINDS.


Section PP_ASM_OP.
  (* We need to catch the pseudo-instructions [BN_ACCR], [BN_ACCW],
     [BN_MODR], and [BN_MODW]. *)
  Let mk name args :=
    {|
      pp_aop_name := name;
      pp_aop_ext := PP_name;
      pp_aop_args := map (fun a => (reg_size, a)) args;
    |}.

  Let wsr_code_MOD : asm_arg := Imm (wrepr U8 0x0).
  Let wsr_code_ACC : asm_arg := Imm (wrepr U8 0x3).

  Definition pp_otbn_op (op : otbn_op) (args : seq asm_arg) : pp_asm_op :=
    match op with
    | BN_MODR => mk "bn.wsrr" (rcons args wsr_code_MOD)
    | BN_MODW => mk "bn.wsrw" (wsr_code_MOD :: args)
    | BN_ACCR => mk "bn.wsrr" (rcons args wsr_code_ACC)
    | BN_ACCW => mk "bn.wsrw" (wsr_code_ACC :: args)
    | _ => mk (otbn_op_to_string op) args
    end.

End PP_ASM_OP.

Lemma check_dest_unop_lword {ws adout} :
  all2 check_arg_dest [:: adout ] [:: lword ws ].
Proof. by case: adout. Qed.

(* -------------------------------------------------------------------------- *)
(* Instruction descriptions for the 32-bit ISA.
   These instructions are unary or binary word operations, so we define generic
   instruction descriptions [desc_rv_unop] and [desc_rv_binop]. *)

Definition acc_mod := [:: ACC; MOD ].
Definition EXa n := ADExplicit (AK_mem Aligned) n (ACR_avoid_xreg acc_mod).
Definition EXc n := ADExplicit AK_compute n (ACR_avoid_xreg acc_mod).

Section RV_DESC.

Context
  (ws : wsize)
  (mn : rv_mnemonic)
.

(* All RV instructions have a register as a first argument.
   Then they may take some more registers, and finally either a register, an
   immediate or an address. *)

Let ak_unary ak := [:: [:: [:: CAreg ]; [:: ak ]]].
Let ak_binary ak := [:: [:: [:: CAreg ]; [:: CAreg ]; [:: ak ]]].

Let pp_rv_op mn args := pp_otbn_op (RV32 mn) args.

(* Kind of the last argument. *)
Definition rv_last_ak : arg_kind :=
  match mn with
  | ADD | SUB | AND | OR | XOR | SLL | SRL | SRA => CAreg
  | ADDI | ANDI | ORI | XORI => ak_s12
  | SLLI | SRLI | SRAI => CAimm (CAimmC_otbn_nbits Unsigned 5) U8
  | LUI => CAimm (CAimmC_otbn_nbits Unsigned 20) U32
  | LW | SW => CAmem false
  | LI => CAimm (CAimmC_otbn_nbits Signed 32) U32
  | LA => CAmem true
  | NOP => CAreg (* absurd *)
  end.

Definition _desc_rv_unop
  (ad_in ad_out : arg_desc) (semi : word ws -> word ws) : instr_desc_t :=
  {|
    id_msb_flag := MSB_MERGE;
    id_tin := [:: lword ws ];
    id_in := [:: ad_in ];
    id_tout := [:: lword ws ];
    id_out := [:: ad_out ];
    id_semi := fun x => ok (semi x);
    id_args_kinds := ak_unary rv_last_ak;
    id_nargs := 2;
    id_str_jas := pp_s (rv_mnemonic_to_string mn);
    id_pp_asm := pp_rv_op mn;
    id_valid := ws == U32; (* TODO_OTBN remove? *)
    id_safe := [::];
    id_eq_size := refl_equal;
    id_check_dest := check_dest_unop_lword;
    id_safe_wf := refl_equal;
    id_semi_errty := fun _ => sem_lprod_ok_error _ _;
    id_semi_safe := fun _ => sem_lprod_ok_safe _ _;
  |}.

Let desc_rv_unop := _desc_rv_unop (Ea 1) (Ea 0).

(* All instructions raise errors when using [x1] if the call stack is empty,
   but this is impossible with our model.
   They have no other unsafe behavior. *)
Definition desc_rv_binop
  (semi : word ws -> word ws -> word ws) : instr_desc_t :=
  {|
    id_msb_flag := MSB_MERGE;
    id_tin := [:: lword ws; lword ws ];
    id_in := [:: Ea 1; Ea 2 ];
    id_tout := [:: lword ws ];
    id_out := [:: Ea 0 ];
    id_semi := fun x y => ok (semi x y);
    id_args_kinds := ak_binary rv_last_ak;
    id_nargs := 3;
    id_str_jas := pp_s (rv_mnemonic_to_string mn);
    id_pp_asm := pp_rv_op mn;
    id_valid := ws == U32; (* TODO_OTBN remove? *)
    id_safe := [::];
    id_eq_size := refl_equal;
    id_check_dest := refl_equal;
    id_safe_wf := refl_equal;
    id_semi_errty := fun _ => sem_lprod_ok_error _ _;
    id_semi_safe := fun _ => sem_lprod_ok_safe _ _;
  |}.

Definition desc_nop :=
  {|
    id_msb_flag := MSB_MERGE;
    id_tin := [::];
    id_in := [:: ];
    id_tout := [::];
    id_out := [::];
    id_semi := ok tt;
    id_args_kinds := [:: [::] ];
    id_nargs := 0;
    id_str_jas := pp_s (rv_mnemonic_to_string NOP);
    id_pp_asm := pp_rv_op NOP;
    id_valid := true;
    id_safe := [::];
    id_eq_size := refl_equal;
    id_check_dest := refl_equal;
    id_safe_wf := refl_equal;
    id_semi_errty := fun _ => sem_lprod_ok_error _ _;
    id_semi_safe := fun _ => sem_lprod_ok_safe _ _;
  |}.


(* TODO_OTBN the reference defines the semantics in terms of integer arithmetic
   and masks rather than modular arithmetic, perhaps it we should use that? *)
Definition _desc_rv_mnemonic : instr_desc_t :=
  match mn with
  | ADD | ADDI => desc_rv_binop wadd
  | SUB => desc_rv_binop wsub
  | AND | ANDI => desc_rv_binop wand
  | OR | ORI => desc_rv_binop wor
  | XOR | XORI => desc_rv_binop wxor
  | SLL | SLLI => desc_rv_binop (fun x y => wshl x (Z.land (wunsigned y) 31))
  | SRL | SRLI => desc_rv_binop (fun x y => wshr x (Z.land (wunsigned y) 31))
  | SRA | SRAI => desc_rv_binop (fun x y => wsar x (Z.land (wunsigned y) 31))
  | LUI => desc_rv_unop (fun x => wshl x 12)
  (* TODO_OTBN: LW/SW must check addr = (grs1 + offset) mod 2^32 is a valid
     4-byte aligned DMEM address; otherwise raise BAD_DATA_ADDR. *)
  | LW => desc_rv_unop id (* TODO_OTBN double check that it fails on unaligned *)
  | SW => _desc_rv_unop (Ea 0) (Ea 1) id (* TODO_OTBN double check that it fails on unaligned *)
  | LI => desc_rv_unop id
  | LA => _desc_rv_unop (Ec 1) (Ea 0) id
  | NOP => desc_nop
  end.

End RV_DESC.

(* TODO_OTBN: Right now we only use ws = U32, but we define it generically. *)
Notation desc_rv_mnemonic := (_desc_rv_mnemonic reg_size) (only parsing).


(* -------------------------------------------------------------------------- *)
(* Big Number ISA. *)

Definition ty_mlz : seq ltype := [:: lbool; lbool; lbool ].
Definition ty_cmlz : seq ltype := lbool :: ty_mlz.

Section CURRENT_FLAG_GROUP.

Context (fg : bn_flag_group).

Definition current_mlz : seq rflag :=
  match fg with
  | FG0 => [:: MF0; LF0; ZF0 ]
  | FG1 => [:: MF1; LF1; ZF1 ]
  end.

Definition current_CF : rflag :=
  match fg with
  | FG0 => CF0
  | FG1 => CF1
  end.

Definition current_cmlz : seq rflag := current_CF :: current_mlz.

Definition ad_mlz : seq arg_desc := map F current_mlz.
Definition ad_cmlz : seq arg_desc := map F current_cmlz.

End CURRENT_FLAG_GROUP.

Definition CF_of_Z (z : Z) : option bool :=
  Some (Z.land (Z.shiftr z 256) 1 == 1).
Definition MF_of_word (res : u256) : option bool := Some (msb res).
Definition LF_of_word (res : u256) : option bool := Some (lsb res).
Definition ZF_of_word (res : u256) : option bool := Some (res == 0)%R.

Definition with_mlz (res : u256) : sem_ltuple (ty_mlz ++ [:: lword256 ]) :=
  (:: MF_of_word res
    , LF_of_word res
    , ZF_of_word res
    & res
  ).

Definition with_cmlz
  (res : u256) (res_unsigned : Z) : sem_ltuple (ty_cmlz ++ [:: lword256 ]) :=
  add_tuple (CF_of_Z res_unsigned) (with_mlz res).

Definition drop_c (idt : instr_desc_t) : instr_desc_t := idt_drop1 idt.

(* -------------------------------------------------------------------------- *)
(* Basic BN mnemonics.
   Several basic BN mnemonics are word operations that shift their last
   argument. Some set flags, and some take the carry flag as input.
   We define generic [instr_desc_t] for these parameterized by the semantics
   (modular and Z semantics for the ones that set flags).
   These are
   - Those that set flags, e.g. [BN_ADD]: [desc_bn_basic_binop_cmlz].
   - Those that don't set the [C] flag, e.g. [BN_AND]:
     [desc_bn_basic_unop_mlz] and [desc_bn_basic_binop_mlz].
   - Those that use the carry flag, e.g. [BN_ADDC]: [desc_bn_basic_carry_binop].
   The instructions [BN_CMP] and [BN_CMPB] are defined separately. *)

Definition word_shift_of_reg_shift
  (sh : bn_register_shift) {ws : wsize} (x : word ws) (sham : Z) : word ws :=
  let f :=
    match sh with
    | RS_left => wshl
    | RS_right => wshr
    end
  in
  f ws x sham.

Definition Z_shift_of_reg_shift
 (sh : bn_register_shift) {ws : wsize} (x : word ws) (sham : Z) : Z :=
  let f :=
    match sh with
    | RS_left => Z.shiftl
    | RS_right => Z.shiftr
    end
  in
  f (wunsigned x) sham.

#[local]
Notation rtuple_drop5th xs :=
  (Let: (:: x0, x1, x2, x3 & x4 ) := xs in ok (:: x0, x1, x2 & x3 ))
  (only parsing).

Section BN_BASIC_DESC.

Let pp_bn_basic_op mn fg args := pp_otbn_op (BN_basic mn fg) args.

Let semi_unop_mlz (semi : u256 -> u256) :
  semi_type [:: lword256 ] (ty_mlz ++ [:: lword256 ]) :=
  fun x => ok (with_mlz (semi x)).

Let semi_binop_cmlz
  (semi : u256 -> u256 -> u256)
  (semiZ : Z -> Z -> Z) :
  semi_type [:: lword256; lword256 ] (ty_cmlz ++ [:: lword256 ]) :=
  fun x y =>
    let res_unsigned := semiZ (wunsigned x) (wunsigned y) in
    ok (with_cmlz (semi x y) res_unsigned).

Definition semi_carry_binop_cmlz
  (semi : u256 -> u256 -> u256)
  (semiZ : Z -> Z -> Z) :
  semi_type
    [:: lword256; lword256; lbool ]
    (ty_cmlz ++ [:: lword256 ]) :=
  fun x y cf =>
    let c := Z.b2z cf in
    let res := semi (semi x y) (wrepr U256 c) in
    let res_unsigned := semiZ (semiZ (wunsigned x) (wunsigned y)) c in
    ok (with_cmlz res res_unsigned).

Context
  (mn : bn_basic_mnemonic)
  (fg : bn_flag_group)
.

Definition desc_bn_basic_unop
  (semi : u256 -> u256) (semiZ : Z -> Z) : instr_desc_t :=
  {|
    id_msb_flag := MSB_MERGE;
    id_tin := [:: lword256 ];
    id_in := [:: EXa 1 ];
    id_tout := ty_mlz ++ [:: lword256 ];
    id_out := ad_mlz fg ++ [:: EXa 0 ];
    id_semi := semi_unop_mlz semi;
    id_args_kinds := ak_xreg_xreg;
    id_nargs := 2;
    id_str_jas := pp_s (bn_basic_mnemonic_to_string mn);
    id_pp_asm := pp_bn_basic_op mn fg;
    id_valid := true;
    id_safe := [::];
    id_eq_size := ltac:(by case: fg);
    id_check_dest := ltac:(by case: fg);
    id_safe_wf := refl_equal;
    id_semi_errty := fun _ => sem_lprod_ok_error _ _;
    id_semi_safe := fun _ => sem_lprod_ok_safe _ _;
  |}.

Definition desc_bn_basic_binop
  (semi : u256 -> u256 -> u256) (semiZ : Z -> Z -> Z) : instr_desc_t :=
  {|
    id_msb_flag := MSB_MERGE;
    id_tin := [:: lword256; lword256 ];
    id_in := [:: EXa 1; EXa 2 ];
    id_tout := ty_cmlz ++ [:: lword256 ];
    id_out := ad_cmlz fg ++ [:: EXa 0 ];
    id_semi := semi_binop_cmlz semi semiZ;
    id_args_kinds := ak_xreg_xreg_xreg;
    id_nargs := 3;
    id_str_jas := pp_s (bn_basic_mnemonic_to_string mn);
    id_pp_asm := pp_bn_basic_op mn fg;
    id_valid := true;
    id_safe := [::];
    id_eq_size := ltac:(by case: fg);
    id_check_dest := ltac:(by case: fg);
    id_safe_wf := refl_equal;
    id_semi_errty := fun _ => sem_lprod_ok_error _ _;
    id_semi_safe := fun _ => sem_lprod_ok_safe _ _;
  |}.

Let desc_bin_mlz semi semiZ := idt_drop1 (desc_bn_basic_binop semi semiZ).

Definition desc_bn_basic_carry_binop
  (semi : u256 -> u256 -> u256) (semiZ : Z -> Z -> Z) : instr_desc_t :=
  {|
    id_msb_flag := MSB_MERGE;
    id_tin := [:: lword256; lword256; lbool ];
    id_in := [:: EXa 1; EXa 2; F (current_CF fg) ];
    id_tout := ty_cmlz ++ [:: lword256 ];
    id_out := ad_cmlz fg ++ [:: EXa 0 ];
    id_semi := semi_carry_binop_cmlz semi semiZ;
    id_args_kinds := ak_xreg_xreg_xreg;
    id_nargs := 3;
    id_str_jas := pp_s (bn_basic_mnemonic_to_string mn);
    id_pp_asm := pp_bn_basic_op mn fg;
    id_valid := true;
    id_safe := [::];
    id_eq_size := ltac:(by case: fg);
    id_check_dest := ltac:(by case: fg);
    id_safe_wf := refl_equal;
    id_semi_errty := fun _ => sem_lprod_ok_error _ _;
    id_semi_safe := fun _ => sem_lprod_ok_safe _ _;
  |}.

Definition desc_BN_CMP : instr_desc_t :=
  {|
    id_msb_flag := MSB_MERGE;
    id_tin := [:: lword256; lword256 ];
    id_in := [:: EXa 0; EXa 1 ];
    id_tout := ty_cmlz;
    id_out := ad_cmlz fg;
    id_semi := fun x y => rtuple_drop5th (semi_binop_cmlz wsub Z.sub x y);
    id_args_kinds := ak_xreg_xreg;
    id_nargs := 2;
    id_str_jas := pp_s (bn_basic_mnemonic_to_string BN_CMP);
    id_pp_asm := pp_bn_basic_op BN_CMP fg;
    id_valid := true;
    id_safe := [::];
    id_eq_size := ltac:(by case: fg);
    id_check_dest := ltac:(by case: fg);
    id_safe_wf := refl_equal;
    id_semi_errty := fun _ => sem_lprod_ok_error _ _;
    id_semi_safe := fun _ => sem_lprod_ok_safe _ _;
  |}.

Definition desc_BN_CMPB : instr_desc_t :=
  {|
    id_msb_flag := MSB_MERGE;
    id_tin := [:: lword256; lword256; lbool ];
    id_in := [:: EXa 0; EXa 1; F (current_CF fg) ];
    id_tout := ty_cmlz;
    id_out := ad_cmlz fg;
    id_semi :=
      fun x y cf => rtuple_drop5th (semi_carry_binop_cmlz wsub Z.sub x y cf);
    id_args_kinds := ak_xreg_xreg;
    id_nargs := 2;
    id_str_jas := pp_s (bn_basic_mnemonic_to_string BN_CMPB);
    id_pp_asm := pp_bn_basic_op BN_CMPB fg;
    id_valid := true;
    id_safe := [::];
    id_eq_size := ltac:(by case: fg);
    id_check_dest := ltac:(by case: fg);
    id_safe_wf := refl_equal;
    id_semi_errty := fun _ => sem_lprod_ok_error _ _;
    id_semi_safe := fun _ => sem_lprod_ok_safe _ _;
  |}.

Definition desc_bn_basic_mnemonic : instr_desc_t :=
  match mn with
  | BN_ADD => desc_bn_basic_binop wadd Z.add
  | BN_ADDC => desc_bn_basic_carry_binop wadd Z.add
  | BN_SUB => desc_bn_basic_binop wsub Z.sub
  | BN_SUBB => desc_bn_basic_carry_binop wsub Z.sub
  | BN_AND => desc_bin_mlz wand Z.land
  | BN_OR => desc_bin_mlz wor Z.lor
  | BN_NOT => desc_bn_basic_unop wnot Z.lnot
  | BN_XOR => desc_bin_mlz wxor Z.lxor
  | BN_CMP => desc_BN_CMP
  | BN_CMPB => desc_BN_CMPB
  end.

End BN_BASIC_DESC.

Section BN_BASIC_SHIFT_DESC.

Notation mk_semi1_shifted sh :=
  (arch_mk_semi1_shifted (@word_shift_of_reg_shift sh)).
Notation mk_semi2_2_shifted sh :=
  (arch_mk_semi2_2_shifted (@word_shift_of_reg_shift sh)).
Notation mk_semi3_2_shifted sh :=
  (arch_mk_semi3_2_shifted (@word_shift_of_reg_shift sh)).

Notation mk_shifted1 mn fg sh :=
  (let d := desc_bn_basic_mnemonic mn fg in
   arch_mk_shifted ak_bn_shift d
     (mk_semi1_shifted sh (id_semi d))
     (fun h => mk_semi1_shifted_errty (d.(id_semi_errty) h))
     (fun h => mk_semi1_shifted_safe _ (d.(id_semi_safe) h))
  ).
Notation mk_shifted2 mn fg sh :=
  (let d := desc_bn_basic_mnemonic mn fg in
   arch_mk_shifted ak_bn_shift d
     (mk_semi2_2_shifted sh (id_semi d))
     (fun h => mk_semi2_2_shifted_errty (d.(id_semi_errty) h))
     (fun h => mk_semi2_2_shifted_safe _ (d.(id_semi_safe) h))
  ).
Notation mk_shifted_carry mn fg sh :=
  (let d := desc_bn_basic_mnemonic mn fg in
   arch_mk_shifted ak_bn_shift d
     (mk_semi3_2_shifted sh (id_semi d))
     (fun h => mk_semi3_2_shifted_errty (d.(id_semi_errty) h))
     (fun h => mk_semi3_2_shifted_safe _ (d.(id_semi_safe) h))
  ).

Definition desc_bn_basic_shift_mnemonic
  (mn : bn_basic_mnemonic)
  (fg : bn_flag_group)
  (sh : bn_register_shift) :
  instr_desc_t :=
  match mn with
  | BN_ADD => mk_shifted2 BN_ADD fg sh
  | BN_SUB => mk_shifted2 BN_SUB fg sh
  | BN_AND => mk_shifted2 BN_AND fg sh
  | BN_OR => mk_shifted2 BN_OR fg sh
  | BN_XOR => mk_shifted2 BN_XOR fg sh
  | BN_CMP => mk_shifted2 BN_CMP fg sh
  | BN_NOT => mk_shifted1 BN_NOT fg sh
  | BN_ADDC => mk_shifted_carry BN_ADDC fg sh
  | BN_SUBB => mk_shifted_carry BN_SUBB fg sh
  | BN_CMPB => mk_shifted_carry BN_CMPB fg sh
  end.

End BN_BASIC_SHIFT_DESC.

(* -------------------------------------------------------------------------- *)
(* Modular BN mnemonics.
   These are arithmetic operations modulo some number (in the [MOD] register).
   We define a generic instruction description parameterized by the integer
   semantics. *)

Section MODULAR_OP.

Definition semi_modular_binop (ws : wsize) (body : Z -> Z -> Z -> Z) :
  semi_type [:: lword ws; lword ws; lword ws ] [:: lword ws ] :=
  fun wx wy wm =>
    ok (wrepr ws (body (wunsigned wx) (wunsigned wy) (wunsigned wm))).

Definition addm_result (x y m : Z) : Z :=
  let res := x + y in
  if res >=? m then res - m else res.

Definition subm_result (x y m : Z) : Z :=
  let res := x - y in
  if res <? 0 then res + m else res.

(* TODO_OTBN: Right now we only use ws = U256, but we define it
   generically. *)

Definition _desc_otbn_op_modular_binop
  (mn : otbn_op) (ws : wsize) (body : Z -> Z -> Z -> Z) : instr_desc_t :=
  {|
    id_msb_flag := MSB_MERGE;
    id_tin := [:: lword ws; lword ws; lword ws ];
    id_in := [:: EXa 1; EXa 2; Xreg MOD ];
    id_tout := [:: lword ws ];
    id_out := [:: EXa 0 ];
    id_semi := semi_modular_binop body;
    id_args_kinds := ak_xreg_xreg_xreg;
    id_nargs := 3;
    id_str_jas := pp_s (otbn_op_to_string mn);
    id_pp_asm := pp_otbn_op mn;
    id_valid := ws == U256;
    id_safe := [::];
    id_eq_size := refl_equal;
    id_check_dest := refl_equal;
    id_safe_wf := refl_equal;
    id_semi_errty := fun _ => sem_lprod_ok_error _ _;
    id_semi_safe := fun _ => sem_lprod_ok_safe _ _;
  |}.

Let desc_otbn_op_modular_binop mn := _desc_otbn_op_modular_binop mn U256.

Definition desc_BN_ADDM : instr_desc_t :=
  desc_otbn_op_modular_binop BN_ADDM addm_result.

Definition desc_BN_SUBM : instr_desc_t :=
  desc_otbn_op_modular_binop BN_SUBM subm_result.

End MODULAR_OP.

Definition semi_binopI_cmlz
  (semi : u256 -> u256 -> u256)
  (semiZ : Z -> Z -> Z) :
  semi_type [:: lword256; lword256 ] (ty_cmlz ++ [:: lword256 ]) :=
  fun x y =>
    let res := semi x y in
    let res_unsigned := semiZ (wunsigned x) (wunsigned y) in
    ok (with_cmlz res res_unsigned).

Definition desc_bn_binopI
  (op : otbn_op)
  (fg : bn_flag_group)
  (semi : u256 -> u256 -> u256)
  (semiZ : Z -> Z -> Z) :
  instr_desc_t :=
  {|
    id_msb_flag := MSB_MERGE;
    id_tin := [:: lword256; lword256 ];
    id_in := [:: EXa 1; Ea 2 ];
    id_tout := ty_cmlz ++ [:: lword256 ];
    id_out := ad_cmlz fg ++ [:: EXa 0 ];
    id_semi := semi_binopI_cmlz semi semiZ;
    id_args_kinds := ak_xreg_xreg_imm10;
    id_nargs := 3;
    id_str_jas := pp_s (otbn_op_to_string op);
    id_pp_asm := pp_otbn_op op;
    id_valid := true;
    id_safe := [::];
    id_eq_size := ltac:(by case: fg);
    id_check_dest := ltac:(by case: fg);
    id_safe_wf := refl_equal;
    id_semi_errty := fun _ => sem_lprod_ok_error _ _;
    id_semi_safe := fun _ => sem_lprod_ok_safe _ _;
  |}.

Definition desc_BN_MOV : instr_desc_t :=
  {|
    id_msb_flag := MSB_MERGE;
    id_tin := [:: lword256 ];
    id_in := [:: EXa 1 ];
    id_tout := [:: lword256 ];
    id_out := [:: EXa 0 ];
    id_semi := fun x => ok x;
    id_args_kinds := ak_xreg_xreg;
    id_nargs := 2;
    id_str_jas := pp_s (otbn_op_to_string BN_MOV);
    id_pp_asm := pp_otbn_op BN_MOV;
    id_valid := true;
    id_safe := [::];
    id_eq_size := refl_equal;
    id_check_dest := refl_equal;
    id_safe_wf := refl_equal;
    id_semi_errty := fun _ => sem_lprod_ok_error _ _;
    id_semi_safe := fun _ => sem_lprod_ok_safe _ _;
  |}.

Definition desc_BN_SEL (fg : bn_flag_group) : instr_desc_t :=
  {|
    id_msb_flag := MSB_MERGE;
    id_tin := [:: lword256; lword256; lbool ];
    id_in := [:: EXa 1; EXa 2; Ea 3 ];
    id_tout := [:: lword256 ];
    id_out := [:: EXa 0 ];
    id_semi := fun wn wm b => ok (if b then wn else wm);
    id_args_kinds := ak_xreg_xreg_xreg_bool;
    id_nargs := 4;
    id_str_jas := pp_s (otbn_op_to_string (BN_SEL fg));
    id_pp_asm := pp_otbn_op (BN_SEL fg);
    id_valid := true;
    id_safe := [::];
    id_eq_size := refl_equal;
    id_check_dest := refl_equal;
    id_safe_wf := refl_equal;
    id_semi_errty := fun _ => sem_lprod_ok_error _ _;
    id_semi_safe := fun _ => sem_lprod_ok_safe _ _;
  |}.

(* TODO_OTBN we are not modeling the semantics exactly as specified because we
   don't have a [u512] type. *)
Definition semi_BN_RSHI (x y : u256) (wsham : u8) : exec u256 :=
  let sham := wunsigned wsham in
  let lo_part := wshr y sham in
  let hi_part := wshl x (256 - sham) in
  ok (wor hi_part lo_part).

Definition desc_BN_RSHI : instr_desc_t :=
  {|
    id_msb_flag := MSB_MERGE;
    id_tin := [:: lword256; lword256; lword8 ];
    id_in := [:: EXa 1; EXa 2; Ea 3 ];
    id_tout := [:: lword256 ];
    id_out := [:: EXa 0 ];
    id_semi := semi_BN_RSHI;
    id_args_kinds := ak_xreg_xreg_xreg_shift;
    id_nargs := 4;
    id_str_jas := pp_s (otbn_op_to_string BN_RSHI);
    id_pp_asm := pp_otbn_op BN_RSHI;
    id_valid := true;
    id_safe := [::];
    id_eq_size := refl_equal;
    id_check_dest := refl_equal;
    id_safe_wf := refl_equal;
    id_semi_errty := fun _ => sem_lprod_ok_error _ _;
    id_semi_safe := fun _ => sem_lprod_ok_safe _ _;
  |}.


(* -------------------------------------------------------------------------- *)
(* [MULQACC]. *)

Section MULQACC.

Context
  (fg : bn_flag_group)
  (wb : bn_halfword_writeback)
.

(* Extract the [n]-bit subword starting at [i]. *)
Definition extract_subword {ws : wsize} (x : word ws) (i n : Z) : word ws :=
  wand (wshr x (i * n)) (wrepr ws (Z.shiftl 1 n - 1)).

(* Get the [i]-th 64-bit word of a 256-bit word.
   Precondition: 0 <= i < 4 *)
Definition get_qword (x : u256) (ix : u8) : u256 :=
  extract_subword x (wunsigned ix) 64.

(* Precondition: [sham] is in the range [0, 192] and a multiple of 64. *)
Definition shift_mulqacc (x : u256) (wsham : u8) : u256 :=
  wshl x (wunsigned wsham).

Let base_mulqacc_tin :=
  [:: lword256; lword8; lword256; lword8; lword256; lword8 ].

Let base_mulqacc_z_tin :=
  [:: lword256; lword8; lword256; lword8; lword8 ].

Definition mulqacc
  (x : u256) (ix : u8) (y : u256) (iy : u8) (acc : u256) (sham : u8) : u256 :=
  let x_sub := get_qword x ix in
  let y_sub := get_qword y iy in
  let mul_res := shift_mulqacc (x_sub * y_sub) sham in
  acc + mul_res.

Definition semi_BN_MULQACC : semi_type base_mulqacc_tin [:: lword256 ] :=
  fun x ix y iy acc sham => ok (mulqacc x ix y iy acc sham).

(* TODO_OTBN: It would be better that the quarterword selectors are indices to
   the mnemonic instead of arguments. *)
Definition desc_BN_MULQACC : instr_desc_t :=
  {|
    id_msb_flag := MSB_MERGE;
    id_tin := base_mulqacc_tin;
    id_in := [:: EXa 0; Ea 1; EXa 2; Ea 3; Xreg ACC; Ea 4 ];
    id_tout := [:: lword256 ];
    id_out := [:: Xreg ACC ];
    id_semi := semi_BN_MULQACC;
    id_args_kinds := ak_xreg_q_xreg_q_shift;
    id_nargs := 5;
    id_str_jas := pp_s (otbn_op_to_string BN_MULQACC);
    id_pp_asm := pp_otbn_op BN_MULQACC;
    id_valid := true;
    id_safe := [::];
    id_eq_size := refl_equal;
    id_check_dest := refl_equal;
    id_safe_wf := refl_equal;
    id_semi_errty := fun _ => sem_lprod_ok_error _ _;
    id_semi_safe := fun _ => sem_lprod_ok_safe _ _;
  |}.

Definition desc_BN_MULQACC_Z : instr_desc_t :=
  {|
    id_msb_flag := MSB_MERGE;
    id_tin := base_mulqacc_z_tin;
    id_in := [:: EXa 0; Ea 1; EXa 2; Ea 3; Ea 4 ];
    id_tout := [:: lword256 ];
    id_out := [:: Xreg ACC ];
    id_semi := fun x ix y iy sham => semi_BN_MULQACC x ix y iy 0%R sham;
    id_args_kinds := ak_xreg_q_xreg_q_shift;
    id_nargs := 5;
    id_str_jas := pp_s (otbn_op_to_string BN_MULQACC_Z);
    id_pp_asm := pp_otbn_op BN_MULQACC_Z;
    id_valid := true;
    id_safe := [::];
    id_eq_size := refl_equal;
    id_check_dest := refl_equal;
    id_safe_wf := refl_equal;
    id_semi_errty := fun _ => sem_lprod_ok_error _ _;
    id_semi_safe := fun _ => sem_lprod_ok_safe _ _;
  |}.

Definition semi_BN_MULQACC_WO :
  semi_type base_mulqacc_tin (ty_mlz ++ [:: lword256; lword256 ]) :=
  fun x ix y iy acc sham =>
    Let res := semi_BN_MULQACC x ix y iy acc sham in
    ok
      (:: MF_of_word res
        , LF_of_word res
        , ZF_of_word res
        , res
        & res
      ).

Definition desc_BN_MULQACC_WO : instr_desc_t :=
  {|
    id_msb_flag := MSB_MERGE;
    id_tin := base_mulqacc_tin;
    id_in := [:: EXa 1; Ea 2; EXa 3; Ea 4; Xreg ACC; Ea 5 ];
    id_tout := ty_mlz ++ [:: lword256; lword256 ];
    id_out := ad_mlz fg ++ [:: EXa 0; Xreg ACC ];
    id_semi := semi_BN_MULQACC_WO;
    id_nargs := 6;
    id_args_kinds := ak_xreg_xreg_q_xreg_q_shift;
    id_str_jas := pp_s (otbn_op_to_string (BN_MULQACC_WO fg));
    id_pp_asm := pp_otbn_op (BN_MULQACC_WO fg);
    id_valid := true;
    id_safe := [::];
    id_eq_size := ltac:(by case: fg);
    id_check_dest := ltac:(by case: fg);
    id_safe_wf := refl_equal;
    id_semi_errty := fun _ => sem_lprod_ok_error _ _;
    id_semi_safe := fun _ => sem_lprod_ok_safe _ _;
  |}.

Definition desc_BN_MULQACC_WO_Z : instr_desc_t :=
  {|
    id_msb_flag := MSB_MERGE;
    id_tin := base_mulqacc_z_tin;
    id_in := [:: EXa 1; Ea 2; EXa 3; Ea 4; Ea 5 ];
    id_tout := ty_mlz ++ [:: lword256; lword256 ];
    id_out := ad_mlz fg ++ [:: EXa 0; Xreg ACC ];
    id_semi := fun x ix y iy sham => semi_BN_MULQACC_WO x ix y iy 0%R sham;
    id_nargs := 6;
    id_args_kinds := ak_xreg_xreg_q_xreg_q_shift;
    id_str_jas := pp_s (otbn_op_to_string (BN_MULQACC_WO_Z fg));
    id_pp_asm := pp_otbn_op (BN_MULQACC_WO_Z fg);
    id_valid := true;
    id_safe := [::];
    id_eq_size := ltac:(by case: fg);
    id_check_dest := ltac:(by case: fg);
    id_safe_wf := refl_equal;
    id_semi_errty := fun _ => sem_lprod_ok_error _ _;
    id_semi_safe := fun _ => sem_lprod_ok_safe _ _;
  |}.

Let mulqacc_so_tin := ty_mlz ++ [:: lword256 ] ++ base_mulqacc_tin.
Let mulqacc_so_tout := ty_mlz ++ [:: lword256; lword256 ].

Definition wrd_hwsel : Z :=
  match wb with
  | WB_upper => 1
  | WB_lower => 0
  end.

Definition mlz_of_MULQACC_SO
  (mf lf zf : bool) (lo_part : u256) : bool * bool * bool :=
  if wb is WB_upper
  then (w2b (wand (wshr lo_part 127) 1), lf, zf && (lo_part == 0))%R
  else (mf, w2b (wand lo_part 1), lo_part == 0)%R.
Notation m_of_MULQACC_SO :=
  (fun mf lf zf lo_part => Some (mlz_of_MULQACC_SO mf lf zf lo_part).1.1).
Notation l_of_MULQACC_SO :=
  (fun mf lf zf lo_part => Some (mlz_of_MULQACC_SO mf lf zf lo_part).1.2).
Notation z_of_MULQACC_SO :=
  (fun mf lf zf lo_part => Some (mlz_of_MULQACC_SO mf lf zf lo_part).2).

Definition semi_BN_MULQACC_SO : semi_type mulqacc_so_tin mulqacc_so_tout :=
  fun mf lf zf r x ix y iy acc sham =>
    let base_res := mulqacc x ix y iy acc sham in
    let lo_part := extract_subword base_res 0 128 in
    let hi_part := extract_subword base_res 1 128 in
    let hw_shift := 128 * wrd_hwsel in
    let hw_mask := wrepr U256 (Z.shiftl (Z.shiftl 1 128 - 1) hw_shift) in
    let new_wrd := wor (wand r (wnot hw_mask)) (wshl lo_part hw_shift) in
    let mf' := m_of_MULQACC_SO mf lf zf lo_part in
    let lf' := l_of_MULQACC_SO mf lf zf lo_part in
    let zf' := z_of_MULQACC_SO mf lf zf lo_part in
    ok (:: mf', lf', zf', new_wrd & hi_part ).

(* TODO_OTBN Can we avoid taking the destination as an argument? *)
Definition desc_BN_MULQACC_SO : instr_desc_t :=
  {|
    id_msb_flag := MSB_MERGE;
    id_tin := mulqacc_so_tin;
    id_in :=
      ad_mlz fg ++ [:: EXa 0; EXa 1; Ea 2; EXa 3; Ea 4; Xreg ACC; Ea 5 ];
    id_tout := mulqacc_so_tout;
    id_out := ad_mlz fg ++ [:: EXa 0; Xreg ACC ];
    id_semi := semi_BN_MULQACC_SO;
    id_args_kinds := ak_xreg_xreg_q_xreg_q_shift;
    id_nargs := 6;
    id_str_jas := pp_s (otbn_op_to_string (BN_MULQACC_SO fg wb));
    id_pp_asm := pp_otbn_op (BN_MULQACC_SO fg wb);
    id_valid := true;
    id_safe := [::];
    id_eq_size := ltac:(by case: fg);
    id_check_dest := ltac:(by case: fg);
    id_safe_wf := refl_equal;
    id_semi_errty := fun _ => sem_lprod_ok_error _ _;
    id_semi_safe := fun _ => sem_lprod_ok_safe _ _;
  |}.

Definition desc_BN_MULQACC_SO_Z : instr_desc_t :=
  {|
    id_msb_flag := MSB_MERGE;
    id_tin := ty_mlz ++ [:: lword256 ] ++ base_mulqacc_z_tin;
    id_in := ad_mlz fg ++ [:: EXa 0; EXa 1; Ea 2; EXa 3; Ea 4; Ea 5 ];
    id_tout := mulqacc_so_tout;
    id_out := ad_mlz fg ++ [:: EXa 0; Xreg ACC ];
    id_semi :=
      fun mf lf zf r x ix y iy sham =>
        semi_BN_MULQACC_SO mf lf zf r x ix y iy 0%R sham;
    id_args_kinds := ak_xreg_xreg_q_xreg_q_shift;
    id_nargs := 6;
    id_str_jas := pp_s (otbn_op_to_string (BN_MULQACC_SO_Z fg wb));
    id_pp_asm := pp_otbn_op (BN_MULQACC_SO_Z fg wb);
    id_valid := true;
    id_safe := [::];
    id_eq_size := ltac:(by case: fg);
    id_check_dest := ltac:(by case: fg);
    id_safe_wf := refl_equal;
    id_semi_errty := fun _ => sem_lprod_ok_error _ _;
    id_semi_safe := fun _ => sem_lprod_ok_safe _ _;
  |}.

End MULQACC.

(* This is used to read and write [MOD] and [ACC].
   In both reads and writes, there is only one explicit argument (which is an
   input or an output, respectively). *)
Definition desc_BN_WSR op xr is_read : instr_desc_t :=
  let: (ad_in, ad_out) :=
    if is_read then (Xreg xr, EXa 0) else (EXa 0, Xreg xr)
  in
  {|
    id_msb_flag := MSB_MERGE;
    id_tin := [:: lword256 ];
    id_in := [:: ad_in ];
    id_tout := [:: lword256 ];
    id_out := [:: ad_out ];
    id_semi := fun x => ok x;
    id_nargs := 1;
    id_args_kinds := ak_xreg;
    id_str_jas := pp_s (otbn_op_to_string op);
    id_pp_asm := pp_otbn_op op;
    id_valid := true;
    id_safe := [::];
    id_eq_size := refl_equal;
    id_check_dest := check_dest_unop_lword;
    id_safe_wf := refl_equal;
    id_semi_errty := fun _ => sem_lprod_ok_error _ _;
    id_semi_safe := fun _ => sem_lprod_ok_safe _ _;
  |}.

Definition desc_BN_LID : instr_desc_t :=
  {|
    id_msb_flag := MSB_MERGE;
    id_tin := [:: lword32; lword256 ];
    id_in := [:: EXa 0; Ea 1 ];
    id_tout := [::];
    id_out := [::];
    id_semi := fun _ _ => Error E.no_semantics;
    id_args_kinds := ak_reg_mem;
    id_nargs := 2;
    id_str_jas := pp_s (otbn_op_to_string BN_LID);
    id_pp_asm := pp_otbn_op BN_LID;
    id_valid := false;
    id_safe := [::];
    id_eq_size := refl_equal;
    id_check_dest := refl_equal;
    id_safe_wf := refl_equal;
    id_semi_errty := ltac:(done);
    id_semi_safe := ltac:(done);
  |}.

Definition desc_BN_SID : instr_desc_t :=
  {|
    id_msb_flag := MSB_MERGE;
    id_tin := [:: lword32; lword256 ];
    id_in := [:: Ea 0; EXa 1 ];
    id_tout := [::];
    id_out := [::];
    id_semi := fun _ _ => Error E.no_semantics;
    id_args_kinds := ak_reg_xreg;
    id_nargs := 2;
    id_str_jas := pp_s (otbn_op_to_string BN_SID);
    id_pp_asm := pp_otbn_op BN_SID;
    id_valid := false;
    id_safe := [::];
    id_eq_size := refl_equal;
    id_check_dest := refl_equal;
    id_safe_wf := refl_equal;
    id_semi_errty := ltac:(done);
    id_semi_safe := ltac:(done);
  |}.

Definition desc_otbn_op (op : otbn_op) : instr_desc_t :=
  match op with
  | RV32 mn => desc_rv_mnemonic mn
  | BN_basic mn fg => desc_bn_basic_mnemonic mn fg
  | BN_basic_shift mn fg sh => desc_bn_basic_shift_mnemonic mn fg sh
  | BN_ADDI fg => desc_bn_binopI op fg wadd Z.add
  | BN_SUBI fg => desc_bn_binopI op fg wsub Z.sub
  | BN_MOV => desc_BN_MOV
  | BN_RSHI => desc_BN_RSHI
  | BN_SEL fg => desc_BN_SEL fg
  | BN_ADDM => desc_BN_ADDM
  | BN_SUBM => desc_BN_SUBM
  | BN_MULQACC => desc_BN_MULQACC
  | BN_MULQACC_Z => desc_BN_MULQACC_Z
  | BN_MULQACC_WO fg => desc_BN_MULQACC_WO fg
  | BN_MULQACC_WO_Z fg => desc_BN_MULQACC_WO_Z fg
  | BN_MULQACC_SO fg wb => desc_BN_MULQACC_SO fg wb
  | BN_MULQACC_SO_Z fg wb => desc_BN_MULQACC_SO_Z fg wb
  | BN_ACCR => desc_BN_WSR BN_ACCR ACC true
  | BN_ACCW => desc_BN_WSR BN_ACCW ACC false
  | BN_MODR => desc_BN_WSR BN_MODR MOD true
  | BN_MODW => desc_BN_WSR BN_MODW MOD false
  | BN_LID => desc_BN_LID
  | BN_SID => desc_BN_SID
  end.

Section PRIM_STRING.

  Let map_prim_string
    {A : Type}
    (to_string : A -> string)
    (to_prim : (A -> prim_constructor otbn_op))
    (s : seq A)
    : seq (string * prim_constructor otbn_op) :=
    map (fun a => (to_string a, to_prim a)) s.

  Let prim_RV32 mn := prim_otbn_none (RV32 mn).
  Let prim_BN_basic mn := prim_otbn_fg (BN_basic mn).

  (* [LA] computes an address relative to the PC. *)
  Let rv_prim_string :=
    let: no_la := filter (fun mn => mn != LA) cenum in
    map_prim_string rv_mnemonic_to_string prim_RV32 no_la.

  (* This also covers the versions with shift. *)
  Let bn_basic_prim_string :=
    map_prim_string bn_basic_mnemonic_to_string prim_BN_basic cenum.

  (* To print these mnemonics with [otbn_op_to_string] we need a flag group,
     but it does not affect the string. *)
  Let bn_fg_prim_string :=
    map_prim_string
      (fun mn => otbn_op_to_string (mn FG0))
      prim_otbn_fg
      [:: BN_ADDI; BN_SUBI; BN_SEL ].

  Let bn_no_opt_prim_string :=
    map_prim_string
      otbn_op_to_string
      prim_otbn_none
      [:: BN_MOV; BN_RSHI; BN_ADDM; BN_SUBM; BN_ACCR; BN_ACCW; BN_MODR; BN_MODW
      ].

  (* MULQACC intrinsic string does not change with flag group or writeback. *)
  Let bn_mulqacc_prim_string :=
      let fg := FG0 in
      let wb := WB_upper in
      let str := otbn_op_to_string BN_MULQACC in
      let str_z := otbn_op_to_string BN_MULQACC_Z in
      let str_wo := otbn_op_to_string (BN_MULQACC_WO fg) in
      let str_wo_z := otbn_op_to_string (BN_MULQACC_WO_Z fg) in
      let str_so := otbn_op_to_string (BN_MULQACC_SO fg wb) in
      let str_so_z := otbn_op_to_string (BN_MULQACC_SO_Z fg wb) in
      [:: (str, prim_otbn_none BN_MULQACC)
        ; (str_z, prim_otbn_none BN_MULQACC_Z)
        ; (str_wo, prim_otbn_fg BN_MULQACC_WO)
        ; (str_wo_z, prim_otbn_fg BN_MULQACC_WO_Z)
        ; (str_so, prim_otbn_mulqacc_so BN_MULQACC_SO)
        ; (str_so_z, prim_otbn_mulqacc_so BN_MULQACC_SO_Z)
      ].

  Definition otbn_prim_string : seq (string * prim_constructor otbn_op) :=
    Eval vm_compute in
    map
      (fun '(s, p) => (replace_dot s, p))
      (rv_prim_string
       ++ bn_basic_prim_string
       ++ bn_fg_prim_string
       ++ bn_no_opt_prim_string
       ++ bn_mulqacc_prim_string).

End PRIM_STRING.

#[export]
Instance otbn_op_decl : asm_op_decl otbn_op :=
  {|
    instr_desc_op := desc_otbn_op;
    prim_string := otbn_prim_string;
  |}.

Definition otbn_prog := asm_prog (asm_op_d := otbn_op_decl).

(* Sanity check for prim_string. *)
Section VALIDATION.
  Import strings.

  Let strings := Eval compute in map fst otbn_prim_string.

  Goal uniq strings. done. Qed.

  Let hidden := [:: "LA"; "BN_LID"; "BN_SID" ]%string.

  Goal
    forall op,
      let: s := replace_dot (otbn_op_to_string op) in
      xorb (s \in hidden) (s \in strings).
  by move=> [] // [] //. Qed.

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

End VALIDATION.

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

End VALIDATION_SEM.
