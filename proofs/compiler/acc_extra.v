From elpi.apps Require Import derive.std.
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssralg.

Require Import
  compiler_util
  expr
  fexpr
  acc_options
  sopn
  utils.
Require Import
  arch_decl
  arch_utils
  arch_extra.
Require Import
  acc
  acc_decl
  acc_instr_decl
  acc_params_core
.
Require arm_extra.

Module E.

  Import compiler_util.

  Definition pass_name : string := "assembly generation".

  Definition internal_error (msg : string) (ii : instr_info) : pp_error_loc :=
    (pp_internal_error_s_at pass_name ii msg).

  Definition internal_error_pp (pp : pp_error) (ii : instr_info) : pp_error_loc :=
    pp_at_ii ii (pp_internal_error pass_name pp).

  Definition invalid_rexprs := internal_error "invalid arguments".
  Definition invalid_args := internal_error "invalid destination or arguments".

  (* [assemble_swap] errors. *)
  Definition bad_swap_lexprs := internal_error "bad swap: invalid destinations".
  Definition bad_swap_rexprs := internal_error "bad swap: invalid sources".
  Definition bad_swap_size (ws : wsize) (ii : instr_info) : pp_error_loc :=
    internal_error_pp
      (pp_box
         [:: pp_s "bad swap: expected size"
          ; pp_s (string_of_wsize reg_size)
          ; pp_s "or"
          ; pp_s (string_of_wsize xreg_size)
          ; pp_s "but got"
          ; pp_s (string_of_wsize ws) ])
      ii.
  Definition bad_swap_dst_arg :=
    internal_error
      "bad swap arguments: first destination should be different from last argument".
  Definition bad_swap_dsts :=
    internal_error "bad swap arguments: destination registers should be different".
  Definition bad_swap_ty :=
    internal_error "bad swap: operands must be a register or a wide register".

End E.

Definition asm_args_of_opn_args
  : seq ACCFopn_core.opn_args -> seq (asm_op_msb_t * lexprs * rexprs) :=
  map (fun '(les, aop, res) => ((None, aop), les, res)).

Section WITH_PARAMS.

Import sopn.

Context {atoI : arch_toIdent}.

Let acc_mod : seq var := map to_var acc_mod.
Let E n := ADExplicit n (sopn.ACR_subset acc_mod).
Let F (f : rflag) := ADImplicit (to_var f).

#[only(eqbOK)] derive
Variant extra_op :=
| set0 of wsize
| MOV  (* [ADDI x, y, 0]. *)
| NOT  (* [XORI x, y, -1]. *)
| SUBI (* [ADDI x, y, -imm]. *)
| ADD_LARGE_IMM (* [LI x, imm; ADD x, x, y]. *)
| SWAP of wsize (* Three [XOR]s. *)
| BN_SELECT_MASKED (* [BN_SEL] with its three arguments in different
                      registers *)
| ZEROIZE_MASKED of wsize (* [set0] forcing first argument to be allocated to
                             output register *)
.

HB.instance Definition _ := hasDecEq.Build extra_op extra_op_eqb_OK.

#[export]
Instance eqTC_acc_extra_op : eqTypeC extra_op := { ceqP := extra_op_eqb_OK }.

Definition string_of_extra_op (eo : extra_op) : string :=
  match eo with
  | set0 _ => "set0"
  | MOV => "MOV"
  | NOT => "NOT"
  | SUBI => "SUBI"
  | ADD_LARGE_IMM => "add_large_imm"
  | SWAP _ => "swap"
  | BN_SELECT_MASKED => "BN_SELECT_MASKED"
  | ZEROIZE_MASKED _ => "ZEROIZE_MASKED"
  end.

Definition desc_set0_small : instruction_desc :=
  mk_instr_desc_safe
    (pp_s (string_of_extra_op (set0 U8)))
    [::] [::]
    [:: aword U32 ] [:: E 0 ]
    0%R
    true DOIT.

Definition desc_set0_large : instruction_desc :=
  let vf := Some false in
  let vt := Some true in
  mk_instr_desc_safe
    (pp_s (string_of_extra_op (set0 U8)))
    [::] [::]
    [:: abool; abool; abool; aword U256 ] ([:: F MF0; F LF0; F ZF0; E 0 ])
    (:: vf, vf, vt & 0%R)
    true DOIT.

Definition desc_MOV : instruction_desc :=
  mk_instr_desc_safe
    (pp_s (string_of_extra_op MOV))
    [:: aword U32 ] [:: E 1 ]
    [:: aword U32 ] [:: E 0 ]
    id
    true DOIT.

Definition desc_NOT : instruction_desc :=
  mk_instr_desc_safe
    (pp_s (string_of_extra_op NOT))
    [:: aword U32 ] [:: E 1 ]
    [:: aword U32 ] [:: E 0 ]
    wnot
    true DOIT.

Definition desc_SUBI : instruction_desc :=
  mk_instr_desc_safe
    (pp_s (string_of_extra_op SUBI))
    [:: aword U32; aword U32 ] [:: E 1; E 2 ]
    [:: aword U32 ] [:: E 0 ]
    (fun x y => x - y)%R
    true DOIT.

(* [conflicts] ensures that the destination register is distinct from the
   first argument: the expansion [LI x, imm; ADD x, x, y] uses the
   destination as a temporary. *)
Definition desc_ADD_LARGE_IMM : instruction_desc :=
  let ty := aword U32 in
  let cty := eval_atype ty in
  let ctin := [:: cty; cty ] in
  let semi := fun (x y : word U32) => (x + y)%R in
  {| str := pp_s (string_of_extra_op ADD_LARGE_IMM)
   ; tin := [:: ty; ty ]
   ; i_in := [:: E 1; E 2 ]
   ; tout := [:: ty ]
   ; i_out := [:: E 0 ]
   ; conflicts := [:: (APout 0, APin 0) ]
   ; semi := sem_prod_ok ctin semi
   ; semu := @values.vuincl_app_sopn_v ctin [:: cty ] (sem_prod_ok ctin semi) refl_equal
   ; i_safe := [::]
   ; i_valid := true
   ; i_doit := DOIT
   ; i_safe_wf := refl_equal
   ; i_semi_errty := fun _ => sem_prod_ok_error (tin := ctin) semi _
   ; i_semi_safe := fun _ => values.sem_prod_ok_safe (tin := ctin) semi
   |}.

Definition desc_swap_large : instruction_desc :=
  mk_instr_desc_safe
    (pp_s (string_of_extra_op (SWAP U256)))
    [:: aword U256; aword U256 ] [:: E 0; E 1 ]
    [:: abool; abool; abool; aword U256; aword U256 ]
    [:: F MF1; F LF1; F ZF1; E 0; E 1 ]
    (fun z w => (:: MF_of_word w, LF_of_word w, ZF_of_word w, w & z))
    true DOIT.

Definition desc_BN_SELECT_MASKED : instruction_desc :=
  let ty := aword U256 in
  let cty := eval_atype ty in
  let ctin := [:: cty; cty; cbool ] in
  let semi := fun (wn wm : word U256) (b : bool) => if b then wn else wm in
  {|
    str := pp_s (string_of_extra_op BN_SELECT_MASKED);
    tin := [:: ty; ty; abool ];
    i_in := [:: E 1; E 2; E 3 ];
    tout := [:: ty ];
    i_out := [:: E 0 ];
    conflicts := [:: (APout 0, APin 0); (APout 0, APin 1); (APin 0, APin 1) ];
    semi := sem_prod_ok ctin semi;
    semu := @values.vuincl_app_sopn_v ctin [:: cty ] (sem_prod_ok ctin semi) refl_equal;
    i_safe := [::];
    i_valid := true;
    i_doit := DOIT;
    i_safe_wf := refl_equal;
    i_semi_errty := fun _ => sem_prod_ok_error (tin := ctin) semi _;
    i_semi_safe := fun _ => values.sem_prod_ok_safe (tin := ctin) semi;
  |}.

(* [conflicts] forces the two inputs into different registers:
   [assemble_zeroize_masked] requires the destination to alias the first
   input, while the second input is XOR-ed with itself to produce the zero
   value; letting the allocator merge the two inputs would corrupt that
   XOR. *)
Definition desc_zeroize_masked_small : instruction_desc :=
  let ty := aword U32 in
  let cty := eval_atype ty in
  let ctin := [:: cty; cty ] in
  let semi := fun (_ _ : word U32) => 0%R in
  {| str := pp_s (string_of_extra_op (ZEROIZE_MASKED U8))
   ; tin := [:: ty; ty ]
   ; i_in := [:: E 0; E 1 ]
   ; tout := [:: ty ]
   ; i_out := [:: E 0 ]
   ; conflicts := [:: (APin 0, APin 1) ]
   ; semi := sem_prod_ok ctin semi
   ; semu := @values.vuincl_app_sopn_v ctin [:: cty ] (sem_prod_ok ctin semi) refl_equal
   ; i_safe := [::]
   ; i_valid := true
   ; i_doit := DOIT
   ; i_safe_wf := refl_equal
   ; i_semi_errty := fun _ => sem_prod_ok_error (tin := ctin) semi _
   ; i_semi_safe := fun _ => values.sem_prod_ok_safe (tin := ctin) semi
   |}.

Definition desc_zeroize_masked_large : instruction_desc :=
  let vf := Some false in
  let vt := Some true in
  let ty := aword U256 in
  let cty := eval_atype ty in
  let ctin := [:: cty; cty ] in
  let semi := fun (_ _ : word U256) => (:: vf, vf, vt & 0%R) in
  {| str := pp_s (string_of_extra_op (ZEROIZE_MASKED U8))
   ; tin := [:: ty; ty ]
   ; i_in := [:: E 0; E 1 ]
   ; tout := [:: abool; abool; abool; ty ]
   ; i_out := [:: F MF0; F LF0; F ZF0; E 0 ]
   ; conflicts := [:: (APin 0, APin 1) ]
   ; semi := sem_prod_ok ctin semi
   ; semu :=
       @values.vuincl_app_sopn_v ctin [:: cbool; cbool; cbool; cty ]
         (sem_prod_ok ctin semi) refl_equal
   ; i_safe := [::]
   ; i_valid := true
   ; i_doit := DOIT
   ; i_safe_wf := refl_equal
   ; i_semi_errty := fun _ => sem_prod_ok_error (tin := ctin) semi _
   ; i_semi_safe := fun _ => values.sem_prod_ok_safe (tin := ctin) semi
   |}.

Definition get_instr_desc (eo : extra_op) : instruction_desc :=
  match eo with
  | set0 ws => if (ws <= reg_size)%CMP then desc_set0_small else desc_set0_large
  | MOV => desc_MOV
  | NOT => desc_NOT
  | SUBI => desc_SUBI
  | ADD_LARGE_IMM => desc_ADD_LARGE_IMM
  | SWAP ws => if (ws <= reg_size)%CMP then Oswap_instr (aword ws) else desc_swap_large
  | BN_SELECT_MASKED => desc_BN_SELECT_MASKED
  | ZEROIZE_MASKED ws =>
      if (ws <= reg_size)%CMP then desc_zeroize_masked_small
      else desc_zeroize_masked_large
  end.

Definition prim_string : seq (string * prim_constructor extra_op) :=
  [:: (string_of_extra_op (set0 U8), prim_acc_ws set0)
    ; (string_of_extra_op MOV, prim_acc_none MOV)
    ; (string_of_extra_op NOT, prim_acc_none NOT)
    ; (string_of_extra_op SUBI, prim_acc_none SUBI)
    ; (string_of_extra_op BN_SELECT_MASKED, prim_acc_none BN_SELECT_MASKED)
    ; (string_of_extra_op (ZEROIZE_MASKED U8), prim_acc_ws ZEROIZE_MASKED)
  ].

#[global]
Instance extra_op_decl : asmOp extra_op | 1 :=
  {
    asm_op_instr := get_instr_desc;
    prim_string := prim_string;
  }.


(* -------------------------------------------------------------------------- *)
(* Assembly of extra operations. *)

Section ASSEMBLE.

Context (ii : instr_info).

(* Zero [les] by XOR-ing register [v] with itself. Shared by [assemble_set0]
   (where [v] is the destination itself) and [assemble_zeroize_masked]
   (where [v] is the op's second argument). *)
Definition assemble_self_xor
  (ws : wsize)
  (les : seq lexpr)
  (v : var_i) :
  cexec (seq (asm_op_msb_t * seq lexpr * seq rexpr)) :=
  let op := if (ws <= reg_size)%CMP then RV32 XOR else BN_basic BN_XOR FG0 in
  let x := rvar v in
  ok [:: ((None, op), les, [:: x; x ]) ].

Let uncons_LLvar := arm_extra.uncons_LLvar ii.
Let uncons_rvar := arm_extra.uncons_rvar ii.
Let uncons_wconst := arm_extra.uncons_wconst ii.

Definition assemble_set0
  (ws : wsize)
  (les : seq lexpr)
  (res : seq rexpr) :
  cexec (seq (asm_op_msb_t * seq lexpr * seq rexpr)) :=
  Let x :=
    if les is [:: _; _; _; LLvar x] then ok x
    else Let: (x, _) := uncons_LLvar les in ok x
  in
  assemble_self_xor ws les x.

(* [MOV x x] is removed by dead code elimination already with [is_move_op], and
   we need to produce at least one instruction for the proof, so we should not
   use [smart_mov]. *)
Definition assemble_MOV
  (les : seq lexpr)
  (res : seq rexpr) :
  cexec (seq (asm_op_msb_t * seq lexpr * seq rexpr)) :=
  Let: (x, _) := uncons_LLvar les in
  Let: (y, _) := uncons_rvar res in
  Let _ := assert (convertible x.(vtype) (aword U32))
                  (E.internal_error "mov: bad register type" ii) in
  ok (asm_args_of_opn_args [:: ACCFopn_core.mov x y ]).

Definition assemble_NOT
  (les : seq lexpr)
  (res : seq rexpr) :
  cexec (seq (asm_op_msb_t * seq lexpr * seq rexpr)) :=
  Let: (x, _) := uncons_LLvar les in
  Let: (y, _) := uncons_rvar res in
  Let _ := assert (convertible x.(vtype) (aword U32))
                  (E.internal_error "not: bad register type" ii) in
  ok (asm_args_of_opn_args [:: ACCFopn_core.not x y ]).

Definition assemble_SUBI
  (les : seq lexpr)
  (res : seq rexpr) :
  cexec (seq (asm_op_msb_t * seq lexpr * seq rexpr)) :=
  Let: (x, _) := uncons_LLvar les in
  Let: (y, res) := uncons_rvar res in
  Let: (imm, _) := uncons_wconst res in
  Let _ := assert (convertible x.(vtype) (aword U32))
                  (E.internal_error "subi: bad register type" ii) in
  Let _ := assert (negb ((imm =? 0)%Z && (v_var x == v_var y)))
                  (E.internal_error "subi: trivial no-op" ii) in
  Let args := o2r (E.invalid_args ii) (ACCFopn_core.smart_subi x y imm) in
  ok (asm_args_of_opn_args args).

(* [x = y + imm] with an immediate too large for [ADDI]: expand to
   [LI x, imm; ADD x, x, y] via [smart_addi]. The [conflicts] field of
   [desc_ADD_LARGE_IMM] makes register allocation keep [x <> y], which
   [smart_addi] requires when [imm] is large. *)
Definition assemble_ADD_LARGE_IMM
  (les : seq lexpr)
  (res : seq rexpr) :
  cexec (seq (asm_op_msb_t * seq lexpr * seq rexpr)) :=
  Let: (x, _) := uncons_LLvar les in
  Let: (y, res) := uncons_rvar res in
  Let: (imm, _) := uncons_wconst res in
  Let _ := assert (v_var x != v_var y)
                  (E.internal_error "add_large_imm: invalid register" ii) in
  Let _ := assert (convertible x.(vtype) (aword U32))
                  (E.internal_error "add_large_imm: bad register type" ii) in
  Let args := o2r (E.invalid_args ii) (ACCFopn_core.smart_addi x y imm) in
  ok (asm_args_of_opn_args args).

(* [x, y = swap(z, w)] using the standard three-[XOR] sequence:
   - [x = z ^ w];
   - [y = x ^ w = z];
   - [x = x ^ y = w].
   A 32-bit swap uses [RV32 XOR] with no flag dests ([fl] empty). A wide swap
   uses [BN_XOR]; its M/L/Z flag dests [fl] are the swap op's implicit FG1
   outputs, already materialized by register allocation (discarded -- they were
   [Lnone] in the lowering). *)
Definition assemble_swap
  (ws : wsize)
  (les : seq lexpr)
  (res : seq rexpr) :
  cexec (seq (asm_op_msb_t * seq lexpr * seq rexpr)) :=
  Let: (z, w) :=
    if res is [:: Rexpr (Fvar z); Rexpr (Fvar w) ] then ok (z, w)
    else Error (E.bad_swap_rexprs ii)
  in
  Let: (op, fl, x, y) :=
    if (ws == reg_size)%CMP then
      if les is [:: LLvar x; LLvar y ] then ok (RV32 XOR, [::], x, y)
      else Error (E.bad_swap_lexprs ii)
    else if (ws == xreg_size)%CMP then
      if les is [:: fM; fL; fZ; LLvar x; LLvar y ] then
        ok (BN_basic BN_XOR FG1, [:: fM; fL; fZ ], x, y)
      else Error (E.bad_swap_lexprs ii)
    else Error (E.bad_swap_size ws ii)
  in
  Let _ := assert (v_var x != v_var w) (E.bad_swap_dst_arg ii) in
  Let _ := assert (v_var y != v_var x) (E.bad_swap_dsts ii) in
  Let _ :=
    assert
      (all (fun v => convertible v.(v_var).(vtype) (aword ws)) [:: x; y; z; w ])
      (E.bad_swap_ty ii)
  in
  let xor (d a b : var_i) :=
    ((None, op), fl ++ [:: LLvar d ], [:: Rexpr (Fvar a); Rexpr (Fvar b) ])
  in
  ok [:: xor x z w; xor y x w; xor x x y ].

Definition assemble_bn_select_masked
  (les : seq lexpr)
  (res : seq rexpr) :
  cexec (seq (asm_op_msb_t * seq lexpr * seq rexpr)) :=
  Let: (x, _) := uncons_LLvar les in
  Let: (wn, res1) := uncons_rvar res in
  Let: (wm, _) := uncons_rvar res1 in
  Let _ :=
    assert
      (uniq [:: v_var x; v_var wn; v_var wm ])
      (E.internal_error
         "bn_select_masked: destination and arguments must be pairwise distinct"
         ii)
  in
  ok [:: ((None, BN_SEL FG0), les, res) ].

Definition assemble_zeroize_masked
  (ws : wsize)
  (les : seq lexpr)
  (res : seq rexpr) :
  cexec (seq (asm_op_msb_t * seq lexpr * seq rexpr)) :=
  Let: (y1, res) := uncons_rvar res in
  Let: (y2, _) := uncons_rvar res in
  Let x :=
    if les is [:: _; _; _; LLvar x] then ok x
    else Let: (x, _) := uncons_LLvar les in ok x
  in
  Let _ :=
    assert
      (all (fun v => convertible v.(v_var).(vtype) (aword ws)) [:: x; y1; y2])
      (E.internal_error "zeroize_masked: bad register type" ii)
  in
  Let _ :=
    assert (v_var x == v_var y1)
      (E.internal_error
         "zeroize_masked: destination must alias first argument" ii)
  in
  Let _ :=
    assert (v_var y1 != v_var y2)
      (E.internal_error
         "zeroize_masked: arguments must be different registers" ii)
  in
  assemble_self_xor ws les y2.

Definition assemble_extra
  (eo : extra_op)
  (les : seq lexpr)
  (res : seq rexpr) :
  cexec (seq (asm_op_msb_t * seq lexpr * seq rexpr)) :=
  match eo with
  | set0 ws => assemble_set0 ws les res
  | MOV => assemble_MOV les res
  | NOT => assemble_NOT les res
  | SUBI => assemble_SUBI les res
  | ADD_LARGE_IMM => assemble_ADD_LARGE_IMM les res
  | SWAP ws => assemble_swap ws les res
  | BN_SELECT_MASKED => assemble_bn_select_masked les res
  | ZEROIZE_MASKED ws => assemble_zeroize_masked ws les res
  end.

End ASSEMBLE.

#[export]
Instance acc_extra :
  asm_extra register empty wide_register rflag condition acc_op extra_op :=
  { to_asm := assemble_extra; }.

(* This concise name is convenient in OCaml code. *)
Definition acc_extended_op : Type := extended_op (asm_e := acc_extra).

Definition Oacc (o : acc_op) : sopn := Oasm (BaseOp (None, o)).

End WITH_PARAMS.
