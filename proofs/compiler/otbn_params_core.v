From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.
From mathcomp Require Import word_ssrZ.

Require Import
  compiler_util
  expr
  fexpr
  linear
  utils.
Require Import
  arch_decl.
Require Import
  otbn_decl
  otbn_instr_decl.

(* TODO_OTBN maybe all of these should also be extra ops, or make all the
   options check and default to normal operation *)

(* Whether [imm] is fits in 12 bits (signed). *)
Definition is_arith_small (imm : Z) : bool :=
  [&& - Z.pow 2 11 <=? imm & imm <? Z.pow 2 11 ]%Z.

Definition is_arith_small_neg (imm : Z) : bool := is_arith_small (- imm).

Module OTBNFopn_core.

  (* TODO_OTBN double check preconditions, some do not apply if we fail
     explicitly *)
  #[local] Open Scope Z.

  Section CORE.

  Definition opn_args := (seq lexpr * otbn_op * seq rexpr)%type.

  Definition op_gen mn x res : opn_args := ([:: LLvar x ], RV32 mn, res).
  Definition op_un_reg mn x y : opn_args := op_gen mn x [:: rvar y ].
  Definition op_un_imm mn x imm : opn_args := op_gen mn x [:: rconst reg_size imm ].
  Definition op_bin_reg mn x y z : opn_args := op_gen mn x [:: rvar y; rvar z ].
  Definition op_bin_imm mn x y imm : opn_args :=
    op_gen mn x [:: rvar y; rconst reg_size imm ].
  (* Shift amounts are encoded as 8-bit immediates (5 significant bits). *)
  Definition op_bin_shamt mn x y imm : opn_args :=
    op_gen mn x [:: rvar y; rconst U8 imm ].

  Definition add := op_bin_reg ADD.
  Definition sub := op_bin_reg SUB.

  Definition li := op_un_imm LI.
  Definition addi := op_bin_imm ADDI.
  Definition subi x y imm : opn_args := addi x y (- imm).
  Definition slli := op_bin_shamt SLLI.
  Definition srli := op_bin_shamt SRLI.
  Definition andi := op_bin_imm ANDI.
  Definition xori := op_bin_imm XORI.

  Definition mov x y: opn_args := addi x y 0.
  Definition smart_mov x y : seq opn_args :=
    if v_var x == v_var y then [::] else [:: mov x y ].

  (* [R[x] := ~ R[y]], implemented as [XORI x, y, -1]. The immediate [-1] is
     always in range, so unlike [smart_addi]/[smart_subi] no fallback via a
     temporary register is ever needed. *)
  Definition not x y : opn_args := xori x y (-1).

  Definition lw ws x e : opn_args :=
    ([:: LLvar x ], RV32 LW, [::  Load Aligned ws e ]).

  Definition sw ws e y : opn_args :=
    ([:: Store Aligned ws e ], RV32 SW, [:: rvar y ]).

  Definition align x y al : opn_args := andi x y (- (wsize_size al)).

  Definition is_mov neutral imm := if neutral is Some n then (imm =? n)%Z else false.

  (* Compute [R[x] := R[y] <o> imm % 2^32].
     Precondition: if [imm] is large and not neutral, [y <> tmp]. *)
  Definition gen_unsafe_smart_opi
    (on_reg : var_i -> var_i -> var_i -> opn_args)
    (on_imm : var_i -> var_i -> Z -> opn_args)
    (is_small : Z -> bool)
    (neutral : option Z)
    (tmp x y : var_i)
    (imm : Z) :
    seq opn_args :=
    if is_mov neutral imm then smart_mov x y
    else if is_small imm then [:: on_imm x y imm ]
    else [:: li tmp imm; on_reg x y tmp].

  (* Compute [R[x] := R[y] <o> imm % 2^32].
     Fail when [imm] is large and [y = tmp] (we compare only [v_var]). *)
  Definition gen_smart_opi
    (on_reg : var_i -> var_i -> var_i -> opn_args)
    (on_imm : var_i -> var_i -> Z -> opn_args)
    (is_small : Z -> bool)
    (neutral : option Z)
    (tmp x y : var_i)
    (imm : Z) :
    option (seq opn_args) :=
    if [|| is_mov neutral imm, is_small imm | v_var y != v_var tmp ] then
      Some (gen_unsafe_smart_opi on_reg on_imm is_small neutral tmp x y imm)
    else None.

  (* Compute [R[x] := R[y] + imm % 2^32
     Precondition: if [imm] is large, [x <> y]. *)
  Definition smart_addi x y :=
    gen_smart_opi add addi is_arith_small (Some 0%Z) x x y.

  (* Compute [R[x] := R[y] - imm % 2^32
     Precondition: if [imm] is large, [x <> y]. *)
  Definition smart_subi x y imm :=
    gen_smart_opi sub subi is_arith_small_neg (Some 0%Z) x x y imm.

  (* Compute [R[x] := R[x] <o> imm % 2^32].
     Precondition: if [imm] is large, [x <> tmp]. *)
  Definition gen_smart_opi_tmp is_arith_small on_reg on_imm x tmp imm :=
    gen_smart_opi on_reg on_imm is_arith_small (Some 0%Z) tmp x x imm.

  (* Compute [R[x] := R[x] + imm % 2^32].
     Precondition: if [imm] is large, [x <> tmp]. *)
  Definition smart_addi_tmp x tmp imm :=
    gen_smart_opi_tmp is_arith_small add addi x tmp imm.

  (* Compute [R[x] := R[x] - imm % 2^32].
     Precondition: if [imm] is large, [x <> tmp]. *)
  Definition smart_subi_tmp x tmp imm :=
    gen_smart_opi_tmp is_arith_small_neg sub subi x tmp imm.

  Definition smart_slli x y imm :=
    if imm =? 0%Z then Some (smart_mov x y)
    else if [&& 0 <=? imm & imm <? 32 ]%Z then Some [:: slli x y imm ]
    else None.

  Definition smart_srli x y imm :=
    if imm =? 0%Z then Some (smart_mov x y)
    else if [&& 0 <=? imm & imm <? 32 ]%Z then Some [:: srli x y imm ]
    else None.

  End CORE.

End OTBNFopn_core.
