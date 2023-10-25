From mathcomp Require Import
  all_ssreflect
  all_algebra.

Require Import
  compiler_util
  expr
  fexpr
  otbn_options
  sopn
  utils.
Require Import
  arch_decl
  arch_utils
  arch_extra.
Require Import
  otbn
  otbn_decl
  otbn_instr_decl.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Module E.

  Definition pass_name : string := "assembly generation".

  Definition internal_error (msg : string) (ii : instr_info) : pp_error_loc :=
    (pp_internal_error_s_at pass_name ii msg).

  Definition set0_invalid_lexprs :=
    internal_error "invalid destination for set0".

End E.

Section WITH_PARAMS.

Import sopn.

#[local]
Notation E n := (ADExplicit n None) (only parsing).

Context {atoI : arch_toIdent}.

Variant extra_op :=
  | set0
.

Scheme Equality for extra_op.

Lemma extra_op_eq_axiom : Equality.axiom extra_op_beq.
Proof.
  exact: (eq_axiom_of_scheme internal_extra_op_dec_bl internal_extra_op_dec_lb).
Qed.

#[export]
Instance eqTC_extra_op : eqTypeC extra_op :=
  {
    ceqP := extra_op_eq_axiom;
  }.

Canonical extra_op_eqType := @ceqT_eqType _ eqTC_extra_op.

Definition string_of_extra_op (eo : extra_op) : string :=
  match eo with
  | set0 => "set0"
  end.

Definition desc_set0 : instruction_desc :=
  let ty_mlz := behead ty_cmlz in
  let ak_mlz := map sopn_arg_desc (behead (ad_cmlz FG0)) in
  let vf := Some false in
  let vt := Some true in
  mk_instr_desc
    (pp_s (string_of_extra_op set0))
    [::] [::]
    (ty_mlz ++ [:: sxreg ]) (ak_mlz ++ [:: E 0 ])
    (ok (:: vf, vf, vt & 0%R))
    [::].

Definition get_instr_desc (eo : extra_op) : instruction_desc :=
  match eo with
  | set0 => desc_set0
  end.

Definition prim_string : seq (string * prim_constructor extra_op) :=
  [:: (string_of_extra_op set0, PrimOTBN_none set0) ].

#[global]
Instance extra_op_decl : asmOp extra_op | 1 :=
  {
    asm_op_instr := get_instr_desc;
    prim_string := prim_string;
  }.


(* -------------------------------------------------------------------------- *)
(* Assembly of extra operations. *)

Definition get_last_var (err : pp_error_loc) (les : seq lexpr) : cexec var_i :=
  match rev les with
  | LLvar x :: _ =>  ok x
  | _ => Error err
  end.

Definition assemble_extra
  (ii : instr_info)
  (eo : extra_op)
  (les : seq lexpr)
  (res : seq rexpr) :
  cexec (seq (asm_op_msb_t * seq lexpr * seq rexpr)) :=
  match eo with
  | set0 =>
      Let x := get_last_var (E.set0_invalid_lexprs ii) les in
      let x := Rexpr (Fvar x) in
      let k0 := Rexpr (fconst reg_size 0) in
      ok [:: ((None, BN_basic BN_XOR FG0), les, [:: x; x ]) ]
  end.

#[export]
Instance otbn_extra :
  asm_extra
    register
    register_ext
    wide_register
    flag
    condition
    otbn_op
    extra_op
  :=
  {
    to_asm := assemble_extra;
  }.

(* This concise name is convenient in OCaml code. *)
Definition otbn_extended_op : Type := extended_op (asm_e := otbn_extra).

Definition Ootbn (o : otbn_op) : sopn := Oasm (BaseOp (None, o)).

End WITH_PARAMS.

(* -------------------------------------------------------------------------- *)
Module Type OPN_ARGS.
  Parameter lval rval : Type.
  Parameter lvar : var_i -> lval.
  Parameter lmem : wsize -> var_i -> Z -> lval.
  Parameter rvar : var_i -> rval.
  Parameter rconst : wsize -> Z -> rval.
End OPN_ARGS.

Module OPN (A : OPN_ARGS).

  Import A.

  #[local]
  Open Scope Z.

  Section WITH_PARAMS.

  Context {atoI : arch_toIdent}.

  Notation opn_args := (seq lval * sopn * seq rval)%type.
  Let op_gen mn x res : opn_args := ([:: lvar x ], Ootbn (RV32 mn), res).
  Let op_un_reg mn x y := op_gen mn x [:: rvar y ].
  Let op_un_imm mn x imm := op_gen mn x [:: rconst reg_size imm ].
  Let op_bin_reg mn x y z := op_gen mn x [:: rvar y; rvar z ].
  Let op_bin_imm mn x y imm := op_gen mn x [:: rvar y; rconst reg_size imm ].

  Definition mov := op_un_reg MOV.
  Definition add := op_bin_reg ADD.
  Definition sub := op_bin_reg SUB.

  Definition li := op_un_imm LI.
  Definition addi := op_bin_imm ADDI.
  Definition subi x y imm := addi x y (- imm).
  Definition slli := op_bin_imm SLLI.
  Definition srli := op_bin_imm SRLI.

  Definition sw ws x off y :=
    ([:: lmem ws x off ], Ootbn (RV32 SW), [:: rvar y ]).

  Definition smart_mov (x y : var_i) : seq opn_args :=
    if v_var x == v_var y then [::] else [:: mov x y ].

  Let imm_is_mov neutral imm :=
    if neutral is Some n then (imm =? n)%Z else false.

  (* Precondition: if [imm] is not small, [y <> tmp] and either [x <> y] or
     [x <> tmp]. *)
  Let gen_smart_opi
    (on_reg : var_i -> var_i -> var_i -> opn_args)
    (on_imm : var_i -> var_i -> Z -> opn_args)
    (is_small : Z -> bool)
    (neutral : option Z)
    (x y tmp : var_i)
    (imm : Z) :
    seq opn_args :=
    if imm_is_mov neutral imm
    then smart_mov x y
    else
      if is_small imm
      then [:: on_imm x y imm ]
      else li tmp imm :: [:: on_reg x y tmp ].

  Definition smart_addi := gen_smart_opi add addi is_w12 (Some 0).
  Definition smart_subi := gen_smart_opi sub subi is_w12 (Some 0).

  (* Precondition: [0 <= imm < 32]. This means [on_reg] is ignored and [tmp] is
     not needed. *)
  Let slli x y := gen_smart_opi add slli (fun _ => true) (Some 0) x y x.
  Let srli x y := gen_smart_opi add srli (fun _ => true) (Some 0) x y x.

  Definition smart_align (x y : var_i) (ws : wsize) : seq opn_args :=
    let imm := wsize_size ws - 1 in
    srli x y imm ++ slli x x imm.

  End WITH_PARAMS.

End OPN.

Module COPN := OPN(COPN_ARGS).
Module FOPN := OPN(FOPN_ARGS).
