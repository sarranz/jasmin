From elpi.apps Require Import derive.std.
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssralg.

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
  otbn_instr_decl
  otbn_params_core
.
Require arm_extra.

Module E.

  Definition pass_name : string := "assembly generation".

  Definition internal_error (msg : string) (ii : instr_info) : pp_error_loc :=
    (pp_internal_error_s_at pass_name ii msg).

  Definition invalid_lexprs := internal_error "invalid destination".
  Definition invalid_rexprs := internal_error "invalid arguments".
  Definition invalid_args := internal_error "invalid destination or arguments".

End E.

Definition asm_args_of_opn_args
  : seq OTBNFopn_core.opn_args -> seq (asm_op_msb_t * lexprs * rexprs) :=
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
| bn_indirect_load
| bn_indirect_store
| MOV  (* [ADDI x, y, 0]. *)
| SUBI (* [ADDI x, y, -imm]. *)
.

HB.instance Definition _ := hasDecEq.Build extra_op extra_op_eqb_OK.

#[export]
Instance eqTC_otbn_extra_op : eqTypeC extra_op := { ceqP := extra_op_eqb_OK }.

Definition string_of_extra_op (eo : extra_op) : string :=
  match eo with
  | set0 _ => "set0"
  | bn_indirect_load => "BN_INDIRECT_LOAD"
  | bn_indirect_store => "BN_INDIRECT_STORE"
  | MOV => "MOV"
  | SUBI => "SUBI"
  end.

Definition desc_set0_small : instruction_desc :=
  mk_instr_desc_safe
    (pp_s (string_of_extra_op (set0 U8)))
    [::] [::]
    [:: aword U32 ] [:: E 0 ]
    0%R
    true.

Definition desc_set0_large : instruction_desc :=
  let vf := Some false in
  let vt := Some true in
  mk_instr_desc_safe
    (pp_s (string_of_extra_op (set0 U8)))
    [::] [::]
    [:: abool; abool; abool; aword U256 ] ([:: F MF0; F LF0; F ZF0; E 0 ])
    (:: vf, vf, vt & 0%R)
    true.

Definition desc_indirect : instruction_desc :=
  mk_instr_desc_safe
    (pp_s (string_of_extra_op bn_indirect_load))
    [:: aword U256 ] [:: E 1 ]
    [:: aword U256 ] [:: E 0 ]
    id
    true.

Definition desc_MOV : instruction_desc :=
  mk_instr_desc_safe
    (pp_s (string_of_extra_op MOV))
    [:: aword U32 ] [:: E 1 ]
    [:: aword U32 ] [:: E 0 ]
    id
    true.

Definition desc_SUBI : instruction_desc :=
  mk_instr_desc_safe
    (pp_s (string_of_extra_op SUBI))
    [:: aword U32; aword U32 ] [:: E 1; E 2 ]
    [:: aword U32 ] [:: E 0 ]
    (fun x y => x - y)%R
    true.

Definition get_instr_desc (eo : extra_op) : instruction_desc :=
  match eo with
  | set0 ws => if (ws <= reg_size)%CMP then desc_set0_small else desc_set0_large
  | bn_indirect_load | bn_indirect_store => desc_indirect
  | MOV => desc_MOV
  | SUBI => desc_SUBI
  end.

Definition prim_string : seq (string * prim_constructor extra_op) :=
  [:: (string_of_extra_op (set0 U8), prim_otbn_ws set0)
    ; (string_of_extra_op bn_indirect_load, prim_otbn_none bn_indirect_load)
    ; (string_of_extra_op bn_indirect_store, prim_otbn_none bn_indirect_store)
    ; (string_of_extra_op MOV, prim_otbn_none MOV)
    ; (string_of_extra_op SUBI, prim_otbn_none SUBI)
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

  Definition assemble_set0
    (ws : wsize)
    (les : seq lexpr)
    (res : seq rexpr) :
    cexec (seq (asm_op_msb_t * seq lexpr * seq rexpr)) :=
    let '(op, v) :=
      if (ws <= reg_size)%CMP then (RV32 XOR, to_var X03)
      else (BN_basic BN_XOR FG0, to_var W01)
    in
    let x := rvar (mk_var_i v) in
    ok [:: ((None, op), les, [:: x; x ]) ].

  Definition idx_of_wide_register (wr : wide_register) : option Z :=
    match wr with
    | W00 => Some 0
    | W01 => Some 1
    | W02 => Some 2
    | W03 => Some 3
    | W04 => Some 4
    | W05 => Some 5
    | W06 => Some 6
    | W07 => Some 7
    | W08 => Some 8
    | W09 => Some 9
    | W10 => Some 10
    | W11 => Some 11
    | W12 => Some 12
    | W13 => Some 13
    | W14 => Some 14
    | W15 => Some 15
    | W16 => Some 16
    | W17 => Some 17
    | W18 => Some 18
    | W19 => Some 19
    | W20 => Some 20
    | W21 => Some 21
    | W22 => Some 22
    | W23 => Some 23
    | W24 => Some 24
    | W25 => Some 25
    | W26 => Some 26
    | W27 => Some 27
    | W28 => Some 28
    | W29 => Some 29
    | W30 => Some 30
    | W31 => Some 31
    | ACC => None
    | MOD => None
    end%Z.

  Let uncons {X} := arm_extra.uncons (X := X) ii.
  Let uncons_LLvar := arm_extra.uncons_LLvar ii.
  Let uncons_rvar := arm_extra.uncons_rvar ii.
  Let uncons_wconst := arm_extra.uncons_wconst ii.

  Definition assemble_bn_indirect_load
    (les : seq lexpr)
    (res : seq rexpr) :
    cexec (seq (asm_op_msb_t * seq lexpr * seq rexpr)) :=
    Let: (vrd, les) := uncons_LLvar les in
    Let: (vwr, les) := uncons_LLvar les in
    Let: (addr, _) := uncons res in
    Let _ :=
      if addr is Load _ U256 _ then ok tt else Error (E.invalid_rexprs ii)
    in
    Let wr := o2r (E.invalid_lexprs ii) (of_var vwr) in
    Let nwr := o2r (E.invalid_lexprs ii) (idx_of_wide_register wr) in
    ok [:: ((None, RV32 LI), [:: LLvar vrd ], [:: rconst reg_size nwr ])
         ; ((None, BN_LID), [:: LLvar vwr ], [:: rvar vrd; addr ])
        (* TODO_OTBN To give a semantics to this operator we should set the
           small register to a fixed value.
           Since indirect addressing has no semantics anyways, I skip it for
           now.
           ((None, RV32 LI), [:: LLvar vrd ], [:: rconst reg_size 0 ] ) *)
      ].

  Definition assemble_bn_indirect_store
    (les : seq lexpr)
    (res : seq rexpr) :
    cexec (seq (asm_op_msb_t * seq lexpr * seq rexpr)) :=
    Let: (vrd, les) := uncons_LLvar les in
    Let: (addr, _) := uncons les in
    Let _ :=
      if addr is Store _ U256 _ then ok tt else Error (E.invalid_lexprs ii)
    in
    Let: (vwr, _) := uncons_rvar res in
    Let wr := o2r (E.invalid_lexprs ii) (of_var vwr) in
    Let nwr := o2r (E.invalid_lexprs ii) (idx_of_wide_register wr) in
    ok [:: ((None, RV32 LI), [:: LLvar vrd ], [:: rconst reg_size nwr ])
         ; ((None, BN_SID), [:: addr ], [:: rvar vrd; rvar vwr ])
        (* ((None, RV32 LI), [:: LLvar vrd ], [:: rconst reg_size 0 ] ) *)
    ].

  Definition assemble_MOV
    (les : seq lexpr)
    (res : seq rexpr) :
    cexec (seq (asm_op_msb_t * seq lexpr * seq rexpr)) :=
    Let: (x, _) := uncons_LLvar les in
    Let: (y, _) := uncons_rvar res in
    ok (asm_args_of_opn_args (OTBNFopn_core.smart_mov x y)).

  Definition assemble_SUBI
    (les : seq lexpr)
    (res : seq rexpr) :
    cexec (seq (asm_op_msb_t * seq lexpr * seq rexpr)) :=
    Let: (x, _) := uncons_LLvar les in
    Let: (y, res) := uncons_rvar res in
    Let: (imm, _) := uncons_wconst res in
    Let args := o2r (E.invalid_args ii) (OTBNFopn_core.smart_subi x y imm) in
    ok (asm_args_of_opn_args args).

  Definition assemble_extra
    (eo : extra_op)
    (les : seq lexpr)
    (res : seq rexpr) :
    cexec (seq (asm_op_msb_t * seq lexpr * seq rexpr)) :=
    match eo with
    | set0 ws => assemble_set0 ws les res
    | bn_indirect_load => assemble_bn_indirect_load les res
    | bn_indirect_store => assemble_bn_indirect_store les res
    | MOV => assemble_MOV les res
    | SUBI => assemble_SUBI les res
    end.

End ASSEMBLE.

#[export]
Instance otbn_extra :
  asm_extra register empty wide_register rflag condition otbn_op extra_op :=
  { to_asm := assemble_extra; }.

(* This concise name is convenient in OCaml code. *)
Definition otbn_extended_op : Type := extended_op (asm_e := otbn_extra).

Definition Ootbn (o : otbn_op) : sopn := Oasm (BaseOp (None, o)).

End WITH_PARAMS.
