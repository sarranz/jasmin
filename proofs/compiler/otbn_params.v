From mathcomp Require Import
  all_ssreflect
  all_algebra
  word_ssrZ.

Require Import
  arch_decl
  arch_extra
  arch_params
.
Require Import
  compiler_util
  expr
  fexpr
.
Require Import
  otbn_decl
  otbn_extra
  otbn_instr_decl
  otbn_lowering
.
Require
  asm_gen
  linearization
  slh_lowering
  stack_alloc
  stack_zeroization
.


Module E.
  Definition pass := "OTBN parameters"%string.

  Section ERROR.
    Import compiler_util.

    Let user_error oii pp :=
      {|
        pel_msg := pp;
        pel_fn := None;
        pel_fi := None;
        pel_ii := oii;
        pel_vi := None;
        pel_pass := Some pass;
        pel_internal := false
      |}.

    Definition szp_cmd :=
      user_error None (pp_s "Stack zeroization not implemented").

  End ERROR.

End E.

#[local]
Open Scope Z.

Section WITH_PARAMS.

Context {atoI : arch_toIdent}.

Section SAPARAMS.

  Import stack_alloc.

  Definition mov_ofs
    (x : lval)
    (tag : assgn_tag)
    (vpk : vptr_kind)
    (y : pexpr)
    (ofs : Z) :
    option instr_r :=
    let eofs := eword_of_int reg_size ofs in
    let '(op, args) :=
      match mk_mov vpk with
      | MK_LEA => (LA, [:: add y eofs ]) (* TODO_OTBN: Is this correct? *)
      | MK_MOV => if (ofs == 0)%Z then (MOV, [:: y ]) else (ADDI, [:: y; eofs ])
      end in
    Some (Copn [:: x ] tag (Ootbn (RV32 op)) args).

  Definition immediate (x : var_i) (imm : Z) : instr_r :=
    instr_of_copn_args AT_none (COPN.li x imm).

  Definition saparams : stack_alloc_params :=
    {|
      sap_mov_ofs := mov_ofs;
      sap_immediate := immediate;
    |}.

End SAPARAMS.

Section LIPARAMS.

  Import linearization.

  Definition vtmp : var := to_var X28. (* TODO_OTBN: Is this a good choice? *)

  Let vtmpi := mk_var_i vtmp.

  Definition allocate_stack_frame (rspi : var_i) (sz : Z) : fopn_args :=
    FOPN.subi rspi rspi sz.

  Definition free_stack_frame (rspi : var_i) (sz : Z) : fopn_args :=
    FOPN.addi rspi rspi sz.

  Definition set_up_sp_register
    (rspi : var_i)
    (sf_sz : Z)
    (al : wsize)
    (r : var_i) :
    option (seq fopn_args) :=
    if [&& 0 <=? sf_sz & sf_sz <? wbase reg_size ]
    then
      let c_copy := FOPN.smart_mov r rspi in
      let c_sub := FOPN.smart_subi rspi rspi vtmpi sf_sz in
      let c_align := FOPN.smart_align rspi rspi al in
      Some (c_copy ++ c_sub ++ c_align)
    else
      None.

  Definition set_up_sp_stack
    (rspi : var_i)
    (sf_sz : Z)
    (al : wsize)
    (off : Z) :
    option (seq fopn_args) :=
    if [&& 0 <=? sf_sz & sf_sz <? wbase reg_size ]
    then
      let c_sub := FOPN.smart_subi vtmpi rspi vtmpi sf_sz in
      let c_align := FOPN.smart_align vtmpi vtmpi al in
      let i_store := FOPN.sw reg_size vtmpi off rspi in
      let c_move := FOPN.smart_mov rspi vtmpi
      in Some (c_sub ++ c_align ++ i_store :: c_move)
    else
      None.

  Definition lassign
    (le : lexpr) (ws : wsize) (re : rexpr) : option fopn_args :=
  let%opt (mn, re') :=
    match le with
    | LLvar _ =>
        match re with
        | Rexpr (Fapp1 (Oword_of_int U32) (Fconst _)) => Some (LI, re)
        | Rexpr (Fvar _) => Some (MOV, re)
        | Load _ _ _ => Some (LW, re)
        | _ => None
        end
    | Store _ _ _ => Some (SW, re)
    end
  in
  Some ([:: le ], Ootbn (RV32 mn), [:: re' ]).

  Definition liparams : linearization_params :=
    {|
      lip_tmp := vname vtmp;
      lip_not_saved_stack := [:: vname vtmp ];
      lip_allocate_stack_frame := allocate_stack_frame;
      lip_free_stack_frame := free_stack_frame;
      lip_set_up_sp_register := set_up_sp_register;
      lip_set_up_sp_stack := set_up_sp_stack;
      lip_lassign := lassign;
    |}.

End LIPARAMS.

Section LOPARAMS.

  Definition loparams : lowering_params lowering_options :=
    {|
      lop_lower_i := fun _ _ _ => lower_i;
      lop_fvars_correct := fun _ _ _ => true;
    |}.

End LOPARAMS.

Section AGPARAMS.

  Import asm_gen.

  Let err ii fe := E.berror ii fe "Can't assemble condition.".

  Definition condt_not ii (c : condition) : cexec condition :=
    match c with
    | RVcond is_eq r0 r1 => ok (RVcond (~~ is_eq) r0 r1)
    | BNcond f => Error (err ii (Fvar (mk_var_i (to_var f))))
    end.

  Fixpoint assemble_cond ii (fe : fexpr) : cexec condition :=
    match fe with
    | Fvar x => Let f := of_var_e ii x in ok (BNcond f)
    | Fapp1 Onot fe => Let c := assemble_cond ii fe in condt_not ii c
    | Fapp2 op1 (Fvar x0) (Fvar x1) =>
        Let is_eq :=
          let chk ws := assert (ws == reg_size) (err ii fe) in
          match op1 with
          | Oeq (Op_w ws) => Let _ := chk ws in ok true
          | Oneq (Op_w ws) => Let _ := chk ws in ok false
          | _ => Error (err ii fe)
          end
        in
        Let r0 := of_var_e ii x0 in
        Let r1 := of_var_e ii x1 in
        ok (RVcond is_eq r0 r1)
    | _ => Error (err ii fe)
    end.

  Definition agparams : asm_gen_params :=
    {|
      agp_assemble_cond := assemble_cond;
    |}.

End AGPARAMS.

Section SHPARAMS.

  Import slh_lowering.

  Definition shparams : sh_params :=
    {|
      shp_lower := fun _ _ _ => None;
    |}.

End SHPARAMS.


Section SZPARAMS.

  Import stack_zeroization.

  Definition szparams : stack_zeroization_params :=
    {|
      szp_cmd := fun _ _ _ _ _ _ => Error E.szp_cmd;
    |}.

End SZPARAMS.

Definition is_move_op (eop : extended_op) : bool :=
  if eop is BaseOp (None, op) then op \in [:: RV32 MOV; BN_MOV ] else false.

Definition otbn_params : architecture_params lowering_options :=
  {|
    ap_sap := saparams;
    ap_lip := liparams;
    ap_lop := loparams;
    ap_agp := agparams;
    ap_shp := shparams;
    ap_szp := szparams;
    ap_is_move_op := is_move_op;
  |}.

End WITH_PARAMS.
