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
  lea
.
Require Import
  otbn_decl
  otbn_extra
  otbn_instr_decl
  otbn_lower_addressing
  otbn_lowering
  otbn_params_core
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

  (* The operation computing [base + imm]: a register move when [imm] is
     zero, [ADDI] when it fits the 12-bit immediate, and the [ADD_LARGE_IMM]
     extra op otherwise. The return type is pinned to [otbn_extended_op]
     (rather than left to infer as the unfolded [extended_op_gen otbn_op
     extra_op]) so that the [asmOp] instance needed by [Oasm]/[sem_sopn] at
     use sites resolves via typeclass search instead of by unification with
     an already-elaborated term. *)
  Definition add_imm_op (base : var_i) (imm : Z) : otbn_extended_op * pexprs :=
    if imm == 0%Z then (ExtOp MOV, [:: Plvar base ])
    else if is_arith_small imm then
      (BaseOp (None, RV32 ADDI), [:: Plvar base; cast_const imm ])
    else (ExtOp ADD_LARGE_IMM, [:: Plvar base; cast_const imm ]).

 (* TODO_OTBN: Is the LEA case correct? *)
  (* Mirrors [riscv_mov_ofs]: in the [MK_MOV] branch we dispatch on the shape
     of [x] and [y] so that spilling/unspilling a [reg ptr] through a stack
     slot emits a load ([LW]) or a store ([SW]) instead of a register move with
     a memory operand (which would be rejected by asmgen as "invalid lvals").
     The displacement [ofs] is already folded into the address, so we fail
     cleanly (return [None]) when [ofs <> 0] in the load or store case.
     Otherwise, [mk_lea] normalizes [y + ofs] (e.g. an unscaled access
     produces [ofs = 1 * e + 0]) and we dispatch on the decomposition:
     [MOV] for a plain register, [ADDI] for a small displacement, the
     [ADD_LARGE_IMM] extra op for a large one, and [ADD] for a register
     offset (scale 1, no displacement). *)
  Definition mov_ofs
    (x : lval) (tag : assgn_tag) (movk : mov_kind) (y : pexpr) (ofs : pexpr) :
    option instr_r :=
    let mk oa := Some (Copn [:: x ] tag (Oasm oa.1) oa.2) in
    match movk with
    | MK_LEA =>
        mk (BaseOp (None, RV32 LA),
            [:: if is_zero Uptr ofs then y else add y ofs ])
    | MK_MOV =>
        match x with
        | Lvar _ =>
            if is_Pload y then
              let%opt _ := oassert (is_zero Uptr ofs) in
              mk (BaseOp (None, RV32 LW), [:: y ])
            else
              let%opt lea := mk_lea Uptr (add y ofs) in
              let%opt base := lea.(lea_base) in
              match lea.(lea_offset) with
              | None => mk (add_imm_op base lea.(lea_disp))
              | Some off =>
                  let%opt _ :=
                    oassert [&& lea.(lea_disp) == 0%Z & lea.(lea_scale) == 1%Z ]
                  in
                  mk (BaseOp (None, RV32 ADD), [:: Plvar base; Plvar off ])
              end
        | Lmem _ _ _ _ =>
            let%opt _ := oassert (is_zero Uptr ofs) in
            mk (BaseOp (None, RV32 SW), [:: y ])
        | _ => None
        end
    end.

  Definition immediate (x : var_i) (imm : Z) : instr_r :=
    Copn [:: Lvar x ] AT_none (Ootbn (RV32 LI)) [:: cast_const imm ].

  Definition swap (t : assgn_tag) (x y z w : var_i) : instr_r :=
    Copn [:: Lvar x; Lvar y ] t (Oasm (ExtOp (SWAP reg_size))) [:: Plvar z; Plvar w ].

  Definition saparams : stack_alloc_params :=
    {|
      sap_mov_ofs := mov_ofs;
      sap_immediate := immediate;
      sap_swap := swap;
    |}.

End SAPARAMS.

Section LIPARAMS.

  Import linearization.

  Definition vtmp : var := to_var X28. (* TODO_OTBN: Is this a good choice? *)
  Definition vtmp2 : var := to_var X29. (* TODO_OTBN: Is this a good choice? *)

  Let vtmpi := mk_var_i vtmp.
  Let vtmp2i := mk_var_i vtmp2.

  Definition fopn_args_of_opn_args (oa : OTBNFopn_core.opn_args) : fopn_args :=
    let '(le, op, re) := oa in (le, Ootbn op, re).

  (* TODO_OTBN use the smart constructors? *)
  Definition allocate_stack_frame
    (rspi : var_i) (tmp : option var_i) (sz : Z) : seq fopn_args :=
    let c := [:: OTBNFopn_core.subi rspi rspi sz ] in
    let c' :=
      let%opt aux := tmp in OTBNFopn_core.smart_subi_tmp rspi aux sz
    in
    [seq fopn_args_of_opn_args x | x <- odflt c c' ].

  Definition free_stack_frame
    (rspi : var_i) (tmp : option var_i) (sz : Z) : seq fopn_args :=
    let c := [:: OTBNFopn_core.addi rspi rspi sz ] in
    let c' :=
      let%opt aux := tmp in OTBNFopn_core.smart_addi_tmp rspi aux sz
    in
    [seq fopn_args_of_opn_args x | x <- odflt c c' ].

  (* TODO_OTBN move inside params_core *)
  Definition smart_addi x y imm :=
    let c := [:: OTBNFopn_core.addi x y imm ] in
    let c' := OTBNFopn_core.smart_addi x y imm in
    odflt c c'.

  (* TODO_OTBN move inside params_core *)
  Definition smart_subi x y imm :=
    let c := [:: OTBNFopn_core.subi x y imm ] in
    let c' := OTBNFopn_core.smart_subi x y imm in
    odflt c c'.

  Definition set_up_sp_register
    (rspi : var_i) (sf_sz : Z) (al : wsize) (r : var_i) (tmp : var_i):
    seq fopn_args :=
    let c_copy := OTBNFopn_core.smart_mov r rspi in
    let c_sub := smart_subi rspi r sf_sz in
    let c_align := [:: OTBNFopn_core.align rspi rspi al ] in
    [seq fopn_args_of_opn_args a | a <- c_copy ++ c_sub ++ c_align ].

  Definition lmove (xd xs : var_i) : fopn_args :=
    fopn_args_of_opn_args (OTBNFopn_core.mov xd xs).

  Definition check_ws ws := ws == reg_size.

  Definition lstore (xd : var_i) (ofs : Z) (xs : var_i) : fopn_args :=
    let e := faddv reg_size xd (fconst reg_size ofs) in
    fopn_args_of_opn_args (OTBNFopn_core.sw reg_size e xs).

  Definition lload (xd : var_i) (xs : var_i) (ofs : Z) :=
    let e := faddv reg_size xs (fconst reg_size ofs) in
    fopn_args_of_opn_args (OTBNFopn_core.lw reg_size xd e).

  Definition smart_addi_fopn x y imm :=
    [seq fopn_args_of_opn_args a | a <- smart_addi x y imm ].

  Definition lstores :=
    lstores_imm_dfl vtmp2.(vname) lstore smart_addi_fopn is_arith_small.

  Definition lloads :=
    lloads_imm_dfl vtmp2.(vname) lload smart_addi_fopn is_arith_small.

  Definition liparams : linearization_params :=
    {|
      lip_tmp := vname vtmp;
      lip_tmp2 := vname vtmp2;
      lip_not_saved_stack := [:: vname vtmp ];
      lip_allocate_stack_frame := allocate_stack_frame;
      lip_free_stack_frame := free_stack_frame;
      lip_set_up_sp_register := set_up_sp_register;
      lip_lmove := lmove;
      lip_check_ws := check_ws;
      lip_lstore  := lstore;
      lip_lload := lload;
      lip_lstores := lstores;
      lip_lloads := lloads;
    |}.

End LIPARAMS.

Section LOPARAMS.

  Definition loparams : lowering_params :=
    {|
      lop_lower_i := fun _ _ => lower_i;
      lop_fvars_correct := fun _ _ _ => true;
    |}.

End LOPARAMS.

Definition is_fzero (ws : wsize) (e : fexpr) : bool :=
  if e is Fapp1 (Oword_of_int ws') (Fconst 0) then ws' == ws else false.

Definition is_fvar (e : fexpr) : option var_i :=
  if e is Fvar x then Some x else None.

Section AGPARAMS.

  Import asm_gen.

  Let err ii fe := E.berror ii fe "Can't assemble condition.".

  Section AUX.
    Context
      (ii : instr_info)
      (fe : fexpr)
    .

  Definition condt_not (c : condition) : cexec condition :=
    match c with
    | RVcond is_eq r0 r1 => ok (RVcond (~~ is_eq) r0 r1)
    | BNcond f => Error (err ii (Fvar (mk_var_i (to_var f))))
    end.

  Definition sop2_is_eq (o : sop2) : cexec bool :=
    let chk ws := assert (ws == reg_size) (err ii fe) in
    match o with
    | Oeq (Op_w ws) => Let _ := chk ws in ok true
    | Oneq (Op_w ws) => Let _ := chk ws in ok false
    | _ => Error (err ii fe)
    end.

  Definition oreg_of_fexpr (e : fexpr) : cexec (option register) :=
    if is_fzero reg_size e then ok None
    else if is_fvar e is Some x then Let r := of_var_e ii x in ok (Some r)
    else Error (err ii fe).

  Definition assemble_cond_app2 (o : sop2) (e0 e1 : fexpr) : cexec condition :=
    Let is_eq := sop2_is_eq o in
    Let r0 := oreg_of_fexpr e0 in
    Let r1 := oreg_of_fexpr e1 in
    ok (RVcond is_eq r0 r1).

  End AUX.

  Fixpoint assemble_cond ii (fe : fexpr) : cexec condition :=
    match fe with
    | Fvar x => Let f := of_var_e ii x in ok (BNcond f)
    | Fapp1 Onot fe => Let c := assemble_cond ii fe in condt_not ii c
    | Fapp2 o e0 e1 => assemble_cond_app2 ii fe o e0 e1
    | _ => Error (err ii fe)
    end.

  (* TODO_OTBN: Is this correct? It can be simplified *)
  Definition is_valid_address (addr : reg_address) :=
    match addr.(ad_disp) != 0%w, isSome addr.(ad_offset), addr.(ad_scale) != 0%N with
    | false, false, false => true
    | true, false, false => true
    | _, _, _ => false
    end.

  Definition agparams : asm_gen_params :=
    {|
      agp_assemble_cond := assemble_cond;
      agp_is_valid_address := is_valid_address;
    |}.

End AGPARAMS.

Section LAPARAMS.

Definition laparams : lower_addressing_params :=
  {| lap_lower_address := lower_addressing_prog; |}.

End LAPARAMS.

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
    {| szp_cmd := fun _ _ _ _ _ _ => Error E.szp_cmd; |}.

End SZPARAMS.

Definition is_move_op (o : asm_op_t) : bool :=
  match o with
  | BaseOp (None, BN_MOV) | ExtOp MOV => true
  | _ => false
  end.

Definition otbn_params : architecture_params :=
  {|
    ap_sap := saparams;
    ap_lip := liparams;
    ap_plp := true;
    ap_lop := loparams;
    ap_agp := agparams;
    ap_lap := laparams;
    ap_shp := shparams;
    ap_szp := szparams;
    ap_is_move_op := is_move_op;
  |}.

End WITH_PARAMS.
