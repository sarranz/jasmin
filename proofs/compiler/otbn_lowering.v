(* Lowering pass for OTBN.
   TODO_OTBN: we always use FG1 for dummies, such that if the source uses FG0
   (the default), we get fewer conflicts. Maybe we should check and insert
   according to whatever is not being used. *)

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssralg.
From mathcomp Require Import word_ssrZ.

Require Import
  compiler_util
  expr
  lowering
  otbn_options
  pseudo_operator.
Require Import
  arch_decl
  arch_extra.
Require Import
  otbn_decl
  otbn_extra
  otbn_instr_decl
  otbn_params_core.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

#[local]
Open Scope Z.

Module E.

  Import compiler_util.

  Definition pass_name : string := "lowering".

  Definition internal_error (msg : string) (ii : instr_info) : pp_error_loc :=
    pp_internal_error_s_at pass_name ii msg.

  Definition user_error (err : pp_error) (ii : instr_info) : pp_error_loc :=
    {|
      pel_msg := err;
      pel_fn := None;
      pel_fi := None;
      pel_ii := Some ii;
      pel_vi := None;
      pel_pass := Some pass_name;
      pel_internal := false;
    |}.

  Definition user_error_s msg := user_error (pp_s msg).

  Section ERRORS.

    Context (ii : instr_info).

    Definition invalid_wsize := internal_error "invalid wsize".
    Definition invalid_type := internal_error "invalid type".

    Definition not_implemented := user_error_s "not implemented".
    Definition invalid_expr := user_error_s "can't lower expression".
    Definition invalid_carry_lvals := user_error_s "invalid carry destination".
    Definition invalid_carry_pexprs := user_error_s "invalid carry arguments".
    Definition cant_lower_mulu := user_error_s "can't lower MULU".

    Definition invalid_sham (e : pexpr) : pp_error_loc :=
      let err := pp_box
        [:: pp_s "invalid shift amount:"
         ; pp_e e
         ; pp_s ". Must be in the range [0, 31] or masked with 0x1f."
        ]
      in
      user_error err ii.

    Definition imm_out_of_range {ws : wsize} (w : word ws) : pp_error_loc :=
      let err :=
        pp_box [:: pp_s "immediate out of range:"; pp_e (wconst w) ]
      in
      user_error err ii.

    Definition invalid_address (e : pexpr) : pp_error_loc :=
      let err := pp_box [:: pp_s "invalid address:"; pp_e e ] in
      user_error err ii.

    Definition bn_immediate (e : pexpr) : pp_error_loc :=
      let err :=
        pp_box [:: pp_s "invalid immediate for wide register"; pp_e e ]
      in
      user_error err ii.

    Definition invalid_arguments (es : seq pexpr) : pp_error_loc :=
      let err := pp_box (pp_s "invalid argumens" :: map pp_e es ) in
      user_error err ii.

  End ERRORS.

End E.


Section WITH_PARAMS.

Context {atoI : arch_toIdent}.

(* -------------------------------------------------------------------------- *)
(* Lowering a Jasmin instruction can lead to:
   - An error.
   - Skipping the instruction.
   - Issuing equivalent architecture-specific code. *)
Definition lresult (A : Type) : Type := cexec (option A).

Definition issue {A : Type} (a : A) : lresult A := ok (Some a).

Definition skip {A : Type} : lresult A := ok None.

Definition lassert (b : bool) (e : pp_error_loc) : lresult unit :=
  Let _ := assert b e in issue tt.

Notation "'let%lr' x ':=' m 'in' body" :=
  (Let o := m in if o is Some x then body else skip)
  (x strict pattern, at level 25, only parsing).

Definition otbn_args : Type := seq lval * extended_op * seq pexpr.

Definition low_instr := lresult otbn_args.

Definition li_sissue
  (lvs : seq lval) (op : extended_op) (es : seq pexpr) : low_instr :=
  issue (lvs, op, es).

Definition li_issue lvs op es := li_sissue lvs (BaseOp (None, op)) es.
Definition li_xissue lvs op es := li_sissue lvs (ExtOp op) es.

Definition li_ssimple := li_sissue [::].
Definition li_simple := li_issue [::].

Definition low_cmd :=
  lresult (seq otbn_args * seq lval * extended_op * seq pexpr).

Definition lc_sissue
  (pre : seq otbn_args) (lvs : seq lval) (op : extended_op) (es : seq pexpr) :
  low_cmd :=
  issue (pre, lvs, op, es).

Definition lc_issue pre lvs op es := lc_sissue pre lvs (BaseOp (None, op)) es.
Definition lc_xissue pre lvs op es := lc_sissue pre lvs (ExtOp op) es.

Definition no_pre (li : low_instr) : low_cmd :=
  let%lr (lvs, op, es) := li in
  lc_sissue [::] lvs op es.

Definition with_pre (pre : seq otbn_args) (li : low_instr) : low_cmd :=
  let%lr (lvs, op, es) := li in
  lc_sissue pre lvs op es.

(* -------------------------------------------------------------------------- *)
Section UTILS.

  Context (ii : instr_info).

  Definition lnoneb : lval := Lnone_b dummy_var_info.
  Definition lnone_mlz : seq lval := nseq 3 lnoneb.
  Definition lnone_cmlz : seq lval := nseq 4 lnoneb.

  Definition chk_le_reg_ws (ws : wsize) : cexec unit :=
    assert (ws <= reg_size)%CMP (E.invalid_wsize ii).

  Notation chk_ws :=
    (fun (ws ws' : wsize) => assert (ws' == ws)%CMP (E.invalid_wsize ii)).
  Definition chk_reg_ws := chk_ws reg_size.
  Definition chk_xreg_ws := chk_ws xreg_size.

  Definition chk_bn_shift (z : Z) : cexec unit :=
    assert (check_bn_shift z) (E.invalid_sham ii (Pconst z)).

  Definition chk_address_displacement (ws : wsize) (w : word ws) : cexec unit :=
    assert (check_nbits Signed 12 w) (E.imm_out_of_range ii w).

  (* [bn.ld] and [bn.sd] *)
  Definition check_bn_displacement (i : Z) : bool :=
    [&& -16384 <=? i, i <=? 16352 & i mod 32 == 0 ]%Z.

  Definition chk_bn_address_displacement
    (ws : wsize) (w : word ws) : cexec unit :=
    assert (check_bn_displacement (wsigned w)) (E.imm_out_of_range ii w).

  Definition reg_shift_of_sop2
    (ws : wsize) (op : sop2) : lresult bn_register_shift :=
    Let _ := chk_xreg_ws ws in
    match op with
    | Olsl (Op_w U256) => issue RS_left
    | Olsr U256 => issue RS_right
    | _ => skip
    end.

  (* Return [(e, <+>, sham)] if an expression has the form [e <+> sham] and
     [<+>] is a shift operator. *)
  Definition get_arg_shift
    (ws : wsize) (e : pexpr) : lresult (pexpr * bn_register_shift * pexpr) :=
    if e is Papp2 op (Pvar x) (Papp1 (Oword_of_int U8) (Pconst z))
    then
      let%lr sh := reg_shift_of_sop2 ws op in
      Let _ := chk_bn_shift z in
      issue (Pvar x, sh, Papp1 (Oword_of_int U8) (Pconst z))
    else skip.

  Definition rsnoc
    {eT aT : Type} (e : eT) (xs : seq aT) : result eT (aT * seq aT) :=
    if xs is x :: xs then ok (x, xs) else Error e.

  Definition rsnoc2
    {eT aT : Type} (e : eT) (xs : seq aT) : result eT (aT * aT * seq aT) :=
    Let: (x, xs) := rsnoc e xs in
    Let: (y, xs) := rsnoc e xs in
    ok (x, y, xs).

  Definition rsnoc3
    {eT aT : Type} (e : eT) (xs : seq aT) : result eT (aT * aT * aT * seq aT) :=
    Let: (x, y, xs) := rsnoc2 e xs in
    Let: (z, xs) := rsnoc e xs in
    ok (x, y, z, xs).

End UTILS.


(* -------------------------------------------------------------------------- *)
(* Lower [Copn] arguments and pseudo-operators. *)
Section LOWER_OPN.

  Context (ii : instr_info).

  (* ------------------------------------------------------------------------ *)
  (* [Copn] arguments. *)

  (* Match the arguments of a basic OTBN operation and return the shift kind
     if there is one, [skip] otherwise. *)
  Definition lower_basic_shift
    (mn : bn_basic_mnemonic) (es : seq pexpr) :
    lresult (bn_register_shift * seq pexpr) :=
    let err := E.invalid_arguments ii es in
    Let: (pre, e, pos) :=
      match mn with
      | BN_NOT => Let: (x, rest) := rsnoc err es in ok ([::], x, rest)
      | BN_ADD | BN_SUB | BN_AND | BN_OR | BN_XOR | BN_CMP | BN_CMPB =>
          Let: (x, y, rest) := rsnoc2 err es in ok ([:: x ], y, rest)
      | BN_ADDC | BN_SUBB =>
          Let: (x, y, cf, rest) := rsnoc3 err es in ok ([:: x ], y, cf :: rest)
      end
    in
    let%lr (ebase, sh, esham) := get_arg_shift ii xreg_size e in
    issue (sh, pre ++ ebase :: pos ++ [:: esham ]).

  (* TODO_OTBN: use the checker from the instruction description to fail early
     for unsafe programs. *)
  (* TODO_OTBN: the other operations should be skipped, not give an error *)
  Definition lower_base_op
    (lvs : seq lval) (op : otbn_op) (es : seq pexpr) : low_instr :=
    match op with
    | RV32 mn => li_issue lvs op es
    | BN_basic mn fg =>
        let%lr (sh, es') := lower_basic_shift mn es in
        li_issue lvs (BN_basic_shift mn fg sh) es'
    | _ => skip
    end.

  (* ------------------------------------------------------------------------ *)
  (* Pseudo-operators. *)

  (* Match [lvs] as [(carry, result)] and introduce dummies for the other
     flags. *)
  Definition get_carry_lvals (lvs : seq lval) : cexec (seq lval) :=
    Let: (cf, r, _) := rsnoc2 (E.invalid_carry_lvals ii) lvs in
    ok [:: cf; lnoneb; lnoneb; lnoneb; r ].

  (* Match [es] as [(e0, e1, carry)], check if the carry is constant [false],
     and remove it if so. *)
  Definition get_carry_pexprs (es : seq pexpr) : cexec (bool * seq pexpr) :=
    Let: (e0, e1, cf, _) := rsnoc3 (E.invalid_carry_pexprs ii) es in
    match cf with
    | Pbool false => ok (false, [:: e0; e1 ])
    | Pvar _ => ok (true, [:: e0; e1; cf ])
    | _ => Error (E.invalid_carry_pexprs ii)
    end.

  Definition carry_op (is_add has_carry : bool) : bn_basic_mnemonic :=
    if is_add then if has_carry then BN_ADDC else BN_ADD
    else if has_carry then BN_SUBB else BN_SUB.

  Definition lower_carry_op
    (is_add : bool) (sz : wsize) (lvs : seq lval) (es : seq pexpr) : low_instr :=
    Let _ := chk_xreg_ws ii sz in
    Let lvs' := get_carry_lvals lvs in
    Let: (has_carry, es') := get_carry_pexprs es in
    let op := carry_op is_add has_carry in
    li_issue lvs' (BN_basic op FG1) es'.

  Definition lower_swap
    (ty : atype) (lvs : seq lval) (es : seq pexpr) : low_instr :=
    if ty is aword sz then
      let%lr lvs :=
        if (sz == reg_size)%CMP then ok (Some lvs)
        else if (sz == xreg_size)%CMP then ok (Some (lnone_mlz ++ lvs))
        else Error (E.not_implemented ii)
      in
      li_xissue lvs (SWAP sz) es
    else skip.

  Definition lower_pseudo_operator
    (lvs : seq lval) (op : pseudo_operator) (es : seq pexpr) : low_instr :=
    let%lr (lvs', op', es') :=
      match op with
      | Oaddcarry sz => lower_carry_op true sz lvs es
      | Osubcarry sz => lower_carry_op false sz lvs es
      | Omulu _ => Error (E.cant_lower_mulu ii)
      | Oswap ty => lower_swap ty lvs es
      | _ => skip
      end
    in
    li_sissue lvs' op' es'.

  Definition lower_copn
    (lvs : seq lval) (op : sopn) (es : seq pexpr) : low_instr :=
    match op with
    | Opseudo_op pop => lower_pseudo_operator lvs pop es
    | Oasm (BaseOp (None, op)) => lower_base_op lvs op es
    | _ => skip
    end.

End LOWER_OPN.


(* -------------------------------------------------------------------------- *)
(* Compute a condition (e.g. with [CMP]). *)

Section LOWER_CONDITION.

  Context (ii : instr_info).

  Definition lower_condition (econd : pexpr) : cexec (seq otbn_args * pexpr) :=
    if econd is Pvar f then ok ([::], econd) else Error (E.not_implemented ii).

End LOWER_CONDITION.


(* -------------------------------------------------------------------------- *)
(* Convert an assignment into an architecture-specific operation. *)
Section LOWER_ASSIGN.

(* TODO_OTBN define a helper for case analysis
   Variant isa_variant := Vsmall | Vwide | Vwrong.
   with a reflection lemma and move all nested ifs to that. *)

  Context (ii : instr_info).

  (* Lower an expression of the form [v].
     Precondition:
     - [v] is a one of the following:
       + a register.
       + a stack variable. *)
  Definition lower_Pvar (ws : wsize) (v : gvar) : low_instr :=
    let%lr op :=
      if is_var_in_memory (gv v) then
        if (ws == reg_size)%CMP then issue (BaseOp (None, RV32 LW))
        else if (ws == xreg_size)%CMP then issue (BaseOp (None, BN_LD))
        else skip
      else
        if (ws == reg_size)%CMP then issue (ExtOp MOV)
        else if (ws == xreg_size)%CMP then issue (BaseOp (None, BN_MOV))
        else skip
    in
    li_ssimple op [:: Pvar v ].

  (* Match a memory access and return the base pointer and displacement (in
     bytes). *)
  Definition get_mem_disp (e : pexpr) : option wreg :=
    match e with
    | Pget _ _ ws x e' =>
        let%opt z := is_const e' in
        Some (wrepr reg_size (z * wsize_size ws))
    | Pload _ _ e => is_wconst reg_size e
    | _ => None
    end.

  (* Lower an expression of the form [(ws)[v]], [(ws)[v + e]] or [tab[ws e]].
     A 32-bit access becomes a [LW]; a 256-bit (wide) access becomes a
     [BN.LD]. *)
  Definition lower_load (ws : wsize) (e : pexpr) : low_instr :=
    let%lr op :=
      if ws == reg_size then
        Let _ :=
          if get_mem_disp e is Some wdisp then chk_address_displacement ii wdisp
          else ok tt
        in
        issue (RV32 LW)
      else if ws == xreg_size then
        Let _ :=
          if get_mem_disp e is Some wdisp
          then chk_bn_address_displacement ii wdisp
          else ok tt
        in
        issue BN_LD
      else skip
    in
    li_simple op [:: e ].

  (* Lower an expression of the form [<+> e]. *)
  Definition lower_Papp1 (ws : wsize) (op : sop1) (e : pexpr) : low_instr :=
    match op with
    | Oword_of_int _ =>
        if ws == reg_size then
          li_simple (RV32 LI) [:: Papp1 op e ]
        else skip
    | Olnot _ =>
        if ws == xreg_size then
          li_issue lnone_mlz (BN_basic BN_NOT FG1) [:: e ]
        else skip
    | Oneg (Op_w _) =>
        if ws == reg_size then
          li_simple (RV32 NEG) [:: e]
        else skip
    | _ => Error (E.not_implemented ii)
    end.

  (* TODO_OTBN Maybe we could extract from [instr_desc_op], but we need to fix
     the position of the immediate argument. *)
  Definition rv_expected_Imn_size (op : sop2) : option wsize :=
    match op with
    | Oadd _ | Osub _ | Oland _ | Olor _ | Olxor _ => Some U32
    | _ => None
    end.

  (* Shifts are special cases *)
  Definition rv_Imn_of_op2
    (op : sop2) (ws : wsize) (w : word ws) (e : pexpr) :
    lresult (rv_mnemonic * pexpr) :=
    let mk mn :=
      let%lr _ :=
        lassert (is_arith_small (wsigned w)) (E.imm_out_of_range ii w)
      in
      issue (mn, e)
    in
    match op with
    | Oadd (Op_w _) => mk ADDI
    | Osub (Op_w _) =>
        let%lr _ :=
          lassert (is_arith_small (wsigned (- w))) (E.imm_out_of_range ii w)
        in
        if insert_minus e is Some e' then issue (ADDI, e')
        else Error (E.invalid_expr ii) (* TODO_OTBN: better internal error *)
    | Oland _ => mk ANDI
    | Olor _ => mk ORI
    | Olxor _ => mk XORI
    | _ => skip
    end.

  (* Shifts are special cases *)
  Definition rv_mn_of_op2
    (op : sop2) (e : pexpr) : lresult (rv_mnemonic * pexpr) :=
    let mk mn := issue (mn, e) in
    match op with
    | Oadd (Op_w _) => mk ADD
    | Osub (Op_w _) => mk SUB
    | Oland _ => mk AND
    | Olor _ => mk OR
    | Olxor _ => mk XOR
    | _ => skip
    end.

  Definition check_shift_amount (e : pexpr) : option pexpr :=
    let mask := wrepr U8 31 in
    if is_wconst U8 e is Some n
    then let%opt _ := oassert (n == wand n mask) in Some e
    else if e is Papp2 (Oland _) a b then
      let%opt n := is_wconst U8 b in
      let%opt _ := oassert (n == mask) in
      Some a
    else None.

  Definition lower_shift
    (mn_imm mn_reg : rv_mnemonic) (e0 e1 : pexpr) : low_instr :=
    if check_shift_amount e1 is Some e1'
    then
      let mn := if is_wconst U8 e1' then mn_imm else mn_reg in
      li_simple (RV32 mn) [:: e0; e1' ]
    else Error (E.invalid_sham ii e1).

  (* Lower a binary 32-bit operation. *)
  Definition lower_Papp2_small
    (ws : wsize) (op : sop2) (e0 e1 : pexpr) : low_instr :=
    match op with
    | Olsl (Op_w _) => lower_shift SLLI SLL e0 e1
    | Olsr U32 => lower_shift SRLI SRL e0 e1
    | Oasr (Op_w U32) => lower_shift SRAI SRA e0 e1
    | _ =>
        let%lr (op, e1') :=
          if rv_expected_Imn_size op is Some ws then
            if is_wconst ws e1 is Some w then rv_Imn_of_op2 op w e1
            else rv_mn_of_op2 op e1
          else rv_mn_of_op2 op e1
        in
        li_simple (RV32 op) [:: e0; e1' ]
    end.

  Definition otbn_Iop_of_op2
    (op : sop2) (fg : bn_flag_group) : lresult (seq lval * otbn_op) :=
    match op with
    | Oadd (Op_w _) => issue (lnone_cmlz, BN_ADDI fg)
    | Osub (Op_w _) => issue (lnone_cmlz, BN_SUBI fg)
    | _ => skip
    end.

  Definition otbn_op_of_op2
    (op : sop2) (fg : bn_flag_group) : lresult (seq lval * otbn_op) :=
    let mk mn := BN_basic mn fg in
    match op with
    | Oadd (Op_w _) => issue (lnone_cmlz, mk BN_ADD)
    | Osub (Op_w _) => issue (lnone_cmlz, mk BN_SUB)
    | Oland _ => issue (lnone_mlz, mk BN_AND)
    | Olor _ => issue (lnone_mlz, mk BN_OR)
    | Olxor _ => issue (lnone_mlz, mk BN_XOR)
    | _ => skip
    end.

  Definition lower_Papp2_large
    (ws : wsize) (op : sop2) (e0 e1 : pexpr) : low_instr :=
    let%lr (lvs, op) :=
      if isSome (is_wconst ws e1) then otbn_Iop_of_op2 op FG0
      else otbn_op_of_op2 op FG0
    in
    li_issue lvs op [:: e0; e1 ].

  (* Lower an expression of the form [e0 <+> e1]. *)
  Definition lower_Papp2 (ws : wsize) (op : sop2) (e0 e1 : pexpr) : low_instr :=
    if ws == reg_size then lower_Papp2_small ws op e0 e1
    else if ws == xreg_size then lower_Papp2_large ws op e0 e1
    else Error (E.invalid_wsize ii).

  Definition lower_pexpr_aux (ws : wsize) (e : pexpr) : low_instr :=
    match e with
    | Pvar v => lower_Pvar ws v
    | Pget _ _ _ _ _ | Pload _ _ _ => lower_load ws e
    | Papp1 op e => lower_Papp1 ws op e
    | Papp2 op a b => lower_Papp2 ws op a b
    | _ => skip
    end.

  (* TODO_OTBN: This should be an extra_op without flag group and we issue
     [BN_SEL] once we know which flag group we need. *)
  Definition lower_Pif (ws : wsize) (econd e0 e1 : pexpr) : low_instr :=
    Let _ := chk_xreg_ws ii ws in
    li_simple (BN_SEL FG0) [:: e0; e1; econd ].

  Definition lower_pexpr (ws : wsize) (e : pexpr) : low_cmd :=
    if e is Pif (aword ws') econd e0 e1 then
      Let _ := assert (ws == ws') (E.invalid_wsize ii) in
      Let: (pre, econd') := lower_condition ii econd in
      with_pre pre (lower_Pif ws econd' e0 e1)
    else no_pre (lower_pexpr_aux ws e).

  Definition destruct_Lmem (e : pexpr) : option (var_i * wreg) :=
    match e with
    | Papp2 (Oadd _) (Pvar x) e' =>
        let%opt w := is_wconst reg_size e in Some (x.(gv), w)
    | Papp2 (Osub _) (Pvar x) e' =>
        let%opt w := is_wconst reg_size e in Some (x.(gv), w)
    | _ => None
    end.

  (* Try to match a memory access and return the base pointer and
     displacement (in bytes). *)
  Definition get_lval_memory_access (lv : lval) : option (var_i * wreg) :=
    match lv with
    | Lvar x => Some (x, 0%R)
    | Lmem _ _ _ e => destruct_Lmem e
    | Laset _ _ ws x e =>
        (* We need to check that the final displacement (in bytes) is in
           bounds. *)
        let%opt z := is_const e in
        Some (x, wrepr reg_size (z * wsize_size ws))
    | _ => None
    end.

  (* A 32-bit store becomes a [SW]; a 256-bit (wide) store becomes a
     [BN.SD]. *)
  Definition lower_store (ws : wsize) (e : pexpr) : low_instr :=
    if ws == reg_size then li_simple (RV32 SW) [:: e ]
    else if ws == xreg_size then li_simple BN_SD [:: e ]
    else Error (E.invalid_wsize ii).

  Definition chk_lower_store (ws : wsize) (lv : lval) : cexec unit :=
    if get_lval_memory_access lv is Some (_, wdisp) then
      if (ws <= reg_size)%CMP then chk_address_displacement ii wdisp
      else chk_bn_address_displacement ii wdisp
    else ok tt.

  Definition lower_cassgn_word (lv : lval) (ws : wsize) (e : pexpr) : low_cmd :=
    let%lr (pre, lvs, op, es) :=
      if is_lval_in_memory lv then
        Let _ := chk_lower_store ws lv in no_pre (lower_store ws e)
      else lower_pexpr ws e
    in
    issue (pre, lvs ++ [:: lv ], op, es).

End LOWER_ASSIGN.


Definition lowering_options := unit.

Let i_of_low_instr ii tag '(lvs, op, es) :=
  MkI ii (instr_of_copn_args tag (lvs, Oasm op, es)).

Let c_of_low_cmd ii tag '(pre, lvs, op, es) :=
  map (i_of_low_instr ii tag) (rcons pre (lvs, op, es)).

Fixpoint lower_i (i : instr) : cexec cmd :=
  let '(MkI ii ir) := i in
  match ir with
  | Cassgn lv tag ty e =>
      if is_word_type ty is Some ws then
        Let oargs := lower_cassgn_word ii lv ws e in
        ok (oapp (c_of_low_cmd ii tag) [:: i ] oargs)
      else ok [:: i ]

  | Copn lvs tag op es =>
      Let oargs := lower_copn ii lvs op es in
      ok [:: oapp (i_of_low_instr ii tag) i oargs ]

  | Cif e c1 c2  =>
      Let c1' := conc_mapM lower_i c1 in
      Let c2' := conc_mapM lower_i c2 in
      ok [:: MkI ii (Cif e c1' c2') ]

  | Cfor fi c =>
      Let c' := conc_mapM lower_i c in
      ok [:: MkI ii (Cfor fi c') ]

  | Cwhile a c0 e ii c1 =>
      Let c0' := conc_mapM lower_i c0 in
      Let c1' := conc_mapM lower_i c1 in
      ok [:: MkI ii (Cwhile a c0' e ii c1') ]

  | Cassert _
  | Csyscall _ _ _
  | Ccall _ _ _ => ok [:: i ]
  end.

End WITH_PARAMS.
