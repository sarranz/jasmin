From Coq Require Import Relations.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssralg.
From mathcomp Require Import word_ssrZ.

Require Import oseq.

Require Import
  arch_params_proof
  compiler_util
  expr
  fexpr
  fexpr_sem
  psem
  psem_facts
  sem_one_varmap.
Require Import
  linearization
  linearization_proof
  lowering
  stack_alloc_params_proof
  stack_zeroization_proof.
Require
  arch_sem.
Require Import
  arch_decl
  arch_extra
  asm_gen
  asm_gen_proof
  sem_params_of_arch_extra.
Require Import
  otbn_decl
  otbn_extra
  otbn_instr_decl
  otbn
  otbn_params_core_proof
  otbn_lower_addressing_proof
  otbn_lowering
  otbn_lowering_proof.
Require Export otbn_params.

Set SsrOldRewriteGoalsOrder.  (* change Set to Unset when porting the file, then remove the line when requiring MathComp >= 2.6 *)

Section Section.

Context
  {atoI  : arch_toIdent}
  {syscall_state : Type}
  {sc_sem : syscall_sem syscall_state}
  {call_conv : calling_convention}.

#[local] Existing Instance withsubword.
#[local] Existing Instance direct_c.

(* ------------------------------------------------------------------------ *)
(* Stack alloc hypotheses. *)

Section STACK_ALLOC.

Lemma otbn_mov_ofsP : mov_ofs_correct (ap_sap otbn_params).(sap_mov_ofs).
Proof.
  move=> P' ev s1 e w ofs pofs x tag mk ii ins s2 P'_globs.
  t_xrbindP=> ve ok_ve ok_w vofs ok_vofs ok_pofs.
  rewrite /sap_mov_ofs /= /mov_ofs.
  case: mk.
  (* MK_LEA: [LA] evaluates the address [add e ofs] to [w + pofs]. *)
  + move=> [<-] hw; exists (evm s2); last done.
    rewrite with_vm_same /sem_sopn /= P'_globs /exec_sopn /=.
    rewrite ok_ve ok_vofs /= /sem_sop2 /= ok_w ok_pofs /=.
    by rewrite truncate_word_u /= hw.
  (* MK_MOV. *)
  case: x => //.
  (* x = Lvar. *)
  - move=> x_.
    case: ifP => _.
    (* [e] is a load: copy it with [LW] (requires [ofs = 0]). *)
    + case: is_zeroP => // hz [<-] hw; exists (evm s2); last done.
      rewrite with_vm_same /sem_sopn /= P'_globs /exec_sopn /= ok_ve /= ok_w /=.
      move: hz ok_vofs ok_pofs hw => -> /=.
      rewrite /sem_sop1 /= => -[<-].
      rewrite /to_word /= truncate_word_u => -[<-].
      by rewrite wunsigned0 wrepr0 GRing.addr0 => ->.
    case: is_zeroP => [hz [<-] hw | hnz].
    (* [ofs = 0]: register move via the [MOV] extra op. *)
    + exists (evm s2); last done.
      rewrite with_vm_same /sem_sopn /= P'_globs /exec_sopn /= ok_ve /=.
      rewrite /sopn_sem /sopn_sem_ /= ok_w /=.
      move: hz ok_vofs ok_pofs hw => -> /=.
      rewrite /sem_sop1 /= => -[<-].
      rewrite /to_word /= truncate_word_u => -[<-].
      by rewrite wunsigned0 wrepr0 GRing.addr0 => ->.
    (* [ofs <> 0]: [ADDI] computes [wadd w pofs = w + pofs] directly. *)
    move=> [<-] hw; exists (evm s2); last done.
    rewrite with_vm_same /sem_sopn /= P'_globs /exec_sopn /= ok_ve ok_vofs /=.
    rewrite ok_w ok_pofs /=.
    by move: hw => /= ->.
  (* x = Lmem: store the word with [SW] (requires [ofs = 0]). *)
  move=> a ws_ vi p_.
  case: is_zeroP => // hz [<-] hw; exists (evm s2); last done.
  rewrite with_vm_same /sem_sopn /= P'_globs /exec_sopn /= ok_ve /= ok_w /=.
  move: hz ok_vofs ok_pofs hw => -> /=.
  rewrite /sem_sop1 /= => -[<-].
  rewrite /to_word /= truncate_word_u => -[<-].
  by rewrite wunsigned0 wrepr0 GRing.addr0 => ->.
Qed.

Lemma otbn_immediateP : immediate_correct (ap_sap otbn_params).(sap_immediate).
Proof.
  move=> P' ev s ii x z.
  case: x => - [] [] // [] // x xi _ /=.
  by rewrite /sem_sopn /= /exec_sopn /= truncate_word_u.
Qed.

Lemma otbn_swapP : swap_correct (ap_sap otbn_params).(sap_swap).
Proof.
  move=> P' ev s ii tag x y z w pz pw hxty hyty hzty hwty hz hw.
  rewrite /= /sem_sopn /= /get_gvar /= /get_var /= hz hw /=.
  rewrite /exec_sopn /= !truncate_word_u /= /write_var /set_var /=.
  by rewrite (convertible_eval_atype hxty) (convertible_eval_atype hyty).
Qed.

End STACK_ALLOC.

Definition otbn_hsaparams :
  h_stack_alloc_params (ap_sap otbn_params) :=
  {|
    mov_ofsP := otbn_mov_ofsP;
    sap_immediateP := otbn_immediateP;
    sap_swapP := otbn_swapP;
  |}.

(* ------------------------------------------------------------------------ *)
(* Bridge: OTBNFopn_coreP.sem_fopn_args <-> linear sem_fopn_args *)

Lemma otbn_sem_fopn_equiv (o : seq lexpr * otbn_op * seq rexpr) (s : estate) :
  OTBNFopn_coreP.sem_fopn_args o s =
  sem_fopn_args (fopn_args_of_opn_args o) s.
Proof.
  case: o => -[xs op] es /=.
  case: sem_rexprs => //= args.
  rewrite /exec_sopn /= /sopn_sem /=; case: id_valid => //=.
  rewrite /sopn_sem_ /= /semi_to_atype.
  move: (computational_eq _) (computational_eq _) => e1 e2.
  rewrite <- e1, <- e2. by case: app_sopn.
Qed.

Lemma otbn_sem_fopns_equiv s (lc : seq (seq lexpr * otbn_op * seq rexpr)) :
  OTBNFopn_coreP.sem_fopns_args s lc =
  sem_fopns_args s (map fopn_args_of_opn_args lc).
Proof.
  elim: lc s => //= o lc ih s.
  rewrite -otbn_sem_fopn_equiv.
  by case: OTBNFopn_coreP.sem_fopn_args.
Qed.

(* ------------------------------------------------------------------------ *)
(* Linearization hypotheses. *)

Section LINEARIZATION.

(* Helper: smart_subi_tmp correctness for allocate_stack_frame *)
Lemma otbn_smart_subi_tmp_sem_fopns (rspi tmp : var_i) (sz : Z) s (ts : wreg) :
  v_var rspi <> v_var tmp ->
  convertible (vtype rspi) (aword Uptr) ->
  convertible (vtype tmp) (aword Uptr) ->
  get_var true (evm s) (v_var rspi) >>= to_word Uptr = ok ts ->
  exists vm',
    [/\ sem_fopns_args s (map fopn_args_of_opn_args
          (odflt [:: otbn_params_core.OTBNFopn_core.subi rspi rspi sz]
            (otbn_params_core.OTBNFopn_core.smart_subi_tmp rspi tmp sz))) =
        ok (with_vm s vm')
      , evm s =[\ Sv.add rspi (Sv.singleton tmp)] vm'
      & vm'.[v_var rspi] = Vword (ts - wrepr Uptr sz) ].
Proof.
  move=> hne hrspi htmp hget.
  rewrite /otbn_params_core.OTBNFopn_core.smart_subi_tmp
          /otbn_params_core.OTBNFopn_core.gen_smart_opi_tmp
          /otbn_params_core.OTBNFopn_core.gen_smart_opi.
  have hneq : v_var rspi != v_var tmp by apply/eqP.
  rewrite hneq !orbT /= -otbn_sem_fopns_equiv.
  have hlc : otbn_params_core.OTBNFopn_core.gen_smart_opi
      otbn_params_core.OTBNFopn_core.sub
      otbn_params_core.OTBNFopn_core.subi
      otbn_params_core.is_arith_small_neg (Some 0%Z) tmp rspi rspi sz =
      Some (otbn_params_core.OTBNFopn_core.gen_unsafe_smart_opi
        otbn_params_core.OTBNFopn_core.sub
        otbn_params_core.OTBNFopn_core.subi
        otbn_params_core.is_arith_small_neg (Some 0%Z) tmp rspi rspi sz).
  { by rewrite /otbn_params_core.OTBNFopn_core.gen_smart_opi hneq !orbT. }
  have neutral_ok : forall (wr : word reg_size), (wr - wrepr reg_size 0%Z)%R = wr.
  { by move=> wr; rewrite wrepr0 GRing.subr0. }
  have [vm' [hsem heq hgetx]] :=
    OTBNFopn_coreP.gen_smart_opi_sem_fopn_args
      (op := fun (x y : word reg_size) => (x - y)%R)
      (on_reg := otbn_params_core.OTBNFopn_core.sub)
      (on_imm := otbn_params_core.OTBNFopn_core.subi)
      (is_small := otbn_params_core.is_arith_small_neg)
      (neutral := Some 0%Z)
      (fun s0 xi y wy z wz hc hgy hgz => OTBNFopn_coreP.sub_sem_fopn_args hc hgy hgz)
      (fun s0 xi y imm wy hc hgy => OTBNFopn_coreP.subi_sem_fopn_args hc hgy)
      neutral_ok htmp hrspi hlc hget.
  exists vm'; split => //.
  + by apply: eq_exS.
  + move: hgetx => /get_varP [-> _ _]; done.
Qed.
Arguments otbn_smart_subi_tmp_sem_fopns rspi tmp sz s ts _ _ _ _ : clear implicits.

(* Helper: smart_addi_tmp correctness for free_stack_frame *)
Lemma otbn_smart_addi_tmp_sem_fopns (rspi tmp : var_i) (sz : Z) s (ts : wreg) :
  v_var rspi <> v_var tmp ->
  convertible (vtype rspi) (aword Uptr) ->
  convertible (vtype tmp) (aword Uptr) ->
  get_var true (evm s) (v_var rspi) >>= to_word Uptr = ok ts ->
  exists vm',
    [/\ sem_fopns_args s (map fopn_args_of_opn_args
          (odflt [:: otbn_params_core.OTBNFopn_core.addi rspi rspi sz]
            (otbn_params_core.OTBNFopn_core.smart_addi_tmp rspi tmp sz))) =
        ok (with_vm s vm')
      , evm s =[\ Sv.add rspi (Sv.singleton tmp)] vm'
      & vm'.[v_var rspi] = Vword (ts + wrepr Uptr sz) ].
Proof.
  move=> hne hrspi htmp hget.
  rewrite /otbn_params_core.OTBNFopn_core.smart_addi_tmp
          /otbn_params_core.OTBNFopn_core.gen_smart_opi_tmp
          /otbn_params_core.OTBNFopn_core.gen_smart_opi.
  have hneq : v_var rspi != v_var tmp by apply/eqP.
  rewrite hneq !orbT /= -otbn_sem_fopns_equiv.
  have hlc : otbn_params_core.OTBNFopn_core.gen_smart_opi
      otbn_params_core.OTBNFopn_core.add
      otbn_params_core.OTBNFopn_core.addi
      otbn_params_core.is_arith_small (Some 0%Z) tmp rspi rspi sz =
      Some (otbn_params_core.OTBNFopn_core.gen_unsafe_smart_opi
        otbn_params_core.OTBNFopn_core.add
        otbn_params_core.OTBNFopn_core.addi
        otbn_params_core.is_arith_small (Some 0%Z) tmp rspi rspi sz).
  { by rewrite /otbn_params_core.OTBNFopn_core.gen_smart_opi hneq !orbT. }
  have neutral_ok : forall (wr : word reg_size), (wr + wrepr reg_size 0%Z)%R = wr.
  { by move=> wr; rewrite wrepr0 GRing.addr0. }
  have [vm' [hsem heq hgetx]] :=
    OTBNFopn_coreP.gen_smart_opi_sem_fopn_args
      (op := fun (x y : word reg_size) => (x + y)%R)
      (on_reg := otbn_params_core.OTBNFopn_core.add)
      (on_imm := otbn_params_core.OTBNFopn_core.addi)
      (is_small := otbn_params_core.is_arith_small)
      (neutral := Some 0%Z)
      (fun s0 xi y wy z wz hc hgy hgz => OTBNFopn_coreP.add_sem_fopn_args hc hgy hgz)
      (fun s0 xi y imm wy hc hgy => OTBNFopn_coreP.addi_sem_fopn_args hc hgy)
      neutral_ok htmp hrspi hlc hget.
  exists vm'; split => //.
  + by apply: eq_exS.
  + move: hgetx => /get_varP [-> _ _]; done.
Qed.
Arguments otbn_smart_addi_tmp_sem_fopns rspi tmp sz s ts _ _ _ _ : clear implicits.

(* Helper: smart_addi_fopn correctness for lstores/lloads *)
Lemma otbn_smart_addi_sem_fopns (xi : var_i) y imm s (w : wreg) :
  convertible xi.(vtype) (aword otbn_reg_size) ->
  otbn_params_core.is_arith_small imm \/ v_var xi <> v_var y ->
  get_var true (evm s) (v_var y) >>= to_word Uptr = ok w ->
  exists vm',
    [/\ sem_fopns_args s (smart_addi_fopn xi y imm) = ok (with_vm s vm')
      , vm' =[\ Sv.singleton xi ] evm s
      & get_var true vm' xi = ok (Vword (w + wrepr reg_size imm)%R) ].
Proof.
  move=> hc hor hget.
  rewrite /smart_addi_fopn /smart_addi
          /otbn_params_core.OTBNFopn_core.smart_addi
          /otbn_params_core.OTBNFopn_core.gen_smart_opi.
  have hcond : [|| (0 =? imm)%Z, otbn_params_core.is_arith_small imm
                 | v_var y != v_var xi].
  { case: hor => [h | h].
    + by rewrite h !orbT.
    + by apply/orP; right; apply/orP; right;
       apply/eqP => heq; exact (h (esym heq)). }
  rewrite hcond /= -otbn_sem_fopns_equiv.
  have hlc : otbn_params_core.OTBNFopn_core.gen_smart_opi
      otbn_params_core.OTBNFopn_core.add
      otbn_params_core.OTBNFopn_core.addi
      otbn_params_core.is_arith_small (Some 0%Z) xi xi y imm =
      Some (otbn_params_core.OTBNFopn_core.gen_unsafe_smart_opi
        otbn_params_core.OTBNFopn_core.add
        otbn_params_core.OTBNFopn_core.addi
        otbn_params_core.is_arith_small (Some 0%Z) xi xi y imm).
  { by rewrite /otbn_params_core.OTBNFopn_core.gen_smart_opi hcond. }
  have neutral_ok : forall (wr : word reg_size), (wr + wrepr reg_size 0%Z)%R = wr.
  { by move=> wr; rewrite wrepr0 GRing.addr0. }
  have [vm' [hsem heq hgetx]] :=
    OTBNFopn_coreP.gen_smart_opi_sem_fopn_args
      (op := fun (x y : word reg_size) => (x + y)%R)
      (on_reg := otbn_params_core.OTBNFopn_core.add)
      (on_imm := otbn_params_core.OTBNFopn_core.addi)
      (is_small := otbn_params_core.is_arith_small)
      (neutral := Some 0%Z)
      (fun s0 xi0 y0 wy0 z0 wz0 hc0 hgy0 hgz0 =>
         OTBNFopn_coreP.add_sem_fopn_args hc0 hgy0 hgz0)
      (fun s0 xi0 y0 imm0 wy0 hc0 hgy0 =>
         OTBNFopn_coreP.addi_sem_fopn_args hc0 hgy0)
      neutral_ok hc hc hlc hget.
  exists vm'; split => //.
  by apply: eq_exI heq; SvD.fsetdec.
Qed.
Arguments otbn_smart_addi_sem_fopns xi y imm s w _ _ _ : clear implicits.

Lemma otbn_spec_lip_allocate_stack_frame :
  allocate_stack_frame_correct (ap_lip otbn_params).
Proof.
  move=> sp_rsp tmp s ts sz htmp hget /=.
  rewrite /lip_allocate_stack_frame /= /allocate_stack_frame /=.
  case: tmp htmp => [tmp [h1 h2] | _] /=.
  (* Some tmp: use smart_subi_tmp *)
  + have [vm' [-> heq hgetx]] :=
      otbn_smart_subi_tmp_sem_fopns
        (mk_var_i {| vtype := aword U32; vname := sp_rsp |})
        tmp sz s ts h1 erefl h2 (to_word_get_var hget).
    by exists vm'; split => //.
  (* None: direct subi *)
  + have hget2 : get_var true (evm s) {| vtype := aword U32; vname := sp_rsp |} =
        ok (Vword (s:=U32) ts).
    { move: hget; exact. }
    rewrite hget2 /= /exec_sopn /= !truncate_word_u /=.
    eexists; split.
    + reflexivity.
    + move=> z hz; rewrite Vm.setP_neq //; apply/eqP; SvD.fsetdec.
    + by rewrite Vm.setP_eq /= /wadd wrepr_opp.
Qed.

Lemma otbn_spec_lip_free_stack_frame :
  free_stack_frame_correct (ap_lip otbn_params).
Proof.
  move=> sp_rsp tmp s ts sz htmp hget /=.
  rewrite /lip_free_stack_frame /= /free_stack_frame /=.
  case: tmp htmp => [tmp [h1 h2] | _] /=.
  (* Some tmp: use smart_addi_tmp *)
  + have [vm' [-> heq hgetx]] :=
      otbn_smart_addi_tmp_sem_fopns
        (mk_var_i {| vtype := aword U32; vname := sp_rsp |})
        tmp sz s ts h1 erefl h2 (to_word_get_var hget).
    by exists vm'; split => //.
  (* None: direct addi *)
  + have hget2 : get_var true (evm s) {| vtype := aword U32; vname := sp_rsp |} =
        ok (Vword (s:=U32) ts).
    { move: hget; exact. }
    rewrite hget2 /= /exec_sopn /= !truncate_word_u /=.
    eexists; split.
    + reflexivity.
    + move=> z hz; rewrite Vm.setP_neq //; apply/eqP; SvD.fsetdec.
    + by rewrite Vm.setP_eq /=.
Qed.

Lemma otbn_spec_lip_set_up_sp_register :
  set_up_sp_register_correct (ap_lip otbn_params).
Proof. Admitted.

Lemma otbn_lmove_correct : lmove_correct (ap_lip otbn_params).
Proof.
  move=> xd xs w ws w' s htxd htxs hget htr.
  rewrite /lip_lmove /= /lmove /fopn_args_of_opn_args /= hget /=.
  rewrite /exec_sopn /= htr /=.
  rewrite truncate_word_u /=.
  rewrite /wadd wrepr0 GRing.addr0 set_var_eq_type ?htxd //.
Qed.

Lemma otbn_lstore_correct :
  lstore_correct_aux (lip_check_ws (ap_lip otbn_params))
                     (lip_lstore (ap_lip otbn_params)).
Proof.
  move=> xd xs ofs ws w wp s m htxs /eqP hchk; t_xrbindP; subst ws.
  move=> vd hgetd htrd vs hgets htrs hwr.
  rewrite /lip_lstore /= /lstore /fopn_args_of_opn_args /= hgets hgetd /=
          /exec_sopn /= htrs /=.
  rewrite /sem_sop2 /= htrd /= !truncate_word_u /=.
  rewrite truncate_word_u /= add_wordE hwr //.
Qed.

Lemma otbn_lload_correct :
  lload_correct_aux (lip_check_ws (ap_lip otbn_params))
                    (lip_lload (ap_lip otbn_params)).
Proof.
  move=> xd xs ofs ws top s w vm heq hcheck.
  t_xrbindP => ? hgets hto hread hset.
  move/eqP: hcheck => ?; subst ws.
  rewrite /lip_lload /= /lload /fopn_args_of_opn_args /= hgets /=.
  rewrite /sem_sop2 /= hto /= !truncate_word_u /= add_wordE.
  rewrite truncate_word_u /= hread /= /exec_sopn /= truncate_word_u /= hset //.
Qed.

Lemma otbn_smart_addi_correct : ladd_imm_correct_aux smart_addi_fopn.
Proof.
  move=> [[_ xn] xii] x2 s w ofs /= -> hne hget.
  apply: otbn_smart_addi_sem_fopns hget => //.
  by right => h; exact (hne h).
Qed.

Lemma otbn_lstores_correct : lstores_correct (ap_lip otbn_params).
Proof.
  apply/lstores_imm_dfl_correct.
  + by apply otbn_lstore_correct.
  apply otbn_smart_addi_correct.
Qed.

Lemma otbn_lloads_correct : lloads_correct (ap_lip otbn_params).
Proof.
  apply/lloads_imm_dfl_correct.
  + by apply otbn_lload_correct.
  apply otbn_smart_addi_correct.
Qed.

Lemma otbn_tmp_correct :
  lip_tmp (ap_lip otbn_params) <> lip_tmp2 (ap_lip otbn_params).
Proof. by move=> h; assert (h1 := inj_to_ident h). Qed.

Lemma otbn_check_ws_correct : lip_check_ws (ap_lip otbn_params) Uptr.
Proof. done. Qed.

End LINEARIZATION.

Definition otbn_hliparams :
  h_linearization_params (ap_lip otbn_params) :=
  {|
    spec_lip_allocate_stack_frame := otbn_spec_lip_allocate_stack_frame;
    spec_lip_free_stack_frame     := otbn_spec_lip_free_stack_frame;
    spec_lip_set_up_sp_register   := otbn_spec_lip_set_up_sp_register;
    spec_lip_lmove                := otbn_lmove_correct;
    spec_lip_lstore               := otbn_lstore_correct;
    spec_lip_lload                := otbn_lload_correct;
    spec_lip_lstores              := otbn_lstores_correct;
    spec_lip_lloads               := otbn_lloads_correct;
    spec_lip_tmp                  := otbn_tmp_correct;
    spec_lip_check_ws             := otbn_check_ws_correct;
  |}.

Lemma otbn_ok_lip_tmp :
  exists r : reg_t, of_ident (lip_tmp (ap_lip otbn_params)) = Some r.
Proof. exists X28; exact: to_identK. Qed.

Lemma otbn_ok_lip_tmp2 :
  exists r : reg_t, of_ident (lip_tmp2 (ap_lip otbn_params)) = Some r.
Proof. exists X29; exact: to_identK. Qed.

(* ------------------------------------------------------------------------ *)
(* Lowering hypotheses. *)

Definition otbn_hloparams : h_lowering_params (ap_lop otbn_params).
Proof.
  split=> *;
    [ by apply: lower_callP; eassumption
    | by apply: it_lower_callP; eassumption ].
Qed.

(* -------------------------------------------------------------------------- *)
(* Lowering of complex addressing mode (identity for OTBN). *)

Lemma otbn_hlaparams : h_lower_addressing_params (ap_lap otbn_params).
Proof.
  split=> /=.
  + exact: lower_addressing_prog_invariants.
  + exact: lower_addressing_fd_invariants.
  + exact: lower_addressing_progP.
  by move=> > /it_lower_addressing_progP.
Qed.

(* -------------------------------------------------------------------------- *)
(* Assembly generation hypotheses. *)

Section ASM_GEN.

Lemma otbn_eval_assemble_cond : assemble_cond_spec (ap_agp otbn_params).
Proof.
  move=> ii m rr rf e c v eqr eqf.
  elim: e c v => [| x | op1 e hind | op2 e0 hind0 e1 hind1 |] //= c v.
  (* [Fvar x] is a flag read, assembled as [BNcond f]. *)
  - t_xrbindP=> f hf ?; subst c; move=> hv.
    rewrite /eval_cond /= get_rf_to_bool_of_rbool value_of_bool_to_bool_of_rbool.
    eexists; first reflexivity.
    exact: (xgetflag_ex eqf hf hv).
  (* [Fapp1 Onot e]: the inner condition must be an [RVcond], which we negate. *)
  - case: op1 => //=.
    t_xrbindP=> c0 ok_c0 hcn ve ok_ve hsop1.
    have [v1 hev huincl] := hind _ _ ok_c0 ok_ve.
    move: hsop1 => /sem_sop1I /= [b [bb] [hb [?] ?]]; subst v bb.
    have hc := value_uincl_to_bool_value_of_bool huincl hb hev.
    have -> : eval_cond rr (get_rf rf) c = ok (~~ b).
    { move: hcn hc; clear ok_c0 hev; case: c0 => [is_eq r0 r1 | f] //=.
      by move=> [<-] [<-]; case: is_eq => /=; rewrite ?negbK. }
    by eexists.
  (* [Fapp2 o e0 e1]: a register comparison, assembled as [RVcond]. *)
  rewrite /assemble_cond_app2.
  t_xrbindP=> is_eq hokeq r0 hr0 r1 hr1 ?; subst c.
  t_xrbindP=> v0 ok_v0 w ok_w ok_v.
  (* Each operand evaluates to (a word uincl to) [sem_cond_arg rr ri]. *)
  have hargP : forall (ea : fexpr) (ora : option register) (va : value),
    oreg_of_fexpr ii (Fapp2 op2 e0 e1) ea = ok ora ->
    sem_fexpr (evm m) ea = ok va ->
    value_uincl va (Vword (riscv.sem_cond_arg rr ora)).
  - move=> ea ora va; rewrite /oreg_of_fexpr; case: ifP => [hz | hnz].
    + move=> [<-]; move: hz; rewrite /is_fzero; case: ea => //= op a.
      by case: op => //= ws'; case: a => //= z; case: z => //=
        /eqP ->{ws'} /= [<-]; exact: value_uincl_refl.
    + rewrite /is_fvar; move: hnz; case: ea => //= x _.
      t_xrbindP=> r hr ?; subst ora.
      move=> /get_varP [-> _ _] /=.
      by rewrite -(of_var_eI hr); apply: eqr.
  have hincl0 := hargP _ _ _ hr0 ok_v0.
  have hincl1 := hargP _ _ _ hr1 ok_w.
  rewrite /eval_cond /=.
  move: hokeq ok_v; clear hr0 hr1 hargP; case: op2 => //=.
  (* [Oeq]: [is_eq = true]. *)
  - case=> //= ws; rewrite /assert; case: eqP => //= ?; subst ws => -[<-].
    rewrite /sem_sop2 /=.
    t_xrbindP=> x0 hx0 x1 hx1 <-.
    move/to_wordI': hx0 => [sz0 [w0' [hle0 ? ?]]]; subst v0 x0.
    move/to_wordI': hx1 => [sz1 [w1' [hle1 ? ?]]]; subst w x1.
    move: hincl0 hincl1; rewrite /= /word_uincl => /andP[_ /eqP ->] /andP[_ /eqP ->].
    by eexists; first reflexivity; rewrite !(zero_extend_idem, zero_extend_u).
  (* [Oneq]: [is_eq = false]. *)
  case=> //= ws; rewrite /assert; case: eqP => //= ?; subst ws => -[<-].
  rewrite /sem_sop2 /=.
  t_xrbindP=> x0 hx0 x1 hx1 <-.
  move/to_wordI': hx0 => [sz0 [w0' [hle0 ? ?]]]; subst v0 x0.
  move/to_wordI': hx1 => [sz1 [w1' [hle1 ? ?]]]; subst w x1.
  move: hincl0 hincl1; rewrite /= /word_uincl => /andP[_ /eqP ->] /andP[_ /eqP ->].
  by eexists; first reflexivity; rewrite !(zero_extend_idem, zero_extend_u).
Qed.

Lemma otbn_assemble_extra_op op :
  assemble_extra_correct (ap_agp otbn_params) op.
Proof. Admitted.

Lemma otbn_assemble_extra_sz ii op lvs args ops :
  to_asm ii op lvs args = ok ops -> ssrnat.leq 1 (size ops).
Proof. Admitted.

Definition otbn_hagparams : h_asm_gen_params (ap_agp otbn_params) :=
  {|
    hagp_eval_assemble_cond := otbn_eval_assemble_cond;
    hagp_assemble_extra_op := otbn_assemble_extra_op;
    hagp_assemble_extra_sz := otbn_assemble_extra_sz;
  |}.

End ASM_GEN.

(* ------------------------------------------------------------------------ *)
(* SLH. *)

Lemma otbn_hshp : slh_lowering_proof.h_sh_params (ap_shp otbn_params).
Proof. by constructor; move=> ???? []. Qed.

(* ------------------------------------------------------------------------ *)
(* Stack zeroization. *)

Lemma otbn_hszparams :
  stack_zeroization_proof.h_stack_zeroization_params (ap_szp otbn_params).
Proof. by split. Qed.

(* ------------------------------------------------------------------------ *)
(* Shared hypotheses. *)

Lemma otbn_is_move_opP op vx v :
  ap_is_move_op otbn_params op ->
  exec_sopn (Oasm op) [:: vx ] = ok v ->
  List.Forall2 value_uincl v [:: vx ].
Proof.
  case: op => [[msb o] | eo] /=.
  - case: msb => //; case: o => // _.
    rewrite /exec_sopn /sopn_sem /sopn_sem_ /=.
    t_xrbindP=> wx hwx hto [<-] <-.
    constructor=> //.
    move/to_wordI: hto => [ws [w0 [-> htr]]].
    exact: (truncate_word_uincl htr).
  case: eo => // _.
  rewrite /exec_sopn /sopn_sem /sopn_sem_ /=.
  t_xrbindP=> wx hwx hto <- <-.
  constructor=> //.
  move/to_wordI: hto => [ws [w0 [-> htr]]].
  exact: (truncate_word_uincl htr).
Qed.

(* ------------------------------------------------------------------------ *)

Definition otbn_h_params {dc : DirectCall} : h_architecture_params otbn_params :=
  {|
    hap_hsap        := otbn_hsaparams;
    hap_hlip        := otbn_hliparams;
    ok_lip_tmp      := otbn_ok_lip_tmp;
    ok_lip_tmp2     := otbn_ok_lip_tmp2;
    hap_hlop        := otbn_hloparams;
    hap_hlap        := otbn_hlaparams;
    hap_hagp        := otbn_hagparams;
    hap_hshp        := otbn_hshp;
    hap_hszp        := otbn_hszparams;
    hap_is_move_opP := otbn_is_move_opP;
  |}.

End Section.
