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
  lea_proof
  psem
  psem_facts
  sem_one_varmap.
Require Import
  linearization
  it_linearization_proof
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
  acc_decl
  acc_extra
  acc_instr_decl
  acc
  acc_params_core_proof
  acc_lower_addressing_proof
  acc_lowering
  acc_lowering_proof
  acc_stack_zeroization
  acc_stack_zeroization_proof.
Require Export acc_params.

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

(* [add_imm_op] emits [MOV]/[ADDI]/[ADD_LARGE_IMM] depending on [imm]; in
   every case, the result is [base + imm]. *)
Lemma add_imm_opP
  (P' : sprog) (tag : assgn_tag) (x : lval) (base : var_i)
  (imm : Z) (s1 : estate) (vb : value) (wb : word U32) :
  p_globs P' = [::] ->
  get_var true (evm s1) base = ok vb ->
  to_word U32 vb = ok wb ->
  sem_sopn (p_globs P') (Oasm (add_imm_op base imm).1) s1 [:: x] (add_imm_op base imm).2
  = write_lval true (p_globs P') x (Vword (wadd wb (wrepr U32 imm))) s1.
Proof.
  move=> P'_globs ok_vb ok_wb.
  rewrite /add_imm_op.
  case: eqP => [heq|hneq].
  - subst imm.
    rewrite /sem_sopn P'_globs /= /get_gvar /= ok_vb /= /exec_sopn /= ok_wb /=.
    rewrite /wadd wrepr0 GRing.addr0.
    by case: (write_lval true [::] x (Vword wb) s1).
  case: ifP => hsmall.
  - rewrite /sem_sopn P'_globs /= /get_gvar /= ok_vb /= /exec_sopn /= ok_wb
      truncate_word_u /=.
    by case: (write_lval true [::] x (Vword (wadd wb (wrepr U32 imm)))).
  rewrite /sem_sopn P'_globs /= /get_gvar /= ok_vb /= /exec_sopn /= ok_wb
    truncate_word_u /=.
  by case: (write_lval true [::] x (Vword (wadd wb (wrepr U32 imm)))).
Qed.

Lemma acc_mov_ofsP : mov_ofs_correct (ap_sap acc_params).(sap_mov_ofs).
Proof.
  move=> P' ev s1 e w ofs pofs x tag mk ii ins s2 P'_globs.
  t_xrbindP=> ve ok_ve ok_w vofs ok_vofs ok_pofs.
  rewrite /sap_mov_ofs /= /mov_ofs.
  case: mk.
  (* MK_LEA. *)
  + move=> [<-] hw; exists (evm s2) => //.
    rewrite with_vm_same /sem_sopn /= P'_globs /exec_sopn.
    case: is_zeroP.
    - move=> hofs.
      rewrite ok_ve /= ok_w /=.
      move: hofs ok_vofs ok_pofs hw => -> /=.
      rewrite /sem_sop1 /= => -[<-] /=.
      rewrite truncate_word_u wrepr0 => -[<-].
      by rewrite GRing.addr0 => -> /=.
    move=> _ /=.
    rewrite ok_ve ok_vofs /= /sem_sop2 /= ok_w ok_pofs /= truncate_word_u /=.
    by rewrite hw.
  (* MK_MOV. *)
  case: x => //.
  (* x = Lvar. *)
  - move=> x_.
    case: ifP => _.
    (* [e] is a load: copy it with [LW] (requires [ofs = 0]). *)
    + move=> /oassertP [/is_zeroP hz [<-]] hw; exists (evm s2); last done.
      rewrite with_vm_same /sem_sopn /= P'_globs /exec_sopn /= ok_ve /= ok_w /=.
      move: hz ok_vofs ok_pofs hw => -> /=.
      rewrite /sem_sop1 /= => -[<-].
      rewrite /to_word /= truncate_word_u => -[<-].
      by rewrite wunsigned0 wrepr0 GRing.addr0 => ->.
    (* [mk_lea] on [e + ofs]: dispatch on [lea_base]/[lea_offset]. *)
    case hlea: mk_lea => [[disp base0 scale offset]|] //=.
    case: base0 hlea => [base|//] hlea.
    have lea_sem: sem_pexpr true [::] s1 (add e ofs) = ok (Vword (w + pofs)).
    - by rewrite /= ok_ve ok_vofs /= /sem_sop2 /= ok_w ok_pofs /=.
    have /(_ (cmp_le_refl _)) /(_ (cmp_le_refl _)) := mk_leaP _ _ hlea lea_sem.
    rewrite zero_extend_u /sem_lea /=.
    apply: rbindP => wb.
    apply: rbindP => vb ok_vb ok_wb.
    apply: rbindP => wo ok_wo.
    move=> /ok_inj; rewrite GRing.addrC => {}lea_sem.
    case: offset {hlea} ok_wo => [offset0|] /=.
    (* [lea_offset = Some _]: [ADD base offset], requires [disp = 0] and
       [scale = 1]. *)
    + t_xrbindP=> vo ok_vo ok_wo.
      move=> /oassertP [/andP [/eqP hdisp /eqP hscale] [<-]] hw.
      subst disp; subst scale.
      exists (evm s2) => //.
      rewrite /sem_sopn P'_globs /= /get_gvar /= ok_vb ok_vo /=
        /exec_sopn /= ok_wb ok_wo /=.
      move: lea_sem; rewrite wrepr1 GRing.mul1r wrepr0 GRing.addr0 /wadd => ->.
      by rewrite hw /= with_vm_same.
    (* [lea_offset = None]: [add_imm_op base disp] computes [base + disp]
       (as [MOV], [ADDI] or the [ADD_LARGE_IMM] extra op; see
       [add_imm_opP]). *)
    move=> [?]; subst wo.
    move=> [<-] hw.
    exists (evm s2) => //.
    rewrite (add_imm_opP tag (Lvar x_) disp P'_globs ok_vb ok_wb).
    move: lea_sem; rewrite GRing.mulr0 GRing.addr0 /wadd => ->.
    rewrite /=.
    by rewrite hw /= with_vm_same.
  (* x = Lmem: store the word with [SW] (requires [ofs = 0]). *)
  move=> a ws_ vi p_ /oassertP [/is_zeroP hz [<-]] hw; exists (evm s2); last done.
  rewrite with_vm_same /sem_sopn /= P'_globs /exec_sopn /= ok_ve /= ok_w /=.
  move: hz ok_vofs ok_pofs hw => -> /=.
  rewrite /sem_sop1 /= => -[<-].
  rewrite /to_word /= truncate_word_u => -[<-].
  by rewrite wunsigned0 wrepr0 GRing.addr0 => ->.
Qed.

Lemma acc_immediateP : immediate_correct (ap_sap acc_params).(sap_immediate).
Proof.
  move=> P' ev s ii x z.
  case: x => - [] [] // [] // x xi _ /=.
  by rewrite /sem_sopn /= /exec_sopn /= truncate_word_u.
Qed.

Lemma acc_swapP : swap_correct (ap_sap acc_params).(sap_swap).
Proof.
  move=> P' ev s ii tag x y z w pz pw hxty hyty hzty hwty hz hw.
  rewrite /= /sem_sopn /= /get_gvar /= /get_var /= hz hw /=.
  rewrite /exec_sopn /= !truncate_word_u /= /write_var /set_var /=.
  by rewrite (convertible_eval_atype hxty) (convertible_eval_atype hyty).
Qed.

End STACK_ALLOC.

Definition acc_hsaparams :
  h_stack_alloc_params (ap_sap acc_params) :=
  {|
    mov_ofsP := acc_mov_ofsP;
    sap_immediateP := acc_immediateP;
    sap_swapP := acc_swapP;
  |}.

(* ------------------------------------------------------------------------ *)
(* Bridge: ACCFopn_coreP.sem_fopn_args <-> linear sem_fopn_args *)

Lemma acc_sem_fopn_equiv (o : seq lexpr * acc_op * seq rexpr) (s : estate) :
  ACCFopn_coreP.sem_fopn_args o s =
  sem_fopn_args (fopn_args_of_opn_args o) s.
Proof.
  case: o => -[xs op] es /=.
  case: sem_rexprs => //= args.
  rewrite /exec_sopn /= /sopn_sem /=; case: id_valid => //=.
  rewrite /sopn_sem_ /= /semi_to_atype.
  move: (computational_eq _) (computational_eq _) => e1 e2.
  rewrite <- e1, <- e2. by case: app_sopn.
Qed.

Lemma acc_sem_fopns_equiv s (lc : seq (seq lexpr * acc_op * seq rexpr)) :
  ACCFopn_coreP.sem_fopns_args s lc =
  sem_fopns_args s (map fopn_args_of_opn_args lc).
Proof.
  elim: lc s => //= o lc ih s.
  rewrite -acc_sem_fopn_equiv.
  by case: ACCFopn_coreP.sem_fopn_args.
Qed.

(* ------------------------------------------------------------------------ *)
(* Linearization hypotheses. *)

Section LINEARIZATION.

(* Helper: smart_subi_tmp correctness for allocate_stack_frame *)
Lemma acc_smart_subi_tmp_sem_fopns (rspi tmp : var_i) (sz : Z) s (ts : wreg) :
  v_var rspi <> v_var tmp ->
  convertible (vtype rspi) (aword Uptr) ->
  convertible (vtype tmp) (aword Uptr) ->
  get_var true (evm s) (v_var rspi) >>= to_word Uptr = ok ts ->
  exists vm',
    [/\ sem_fopns_args s (map fopn_args_of_opn_args
          (odflt [:: acc_params_core.ACCFopn_core.subi rspi rspi sz]
            (acc_params_core.ACCFopn_core.smart_subi_tmp rspi tmp sz))) =
        ok (with_vm s vm')
      , evm s =[\ Sv.add rspi (Sv.singleton tmp)] vm'
      & vm'.[v_var rspi] = Vword (ts - wrepr Uptr sz) ].
Proof.
  move=> hne hrspi htmp hget.
  rewrite /acc_params_core.ACCFopn_core.smart_subi_tmp
          /acc_params_core.ACCFopn_core.gen_smart_opi_tmp
          /acc_params_core.ACCFopn_core.gen_smart_opi.
  have hneq : v_var rspi != v_var tmp by apply/eqP.
  rewrite hneq !orbT /= -acc_sem_fopns_equiv.
  have hlc : acc_params_core.ACCFopn_core.gen_smart_opi
      acc_params_core.ACCFopn_core.sub
      acc_params_core.ACCFopn_core.subi
      acc_params_core.is_arith_small_neg (Some 0%Z) tmp rspi rspi sz =
      Some (acc_params_core.ACCFopn_core.gen_unsafe_smart_opi
        acc_params_core.ACCFopn_core.sub
        acc_params_core.ACCFopn_core.subi
        acc_params_core.is_arith_small_neg (Some 0%Z) tmp rspi rspi sz).
  { by rewrite /acc_params_core.ACCFopn_core.gen_smart_opi hneq !orbT. }
  have neutral_ok : forall (wr : word reg_size), (wr - wrepr reg_size 0%Z)%R = wr.
  { by move=> wr; rewrite wrepr0 GRing.subr0. }
  have [vm' [hsem heq hgetx]] :=
    ACCFopn_coreP.gen_smart_opi_sem_fopn_args
      (op := fun (x y : word reg_size) => (x - y)%R)
      (on_reg := acc_params_core.ACCFopn_core.sub)
      (on_imm := acc_params_core.ACCFopn_core.subi)
      (is_small := acc_params_core.is_arith_small_neg)
      (neutral := Some 0%Z)
      (fun s0 xi y wy z wz hc hgy hgz => ACCFopn_coreP.sub_sem_fopn_args hc hgy hgz)
      (fun s0 xi y imm wy hc hgy => ACCFopn_coreP.subi_sem_fopn_args hc hgy)
      neutral_ok htmp hrspi hlc hget.
  exists vm'; split => //.
  + by apply: eq_exS.
  + move: hgetx => /get_varP [-> _ _]; done.
Qed.
Arguments acc_smart_subi_tmp_sem_fopns rspi tmp sz s ts _ _ _ _ : clear implicits.

(* Helper: smart_addi_tmp correctness for free_stack_frame *)
Lemma acc_smart_addi_tmp_sem_fopns (rspi tmp : var_i) (sz : Z) s (ts : wreg) :
  v_var rspi <> v_var tmp ->
  convertible (vtype rspi) (aword Uptr) ->
  convertible (vtype tmp) (aword Uptr) ->
  get_var true (evm s) (v_var rspi) >>= to_word Uptr = ok ts ->
  exists vm',
    [/\ sem_fopns_args s (map fopn_args_of_opn_args
          (odflt [:: acc_params_core.ACCFopn_core.addi rspi rspi sz]
            (acc_params_core.ACCFopn_core.smart_addi_tmp rspi tmp sz))) =
        ok (with_vm s vm')
      , evm s =[\ Sv.add rspi (Sv.singleton tmp)] vm'
      & vm'.[v_var rspi] = Vword (ts + wrepr Uptr sz) ].
Proof.
  move=> hne hrspi htmp hget.
  rewrite /acc_params_core.ACCFopn_core.smart_addi_tmp
          /acc_params_core.ACCFopn_core.gen_smart_opi_tmp
          /acc_params_core.ACCFopn_core.gen_smart_opi.
  have hneq : v_var rspi != v_var tmp by apply/eqP.
  rewrite hneq !orbT /= -acc_sem_fopns_equiv.
  have hlc : acc_params_core.ACCFopn_core.gen_smart_opi
      acc_params_core.ACCFopn_core.add
      acc_params_core.ACCFopn_core.addi
      acc_params_core.is_arith_small (Some 0%Z) tmp rspi rspi sz =
      Some (acc_params_core.ACCFopn_core.gen_unsafe_smart_opi
        acc_params_core.ACCFopn_core.add
        acc_params_core.ACCFopn_core.addi
        acc_params_core.is_arith_small (Some 0%Z) tmp rspi rspi sz).
  { by rewrite /acc_params_core.ACCFopn_core.gen_smart_opi hneq !orbT. }
  have neutral_ok : forall (wr : word reg_size), (wr + wrepr reg_size 0%Z)%R = wr.
  { by move=> wr; rewrite wrepr0 GRing.addr0. }
  have [vm' [hsem heq hgetx]] :=
    ACCFopn_coreP.gen_smart_opi_sem_fopn_args
      (op := fun (x y : word reg_size) => (x + y)%R)
      (on_reg := acc_params_core.ACCFopn_core.add)
      (on_imm := acc_params_core.ACCFopn_core.addi)
      (is_small := acc_params_core.is_arith_small)
      (neutral := Some 0%Z)
      (fun s0 xi y wy z wz hc hgy hgz => ACCFopn_coreP.add_sem_fopn_args hc hgy hgz)
      (fun s0 xi y imm wy hc hgy => ACCFopn_coreP.addi_sem_fopn_args hc hgy)
      neutral_ok htmp hrspi hlc hget.
  exists vm'; split => //.
  + by apply: eq_exS.
  + move: hgetx => /get_varP [-> _ _]; done.
Qed.
Arguments acc_smart_addi_tmp_sem_fopns rspi tmp sz s ts _ _ _ _ : clear implicits.

(* Helper: smart_addi_fopn correctness for lstores/lloads *)
Lemma acc_smart_addi_sem_fopns (xi : var_i) y imm s (w : wreg) :
  convertible xi.(vtype) (aword acc_reg_size) ->
  acc_params_core.is_arith_small imm \/ v_var xi <> v_var y ->
  get_var true (evm s) (v_var y) >>= to_word Uptr = ok w ->
  exists vm',
    [/\ sem_fopns_args s (smart_addi_fopn xi y imm) = ok (with_vm s vm')
      , vm' =[\ Sv.singleton xi ] evm s
      & get_var true vm' xi = ok (Vword (w + wrepr reg_size imm)%R) ].
Proof using atoI call_conv sc_sem syscall_state.
  move=> hc hor hget.
  rewrite /smart_addi_fopn /smart_addi
          /acc_params_core.ACCFopn_core.smart_addi
          /acc_params_core.ACCFopn_core.gen_smart_opi.
  have hcond : [|| (0 =? imm)%Z, acc_params_core.is_arith_small imm
                 | v_var y != v_var xi].
  { case: hor => [h | h].
    + by rewrite h !orbT.
    + by apply/orP; right; apply/orP; right;
       apply/eqP => heq; exact (h (esym heq)). }
  rewrite hcond /= -acc_sem_fopns_equiv.
  have hlc : acc_params_core.ACCFopn_core.gen_smart_opi
      acc_params_core.ACCFopn_core.add
      acc_params_core.ACCFopn_core.addi
      acc_params_core.is_arith_small (Some 0%Z) xi xi y imm =
      Some (acc_params_core.ACCFopn_core.gen_unsafe_smart_opi
        acc_params_core.ACCFopn_core.add
        acc_params_core.ACCFopn_core.addi
        acc_params_core.is_arith_small (Some 0%Z) xi xi y imm).
  { by rewrite /acc_params_core.ACCFopn_core.gen_smart_opi hcond. }
  have neutral_ok : forall (wr : word reg_size), (wr + wrepr reg_size 0%Z)%R = wr.
  { by move=> wr; rewrite wrepr0 GRing.addr0. }
  have [vm' [hsem heq hgetx]] :=
    ACCFopn_coreP.gen_smart_opi_sem_fopn_args
      (op := fun (x y : word reg_size) => (x + y)%R)
      (on_reg := acc_params_core.ACCFopn_core.add)
      (on_imm := acc_params_core.ACCFopn_core.addi)
      (is_small := acc_params_core.is_arith_small)
      (neutral := Some 0%Z)
      (fun s0 xi0 y0 wy0 z0 wz0 hc0 hgy0 hgz0 =>
         ACCFopn_coreP.add_sem_fopn_args hc0 hgy0 hgz0)
      (fun s0 xi0 y0 imm0 wy0 hc0 hgy0 =>
         ACCFopn_coreP.addi_sem_fopn_args hc0 hgy0)
      neutral_ok hc hc hlc hget.
  exists vm'; split => //.
  by apply: eq_exI heq; SvD.fsetdec.
Qed.
Arguments acc_smart_addi_sem_fopns xi y imm s w _ _ _ : clear implicits.

Lemma acc_spec_lip_allocate_stack_frame :
  allocate_stack_frame_correct (ap_lip acc_params).
Proof using atoI call_conv sc_sem syscall_state.
  move=> sp_rsp tmp s ts sz htmp hget /=.
  rewrite /lip_allocate_stack_frame /= /allocate_stack_frame /=.
  case: tmp htmp => [tmp [h1 h2] | _] /=.
  (* Some tmp: use smart_subi_tmp *)
  + have [vm' [-> heq hgetx]] :=
      acc_smart_subi_tmp_sem_fopns
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

Lemma acc_spec_lip_free_stack_frame :
  free_stack_frame_correct (ap_lip acc_params).
Proof using atoI call_conv sc_sem syscall_state.
  move=> sp_rsp tmp s ts sz htmp hget /=.
  rewrite /lip_free_stack_frame /= /free_stack_frame /=.
  case: tmp htmp => [tmp [h1 h2] | _] /=.
  (* Some tmp: use smart_addi_tmp *)
  + have [vm' [-> heq hgetx]] :=
      acc_smart_addi_tmp_sem_fopns
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

(* Helper: smart_subi_fopn correctness for set_up_sp_register *)
Definition smart_subi_fopn (x y : var_i) imm :=
  [seq fopn_args_of_opn_args a | a <- smart_subi x y imm ].

Lemma acc_smart_subi_sem_fopns (xi : var_i) y imm s (w : wreg) :
  convertible xi.(vtype) (aword acc_reg_size) ->
  acc_params_core.is_arith_small_neg imm \/ v_var xi <> v_var y ->
  get_var true (evm s) (v_var y) >>= to_word Uptr = ok w ->
  exists vm',
    [/\ sem_fopns_args s (smart_subi_fopn xi y imm) = ok (with_vm s vm')
      , vm' =[\ Sv.singleton xi ] evm s
      & get_var true vm' xi = ok (Vword (w - wrepr reg_size imm)%R) ].
Proof using atoI call_conv sc_sem syscall_state.
  move=> hc hor hget.
  rewrite /smart_subi_fopn /smart_subi
          /acc_params_core.ACCFopn_core.smart_subi
          /acc_params_core.ACCFopn_core.gen_smart_opi.
  have hcond : [|| (0 =? imm)%Z, acc_params_core.is_arith_small_neg imm
                 | v_var y != v_var xi].
  { case: hor => [h | h].
    + by rewrite h !orbT.
    + by apply/orP; right; apply/orP; right;
       apply/eqP => heq; exact (h (esym heq)). }
  rewrite hcond /= -acc_sem_fopns_equiv.
  have hlc : acc_params_core.ACCFopn_core.gen_smart_opi
      acc_params_core.ACCFopn_core.sub
      acc_params_core.ACCFopn_core.subi
      acc_params_core.is_arith_small_neg (Some 0%Z) xi xi y imm =
      Some (acc_params_core.ACCFopn_core.gen_unsafe_smart_opi
        acc_params_core.ACCFopn_core.sub
        acc_params_core.ACCFopn_core.subi
        acc_params_core.is_arith_small_neg (Some 0%Z) xi xi y imm).
  { by rewrite /acc_params_core.ACCFopn_core.gen_smart_opi hcond. }
  have neutral_ok : forall (wr : word reg_size), (wr - wrepr reg_size 0%Z)%R = wr.
  { by move=> wr; rewrite wrepr0 GRing.subr0. }
  have [vm' [hsem heq hgetx]] :=
    ACCFopn_coreP.gen_smart_opi_sem_fopn_args
      (op := fun (x y : word reg_size) => (x - y)%R)
      (on_reg := acc_params_core.ACCFopn_core.sub)
      (on_imm := acc_params_core.ACCFopn_core.subi)
      (is_small := acc_params_core.is_arith_small_neg)
      (neutral := Some 0%Z)
      (fun s0 xi0 y0 wy0 z0 wz0 hc0 hgy0 hgz0 =>
         ACCFopn_coreP.sub_sem_fopn_args hc0 hgy0 hgz0)
      (fun s0 xi0 y0 imm0 wy0 hc0 hgy0 =>
         ACCFopn_coreP.subi_sem_fopn_args hc0 hgy0)
      neutral_ok hc hc hlc hget.
  exists vm'; split => //.
  by apply: eq_exI heq; SvD.fsetdec.
Qed.
Arguments acc_smart_subi_sem_fopns xi y imm s w _ _ _ : clear implicits.


Lemma acc_spec_lip_set_up_sp_register :
  set_up_sp_register_correct (ap_lip acc_params).
Proof.
Local Opaque sem_fopn_args.
move=> [[? nrsp] vi1] [[? nr] vi2] tmp ts al sz s + /= ? hc _ _ + _; subst.
set vrsp := {| vname := nrsp |}.
set rsp := {| v_var := vrsp; v_info := vi1 |}.
set vr := {| vname := nr |}.
set r := {| v_var := vr; v_info := vi2 |}.
move=> hget hne.
rewrite /lip_set_up_sp_register /= /set_up_sp_register /=.
(* smart_mov r rsp = [:: mov r rsp] since r != rsp *)
have hne_var : v_var r != v_var rsp.
{ by apply/eqP. }
have smart_mov_eq : acc_params_core.ACCFopn_core.smart_mov r rsp =
    [:: acc_params_core.ACCFopn_core.mov r rsp].
{ rewrite /acc_params_core.ACCFopn_core.smart_mov.
  by case: ifP => /eqP heq //; exfalso; apply hne_var; apply/eqP. }
rewrite smart_mov_eq map_cat map_cat sem_fopns_args_cat.
set vm0 := (evm s).[r <- Vword ts].
(* Step 1: mov r rsp *)
have hrc : convertible (vtype r) (aword acc_reg_size) := hc.
have hget_ts : get_var true (evm s) (v_var rsp) >>= to_word Uptr = ok ts :=
  to_word_get_var hget.
have step1 : ACCFopn_coreP.sem_fopns_args s [:: acc_params_core.ACCFopn_core.mov r rsp] =
    ok (with_vm s vm0).
{ simpl. rewrite hget /= !truncate_word_u /= /wadd wrepr0 /=.
  rewrite /vm0 set_var_eq_type //=.
  by rewrite GRing.addr0.
  by symmetry; exact: convertible_eval_atype hc. }
rewrite -(acc_sem_fopns_equiv s) step1 /=.
(* Step 2: smart_subi rsp r sz on with_vm s vm0 *)
set s0 := with_vm s vm0.
have hget_r_s0 : get_var true (evm s0) (v_var r) >>= to_word Uptr = ok ts.
{ rewrite /s0 /= /vm0 /get_var Vm.setP_eq.
  by rewrite (convertible_eval_atype hrc) /= truncate_word_u. }
have hcond_sub : acc_params_core.is_arith_small_neg sz \/ v_var rsp <> v_var r.
{ right. move=> h; exact (hne (esym h)). }
rewrite sem_fopns_args_cat.
have [vm1 [hmov_sub heq1 hgetx1]] :=
  acc_smart_subi_sem_fopns rsp r sz s0 ts erefl hcond_sub hget_r_s0.
rewrite /smart_subi_fopn in hmov_sub.
rewrite hmov_sub /=.
(* Step 3: align rsp rsp al (ANDI) *)
set vm2 := vm1.[rsp <- Vword (align_word al (ts - wrepr Uptr sz))].
have hgetx1_val : vm1.[rsp] = Vword (s:=reg_size) (ts - wrepr reg_size sz).
{ by move: hgetx1 => /get_varP [h1 _ _]. }
Local Transparent sem_fopn_args.
(* Tight invariant for vm2 - used in both modified-set and flags goals *)
have tight : vm2 =[\ Sv.add vrsp (Sv.singleton vr)] evm s.
{ move=> zz hzz.
  rewrite /vm2 Vm.setP.
  case: eqP => heqz.
  + subst zz. exfalso. apply hzz. rewrite /vrsp /=. SvD.fsetdec.
  + have hzz_vr : ~ Sv.In zz (Sv.singleton vr) by
      rewrite /vr /vrsp /=; SvD.fsetdec.
    have h3 : vm1.[zz] = (evm s0).[zz].
    { apply heq1. rewrite /rsp /=. SvD.fsetdec. }
    rewrite h3 /s0 /= /vm0.
    rewrite Vm.setP_neq; last by apply/eqP => hh2; apply hzz_vr; rewrite -hh2 /r /=; SvD.fsetdec.
    done. }
have hsub : Sv.Subset (Sv.add vrsp (Sv.singleton vr))
                      (Sv.add vr (Sv.add tmp (Sv.add vrsp vflags))).
{ rewrite /vr /vrsp /=. SvD.fsetdec. }
(* Final vm2: provide witnesses and prove invariants *)
exists vm2; split.
+ rewrite /sem_fopn_args /= /get_var hgetx1_val /= /exec_sopn /=
          !truncate_word_u /=.
  done.
+ apply: (eq_exI hsub tight).
+ (* get_var rsp = align_word al (ts - wrepr sz) *)
  rewrite /get_var /vm2 Vm.setP_eq /=.
  done.
+ (* get_var r = ts *)
  rewrite /vm2 /get_var.
  rewrite Vm.setP_neq; last by apply/eqP => hh; exact (hne (esym hh)).
  have h3 : vm1.[vr] = (evm s0).[vr].
  { apply heq1. rewrite /rsp /vr /=. SvD.fsetdec. }
  rewrite h3 /s0 /= /vm0.
  rewrite Vm.setP_eq /=.
  by move: (convertible_eval_atype hc) => ->; done.
+ (* flags invariant *)
  move=> ff /vflagsP hfftype _.
  have hvrsp_ff : vrsp <> ff.
  { apply/eqP/vtype_diff. by rewrite hfftype. }
  have hvr_ff : vr <> ff.
  { apply/eqP/vtype_diff. rewrite hfftype.
    apply/eqP => hh.
    move: hc. rewrite /r /= /vr /= in hh. rewrite hh. done. }
  symmetry.
  apply: (tight ff).
  rewrite /vrsp /vr /=. SvD.fsetdec.
Local Transparent sem_fopn_args.
Qed.

Lemma acc_lmove_correct : lmove_correct (ap_lip acc_params).
Proof.
  move=> xd xs [] // w' s _ htxd; t_xrbindP=> v hget htr.
  rewrite /lip_lmove /= /lmove /fopn_args_of_opn_args /= hget /=.
  rewrite /exec_sopn /= htr /=.
  rewrite truncate_word_u /=.
  rewrite /wadd wrepr0 GRing.addr0 /set_var /=.
  by case: vtype htxd.
Qed.

Lemma acc_lstore_correct :
  lstore_correct_aux (lip_check_ws (ap_lip acc_params))
                     (lip_lstore (ap_lip acc_params)).
Proof.
  move=> xd xs ofs [] // w wp s m _.
  t_xrbindP => vd hgetd htrd vs hgets htrs hwr.
  rewrite /lip_lstore /= /lstore /fopn_args_of_opn_args /= hgets hgetd /=
          /exec_sopn /= htrs /=.
  rewrite /sem_sop2 /= htrd /= !truncate_word_u /=.
  by rewrite truncate_word_u /= hwr.
Qed.

Lemma acc_lload_correct :
  lload_correct_aux (lip_check_ws (ap_lip acc_params))
                    (lip_lload (ap_lip acc_params)).
Proof.
  move=> xd xs ofs [] // top s w vm _.
  t_xrbindP => vs hgets hto hread hset.
  rewrite /lip_lload /= /lload /fopn_args_of_opn_args /= hgets /=.
  rewrite /sem_sop2 /= hto /= !truncate_word_u /=.
  by rewrite truncate_word_u /= hread /= /exec_sopn /= truncate_word_u /= hset.
Qed.

Lemma acc_smart_addi_correct : ladd_imm_correct_aux smart_addi_fopn.
Proof using atoI call_conv sc_sem syscall_state.
  move=> [[_ xn] xii] x2 s w ofs /= -> hne hget.
  apply: acc_smart_addi_sem_fopns hget => //.
  by right => h; exact (hne h).
Qed.

Lemma acc_lstores_correct : lstores_correct (ap_lip acc_params).
Proof using atoI call_conv sc_sem syscall_state.
apply/lstores_imm_dfl_correct; first exact: acc_lstore_correct.
exact: acc_smart_addi_correct.
Qed.

Lemma acc_lloads_correct : lloads_correct (ap_lip acc_params).
Proof using atoI call_conv sc_sem syscall_state.
  apply/lloads_imm_dfl_correct.
  + by apply acc_lload_correct.
  apply acc_smart_addi_correct.
Qed.

Lemma acc_tmp_correct :
  lip_tmp (ap_lip acc_params) <> lip_tmp2 (ap_lip acc_params).
Proof. by move=> h; assert (h1 := inj_to_ident h). Qed.

Lemma acc_check_ws_correct : lip_check_ws (ap_lip acc_params) Uptr.
Proof. done. Qed.

End LINEARIZATION.

Definition acc_hliparams :
  h_linearization_params (ap_lip acc_params) :=
  {|
    spec_lip_allocate_stack_frame := acc_spec_lip_allocate_stack_frame;
    spec_lip_free_stack_frame     := acc_spec_lip_free_stack_frame;
    spec_lip_set_up_sp_register   := acc_spec_lip_set_up_sp_register;
    spec_lip_lmove                := acc_lmove_correct;
    spec_lip_lstore               := acc_lstore_correct;
    spec_lip_lload                := acc_lload_correct;
    spec_lip_lstores              := acc_lstores_correct;
    spec_lip_lloads               := acc_lloads_correct;
    spec_lip_tmp                  := acc_tmp_correct;
    spec_lip_check_ws             := acc_check_ws_correct;
  |}.

Lemma acc_ok_lip_tmp :
  exists r : reg_t, of_ident (lip_tmp (ap_lip acc_params)) = Some r.
Proof. exists X28; exact: to_identK. Qed.

Lemma acc_ok_lip_tmp2 :
  exists r : reg_t, of_ident (lip_tmp2 (ap_lip acc_params)) = Some r.
Proof. exists X29; exact: to_identK. Qed.

(* ------------------------------------------------------------------------ *)
(* Lowering hypotheses. *)

Definition acc_hloparams : h_lowering_params (ap_lop acc_params).
Proof.
  split=> pT sCP E E0 wE rE p ev warning fv lp fn heq hfv.
  exact: (it_lower_callP ev hfv heq).
Qed.

(* -------------------------------------------------------------------------- *)
(* Lowering of complex addressing mode (identity for ACC). *)

Lemma acc_hlaparams : h_lower_addressing_params (ap_lap acc_params).
Proof.
  split=> /=.
  + exact: lower_addressing_prog_invariants.
  + exact: lower_addressing_fd_invariants.
  by move=> > /it_lower_addressing_progP.
Qed.

(* -------------------------------------------------------------------------- *)
(* Assembly generation hypotheses. *)

Section ASM_GEN.

Lemma acc_eval_assemble_cond : assemble_cond_spec (ap_agp acc_params).
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

(* Bridge: sem_sopns over assembly ops = sem_fopns_args over fopn ops *)
Lemma acc_sem_sopns_asm_args m (lc : seq acc_params_core.ACCFopn_core.opn_args) :
  sem_sopns m (asm_args_of_opn_args lc) =
  sem_fopns_args m (map fopn_args_of_opn_args lc).
Proof.
  elim: lc m => //= o lc ih m.
  case: o => -[les op] res /=.
  rewrite /sem_sopns /= /sem_fopn_args /=.
  case: sem_rexprs => //= args.
  case: exec_sopn => [| ys] /=.
  move=> a.
  case: write_lexprs => [| m''] /=.
  exact: ih.
  done.
  done.
Qed.
Arguments acc_sem_sopns_asm_args m lc : clear implicits.

(* Proof plan (set0 ws) -- follows the x86 Oset0 case.

   The assembly is a single op that self-XORs the DESTINATION itself:
   ((None, op), les, [x; x]) with x the destination (extracted from les via
   uncons_LLvar / the 4-element wide shape). The destination is not read on
   the jasmin side (id_semi ignores it: it's not even a real input), so
   assemble_opsP is NOT usable here (its sem_sopns premise would need x
   defined in m, which is not guaranteed). Instead reason on the asm side,
   where registers are total -- asm_reg always returns a register-sized
   word -- via compile_lvals, like x86.

   Steps:
   1. From the to_asm hypothesis, ops is the single op above and mapM yields
      a single assembled op. Apply assemble_asm_opI to obtain
      check_sopn_args, check_sopn_dests, check_i_args_kinds and op' = op.2.
   2. foldM eval_op .. reduces to eval_op on that single op. check_sopn_args
      pins both source asm_args to x's own compiled register: since both
      sources are literally [rvar x; rvar x], a single xreg_of_var ii x
      case-split covers both occurrences syntactically at once (as in
      x86_params_proof.v).
   3. Unfold eval_op / exec_instr_op / eval_instr_op and rewrite the acc
      semantics of (RV32 XOR) [resp. (BN_basic BN_XOR FG0)]; the two equal
      operands collapse to the zero word with wxor_xx. The goal becomes
      mem_write_vals .. (list_ltuple vt) = ok s'.
   4. Apply compile_lvals with vt and the given write_lexprs hypothesis
      (note list_ltuple vt = ys). Small case: vt is the single U32 word 0
      (id_tout = [word], no flags). Wide case: vt =
      (MF_of_word 0, LF_of_word 0, ZF_of_word 0, 0) = (false, false, true,
      0), matching desc_set0_large. Side goals: size id_out = size id_tout
      (refl), check_sopn_dests (from step 1), all2 check_arg_dest (refl on
      the desc).
   5. compile_lvals yields s' with lom_eqv m' s'.

   Key lemmas: assemble_asm_opI, compile_lvals, wxor_xx; for the wide case
     MF_of_word/LF_of_word/ZF_of_word at 0 (= false/false/true). Uses the
     acc semantics of RV32 XOR and BN_basic BN_XOR.
   Pitfalls: asm registers are total, so the self-XOR always succeeds and
     yields 0 regardless of x's contents -- this is exactly why the asm-side
     compile_lvals works where the jasmin-side assemble_opsP would not.
     Split ws <= reg_size (single-word output, no flags) from the wide case
     (3 flag outputs + word); the wide case's xreg_of_var result also needs
     r \notin acc_mod (from the BN_basic instruction's own EXa/ACR_avoid_xreg
     constraint), unpacked from check_sopn_arg alongside compat_imm.
     mapM over the single assembled op only exposes its bind shape to
     t_xrbindP after an explicit [rewrite /mapM /=] (plain [/=] on hmap is
     not enough here since [ops] is not yet a literal singleton at that
     point).
   cf. x86_params_proof.v, the Oset0 case of assemble_extra_op. *)
Lemma acc_assemble_set0_correct ws :
  assemble_extra_correct (ap_agp acc_params) (set0 ws).
Proof.
move=> rip ii lvs vs m xs ys m' s ops ops'.
move=> ho hexec hwle hops hmap hlom.
rewrite /to_asm /= /assemble_extra /assemble_set0 in hops.
rewrite /assemble_self_xor in hops.
case hws: (ws <= reg_size)%CMP in hops.
(* Small case: ws <= reg_size, op = RV32 XOR, x is the destination *)
- move: hops; t_xrbindP => x hx heq; subst ops.
  move: hexec ho.
  rewrite /exec_sopn /sopn_sem /sopn_sem_ /= hws /=.
  case: xs => [|//]; move=> hexec _.
  simpl in hexec.
  move: hexec => /ok_inj hexeq; rewrite -hexeq in hwle.
  move: hmap; rewrite /mapM /=.
  t_xrbindP => -[op' asm_args] hass <- /=.
  assert (h := assemble_asm_opI hass); case: h => hca hcd hidc -> /= {hass}.
  rewrite /id_args_kinds /= in hidc.
  rewrite orbF /check_args_kinds /= in hidc.
  case: asm_args hidc hca hcd =>
    [// | a0 [// | a1 [// | a2 [// | a3 rest]]]] hidc hca hcd.
  + by rewrite /= /= /= in hidc; move: hidc; rewrite !andbF.
  + move: hca; rewrite /check_sopn_args /= => /and3P [hca1 hca2 _].
    rewrite /check_sopn_arg /= in hca1 hca2.
    case hxr: (xreg_of_var ii x) => [r|//] in hca1 hca2.
    have hxrI := xreg_of_varI hxr.
    case: r hxr hxrI hca1 hca2 => [r|r|r|||] hxr hxrI hca1 hca2;
      try (by move: hxrI).
    + move: hca1 hca2; rewrite andbT /compat_imm /= => /orP [/eqP ha1|//] /orP [/eqP ha2|//].
      rewrite orbF in ha2. move: ha2 => /eqP/eqP ha2.
      rewrite -ha1 -ha2.
      rewrite /arch_sem.eval_op /arch_sem.exec_instr_op /arch_sem.eval_instr_op /=.
      have hcheck : (check_arg_kind a0 CAreg || false) && true || false = true.
      { rewrite /= /= /= in hidc.
        move: hidc => /and3P [h0 _ _].
        by rewrite /= h0. }
      rewrite /assert hcheck /= !truncate_word_u /= wxor_xx /=.
      rewrite -ha1 -ha2 in hcd.
      set id := instr_desc (None, RV32 XOR).
      have hsize : size (id_out id) = size (id_tout id)
        by exact: eqP (andP (id_eq_size id)).2.
      have [s' hfold hlom'] :=
        compile_lvals (agparams := ap_agp acc_params) MSB_MERGE
          hsize hwle hlom hcd id.(id_check_dest).
      by exists s'; [rewrite hfold | exact: hlom'].
    + (* x compiles to XReg: contradicts check_arg_kind a1 CAreg *)
      move=> hca2'.
      move: hidc; rewrite /= /= /= => /and3P [h0 h1 h2].
      move: hca2; rewrite /compat_imm /= andbT => /orP [/eqP heq|//].
      by move: h1; rewrite -heq /check_arg_kind.
  + by rewrite /= /= /= in hidc; move: hidc; rewrite !andbF.
(* Wide case: ws > reg_size, op = BN_basic BN_XOR FG0, x is the destination *)
- move: hops; t_xrbindP => x hx heq; subst ops.
  move: hexec ho.
  rewrite /exec_sopn /sopn_sem /sopn_sem_ /=.
  move=> hexec _.
  rewrite /= hws /= in hexec.
  case: xs hexec => [|//]; move=> hexec.
  simpl in hexec.
  move: hexec => /ok_inj hexeq; rewrite -hexeq in hwle.
  move: hmap; rewrite /mapM /=.
  t_xrbindP => -[op' asm_args] hass <- /=.
  assert (h := assemble_asm_opI hass); case: h => hca hcd hidc -> /= {hass}.
  rewrite /id_args_kinds /= in hidc.
  rewrite orbF /check_args_kinds /= in hidc.
  case: asm_args hidc hca hcd =>
    [// | a0 [// | a1 [// | a2 [// | a3 rest]]]] hidc hca hcd.
  + by rewrite /= /= /= in hidc; move: hidc; rewrite !andbF.
  + move: hca; rewrite /check_sopn_args /= => /and3P [hca1 hca2 _].
    rewrite /check_sopn_arg /= in hca1 hca2.
    case hxr: (xreg_of_var ii x) => [r|//] in hca1 hca2.
    have hxrI := xreg_of_varI hxr.
    case: r hxr hxrI hca1 hca2 => [r|r|r|||] hxr hxrI hca1 hca2;
      try (by move: hxrI).
    + (* x compiles to Reg: contradicts check_arg_kind a1 CAxmm *)
      move: hidc; rewrite /= /= /= => /and3P [h0 h1 h2].
      move: hca1 => /andP [hcompat _].
      move: hcompat; rewrite /compat_imm /= orbF => /eqP heq.
      by move: h1; rewrite -heq /check_arg_kind.
    + move: hca2 => /andP [heq1 hnotin1].
      move: heq1; rewrite /compat_imm /= orbF => /eqP ha1.
      move=> hca2'; move: hca2' => /andP [heq2 hnotin2].
      move: heq2; rewrite /compat_imm /= orbF => /eqP ha2.
      rewrite -ha1 in hnotin1.
      rewrite -ha2 in hnotin2.
      rewrite -ha1 -ha2.
      rewrite -ha1 -ha2 in hcd.
      rewrite /arch_sem.eval_op /arch_sem.exec_instr_op /arch_sem.eval_instr_op /=.
      have hcheck : (check_arg_kind a0 CAxmm || false) && true || false = true.
      { rewrite /= /= /= in hidc.
        move: hidc => /and3P [h0 _ _].
        by rewrite /= h0. }
      rewrite /assert hcheck hnotin1 /= !truncate_word_u /= wxor_xx /=.
      rewrite /lsb w0E msb0 eqxx /=.
      set id := instr_desc (None, BN_basic BN_XOR acc_options.FG0).
      have hid_tout : id_tout id = [:: lbool; lbool; lbool; lword256] by rewrite /id /=.
      have hid_out : id_out id = [:: F MF0; F LF0; F ZF0; EXa 0] by rewrite /id /=.
      rewrite hid_out hid_tout in hcd.
      have hsize : size (id_out id) = size (id_tout id)
        by exact: eqP (andP (id_eq_size id)).2.
      have [s' hfold hlom'] :=
        compile_lvals (agparams := ap_agp acc_params)
          (id_tout := [:: lbool; lbool; lbool; lword256])
          (vt := (Some false, (Some false, (Some true, (0%R : word U256)))))
          MSB_MERGE hsize hwle hlom hcd id.(id_check_dest).
      by exists s'; [rewrite hfold | exact: hlom'].
  + by rewrite /= /= /= in hidc; move: hidc; rewrite !andbF.
Qed.

(* --------------------------------------------------------------------------
   Common skeleton for MOV / SUBI / SWAP (the assemble_opsP bridge).

   All three lower to a list of fopn-style ops and share this structure:
   - Apply assemble_opsP acc_eval_assemble_cond to the given
     [mapM (assemble_asm_args ..) ops = ok ops'] hypothesis. This reduces
     the goal to (a) the all-None side condition on ops, and (b) the
     jasmin-side obligation [sem_sopns m ops = ok m'], where m' is the
     extra-op result already fixed by the write_lexprs hypothesis;
     assemble_opsP then returns the asm state s' with
     [foldM eval_op .. = ok s'] and [lom_eqv m' s'].
   - all-None side condition: every assembled op carries msb None. For
     MOV/SUBI (ops = asm_args_of_opn_args _) discharge with all_map; for
     SWAP (explicit tuples) it is refl.
   - MOV and SUBI get ops from asm_args_of_opn_args of a smart_* opn_args
     list, so rewrite sem_sopns into sem_fopns_args with the bridge
     acc_sem_sopns_asm_args and discharge that with the ACCFopn_coreP fopn
     lemmas. SWAP's ops are raw asm tuples, so its sem_sopns is computed
     directly (see its plan).
   - Close by proving the varmap from the fopn computation equals evm m'
     (reconcile the written words, modulo the extra op's U32 truncation).
   -------------------------------------------------------------------------- *)

(* Proof plan (MOV) -- uses the common assemble_opsP bridge above.

   assemble_MOV: les = [LLvar x], res = [rvar y] (uncons_LLvar /
   uncons_rvar), ops = asm_args_of_opn_args (smart_mov x y), where
   smart_mov x y = if x == y then [::] else [:: mov x y] and mov = addi _ _ 0.
   The extra op desc_MOV reads y and writes the U32-truncated value to x
   (semi = id).

   Suggested helper (add it; analogous to acc_smart_subi_sem_fopns): for x
   convertible to (aword acc_reg_size) and y readable as a Uptr-word wy,
   running [sem_fopns_args s (map fopn_args_of_opn_args (smart_mov x y))]
   leaves the varmap unchanged off x and sets get_var x = Vword wy. Prove it
   by casing x == y: the empty-list branch keeps vm = evm s, where get_var x
   (= get_var y) already yields Vword wy since y holds a U32 word; the x <> y
   branch is ACCFopn_coreP.mov_sem_fopn_args.

   Steps:
   1. Bridge: assemble_opsP + acc_sem_sopns_asm_args (common block).
   2. Discharge sem_fopns_args with the helper; the premise
      [get_var y >>= to_word Uptr = ok wy] comes from the given sem_rexprs
      hypothesis.
   3. The helper writes x <- Vword wy; the extra op writes x <- (U32
      truncation of y's value). These coincide since wy = to_word U32 of y's
      value; conclude with_vm m vm' = m', then lom_eqv from assemble_opsP.

   Key lemmas: assemble_opsP, acc_eval_assemble_cond,
     acc_sem_sopns_asm_args, ACCFopn_coreP.mov_sem_fopn_args (plus the new
     acc_smart_mov_sem_fopns helper).
   Pitfalls: the x == y branch is a no-op (empty op list; writing back y's
     already-truncated value is the identity). Mind acc_reg_size = Uptr =
     U32 and the U32 truncation when matching values.
   cf. riscv_params_proof.v assemble_add_large_imm_correct (same smart_* +
   assemble_opsP shape). *)
Lemma acc_assemble_MOV_correct :
  assemble_extra_correct (ap_agp acc_params) MOV.
Proof.
move=> rip ii lvs args m xs ys m' s ops ops'.
move=> hrex hexec hwle hops hmap hlom.
move: hops hwle hrex; rewrite /to_asm /= /assemble_extra /assemble_MOV.
t_xrbindP=> -[x les] /=.
case: lvs => // -[] // [[aty aid] aii] _ /= [<- ->] {x}.
t_xrbindP=> -[y res]; case: args => // -[] // -[] // b _ /= [<- ->] {y}.
t_xrbindP; case: aty => // _ /eqP [->].
set a := {| vname := aid; |}.
set ai := {| v_var := a |}.
move=> hops_eq.
case: ys hexec => // v ys.
t_xrbindP=> + _ vm0 hvm0 <- + v1 + vs + ?; subst xs.
rewrite /exec_sopn /sopn_sem /sopn_sem_ /=.
t_xrbindP; case: vs => // _ v0 hv0 [<-] ??; subst v ys.
change U32 with Uptr in v0.
case: les => //= -[?]; subst m'.
case: res => //=; last by t_xrbindP.
move=> hv1 _.
have hc : convertible ai.(v_var).(vtype) (aword reg_size) by [].
have hget : get_var true (evm m) b >>= to_word Uptr = ok v0.
- by rewrite hv1 /= hv0.
set vm' := (evm m).[v_var ai <- Vword v0].
have hsem := ACCFopn_coreP.mov_sem_fopn_args hc hget.
have hops_form : ops =
    asm_args_of_opn_args [:: acc_params_core.ACCFopn_core.mov ai b]
  by rewrite -hops_eq.
have hsopns : sem_sopns m ops = ok (with_vm m vm').
- rewrite hops_form acc_sem_sopns_asm_args
    -acc_sem_fopns_equiv /ACCFopn_coreP.sem_fopns_args.
  cbn [foldM].
  by rewrite hsem.
have hall : all (fun '(op, _, _) =>
  match op.1 with | Some _ => false | None => true end) ops.
- by rewrite hops_form all_map; apply/allT => -[[]].
have [s' hfold hlom'] :=
  assemble_opsP acc_eval_assemble_cond hmap hall hsopns hlom.
exists s' => //.
apply: (lom_eqv_ext _ hlom') => z /=.
move/set_varP : hvm0 => [_ _ ->].
rewrite Vm.setP (convertible_eval_atype hc).
done.
Qed.

(* Proof plan (NOT) -- identical to [acc_assemble_MOV_correct] above (same
   uncons_LLvar / uncons_rvar / convertible-assert shape in [assemble_NOT]),
   except the extra op's semantics is [wnot] instead of [id] and the emitted
   opn_args is [ACCFopn_core.not] (single [XORI _, _, -1]) instead of
   [ACCFopn_core.mov]: the destination is set to [wnot v0] rather than
   [v0], where [v0] is [b]'s (U32-truncated) value.

   Key lemmas: assemble_opsP, acc_eval_assemble_cond,
     acc_sem_sopns_asm_args, ACCFopn_coreP.not_sem_fopn_args. *)
Lemma acc_assemble_NOT_correct :
  assemble_extra_correct (ap_agp acc_params) NOT.
Proof.
move=> rip ii lvs args m xs ys m' s ops ops'.
move=> hrex hexec hwle hops hmap hlom.
move: hops hwle hrex; rewrite /to_asm /= /assemble_extra /assemble_NOT.
t_xrbindP=> -[x les] /=.
case: lvs => // -[] // [[aty aid] aii] _ /= [<- ->] {x}.
t_xrbindP=> -[y res]; case: args => // -[] // -[] // b _ /= [<- ->] {y}.
t_xrbindP; case: aty => // _ /eqP [->].
set a := {| vname := aid; |}.
set ai := {| v_var := a |}.
move=> hops_eq.
case: ys hexec => // v ys.
t_xrbindP=> + _ vm0 hvm0 <- + v1 + vs + ?; subst xs.
rewrite /exec_sopn /sopn_sem /sopn_sem_ /=.
t_xrbindP; case: vs => // _ v0 hv0 [<-] ??; subst v ys.
change U32 with Uptr in v0.
case: les => //= -[?]; subst m'.
case: res => //=; last by t_xrbindP.
move=> hv1 _.
have hc : convertible ai.(v_var).(vtype) (aword reg_size) by [].
have hget : get_var true (evm m) b >>= to_word Uptr = ok v0.
- by rewrite hv1 /= hv0.
set vm' := (evm m).[v_var ai <- Vword (wnot v0)].
have hsem := ACCFopn_coreP.not_sem_fopn_args hc hget.
have hops_form : ops =
    asm_args_of_opn_args [:: acc_params_core.ACCFopn_core.not ai b]
  by rewrite -hops_eq.
have hsopns : sem_sopns m ops = ok (with_vm m vm').
- rewrite hops_form acc_sem_sopns_asm_args
    -acc_sem_fopns_equiv /ACCFopn_coreP.sem_fopns_args.
  cbn [foldM].
  by rewrite hsem.
have hall : all (fun '(op, _, _) =>
  match op.1 with | Some _ => false | None => true end) ops.
- by rewrite hops_form all_map; apply/allT => -[[]].
have [s' hfold hlom'] :=
  assemble_opsP acc_eval_assemble_cond hmap hall hsopns hlom.
exists s' => //.
apply: (lom_eqv_ext _ hlom') => z /=.
move/set_varP : hvm0 => [_ _ ->].
rewrite Vm.setP (convertible_eval_atype hc).
done.
Qed.

(* Proof plan (SUBI) -- uses the common assemble_opsP bridge above.

   assemble_SUBI: les = [LLvar x], res = [rvar y; wconst imm] (uncons_LLvar /
   uncons_rvar / uncons_wconst). It returns ok via
   [o2r (ACCFopn_core.smart_subi x y imm)], hence succeeds iff that option
   is Some args. In the Some case the unqualified seq smart_subi x y imm
   (= odflt [subi x y imm] (Some args)) equals args, so ops =
   asm_args_of_opn_args (smart_subi x y imm) and
   [map fopn_args_of_opn_args ops = smart_subi_fopn x y imm]. The extra op
   desc_SUBI reads y and imm and writes x <- y - imm.

   Steps:
   1. From assemble_SUBI = ok ops derive ACCFopn_core.smart_subi = Some _
      (o2rP) and rewrite ops = asm_args_of_opn_args (smart_subi x y imm).
   2. Bridge: assemble_opsP + acc_sem_sopns_asm_args (common block),
      leaving [sem_fopns_args m (smart_subi_fopn x y imm) = ok m'].
   3. Discharge with the EXISTING helper acc_smart_subi_sem_fopns, which
      gives x <- Vword (w - wrepr reg_size imm) with w = to_word Uptr of y's
      value (the read of y comes from the sem_rexprs hypothesis). Its
      precondition [is_arith_small_neg imm \/ x <> y] follows from the
      gen_smart_opi Some-guard [|| is_mov (Some 0) imm, is_arith_small_neg
      imm | y != x]: the is_mov disjunct forces imm = 0 (small), otherwise
      the small or the y != x disjunct applies.
   4. Match values: the extra op writes y's word minus imm's word; the Z imm
      from uncons_wconst equals the unsigned of SUBI's second input, so
      w - wrepr imm coincides; conclude lom_eqv via assemble_opsP.

   Key lemmas: assemble_opsP, acc_eval_assemble_cond,
     acc_sem_sopns_asm_args, acc_smart_subi_sem_fopns (already proved),
     o2rP.
   Pitfalls: assemble only succeeds in the Some case -- derive it first and
     rewrite ops accordingly; reconcile the immediate (Z vs wrepr) and the
     U32 truncation.
   cf. riscv_params_proof.v assemble_add_large_imm_correct. *)
Lemma acc_assemble_SUBI_correct :
  assemble_extra_correct (ap_agp acc_params) SUBI.
Proof using atoI call_conv sc_sem syscall_state.
  move=> rip ii lvs args m xs ys m' s ops ops'.
  move=> hrex hexec hwle hops hmap hlom.
  move: hops; rewrite /to_asm /= /assemble_extra /assemble_SUBI.
  move: hrex hwle.
  case: lvs => // -[] // [[xt xn] xii] [] //.
  case: args => // -[] //.
  move=> f l.
  case: f => //= y.
  (* peel the [wconst] immediate *)
  rewrite /arm_extra.uncons_wconst.
  case: l => // -[] // -[] //.
  move=> s0 f0 l0.
  case: s0 => //= ws.
  case: f0 => //= imm.
  (* peel the assemble premise: [hc] (the dest type assert), [args0], etc. *)
  move=> hrex hwle; t_xrbindP => hc htrivial args0 hsmart hops_eq.
  set xi := {| v_var := {| vtype := xt; vname := xn |}; v_info := xii |}.
  move: hrex hexec hwle hmap hlom.
  (* peel [sem_rexprs]; note the scrambled binder order from the nested Lets *)
  t_xrbindP => vy hvy vs hvs.
  move=> hvl heqv heqxs; subst vs; subst xs.
  move=> hexec; move: hexec.
  rewrite /exec_sopn /sopn_sem /sopn_sem_ /=.
  change (to_word U32) with (to_word Uptr).
  (* split off the degenerate l0-tail: [main], [l0-tail], [extra dests] *)
  case: hvs hvl => [|v1 vl1] hvl /=.
  (* --- main case --- *)
  change (to_word U32) with (to_word Uptr).
  t_xrbindP => tval wyv hvyw wiv htr hsub heqys.
  subst tval; subst ys.
  case heq: (set_var true (evm m) {| vtype := xt; vname := xn |}
                       (Vword (wyv - wiv)%R))
    => [vm1 |] /= // [<-] hmap hlom.
  have hc' : convertible xi.(vtype) (aword acc_reg_size) := hc.
  have hget : get_var true (evm m) y >>= to_word U32 = ok wyv
    by rewrite hvy /=; exact hvyw.
  have hsome : acc_params_core.ACCFopn_core.smart_subi xi y imm = Some args0
    := o2rP hsmart.
  have HOR : acc_params_core.is_arith_small_neg imm \/ v_var xi <> v_var y.
  move: hsome;
    rewrite /acc_params_core.ACCFopn_core.smart_subi
            /acc_params_core.ACCFopn_core.gen_smart_opi
            /acc_params_core.ACCFopn_core.is_mov;
    case: ifP => // hg _;
    move: hg => /or3P [/Z.eqb_eq -> | hsmall | hne];
    [ by left | by left | by right => h; move: hne; rewrite h eqxx ].
  have [vm' [hsem heq_vm hgetx]] :=
    acc_smart_subi_sem_fopns (xi := xi) (y := y) (imm := imm)
      (s := m) (w := wyv) hc' HOR hget.
  have hargs_eq :
    smart_subi_fopn xi y imm = [seq fopn_args_of_opn_args a | a <- args0]
    by rewrite /smart_subi_fopn /smart_subi hsome /=.
  have hsopns : sem_sopns m ops = ok (with_vm m vm')
    by rewrite -hops_eq acc_sem_sopns_asm_args -hargs_eq; exact: hsem.
  have hall : all (fun '(op, _, _) =>
    match op.1 with | Some _ => false | None => true end) ops
    by rewrite -hops_eq all_map; apply/allT => -[[]].
  have [s' hfold hlom'] :=
    assemble_opsP acc_eval_assemble_cond hmap hall hsopns hlom.
  exists s' => //.
  apply: (lom_eqv_ext _ hlom') => z /=.
  (* the immediate reconciliation: [wiv = wrepr reg_size imm] *)
  have hwiv : wiv = wrepr U32 imm
    by move: htr => /truncate_wordP [hle ->]; rewrite zero_extend_wrepr.
  move/set_varP: heq => [_ _ ->].
  rewrite Vm.setP (convertible_eval_atype hc).
  case: eqP => [<- | hne];
    last by apply: heq_vm; rewrite Sv.singleton_spec; exact: not_eq_sym hne.
  rewrite hwiv.
  move/get_varP: hgetx => [h1 _ _].
  by rewrite -h1.
  (* --- l0-tail (degenerate: SUBI reads only [y] and [imm]) --- *)
  by move=> /=; case: (to_word U32 vy) => //= ?;
     case: (truncate_word U32 (wrepr ws imm)) => //=.
  (* --- extra dests (SUBI has exactly one output) --- *)
  move=> a l hrex hwle _.
  case: ys hexec hwle => [| b [| b0 lb]] hexec hwle.
  - move: hexec; rewrite /exec_sopn /sopn_sem /sopn_sem_ /=; by t_xrbindP.
  - move: hwle; rewrite /write_lexprs /=.
    by case: (set_var true (evm m) {| vtype := xt; vname := xn |} b).
  - by move: hexec; rewrite /exec_sopn /sopn_sem /sopn_sem_ /=; t_xrbindP.
Qed.

(* Proof plan (ADD_LARGE_IMM) -- same shape as SUBI, but simpler: the
   [v_var x != v_var y] assert is unconditional (not an "or" with
   [imm = 0]), so [acc_smart_addi_sem_fopns]'s disjunctive precondition is
   discharged directly from that hypothesis, without SUBI's [gen_smart_opi]
   guard unpacking. cf. acc_assemble_SUBI_correct. *)
Lemma acc_assemble_ADD_LARGE_IMM_correct :
  assemble_extra_correct (ap_agp acc_params) ADD_LARGE_IMM.
Proof using atoI call_conv sc_sem syscall_state.
  move=> rip ii lvs args m xs ys m' s ops ops'.
  move=> hrex hexec hwle hops hmap hlom.
  move: hops; rewrite /to_asm /= /assemble_extra /assemble_ADD_LARGE_IMM.
  move: hrex hwle.
  case: lvs => // -[] // [[xt xn] xii] [] //.
  case: args => // -[] //.
  move=> f l.
  case: f => //= y.
  (* peel the [wconst] immediate *)
  rewrite /arm_extra.uncons_wconst.
  case: l => // -[] // -[] //.
  move=> s0 f0 l0.
  case: s0 => //= ws.
  case: f0 => //= imm.
  (* peel the assemble premise: [hxy] (register disequality), [hc] (the
     dest type assert), [args0], etc. *)
  move=> hrex hwle; t_xrbindP => hxy hc args0 hsmart hops_eq.
  set xi := {| v_var := {| vtype := xt; vname := xn |}; v_info := xii |}.
  move: hrex hexec hwle hmap hlom.
  (* peel [sem_rexprs]; note the scrambled binder order from the nested Lets *)
  t_xrbindP => vy hvy vs hvs.
  move=> hvl heqv heqxs; subst vs; subst xs.
  move=> hexec; move: hexec.
  rewrite /exec_sopn /sopn_sem /sopn_sem_ /=.
  change (to_word U32) with (to_word Uptr).
  (* split off the degenerate l0-tail: [main], [l0-tail], [extra dests] *)
  case: hvs hvl => [|v1 vl1] hvl /=.
  (* --- main case --- *)
  change (to_word U32) with (to_word Uptr).
  t_xrbindP => tval wyv hvyw wiv htr hadd heqys.
  subst tval; subst ys.
  case heq: (set_var true (evm m) {| vtype := xt; vname := xn |}
                       (Vword (wyv + wiv)%R))
    => [vm1 |] /= // [<-] hmap hlom.
  have hc' : convertible xi.(vtype) (aword acc_reg_size) := hc.
  have hget : get_var true (evm m) y >>= to_word U32 = ok wyv
    by rewrite hvy /=; exact hvyw.
  have hsome : acc_params_core.ACCFopn_core.smart_addi xi y imm = Some args0
    := o2rP hsmart.
  have HOR : acc_params_core.is_arith_small imm \/ v_var xi <> v_var y.
    right => h; rewrite /xi /= in h; move: hxy; rewrite h eqxx; by [].
  have [vm' [hsem heq_vm hgetx]] :=
    acc_smart_addi_sem_fopns (xi := xi) (y := y) (imm := imm)
      (s := m) (w := wyv) hc' HOR hget.
  have hargs_eq :
    smart_addi_fopn xi y imm = [seq fopn_args_of_opn_args a | a <- args0]
    by rewrite /smart_addi_fopn /smart_addi hsome /=.
  have hsopns : sem_sopns m ops = ok (with_vm m vm')
    by rewrite -hops_eq acc_sem_sopns_asm_args -hargs_eq; exact: hsem.
  have hall : all (fun '(op, _, _) =>
    match op.1 with | Some _ => false | None => true end) ops
    by rewrite -hops_eq all_map; apply/allT => -[[]].
  have [s' hfold hlom'] :=
    assemble_opsP acc_eval_assemble_cond hmap hall hsopns hlom.
  exists s' => //.
  apply: (lom_eqv_ext _ hlom') => z /=.
  (* the immediate reconciliation: [wiv = wrepr reg_size imm] *)
  have hwiv : wiv = wrepr U32 imm
    by move: htr => /truncate_wordP [hle ->]; rewrite zero_extend_wrepr.
  move/set_varP: heq => [_ _ ->].
  rewrite Vm.setP (convertible_eval_atype hc).
  case: eqP => [<- | hne];
    last by apply: heq_vm; rewrite Sv.singleton_spec; exact: not_eq_sym hne.
  rewrite hwiv.
  move/get_varP: hgetx => [h1 _ _].
  by rewrite -h1.
  (* --- l0-tail (degenerate: ADD_LARGE_IMM reads only [y] and [imm]) --- *)
  by move=> /=; case: (to_word U32 vy) => //= ?;
     case: (truncate_word U32 (wrepr ws imm)) => //=.
  (* --- extra dests (ADD_LARGE_IMM has exactly one output) --- *)
  move=> a l hrex hwle _.
  case: ys hexec hwle => [| b [| b0 lb]] hexec hwle.
  - move: hexec; rewrite /exec_sopn /sopn_sem /sopn_sem_ /=; by t_xrbindP.
  - move: hwle; rewrite /write_lexprs /=.
    by case: (set_var true (evm m) {| vtype := xt; vname := xn |} b).
  - by move: hexec; rewrite /exec_sopn /sopn_sem /sopn_sem_ /=; t_xrbindP.
Qed.

Lemma acc_assemble_swap_correct ws :
  assemble_extra_correct (ap_agp acc_params) (SWAP ws).
Proof.
  move=> rip ii lvs args m xs ys m' s ops ops' /= h ++ h'.
  move: h h'.
  case: args => // -[] // [] // z [] // [] // [] // w [] //=.
  rewrite /assemble_swap /=.
  t_xrbindP => vz hz _ vw hw <- <-.
  case: (ws =P U32) => [?|_].
  - subst ws; case: lvs => // -[] // x [] // [] // y [] //.
    move=> -[[[_ _] _] _] [<- <- <- <-] + hex hwr.
    move: hex hwr.
    rewrite /exec_sopn /= /sopn_sem /sopn_sem_ /= /swap_semi.
    t_xrbindP => /= _ wz hvz ww hvw <- <- /=.
    t_xrbindP => _ vm1 /set_varP [_ htrx ->] <- _ vm2 /set_varP [_ htry ->] <- <- /eqP hxw /eqP hyx /and4P [hxt hyt hzt hwt] <-.
    move=> hmap hlom.
    have h := (assemble_opsP acc_eval_assemble_cond hmap erefl _ hlom).
    set m1 := (with_vm m (((evm m).[x <- Vword (wxor wz ww)]).[y <- Vword (wxor (wxor wz ww) ww)])
                                .[x <- Vword (wxor (wxor wz ww) (wxor (wxor wz ww) ww))]).
    case: (h m1) => {h}.
    + rewrite /= hz /= hw /= /exec_sopn /= hvz hvw /=.
      rewrite set_var_truncate //= !get_var_eq //= (convertible_eval_atype hxt) /=.
      rewrite get_var_neq // hw /= truncate_word_u /= hvw /=.
      rewrite set_var_truncate //= !get_var_eq //= (convertible_eval_atype hyt) /=.
      rewrite get_var_neq // get_var_eq //= (convertible_eval_atype hxt) /= !truncate_word_u /=.
      by rewrite set_var_truncate //= !with_vm_idem.
    move=> s' hfold hlom'; exists s' => //; apply: lom_eqv_ext hlom'.
    move=> i /=; rewrite !Vm.setP; case: eqP => [<- | ?].
    + by move/eqP/negbTE: hyx => -> /=; rewrite (convertible_eval_atype hxt) /= wxorA wxor_xx wxor0.
    by case: eqP => // _; rewrite -wxorA wxor_xx wxorC wxor0.
  case: (ws =P U256) => [?|//].
  subst ws.
  case: lvs => // fM [] // fL [] // fZ [] // [] // x [] // [] // y [] //.
  move=> -[[[_ _] _] _] [<- <- <- <-] + hex hwr.
  move: hex hwr.
  rewrite /exec_sopn /= /sopn_sem /sopn_sem_ /= /swap_semi.
  t_xrbindP=> /= _ wz hvz ww hvw <- <- /=; t_xrbindP.
  move=> z0 hM z1 hL z2 hZ z3 z4 hsx ? z5 z6 hsy ? ?; subst z3 z5 m'.
  move: hM hL hZ.
  case: fM => [al sz ae|fm] /=; first by t_xrbindP.
  case: fL => [al sz ae|fl] /=; first by move=> _; t_xrbindP.
  case: fZ => [al sz ae|fz] /=; first by move=> _ _; t_xrbindP.
  move=> hsetM hsetL hsetZ.
  move=> hxw hyx /and5P [hxt hyt hzt hwt _] <- hmap hlom.
  move: hsetM => /=; t_xrbindP => vm0 hvm0 ?; subst z0.
  move: hsetL => /=; t_xrbindP => vm1 hvm1 ?; subst z1.
  move: hsetZ => /=; t_xrbindP => vm2 hvm2 ?; subst z2.
  have hfmty : eval_atype (vtype fm) = cbool
    by have /set_varP [_ h _] := hvm0; case: (eval_atype (vtype fm)) h.
  have hflty : eval_atype (vtype fl) = cbool
    by have /set_varP [_ h _] := hvm1; case: (eval_atype (vtype fl)) h.
  have hfzty : eval_atype (vtype fz) = cbool
    by have /set_varP [_ h _] := hvm2; case: (eval_atype (vtype fz)) h.
  have hne : forall (f g : var_i), eval_atype (vtype f) = cbool ->
      convertible (vtype g) (aword U256) -> v_var f <> v_var g.
    by move=> f g hf hg he; move: hf; rewrite he (convertible_eval_atype hg).
  have h := assemble_opsP acc_eval_assemble_cond hmap erefl _ hlom.
  set r1 := wxor wz ww.
  set r2 := wxor r1 ww.
  set r3 := wxor r1 r2.
  set m1 := with_vm m
    m.(evm)
    .[fm <- msb r1].[fl <- lsb r1].[fz <- (r1 == 0%R)]
    .[x  <- Vword r1]
    .[fm <- msb r2].[fl <- lsb r2].[fz <- (r2 == 0%R)]
    .[y  <- Vword r2]
    .[fm <- msb r3].[fl <- lsb r3].[fz <- (r3 == 0%R)]
    .[x  <- Vword r3].
  case: (h m1) => {h}.
  rewrite /= hz /= hw /= /exec_sopn /= hvz hvw /=.
  move/eqP in hxw; move/eqP in hyx.
  have hfmw := hne _ _ hfmty hwt.
  have hflw := hne _ _ hflty hwt.
  have hfzw := hne _ _ hfzty hwt.
  have hfmx := hne _ _ hfmty hxt.
  have hflx := hne _ _ hflty hxt.
  have hfzx := hne _ _ hfzty hxt.
  do !rewrite set_var_truncate //=.
  t_get_var.
  rewrite /= (convertible_eval_atype hxt) /= hw /= truncate_word_u /= hvw /=.
  do !rewrite set_var_truncate //=.
  t_get_var.
  rewrite /= (convertible_eval_atype hyt) /= (convertible_eval_atype hxt) /=
    !truncate_word_u /=.
  do !rewrite set_var_truncate //=.
  all: try by rewrite ?(convertible_eval_atype hxt)
    ?(convertible_eval_atype hyt) ?hfmty ?hflty ?hfzty.
  move=> s' hfold hlom'; exists s' => //.
  move/set_varP: hvm0 => [_ _ ?]; subst vm0.
  move/set_varP: hvm1 => [_ _ ?]; subst vm1.
  move/set_varP: hvm2 => [_ _ ?]; subst vm2.
  move/set_varP: hsx => [_ _ ?]; subst z4.
  move/set_varP: hsy => [_ _ ?]; subst z6.
  apply: lom_eqv_ext hlom'.
  have hr2 : r2 = wz by rewrite /r2 /r1 -wxorA wxor_xx wxorC wxor0.
  have hr3 : r3 = ww by rewrite /r3 /r2 /r1 wxorA wxor_xx wxor0.
  have hyfz := introN eqP (not_eq_sym (hne _ _ hfzty hyt)).
  have hyfl := introN eqP (not_eq_sym (hne _ _ hflty hyt)).
  have hyfm := introN eqP (not_eq_sym (hne _ _ hfmty hyt)).
  move=> i /=; rewrite !Vm.setP hr2 hr3.
  by do 4!(case: eqP => [<- | _] /=;
    first by rewrite ?(negbTE hyx) ?(negbTE hyfz) ?(negbTE hyfl) ?(negbTE hyfm)).
Qed.

(* [assemble_bn_select_masked] only succeeds when its own [uniq] check on
   the destination [x] and the two selected inputs [wn]/[wm] holds. This
   states that fact directly against the assembled [ops]: whatever
   destination lexpr and pair of leading source rexprs [ops] carries (the
   registers at the register-allocation conflict positions declared by
   [desc_BN_SELECT_MASKED], namely [(APout 0, APin 0); (APout 0, APin 1);
   (APin 0, APin 1)]) are pairwise distinct. The list-length of [les]/[res]
   is deliberately left open (only their heads are matched), since
   [assemble_bn_select_masked] itself never checks it -- that invariant
   (exactly one destination, three arguments) is enforced by the caller
   ([asm_gen]'s [check_sopn_args]), not by this function. *)
Lemma assemble_bn_select_masked_conflicts ii les res ops :
  assemble_bn_select_masked ii les res = ok ops ->
  if ops is [:: (_, LLvar x :: _, Rexpr (Fvar wn) :: Rexpr (Fvar wm) :: _)]
  then [&& v_var x != v_var wn, v_var x != v_var wm & v_var wn != v_var wm]
  else false.
Proof.
  have huncons_LLvar : forall ii' (l : seq lexpr) z zs,
      arm_extra.uncons_LLvar ii' l = ok (z, zs) -> l = LLvar z :: zs
    by move=> ii' [|[al ws f|x]] //= l0 z zs [-> ->].
  have huncons_rvar : forall ii' (r : seq rexpr) z zs,
      arm_extra.uncons_rvar ii' r = ok (z, zs) -> r = Rexpr (Fvar z) :: zs
    by move=> ii' [|[|[]]] //= ???? [<- <-].
  rewrite /assemble_bn_select_masked.
  t_xrbindP => -[x le] hx.
  t_xrbindP => -[wn res1] hwn.
  t_xrbindP => -[wm res'] hwm.
  t_xrbindP => huniq ?; subst ops.
  have ? := huncons_LLvar _ _ _ _ hx; subst les.
  have ? := huncons_rvar _ _ _ _ hwn; subst res.
  have ? := huncons_rvar _ _ _ _ hwm; subst res1.
  simpl.
  move: huniq => /=; rewrite negb_or => /andP [/andP [hxwn hxwm] hwnwm].
  rewrite orbF in hxwm.
  rewrite andbT inE in hwnwm.
  by apply/and3P.
Qed.

(* Proof plan (BN_SELECT_MASKED) -- unlike set0/SWAP, every operand
   here is a genuine, already-defined jasmin value (no undefined scratch or
   self register), so this should go through the [assemble_opsP] "common
   skeleton" (as MOV/SUBI/SWAP do below), NOT the asm-side/[compile_lvals]
   route used by [acc_assemble_set0_correct].

   [assemble_bn_select_masked] is a pure pass-through: [les]/[res] reach the
   assembled op completely unchanged, just retagged from the extra_op to the
   real [BN_SEL FG0] acc_op.

   Steps:
   1. Unfold [to_asm]/[assemble_extra]/[assemble_bn_select_masked] in [hops]
      and peel with [t_xrbindP], destructuring each pair inline (as in
      [acc_assemble_extra_sz]'s bullet for this op): [-[x le] hx] for the
      [uncons_LLvar] step, then [-[wn res1] hwn] and [-[wm le'] hwm] for the
      two [uncons_rvar] steps on [res], then the
      [uniq [:: v_var x; v_var wn; v_var wm]] assert. This leaves
      [ops = [:: ((None, BN_SEL FG0), lvs, args)]] with [lvs]/[args] the
      lemma's own [les]/[res] (unrenamed).
   2. Apply [assemble_opsP acc_eval_assemble_cond] to [hmap]. The all-None
      side condition is trivial ([erefl], one literal op with msb [None]).
      This reduces the goal to
      [sem_sopns m [:: ((None, BN_SEL FG0), lvs, args)] = ok m'].
   3. Unfold [sem_sopns]/[sem_sopn_t] (asm_gen_proof.v, just above
      [assemble_opsP]) to
      [sem_rexprs m args >>= exec_sopn (Oasm (BaseOp (None, BN_SEL FG0)))
        >>= write_lexprs lvs].
      The first component is exactly [ho]; the last is exactly [hwle] once
      [ys] is pinned. The middle component needs
      [exec_sopn (Oasm (BaseOp (None, BN_SEL FG0))) xs = ok ys] derived from
      [hexec : exec_sopn (Oasm (ExtOp BN_SELECT_MASKED)) xs = ok ys].
   4. This is NOT definitional: the [BaseOp] path goes through
      [arch_extra.v]'s [get_instr_desc]/[semi_to_atype] (an [ecast] via
      [computational_eq_refl], not [erefl]), while the [ExtOp] path uses
      [desc_BN_SELECT_MASKED]'s own [sem_prod_ok]. Both sides ultimately
      compute [ok (if b then wn else wm)] on the same [wn]/[wm]/[b] from
      [xs], but getting there needs unfolding both. [lower_PifP] in
      acc_lowering_proof.v (the [Pif]-lowering correctness proof, the only
      other place in the tree that unfolds [BN_SEL FG0]'s own
      [exec_sopn]/[sopn_sem]/[sopn_sem_] from scratch) is the recipe to
      mirror here for the [BaseOp] side rather than re-deriving it.
   5. Conclude with the [s']/[hfold]/[hlom'] that [assemble_opsP] returns.

   Key lemmas: [assemble_opsP] (asm_gen_proof.v), [acc_eval_assemble_cond],
     [arch_extra.v]'s [semi_to_atype]/[computational_eq_refl] for the
     [BaseOp]-side cast, [lower_PifP] (acc_lowering_proof.v) as the existing
     unfolding of [BN_SEL FG0]'s semantics to reuse.
   Pitfalls: the [uniq] assert and the descriptor's [conflicts] are
     register-allocation-time artifacts only; this value-level proof gets
     them for free from [hops] succeeding and never needs to use them
     (the extra_op's own [semi] does not depend on registers being
     distinct). Do not reach for [xreg_of_var]/[compile_lvals]-style asm-side
     reasoning here -- that machinery exists to handle registers with no
     jasmin-level value, which is not the situation for this op. *)
Lemma acc_assemble_BN_SELECT_MASKED_correct :
  assemble_extra_correct (ap_agp acc_params) BN_SELECT_MASKED.
Proof.
move=> rip ii lvs args m xs ys m' s ops ops'.
move=> ho hexec hwle hops hmap hlom.
rewrite /to_asm /= /assemble_extra /assemble_bn_select_masked in hops.
move: hops; t_xrbindP => -[x le] hx.
t_xrbindP => -[wn res1] hwn.
t_xrbindP => -[wm le'] hwm.
t_xrbindP => huniq ?; subst ops.
have h := assemble_opsP acc_eval_assemble_cond hmap erefl _ hlom.
case: (h m') => {h}.
(* [sem_sopns] on the single assembled [BN_SEL FG0]: the [sem_rexprs] part is
   [ho], the [write_lexprs] part is [hwle], and the [exec_sopn] in between is
   convertible to the extra op's own [exec_sopn] ([semi_to_atype]'s
   [computational_eq] cast reduces, both descriptors being concrete). *)
- rewrite /sem_sopns /= /sem_sopn_t ho /=.
  have hbase :
    exec_sopn (Oasm (BaseOp (None, BN_SEL acc_options.FG0))) xs = ok ys
    by exact: hexec.
  by rewrite hbase /= hwle.
by move=> s' hfold hlom'; exists s'.
Qed.

(* [assemble_zeroize_masked] only succeeds when its own assert that the two
   inputs [y1]/[y2] are different registers holds, matching
   [desc_zeroize_masked_small]/[desc_zeroize_masked_large]'s declared
   conflict [(APin 0, APin 1)]. Unlike [x], the destination register, [y1]
   itself never survives into the assembled [ops] (it is only checked to
   alias [x], then discarded); [y2] does, twice over (the self-XOR). So this
   states the fact against both the pre-assembly [res] (source of [y1]) and
   the assembled [ops] (source of [y2]), tying them together via [y2]'s
   coincidence between the two. *)
Lemma assemble_zeroize_masked_conflicts ii ws les res ops :
  assemble_zeroize_masked ii ws les res = ok ops ->
  if res is Rexpr (Fvar y1) :: Rexpr (Fvar y2) :: _ then
    if ops is [:: (_, _, [:: Rexpr (Fvar y2'); _])] then
      [&& v_var y2 == v_var y2' & v_var y1 != v_var y2]
    else false
  else false.
Proof.
  rewrite /assemble_zeroize_masked.
  t_xrbindP => -[y1 res1] hy1.
  t_xrbindP => -[y2 res2] hy2.
  t_xrbindP => x hx hcv hxy1 hxy2.
  rewrite /assemble_self_xor => -[?]; subst ops.
  simpl.
  have huncons_rvar : forall ii' (r : seq rexpr) z zs,
      arm_extra.uncons_rvar ii' r = ok (z, zs) -> r = Rexpr (Fvar z) :: zs
    by move=> ii' [|[|[]]] //= ???? [<- <-].
  have ? := huncons_rvar _ _ _ _ hy1; subst res.
  have ? := huncons_rvar _ _ _ _ hy2; subst res1.
  simpl.
  by rewrite eqxx hxy2.
Qed.

(* Proof plan (ZEROIZE_MASKED ws) -- despite reusing
   [assemble_self_xor], this is structurally closer to the MOV/SUBI/SWAP
   "common skeleton" than to [acc_assemble_set0_correct]: [set0] needed the
   asm-side/[compile_lvals] route specifically because its scratch (X03/W01)
   is NOT a jasmin variable, so [assemble_opsP]'s [sem_sopns] premise
   couldn't be established for it. Here [y1]/[y2] ARE genuine jasmin
   variables with values governed by [m] (via [ho]), so [assemble_opsP] is
   directly usable.

   Steps:
   1. Unfold [to_asm]/[assemble_extra]/[assemble_zeroize_masked] in [hops]
      and peel with [t_xrbindP]: [y1] via [uncons_rvar] (2 items), [y2] via
      [uncons_rvar] (2 items), [x] via the same generic
      if/[uncons_LLvar]-branch peel used in [acc_assemble_set0_correct] (2
      items, one [x hx]), the [convertible] assert (1 item), and the
      [v_var x == v_var y1] assert (1 item, name it [hxy1]). Then unfold
      [assemble_self_xor] to expose
      [ops = [:: ((None, op), lvs, [:: rvar y2; rvar y2])]] with
      [op := if (ws <= reg_size)%CMP then RV32 XOR else BN_basic BN_XOR FG0].
   2. As in [acc_assemble_set0_correct], [case hws: (ws <= reg_size)%CMP] to
      fix [op] and, via [hexec] (unfold [exec_sopn]/[sopn_sem]/[sopn_sem_]),
      the shape of [ys]: [[:: Vword 0]] (small) or
      [[:: false; false; true; Vword 0]] (wide).
   3. Apply [assemble_opsP acc_eval_assemble_cond] to [hmap] (all-None side
      condition trivial, one literal op), reducing to
      [sem_sopns m [:: ((None, op), lvs, [:: rvar y2; rvar y2])] = ok m'].
   4. Unfold [sem_sopns]/[sem_sopn_t]:
      [sem_rexprs m [:: rvar y2; rvar y2] >>= exec_sopn (Oasm (BaseOp (None, op)))
        >>= write_lexprs lvs].
      Recover [y2]'s value [wy2] from [ho] (which reads the lemma's own
      2-element [args], i.e. [y1] then [y2]) via [get_var]/[sem_rexprs]
      projection, then show [sem_rexprs m [:: rvar y2; rvar y2] =
      ok [:: Vword wy2; Vword wy2]].
   5. [exec_sopn (Oasm (BaseOp (None, op))) [:: Vword wy2; Vword wy2]]
      collapses via [wxor_xx] to the zero word (small case), or to
      [(MF_of_word 0, LF_of_word 0, ZF_of_word 0, 0) = (false, false, true,
      0)] (wide case) -- the exact same [wxor_xx]/flag constants already
      used in the wide case of [acc_assemble_set0_correct]. Match this
      against [ys] from step 2 (definitionally the same tuple).
   6. [write_lexprs lvs ys m = ok m'] is exactly [hwle]. Conclude with the
      [s']/[hfold]/[hlom'] that [assemble_opsP] returns.

   Key lemmas: [assemble_opsP], [acc_eval_assemble_cond], [wxor_xx],
     [MF_of_word]/[LF_of_word]/[ZF_of_word] at [0] (reuse verbatim from
     [acc_assemble_set0_correct]'s wide case), [get_var]/[sem_rexprs]
     projection for reading [y2] twice from one [ho].
   Pitfalls: do NOT reach for [xreg_of_var]/[compile_lvals] here -- that was
     [set0]'s answer to a problem ("this register has no jasmin value")
     that does not exist for [y1]/[y2]. The [convertible] and
     [v_var x == v_var y1] asserts, like [BN_SELECT_MASKED]'s [uniq] check,
     are register-allocation-time artifacts the value-level proof does not
     need to exploit: [x] is never read by the assembled instruction (only
     [y2], twice), and [y1]'s value (read once by [ho], since it is still
     part of the original [args]) is likewise never otherwise used. Keep the
     small/wide case split consistent between [hexec] (which fixes [ys])
     and [assemble_self_xor]'s own [(ws <= reg_size)%CMP] test for [op]. *)
Lemma acc_assemble_ZEROIZE_MASKED_correct ws :
  assemble_extra_correct (ap_agp acc_params) (ZEROIZE_MASKED ws).
Proof.
move=> rip ii lvs args m xs ys m' s ops ops'.
move=> ho hexec hwle hops hmap hlom.
rewrite /to_asm /= /assemble_extra /assemble_zeroize_masked in hops.
move: hops; t_xrbindP => -[y1 res1] hy1.
t_xrbindP => -[y2 res2] hy2.
t_xrbindP => x hx hcv hxy1 hxy2.
rewrite /assemble_self_xor => -[?]; subst ops.
(* [args] is literally [[:: rvar y1; rvar y2 & res2]]. *)
have huncons : forall ii' (r : seq rexpr) z zs,
    arm_extra.uncons_rvar ii' r = ok (z, zs) -> r = Rexpr (Fvar z) :: zs
  by move=> ii' [|[|[]]] //= ???? [<- <-].
have ? := huncons _ _ _ _ hy1; subst args.
have ? := huncons _ _ _ _ hy2; subst res1.
case hws: (ws <= U32)%CMP in hmap.
(* Small case: [op = RV32 XOR], [ys = [:: Vword 0]]. [hexec] also pins [xs]
   to exactly two values (the descriptor's [tin] has length two). *)
- move: hexec; rewrite /exec_sopn /sopn_sem /sopn_sem_ /= hws /=.
  case: xs ho => [|v1 [|v2 [|v3 xs3]]] ho //=; [by t_xrbindP | | by t_xrbindP].
  t_xrbindP => t w1 hw1 w2 hw2 ? ?; subst t ys.
  move: ho => /=; t_xrbindP => u1 hgy1 zz u2 hgy2 zs hzs hzz hu1 hzz2.
  subst zz u1; case: hzz2 => ??; subst u2 zs.
  have h := assemble_opsP acc_eval_assemble_cond hmap erefl _ hlom.
  case: (h m') => {h}.
  (* [y2] is read twice and yields the same value, so the self-XOR collapses
     to the zero word and [write_lexprs] is exactly [hwle]. *)
  + rewrite /sem_sopns /= /sem_sopn_t /= hgy2 /=.
    by rewrite /exec_sopn /sopn_sem /sopn_sem_ /= hw2 /= wxor_xx /= hwle.
  by move=> s' hfold hlom'; exists s'.
(* Wide case: [op = BN_basic BN_XOR FG0], three flag outputs before the word;
   at [0] they are [(false, false, true)]. *)
move: hexec; rewrite /exec_sopn /sopn_sem /sopn_sem_ /= hws /=.
case: xs ho => [|v1 [|v2 [|v3 xs3]]] ho //=; [by t_xrbindP | | by t_xrbindP].
t_xrbindP => t w1 hw1 w2 hw2 ? ?; subst t ys.
rewrite /= in hwle.
move: ho => /=; t_xrbindP => u1 hgy1 zz u2 hgy2 zs hzs hzz hu1 hzz2.
subst zz u1; case: hzz2 => ??; subst u2 zs.
have h := assemble_opsP acc_eval_assemble_cond hmap erefl _ hlom.
case: (h m') => {h}.
- rewrite /sem_sopns /= /sem_sopn_t /= hgy2 /=.
  by rewrite /exec_sopn /sopn_sem /sopn_sem_ /= hw2 /= wxor_xx
    /lsb w0E msb0 eqxx /= hwle.
by move=> s' hfold hlom'; exists s'.
Qed.

(* [ExtOp SELECT] assembles to [BN_SEL fg], [fg] the flag group of the
   condition's flag; a negated condition swaps the two sources so the base
   op always tests the un-negated flag. Both ops share the same
   [aword U256; aword U256; abool] argument shape and select-function, so
   once the condition and (for the negated case) the operand order are
   accounted for, the two [exec_sopn] computations agree pointwise. *)
Lemma acc_assemble_SELECT_correct :
  assemble_extra_correct (ap_agp acc_params) SELECT.
Proof.
move=> rip ii lvs args m xs ys m' s ops ops' hrex hexec hwle hops hmap hlom.
move: hops hrex hmap; rewrite /to_asm /= /assemble_extra /assemble_SELECT.
case: args => [|a [|b [|c [|? ?]]]] //=; last by case: c.
case: c => [al ws e|fc] //=.
case: fc => [z|fv|o e|o e1 e2|e1 e2 e3] //=.
- (* [Fvar fv]: non-negated. *)
  case: (of_var fv : option rflag) => [flag|] //=.
  set fg := bn_flag_group_of_rflag flag.
  move=> [<-] hrex hmap.
  move: hrex; rewrite /sem_rexprs /=.
  case Eha: (sem_rexpr (emem m) (evm m) a) => [va|] //=.
  case Ehb: (sem_rexpr (emem m) (evm m) b) => [vb|] //=.
  case Ehfv: (get_var true (evm m) fv) => [vfv|] //=.
  move=> [hxs]; subst xs.
  move: hexec hwle; rewrite /exec_sopn /sopn_sem /sopn_sem_ /=.
  case Ewa: (to_word U256 va) => [wa|] //=.
  case Ewb: (to_word U256 vb) => [wb|] //=.
  case Ebc: (to_bool vfv) => [bc|] //=.
  move=> [<-] hwle.
  have hvs : sem_rexprs m [:: a; b; Rexpr (Fvar fv)] = ok [:: va; vb; vfv].
  - by rewrite /sem_rexprs /= Eha Ehb Ehfv.
  have hys :
    exec_sopn (Oasm (BaseOp (None, BN_SEL fg))) [:: va; vb; vfv]
    = ok [:: Vword (if bc then wa else wb)].
  - by rewrite /exec_sopn /sopn_sem /sopn_sem_ /= Ewa Ewb Ebc.
  have hsopns :
    sem_sopns m [:: ((None, BN_SEL fg), lvs, [:: a; b; Rexpr (Fvar fv)])]
    = ok m'.
  - by rewrite /sem_sopns /sem_sopn_t /foldM hvs /= hys /= hwle.
  have [s' hfold hlom'] :=
    assemble_opsP acc_eval_assemble_cond hmap erefl hsopns hlom.
  by exists s'.
(* [Fapp1 o e]: keep only [Onot], and within it only [Fvar fv]. *)
case: o e => // e.
case: e => [z|fv|o' e'|o' e1' e2'|e1' e2' e3'] //=.
case: (of_var fv : option rflag) => [flag|] //=.
set fg := bn_flag_group_of_rflag flag.
move=> [<-] hrex hmap.
move: hrex.
case Eha: (sem_rexpr (emem m) (evm m) a) => [va|] //=.
case Ehb: (sem_rexpr (emem m) (evm m) b) => [vb|] //=.
case Ehfv: (get_var true (evm m) fv) => [vfv|] //=.
case Ebfv: (sem_sop1 Onot vfv) => [vc|] //=.
move=> [hxs]; subst xs.
move: Ebfv hexec; rewrite /sem_sop1 /=.
case Ebfv: (to_bool vfv) => [bfv|] //=.
move=> [<-] hexec.
move: hexec hwle; rewrite /exec_sopn /sopn_sem /sopn_sem_ /=.
case Ewa: (to_word U256 va) => [wa|] //=.
case Ewb: (to_word U256 vb) => [wb|] //=.
case Ebc: (to_bool (~~ bfv : value)) => [bc|] //=.
move=> [<-] hwle.
have hvs : sem_rexprs m [:: b; a; Rexpr (Fvar fv)] = ok [:: vb; va; vfv].
- by rewrite /sem_rexprs /= Ehb Eha Ehfv.
have hys :
  exec_sopn (Oasm (BaseOp (None, BN_SEL fg))) [:: vb; va; vfv]
  = ok [:: Vword (if ~~ bfv then wa else wb)].
- rewrite /exec_sopn /sopn_sem /sopn_sem_ /= Ewb Ewa Ebfv /=.
  move: Ebfv Ebc hwle; case: bfv => _ _ _; done.
have hsopns :
  sem_sopns m [:: ((None, BN_SEL fg), lvs, [:: b; a; Rexpr (Fvar fv)])]
  = ok m'.
- by rewrite /sem_sopns /sem_sopn_t /foldM hvs /= hys /= hwle.
have [s' hfold hlom'] :=
  assemble_opsP acc_eval_assemble_cond hmap erefl hsopns hlom.
by exists s'.
Qed.

Lemma acc_assemble_extra_op op :
  assemble_extra_correct (ap_agp acc_params) op.
Proof using atoI call_conv sc_sem syscall_state.
  case: op.
  + exact: acc_assemble_set0_correct.
  + exact: acc_assemble_MOV_correct.
  + exact: acc_assemble_NOT_correct.
  + exact: acc_assemble_SUBI_correct.
  + exact: acc_assemble_ADD_LARGE_IMM_correct.
  + exact: acc_assemble_swap_correct.
  + exact: acc_assemble_BN_SELECT_MASKED_correct.
  exact: acc_assemble_ZEROIZE_MASKED_correct.
  exact: acc_assemble_SELECT_correct.
Qed.

Lemma acc_assemble_extra_sz ii op lvs args ops :
  to_asm ii op lvs args = ok ops -> ssrnat.leq 1 (size ops).
Proof.
  rewrite /to_asm /= /assemble_extra /=.
  case: op.
  + move=> ws; rewrite /assemble_set0.
    t_xrbindP => x hx.
    rewrite /assemble_self_xor /=.
    by move=> [<-].
  + rewrite /assemble_MOV.
    case: (arm_extra.uncons_LLvar ii lvs) => // -[x ?].
    case: (arm_extra.uncons_rvar ii args) => // -[y ?].
    simpl; t_xrbindP => _ <-; done.
  + rewrite /assemble_NOT.
    case: (arm_extra.uncons_LLvar ii lvs) => // -[x ?].
    case: (arm_extra.uncons_rvar ii args) => // -[y ?].
    simpl; t_xrbindP => _ <-; done.
  + rewrite /assemble_SUBI.
    case: (arm_extra.uncons_LLvar ii lvs) => // -[x ?].
    case: (arm_extra.uncons_rvar ii args) => // -[y ?].
    simpl; case: (arm_extra.uncons_wconst ii _) => // -[imm ?].
    simpl; t_xrbindP => _ hne args0 hargs <-.
    rewrite /asm_args_of_opn_args size_map.
    move/o2rP: hargs.
    rewrite /acc_params_core.ACCFopn_core.smart_subi
            /acc_params_core.ACCFopn_core.gen_smart_opi.
    case: ifP => // _ [<-].
    rewrite /acc_params_core.ACCFopn_core.gen_unsafe_smart_opi
            /acc_params_core.ACCFopn_core.is_mov /=
            /acc_params_core.ACCFopn_core.smart_mov.
    case: ifP => hmov.
    - case: ifP => hxy //=.
      by move: hne; rewrite hmov hxy.
    - by case: ifP.
  + (* ADD_LARGE_IMM: [v_var x != v_var y] is unconditional (unlike SUBI's
       [imm = 0 \/ x <> y]), so the [is_mov]/[smart_mov] branch never hits
       the [x == y] empty-list case; both branches give a singleton list. *)
    rewrite /assemble_ADD_LARGE_IMM.
    case: (arm_extra.uncons_LLvar ii lvs) => // -[x ?].
    case: (arm_extra.uncons_rvar ii args) => // -[y ?].
    simpl; case: (arm_extra.uncons_wconst ii _) => // -[imm ?].
    simpl.
    t_xrbindP => hxy hc args0 hargs <-.
    rewrite /asm_args_of_opn_args size_map.
    move/o2rP: hargs.
    rewrite /acc_params_core.ACCFopn_core.smart_addi
            /acc_params_core.ACCFopn_core.gen_smart_opi.
    case: ifP => // _ [<-].
    rewrite /acc_params_core.ACCFopn_core.gen_unsafe_smart_opi
            /acc_params_core.ACCFopn_core.is_mov /=
            /acc_params_core.ACCFopn_core.smart_mov.
    case: ifP => hmov.
    - by rewrite (negbTE hxy).
    - by case: ifP.
  + move=> ws; rewrite /assemble_swap.
    case: args => // -[] // [] // z [] // -[] // [] // w [] //.
    simpl; case: ifP => _.
    - case: lvs => // -[] // x [] // -[] // y [] //.
      simpl; t_xrbindP => _ _ _ <-; done.
    - case: ifP => _.
      + case: lvs => // ? [] // ? [] // ? [] // -[] // x [] // -[] // y [] //.
        simpl; t_xrbindP => _ _ _ <-; done.
      + done.
  + rewrite /assemble_bn_select_masked.
    t_xrbindP => -[x le] hx.
    t_xrbindP => -[wn res1] hwn.
    t_xrbindP => -[wm le'] hwm.
    by t_xrbindP => _ <-.
  + move=> ws; rewrite /assemble_zeroize_masked.
    case: (arm_extra.uncons_rvar ii args) => // -[y1 args1].
    simpl; case: (arm_extra.uncons_rvar ii args1) => // -[y2 ?].
    simpl; t_xrbindP => _ _ _ _ _.
    rewrite /assemble_self_xor /=.
    by move=> [<-].
  rewrite /assemble_SELECT.
  case: args => [|a [|b [|c [|? ?]]]] //=; last by case: c.
  case: c => [al ws e|fc] //=.
  case: fc => [z|fv|o e|o e1 e2|e1 e2 e3] //=.
  - by case: (of_var fv : option rflag) => [flag|] //= [<-].
  case: o e => // e.
  case: e => [z|fv|o' e'|o' e1' e2'|e1' e2' e3'] //=.
  by case: (of_var fv : option rflag) => [flag|] //= [<-].
Qed.

Definition acc_hagparams : h_asm_gen_params (ap_agp acc_params) :=
  {|
    hagp_eval_assemble_cond := acc_eval_assemble_cond;
    hagp_assemble_extra_op := acc_assemble_extra_op;
    hagp_assemble_extra_sz := acc_assemble_extra_sz;
  |}.

End ASM_GEN.

(* ------------------------------------------------------------------------ *)
(* SLH. *)

Lemma acc_hshp : slh_lowering_proof.h_sh_params (ap_shp acc_params).
Proof. by constructor; move=> ???? []. Qed.

(* ------------------------------------------------------------------------ *)
(* Stack zeroization. *)

Lemma acc_hszparams :
  stack_zeroization_proof.h_stack_zeroization_params (ap_szp acc_params).
Proof.
  split.
  + exact: acc_stack_zero_cmd_not_ext_lbl.
  exact: acc_stack_zero_cmdP.
Qed.

(* ------------------------------------------------------------------------ *)
(* Shared hypotheses. *)

Lemma acc_is_move_opP op vx v :
  ap_is_move_op acc_params op ->
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

Definition acc_h_params {dc : DirectCall} : h_architecture_params acc_params :=
  {|
    hap_hsap        := acc_hsaparams;
    hap_hlip        := acc_hliparams;
    ok_lip_tmp      := acc_ok_lip_tmp;
    ok_lip_tmp2     := acc_ok_lip_tmp2;
    hap_hlop        := acc_hloparams;
    hap_hlap        := acc_hlaparams;
    hap_hagp        := acc_hagparams;
    hap_hshp        := acc_hshp;
    hap_hszp        := acc_hszparams;
    hap_is_move_opP := acc_is_move_opP;
  |}.

End Section.
