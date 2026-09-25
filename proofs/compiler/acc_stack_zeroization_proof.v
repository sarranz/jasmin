From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype ssralg.
From mathcomp Require Import word_ssrZ.
From Coq Require Import Lia.

Require Import
  expr
  fexpr
  fexpr_sem
  linear
  linear_sem
  linear_facts
  psem
  psem_facts
  low_memory.
Require stack_zeroization_proof.
Require Import
  arch_decl
  arch_extra
  sem_params_of_arch_extra.
Require Import
  acc_decl
  acc_extra
  acc_instr_decl
  acc_params_core_proof.
Require Export acc_stack_zeroization.
Require Import acc_admit.
Import seq_extra.

Set SsrOldRewriteGoalsOrder.  (* change Set to Unset when porting the file, then remove the line when requiring MathComp >= 2.6 *)

(* FIXME: We should use the higher-level [eval_lsem] lemmas. *)
Section FIXME.

Context
  {asm_op syscall_state : Type}
  {ep : EstateParams syscall_state}
  {sip : SemInstrParams asm_op syscall_state}.

#[local]
Lemma find_instr_skip p fn P Q :
  is_linear_of p fn (P ++ Q) ->
  forall scs m vm cs n,
  find_instr p (Lstate scs m vm cs fn (size P + n)) = oseq.onth Q n.
Proof. by eauto using find_instr_skip'. Qed.

End FIXME.

#[local] Existing Instance withsubword.

Section STACK_ZEROIZATION.

Context {atoI : arch_toIdent} {syscall_state : Type} {sc_sem : syscall_sem syscall_state}.
Context {call_conv : calling_convention}.
Context {hwcs_i : hw_call_stack_info}.

Section RSP.

Context (rspn : Ident.ident).
Let rspi := vid rspn.

Let vsaved_sp := mk_var_i (to_var X05).
Let voff := mk_var_i (to_var X06).
Let vzero := mk_var_i (to_var X07).
Let vtmp := mk_var_i (to_var X12).
Let vwzero := mk_var_i (to_var W31).
Let vflags := map (fun f => mk_var_i (to_var f)) [:: MF0; LF0; ZF0 ].

(* Convenience projections of [vflags]'s three entries, used to state
   [set0_wide_eval_instr]'s conclusion without indexing into the list.  Not
   present in [acc_stack_zeroization.v] itself (that file only needs
   [vflags] as a whole); added here for readability. *)
Let vmf := mk_var_i (to_var MF0).
Let vlf := mk_var_i (to_var LF0).
Let vzf := mk_var_i (to_var ZF0).

(* -------------------------------------------------------------------- *)
(* Per-instruction semantics, small clear step ([sw x7, off(v)]). *)
Lemma store_zero_small_eval_instr lp ii (v : var_i) off (ls : lstate)
    (w1 : word Uptr) m' :
  get_var true (lvm ls) (v_var vzero) = ok (@Vword U32 0) ->
  get_var true (lvm ls) (v_var v) = ok (Vword w1) ->
  write (lmem ls) Aligned (w1 + wrepr _ off)%R (sz := U32) 0 = ok m' ->
  let: i := MkLI ii (store_zero U32 v off) in
  linear_sem.eval_instr lp i ls = ok (lnext_pc (lset_mem ls m')).
Proof.
  move=> hvzero hv hm'.
  rewrite /linear_sem.eval_instr /=.
  rewrite hvzero /=.
  rewrite /exec_sopn /sopn_sem /sopn_sem_ /=.
  rewrite hv /= /sem_sop2 /= !truncate_word_u /= !truncate_word_u /=.
  by rewrite hm' /=.
Qed.

(* Per-instruction semantics, large clear step ([bn.sd w31, off(v)]). *)
Lemma store_zero_large_eval_instr lp ii (v : var_i) off (ls : lstate)
    (w1 : word Uptr) m' :
  get_var true (lvm ls) (v_var vwzero) = ok (@Vword U256 0) ->
  get_var true (lvm ls) (v_var v) = ok (Vword w1) ->
  write (lmem ls) Aligned (w1 + wrepr _ off)%R (sz := U256) 0 = ok m' ->
  let: i := MkLI ii (store_zero U256 v off) in
  linear_sem.eval_instr lp i ls = ok (lnext_pc (lset_mem ls m')).
Proof.
  move=> hvwzero hv hm'.
  rewrite /linear_sem.eval_instr /=.
  rewrite hvwzero /=.
  rewrite /exec_sopn /sopn_sem /sopn_sem_ /=.
  rewrite hv /= /sem_sop2 /= !truncate_word_u /= !truncate_word_u /=.
  by rewrite hm' /=.
Qed.

(* Per-instruction semantics of [w31 = #set0_256()], i.e.
   [bn.xor w31, w31, w31, FG0]. *)
Lemma set0_wide_eval_instr lp (ls : lstate) :
  let: vm' :=
    ((((lvm ls).[vmf <- Vbool false])
        .[vlf <- Vbool false])
        .[vzf <- Vbool true])
        .[vwzero <- @Vword U256 0]
  in
  linear_sem.eval_instr lp set0_wide ls = ok (lnext_pc (lset_vm ls vm')).
Proof.
  by rewrite /linear_sem.eval_instr /set0_wide
    /lset_estate' /with_vm /to_estate /lset_vm /lset_mem_vm /lset_estate /=.
Qed.

Context (lp : lprog) (fn : funname) (cs : seq pointer).
Context (ws_align : wsize) (ws : wsize) (stk_max : Z).
Context (lt_0_stk_max : (0 < stk_max)%Z).
Context (halign : is_align stk_max ws).
Context (le_ws_ws_align : (ws <= ws_align)%CMP).
Context (ptr : pointer).
Context (hstack : (stk_max <= wunsigned (align_word ws_align ptr))%Z).
Let top := (align_word ws_align ptr - wrepr Uptr stk_max)%R.

#[local]
Lemma top_aligned : is_align top ws.
Proof using halign le_ws_ws_align.
  rewrite /top.
  apply is_align_add.
  + apply (is_align_m le_ws_ws_align).
    by apply do_align_is_align.
  move: halign; rewrite -WArray.arr_is_align => /is_align_addE <-.
  by rewrite GRing.addrN.
Qed.

Record state_rel_unrolled_small vars s1 s2 n (p : word Uptr) := {
  sr_scs : s1.(escs) = s2.(escs);
  sr_mem : mem_equiv s1.(emem) s2.(emem);
  sr_mem_valid : forall p, between top stk_max p U8 -> validw s2.(emem) Aligned p U8;
  sr_disjoint :
    forall p, disjoint_zrange top stk_max p (wsize_size U8) ->
      read s1.(emem) Aligned p U8 = read s2.(emem) Aligned p U8;
  sr_zero : forall p,
    between (top + wrepr _ n) (stk_max - n) p U8 -> read s2.(emem) Aligned p U8 = ok 0%R;
  sr_vm : s1.(evm) =[\ Sv.add rspi vars] s2.(evm) ;
  sr_vsaved : s2.(evm).[vsaved_sp] = Vword ptr;
  sr_rsp : s2.(evm).[rspi] = Vword p;
  sr_vzero : s2.(evm).[vzero] = @Vword U32 0;
  sr_aligned : is_align n ws;
  sr_bound : (0 <= n <= stk_max)%Z;
}.

Record state_rel_unrolled_large vars s1 s2 n p := {
  srul_wzero : s2.(evm).[vwzero] = @Vword U256 0;
  srul_srs :> state_rel_unrolled_small vars s1 s2 n p;
}.

Record state_rel_loop_small vars s1 s2 n p := {
  srl_off : s2.(evm).[voff] = Vword (wrepr Uptr n);
  srl_srs :> state_rel_unrolled_small vars s1 s2 n p;
}.

Record state_rel_loop_large vars s1 s2 n p := {
  srll_wzero : s2.(evm).[vwzero] = @Vword U256 0;
  srll_srs :> state_rel_loop_small vars s1 s2 n p;
}.

Lemma state_rel_unrolled_smallI vars1 vars2 s1 s2 n p :
  Sv.Subset vars1 vars2 ->
  state_rel_unrolled_small vars1 s1 s2 n p ->
  state_rel_unrolled_small vars2 s1 s2 n p.
Proof.
  move=> hsubset hsr.
  case: hsr => hscs hmem hvalid hdisj hzero hvm hsaved hrsp hvzero haligned hbound.
  split=> //.
  apply: eq_exI hvm.
  by apply (SvD.F.add_s_m erefl hsubset).
Qed.

Lemma state_rel_unrolled_largeI vars1 vars2 s1 s2 n p :
  Sv.Subset vars1 vars2 ->
  state_rel_unrolled_large vars1 s1 s2 n p ->
  state_rel_unrolled_large vars2 s1 s2 n p.
Proof.
  move=> hsubset hsr.
  case: hsr => hwzero hsr.
  split=> //.
  exact: state_rel_unrolled_smallI hsubset hsr.
Qed.

Lemma state_rel_loop_smallI vars1 vars2 s1 s2 n p :
  Sv.Subset vars1 vars2 ->
  state_rel_loop_small vars1 s1 s2 n p ->
  state_rel_loop_small vars2 s1 s2 n p.
Proof.
  move=> hsubset hsr.
  case: hsr => hoff hsr.
  split=> //.
  exact: state_rel_unrolled_smallI hsubset hsr.
Qed.

Lemma state_rel_loop_largeI vars1 vars2 s1 s2 n p :
  Sv.Subset vars1 vars2 ->
  state_rel_loop_large vars1 s1 s2 n p ->
  state_rel_loop_large vars2 s1 s2 n p.
Proof.
  move=> hsubset hsr.
  case: hsr => hwzero hsr.
  split=> //.
  exact: state_rel_loop_smallI hsubset hsr.
Qed.

(* -------------------------------------------------------------------- *)
(* Facts shared by every strategy: none of [sz_init], [set0_wide] or
   [sz_loophw] ever contains an [Llabel], so no strategy's command can jump
   to an external label placed inside them. [sz_unrolled]'s own no-label
   fact is proved directly in [acc_stack_zero_cmd_not_ext_lbl] (Phase 2.6):
   it needs an induction on the [rev (ziota ...)] list, unlike these three,
   which hold by plain computation. *)
Section NO_EXT_LABEL.

Context (lbl : label.label).

Lemma sz_init_no_lbl : ~~ has (is_label lbl) (sz_init rspi ws_align stk_max).
Proof. done. Qed.

Lemma set0_wide_no_lbl : ~~ has (is_label lbl) [:: set0_wide ].
Proof. done. Qed.

Lemma sz_loophw_no_lbl : ~~ has (is_label lbl) (sz_loophw rspi ws stk_max).
Proof. done. Qed.

End NO_EXT_LABEL.

(* -------------------------------------------------------------------- *)
(* Phase 2.3: init and restore. *)
Section INIT.

Definition sz_init_vars :=
  sv_of_list v_var [:: vsaved_sp; voff; vzero ].

Definition sz_init_large_vars :=
  sv_of_list v_var ([:: vsaved_sp; voff; vzero; vwzero ] ++ vflags).

Context (pre pos : seq linstr).
Context (hbody : is_linear_of lp fn (pre ++ sz_init rspi ws_align stk_max ++ pos)).
Context (rsp_nin : ~ Sv.In rspi sz_init_vars).

Lemma sz_initP (s1 : estate) :
  valid_between (emem s1) top stk_max ->
  s1.(evm).[rspi] = Vword ptr ->
  exists s2,
    lsem_n lp (endpc lp fn) (of_estate s1 cs fn (size pre))
      (of_estate s2 cs fn (size pre + size (sz_init rspi ws_align stk_max))) /\
    state_rel_loop_small sz_init_vars s1 s2 stk_max top.
Proof using lt_0_stk_max halign hbody rsp_nin.
  move=> hvalid hrsp.
  move: hbody; rewrite /= => hbody'.
  rewrite /of_estate.

  eexists (Estate _ _ _); split=> /=.
  apply: (lsem_n_eval_lin (n:=0) hbody') => //=.
  + by rewrite addn0.
  + apply: ACCFopn_coreP.mov_eval_instr => //=.
    by rewrite /get_var /= hrsp.
  rewrite /lnext_pc /=; apply: (lsem_n_eval_lin (n:=1) hbody');
   [ done | by rewrite addnC | done | | ].
  + by apply: (ACCFopn_coreP.movi_eval_instr (xi := voff) (imm := stk_max)).
  rewrite /lnext_pc /=; apply: (lsem_n_eval_lin (n:=2) hbody') => //=; first by rewrite addnC.
  + apply: (ACCFopn_coreP.align_eval_instr (al := ws_align)) => //=.
    rewrite get_var_neq; last by move=> /(@inj_to_var _ _ _ _ _ _).
    by rewrite get_var_eq.
  rewrite /lnext_pc /=; apply: (lsem_n_eval_lin (n:=3) hbody') => //=; first by rewrite addnC.
  + apply: ACCFopn_coreP.mov_eval_instr => //=; by rewrite get_var_eq.
  rewrite /lnext_pc /=; apply: (lsem_n_eval_lin (n:=4) hbody') => //=; first by rewrite addnC.
  + apply: ACCFopn_coreP.sub_eval_instr => //=.
    * rewrite get_var_eq /=; last by []. reflexivity.
    rewrite get_var_neq;
      last by move=> h; apply /rsp_nin /sv_of_listP;
      rewrite !in_cons /= -h eqxx /= ?orbT.
    rewrite get_var_neq; last by move=> /esym /(@inj_to_var _ _ _ _ _ _).
    by rewrite get_var_eq //=.

  rewrite /lnext_pc /=; apply: (lsem_n_eval_lin (n:=5) hbody');
   [ done | by rewrite addnC | done | | ].
  + by apply: (ACCFopn_coreP.movi_eval_instr (xi := vzero) (imm := 0)).
  rewrite /lnext_pc /= addnC; apply lsem_n_0.
  split=> /=.
  + do 4 (rewrite Vm.setP_neq;
      last by [
        apply /eqP => /esym /(@inj_to_var _ _ _ _ _ _) |
        apply /eqP => h; apply /rsp_nin /sv_of_listP;
          rewrite !in_cons /= -h eqxx /= ?orbT]).
  by rewrite Vm.setP_eq /=.

  split=> //=.
  + move=> p.
    by rewrite Z.sub_diag /between (negbTE (not_zbetween_neg _ _ _ _)).
  + do 6 (rewrite (eq_ex_set_l _ (eq_ex_refl _));
      last by case; apply Sv.add_spec; (left; reflexivity) ||
      right; apply /sv_of_listP; rewrite !in_cons /= eqxx /= ?orbT).
    by apply eq_ex_refl.
  + do 5 (rewrite Vm.setP_neq;
      last by [
        apply /eqP => /esym /(@inj_to_var _ _ _ _ _ _) |
        apply /eqP => h; apply /rsp_nin /sv_of_listP;
          rewrite !in_cons /= -h eqxx /= ?orbT]).
    by rewrite Vm.setP_eq.
  + rewrite Vm.setP_neq;
      last by apply /eqP => h; apply /rsp_nin /sv_of_listP;
      rewrite !in_cons /= -h eqxx /= ?orbT.
    by rewrite Vm.setP_eq.
  + rewrite Vm.setP_eq /=.
    by rewrite wrepr0.
  by clear -lt_0_stk_max; lia.
Qed.

(* [sz_initP]'s step sequence, restated with an explicit [is_linear_of]
   witness (rather than the section's [hbody]/[rsp_nin]) so it can be
   reused by both [sz_init_largeP] and [sz_init_wsP]'s large branch: those
   need it for a *different* [pos] (the one following [hbody_large], namely
   [[:: set0_wide] ++ pos] or similar), and reusing [hbody]/[rsp_nin]
   directly (a [Proof using] on the section's own [hbody]) would force
   [hbody] and [hbody_large] to agree on the very same [pos], which is
   unsatisfiable once both are discharged at [End INIT]. *)
Local Lemma sz_init_stepsP {pre1 pos1}
    (hbody1 : is_linear_of lp fn (pre1 ++ sz_init rspi ws_align stk_max ++ pos1))
    (rsp_nin1 : ~ Sv.In rspi sz_init_vars) (s1 : estate) :
  valid_between (emem s1) top stk_max ->
  s1.(evm).[rspi] = Vword ptr ->
  exists s2,
    lsem_n lp (endpc lp fn) (of_estate s1 cs fn (size pre1))
      (of_estate s2 cs fn (size pre1 + size (sz_init rspi ws_align stk_max))) /\
    state_rel_loop_small sz_init_vars s1 s2 stk_max top.
Proof using lt_0_stk_max halign.
  move=> hvalid hrsp.
  move: hbody1; rewrite /= => hbody1'.
  rewrite /of_estate.

  eexists (Estate _ _ _); split=> /=.
  apply: (lsem_n_eval_lin (n:=0) hbody1') => //=.
  + by rewrite addn0.
  + apply: ACCFopn_coreP.mov_eval_instr => //=.
    by rewrite /get_var /= hrsp.
  rewrite /lnext_pc /=; apply: (lsem_n_eval_lin (n:=1) hbody1');
   [ done | by rewrite addnC | done | | ].
  + by apply: (ACCFopn_coreP.movi_eval_instr (xi := voff) (imm := stk_max)).
  rewrite /lnext_pc /=; apply: (lsem_n_eval_lin (n:=2) hbody1') => //=; first by rewrite addnC.
  + apply: (ACCFopn_coreP.align_eval_instr (al := ws_align)) => //=.
    rewrite get_var_neq; last by move=> /(@inj_to_var _ _ _ _ _ _).
    by rewrite get_var_eq.
  rewrite /lnext_pc /=; apply: (lsem_n_eval_lin (n:=3) hbody1') => //=; first by rewrite addnC.
  + apply: ACCFopn_coreP.mov_eval_instr => //=; by rewrite get_var_eq.
  rewrite /lnext_pc /=; apply: (lsem_n_eval_lin (n:=4) hbody1') => //=; first by rewrite addnC.
  + apply: ACCFopn_coreP.sub_eval_instr => //=.
    * rewrite get_var_eq /=; last by []. reflexivity.
    rewrite get_var_neq;
      last by move=> h; apply /rsp_nin1 /sv_of_listP;
      rewrite !in_cons /= -h eqxx /= ?orbT.
    rewrite get_var_neq; last by move=> /esym /(@inj_to_var _ _ _ _ _ _).
    by rewrite get_var_eq //=.

  rewrite /lnext_pc /=; apply: (lsem_n_eval_lin (n:=5) hbody1');
   [ done | by rewrite addnC | done | | ].
  + by apply: (ACCFopn_coreP.movi_eval_instr (xi := vzero) (imm := 0)).
  rewrite /lnext_pc /= addnC; apply lsem_n_0.
  split=> /=.
  + do 4 (rewrite Vm.setP_neq;
      last by [
        apply /eqP => /esym /(@inj_to_var _ _ _ _ _ _) |
        apply /eqP => h; apply /rsp_nin1 /sv_of_listP;
          rewrite !in_cons /= -h eqxx /= ?orbT]).
  by rewrite Vm.setP_eq /=.

  split=> //=.
  + move=> p.
    by rewrite Z.sub_diag /between (negbTE (not_zbetween_neg _ _ _ _)).
  + do 6 (rewrite (eq_ex_set_l _ (eq_ex_refl _));
      last by case; apply Sv.add_spec; (left; reflexivity) ||
      right; apply /sv_of_listP; rewrite !in_cons /= eqxx /= ?orbT).
    by apply eq_ex_refl.
  + do 5 (rewrite Vm.setP_neq;
      last by [
        apply /eqP => /esym /(@inj_to_var _ _ _ _ _ _) |
        apply /eqP => h; apply /rsp_nin1 /sv_of_listP;
          rewrite !in_cons /= -h eqxx /= ?orbT]).
    by rewrite Vm.setP_eq.
  + rewrite Vm.setP_neq;
      last by apply /eqP => h; apply /rsp_nin1 /sv_of_listP;
      rewrite !in_cons /= -h eqxx /= ?orbT.
    by rewrite Vm.setP_eq.
  + rewrite Vm.setP_eq /=.
    by rewrite wrepr0.
  by clear -lt_0_stk_max; lia.
Qed.

Context (hbody_large :
  is_linear_of lp fn (pre ++ sz_init_ws rspi ws_align ws stk_max ++ pos)).
Context (rsp_nin_large : ~ Sv.In rspi sz_init_large_vars).
Context (hlarge : ws = U256).

Lemma sz_init_largeP (s1 : estate) :
  valid_between (emem s1) top stk_max ->
  s1.(evm).[rspi] = Vword ptr ->
  exists s2,
    lsem_n lp (endpc lp fn) (of_estate s1 cs fn (size pre))
      (of_estate s2 cs fn (size pre + size (sz_init_ws rspi ws_align ws stk_max))) /\
    state_rel_loop_large sz_init_large_vars s1 s2 stk_max top.
Proof using lt_0_stk_max halign hbody_large rsp_nin_large hlarge.
  move=> hvalid hrsp.
  have hsubset : Sv.Subset sz_init_vars sz_init_large_vars.
  + move=> x /sv_of_listP hin.
    apply /sv_of_listP.
    move: hin; apply: allP.
    by rewrite /= !eqxx ?orbT /=.
  have rsp_nin' : ~ Sv.In rspi sz_init_vars := fun h => rsp_nin_large (hsubset _ h).
  move: hbody_large; rewrite /sz_init_ws hlarge /= => hbody'.
  have [s2 [hsem2 hsr2]] :=
    @sz_init_stepsP pre ([:: set0_wide ] ++ pos) hbody' rsp_nin' s1 hvalid
      hrsp.
  have hsr2' := state_rel_loop_smallI hsubset hsr2.
  exists (Estate (escs s2) (emem s2)
    ((((evm s2).[vmf <- Vbool false]).[vlf <- Vbool false])
      .[vzf <- Vbool true]).[vwzero <- @Vword U256 0]); split=> /=.
  + apply: (lsem_n_trans hsem2).
    rewrite addnS.
    by apply: (lsem_n_eval_lin1 (n:=size (sz_init rspi ws_align stk_max)) hbody').
  split=> /=.
  + by rewrite Vm.setP_eq.
  case: hsr2' => hoff [hscs hmem hvalid2 hdisj hzero hvm hsaved hrsp2 hvzero haligned hbound].
  split=> /=.
  + by do 4 (rewrite Vm.setP_neq; last by []).
  split=> //=.
  + by do 4 (rewrite (eq_ex_set_l _ (eq_ex_refl _));
      last by case; apply Sv.add_spec; right;
      apply /sv_of_listP; rewrite !in_cons /= eqxx /= ?orbT).
  + by do 4 (rewrite Vm.setP_neq; last by []).
  + by do 4 (rewrite Vm.setP_neq; last by []).
  by do 4 (rewrite Vm.setP_neq; last by []).
Qed.

Lemma sz_init_wsP (s1 : estate) :
  is_linear_of lp fn (pre ++ sz_init_ws rspi ws_align ws stk_max ++ pos) ->
  ~ Sv.In rspi (stack_zero_vars ws) ->
  valid_between (emem s1) top stk_max ->
  s1.(evm).[rspi] = Vword ptr ->
  exists s2,
    lsem_n lp (endpc lp fn) (of_estate s1 cs fn (size pre))
      (of_estate s2 cs fn (size pre + size (sz_init_ws rspi ws_align ws stk_max))) /\
    if ws == U256 then state_rel_loop_large (stack_zero_vars ws) s1 s2 stk_max top
    else state_rel_loop_small (stack_zero_vars ws) s1 s2 stk_max top.
Proof using lt_0_stk_max halign le_ws_ws_align hbody rsp_nin.
  move=> hbody0 rsp_nin0 hvalid hrsp.
  case: eqP => [hws | hws].
  + (* ws = U256 *)
    move: hbody0 rsp_nin0 hvalid hrsp.
    rewrite hws => {hws} hbody0 rsp_nin0 hvalid hrsp.
    have hsubset : Sv.Subset sz_init_large_vars (stack_zero_vars U256).
    + move=> x /sv_of_listP hin.
      apply /sv_of_listP.
      move: hin; apply: allP.
      by rewrite /stack_zero_vars /= !eqxx ?orbT /=.
    have rsp_nin_large' : ~ Sv.In rspi sz_init_large_vars :=
      fun h => rsp_nin0 (hsubset _ h).
    have hsubset0 : Sv.Subset sz_init_vars sz_init_large_vars.
    + move=> x /sv_of_listP hin.
      apply /sv_of_listP.
      move: hin; apply: allP.
      by rewrite /= !eqxx ?orbT /=.
    have rsp_nin' : ~ Sv.In rspi sz_init_vars :=
      fun h => rsp_nin_large' (hsubset0 _ h).
    move: hbody0; rewrite /sz_init_ws /= => hbody0'.
    have [s2 [hsem2 hsr2]] :=
      @sz_init_stepsP pre ([:: set0_wide ] ++ pos) hbody0' rsp_nin' s1 hvalid
        hrsp.
    have hsr2' := state_rel_loop_smallI hsubset0 hsr2.
    exists (Estate (escs s2) (emem s2)
      ((((evm s2).[vmf <- Vbool false]).[vlf <- Vbool false])
        .[vzf <- Vbool true]).[vwzero <- @Vword U256 0]); split=> /=.
    + apply: (lsem_n_trans hsem2).
      rewrite addnS.
      by apply: (lsem_n_eval_lin1 (n:=size (sz_init rspi ws_align stk_max)) hbody0').
    apply: (state_rel_loop_largeI hsubset).
    split=> /=.
    + by rewrite Vm.setP_eq.
    case: hsr2' => hoff [hscs hmem hvalid2 hdisj hzero hvm hsaved hrsp2 hvzero
      haligned hbound].
    split=> /=.
    + by do 4 (rewrite Vm.setP_neq; last by []).
    split=> //=.
    + by do 4 (rewrite (eq_ex_set_l _ (eq_ex_refl _));
        last by case; apply Sv.add_spec; right;
        apply /sv_of_listP; rewrite !in_cons /= eqxx /= ?orbT).
    + by do 4 (rewrite Vm.setP_neq; last by []).
    + by do 4 (rewrite Vm.setP_neq; last by []).
    by do 4 (rewrite Vm.setP_neq; last by []).
  (* ws <> U256, hence ws = U32 by the top-level assert *)
  have hf : (ws == U256) = false := negbTE (introN eqP hws).
  have hsubset : Sv.Subset sz_init_vars (stack_zero_vars ws).
  + move=> x /sv_of_listP hin.
    apply /sv_of_listP.
    move: hin; apply: allP.
    by rewrite /stack_zero_vars hf /= !eqxx ?orbT /=.
  have rsp_nin' : ~ Sv.In rspi sz_init_vars := fun h => rsp_nin0 (hsubset _ h).
  move: hbody0; rewrite /sz_init_ws hf /= => hbody0'.
  have [s2 [hsem2 hsr2]] := @sz_init_stepsP pre pos hbody0' rsp_nin' s1 hvalid hrsp.
  have hsr2' := state_rel_loop_smallI hsubset hsr2.
  by exists s2; split.
Qed.

End INIT.

Section RESTORE.

(* We write to [rspi], so we assume that it is different from the variables
   occurring in the invariant predicate. *)
Definition restore_sp_vars :=
  sv_of_list v_var [:: voff; vzero ].

Context (pre pos : seq linstr).
Context (hbody : is_linear_of lp fn (pre ++ restore_sp rspi ++ pos)).
Context (rsp_nin : ~ Sv.In rspi restore_sp_vars).

Lemma restore_spP vars (s1 s2 : estate) :
  state_rel_unrolled_small vars s1 s2 0 top ->
  exists s3,
    lsem_n lp (endpc lp fn)
      (of_estate s2 cs fn (size pre))
      (of_estate s3 cs fn (size pre + size (restore_sp rspi))) /\
    state_rel_unrolled_small vars s1 s3 0 ptr.
Proof using hbody rsp_nin.
  move=> hsr.
  have [hscs hmem hvalid hdisj hzero hvm hsaved hrsp hvzero haligned hbound] := hsr.
  eexists (Estate _ _ _); split=> /=.
  + apply: (lsem_n_eval_lin1 (n:=0) hbody) => //=; first by rewrite addn0.
    rewrite addn1; apply: ACCFopn_coreP.mov_eval_instr => //=.
    by rewrite /get_var /= hsaved /=; reflexivity.
  case: hsr => hscs' hmem' hvalid' hdisj' hzero' hvm' hsaved' hrsp' hvzero' haligned' hbound'.
  split=> //=.
  + by rewrite (eq_ex_set_l _ (eq_ex_refl _));
      last by case; apply Sv.add_spec; left; reflexivity.
  + rewrite Vm.setP /=.
    by case: eq_op.
  + by rewrite Vm.setP_eq.
  + by rewrite Vm.setP_neq;
      last by apply /eqP => h; apply /rsp_nin /sv_of_listP;
      rewrite !in_cons /= -h eqxx /= ?orbT.
Qed.

Lemma restore_sp_largeP vars (s1 s2 : estate) :
  state_rel_unrolled_large vars s1 s2 0 top ->
  exists s3,
    lsem_n lp (endpc lp fn)
      (of_estate s2 cs fn (size pre))
      (of_estate s3 cs fn (size pre + size (restore_sp rspi))) /\
    state_rel_unrolled_large vars s1 s3 0 ptr.
Proof using hbody rsp_nin.
  move=> hsr.
  case: hsr => hwzero hsmall.
  have [hscs hmem hvalid hdisj hzero hvm hsaved hrsp hvzero haligned hbound] := hsmall.
  eexists (Estate _ _ _); split=> /=.
  + apply: (lsem_n_eval_lin1 (n:=0) hbody) => //=; first by rewrite addn0.
    rewrite addn1; apply: ACCFopn_coreP.mov_eval_instr => //=.
    by rewrite /get_var /= hsaved /=; reflexivity.
  split=> /=.
  + by rewrite Vm.setP_neq; last by [].
  case: hsmall => hscs' hmem' hvalid' hdisj' hzero' hvm' hsaved' hrsp' hvzero' haligned' hbound'.
  split=> //=.
  + by rewrite (eq_ex_set_l _ (eq_ex_refl _));
      last by case; apply Sv.add_spec; left; reflexivity.
  + rewrite Vm.setP /=.
    by case: eq_op.
  + by rewrite Vm.setP_eq.
  + by rewrite Vm.setP_neq;
      last by apply /eqP => h; apply /rsp_nin /sv_of_listP;
      rewrite !in_cons /= -h eqxx /= ?orbT.
Qed.

End RESTORE.

(* -------------------------------------------------------------------- *)
(* Phase 2.4: loop. *)
Section LOOP.

Definition sz_loop_vars :=
  sv_of_list v_var [:: voff; vtmp ].

Context (lbl : label.label) (pre pos : seq linstr).
Context (rsp_nin : ~ Sv.In rspi sz_loop_vars).
Context (hlabel : ~~ has (is_label lbl) pre).

(* Memory reasoning for one loop-body store: identical for both clear-step
   widths (the store width [ws] is generic here), so shared between
   [loop_body_smallP] and [loop_body_largeP]. *)
Lemma loop_body_mem vars s1 s2 n :
  state_rel_unrolled_small vars s1 s2 n top ->
  (0 < n)%Z ->
  exists m',
    write (emem s2) Aligned
      (top + (wrepr Uptr n - wrepr Uptr (wsize_size ws)))%R (sz := ws) 0 = ok m'
    /\ mem_equiv (emem s1) m'
    /\ (forall p, between top stk_max p U8 -> validw m' Aligned p U8)
    /\ (forall p, disjoint_zrange top stk_max p (wsize_size U8) ->
          read (emem s1) Aligned p U8 = read m' Aligned p U8)
    /\ (forall p,
          between (top + wrepr _ (n - wsize_size ws))
            (stk_max - (n - wsize_size ws)) p U8 ->
          read m' Aligned p U8 = ok 0%R)
    /\ is_align (n - wsize_size ws)%Z ws
    /\ (0 <= n - wsize_size ws <= stk_max)%Z.
Proof using halign hstack le_ws_ws_align.
  Local Opaque wsize_size.
  move=> hsr hlt.
  have hbound := hsr.(sr_bound).
  have hn : (0 < wsize_size ws <= n)%Z.
  + split=> //.
    have := hsr.(sr_aligned).
    rewrite is_alignE WArray.p_to_zE.
    move=> /eqP /Z.mod_divide [//|m ?].
    have ? := wsize_size_pos ws.
    have: (0 < m)%Z; nia.
  have: validw (emem s2) Aligned
      (top + (wrepr Uptr n - wrepr Uptr (wsize_size ws)))%R ws.
  + apply /validwP; split.
    + rewrite /= (is_align_addE top_aligned).
      have /is_align_addE <- := [elaborate (is_align_mul ws 1)].
      rewrite Z.mul_1_r GRing.addrC GRing.subrK.
      rewrite WArray.arr_is_align.
      by apply hsr.(sr_aligned).
    move=> k hk.
    apply hsr.(sr_mem_valid).
    rewrite /between /zbetween wsize8 !zify addE /top.
    rewrite -wrepr_sub -GRing.addrA -[(_ + wrepr _ k)%R]wrepr_add.
    have h := [elaborate (wunsigned_range (align_word ws_align ptr))].
    by rewrite [_ (_ + _ + _)%R]wunsigned_add; last rewrite wunsigned_sub;
      clear -hstack hn hk hbound h; lia.
  move=> /(writeV 0) [m' hm'].
  exists m'; split=> //.
  split.
  + apply (mem_equiv_trans hsr.(sr_mem)).
    split.
    + by apply (Memory.write_mem_stable hm').
    by move=> ??; symmetry; apply (write_validw_eq hm').
  split.
  + move=> p hb.
    rewrite (write_validw_eq hm').
    by apply hsr.(sr_mem_valid).
  split.
  + move=> p hp.
    rewrite (writeP_neq _ hm'); first by apply hsr.(sr_disjoint).
    apply: disjoint_range_alt.
    apply: disjoint_zrange_incl_l hp.
    rewrite /top /zbetween !zify -wrepr_sub.
    assert (h := wunsigned_range (align_word ws_align ptr)).
    by rewrite wunsigned_add; last rewrite wunsigned_sub;
      clear -hstack hn hbound h; lia.
  split.
  + move=> p hb.
    rewrite (write_read8 hm') subE /=.
    case: ifPn => [_|h].
    + by rewrite LE.read0.
    apply hsr.(sr_zero).
    move: h hb; rewrite /between /zbetween wsize8 !zify /top.
    change acc_reg_size with Uptr.
    rewrite -wrepr_sub -wrepr_opp -!GRing.addrA -!wrepr_add.
    have h := [elaborate (wunsigned_range (align_word ws_align ptr))].
    rewrite wunsigned_sub_if.
    rewrite wunsigned_add; last by clear -hstack hn hbound h; lia.
    rewrite wunsigned_add; last by clear -hstack hbound h; lia.
    change U32 with Uptr in *.
    case: ZleP; clear; lia.
  split.
  + rewrite -WArray.arr_is_align wrepr_sub.
    have /is_align_addE <- := [elaborate (is_align_mul ws 1)].
    rewrite Z.mul_1_r GRing.addrC GRing.subrK.
    rewrite WArray.arr_is_align.
    by apply hsr.(sr_aligned).
  by clear -hn hbound; lia.
  Local Transparent wsize_size.
Qed.

Section SMALL.

Context (hsmall : ws = U32).
Context (hbody : is_linear_of lp fn (pre ++ sz_loop rspi lbl ws ++ pos)).

Lemma loop_body_smallP vars s1 s2 n :
  Sv.Subset sz_loop_vars vars ->
  state_rel_loop_small vars s1 s2 n top ->
  (0 < n)%Z ->
  exists s3,
    [/\ lsem_n lp (endpc lp fn) (of_estate s2 cs fn (size pre + 1))
                (of_estate s3 cs fn (size pre + 4))
      & state_rel_loop_small vars s1 s3 (n - wsize_size ws) top ].
Proof using halign le_ws_ws_align hstack hsmall hbody rsp_nin.
  Local Opaque wsize_size.
  move=> hsubset hsr hlt.
  have [m' [hm' [hmem2 [hvalid2 [hdisj2 [hzero2 [haligned2 hbound2]]]]]]] :=
    loop_body_mem hsr hlt.
  move: hbody; rewrite hsmall => hbody32.
  rewrite hsmall in hm' hmem2 hvalid2 hdisj2 hzero2 haligned2 hbound2 *.
  eexists (Estate _ _ _); split=> /=.
  + apply: (lsem_n_eval_lin (n:=1) hbody32) => //=.
    + apply: (ACCFopn_coreP.subi_eval_instr (imm := wsize_size U32)) => //=.
      by rewrite /get_var /= hsr.(srl_off).
    apply: (lsem_n_eval_lin (n:=2) hbody32) => //=; first by rewrite -addnS.
    + apply: ACCFopn_coreP.add_eval_instr => //=.
      + rewrite get_var_neq;
          last by move=> h; apply /rsp_nin /sv_of_listP;
          rewrite !in_cons /= -h eqxx /= ?orbT.
        by rewrite /get_var /= hsr.(sr_rsp).
      by rewrite get_var_eq.
    apply: (lsem_n_eval_lin (n:=3) hbody32) => //=; first by rewrite -2!addnS.
    + apply: store_zero_small_eval_instr => //=.
      + do 2 (rewrite (@get_var_neq _ _ _ vzero);
          last by [|move=> /(@inj_to_var _ _ _ _ _ _)]).
        by rewrite /get_var hsr.(sr_vzero).
      + by rewrite get_var_eq.
      by rewrite wrepr0 GRing.addr0; exact: hm'.
    by rewrite /lnext_pc /= -!addnS; apply lsem_n_0.
  case: hsr => hoff [hscs hmem1 hvalid1 hdisj1 hzero1 hvm hsaved hrsp hvzero
    haligned1 hbound1].
  split=> /=.
  + rewrite Vm.setP_neq /=;
        last by apply /eqP => /(@inj_to_var _ _ _ _ _ _).
    rewrite Vm.setP_eq /=.
    by rewrite -wrepr_sub.
  split=> //=.
  + by do 2 (rewrite (eq_ex_set_l _ (eq_ex_refl _));
      last by case; apply Sv.add_spec; right;
      apply /hsubset /sv_of_listP; rewrite !in_cons /= eqxx /= ?orbT).
  + by do 2 (rewrite Vm.setP_neq; last by apply /eqP => /(@inj_to_var _ _ _ _ _ _)).
  + by do 2 (rewrite Vm.setP_neq;
      last by apply /eqP => h; apply /rsp_nin /sv_of_listP;
      rewrite !in_cons /= -h eqxx /= ?orbT).
  + by do 2 (rewrite Vm.setP_neq;
      last by [|apply /eqP => /(@inj_to_var _ _ _ _ _ _)]).
  by rewrite hsmall.
  Local Transparent wsize_size.
Qed.

Lemma loop_smallP vars s1 s2 n :
  Sv.Subset sz_loop_vars vars ->
  state_rel_loop_small vars s1 s2 n top ->
  (0 < n)%Z ->
  exists s3,
    [/\ lsem_n lp (endpc lp fn) (of_estate s2 cs fn (size pre + 1))
                (of_estate s3 cs fn (size pre + 5))
      & state_rel_loop_small vars s1 s3 0 top ].
Proof using halign le_ws_ws_align hstack hsmall hbody rsp_nin hlabel.
  Local Opaque wsize_size.
  move=> hsubset hsr hlt.
  have [k hn]: (exists k, n = Z.of_nat k * wsize_size ws)%Z.
  + have := hsr.(sr_aligned).
    rewrite is_alignE WArray.p_to_zE.
    move=> /eqP /Z.mod_divide [//|m h].
    exists (Z.to_nat m).
    rewrite Z2Nat.id //.
    have := wsize_size_pos ws.
    by clear -hlt h; lia.
  elim: k n s2 hsr hlt hn => [|k ih] n s2 hsr hlt hn.
  + move: hn; rewrite Z.mul_0_l.
    by clear -hlt; lia.
  have [s3 [hsem3 hsr3]] := loop_body_smallP hsubset hsr hlt.
  have: (k = 0 \/ 0 < k)%coq_nat by clear; lia.
  case=> hk.
  + subst k.
    move: hn; rewrite Z.mul_1_l => ?; subst n.
    exists s3; split.
    + apply: (lsem_n_step_end hsem3) => //.
      by rewrite /step (find_instr_skip hbody) /= /linear_sem.eval_instr /=
         /get_var hsr3.(srl_off) /= /sem_sop2 /= !truncate_word_u /=
         Z.sub_diag eqxx /= -(addn1 4) addnA addn1; reflexivity.
    by move: hsr3; rewrite Z.sub_diag.
  have hlt3: (0 < n - wsize_size ws)%Z by clear -hlt hn hk; nia.
  have hn3: (n - wsize_size ws)%Z = (Z.of_nat k * wsize_size ws)%Z by clear -hn; lia.
  have [s4 [hsem4 hsr4]] := ih _ _ hsr3 hlt3 hn3.
  exists s4; split=> //.
  apply: (lsem_n_trans hsem3).
  apply: (lsem_n_eval_lin (n:=4) hbody) => //=; last by apply hsem4.
  rewrite /linear_sem.eval_instr /=.
  rewrite /get_var /= hsr3.(srl_off) /= /sem_sop2 /= !truncate_word_u /=.
  have->: (wrepr Uptr (n - wsize_size ws) != wrepr Uptr 0).
  + apply /eqP => /(f_equal wunsigned).
    rewrite wrepr0 wunsigned0 wunsigned_repr_small; first by clear -hlt3; lia.
    have := hsr.(sr_bound).
    have! := (wunsigned_range (align_word ws_align ptr)).
    have := wsize_size_pos ws.
    by clear -hstack hlt3; lia.
  have [lfd -> -> /=] := hbody.
  rewrite (find_label_cat_hd (sip := sip_of_asm_e) _ hlabel).
  rewrite (find_labelE (sip := sip_of_asm_e)) /=.
  rewrite /is_label /= eqxx /=.
  rewrite /setcpc /=.
  by rewrite -addnS.
  Local Transparent wsize_size.
Qed.

Lemma sz_loop_smallP vars s1 s2 n :
  Sv.Subset sz_loop_vars vars ->
  state_rel_loop_small vars s1 s2 n top ->
  (0 < n)%Z ->
  exists s3,
    [/\ lsem_n lp (endpc lp fn)
          (of_estate s2 cs fn (size pre))
          (of_estate s3 cs fn (size pre + size (sz_loop rspi lbl ws)))
      & state_rel_loop_small vars s1 s3 0 top ].
Proof using halign le_ws_ws_align hstack hsmall hbody rsp_nin hlabel.
  move=> hsubset hsr hlt.
  have [s3 [hsem3 hsr3]] := loop_smallP hsubset hsr hlt.
  exists s3; split=> //.
  apply: (lsem_n_eval_lin (n:=0) hbody) => //=.
  + by rewrite addn0.
  rewrite /lnext_pc -addn1; apply hsem3.
Qed.

End SMALL.

Section LARGE.

Context (hlarge : ws = U256).
Context (hbody : is_linear_of lp fn (pre ++ sz_loop rspi lbl ws ++ pos)).

Lemma loop_body_largeP vars s1 s2 n :
  Sv.Subset sz_loop_vars vars ->
  state_rel_loop_large vars s1 s2 n top ->
  (0 < n)%Z ->
  exists s3,
    [/\ lsem_n lp (endpc lp fn) (of_estate s2 cs fn (size pre + 1))
                (of_estate s3 cs fn (size pre + 4))
      & state_rel_loop_large vars s1 s3 (n - wsize_size ws) top ].
Proof using halign le_ws_ws_align hstack hlarge hbody rsp_nin.
  Local Opaque wsize_size.
  move=> hsubset hsr hlt.
  have [m' [hm' [hmem2 [hvalid2 [hdisj2 [hzero2 [haligned2 hbound2]]]]]]] :=
    loop_body_mem hsr hlt.
  move: hbody; rewrite hlarge => hbody256.
  rewrite hlarge in hm' hmem2 hvalid2 hdisj2 hzero2 haligned2 hbound2 *.
  eexists (Estate _ _ _); split=> /=.
  + apply: (lsem_n_eval_lin (n:=1) hbody256) => //=.
    + apply: (ACCFopn_coreP.subi_eval_instr (imm := wsize_size U256)) => //=.
      by rewrite /get_var /= hsr.(srl_off).
    apply: (lsem_n_eval_lin (n:=2) hbody256) => //=; first by rewrite -addnS.
    + apply: ACCFopn_coreP.add_eval_instr => //=.
      + rewrite get_var_neq;
          last by move=> h; apply /rsp_nin /sv_of_listP;
          rewrite !in_cons /= -h eqxx /= ?orbT.
        by rewrite /get_var /= hsr.(sr_rsp).
      by rewrite get_var_eq.
    apply: (lsem_n_eval_lin (n:=3) hbody256) => //=; first by rewrite -2!addnS.
    + apply: store_zero_large_eval_instr => //=.
      + do 2 (rewrite (@get_var_neq _ _ _ vwzero);
          last by [|move=> /(@inj_to_var _ _ _ _ _ _)]).
        by rewrite /get_var hsr.(srll_wzero).
      + by rewrite get_var_eq.
      by rewrite wrepr0 GRing.addr0; exact: hm'.
    by rewrite /lnext_pc /= -!addnS; apply lsem_n_0.
  case: hsr => hwzero [hoff [hscs hmem1 hvalid1 hdisj1 hzero1 hvm hsaved hrsp
    hvzero haligned1 hbound1]].
  split=> /=.
  + by do 2 (rewrite Vm.setP_neq; last by []).
  split=> /=.
  + rewrite Vm.setP_neq /=;
        last by apply /eqP => /(@inj_to_var _ _ _ _ _ _).
    rewrite Vm.setP_eq /=.
    by rewrite -wrepr_sub.
  split=> //=.
  + by do 2 (rewrite (eq_ex_set_l _ (eq_ex_refl _));
      last by case; apply Sv.add_spec; right;
      apply /hsubset /sv_of_listP; rewrite !in_cons /= eqxx /= ?orbT).
  + by do 2 (rewrite Vm.setP_neq; last by apply /eqP => /(@inj_to_var _ _ _ _ _ _)).
  + by do 2 (rewrite Vm.setP_neq;
      last by apply /eqP => h; apply /rsp_nin /sv_of_listP;
      rewrite !in_cons /= -h eqxx /= ?orbT).
  + by do 2 (rewrite Vm.setP_neq;
      last by [|apply /eqP => /(@inj_to_var _ _ _ _ _ _)]).
  by rewrite hlarge.
  Local Transparent wsize_size.
Qed.

Lemma loop_largeP vars s1 s2 n :
  Sv.Subset sz_loop_vars vars ->
  state_rel_loop_large vars s1 s2 n top ->
  (0 < n)%Z ->
  exists s3,
    [/\ lsem_n lp (endpc lp fn) (of_estate s2 cs fn (size pre + 1))
                (of_estate s3 cs fn (size pre + 5))
      & state_rel_loop_large vars s1 s3 0 top ].
Proof using halign le_ws_ws_align hstack hlarge hbody rsp_nin hlabel.
  Local Opaque wsize_size.
  move=> hsubset hsr hlt.
  have [k hn]: (exists k, n = Z.of_nat k * wsize_size ws)%Z.
  + have := hsr.(srll_srs).(srl_srs).(sr_aligned).
    rewrite is_alignE WArray.p_to_zE.
    move=> /eqP /Z.mod_divide [//|m h].
    exists (Z.to_nat m).
    rewrite Z2Nat.id //.
    have := wsize_size_pos ws.
    by clear -hlt h; lia.
  elim: k n s2 hsr hlt hn => [|k ih] n s2 hsr hlt hn.
  + move: hn; rewrite Z.mul_0_l.
    by clear -hlt; lia.
  have [s3 [hsem3 hsr3]] := loop_body_largeP hsubset hsr hlt.
  have: (k = 0 \/ 0 < k)%coq_nat by clear; lia.
  case=> hk.
  + subst k.
    move: hn; rewrite Z.mul_1_l => ?; subst n.
    exists s3; split.
    + apply: (lsem_n_step_end hsem3) => //.
      by rewrite /step (find_instr_skip hbody) /= /linear_sem.eval_instr /=
         /get_var hsr3.(srll_srs).(srl_off) /= /sem_sop2 /= !truncate_word_u /=
         Z.sub_diag eqxx /= -(addn1 4) addnA addn1; reflexivity.
    by move: hsr3; rewrite Z.sub_diag.
  have hlt3: (0 < n - wsize_size ws)%Z by clear -hlt hn hk; nia.
  have hn3: (n - wsize_size ws)%Z = (Z.of_nat k * wsize_size ws)%Z by clear -hn; lia.
  have [s4 [hsem4 hsr4]] := ih _ _ hsr3 hlt3 hn3.
  exists s4; split=> //.
  apply: (lsem_n_trans hsem3).
  apply: (lsem_n_eval_lin (n:=4) hbody) => //=; last by apply hsem4.
  rewrite /linear_sem.eval_instr /=.
  rewrite /get_var /= hsr3.(srll_srs).(srl_off) /= /sem_sop2 /= !truncate_word_u /=.
  have->: (wrepr Uptr (n - wsize_size ws) != wrepr Uptr 0).
  + apply /eqP => /(f_equal wunsigned).
    rewrite wrepr0 wunsigned0 wunsigned_repr_small; first by clear -hlt3; lia.
    have := hsr.(srll_srs).(srl_srs).(sr_bound).
    have! := (wunsigned_range (align_word ws_align ptr)).
    have := wsize_size_pos ws.
    by clear -hstack hlt3; lia.
  have [lfd -> -> /=] := hbody.
  rewrite (find_label_cat_hd (sip := sip_of_asm_e) _ hlabel).
  rewrite (find_labelE (sip := sip_of_asm_e)) /=.
  rewrite /is_label /= eqxx /=.
  rewrite /setcpc /=.
  by rewrite -addnS.
  Local Transparent wsize_size.
Qed.

Lemma sz_loop_largeP vars s1 s2 n :
  Sv.Subset sz_loop_vars vars ->
  state_rel_loop_large vars s1 s2 n top ->
  (0 < n)%Z ->
  exists s3,
    [/\ lsem_n lp (endpc lp fn)
          (of_estate s2 cs fn (size pre))
          (of_estate s3 cs fn (size pre + size (sz_loop rspi lbl ws)))
      & state_rel_loop_large vars s1 s3 0 top ].
Proof using halign le_ws_ws_align hstack hlarge hbody rsp_nin hlabel.
  move=> hsubset hsr hlt.
  have [s3 [hsem3 hsr3]] := loop_largeP hsubset hsr hlt.
  exists s3; split=> //.
  apply: (lsem_n_eval_lin (n:=0) hbody) => //=.
  + by rewrite addn0.
  rewrite /lnext_pc -addn1; apply hsem3.
Qed.

End LARGE.

End LOOP.

Section UNROLLED.

Section SMALL.

Context (hsmall : ws = U32).
Context (pre pos : seq linstr).
Context (hbody : is_linear_of lp fn (pre ++ sz_unrolled rspi ws stk_max ++ pos)).

Lemma unrolled_body_smallP vars s1 s2 n :
  state_rel_unrolled_small vars s1 s2 (stk_max - Z.of_nat n * wsize_size ws) top ->
  (Z.of_nat n < stk_max / wsize_size ws)%Z ->
  exists s3,
    [/\ lsem_n lp (endpc lp fn)
           (of_estate s2 cs fn (size pre + n))
           (of_estate s3 cs fn (size pre + n.+1))
      & state_rel_unrolled_small vars s1 s3
          (stk_max - Z.of_nat n.+1 * wsize_size ws) top ].
Proof using halign le_ws_ws_align hstack hsmall hbody.
  move=> hsr hlt.
  have hpos := wsize_size_pos ws.
  have hstep :
    (Z.of_nat n.+1 * wsize_size ws = Z.of_nat n * wsize_size ws + wsize_size ws)%Z.
  + by rewrite Nat2Z.inj_succ Z.mul_succ_l.
  have hlt' : (0 < Z.of_nat n.+1 * wsize_size ws <= stk_max)%Z.
  + split; first by clear -hpos; lia.
    etransitivity; last by apply (Z.mul_div_le _ (wsize_size ws)).
    rewrite Z.mul_comm; apply Z.mul_le_mono_nonneg_l => //.
    rewrite Nat2Z.inj_succ.
    by apply Z.le_succ_l.
  have hltn : (0 < stk_max - Z.of_nat n * wsize_size ws)%Z.
  + move: hlt'; rewrite hstep; lia.
  have heq :
    (stk_max - Z.of_nat n * wsize_size ws - wsize_size ws
     = stk_max - Z.of_nat n.+1 * wsize_size ws)%Z.
  + rewrite hstep; lia.
  have [m' [hm' [hmem2 [hvalid2 [hdisj2 [hzero2 [haligned2 hbound2]]]]]]] :=
    loop_body_mem hsr hltn.
  have heqw :
    (wrepr Uptr (stk_max - Z.of_nat n * wsize_size ws)
     - wrepr Uptr (wsize_size ws))%R
    = wrepr Uptr (stk_max - Z.of_nat n.+1 * wsize_size ws).
  + by rewrite -wrepr_sub heq.
  rewrite heqw in hm'.
  rewrite heq in hzero2 haligned2 hbound2.
  move: hbody; rewrite hsmall => hbody32.
  rewrite hsmall in hm' hmem2 hvalid2 hdisj2 hzero2 haligned2 hbound2 *.
  eexists (Estate _ _ _); split.
  + apply: (lsem_n_eval_lin1 (n:= n) hbody32) => //.
    + rewrite oseq.onth_cat !size_map size_rev size_ziota.
      have hlt'' : n < Z.to_nat (stk_max / wsize_size U32).
      + by apply /ltP; move: hlt; rewrite hsmall; lia.
      rewrite hlt''.
      rewrite onth_map.
      rewrite oseq.onth_nth (nth_map 0%Z); last by rewrite size_rev size_ziota.
      have -> //:
        (nth 0 (rev (ziota 0 (stk_max / wsize_size U32))) n * wsize_size U32 =
          stk_max - Z.of_nat n.+1 * wsize_size U32)%Z.
      rewrite nth_rev; last by rewrite size_ziota.
      rewrite nth_ziota /=; last first.
      + by rewrite size_ziota -minusE; apply /ltP; move: hlt; rewrite hsmall; lia.
      rewrite size_ziota.
      rewrite Nat2Z.n2zB //.
      rewrite Z2Nat.id; last by move: hlt; rewrite hsmall; lia.
      rewrite Z.mul_sub_distr_r.
      rewrite Z.mul_comm -(proj2 (Z.div_exact _ _ _)) //.
      by move: halign; rewrite hsmall is_alignE WArray.p_to_zE => /eqP.
    rewrite addnS.
    apply: store_zero_small_eval_instr => //=.
    + by rewrite /get_var hsr.(sr_vzero).
    + by rewrite /get_var hsr.(sr_rsp); reflexivity.
    exact: hm'.
  rewrite /lset_mem /=.
  case: hsr => hscs hmem hvalid hdisj hzero hvm hsaved hrsp hvzero haligned hbound.
  split=> //=.
  + rewrite hsmall.
    exact: haligned2.
Qed.

Lemma sz_unrolled_smallP vars s1 s2 :
  state_rel_unrolled_small vars s1 s2 stk_max top ->
  exists s3,
    [/\ lsem_n lp (endpc lp fn)
          (of_estate s2 cs fn (size pre))
          (of_estate s3 cs fn (size pre + size (sz_unrolled rspi ws stk_max)))
      & state_rel_unrolled_small vars s1 s3 0 top ].
Proof using lt_0_stk_max halign le_ws_ws_align hstack hsmall hbody.
  move=> hsr.
  rewrite /sz_unrolled size_map size_rev size_ziota.
  have [k [hmax hbound]]:
    exists k, (stk_max = Z.of_nat k * wsize_size ws)%Z
           /\ k <= Z.to_nat (stk_max / wsize_size ws).
  + have := halign.
    rewrite is_alignE WArray.p_to_zE.
    move=> /eqP /Z.mod_divide [//|m h].
    exists (Z.to_nat m).
    split.
    + rewrite Z2Nat.id //.
      by have := wsize_size_pos ws; clear -lt_0_stk_max h; lia.
    by rewrite h Z.div_mul.
  rewrite -(Z.sub_diag stk_max).
  rewrite {1 3}hmax {hmax}.
  rewrite Z.div_mul // Nat2Z.id.
  elim: k s2 hbound hsr => [|k ih] s2 hbound hsr.
  + rewrite /= addn0 Z.sub_0_r.
    exists s2; split=> //.
    apply lsem_n_0.
  have [s3 [hsem3 hsr3]] := ih _ (ltnW hbound) hsr.
  have hbound': (Z.of_nat k < stk_max / wsize_size ws)%Z.
  + by move/leP: hbound; clear; lia.
  have [s4 [hsem4 hsr4]] := unrolled_body_smallP hsr3 hbound'.
  exists s4; split=> //.
  by apply (lsem_n_trans hsem3).
Qed.

End SMALL.

Section LARGE.

Context (hlarge : ws = U256).
Context (pre pos : seq linstr).
Context (hbody : is_linear_of lp fn (pre ++ sz_unrolled rspi ws stk_max ++ pos)).

Lemma unrolled_body_largeP vars s1 s2 n :
  state_rel_unrolled_large vars s1 s2 (stk_max - Z.of_nat n * wsize_size ws) top ->
  (Z.of_nat n < stk_max / wsize_size ws)%Z ->
  exists s3,
    [/\ lsem_n lp (endpc lp fn)
           (of_estate s2 cs fn (size pre + n))
           (of_estate s3 cs fn (size pre + n.+1))
      & state_rel_unrolled_large vars s1 s3
          (stk_max - Z.of_nat n.+1 * wsize_size ws) top ].
Proof using halign le_ws_ws_align hstack hlarge hbody.
  move=> hsr hlt.
  have hsmall_sr := hsr.(srul_srs).
  have hpos := wsize_size_pos ws.
  have hstep :
    (Z.of_nat n.+1 * wsize_size ws = Z.of_nat n * wsize_size ws + wsize_size ws)%Z.
  + by rewrite Nat2Z.inj_succ Z.mul_succ_l.
  have hlt' : (0 < Z.of_nat n.+1 * wsize_size ws <= stk_max)%Z.
  + split; first by clear -hpos; lia.
    etransitivity; last by apply (Z.mul_div_le _ (wsize_size ws)).
    rewrite Z.mul_comm; apply Z.mul_le_mono_nonneg_l => //.
    rewrite Nat2Z.inj_succ.
    by apply Z.le_succ_l.
  have hltn : (0 < stk_max - Z.of_nat n * wsize_size ws)%Z.
  + move: hlt'; rewrite hstep; lia.
  have heq :
    (stk_max - Z.of_nat n * wsize_size ws - wsize_size ws
     = stk_max - Z.of_nat n.+1 * wsize_size ws)%Z.
  + rewrite hstep; lia.
  have [m' [hm' [hmem2 [hvalid2 [hdisj2 [hzero2 [haligned2 hbound2]]]]]]] :=
    loop_body_mem hsmall_sr hltn.
  have heqw :
    (wrepr Uptr (stk_max - Z.of_nat n * wsize_size ws)
     - wrepr Uptr (wsize_size ws))%R
    = wrepr Uptr (stk_max - Z.of_nat n.+1 * wsize_size ws).
  + by rewrite -wrepr_sub heq.
  rewrite heqw in hm'.
  rewrite heq in hzero2 haligned2 hbound2.
  move: hbody; rewrite hlarge => hbody256.
  rewrite hlarge in hm' hmem2 hvalid2 hdisj2 hzero2 haligned2 hbound2 *.
  eexists (Estate _ _ _); split.
  apply: (lsem_n_eval_lin1 (n:= n) hbody256) => //.
  + rewrite oseq.onth_cat !size_map size_rev size_ziota.
    have hlt'' : n < Z.to_nat (stk_max / wsize_size U256).
    + by apply /ltP; move: hlt; rewrite hlarge; lia.
    rewrite hlt''.
    rewrite onth_map.
    rewrite oseq.onth_nth (nth_map 0%Z); last by rewrite size_rev size_ziota.
    have -> //:
      (nth 0 (rev (ziota 0 (stk_max / wsize_size U256))) n * wsize_size U256 =
        stk_max - Z.of_nat n.+1 * wsize_size U256)%Z.
    rewrite nth_rev; last by rewrite size_ziota.
    rewrite nth_ziota /=; last first.
    + by rewrite size_ziota -minusE; apply /ltP; move: hlt; rewrite hlarge; lia.
    rewrite size_ziota.
    rewrite Nat2Z.n2zB //.
    rewrite Z2Nat.id; last by move: hlt; rewrite hlarge; lia.
    rewrite Z.mul_sub_distr_r.
    rewrite Z.mul_comm -(proj2 (Z.div_exact _ _ _)) //.
    by move: halign; rewrite hlarge is_alignE WArray.p_to_zE => /eqP.
  rewrite addnS.
  apply: store_zero_large_eval_instr => //=.
  + by rewrite /get_var hsr.(srul_wzero).
  + by rewrite /get_var hsmall_sr.(sr_rsp); reflexivity.
  exact: hm'.
  rewrite /lset_mem /=.
  case: hsr => hwzero hsmall_sr'.
  split=> /=.
  + exact hwzero.
  case: hsmall_sr' => hscs hmem hvalid hdisj hzero hvm hsaved hrsp hvzero haligned hbound.
  split=> //=.
  + rewrite hlarge.
    exact: haligned2.
Qed.

Lemma sz_unrolled_largeP vars s1 s2 :
  state_rel_unrolled_large vars s1 s2 stk_max top ->
  exists s3,
    [/\ lsem_n lp (endpc lp fn)
          (of_estate s2 cs fn (size pre))
          (of_estate s3 cs fn (size pre + size (sz_unrolled rspi ws stk_max)))
      & state_rel_unrolled_large vars s1 s3 0 top ].
Proof using lt_0_stk_max halign le_ws_ws_align hstack hlarge hbody.
  move=> hsr.
  rewrite /sz_unrolled size_map size_rev size_ziota.
  have [k [hmax hbound]]:
    exists k, (stk_max = Z.of_nat k * wsize_size ws)%Z
           /\ k <= Z.to_nat (stk_max / wsize_size ws).
  + have := halign.
    rewrite is_alignE WArray.p_to_zE.
    move=> /eqP /Z.mod_divide [//|m h].
    exists (Z.to_nat m).
    split.
    + rewrite Z2Nat.id //.
      by have := wsize_size_pos ws; clear -lt_0_stk_max h; lia.
    by rewrite h Z.div_mul.
  rewrite -(Z.sub_diag stk_max).
  rewrite {1 3}hmax {hmax}.
  rewrite Z.div_mul // Nat2Z.id.
  elim: k s2 hbound hsr => [|k ih] s2 hbound hsr.
  + rewrite /= addn0 Z.sub_0_r.
    exists s2; split=> //.
    apply lsem_n_0.
  have [s3 [hsem3 hsr3]] := ih _ (ltnW hbound) hsr.
  have hbound': (Z.of_nat k < stk_max / wsize_size ws)%Z.
  + by move/leP: hbound; clear; lia.
  have [s4 [hsem4 hsr4]] := unrolled_body_largeP hsr3 hbound'.
  exists s4; split=> //.
  by apply (lsem_n_trans hsem3).
Qed.

End LARGE.

End UNROLLED.

Section STACK_ZERO_LOOP.

Context (hlbl : label.label) (pre pos : seq linstr).
Context (rsp_nin : ~ Sv.In rspi (stack_zero_vars ws)).
Context (hlabel : ~~ has (is_label hlbl) pre).

Context (hbody_small :
  is_linear_of lp fn (pre ++ stack_zero_loop rspi hlbl ws_align ws stk_max ++ pos)).
Context (hsmall : ws = U32).

Lemma stack_zero_loop_smallP (s1 : estate) :
  valid_between (emem s1) top stk_max ->
  (evm s1).[rspi] = Vword ptr ->
  exists s2,
    [/\ lsem_n lp (endpc lp fn)
          (of_estate s1 cs fn (size pre))
          (of_estate s2 cs fn (size pre + size (stack_zero_loop rspi hlbl ws_align ws stk_max)))
      & state_rel_unrolled_small (stack_zero_vars ws) s1 s2 0 ptr ].
Proof using lt_0_stk_max halign le_ws_ws_align hstack hsmall hbody_small rsp_nin hlabel.
  move=> hvalid hrsp.
  have heq : sz_init_ws rspi ws_align ws stk_max = sz_init rspi ws_align stk_max.
  + by rewrite /sz_init_ws hsmall.
  move: hbody_small; rewrite /stack_zero_loop heq -!catA => hbody0.
  have hsubset_init : Sv.Subset sz_init_vars (stack_zero_vars ws).
  + move=> x /sv_of_listP hin.
    apply /sv_of_listP.
    move: hin; apply: allP.
    by rewrite /stack_zero_vars hsmall /= !eqxx ?orbT /=.
  have rsp_nin_init : ~ Sv.In rspi sz_init_vars.
  + by move=> /hsubset_init.
  have [s2 [hsem2 hsr2]] := sz_initP hbody0 rsp_nin_init hvalid hrsp.
  move: hbody0; rewrite catA => hbody1.
  have hsubset_loop : Sv.Subset sz_loop_vars (stack_zero_vars ws).
  + move=> x /sv_of_listP hin.
    apply /sv_of_listP.
    move: hin; apply: allP.
    by rewrite /stack_zero_vars hsmall /= !eqxx ?orbT /=.
  have rsp_nin_loop : ~ Sv.In rspi sz_loop_vars.
  + by move=> /hsubset_loop.
  have hlabel_loop : ~~ has (is_label hlbl) (pre ++ sz_init rspi ws_align stk_max).
  + by rewrite has_cat negb_or hlabel sz_init_no_lbl.
  have hsr2' := state_rel_loop_smallI hsubset_init hsr2.
  have [s3 [hsem3 hsr3]] :=
    sz_loop_smallP rsp_nin_loop hlabel_loop hsmall hbody1 hsubset_loop hsr2'
      lt_0_stk_max.
  move: hbody1; rewrite catA => hbody2.
  have hsubset_restore : Sv.Subset restore_sp_vars (stack_zero_vars ws).
  + move=> x /sv_of_listP hin.
    apply /sv_of_listP.
    move: hin; apply: allP.
    by rewrite /stack_zero_vars hsmall /= !eqxx ?orbT /=.
  have rsp_nin_restore : ~ Sv.In rspi restore_sp_vars.
  + by move=> /hsubset_restore.
  have [s4 [hsem4 hsr4]] := restore_spP hbody2 rsp_nin_restore hsr3.
  exists s4; split=> //.
  apply (lsem_n_trans hsem2).
  rewrite -size_cat.
  apply (lsem_n_trans hsem3).
  rewrite -!size_cat !catA (size_cat _ (restore_sp _)).
  exact: hsem4.
Qed.

Context (hbody_large :
  is_linear_of lp fn (pre ++ stack_zero_loop rspi hlbl ws_align ws stk_max ++ pos)).
Context (hlarge : ws = U256).

Lemma stack_zero_loop_largeP (s1 : estate) :
  valid_between (emem s1) top stk_max ->
  (evm s1).[rspi] = Vword ptr ->
  exists s2,
    [/\ lsem_n lp (endpc lp fn)
          (of_estate s1 cs fn (size pre))
          (of_estate s2 cs fn (size pre + size (stack_zero_loop rspi hlbl ws_align ws stk_max)))
      & state_rel_unrolled_large (stack_zero_vars ws) s1 s2 0 ptr ].
Proof using lt_0_stk_max halign le_ws_ws_align hstack hlarge hbody_large rsp_nin hlabel.
  move=> hvalid hrsp.
  move: hbody_large; rewrite /stack_zero_loop => hbodyX.
  rewrite -[X in pre ++ X]catA in hbodyX.
  have hsubset_init : Sv.Subset sz_init_large_vars (stack_zero_vars ws).
  + move=> x /sv_of_listP hin.
    apply /sv_of_listP.
    move: hin; apply: allP.
    by rewrite /stack_zero_vars hlarge /= !eqxx ?orbT /=.
  have rsp_nin_init : ~ Sv.In rspi sz_init_large_vars.
  + by move=> /hsubset_init.
  have [s2 [hsem2 hsr2]] := sz_init_largeP hbodyX rsp_nin_init hlarge hvalid hrsp.
  move: hbodyX; rewrite catA => hbody1.
  have hsubset_loop : Sv.Subset sz_loop_vars (stack_zero_vars ws).
  + move=> x /sv_of_listP hin.
    apply /sv_of_listP.
    move: hin; apply: allP.
    by rewrite /stack_zero_vars hlarge /= !eqxx ?orbT /=.
  have rsp_nin_loop : ~ Sv.In rspi sz_loop_vars.
  + by move=> /hsubset_loop.
  have hlabel_loop :
      ~~ has (is_label hlbl) (pre ++ sz_init_ws rspi ws_align ws stk_max).
  + by rewrite has_cat negb_or hlabel /sz_init_ws hlarge eqxx has_cat negb_or
      sz_init_no_lbl.
  have hsr2' := state_rel_loop_largeI hsubset_init hsr2.
  have [s3 [hsem3 hsr3]] :=
    sz_loop_largeP rsp_nin_loop hlabel_loop hlarge hbody1 hsubset_loop hsr2'
      lt_0_stk_max.
  rewrite -(catA (sz_loop rspi hlbl ws) (restore_sp rspi) pos) in hbody1.
  rewrite catA in hbody1.
  have hsubset_restore : Sv.Subset restore_sp_vars (stack_zero_vars ws).
  + move=> x /sv_of_listP hin.
    apply /sv_of_listP.
    move: hin; apply: allP.
    by rewrite /stack_zero_vars hlarge /= !eqxx ?orbT /=.
  have rsp_nin_restore : ~ Sv.In rspi restore_sp_vars.
  + by move=> /hsubset_restore.
  have hsr3' : state_rel_unrolled_large (stack_zero_vars ws) s1 s3 0 top :=
    {| srul_wzero := hsr3.(srll_wzero); srul_srs := hsr3 |}.
  have [s4 [hsem4 hsr4]] := restore_sp_largeP hbody1 rsp_nin_restore hsr3'.
  exists s4; split=> //.
  apply (lsem_n_trans hsem2).
  rewrite -size_cat.
  apply (lsem_n_trans hsem3).
  rewrite -!size_cat !catA (size_cat _ (restore_sp _)).
  rewrite /sz_init_ws catA in hsem4; exact: hsem4.
Qed.

End STACK_ZERO_LOOP.

Section STACK_ZERO_UNROLLED.

Context (pre pos : seq linstr).
Context (rsp_nin : ~ Sv.In rspi (stack_zero_vars ws)).

Context (hbody_small :
  is_linear_of lp fn (pre ++ stack_zero_unrolled rspi ws_align ws stk_max ++ pos)).
Context (hsmall : ws = U32).

Lemma stack_zero_unrolled_smallP (s1 : estate) :
  valid_between (emem s1) top stk_max ->
  (evm s1).[rspi] = Vword ptr ->
  exists s2,
    [/\ lsem_n lp (endpc lp fn)
          (of_estate s1 cs fn (size pre))
          (of_estate s2 cs fn (size pre + size (stack_zero_unrolled rspi ws_align ws stk_max)))
      & state_rel_unrolled_small (stack_zero_vars ws) s1 s2 0 ptr ].
Proof using lt_0_stk_max halign le_ws_ws_align hstack hsmall hbody_small rsp_nin.
  move=> hvalid hrsp.
  have heq : sz_init_ws rspi ws_align ws stk_max = sz_init rspi ws_align stk_max.
  + by rewrite /sz_init_ws hsmall.
  move: hbody_small; rewrite /stack_zero_unrolled heq -!catA => hbody0.
  have hsubset_init : Sv.Subset sz_init_vars (stack_zero_vars ws).
  + move=> x /sv_of_listP hin.
    apply /sv_of_listP.
    move: hin; apply: allP.
    by rewrite /stack_zero_vars hsmall /= !eqxx ?orbT /=.
  have rsp_nin_init : ~ Sv.In rspi sz_init_vars.
  + by move=> /hsubset_init.
  have [s2 [hsem2 hsr2]] := sz_initP hbody0 rsp_nin_init hvalid hrsp.
  move: hbody0; rewrite catA => hbody1.
  have hsr2' := state_rel_unrolled_smallI hsubset_init hsr2.
  have [s3 [hsem3 hsr3]] := sz_unrolled_smallP hsmall hbody1 hsr2'.
  move: hbody1; rewrite catA => hbody2.
  have hsubset_restore : Sv.Subset restore_sp_vars (stack_zero_vars ws).
  + move=> x /sv_of_listP hin.
    apply /sv_of_listP.
    move: hin; apply: allP.
    by rewrite /stack_zero_vars hsmall /= !eqxx ?orbT /=.
  have rsp_nin_restore : ~ Sv.In rspi restore_sp_vars.
  + by move=> /hsubset_restore.
  have [s4 [hsem4 hsr4]] := restore_spP hbody2 rsp_nin_restore hsr3.
  exists s4; split=> //.
  apply (lsem_n_trans hsem2).
  rewrite -size_cat.
  apply (lsem_n_trans hsem3).
  rewrite -!size_cat !catA (size_cat _ (restore_sp _)).
  exact: hsem4.
Qed.

Context (hbody_large :
  is_linear_of lp fn (pre ++ stack_zero_unrolled rspi ws_align ws stk_max ++ pos)).
Context (hlarge : ws = U256).

Lemma stack_zero_unrolled_largeP (s1 : estate) :
  valid_between (emem s1) top stk_max ->
  (evm s1).[rspi] = Vword ptr ->
  exists s2,
    [/\ lsem_n lp (endpc lp fn)
          (of_estate s1 cs fn (size pre))
          (of_estate s2 cs fn (size pre + size (stack_zero_unrolled rspi ws_align ws stk_max)))
      & state_rel_unrolled_large (stack_zero_vars ws) s1 s2 0 ptr ].
Proof using lt_0_stk_max halign le_ws_ws_align hstack hlarge hbody_large rsp_nin.
  move=> hvalid hrsp.
  move: hbody_large; rewrite /stack_zero_unrolled => hbodyX.
  rewrite -[X in pre ++ X]catA in hbodyX.
  have hsubset_init : Sv.Subset sz_init_large_vars (stack_zero_vars ws).
  + move=> x /sv_of_listP hin.
    apply /sv_of_listP.
    move: hin; apply: allP.
    by rewrite /stack_zero_vars hlarge /= !eqxx ?orbT /=.
  have rsp_nin_init : ~ Sv.In rspi sz_init_large_vars.
  + by move=> /hsubset_init.
  have [s2 [hsem2 hsr2]] := sz_init_largeP hbodyX rsp_nin_init hlarge hvalid hrsp.
  move: hbodyX; rewrite catA => hbody1.
  have hsr2_ul : state_rel_unrolled_large sz_init_large_vars s1 s2 stk_max top :=
    {| srul_wzero := hsr2.(srll_wzero); srul_srs := hsr2 |}.
  have hsr2' := state_rel_unrolled_largeI hsubset_init hsr2_ul.
  rewrite -(catA (sz_unrolled rspi ws stk_max) (restore_sp rspi) pos) in hbody1.
  have [s3 [hsem3 hsr3]] := sz_unrolled_largeP hlarge hbody1 hsr2'.
  rewrite (catA (pre ++ sz_init_ws rspi ws_align ws stk_max)
    (sz_unrolled rspi ws stk_max) (restore_sp rspi ++ pos)) in hbody1.
  have hsubset_restore : Sv.Subset restore_sp_vars (stack_zero_vars ws).
  + move=> x /sv_of_listP hin.
    apply /sv_of_listP.
    move: hin; apply: allP.
    by rewrite /stack_zero_vars hlarge /= !eqxx ?orbT /=.
  have rsp_nin_restore : ~ Sv.In rspi restore_sp_vars.
  + by move=> /hsubset_restore.
  have [s4 [hsem4 hsr4]] := restore_sp_largeP hbody1 rsp_nin_restore hsr3.
  exists s4; split=> //.
  apply (lsem_n_trans hsem2).
  rewrite -size_cat.
  apply (lsem_n_trans hsem3).
  rewrite -!size_cat !catA (size_cat _ (restore_sp _)).
  rewrite /sz_init_ws catA in hsem4; exact: hsem4.
Qed.

End STACK_ZERO_UNROLLED.

Section STACK_ZERO_LOOPHW.

Context (pre pos : seq linstr).
Context (rsp_nin : ~ Sv.In rspi (stack_zero_vars ws)).
Context (hbody :
  is_linear_of lp fn (pre ++ stack_zero_loophw rspi ws_align ws stk_max ++ pos)).

(* The hardware [Lrepeat_loop] instruction has no semantics in the model
   ([linear_sem.eval_instr] returns [Error ErrSemUndef] on it), so the
   [loophw] strategy is unverified by design (see [proofs/lang/acc_admit.v]). *)
Lemma stack_zero_loophwP (s1 : estate) :
  valid_between (emem s1) top stk_max ->
  (evm s1).[rspi] = Vword ptr ->
  exists s2,
    [/\ lsem_n lp (endpc lp fn)
          (of_estate s1 cs fn (size pre))
          (of_estate s2 cs fn (size pre + size (stack_zero_loophw rspi ws_align ws stk_max)))
      & state_rel_unrolled_small (stack_zero_vars ws) s1 s2 0 ptr ].
Proof using rsp_nin hbody.
  exact: ACC_ADMIT_PROOF.
Qed.

End STACK_ZERO_LOOPHW.

End RSP.

Lemma acc_stack_zero_cmd_not_ext_lbl szs rspn lbl ws_align ws stk_max cmd vars :
  stack_zeroization_cmd szs rspn lbl ws_align ws stk_max = ok (cmd, vars) ->
  label_in_lcmd cmd = [::].
Proof.
  rewrite /stack_zeroization_cmd.
  t_xrbindP=> _.
  case: szs => //.
  + move=> [<- _]; rewrite /stack_zero_loop.
    case: (ws =P U256) => hws; subst.
    + by rewrite /sz_init_ws /sz_loop /restore_sp /store_zero
        /li_of_opn_args /=.
    have hf : (ws == U256) = false := negbTE (introN eqP hws).
    by rewrite /sz_init_ws /sz_loop /restore_sp /store_zero /li_of_opn_args
      hf /=.
  + t_xrbindP=> _ <- _.
    rewrite /stack_zero_unrolled.
    case: (ws =P U256) => hws; subst.
    + rewrite /sz_init_ws /restore_sp /li_of_opn_args !label_in_lcmd_cat
        /= cats0 /sz_unrolled.
      by elim: rev => [//|?? ih] /=.
    have hf : (ws == U256) = false := negbTE (introN eqP hws).
    rewrite /sz_init_ws /restore_sp /li_of_opn_args !label_in_lcmd_cat /=
      hf cats0.
    rewrite /sz_unrolled /store_zero hf /=.
    elim: rev => [//|a l ih] /=.
    by rewrite ih.
  move=> [<- _].
  rewrite /stack_zero_loophw /sz_init_ws /sz_loophw /restore_sp
    /li_of_opn_args.
  by case: ifP => _ /=.
Qed.

Lemma acc_stack_zero_cmdP szs rspn lbl ws_align ws stk_max cmd vars :
  stack_zeroization_cmd szs rspn lbl ws_align ws stk_max = ok (cmd, vars) ->
  stack_zeroization_proof.sz_cmd_spec rspn lbl ws_align ws stk_max cmd vars.
Proof.
  (* [SZSloopHW] is closed by [stack_zero_loophwP]. *)
  move=> hcmd rsp_nin lt_0_stk_max halign le_ws_ws_align lp fn lc
    /negP hlabel hbody ls ptr hfn hpc hstack hrsp top hvalid.
  have [s2 [hsem hsr]]: exists s2,
      lsem_n lp (endpc lp fn) ls
        (of_estate s2 (lhwcs ls) fn (size lc + size cmd))
      /\ state_rel_unrolled_small rspn ws_align ws stk_max ptr vars
           (to_estate ls) s2 0 ptr.
  + move: hcmd; rewrite /stack_zeroization_cmd.
    t_xrbindP=> ws_ok.
    case: szs => //.
    + move=> [??]; subst cmd vars.
      rewrite -(cats0 (stack_zero_loop _ _ _ _ _)) in hbody.
      case/orP: ws_ok => /eqP hws; subst ws.
      + have [s2 [hsem hsr]] :=
          stack_zero_loop_smallP (lhwcs ls) lt_0_stk_max halign le_ws_ws_align
            hstack rsp_nin hlabel hbody erefl (s1 := to_estate ls) hvalid
            hrsp.
        exists s2; split=> //.
        by move: hsem; rewrite -hfn -hpc of_estate_to_estate.
      have [s2 [hsem hsr]] :=
        stack_zero_loop_largeP (lhwcs ls) lt_0_stk_max halign le_ws_ws_align
          hstack rsp_nin hlabel hbody erefl (s1 := to_estate ls) hvalid hrsp.
      exists s2; split.
      + by move: hsem; rewrite -hfn -hpc of_estate_to_estate.
      exact: hsr.
    + t_xrbindP=> _ ??; subst cmd vars.
      rewrite -(cats0 (stack_zero_unrolled _ _ _ _)) in hbody.
      case/orP: ws_ok => /eqP hws; subst ws.
      + have [s2 [hsem hsr]] :=
          stack_zero_unrolled_smallP (lhwcs ls) lt_0_stk_max halign
            le_ws_ws_align hstack rsp_nin hbody erefl (s1 := to_estate ls)
            hvalid hrsp.
        exists s2; split=> //.
        by move: hsem; rewrite -hfn -hpc of_estate_to_estate.
      have [s2 [hsem hsr]] :=
        stack_zero_unrolled_largeP (lhwcs ls) lt_0_stk_max halign
          le_ws_ws_align hstack rsp_nin hbody erefl (s1 := to_estate ls)
          hvalid hrsp.
      exists s2; split.
      + by move: hsem; rewrite -hfn -hpc of_estate_to_estate.
      exact: hsr.
    move=> [??]; subst cmd vars.
    rewrite -(cats0 (stack_zero_loophw _ _ _ _)) in hbody.
    have [s2 [hsem hsr]] :=
      stack_zero_loophwP (lhwcs ls) rsp_nin hbody (s1 := to_estate ls) hvalid
        hrsp.
    exists s2; split.
    + by move: hsem; rewrite -hfn -hpc of_estate_to_estate.
    exact: hsr.
  exists (emem s2), (evm s2); split=> //.
  + by rewrite -{2}hfn /of_estate -hsr.(sr_scs) in hsem.
  + move=> x hin.
    case: (x =P vid rspn) => [->|hneq].
    + by rewrite hsr.(sr_rsp).
    apply hsr.(sr_vm).
    by case/Sv.add_spec.
  + by apply hsr.(sr_mem).
  + have := hsr.(sr_zero).
    by rewrite wrepr0 GRing.addr0 Z.sub_0_r.
  exact: hsr.(sr_disjoint).
Qed.

End STACK_ZEROIZATION.
