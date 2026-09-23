Set Uniform Inductive Parameters.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype order ssralg.
Import
  Order.POrderTheory
  Order.TotalTheory.
From mathcomp Require Import word_ssrZ.

Require Import
  compiler_util
  constant_prop
  constant_prop_proof
  expr
  lowering
  lowering_lemmas
  pseudo_operator
  psem
  psem_facts
  utils.
Require Import
  arch_decl
  arch_extra
  sem_params_of_arch_extra.
Require Import
  acc_decl
  acc_extra
  acc_instr_decl
  acc_lowering.

Set SsrOldRewriteGoalsOrder.  (* change Set to Unset when porting the file, then remove the line when requiring MathComp >= 2.6 *)

Section PROOF.

Context
  {wsw : WithSubWord}
  {dc : DirectCall}
  {atoI : arch_toIdent}
  {syscall_state : Type}
  {sc_sem : syscall_sem syscall_state}
  {pT : progT}
  {sCP : semCallParams}
  (p : prog)
  (ev : extra_val_t)
  (warning : instr_info -> warning_msg -> instr_info)
  (fv : lowering.fresh_vars)
  (fv_correct : fvars_correct fv (p_funcs p)).

Notation lower_i := (lower_i fv).
Notation lower_cmd :=
  (lower_cmd
     (fun _ _ => lower_i)
     warning
     fv).
Notation lower_prog :=
  (lower_prog
     (fun _ _ => lower_i)
     warning
     fv).

(* [lower_cmp]/[lower_Pif]/[lower_copn]/[lower_cassgn_bool] (transitively,
   through [lower_cmp]) and [lower_pexpr]/[lower_cassgn_word] (transitively,
   through [lower_Pif]) all depend on [fv] after [End WITH_PARAMS] in
   acc_lowering.v; abbreviate them here so every statement below can spell
   them as before Stage A. *)
Notation lower_cmp := (lower_cmp fv).
Notation lower_pexpr := (lower_pexpr fv).
Notation lower_cassgn_word := (lower_cassgn_word fv).
Notation lower_Pif := (lower_Pif fv).
Notation lower_copn := (lower_copn fv).
Notation lower_cassgn_bool := (lower_cassgn_bool fv).

Notation fvars := (fvars fv).
Notation disj_fvars := (disj_fvars fvars).

Definition eq_fv := st_eq_ex fvars.

Lemma fvars_CF1 : Sv.In (fvCF1 fv) fvars.
Proof. by repeat (exact: SvD.F.add_1 || apply: SvD.F.add_2). Qed.

Lemma fvars_MF1 : Sv.In (fvMF1 fv) fvars.
Proof. by repeat (exact: SvD.F.add_1 || apply: SvD.F.add_2). Qed.

Lemma fvars_LF1 : Sv.In (fvLF1 fv) fvars.
Proof. by repeat (exact: SvD.F.add_1 || apply: SvD.F.add_2). Qed.

Lemma fvars_ZF1 : Sv.In (fvZF1 fv) fvars.
Proof. by repeat (exact: SvD.F.add_1 || apply: SvD.F.add_2). Qed.

(* [i_of_low_instr]/[c_of_low_cmd] (acc_lowering.v) are section-local and do
   not survive past [End WITH_PARAMS]; these reconstruct them for the
   statements below. *)
Local Definition low_instr_i
  (ii : instr_info) (tag : assgn_tag) (a : acc_args) : instr :=
  let '(lvs, op, es) := a in MkI ii (instr_of_copn_args tag (lvs, Oasm op, es)).

Local Definition low_cmd_c
  (ii : instr_info) (tag : assgn_tag)
  (lc : seq acc_args * seq lval * extended_op * seq pexpr) : cmd :=
  let '(pre, lvs, op, es) := lc in
  map (low_instr_i ii tag) (rcons pre (lvs, op, es)).

(* -------------------------------------------------------------------- *)
Lemma lower_cmd_nil lc : lower_cmd [::] = ok lc -> lc = [::].
Proof. by move=> [<-]. Qed.

Lemma lower_cmd_cons i c lc :
  lower_cmd (i :: c) = ok lc ->
  exists li lc',
    [/\ lower_i i = ok li, lower_cmd c = ok lc' & lc = li ++ lc'].
Proof.
  rewrite /lower_cmd /lowering.lower_cmd /conc_mapM /=.
  t_xrbindP=> _ y py ys pmap <- <-.
  exists y, (flatten ys); split=> //.
  by rewrite pmap.
Qed.

Lemma lower_prog_globs lp : lower_prog p = ok lp -> p_globs lp = p_globs p.
Proof. by rewrite /lower_prog; t_xrbindP=> ? _ <-. Qed.

Lemma lower_prog_extra lp : lower_prog p = ok lp -> p_extra lp = p_extra p.
Proof. by rewrite /lower_prog; t_xrbindP=> ? _ <-. Qed.

Lemma lower_prog_funcs lp :
  lower_prog p = ok lp ->
  map_cfprog (lower_fd (fun _ _ => lower_i) warning fv) (p_funcs p)
  = ok (p_funcs lp).
Proof. by rewrite /lower_prog; t_xrbindP=> fns hfns <-. Qed.

(* [check_shift_amount e = Some sa]: [sa] evaluates (to [U8]) to the shift
   amount, and shifting by [w] equals shifting by [wand n (wrepr U8 31)].
   Proof idea: the [is_wconst] direct case and the [Oland _ a (mask)] case;
   [is_wconstP], [wand_zero_extend]. *)
Lemma check_shift_amountP e sa s z w :
  check_shift_amount e = Some sa ->
  sem_pexpr true (p_globs p) s e = ok z ->
  to_word U8 z = ok w ->
  Sv.Subset (read_e sa) (read_e e) /\
  exists2 n, sem_pexpr true (p_globs p) s sa >>= to_word U8 = ok n
    & forall f (a : word U32),
        sem_shift f a w = sem_shift f a (wand n (wrepr U8 31)).
Proof.
  rewrite /check_shift_amount.
  case en: is_wconst => [ n | ].
  - case: eqP; last by [].
    move => n_in_range /Some_inj <-{sa} ok_z ok_w.
    have hconst := (is_wconstP true (p_globs p) s en).
    specialize (hconst _).
    rewrite ok_z /= in hconst.
    move: ok_w; rewrite hconst => [[?]]; subst w.
    split; first by [].
    exists n; first by rewrite ok_z /= hconst.
    by move=> f a; rewrite -n_in_range.
  case: {en} e => // - [] // sz' a b.
  case en: is_wconst => [ n | ]; last by [].
  case: eqP; last by [].
  move => ? /Some_inj ?; subst sa n.
  apply: rbindP => va ok_va.
  apply: rbindP => vb ok_vb.
  rewrite /sem_sop2 /=.
  t_xrbindP=> wa ok_wa wb ok_wb <-{z} ok_w.
  have hc := (is_wconstP true (p_globs p) s en).
  specialize (hc _).
  have ok_vb_abs : sem_pexpr true (p_globs p) s b = ok vb by exact ok_vb.
  rewrite ok_vb_abs /= in hc.
  have ok_va_abs : sem_pexpr true (p_globs p) s a = ok va by exact ok_va.
  have hwa : to_word U8 va = ok (zero_extend U8 wa)
    by case/to_wordI': ok_wa => sz0 [wa0 [hsz0 -> ->]];
       rewrite /to_word /= truncate_word_le ?zero_extend_idem //; exact: wsize_le_U8.
  split.
  - clear; rewrite {2}/read_e /= !read_eE; SvD.fsetdec.
  eexists; first by rewrite ok_va_abs /= hwa.
  move => f x.
  have hwb : to_word U8 vb = ok (zero_extend U8 wb)
    by case/to_wordI': ok_wb => sz0 [wb0 [hsz0 -> ->]];
       rewrite /to_word /= truncate_word_le ?zero_extend_idem //; exact: wsize_le_U8.
  move: ok_w; rewrite /to_word /= truncate_word_le; last exact: wsize_le_U8.
  move=> /ok_inj <-.
  rewrite hc in hwb; move: hwb => /ok_inj ->; rewrite -wand_zero_extend //; exact: wsize_le_U8.
Qed.

Lemma Hassgn_op2_generic s e1 e2 v1 v2 op2 v ws v' lv s1 (op2' : sopn) :
  sem_pexpr true (p_globs p) s e1 = ok v1 ->
  sem_pexpr true (p_globs p) s e2 = ok v2 ->
  sem_sop2 op2 v1 v2 = ok v ->
  truncate_val (cword ws) v = ok v' ->
  write_lval true (p_globs p) lv v' s = ok s1 ->
  i_valid (sopn.get_instr_desc op2') ->
  forall ws1 ws2 ws3 ws1' ws2'
    (eq1 : type_of_op2 op2 = (aword ws1, aword ws2, aword ws3))
    (eq2 : tin (sopn.get_instr_desc op2') = [:: aword ws1'; aword ws2'])
    (eq3 : tout (sopn.get_instr_desc op2') = [:: aword ws]),
  (ws <= ws3)%CMP
  /\ exists w1 w2, [/\
      to_word ws1 v1 = ok w1,
      to_word ws2 v2 = ok w2 &
      forall e1' e2' w1' w2'
        (hcmp1 : (ws1' <= ws1)%CMP)
        (hcmp2 : (ws2' <= ws2)%CMP),
        sem_pexpr true (p_globs p) s e1' >>= to_word ws1 = ok w1' ->
        sem_pexpr true (p_globs p) s e2' >>= to_word ws2 = ok w2' ->
        Let w := ecast t (let t := t in _) eq1 (sem_sop2_typed op2) w1 w2 in
        ok (zero_extend ws w)
        = ecast l (sem_prod (map eval_atype l) _) eq2
            (ecast l (sem_prod _ (exec (sem_tuple (map eval_atype l)))) eq3
              (semi (sopn.get_instr_desc op2')))
            (zero_extend ws1' w1') (zero_extend ws2' w2') ->
        sem_sopn (p_globs p) op2' s [::lv] [:: e1'; e2'] = ok s1].
Proof.
  move=> ok_v1 ok_v2 ok_v htrunc hwrite hvalid ws1 ws2 ws3 ws1' ws2' eq1 eq2 eq3.
  move: ok_v.
  rewrite /sem_sop2 /=; move: (sem_sop2_typed op2).
  rewrite -> eq1 => /= sem_sop2_typed ok_v.
  rewrite /sem_sopn /= /exec_sopn /= /sopn_sem /sopn_sem_ hvalid /=.
  move: (semi (sopn.get_instr_desc op2')).
  rewrite -> eq2, -> eq3 => semi.
  move: ok_v.
  t_xrbindP=> w1 ok_w1 w2 ok_w2 w ok_w ?; subst.
  move: htrunc; rewrite /truncate_val /=.
  t_xrbindP=> _ /truncate_wordP [hcmp3 ->] ?; subst.
  split=> //.
  rewrite ok_w1 ok_w2 /=.
  exists w1, w2; split=> //.
  t_xrbindP=> e1' e2' w1' w2' hcmp1 hcmp2 v1' ok_v1' ok_w1' v2' ok_v2' ok_w2' eq_sem.
  rewrite ok_v1' ok_v2' /=.
  have hw1' : to_word ws1' v1' = ok (zero_extend ws1' w1').
  { move: ok_w1'; rewrite /to_word.
    case: v1' ok_v1' => // sz1 ww _ /=.
    move/truncate_wordP => [hle1 ->].
    rewrite truncate_word_le; last exact: (cmp_le_trans hcmp1 hle1).
    by rewrite zero_extend_idem.
    by move=> h; case: sz1 ww h => // ?. }
  have hw2' : to_word ws2' v2' = ok (zero_extend ws2' w2').
  { move: ok_w2'; rewrite /to_word.
    case: v2' ok_v2' => // sz2 ww _ /=.
    move/truncate_wordP => [hle2 ->].
    rewrite truncate_word_le; last exact: (cmp_le_trans hcmp2 hle2).
    by rewrite zero_extend_idem.
    by move=> h; case: sz2 ww h => // ?. }
  rewrite hw1' hw2' /=.
  by rewrite -eq_sem ok_w /= /write_lvals /= hwrite.
Qed.

(* -------------------------------------------------------------------- *)
(* Per-construct case lemmas (interface described in the plan above). *)

(* [RV32 SW] (ws <= reg_size) or [BN_SD] (wide).  Stores the value of [e]
   to memory [lv]; no flags ([lvs = [::]]), [es = [:: e]]. *)
Lemma lower_storeP ii ws e lv v v' s0 s1 lvs op es :
  lower_store ii ws e = ok (Some (lvs, op, es)) ->
  sem_pexpr true (p_globs p) s0 e = ok v ->
  truncate_val (cword ws) v = ok v' ->
  write_lval true (p_globs p) lv v' s0 = ok s1 ->
  sem_sopn (p_globs p) (Oasm op) s0 (lvs ++ [:: lv]) es = ok s1.
Proof.
move=> + he htr hw.
rewrite /lower_store.
case: eqP => [?|_].
- subst ws => -[???]; subst lvs op es.
  rewrite /sem_sopn /= he /= /exec_sopn /=.
  have [w [ws' [w' [htw hv hv']]]] := truncate_val_typeE htr.
  subst v v'.
  rewrite /= /to_word htw /= /sopn_sem_ /= /write_lvals /=.
  by rewrite hw.
case: eqP => [?|//]; subst ws => -[???]; subst lvs op es.
rewrite /sem_sopn /= he /= /exec_sopn /=.
have [w [ws' [w' [htw hv hv']]]] := truncate_val_typeE htr.
subst v v'.
rewrite /= /to_word htw /= /sopn_sem_ /= /write_lvals /=.
by rewrite hw.
Qed.

(* Register move [ExtOp MOV] / [BN_MOV] (identity up to [sign_extend_u] /
   [zero_extend_u]) or stack load [RV32 LW] / [BN_LD] when
   [is_var_in_memory].  [lvs = [::]], [es = [:: Pvar gv]]. *)
Lemma lower_PvarP ws gv lv v v' s0 s1 lvs op es :
  lower_Pvar ws gv = ok (Some (lvs, op, es)) ->
  sem_pexpr true (p_globs p) s0 (Pvar gv) = ok v ->
  truncate_val (cword ws) v = ok v' ->
  write_lval true (p_globs p) lv v' s0 = ok s1 ->
  sem_sopn (p_globs p) (Oasm op) s0 (lvs ++ [:: lv]) es = ok s1.
Proof.
move=> + he htr hw.
have hge : get_gvar true (p_globs p) (evm s0) gv = ok v := he.
rewrite /lower_Pvar.
case: eqP => [?|_].
- subst ws.
  case: ifP => _ [???]; subst lvs op es.
  + rewrite /sem_sopn /= /exec_sopn /= hge /=.
    have [w [ws' [w' [htw hv hv']]]] := truncate_val_typeE htr.
    subst v v'.
    rewrite /= /to_word htw /= /sopn_sem_ /= /write_lvals /=.
    by rewrite hw.
  + rewrite /sem_sopn /= /exec_sopn /= hge /=.
    have [w [ws' [w' [htw hv hv']]]] := truncate_val_typeE htr.
    subst v v'.
    by rewrite /= /to_word htw /= /sopn_sem_ /= /write_lvals /= hw.
case: eqP => [?|_]; last by case: ifP.
subst ws; case: ifP => _ [???]; subst lvs op es.
+ rewrite /sem_sopn /= /exec_sopn /= hge /=.
  have [w [ws' [w' [htw hv hv']]]] := truncate_val_typeE htr.
  subst v v'.
  rewrite /= /to_word htw /= /sopn_sem_ /= /write_lvals /=.
  by rewrite hw.
rewrite /sem_sopn /= /exec_sopn /= hge /=.
have [w [ws' [w' [htw hv hv']]]] := truncate_val_typeE htr.
subst v v'.
rewrite /= /to_word htw /= /sopn_sem_ /= /write_lvals /=.
by rewrite hw.
Qed.

(* [RV32 LW] (ws <= reg_size) or [BN_LD] (wide); memory load
   ([sign_extend_u]).  [lvs = [::]], [es = [:: e]].  Displacement checks
   ([get_mem_disp], [chk_*_displacement]) are asserts, semantics-free. *)
Lemma lower_loadP ii ws e lv v v' s0 s1 lvs op es :
  lower_load ii ws e = ok (Some (lvs, op, es)) ->
  sem_pexpr true (p_globs p) s0 e = ok v ->
  truncate_val (cword ws) v = ok v' ->
  write_lval true (p_globs p) lv v' s0 = ok s1 ->
  sem_sopn (p_globs p) (Oasm op) s0 (lvs ++ [:: lv]) es = ok s1.
Proof.
move=> + he htr hw.
rewrite /lower_load.
case: eqP => [?|_].
- subst ws.
  t_xrbindP=> -[] // _ _ [<-] [???]; subst lvs op es.
  rewrite /sem_sopn /= he /= /exec_sopn /=.
  have [w [ws' [w' [htw hv hv']]]] := truncate_val_typeE htr.
  subst v v'.
  rewrite /= /to_word htw /= /sopn_sem_ /= /write_lvals /=.
  by rewrite hw.
case: eqP => [?|//]; subst ws.
t_xrbindP=> -[] // _ _ [<-] [???]; subst lvs op es.
rewrite /sem_sopn /= he /= /exec_sopn /=.
have [w [ws' [w' [htw hv hv']]]] := truncate_val_typeE htr.
subst v v'.
change arch_decl.xreg_size with U256 in htw.
rewrite /= /to_word htw /= /sopn_sem_ /= /write_lvals /=.
by rewrite hw.
Qed.

(* [Oword_of_int] (ws <= reg_size) -> [RV32 LI] (immediate;
   [es = [:: Papp1 op1 e1]]); [Olnot] (ws = xreg_size) -> [BN_NOT FG1] with
   [lvs = lnone_mlz] (3 dummies); [Olnot] (ws = reg_size) -> [ExtOp NOT]
   (i.e. [XORI _, _, -1]); [Oneg] (ws = reg_size) -> [RV32 NEG].
   Other [sop1] are errors (not reached). *)
Lemma lower_Papp1P ii ws op1 e1 lv v v' s0 s1 lvs op es :
  lower_Papp1 ii ws op1 e1 = ok (Some (lvs, op, es)) ->
  sem_pexpr true (p_globs p) s0 (Papp1 op1 e1) = ok v ->
  truncate_val (cword ws) v = ok v' ->
  write_lval true (p_globs p) lv v' s0 = ok s1 ->
  sem_sopn (p_globs p) (Oasm op) s0 (lvs ++ [:: lv]) es = ok s1.
Proof.
move=> + he htr hw.
rewrite /lower_Papp1.
case: op1 he => //= ws'; t_xrbindP=> v0.
- case: eqP => [?|//]; subst ws.
  move=> he ht [???]; subst lvs op es.
  rewrite /sem_sopn /= he /= /exec_sopn /= ht.
  have [w_r [ws'' [w' [htw hv hv']]]] := truncate_val_typeE htr.
  subst v v'.
  rewrite /= /to_word htw /= /sopn_sem_ /= /write_lvals /=.
  by rewrite hw.
- case: eqP => [?|_]; first subst ws.
  + move=> ++ [???]; subst lvs op es.
    have [w_r [ws_v [w' [htw hv hv']]]] := truncate_val_typeE htr.
    subst v v'.
    rewrite /sem_sop1 /=.
    t_xrbindP=> hwe1 we1 heq ?; subst ws_v.
    move=> [?]; subst w'.
    rewrite /sem_sopn /= hwe1 /exec_sopn /= /sopn_sem /sopn_sem_ /=.
    move: we1 htr htw hwe1 heq; case: ws' => //= we1 htr htw hwe1 heq.
    have h_wr : w_r = wnot we1.
    * by have [_ ->] := truncate_wordP htw; apply: zero_extend_u.
    subst w_r.
    by rewrite heq /= /semi_to_atype /= /write_lvals /= /write_none /= hw.
  (* [ws == reg_size]: [ExtOp NOT], mirrors the [Oneg]/[RV32 NEG] case below
     (same [lvs = [::]] / single-argument shape, same cross-width
     [wnot_zero_extend]/[to_wordI']/[zero_extend_idem] reasoning). *)
  case: eqP => [?|//]; subst ws.
  move=> ++ [???]; subst lvs op es.
  have [w_r [ws_v [w' [htw hv hv']]]] := truncate_val_typeE htr.
  subst v v'.
  rewrite /sem_sop1 /=.
  t_xrbindP=> hwe1 we1 heq ?; subst ws_v.
  move=> [?]; subst w'.
  rewrite /sem_sopn /= hwe1 /exec_sopn /= /sopn_sem /sopn_sem_ /=.
  have [hcmp hw_req] := truncate_wordP htw.
  rewrite -(wnot_zero_extend we1 hcmp) in hw_req.
  subst w_r.
  have [sz0 [w0 [hsz0 hv0 hwe1eq]]] := to_wordI' heq.
  subst v0 we1.
  rewrite /to_word /= truncate_word_le; last exact: (cmp_le_trans hcmp hsz0).
  rewrite zero_extend_idem // in hw.
  rewrite /semi_to_atype /=.
  rewrite /write_lvals /=.
  by rewrite hw.
case: ws' => [|ws'] //=.
case: eqP => [?|//]; subst ws.
move=> ++ [???]; subst lvs op es.
have [w_r [ws_v [w' [htw hv hv']]]] := truncate_val_typeE htr.
subst v v'.
rewrite /sem_sop1 /=.
t_xrbindP=> hwe1 we1 heq ?; subst ws_v.
move=> [?]; subst w'.
rewrite /sem_sopn /= hwe1 /exec_sopn /= /sopn_sem /sopn_sem_ /=.
have [hcmp hw_req] := truncate_wordP htw.
rewrite (wopp_zero_extend we1 hcmp) in hw_req.
subst w_r.
have [sz0 [w0 [hsz0 hv0 hwe1eq]]] := to_wordI' heq.
subst v0 we1.
rewrite /to_word /= truncate_word_le; last exact: (cmp_le_trans hcmp hsz0).
rewrite zero_extend_idem // in hw.
rewrite /semi_to_atype /=.
rewrite /write_lvals /=.
by rewrite hw.
Qed.

(* RV32 small case -- shifts [Olsl/Olsr/Oasr] via
   [check_shift_amount] + [Hassgn_op2_shift]; arithmetic via [is_wconst] +
   [Hassgn_op2] (register [ADD/SUB/AND/OR/XOR] or immediate
   [ADDI/.../XORI], with [Osub] materialized as [ADDI (- w)]); [lvs = [::]]. *)
Lemma lower_Papp2_smallP ii op2 a b lv v v' s0 s1 lvs op es :
  lower_Papp2 ii reg_size op2 a b = ok (Some (lvs, op, es)) ->
  sem_pexpr true (p_globs p) s0 (Papp2 op2 a b) = ok v ->
  truncate_val (cword reg_size) v = ok v' ->
  write_lval true (p_globs p) lv v' s0 = ok s1 ->
  sem_sopn (p_globs p) (Oasm op) s0 (lvs ++ [:: lv]) es = ok s1.
Proof.
move=> hlow he htr hw.
move: hlow.
rewrite /lower_Papp2 eqxx /=.
move: he; rewrite /=.
t_xrbindP=> v1 ok_v1 v2 ok_v2 ok_v hlow.
rewrite /lower_Papp2_small in hlow.
case: op2 ok_v hlow => //.
(* Oadd o *)
- move=> o ok_v.
  case: o ok_v => [ok_int | ws ok_v'].
  + by move=> hlow; rewrite /rv_expected_Imn_size /rv_Imn_of_op2 /rv_mn_of_op2 /= in hlow;
       case: (is_wconst U32 b) hlow.
  + rewrite /= /rv_Imn_of_op2 /rv_mn_of_op2.
    case hconst: is_wconst => [w | ] /= hlow.
    * move: hlow; rewrite /lassert /assert.
      case: ifP => //= hsmall [<- <- <-].
      set op2' := Oasm (BaseOp (None, RV32 ADDI)).
      have [hcmp [w1 [w2 [ok_w1 ok_w2 sem_correct]]]] :=
        Hassgn_op2 ok_v1 ok_v2 ok_v' htr hw (op2' := op2') erefl erefl erefl.
      apply sem_correct.
      by rewrite /= wadd_zero_extend //.
    * move: hlow => [] <- <- <-.
      set op2' := Oasm (BaseOp (None, RV32 ADD)).
      have [hcmp [w1 [w2 [ok_w1 ok_w2 sem_correct]]]] :=
        Hassgn_op2 ok_v1 ok_v2 ok_v' htr hw (op2' := op2') erefl erefl erefl.
      apply sem_correct.
      by rewrite /= wadd_zero_extend //.
(* Osub o *)
- move=> o ok_v.
  case: o ok_v => [ok_int | ws ok_v'].
  + by move=> hlow; rewrite /rv_expected_Imn_size /rv_Imn_of_op2 /rv_mn_of_op2 /= in hlow;
       case: (is_wconst U32 b) hlow.
  + rewrite /= /rv_Imn_of_op2 /rv_mn_of_op2.
    case hconst: is_wconst => [w | ] /= hlow.
    * move: hlow; rewrite /lassert /assert.
      case: ifP => //= hsmall.
      case h_insert: insert_minus => [e1' | //].
      move=> [<- <- <-].
      set op2' := Oasm (BaseOp (None, RV32 ADDI)).
      have [hcmp [w1 [w2 [ok_w1 ok_w2 sem_correct]]]] :=
        Hassgn_op2_generic ok_v1 ok_v2 ok_v' htr hw (op2' := op2') erefl erefl erefl.
      rewrite (sem_correct _ _ w1 (- w2)%R) => //.
      + by rewrite ok_v1.
      + apply (minus_insertP h_insert).
        by rewrite ok_v2.
      by rewrite /= sub_wordE wadd_zero_extend.
    * move: hlow => [] <- <- <-.
      set op2' := Oasm (BaseOp (None, RV32 SUB)).
      have [hcmp [w1 [w2 [ok_w1 ok_w2 sem_correct]]]] :=
        Hassgn_op2 ok_v1 ok_v2 ok_v' htr hw (op2' := op2') erefl erefl erefl.
      apply sem_correct.
      by rewrite /semi_to_atype /= sub_wordE wsub_zero_extend //.
(* Oland w *)
- move=> w ok_v.
  rewrite /= /rv_Imn_of_op2 /rv_mn_of_op2.
  case hconst: is_wconst => [wimm | ] /= hlow.
  + move: hlow; rewrite /lassert /assert.
    case: ifP => //= hsmall [<- <- <-].
    set op2' := Oasm (BaseOp (None, RV32 ANDI)).
    have [hcmp [w1 [w2 [ok_w1 ok_w2 sem_correct]]]] :=
      Hassgn_op2 ok_v1 ok_v2 ok_v htr hw (op2' := op2') erefl erefl erefl.
    apply sem_correct.
    by rewrite /= -wand_zero_extend //.
  + move: hlow => [] <- <- <-.
    set op2' := Oasm (BaseOp (None, RV32 AND)).
    have [hcmp [w1 [w2 [ok_w1 ok_w2 sem_correct]]]] :=
      Hassgn_op2 ok_v1 ok_v2 ok_v htr hw (op2' := op2') erefl erefl erefl.
    apply sem_correct.
    by rewrite /= -wand_zero_extend //.
(* Olor w *)
- move=> w ok_v.
  rewrite /= /rv_Imn_of_op2 /rv_mn_of_op2.
  case hconst: is_wconst => [wimm | ] /= hlow.
  + move: hlow; rewrite /lassert /assert.
    case: ifP => //= hsmall [<- <- <-].
    set op2' := Oasm (BaseOp (None, RV32 ORI)).
    have [hcmp [w1 [w2 [ok_w1 ok_w2 sem_correct]]]] :=
      Hassgn_op2 ok_v1 ok_v2 ok_v htr hw (op2' := op2') erefl erefl erefl.
    apply sem_correct.
    by rewrite /= -wor_zero_extend //.
  + move: hlow => [] <- <- <-.
    set op2' := Oasm (BaseOp (None, RV32 OR)).
    have [hcmp [w1 [w2 [ok_w1 ok_w2 sem_correct]]]] :=
      Hassgn_op2 ok_v1 ok_v2 ok_v htr hw (op2' := op2') erefl erefl erefl.
    apply sem_correct.
    by rewrite /= -wor_zero_extend //.
(* Olxor w *)
- move=> w ok_v.
  rewrite /= /rv_Imn_of_op2 /rv_mn_of_op2.
  case hconst: is_wconst => [wimm | ] /= hlow.
  + move: hlow; rewrite /lassert /assert.
    case: ifP => //= hsmall [<- <- <-].
    set op2' := Oasm (BaseOp (None, RV32 XORI)).
    have [hcmp [w1 [w2 [ok_w1 ok_w2 sem_correct]]]] :=
      Hassgn_op2 ok_v1 ok_v2 ok_v htr hw (op2' := op2') erefl erefl erefl.
    apply sem_correct.
    by rewrite /= -wxor_zero_extend //.
  + move: hlow => [] <- <- <-.
    set op2' := Oasm (BaseOp (None, RV32 XOR)).
    have [hcmp [w1 [w2 [ok_w1 ok_w2 sem_correct]]]] :=
      Hassgn_op2 ok_v1 ok_v2 ok_v htr hw (op2' := op2') erefl erefl erefl.
    apply sem_correct.
    by rewrite /= -wxor_zero_extend //.
(* Olsr w *)
- move=> w ok_v.
  case: w ok_v => // ok_v.
  rewrite /lower_shift.
  case good_shift: (check_shift_amount b) => [ sa | ] //.
  move=> [<- <- <-].
  rewrite !fun_if if_same.
  set op2' := Oasm _.
  have [_ [w1 [w2 [ok_w1 ok_w2 sem_correct]]]] :=
    Hassgn_op2_shift ok_v1 ok_v2 ok_v htr hw (op2' := op2') erefl erefl erefl.
  have [_ [wa ok_wa eq_shift]] := check_shift_amountP good_shift ok_v2 ok_w2.
  rewrite (sem_correct _ _ ok_wa) //= !zero_extend_u /sem_shr eq_shift.
  by rewrite /sem_shift /semi_to_atype /= (wand_modulo wa 5) -Z.land_ones.
(* Olsl o *)
- move=> [|w] ok_v //.
  rewrite /lower_shift.
  case good_shift: (check_shift_amount b) => [ sa | ] //.
  move=> [<- <- <-].
  rewrite !fun_if if_same.
  set op2' := Oasm _.
  have [hcmp [w1 [w2 [ok_w1 ok_w2 sem_correct]]]] :=
    Hassgn_op2_shift ok_v1 ok_v2 ok_v htr hw (op2' := op2') erefl erefl erefl.
  have [_ [wa ok_wa eq_shift]] := check_shift_amountP good_shift ok_v2 ok_w2.
  rewrite (sem_correct _ _ ok_wa) //=.
  rewrite /sem_shl /= zero_extend_wshl //;
    last by have [? _] := wunsigned_range w2.
  by rewrite -/(sem_shift _ _ _) eq_shift /sem_shift /semi_to_atype /=
       (wand_modulo wa 5) -Z.land_ones.
(* Oasr o *)
- move=> [|[]] // ok_v.
  rewrite /lower_shift.
  case good_shift: (check_shift_amount b) => [ sa | ] //.
  move=> [<- <- <-].
  rewrite !fun_if if_same.
  set op2' := Oasm _.
  have [_ [w1 [w2 [ok_w1 ok_w2 sem_correct]]]] :=
    Hassgn_op2_shift ok_v1 ok_v2 ok_v htr hw (op2' := op2') erefl erefl erefl.
  have [_ [wa ok_wa eq_shift]] := check_shift_amountP good_shift ok_v2 ok_w2.
  rewrite (sem_correct _ _ ok_wa) //= !zero_extend_u /sem_sar eq_shift.
  by rewrite /sem_shift /semi_to_atype /= (wand_modulo wa 5) -Z.land_ones.
Qed.

(* Wide case: [BN_ADDI/BN_SUBI FG0] (immediate) or [BN_ADD/BN_SUB FG0]
   ([lvs = lnone_cmlz]) / [BN_AND/BN_OR/BN_XOR FG0] ([lvs = lnone_mlz]);
   reuse the [with_cmlz] / [with_mlz] result projection + [write_none] from
   [lower_carry_opP] ([waddsubcarry_cmlzP] is available if a flag value is
   ever needed, but here all flags go to dummies).  Small case fixes
   width [U32]. *)
Lemma lower_Papp2_largeP ii op2 a b lv v v' s0 s1 lvs op es :
  lower_Papp2 ii xreg_size op2 a b = ok (Some (lvs, op, es)) ->
  sem_pexpr true (p_globs p) s0 (Papp2 op2 a b) = ok v ->
  truncate_val (cword xreg_size) v = ok v' ->
  write_lval true (p_globs p) lv v' s0 = ok s1 ->
  sem_sopn (p_globs p) (Oasm op) s0 (lvs ++ [:: lv]) es = ok s1.
Proof.
move=> hlow he htr hw.
move: he; rewrite /=; t_xrbindP=> v1 ok_v1 v2 ok_v2 ok_v.
have [w [ws' [w' [htw hv hv']]]] := truncate_val_typeE htr.
subst v v'.
have hle' : (U256 <= ws')%CMP by exact: (truncate_wordP htw).1.
have hws' : ws' = U256 := cmp_le_antisym (wsize_ge_U256 ws') hle'.
subst ws'.
move: htw; rewrite truncate_word_u => heq_tw; injection heq_tw as <-.
rewrite /lower_Papp2 in hlow.
have hneq : (xreg_size == reg_size) = false by vm_compute.
rewrite hneq eqxx /lower_Papp2_large in hlow.
move: hlow; case: (isSome (is_wconst xreg_size b)).
- rewrite /acc_Iop_of_op2.
  case: op2 ok_v => // -[] // ws.
  + move=> ok_v [???]; subst lvs op es.
    move: ok_v; rewrite /sem_sop2 /=.
    t_xrbindP=> bw0 hbw0 bw1 hbw1 ?; subst ws.
    move=> [?]; subst w'.
    rewrite /sem_sopn /= ok_v1 ok_v2 /= /exec_sopn /= /sopn_sem /sopn_sem_ /=.
    rewrite /type_of_opk /eval_atype /= in hbw0 hbw1.
    rewrite hbw0 hbw1 /= /semi_binopI_cmlz /semi_to_atype /=.
    cbn [sem_ot eval_ltype ty_mlz ty_cmlz ltuple with_cmlz add_tuple with_mlz].
    by change (wadd bw0 bw1) with ((bw0 + bw1)%w); rewrite hw.
  + move=> ok_v [???]; subst lvs op es.
    move: ok_v; rewrite /sem_sop2 /=.
    t_xrbindP=> bw0 hbw0 bw1 hbw1 ?; subst ws.
    move=> [?]; subst w'.
    rewrite /sem_sopn /= ok_v1 ok_v2 /= /exec_sopn /= /sopn_sem /sopn_sem_ /=.
    rewrite /type_of_opk /eval_atype /= in hbw0 hbw1.
    rewrite hbw0 hbw1 /= /semi_binopI_cmlz /semi_to_atype /=.
    cbn [sem_ot eval_ltype ty_mlz ty_cmlz ltuple with_cmlz add_tuple with_mlz].
    by rewrite /wsub -sub_wordE hw /=.
- rewrite /acc_op_of_op2.
  case: op2 ok_v => //.
  + move=> [] // ws + [<- <- <-]; rewrite /sem_sop2 /=.
    t_xrbindP=> bw0 hbw0 bw1 hbw1 ?; subst ws.
    move=> [?]; subst w'.
    rewrite /type_of_opk /eval_atype /= in hbw0 hbw1.
    rewrite /sem_sopn /= ok_v1 ok_v2 /= /exec_sopn /= /sopn_sem /sopn_sem_ /=.
    rewrite hbw0 hbw1 /=.
    cbn [sem_ot eval_ltype ty_mlz ty_cmlz ltuple with_cmlz add_tuple with_mlz].
    change (wadd bw0 bw1) with ((bw0 + bw1)%w).
    by rewrite hw /=.
  + move=> [] // ws + [<- <- <-]; rewrite /sem_sop2 /=.
    t_xrbindP => bw0 hbw0 bw1 hbw1 ?; subst ws.
    move=> [?]; subst w'.
    rewrite /type_of_opk /eval_atype /= in hbw0 hbw1.
    rewrite /sem_sopn /= ok_v1 ok_v2 /= /exec_sopn /= /sopn_sem /sopn_sem_ /=.
    rewrite hbw0 hbw1 /=.
    cbn [sem_ot eval_ltype ty_mlz ty_cmlz ltuple with_cmlz add_tuple with_mlz].
    by rewrite /wsub -sub_wordE hw /=.
  + move=> ws + [<- <- <-]; rewrite /sem_sop2 /=.
    t_xrbindP => bw0 hbw0 bw1 hbw1 ?; subst ws.
    move=> [?]; subst w'.
    rewrite /sem_sopn /= ok_v1 ok_v2 /= /exec_sopn /= /sopn_sem /sopn_sem_ /=.
    rewrite hbw0 hbw1 /=.
    cbn [sem_ot eval_ltype ty_mlz ty_cmlz ltuple with_mlz add_tuple with_cmlz].
    by rewrite /write_none /= hw /=.
  + move=> ws + [<- <- <-]; rewrite /sem_sop2 /=.
    t_xrbindP => bw0 hbw0 bw1 hbw1 ?; subst ws.
    move=> [?]; subst w'.
    rewrite /sem_sopn /= ok_v1 ok_v2 /= /exec_sopn /= /sopn_sem /sopn_sem_ /=.
    rewrite hbw0 hbw1 /=.
    cbn [sem_ot eval_ltype ty_mlz ty_cmlz ltuple with_mlz add_tuple with_cmlz].
    by rewrite /write_none /= hw /=.
  + move=> ws + [<- <- <-]; rewrite /sem_sop2 /=.
    t_xrbindP => bw0 hbw0 bw1 hbw1 ?; subst ws.
    move=> [?]; subst w'.
    rewrite /sem_sopn /= ok_v1 ok_v2 /= /exec_sopn /= /sopn_sem /sopn_sem_ /=.
    rewrite hbw0 hbw1 /=.
    cbn [sem_ot eval_ltype ty_mlz ty_cmlz ltuple with_mlz add_tuple with_cmlz].
    by rewrite /write_none /= hw /=.
Qed.

Lemma lower_Papp2P ii ws op2 a b lv v v' s0 s1 lvs op es :
  lower_Papp2 ii ws op2 a b = ok (Some (lvs, op, es)) ->
  sem_pexpr true (p_globs p) s0 (Papp2 op2 a b) = ok v ->
  truncate_val (cword ws) v = ok v' ->
  write_lval true (p_globs p) lv v' s0 = ok s1 ->
  sem_sopn (p_globs p) (Oasm op) s0 (lvs ++ [:: lv]) es = ok s1.
Proof.
rewrite /lower_Papp2.
case: eqP => [?|_].
- subst ws; exact: lower_Papp2_smallP.
case: eqP => [?|//]; subst; exact: lower_Papp2_largeP.
Qed.

(* [waddsubcarry_cmlzP]: the wide-carry op's flag and result match the
   pseudo-op's [waddcarry]/[wsubcarry].  The carry-out [CF_of_Z z] (= [Some]
   of bit 256 of [z]) equals the boolean carry, and the wide result equals
   the word result.  Idea (cf. ARM [wunsigned_carry], proving
   [(wbase <=? res') = (res != res')]): additionally relate [CF_of_Z]'s
   bit-256 extraction to that overflow predicate -- for
   [z = wunsigned x +/- wunsigned y +/- b2z c], [z] stays in a range where
   bit 256 equals [wbase <=? z] (add) / the borrow (sub).  Pure word/[Z]
   arithmetic: [wunsigned_range], [wbase] bounds, [wrepr]/[wunsigned]
   round-trips, [lia]. *)
Lemma waddsubcarry_cmlzP is_add (x y : word arch_decl.xreg_size) (c : bool) :
  let fZ := if is_add then Z.add else Z.sub in
  let fw := if is_add then +%R else (fun a b => a - b)%R in
  CF_of_Z (fZ (fZ (wunsigned x) (wunsigned y)) (Z.b2z c))
  = Some (if is_add then (waddcarry x y c).1 else (wsubcarry x y c).1)
  /\ fw (fw x y) (wrepr arch_decl.xreg_size (Z.b2z c))
     = (if is_add then (waddcarry x y c).2 else (wsubcarry x y c).2).
Proof.
  case: is_add => /=; split.
  - (* add CF *)
    rewrite /CF_of_Z; congr Some; rewrite Z.shiftr_div_pow2 //.
    have hx := wunsigned_range x.
    have hy := wunsigned_range y.
    have hb : (0 <= Z.b2z c <= 1)%Z by case: c.
    have hbas : (wbase arch_decl.xreg_size = 2^256)%Z by vm_compute.
    have hbas256 : (wbase U256 = 2^256)%Z by vm_compute.
    case: ZleP => hz.
    + have hq : ((wunsigned x + wunsigned y + Z.b2z c) / 2^256 = 1)%Z.
        have h1 : (1 <= (wunsigned x + wunsigned y + Z.b2z c) / 2^256)%Z.
          apply Z.div_le_lower_bound; first by vm_compute.
          by rewrite Z.mul_1_r -hbas256.
        have h2 : ((wunsigned x + wunsigned y + Z.b2z c) / 2^256 < 2)%Z.
          apply Z.div_lt_upper_bound; first by vm_compute.
          by move: hx hy hb hbas; t_lia.
        by move: h1 h2; t_lia.
      by rewrite hq; vm_compute.
    + have hq : ((wunsigned x + wunsigned y + Z.b2z c) / 2^256 = 0)%Z.
        apply Z.div_small; split; first by move: hx hy hb; t_lia.
        move: hz => /Z.lt_nge hz; rewrite -hbas256; exact hz.
      by rewrite hq; vm_compute.
  - by rewrite wrepr_add wrepr_add wrepr_unsigned wrepr_unsigned.
  - (* sub CF *)
    rewrite /CF_of_Z; congr Some; rewrite Z.shiftr_div_pow2 //.
    have hx := wunsigned_range x.
    have hy := wunsigned_range y.
    have hb : (0 <= Z.b2z c <= 1)%Z by case: c.
    have hbas : (wbase arch_decl.xreg_size = 2^256)%Z by vm_compute.
    case: ZltP => hz.
    + have hq : ((wunsigned x - wunsigned y - Z.b2z c) / 2^256 = -1)%Z.
        have h1 : ((wunsigned x - wunsigned y - Z.b2z c) / 2^256 < 0)%Z.
          apply Z.div_lt_upper_bound; first by vm_compute.
          rewrite Z.mul_0_r; exact hz.
        have h2 : (-1 <= (wunsigned x - wunsigned y - Z.b2z c) / 2^256)%Z.
          apply Z.div_le_lower_bound; first by vm_compute.
          by move: hx hy hb hbas; t_lia.
        by move: h1 h2; t_lia.
      by rewrite hq; vm_compute.
    + have hq : ((wunsigned x - wunsigned y - Z.b2z c) / 2^256 = 0)%Z.
        apply Z.div_small; split.
        + move: hz => /Z.le_ngt hz; exact hz.
        + by move: hx hy hb hbas; t_lia.
      by rewrite hq; vm_compute.
  - by rewrite wrepr_sub wrepr_sub wrepr_unsigned wrepr_unsigned.
Qed.

(* [CF_of_Z_subP]/[ZF_of_word_subP]: the two flag facts [BN.CMP] needs out of
   the descriptor semantics [with_cmlz (x - y) (wunsigned x - wunsigned y)]
   (Facts 2.).  [CF_of_Z_subP] specializes [waddsubcarry_cmlzP] to
   [is_add := false], [c := false] rather than redoing the [Z.div_*]
   derivation.  [M]/[L] are never needed (Stage D item 1). *)
Lemma CF_of_Z_subP (x y : u256) :
  CF_of_Z (wunsigned x - wunsigned y) = Some (wlt Unsigned x y).
Proof.
  have [hCF _] := waddsubcarry_cmlzP false x y false.
  move: hCF; rewrite /wsubcarry /wlt /= !Z.sub_0_r.
  move=> ->; congr Some; rewrite /wunsigned.
  move: (word.urepr x) (word.urepr y) => a b.
  case: ZltP => h1; case: ZltP => h2 //; exfalso; Lia.lia.
Qed.

Lemma ZF_of_word_subP (x y : u256) :
  ZF_of_word (x - y) = Some (x == y).
Proof. by rewrite /ZF_of_word GRing.subr_eq0. Qed.

(* [norm_condP]: evaluating the [empty_const_prop_e]-normalized condition
   gives the same boolean as the original, in the same state.  Direct
   application of [empty_const_prop_eP] (no globals, empty constant-
   propagation map) plus [to_boolI]/[value_uinclE] to recover equality
   (rather than just [value_uincl]) from a [bool]-typed source value.
   [acc_fcp] is pinned explicitly on the goal side, matching the pin
   [lower_cmp] itself now uses (see the comment there): [empty_const_prop_e]'s
   own [{fcp}] is a bare, unqualified [FlagCombinationParams] implicit with
   several competing global instances ([acc_extra] transitively [Require]s
   [arm_extra]), so writing the goal without pinning risks resolving to a
   different (wrong) instance than [lower_cmp]'s.  [empty_const_prop_eP]
   itself has no separate [fcp] slot to instantiate -- its own internal use
   of [const_prop_e] is already committed, at its own compile time, to
   [_fcp spp] (a de-facto per-architecture choice, since [spp] is a genuine
   parameter unified from [he]); for ACC, [_fcp spp] reduces definitionally
   to [ad_fcp acc_decl] = [acc_fcp] (acc_decl.v's own [Build_arch_decl]
   sets [ad_fcp := acc_fcp]), so the two pins agree up to conversion and
   [empty_const_prop_eP] applies directly. *)
Lemma norm_condP e s v b :
  sem_pexpr true (p_globs p) s e = ok v ->
  to_bool v = ok b ->
  sem_pexpr true (p_globs p) s (@empty_const_prop_e acc_fcp e) = ok (Vbool b).
Proof.
  move=> he /to_boolI ?; subst v.
  by have [v' [-> /value_uinclE ->]] := empty_const_prop_eP he.
Qed.

(* [get_arg_shiftP]: if [get_arg_shift] accepts [e] then [e] evaluates to
   the shifted base value.  Idea (cf. ARM [get_arg_shiftP]): [e] must be
   [Papp2 op (Pvar x) (Papp1 (Oword_of_int U8) (Pconst z))] with [op] a
   256-bit [Olsl]/[Olsr]; its typed [sem_sop2] computes exactly
   [word_shift_of_reg_shift sh base (wunsigned sham)].  Destruct [e] to
   that shape, read off [ebase = Pvar x] and [esham], and relate [sem_sop2]
   to [word_shift_of_reg_shift].  Check whether a [zero_extend] to
   xreg_size appears (ARM zero-extends the base; here it is already
   256-bit).  Moved up from its original position (after [Hassgn_esem]) so
   [sem_BN_CMP] below can use it -- nothing here depends on anything
   defined between the two positions. *)
Lemma get_arg_shiftP ii ws e ebase sh esham s v :
  get_arg_shift ii ws e = ok (Some (ebase, sh, esham)) ->
  sem_pexpr true (p_globs p) s e = ok v ->
  exists (wb : word ws) (wa : word U8),
    [/\ sem_pexpr true (p_globs p) s ebase = ok (Vword wb)
      , sem_pexpr true (p_globs p) s esham = ok (Vword wa)
      & to_word ws v = ok (word_shift_of_reg_shift sh wb (wunsigned wa)) ].
Proof.
move=> hshift hsem.
rewrite /get_arg_shift /= in hshift.
case: e hshift hsem => // op e1 e2 hshift hsem /=.
case: e1 hshift hsem => // x hshift hsem /=.
case: e2 hshift hsem => // s0 e3 hshift hsem /=.
case: s0 hshift hsem => // ws0 hshift hsem /=.
case: ws0 hshift hsem => // hshift hsem /=.
case: e3 hshift hsem => // z hshift hsem /=.
move: hshift; t_xrbindP => o hrso.
case: o hrso => [sh0 |] hrso //=.
move=> hbn; move: hbn; apply: rbindP => _ _.
move=> [] <- <- <-.
move: hrso; rewrite /reg_shift_of_sop2 /chk_xreg_ws /assert.
case: ifP => // /eqP -> hmatcho.
move: hmatcho => /= hmatcho.
case: op hmatcho hsem => //=.
- move=> ws0' hmatcho hsem.
  case: ws0' hmatcho hsem => //= hmatcho hsem.
  move: hmatcho => [] <-.
  move: hsem; apply: rbindP => v1 hv1 hsop.
  move: hsop; rewrite /sem_sop2 /=; t_xrbindP => wb hwb wa hwa hres.
  rewrite -hres.
  move: hwb => /to_wordI' [sz0 [wb0 [hcmp hv1_eq hwb_eq]]].
  case: sz0 hcmp wb0 hv1_eq hwb_eq => //= _ wb0 hv1_eq hwb_eq; subst wb v1.
  move: hwa => /truncate_wordP [_ ->]; rewrite zero_extend_u.
  exists wb0, (wrepr U8 z); split.
  + exact: hv1.
  + by rewrite /sem_sop1 /=.
  + by rewrite zero_extend_u /to_word /= truncate_word_u /sem_shr.
- move=> op1 hmatcho hsem.
  case: op1 hmatcho hsem => //= ws0' hmatcho hsem.
  case: ws0' hmatcho hsem => //= hmatcho hsem.
  move: hmatcho => [] <-.
  move: hsem; apply: rbindP => v1 hv1 hsop.
  move: hsop; rewrite /sem_sop2 /=; t_xrbindP => wb hwb wa hwa hres.
  rewrite -hres.
  move: hwb => /to_wordI' [sz0 [wb0 [hcmp hv1_eq hwb_eq]]].
  case: sz0 hcmp wb0 hv1_eq hwb_eq => //= _ wb0 hv1_eq hwb_eq; subst wb v1.
  move: hwa => /truncate_wordP [_ ->]; rewrite zero_extend_u.
  exists wb0, (wrepr U8 z); split.
  + exact: hv1.
  + by rewrite /sem_sop1 /=.
  + by rewrite zero_extend_u /to_word /= truncate_word_u /sem_shl.
Qed.

(* [bn_shifted_binopP]: the shifted instruction's [exec_sopn] equals the
   base one's when the operand that gets shifted is supplied pre-shifted
   (binop arity: the shift lands on the 2nd operand).  Moved up from its
   original position (right after [Hassgn_esem]) for the same reason as
   [get_arg_shiftP]; self-contained, no dependency on [bn_shifted_unopP]/
   [bn_shifted_teropP], which stay at their original position. *)
Lemma bn_shifted_binopP mn fg sh (wb : word arch_decl.xreg_size) (wa : word U8) x y vs r :
  to_word arch_decl.xreg_size y
  = ok (word_shift_of_reg_shift sh wb (wunsigned wa)) ->
  exec_sopn (Oasm (BaseOp (None, BN_basic mn fg))) [:: x, y & vs] = ok r ->
  mn \in [:: BN_ADD; BN_SUB; BN_AND; BN_OR; BN_XOR; BN_CMP; BN_CMPB ] ->
  exec_sopn (Oasm (BaseOp (None, BN_basic_shift mn fg sh)))
    (x :: Vword wb :: vs ++ [:: Vword wa]) = ok r.
Proof.
move=> hshift hexec hmn.
have letok : forall (eT aT rT : Type) (a : aT) (f : aT -> result eT rT),
    (Let x := ok a in f x) = f a by move=> *.
rewrite !inE in hmn.
case: mn hmn hexec => hmn hexec //.
all: rewrite /exec_sopn /= /sopn_sem /sopn_sem_ /= in hexec |- *.
all: (move: hexec; t_xrbindP => hwx hx hwy hy;
      move=> hwy_eq; case: vs => [| a vs'] //= hsemi <-).
all: rewrite hwy !truncate_word_u !letok.
all: have hwy_val : word_shift_of_reg_shift sh wb (wunsigned wa) = hy
       by move: hshift; rewrite hwy_eq => [[<-]].
all: rewrite /semi_to_atype /= in hsemi.
1-6: (rewrite hwy_val; move: hsemi => [hsemi]; rewrite hsemi //).
(* BN_CMPB: vs' is abstract, extract vs'=[] from hsemi *)
case: vs' hsemi => [| ?? ] //= hsemi.
2: by case: (to_bool a) hsemi.
rewrite truncate_word_u /semi_to_atype /= /arch_utils.arch_mk_semi3_2_shifted /= hwy_val.
rewrite hsemi //.
Qed.

(* [to_word_u256P]: [U256] is the largest [wsize] ([wsize_ge_U256]), so a
   value that [to_word U256] accepts is already exactly a [Vword] at that
   width -- no genuine truncation can have happened. *)
Lemma to_word_u256P (v : value) (w : u256) :
  to_word U256 v = ok w -> v = Vword w.
Proof.
  move=> /to_wordI' [sz' [w' [hle heqv heqw]]].
  have hle' : (sz' <= U256)%CMP := wsize_ge_U256 sz'.
  have hEq := cmp_le_antisym hle hle'.
  subst sz'.
  by rewrite heqv heqw zero_extend_u.
Qed.

(* [sem_cf]: the boolean value a combine-flags label denotes directly on
   two words, taking the operand order [Decision 2] of the plan fixes
   (composite labels already swapped to a flag or its negation before
   [pexpr_of_cf] ever sees them; [sem_combine_cfP] below relates this to
   the actual [sem_combine_flags] value once specialized to the four
   shapes [lower_cmp] can still produce at that point). *)
Definition sem_cf (cf : combine_flags) (ws : wsize) (x y : word ws) : bool :=
  match cf with
  | CF_EQ => x == y
  | CF_NEQ => x != y
  | CF_LT sg => wlt sg x y
  | CF_LE sg => wle sg x y
  | CF_GT sg => wlt sg y x
  | CF_GE sg => wle sg y x
  end.

(* [sem_cf_of_conditionP]: a [U256] comparison condition [Papp2 op e0 e1]
   evaluates to [sem_cf cf] of its operands' words, where [cf] is
   [cf_of_condition]'s label. Case on [op]'s six comparison shapes and
   unfold [sem_sop2]; [to_word_u256P] turns the generic [to_word]
   inversion into the exact [Vword] shape [sem_cf]'s statement needs. *)
Lemma sem_cf_of_conditionP op cf e0 e1 s0 (b : bool) :
  cf_of_condition op = Some (cf, U256) ->
  sem_pexpr true (p_globs p) s0 (Papp2 op e0 e1) = ok (Vbool b) ->
  exists (w0 w1 : u256),
    [/\ sem_pexpr true (p_globs p) s0 e0 = ok (Vword w0)
      , sem_pexpr true (p_globs p) s0 e1 = ok (Vword w1)
      & b = sem_cf cf w0 w1 ].
Proof.
move=> hcf.
rewrite /=; t_xrbindP=> v0 hv0 v1 hv1.
move: hcf; rewrite /cf_of_condition.
case: op hv0 hv1 => //=.
- move=> o hv0 hv1; case: o hv0 hv1 => // ws0 hv0 hv1 [] <- ->.
  rewrite /sem_sop2 /=; t_xrbindP=> w0 hw0 w1 hw1 <-.
  exists w0, w1; split.
  + by rewrite hv0 (to_word_u256P hw0).
  + by rewrite hv1 (to_word_u256P hw1).
  + done.
- move=> o hv0 hv1; case: o hv0 hv1 => // ws0 hv0 hv1 [] <- ->.
  rewrite /sem_sop2 /=; t_xrbindP=> w0 hw0 w1 hw1 <-.
  exists w0, w1; split.
  + by rewrite hv0 (to_word_u256P hw0).
  + by rewrite hv1 (to_word_u256P hw1).
  + done.
- move=> c hv0 hv1; case: c hv0 hv1 => // sg ws0 hv0 hv1 [] <- ->.
  rewrite /sem_sop2 /=; t_xrbindP=> w0 hw0 w1 hw1 <-.
  exists w0, w1; split.
  + by rewrite hv0 (to_word_u256P hw0).
  + by rewrite hv1 (to_word_u256P hw1).
  + done.
- move=> c hv0 hv1; case: c hv0 hv1 => // sg ws0 hv0 hv1 [] <- ->.
  rewrite /sem_sop2 /=; t_xrbindP=> w0 hw0 w1 hw1 <-.
  exists w0, w1; split.
  + by rewrite hv0 (to_word_u256P hw0).
  + by rewrite hv1 (to_word_u256P hw1).
  + done.
- move=> c hv0 hv1; case: c hv0 hv1 => // sg ws0 hv0 hv1 [] <- ->.
  rewrite /sem_sop2 /=; t_xrbindP=> w0 hw0 w1 hw1 <-.
  exists w0, w1; split.
  + by rewrite hv0 (to_word_u256P hw0).
  + by rewrite hv1 (to_word_u256P hw1).
  + done.
- move=> c hv0 hv1; case: c hv0 hv1 => // sg ws0 hv0 hv1 [] <- ->.
  rewrite /sem_sop2 /=; t_xrbindP=> w0 hw0 w1 hw1 <-.
  exists w0, w1; split.
  + by rewrite hv0 (to_word_u256P hw0).
  + by rewrite hv1 (to_word_u256P hw1).
  + done.
Qed.

(* [wleNgt]: the word order's antisymmetry, both signednesses reduce to
   [Z.leb]/[Z.ltb] on [word.urepr]/[word.srepr] and close by [Lia.lia]. *)
Lemma wleNgt sg sz (a b : word sz) : wle sg a b = ~~ wlt sg b a.
Proof.
rewrite /wle /wlt; case: sg.
- case: ZleP => h1; case: ZltP => h2 //; exfalso; Lia.lia.
- case: ZleP => h1; case: ZltP => h2 //; exfalso; Lia.lia.
Qed.

(* [negate_cfP]: [negate_cf] flips [sem_cf]'s boolean, for every label
   (needed generically since [Decision 7]'s peeled negation can land on
   any of the six shapes before [swap_cf] simplifies further). *)
Lemma negate_cfP (cf : combine_flags) (x y : u256) :
  sem_cf (negate_cf cf) x y = ~~ sem_cf cf x y.
Proof.
case cf; rewrite /negate_cf/=.
- by move=> s; rewrite wleNgt.
- by move=> s; rewrite wleNgt negbK.
- done.
- by rewrite negbK.
- by move=> s; rewrite wleNgt negbK.
- by move=> s; rewrite wleNgt.
Qed.

(* [swap_cfP]: [swap_cf]'s label on the swapped operands denotes the same
   boolean as the original label on the original operands ([Decision 2]).
   Only [CF_LE]/[CF_GT] swap, to [CF_GE]/[CF_LT] respectively; both cases
   unfold directly from [sem_cf]'s definition. *)
Lemma swap_cfP (cf cf' : combine_flags) (x y : u256) :
  swap_cf cf = Some cf' -> sem_cf cf' y x = sem_cf cf x y.
Proof. by case: cf => //= s [<-]. Qed.

(* [sem_cf_symmetric]: [CF_EQ]/[CF_NEQ] do not care about operand order
   (used for the shift-driven operand swap of [lower_cmp]'s step 6, which
   only ever fires on a symmetric label). *)
Lemma sem_cf_symmetric (cf : combine_flags) (x y : u256) :
  is_symmetric_cf cf -> sem_cf cf x y = sem_cf cf y x.
Proof. by case: cf => //= _; rewrite eq_sym. Qed.

(* [sem_combine_cfP]: for the four labels [pexpr_of_cf] ever actually
   receives after [lower_cmp]'s signed check and [swap_cf] ([CF_EQ],
   [CF_NEQ], [CF_LT Unsigned], [CF_GE Unsigned] -- [Stage D item 2] of the
   plan), [sem_combine_flags] on the [BN.CMP] flag values [C := wlt
   Unsigned A B] / [Z := (A == B)] equals [sem_cf] of the same label and
   operands, for *any* [M]/[L] ([sem_combine_flags]'s own value does not
   depend on them for these four labels). [acc_fcp] is pinned explicitly,
   for the same reason as [lower_cmp]/[norm_condP] (see their comments):
   plain [sem_combine_flags] would let generic instance search pick
   whichever [FlagCombinationParams] it finds first, not necessarily
   ACC's; [sem_pexpr_of_cfP2] below checks this pin is the one the real
   [PappN (Ocombine_flags _) _] evaluation actually uses. *)
Lemma sem_combine_cfP cf (A B : u256) (M L : bool) :
  (cf = CF_EQ \/ cf = CF_NEQ \/ cf = CF_LT Unsigned \/ cf = CF_GE Unsigned) ->
  @sem_combine_flags acc_fcp cf (wlt Unsigned A B) M L (A == B) = sem_cf cf A B.
Proof.
move=> [-> | [-> | [-> | ->]]]; rewrite /sem_combine_flags /cf_xsem /=.
- done.
- done.
- done.
- case: ZltP => h1; case: ZleP => h2 //; exfalso; Lia.lia.
Qed.

(* [sem_BN_CMP]: executing the [BN.CMP] emitted by [lower_cmp] (plain or
   with the second operand shifted) from a state [t] where the two
   comparison operands evaluate to words [w0]/[w1] writes the four fresh
   flags, landing in a state related to [t] by [eq_fv], with [C] and [Z]
   carrying the values [CF_of_Z_subP]/[ZF_of_word_subP] give.  [M]/[L] are
   never inspected for their *value* downstream (per Stage D item 1 of the
   plan), but [lower_cmp_finishP]/[sem_pexpr_of_cfP2] below still need
   [get_var] on them to *succeed* (to evaluate [pexpr_of_cf]'s
   [PappN], which reads all four flags), hence the two trailing
   existentials rather than dropping [M]/[L] altogether. The shifted case
   is lifted from the plain one with [bn_shifted_binopP] (already in this
   file, [BN_CMP] is in its mnemonic whitelist); [get_arg_shiftP] relates
   [ebase]/[esham]'s values to the shift, and since [sem_pexpr t e1 = ok
   (Vword w1)] already, its [to_word] hypothesis instantiates directly to
   [w1 = word_shift_of_reg_shift sh wb (wunsigned wa)].  The write order
   inside the descriptor's result tuple is [C, M, L, Z] (matching
   [fresh_flags]'s own [C; M; L; Z] order): reading [Z] needs no peeling
   (outermost [Vm.set]), reading [C] peels [Z], [L], [M]; reading [M]
   peels [Z], [L]; reading [L] peels only [Z]. *)
Lemma sem_BN_CMP ii fg op args e0 e1 t (w0 w1 : u256) :
  sem_pexpr true (p_globs p) t e0 = ok (Vword w0) ->
  sem_pexpr true (p_globs p) t e1 = ok (Vword w1) ->
  (op = BN_basic BN_CMP fg /\ args = [:: e0; e1 ])
  \/ (exists base sh sham,
        [/\ op = BN_basic_shift BN_CMP fg sh, args = [:: e0; base; sham ]
          & get_arg_shift ii arch_decl.xreg_size e1
            = ok (Some (base, sh, sham)) ]) ->
  exists2 t',
    sem_sopn (p_globs p) (Oasm (BaseOp (None, op))) t
      [seq Lvar {| v_var := x; v_info := var_info_of_ii ii |}
          | x <- fresh_flags fv ]
      args
    = ok t'
  & [/\ eq_fv t t'
      , get_var true (evm t') (fvCF1 fv) = ok (Vbool (wlt Unsigned w0 w1))
      , get_var true (evm t') (fvZF1 fv) = ok (Vbool (w0 == w1))
      , exists m, get_var true (evm t') (fvMF1 fv) = ok (Vbool m)
      & exists l, get_var true (evm t') (fvLF1 fv) = ok (Vbool l) ].
Proof using atoI fv fv_correct p pT sc_sem syscall_state wsw.
move=> he0 he1 hcase.
have hplain : exists2 t',
    sem_sopn (p_globs p) (Oasm (BaseOp (None, BN_basic BN_CMP fg))) t
      [seq Lvar {| v_var := x; v_info := var_info_of_ii ii |} | x <- fresh_flags fv]
      [:: e0; e1] = ok t'
  & [/\ eq_fv t t', get_var true (evm t') (fvCF1 fv) = ok (Vbool (wlt Unsigned w0 w1))
    , get_var true (evm t') (fvZF1 fv) = ok (Vbool (w0 == w1))
    , exists m, get_var true (evm t') (fvMF1 fv) = ok (Vbool m)
    & exists l, get_var true (evm t') (fvLF1 fv) = ok (Vbool l)].
2: case: hcase => [[-> ->] | [base [sh [sham [-> -> hgas]]]]].
2: exact: hplain.
2: case: hplain => t0 hplain_sem [heq hCF hZF hM hL].
2: move: hplain_sem; rewrite /sem_sopn /= he0 he1 /=.
2: t_xrbindP => r hexec hwrite.
2: have [wb [wa [hbase hsham hshift]]] := get_arg_shiftP hgas he1.
2: have hexec' := bn_shifted_binopP hshift hexec ltac:(by vm_compute).
2: exists t0 => //.
2: rewrite hbase /= hsham /=.
2: move: hexec'; rewrite cat0s => hexec'.
2: rewrite hexec'; exact: hwrite.
rewrite /sem_sopn /= he0 he1 /= /exec_sopn /= /sopn_sem /sopn_sem_ /=.
rewrite truncate_word_u.
rewrite truncate_word_u.
cbn -[CF_of_Z MF_of_word LF_of_word ZF_of_word wsub wunsigned].
rewrite CF_of_Z_subP ZF_of_word_subP /=.
eexists; first reflexivity.
have huniq : uniq (all_fresh_vars fv) := (andP fv_correct).2.
move: huniq.
rewrite /all_fresh_vars /= !inE !negb_or.
move=> /and4P[/and3P[hCM hCL hCZ] /andP[hML hMZ] hLZ _].
have hCMv : fvCF1 fv != fvMF1 fv by [].
have hCLv : fvCF1 fv != fvLF1 fv by [].
have hCZv : fvCF1 fv != fvZF1 fv by [].
have hMLv : fvMF1 fv != fvLF1 fv by [].
have hMZv : fvMF1 fv != fvZF1 fv by [].
have hLZv : fvLF1 fv != fvZF1 fv by [].
have hZCv : fvZF1 fv != fvCF1 fv by rewrite neq_sym.
have hLCv : fvLF1 fv != fvCF1 fv by rewrite neq_sym.
have hMCv : fvMF1 fv != fvCF1 fv by rewrite neq_sym.
have hZMv : fvZF1 fv != fvMF1 fv by rewrite neq_sym.
have hLMv : fvLF1 fv != fvMF1 fv by rewrite neq_sym.
have hZLv : fvZF1 fv != fvLF1 fv by rewrite neq_sym.
split.
- rewrite /eq_fv /st_eq_ex /st_rel /=; split=> //.
  move=> x hx.
  have hCFne : fvCF1 fv != x by apply/eqP=> heq; apply: hx; rewrite -heq; exact: fvars_CF1.
  have hMFne : fvMF1 fv != x by apply/eqP=> heq; apply: hx; rewrite -heq; exact: fvars_MF1.
  have hLFne : fvLF1 fv != x by apply/eqP=> heq; apply: hx; rewrite -heq; exact: fvars_LF1.
  have hZFne : fvZF1 fv != x by apply/eqP=> heq; apply: hx; rewrite -heq; exact: fvars_ZF1.
  by rewrite (Vm.setP_neq _ _ hZFne) (Vm.setP_neq _ _ hLFne) (Vm.setP_neq _ _ hMFne) (Vm.setP_neq _ _ hCFne).
- rewrite /get_var /=.
  by rewrite (Vm.setP_neq _ _ hZCv) (Vm.setP_neq _ _ hLCv) (Vm.setP_neq _ _ hMCv) Vm.setP_eq //.
- by rewrite /get_var /= Vm.setP_eq /=.
- eexists; rewrite /get_var /=.
  by rewrite (Vm.setP_neq _ _ hZMv) (Vm.setP_neq _ _ hLMv) Vm.setP_eq //.
- eexists; rewrite /get_var /=.
  by rewrite (Vm.setP_neq _ _ hZLv) Vm.setP_eq //.
Qed.

(* [sem_pexpr_of_cfP2]: evaluating [pexpr_of_cf cf vi (fresh_flags fv)] in
   a state where [C]/[Z] hold the given booleans and [M]/[L] hold *some*
   booleans (their value is irrelevant, [hmix] must hold for every choice)
   reduces via [PappN]/[sem_opN]/[get_gvar] to [sem_combine_flags cf c M L
   z], and [hmix] then rewrites that to [bres]. *)
Lemma sem_pexpr_of_cfP2 (ii : instr_info) cf t' (c z bres : bool) :
  get_var true (evm t') (fvCF1 fv) = ok (Vbool c) ->
  get_var true (evm t') (fvZF1 fv) = ok (Vbool z) ->
  (exists m, get_var true (evm t') (fvMF1 fv) = ok (Vbool m)) ->
  (exists l, get_var true (evm t') (fvLF1 fv) = ok (Vbool l)) ->
  (forall M L : bool, @sem_combine_flags acc_fcp cf c M L z = bres) ->
  sem_pexpr true (p_globs p) t' (pexpr_of_cf cf (var_info_of_ii ii) (fresh_flags fv))
  = ok (Vbool bres).
Proof.
move=> hc hz [m hm] [l hl] hmix.
rewrite /pexpr_of_cf /fresh_flags /=.
rewrite /sem_pexpr /= /get_gvar /=.
move: hc hz hm hl; rewrite /get_var /= => -> -> -> -> /=.
rewrite /sem_opN /=.
by rewrite (hmix m l).
Qed.

(* [lower_cmp_finishP]: the tail shared by every branch of [lower_cmpP]'s
   proof, from right after [lower_cmp]'s [swap_cf] step (which has already
   picked the concrete pair [(ee0, ee3)] and the label [cf], guaranteed by
   then to be one of the four shapes [sem_combine_cfP] covers) through to
   the final existential. Case on [get_arg_shift]'s two results (as
   concrete [Some]/[None] shapes, not just their [isSome] reflection, so
   [lower_cmp]'s own case split -- including the symmetric-label operand
   swap of its step 6 -- reduces definitionally): the [(Some, Some)] case
   is the [shifted_operand_side] contradiction on *both* sides at once,
   [(Some, None)] only survives when the label is symmetric (else the same
   contradiction), [(None, Some)] and [(None, None)] are the two intended
   shifted/plain shapes.  Each surviving case feeds [sem_BN_CMP] the right
   disjunct and [sem_pexpr_of_cfP2] the resulting flag reads, discharging
   [sem_pexpr_of_cfP2]'s [hmix] with [sem_combine_cfP] (and, in the
   symmetric case, [sem_cf_symmetric] to swap the operand order back). *)
Lemma lower_cmp_finishP (ii : instr_info) (tag : assgn_tag)
  (cf : combine_flags) (ee0 ee3 errsrc : pexpr)
  (wa wb : u256) (bres : bool) t0 pre e' :
  (cf = CF_EQ \/ cf = CF_NEQ \/ cf = CF_LT Unsigned \/ cf = CF_GE Unsigned) ->
  sem_pexpr true (p_globs p) t0 ee0 = ok (Vword wa) ->
  sem_pexpr true (p_globs p) t0 ee3 = ok (Vword wb) ->
  bres = sem_cf cf wa wb ->
  (Let osh0 := get_arg_shift ii U256 ee0
   in Let osh1 := get_arg_shift ii U256 ee3
      in (let
          '(e0, e3, osh3, osh2) :=
           if [&& isSome osh0, ~~ isSome osh1 & is_symmetric_cf cf]
           then (ee3, ee0, osh1, osh0)
           else (ee0, ee3, osh0, osh1) in
           assert (~~ isSome osh3) (E.shifted_operand_side ii errsrc) >>
           (let
            '(cmp_op, cmp_args) :=
             match osh2 with
             | Some (base, sh, sham) =>
                 (BN_basic_shift BN_CMP acc_options.FG1 sh,
                  [:: e0; base; sham])
             | None => (BN_basic BN_CMP acc_options.FG1, [:: e0; e3])
             end in
             issue
               ([:: ([:: Lvar {| v_var := fvCF1 fv; v_info := var_info_of_ii ii |};
                         Lvar {| v_var := fvMF1 fv; v_info := var_info_of_ii ii |};
                         Lvar {| v_var := fvLF1 fv; v_info := var_info_of_ii ii |};
                         Lvar {| v_var := fvZF1 fv; v_info := var_info_of_ii ii |}],
                     BaseOp (None, cmp_op), cmp_args)],
                pexpr_of_cf cf (var_info_of_ii ii) (fresh_flags fv)))))
  = ok (Some (pre, e')) ->
  exists2 t : estate,
    esem p ev [seq low_instr_i ii tag i | i <- pre] t0 = ok t
    & eq_fv t0 t /\ sem_pexpr true (p_globs p) t e' = ok (Vbool bres).
Proof using atoI ev fv fv_correct p pT sCP sc_sem syscall_state wsw.
move=> hcf4 hwa hwb hbres.
t_xrbindP=> osh0 hosh0 osh1 hosh1.
case: osh0 hosh0 => [[[base0 sh0] sham0]|] hosh0;
case: osh1 hosh1 => [[[base1 sh1] sham1]|] hosh1 /=.
- by move=> heq; discriminate heq.
- case: ifP => hsym.
  + move=> [] <- <-.
    have hcase : (BN_basic_shift BN_CMP acc_options.FG1 sh0 = BN_basic BN_CMP acc_options.FG1 /\ [:: ee3; base0; sham0] = [:: ee3; ee0])
      \/ (exists base sh sham,
            [/\ BN_basic_shift BN_CMP acc_options.FG1 sh0 = BN_basic_shift BN_CMP acc_options.FG1 sh
              , [:: ee3; base0; sham0] = [:: ee3; base; sham]
              & get_arg_shift ii arch_decl.xreg_size ee0 = ok (Some (base, sh, sham)) ]).
    * right; exists base0, sh0, sham0; split=> //.
    have [t2 hsem2 [heqt2 hCF hZF hMex hLex]] := sem_BN_CMP hwb hwa hcase.
    exists t2.
    * by rewrite /= hsem2.
    * split=> //.
      apply: (sem_pexpr_of_cfP2 ii hCF hZF hMex hLex).
      move=> M L.
      rewrite (sem_combine_cfP wb wa M L hcf4) -(sem_cf_symmetric wa wb hsym).
      by rewrite -hbres.
  + by move=> heq; discriminate heq.
- move=> [] <- <-.
  have hcase : (BN_basic_shift BN_CMP acc_options.FG1 sh1 = BN_basic BN_CMP acc_options.FG1 /\ [:: ee0; base1; sham1] = [:: ee0; ee3])
    \/ (exists base sh sham,
          [/\ BN_basic_shift BN_CMP acc_options.FG1 sh1 = BN_basic_shift BN_CMP acc_options.FG1 sh
            , [:: ee0; base1; sham1] = [:: ee0; base; sham]
            & get_arg_shift ii arch_decl.xreg_size ee3 = ok (Some (base, sh, sham)) ]).
  * right; exists base1, sh1, sham1; split=> //.
  have [t2 hsem2 [heqt2 hCF hZF hMex hLex]] := sem_BN_CMP hwa hwb hcase.
  exists t2.
  * by rewrite /= hsem2.
  * split=> //.
    apply: (sem_pexpr_of_cfP2 ii hCF hZF hMex hLex).
    move=> M L.
    by rewrite (sem_combine_cfP wa wb M L hcf4) -hbres.
- move=> [] <- <-.
  have hcase : (BN_basic BN_CMP acc_options.FG1 = BN_basic BN_CMP acc_options.FG1 /\ [:: ee0; ee3] = [:: ee0; ee3])
    \/ (exists base sh sham,
          [/\ BN_basic BN_CMP acc_options.FG1 = BN_basic_shift BN_CMP acc_options.FG1 sh
            , [:: ee0; ee3] = [:: ee0; base; sham]
            & get_arg_shift ii arch_decl.xreg_size ee3 = ok (Some (base, sh, sham)) ]).
  * by left.
  have [t2 hsem2 [heqt2 hCF hZF hMex hLex]] := sem_BN_CMP hwa hwb hcase.
  exists t2.
  * by rewrite /= hsem2.
  * split=> //.
    apply: (sem_pexpr_of_cfP2 ii hCF hZF hMex hLex).
    move=> M L.
    by rewrite (sem_combine_cfP wa wb M L hcf4) -hbres.
Qed.

(* [cf_after_swap_4shape]: after [lower_cmp]'s signed check, [swap_cf]
   always leaves one of the four labels [sem_combine_cfP]/
   [lower_cmp_finishP] are stated for -- [CF_LE]/[CF_GT] always swap away,
   [CF_EQ]/[CF_NEQ]/[CF_LT Unsigned]/[CF_GE Unsigned] never swap. *)
Lemma cf_after_swap_4shape cf1 :
  ~~ is_signed_cf cf1 ->
  match swap_cf cf1 with
  | Some cf' => cf' = CF_EQ \/ cf' = CF_NEQ \/ cf' = CF_LT Unsigned \/ cf' = CF_GE Unsigned
  | None => cf1 = CF_EQ \/ cf1 = CF_NEQ \/ cf1 = CF_LT Unsigned \/ cf1 = CF_GE Unsigned
  end.
Proof.
case: cf1 => [[]|[]|||[]|[]] //= _; auto.
Qed.

(* [lower_cmpP]: the analog of ARM's [sem_lower_condition_pexpr].  Moving
   the evaluation of [e] to [s'] with [eeq_exc_sem_pexpr], normalizing with
   [norm_condP], then case-splitting on the normalized shape (mirroring
   [lower_cmp]'s own definition: peel one [Papp1 Onot], match [Papp2 op e0
   e1] with [cf_of_condition op = Some (cf, U256)], reject signed, swap via
   [swap_cf]) and handing off to [lower_cmp_finishP] for the shift routing
   and the [BN.CMP]/[pexpr_of_cf] evaluation. The peeled-negation branch
   needs [negate_cfP] to relate the pre-negation [sem_cf] value ([b]'s
   defining equation, from [sem_cf_of_conditionP] on the un-negated
   [Papp2]) to the post-negation label [lower_cmp] actually swaps on; the
   direct (non-negated) branch skips that step. Both then need
   [swap_cfP]/[cf_after_swap_4shape] to feed [lower_cmp_finishP] the right
   operand order, label and 4-shape witness; [eeq_excT] closes the
   [eq_fv s t] side (through the intermediate [eq_fv s s']). *)
Lemma lower_cmpP ii tag e pre e' s s' v b :
  lower_cmp ii e = ok (Some (pre, e')) ->
  eq_fv s s' ->
  disj_fvars (read_e e) ->
  sem_pexpr true (p_globs p) s e = ok v ->
  to_bool v = ok b ->
  exists2 t,
    esem p ev (map (low_instr_i ii tag) pre) s' = ok t
    & eq_fv s t /\ sem_pexpr true (p_globs p) t e' = ok (Vbool b).
Proof using atoI ev fv fv_correct p pT sCP sc_sem syscall_state wsw.
move=> hlow heq hdisj he htb.
have he' := eeq_exc_sem_pexpr hdisj heq he.
have hn := norm_condP he' htb.
move: hlow.
rewrite /lower_cmp /=.
case: (empty_const_prop_e e) hn =>
  [ z | bb | ws0 z | vv | al aa ws0 xx ee | aa ws0 z xx ee | al ws0 ee
  | op1 ee | op2 e1 e2 | opn es | ty e1 e2 e3 ] hn //=.
case: op1 hn => // hn //=.
case: ee hn => // op e1 e2 hn //=.
- case Ecf: (cf_of_condition op) => [[cf ws]|] //=.
  case: eqP Ecf => [-> Ecf | hne] //=.
  move: hn; rewrite /=; t_xrbindP=> va hva vb hvb v0 hv0 hsop1.
  move: hsop1; rewrite /sem_sop1 /=; t_xrbindP=> bx hbx <-.
  move: hbx => /to_boolI ?; subst va.
  have hcomb : sem_pexpr true (p_globs p) s' (Papp2 op e1 e2) = ok (Vbool bx).
    by rewrite /= vb v0 /= hv0.
  have [w0 [w1 [hw0 hw1 hbxeq]]] := sem_cf_of_conditionP Ecf hcomb.
  have hb1 : sem_cf (negate_cf cf) w0 w1 = ~~ bx.
    by rewrite negate_cfP hbxeq.
  move=> hsig.
  case Esw: (swap_cf (negate_cf cf)) => [cf2|] /=.
  + have h4shape := cf_after_swap_4shape hsig.
    rewrite Esw in h4shape.
    have hbres2 : ~~ bx = sem_cf cf2 w1 w0.
      by rewrite (swap_cfP w0 w1 Esw).
    have hfin := lower_cmp_finishP tag h4shape hw1 hw0 hbres2.
    move=> hmain.
    have [t2 hsem2 [heq2 hval2]] := hfin ii (Papp2 op e1 e2) pre e' hmain.
    exists t2 => //.
    split; [exact: (eeq_excT heq heq2) | exact: hval2].
  + have h4shape := cf_after_swap_4shape hsig.
    rewrite Esw in h4shape.
    have hfin := lower_cmp_finishP tag h4shape hw0 hw1 (esym hb1).
    move=> hmain.
    have [t2 hsem2 [heq2 hval2]] := hfin ii (Papp2 op e1 e2) pre e' hmain.
    exists t2 => //.
    split; [exact: (eeq_excT heq heq2) | exact: hval2].
case Ecf: (cf_of_condition op2) => [[cf ws]|] //=.
case: eqP Ecf => [-> Ecf | hne] //=.
have [wA [wB [hwA hwB hbeq]]] := sem_cf_of_conditionP Ecf hn.
t_xrbindP=> hsig2.
case Esw2: (swap_cf cf) => [cf3|] /=.
- have h4shape2 := cf_after_swap_4shape hsig2.
  rewrite Esw2 in h4shape2.
  have hbeq2 : b = sem_cf cf3 wB wA.
    by rewrite hbeq (swap_cfP wA wB Esw2).
  have hfin2 := lower_cmp_finishP tag h4shape2 hwB hwA hbeq2.
  move=> hmain2.
  have [t2 hsem2b [heq2b hval2b]] := hfin2 ii (Papp2 op2 e1 e2) pre e' hmain2.
  exists t2 => //.
  split; [exact: (eeq_excT heq heq2b) | exact: hval2b].
- have h4shape2 := cf_after_swap_4shape hsig2.
  rewrite Esw2 in h4shape2.
  have hfin2 := lower_cmp_finishP tag h4shape2 hwA hwB hbeq.
  move=> hmain2.
  have [t2 hsem2b [heq2b hval2b]] := hfin2 ii (Papp2 op2 e1 e2) pre e' hmain2.
  exists t2 => //.
  split; [exact: (eeq_excT heq heq2b) | exact: hval2b].
Qed.

(* [esem] of a list built entirely from [low_instr_i] (all [Copn]
   instructions, per [instr_of_copn_args]) only reads [p_globs]; running it
   against a program [p1] with the same [p_globs] as the ambient [p]
   (as in [lower_PifP]'s [p'] vs [p], needed to relate [lower_cmpP]'s [p]-side
   conclusion to a [p']-side goal) gives the same result. *)
Lemma esem_low_instr_i_glob (p1 p2 : prog) (ev1 ev2 : extra_val_t)
  ii tag (c : seq acc_args) s :
  p_globs p1 = p_globs p2 ->
  esem p1 ev1 [seq low_instr_i ii tag i | i <- c] s
  = esem p2 ev2 [seq low_instr_i ii tag i | i <- c] s.
Proof.
move=> hglob.
elim: c s => [| a c ih] s //=.
case: a => [[lvs op] es].
rewrite /low_instr_i /= /esem_i /= hglob.
by case: (sem_sopn (p_globs p2) (Oasm op) s lvs es) => // s'; exact: ih.
Qed.

Lemma lower_PifP (p' : prog) (hglob : p_globs p' = p_globs p)
  ii tag ws econd e0 e1 lv v v' s0 s1 pre lvs op es :
  lower_Pif ii ws econd e0 e1 = ok (Some (pre, lvs, op, es)) ->
  disj_fvars (read_e (Pif (aword ws) econd e0 e1)) ->
  disj_fvars (vars_lval lv) ->
  sem_pexpr true (p_globs p) s0 (Pif (aword ws) econd e0 e1) = ok v ->
  truncate_val (cword ws) v = ok v' ->
  write_lval true (p_globs p) lv v' s0 = ok s1 ->
  exists2 s1',
    esem p' ev (low_cmd_c ii tag (pre, lvs ++ [:: lv], op, es)) s0 = ok s1'
    & eq_fv s1 s1'.
Proof using atoI dc ev fv fv_correct p pT sCP sc_sem syscall_state wsw.
move=> hlow hdisj hdisjlv he htr hw.
have hdisj3 : disj_fvars (read_e econd) /\ disj_fvars (read_e e0) /\ disj_fvars (read_e e1).
  move: hdisj; rewrite /read_e /=.
  have e1u := read_eE e1 Sv.empty.
  have e0u := read_eE e0 (read_e_rec Sv.empty e1).
  have econdu := read_eE econd (read_e_rec (read_e_rec Sv.empty e1) e0).
  move=> hdisj'.
  split; last split; apply: disjoint_w hdisj'; SvD.fsetdec.
have [hdisj_econd [hdisj_e0 hdisj_e1]] := hdisj3.
rewrite /lower_Pif /chk_xreg_ws /assert in hlow.
case: eqP hlow => [?|//]; subst ws.
move=> hlow.
move: hlow; t_xrbindP=> _ ocmp hocmp.
case: ocmp hocmp => [[pre0 econd']|] hocmp /=.
2: rewrite /lc_xissue /lc_sissue /issue => -[] h1 h2 h3 h4; subst pre lvs op es.
2: simpl.
2: rewrite hglob.
2: exists s1; last by [].
2: rewrite /sem_sopn /exec_sopn /= /sopn_sem /sopn_sem_ /=.
2: move: he; rewrite /=.
2: t_xrbindP=> b hb v0 hv0 v1 hv1 hv.
2: move=> htrv1 z3 z4 hv_e1 htrz3 hsel.
2: have [w0 [ws0 [w0' [htw0 hv1_eq hv0'_eq]]]] := truncate_val_typeE htrv1.
2: have [w1 [ws1 [w1' [htw1 hz4_eq hz3_eq]]]] := truncate_val_typeE htrz3.
2: subst hv1 v1 z4 z3.
2: rewrite hv hv_e1 v0 /= htw0 htw1 hv0 /=.
2: have hv_eq : v' = Vword (if b then w0 else w1).
2: { move: htr; rewrite -hsel /truncate_val /=.
     by case: b hv0 hsel; rewrite /= truncate_word_u => _ _ [<-]. }
2: rewrite hv_eq in hw.
2: by rewrite /= hw.
move=> heq; move: heq => [] h1 h2 h3 h4; subst pre lvs op es.
move: he; rewrite /=.
t_xrbindP=> b hb v0 hv0 v1 hv1 hv.
move=> htrv1 z3 z4 hv_e1 htrz3 hsel.
have [t hsem_t [heqt hval_t]] := lower_cmpP tag hocmp (eeq_excR fvars s0) hdisj_econd v0 hv0.
rewrite -cats1 map_cat esem_cat (esem_low_instr_i_glob ev ev ii tag pre0 s0 hglob) hsem_t /=.
rewrite hglob.
have he0t := eeq_exc_sem_pexpr hdisj_e0 heqt hv.
have he1t := eeq_exc_sem_pexpr hdisj_e1 heqt hv_e1.
rewrite /sem_sopn /exec_sopn /= /sopn_sem /sopn_sem_ /=.
have [w0 [ws0 [w0' [htw0 hv1_eq hv0'_eq]]]] := truncate_val_typeE htrv1.
have [w1 [ws1 [w1' [htw1 hz4_eq hz3_eq]]]] := truncate_val_typeE htrz3.
subst hv1 v1 z4 z3.
rewrite he0t he1t hval_t /= htw0 htw1 /=.
have hv_eq : v' = Vword (if b then w0 else w1).
{ move: htr; rewrite -hsel /truncate_val /=.
  case: b hv0 hsel hval_t => hv0 hsel hval_t.
  rewrite /= truncate_word_u /=.
  move=> [<-].
  by [].
  rewrite /= truncate_word_u /=.
  move=> [<-].
  by []. }
rewrite hv_eq in hw.
have [s1' hw' heq'] := eeq_exc_write_lval hdisjlv heqt hw.
exists s1'; last exact: heq'.
by rewrite /= hw'.
Qed.

(* Every branch of [lower_cassgn_word]/[lower_copn] other than the [Pif]
   condition (Section LOWER_CONDITION) keeps [pre = [::]], as before Stage
   A; lift such a branch's plain [sem_sopn] fact to the [esem]/[eq_fv]
   level [lower_cassgn_wordP]/[lower_copnP] need. *)
Lemma esem_no_pre_of_sem_sopn (p' : prog) (hglob : p_globs p' = p_globs p)
  ii tag lvs (op : extended_op) es s0 s1 :
  sem_sopn (p_globs p) (Oasm op) s0 lvs es = ok s1 ->
  exists2 s1', esem p' ev (low_cmd_c ii tag ([::], lvs, op, es)) s0 = ok s1' & eq_fv s1 s1'.
Proof.
move=> hsem.
exists s1; last exact: eeq_excR.
rewrite /low_cmd_c /=.
by rewrite hglob hsem.
Qed.

(* -------------------------------------------------------------------- *)
(* Dispatch (see plan above).  [pre] is non-empty exactly when [e] is a
   [Pif] whose condition [lower_cmp] rewrites to a [BN.CMP]; every other
   branch keeps [pre = [::]] as before. *)
Lemma lower_cassgn_wordP (p' : prog) (hglob : p_globs p' = p_globs p)
  ii tag lv ws e v v' s0 s1 pre lvs op es :
  lower_cassgn_word ii lv ws e = ok (Some (pre, lvs, op, es)) ->
  disj_fvars (read_e e) ->
  disj_fvars (vars_lval lv) ->
  sem_pexpr true (p_globs p) s0 e = ok v ->
  truncate_val (cword ws) v = ok v' ->
  write_lval true (p_globs p) lv v' s0 = ok s1 ->
  exists2 s1',
    esem p' ev (low_cmd_c ii tag (pre, lvs, op, es)) s0 = ok s1'
    & eq_fv s1 s1'.
Proof using atoI dc ev fv fv_correct p pT sCP sc_sem syscall_state wsw.
rewrite /lower_cassgn_word /=.
move=> hlow hdisj hdisjlv he htr hw.
case hmem: (is_lval_in_memory lv).
rewrite hmem /= in hlow.
2: rewrite hmem /= in hlow.
move: hlow; t_xrbindP=> o hchk ho hmatch.
case: o ho hmatch => [[[[pre0 lvs0] op0] es0]|] ho hmatch //=.
move: hmatch => [] h1 h2 h3 h4; subst pre lvs op es.
move: ho; rewrite /no_pre; t_xrbindP => o hstore hmatch2.
case: o hstore hmatch2 => [[[lvs1 op1] es1]|] hstore.
rewrite /lc_sissue /issue => -[] h1 h2 h3 h4; subst pre0 lvs0 op0 es0.
simpl.
have [s1' hsem heqfv] := esem_no_pre_of_sem_sopn hglob ii tag (lower_storeP hstore he htr hw).
exists s1'; last exact: heqfv.
by move: hsem; rewrite /low_cmd_c /=.
by [].
move: hlow; t_xrbindP=> o hlp hmatch.
case: o hlp hmatch => [[[[pre0 lvs0] op0] es0]|] hlp hmatch //=.
move: hmatch => [] h1 h2 h3 h4; subst pre lvs op es.
move: hlp; rewrite /lower_pexpr /=.
case: e he hdisj => // [gv|al aa ws0 xx ee|al ws0 ee|op1 e1|op2 a b|ty econd e0 e1] he hdisj hlp.
move: hlp; rewrite /lower_pexpr_aux /no_pre /=; t_xrbindP=> o hlx hmatch2.
case: o hlx hmatch2 => [[[lvs1 op1] es1]|] hlx.
rewrite /lc_sissue /issue => -[] h1 h2 h3 h4; subst pre0 lvs0 op0 es0.
simpl.
have [s1' hsem heqfv] := esem_no_pre_of_sem_sopn hglob ii tag (lower_PvarP hlx he htr hw).
exists s1'; last exact: heqfv.
by move: hsem; rewrite /low_cmd_c /=.
by [].
move: hlp; rewrite /lower_pexpr_aux /no_pre /=; t_xrbindP=> o hlx hmatch2.
case: o hlx hmatch2 => [[[lvs1 op1] es1]|] hlx.
rewrite /lc_sissue /issue => -[] h1 h2 h3 h4; subst pre0 lvs0 op0 es0.
simpl.
have [s1' hsem heqfv] := esem_no_pre_of_sem_sopn hglob ii tag (lower_loadP hlx he htr hw).
exists s1'; last exact: heqfv.
by move: hsem; rewrite /low_cmd_c /=.
by [].
move: hlp; rewrite /lower_pexpr_aux /no_pre /=; t_xrbindP=> o hlx hmatch2.
case: o hlx hmatch2 => [[[lvs1 op1] es1]|] hlx.
rewrite /lc_sissue /issue => -[] h1 h2 h3 h4; subst pre0 lvs0 op0 es0.
simpl.
have [s1' hsem heqfv] := esem_no_pre_of_sem_sopn hglob ii tag (lower_loadP hlx he htr hw).
exists s1'; last exact: heqfv.
by move: hsem; rewrite /low_cmd_c /=.
by [].
move: hlp; rewrite /lower_pexpr_aux /no_pre /=; t_xrbindP=> o hlx hmatch2.
case: o hlx hmatch2 => [[[lvsx opx] esx]|] hlx.
rewrite /lc_sissue /issue => -[] h1 h2 h3 h4; subst pre0 lvs0 op0 es0.
simpl.
have [s1' hsem heqfv] := esem_no_pre_of_sem_sopn hglob ii tag (lower_Papp1P hlx he htr hw).
exists s1'; last exact: heqfv.
by move: hsem; rewrite /low_cmd_c /=.
by [].
move: hlp; rewrite /lower_pexpr_aux /no_pre /=; t_xrbindP=> o hlx hmatch2.
case: o hlx hmatch2 => [[[lvsx opx] esx]|] hlx.
rewrite /lc_sissue /issue => -[] h1 h2 h3 h4; subst pre0 lvs0 op0 es0.
simpl.
have [s1' hsem heqfv] := esem_no_pre_of_sem_sopn hglob ii tag (lower_Papp2P hlx he htr hw).
exists s1'; last exact: heqfv.
by move: hsem; rewrite /low_cmd_c /=.
by [].
case: ty he hdisj hlp => [| | | ws'] he hdisj hlp //=.
move: hlp; rewrite /assert; t_xrbindP=> heqws hpif.
case: eqP heqws => [? _ | //]; subst ws'.
have [s1' hsem heqfv] := lower_PifP hglob tag hpif hdisj hdisjlv he htr hw.
exists s1'; last exact: heqfv.
by move: hsem hpif => -> _.
Qed.

(* -------------------------------------------------------------------- *)
(* Top-level.  Assemble via [Hassgn_id] (identity branches) and
   [lower_cassgn_wordP] (meaningful branch); reduction in the plan above. *)
Lemma Hassgn_esem (p' : prog) (hglob : p_globs p' = p_globs p)
  {ii lv tag ty e s0 s1 lc} :
  disj_fvars (read_e e) ->
  disj_fvars (vars_lval lv) ->
  sem_assgn p lv tag ty e s0 = ok s1 ->
  lower_i (MkI ii (Cassgn lv tag ty e)) = ok lc ->
  exists2 s1', esem p' ev lc s0 = ok s1' & eq_fv s1 s1'.
Proof using atoI dc ev fv fv_correct p pT sCP sc_sem syscall_state wsw.
move=> hdisje hdisjlv hsem hlc.
move: hsem; rewrite /sem_assgn; t_xrbindP=> v he v' htr hw.
rewrite /lower_i /= in hlc.
case heq: (is_word_type ty) hlc => [ws | ] hlc.
move: hlc; t_xrbindP=> oargs hoargs <-.
case: oargs hoargs => [x | ] hoargs.
case: x hoargs => [[[pre lvs'] op] es'] hoargs.
simpl.
move: htr; rewrite (is_word_typeP heq) /= => htr.
have [s1' hsem heqfv] := lower_cassgn_wordP hglob tag hoargs hdisje hdisjlv he htr hw.
exists s1'; last exact: heqfv.
by move: hsem; rewrite /low_cmd_c /=.
simpl.
exists s1; last exact: eeq_excR.
by rewrite /sem_assgn hglob he /= htr /= hw.
case: ty heq hlc htr => [| |ws' len|ws'] heq hlc htr //=.
2: move: hlc => [<-].
2: exists s1; last exact: eeq_excR.
2: by rewrite esem1 /= /sem_assgn hglob he /= htr /= hw.
2: move: hlc => [<-].
2: exists s1; last exact: eeq_excR.
2: by rewrite esem1 /= /sem_assgn hglob he /= htr /= hw.
move: hlc; rewrite /lower_cassgn_bool; t_xrbindP=> oe hoe hlc.
case: oe hoe hlc => [[pre e']|] hoe hlc //=.
move: hlc => [<-].
move: htr; rewrite /truncate_val /=.
t_xrbindP=> b htb ?; subst v'.
have [t hsem_t [heqt hval_t]] := lower_cmpP tag hoe (eeq_excR fvars s0) hdisje he htb.
rewrite esem_cat (esem_low_instr_i_glob ev ev ii tag pre s0 hglob) hsem_t /=.
rewrite /sem_assgn hglob hval_t /= /truncate_val /=.
have [s1' hw' heq'] := eeq_exc_write_lval hdisjlv heqt hw.
exists s1'; last exact: heq'.
by rewrite /= hw'.
move: hlc => [<-].
exists s1; last exact: eeq_excR.
by rewrite esem1 /= /sem_assgn hglob he /= htr /= hw.
Qed.

(* [bn_shifted_unopP]/[bn_shifted_binopP]/[bn_shifted_teropP]: the shifted
   instruction's [exec_sopn] equals the base one's when the operand that
   gets shifted is supplied pre-shifted.  The three lemmas match the three
   arities [lower_basic_shift] uses: unop [BN_NOT] (1 wide operand); binop
   [BN_ADD/SUB/AND/OR/XOR/CMP/CMPB] (shift on the 2nd operand); carry-terop
   [BN_ADDC/SUBB] (operands x, base, cf; the U8 shift amount appended
   last).  Idea (cf. ARM [with_shift_unop]/[with_shift_binop]/
   [with_shift_terop]): unfold [exec_sopn]/[app_sopn]; the shifted [semi]
   (via [arch_mk_semiN_2_shifted]) is the base [semi] precomposed with
   [word_shift_of_reg_shift] on the designated operand.  Note: [BN_ADDC]/
   [BN_SUBB] read the carry from the flag group [current_CF fg] (id_in
   [F]); reconcile the [cf] argument position with the instruction
   description. *)
Lemma bn_shifted_unopP fg sh (wb : word arch_decl.xreg_size) (wa : word U8) x vs r :
  to_word arch_decl.xreg_size x
  = ok (word_shift_of_reg_shift sh wb (wunsigned wa)) ->
  exec_sopn (Oasm (BaseOp (None, BN_basic BN_NOT fg))) [:: x & vs] = ok r ->
  exec_sopn (Oasm (BaseOp (None, BN_basic_shift BN_NOT fg sh)))
    (Vword wb :: vs ++ [:: Vword wa]) = ok r.
Proof.
move=> hshift hexec.
rewrite /exec_sopn /= /sopn_sem /sopn_sem_ /= in hexec |- *.
move: hexec; t_xrbindP => wx hwx.
move=> htw.
case: vs => [ | ? ?] //= hmatch.
move=> <-.
rewrite /arch_utils.arch_mk_semi1_shifted /=.
rewrite truncate_word_u /= truncate_word_u /=.
have heq : hwx = word_shift_of_reg_shift sh wb (wunsigned wa)
  by move: htw; rewrite hshift => [[<-]].
rewrite heq in hmatch.
move: hmatch; rewrite /semi_to_atype /= => [[<-]].
by rewrite /with_mlz /=.
Qed.

Lemma bn_shifted_teropP mn fg sh (wb : word arch_decl.xreg_size) (wa : word U8) x y cf vs r :
  to_word arch_decl.xreg_size y
  = ok (word_shift_of_reg_shift sh wb (wunsigned wa)) ->
  exec_sopn (Oasm (BaseOp (None, BN_basic mn fg))) [:: x, y, cf & vs] = ok r ->
  mn \in [:: BN_ADDC; BN_SUBB ] ->
  exec_sopn (Oasm (BaseOp (None, BN_basic_shift mn fg sh)))
    (x :: Vword wb :: cf :: vs ++ [:: Vword wa]) = ok r.
Proof.
move=> hshift hexec hmn.
have letok : forall (eT aT rT : Type) (a : aT) (f : aT -> result eT rT),
    (Let x := ok a in f x) = f a by move=> *.
rewrite !inE in hmn.
case: mn hmn hexec => hmn hexec //.
all: rewrite /exec_sopn /= /sopn_sem /sopn_sem_ /= in hexec |- *.
all: (move: hexec; t_xrbindP => hwx hx hwy hy hwy_eq hcf hcf_eq;
      case: vs => [| a vs'] //= hsemi <-).
all: rewrite hwy !truncate_word_u hcf_eq !letok.
all: have hwy_val : word_shift_of_reg_shift sh wb (wunsigned wa) = hy
       by move: hshift; rewrite hwy_eq => [[<-]].
all: (rewrite hwy_val; move: hsemi => [hsemi]; rewrite hsemi //).
Qed.

Lemma lower_basic_shift_notP ii fg lvs es sh es'' s0 s1 :
  lower_basic_shift ii BN_NOT es = ok (Some (sh, es'')) ->
  sem_sopn (p_globs p) (Oasm (BaseOp (None, BN_basic BN_NOT fg))) s0 lvs es
  = ok s1 ->
  sem_sopn (p_globs p)
    (Oasm (BaseOp (None, BN_basic_shift BN_NOT fg sh))) s0 lvs es'' = ok s1.
Proof.
move=> hshift hsrc.
rewrite /lower_basic_shift in hshift.
move: hshift; t_xrbindP.
move=> z [x0 rest0] hrsnoc [<-] hget.
apply: rbindP hget => o hgas.
case: o hgas => [[[ebase sh0] esham] | ] hgas; last by [].
rewrite /issue cat0s => heq_issue; injection heq_issue as <- <-.
move: hgas.
case: es hrsnoc hsrc => [| a bs] hrsnoc hsrc //=.
move: hrsnoc => [] <- <-.
move=> hgas.
rewrite /sem_sopn in hsrc |- *.
move: hsrc; t_xrbindP => vs hvs r hexec hw.
move: hexec.
move: r; rewrite /sem_pexprs /=; t_xrbindP => x_v hx vrest hvrest <-.
move=> hexec.
have [wb [wa [h_ebase h_esham h_shift]]] := get_arg_shiftP hgas hx.
have hexec' := bn_shifted_unopP h_shift hexec.
rewrite h_ebase /= mapM_cat hvrest /= h_esham /= hexec' /= hw //.
Qed.

Lemma lower_basic_shift_addcP ii fg lvs es sh es'' s0 s1 :
  lower_basic_shift ii BN_ADDC es = ok (Some (sh, es'')) ->
  sem_sopn (p_globs p) (Oasm (BaseOp (None, BN_basic BN_ADDC fg))) s0 lvs es
  = ok s1 ->
  sem_sopn (p_globs p)
    (Oasm (BaseOp (None, BN_basic_shift BN_ADDC fg sh))) s0 lvs es'' = ok s1.
Proof.
move=> hshift hsrc.
rewrite /lower_basic_shift in hshift.
move: hshift; t_xrbindP.
move=> z [[[x_e y_e] cf_e] rest] hrsnoc [<-] hget.
apply: rbindP hget => o hgas.
case: o hgas => [[[ebase sh0] esham] | ] hgas; last by [].
rewrite /issue => heq_issue; injection heq_issue as <- <-.
move: hgas.
case: es hrsnoc hsrc => [| e1 [| e2 [| e3 es3]]] hrsnoc hsrc //=.
move: hrsnoc => [] <- <- <- <-.
move=> hgas.
rewrite /sem_sopn in hsrc |- *.
move: hsrc; t_xrbindP => vs hvs r hexec hw.
move: hexec.
move: r; rewrite /sem_pexprs /=.
apply: rbindP => x_v hx.
apply: rbindP => ys_x hys_x.
move=> [<-].
move=> hexec.
move: hys_x.
apply: rbindP => y_v hy.
apply: rbindP => ys_y hys_y.
move=> [heq_x]; subst ys_x.
move: hys_y.
apply: rbindP => cf_v hcf.
apply: rbindP => vrest hvrest.
move=> [heq_y]; subst ys_y.
have [wb [wa [h_ebase h_esham h_shift]]] := get_arg_shiftP hgas hy.
have hexec' := bn_shifted_teropP h_shift hexec ltac:(by vm_compute).
rewrite hx /= h_ebase /= hcf /= mapM_cat hvrest /= h_esham /= hexec' /= hw //.
Qed.

Lemma lower_basic_shift_subbP ii fg lvs es sh es'' s0 s1 :
  lower_basic_shift ii BN_SUBB es = ok (Some (sh, es'')) ->
  sem_sopn (p_globs p) (Oasm (BaseOp (None, BN_basic BN_SUBB fg))) s0 lvs es
  = ok s1 ->
  sem_sopn (p_globs p)
    (Oasm (BaseOp (None, BN_basic_shift BN_SUBB fg sh))) s0 lvs es'' = ok s1.
Proof.
move=> hshift hsrc.
rewrite /lower_basic_shift in hshift.
move: hshift; t_xrbindP.
move=> z [[[x_e y_e] cf_e] rest] hrsnoc [<-] hget.
apply: rbindP hget => o hgas.
case: o hgas => [[[ebase sh0] esham] | ] hgas; last by [].
rewrite /issue => heq_issue; injection heq_issue as <- <-.
move: hgas.
case: es hrsnoc hsrc => [| e1 [| e2 [| e3 es3]]] hrsnoc hsrc //=.
move: hrsnoc => [] <- <- <- <-.
move=> hgas.
rewrite /sem_sopn in hsrc |- *.
move: hsrc; t_xrbindP => vs hvs r hexec hw.
move: hexec.
move: r; rewrite /sem_pexprs /=.
apply: rbindP => x_v hx.
apply: rbindP => ys_x hys_x.
move=> [<-].
move=> hexec.
move: hys_x.
apply: rbindP => y_v hy.
apply: rbindP => ys_y hys_y.
move=> [heq_x]; subst ys_x.
move: hys_y.
apply: rbindP => cf_v hcf.
apply: rbindP => vrest hvrest.
move=> [heq_y]; subst ys_y.
have [wb [wa [h_ebase h_esham h_shift]]] := get_arg_shiftP hgas hy.
have hexec' := bn_shifted_teropP h_shift hexec ltac:(by vm_compute).
rewrite hx /= h_ebase /= hcf /= mapM_cat hvrest /= h_esham /= hexec' /= hw //.
Qed.

(* The semantic condition extracted from [bn_shifted_binopP]: for [mn],
   shifting the second operand commutes between [BN_basic] and
   [BN_basic_shift] at the [exec_sopn] level.  Every binop mnemonic satisfies
   it (via [bn_shifted_binopP]).  The generic lemma
   [gen_lower_basic_shift_binopP] below is proved uniformly from this
   condition, with no case analysis on [mn]. *)
Definition bn_basic_shift_commutes
  (mn : bn_basic_mnemonic)
  (fg : acc_options.bn_flag_group)
  (sh : acc_options.bn_register_shift) : Prop :=
  forall (wb : word arch_decl.xreg_size) (wa : word U8) x y vs r,
    to_word arch_decl.xreg_size y
    = ok (word_shift_of_reg_shift sh wb (wunsigned wa)) ->
    exec_sopn (Oasm (BaseOp (None, BN_basic mn fg))) [:: x, y & vs] = ok r ->
    exec_sopn (Oasm (BaseOp (None, BN_basic_shift mn fg sh)))
      (x :: Vword wb :: vs ++ [:: Vword wa]) = ok r.

(* Structural characterization of [lower_basic_shift] on the seven binop
   mnemonics: it peels the first operand, recognizes a shift on the second,
   and appends the shift amount.  This isolates the only place the proof needs
   to reduce the [match mn] in [lower_basic_shift]. *)
Lemma lower_basic_shift_binopE ii mn es sh es'' :
  mn \in [:: BN_ADD; BN_SUB; BN_AND; BN_OR; BN_XOR; BN_CMP; BN_CMPB] ->
  lower_basic_shift ii mn es = ok (Some (sh, es'')) ->
  exists e1 e2 es2 ebase esham,
    [/\ es = [:: e1, e2 & es2]
      , get_arg_shift ii arch_decl.xreg_size e2 = ok (Some (ebase, sh, esham))
      & es'' = [:: e1, ebase & es2 ++ [:: esham] ] ].
Proof.
  move=> hmn hshift.
  move: hshift hmn; case: mn => /= hshift hmn //;
    (rewrite /lower_basic_shift in hshift;
     move: hshift; t_xrbindP=> z [[x_e y_e] rest] hrsnoc [<-] hget;
     apply: rbindP hget => o hgas;
     case: o hgas => [[[ebase sh0] esham] | ] hgas; last by [];
     rewrite /issue => heq_issue; injection heq_issue as <- <-;
     move: hgas;
     case: es hrsnoc => [| e1 [| e2 es2]] hrsnoc //=;
     move: hrsnoc => [] <- <- <-;
     move=> hgas;
     by exists e1, e2, es2, ebase, esham).
Qed.

(* Generic, uniform binop lemma: given the semantic commutation condition and
   the structural shape produced by [lower_basic_shift], the [BN_basic_shift]
   [sem_sopn] reproduces the [BN_basic] one.  No case analysis on [mn]. *)
Lemma gen_lower_basic_shift_binopP
  ii mn fg lvs es sh es'' s0 s1 e1 e2 es2 ebase esham :
  bn_basic_shift_commutes mn fg sh ->
  es = [:: e1, e2 & es2] ->
  get_arg_shift ii arch_decl.xreg_size e2 = ok (Some (ebase, sh, esham)) ->
  es'' = [:: e1, ebase & es2 ++ [:: esham] ] ->
  sem_sopn (p_globs p) (Oasm (BaseOp (None, BN_basic mn fg))) s0 lvs es = ok s1 ->
  sem_sopn (p_globs p) (Oasm (BaseOp (None, BN_basic_shift mn fg sh))) s0 lvs es''
  = ok s1.
Proof.
  move=> hcomm -> hgas -> hsrc.
  rewrite /sem_sopn in hsrc |- *.
  move: hsrc; t_xrbindP => vs hvs r hexec hw.
  move: hexec.
  move: r; rewrite /sem_pexprs /=.
  apply: rbindP => x_v hx.
  apply: rbindP => ys hys.
  move=> [<-].
  move=> hexec.
  move: hys.
  apply: rbindP => y_v hy.
  apply: rbindP => vrest hvrest.
  move=> [heq]; subst ys.
  have [wb [wa [h_ebase h_esham h_shift]]] := get_arg_shiftP hgas hy.
  have hexec' := hcomm _ _ _ _ _ _ h_shift hexec.
  rewrite hx /= h_ebase /= mapM_cat hvrest /= h_esham /= hexec' /= hw //.
Qed.

(* [lower_basic_shift_binopP] (case lemma for the seven binop mnemonics
   BN_ADD/BN_SUB/BN_AND/BN_OR/BN_XOR/BN_CMP/BN_CMPB): obtained uniformly, with
   no case analysis on [mn], by combining the structural characterization
   [lower_basic_shift_binopE] with the generic [gen_lower_basic_shift_binopP],
   discharging the latter's semantic condition [bn_basic_shift_commutes] via
   [bn_shifted_binopP].  The membership hypothesis [mn \in [:: BN_ADD; ...]] is
   placed last so callers can supply it with [ltac:(by vm_compute)] after the
   other two explicit arguments. *)
Lemma lower_basic_shift_binopP ii mn fg lvs es sh es'' s0 s1 :
  lower_basic_shift ii mn es = ok (Some (sh, es'')) ->
  sem_sopn (p_globs p) (Oasm (BaseOp (None, BN_basic mn fg))) s0 lvs es = ok s1 ->
  mn \in [:: BN_ADD; BN_SUB; BN_AND; BN_OR; BN_XOR; BN_CMP; BN_CMPB] ->
  sem_sopn (p_globs p) (Oasm (BaseOp (None, BN_basic_shift mn fg sh))) s0 lvs es''
  = ok s1.
Proof.
move=> hshift hsrc hmn.
have [e1 [e2 [es2 [ebase [esham [hes hgas hes'']]]]]] :=
  lower_basic_shift_binopE hmn hshift.
have hcomm : bn_basic_shift_commutes mn fg sh.
  by move=> wb wa x y vs r hsh hexec; exact: (bn_shifted_binopP hsh hexec hmn).
exact: (gen_lower_basic_shift_binopP hcomm hes hgas hes'' hsrc).
Qed.

(* [lower_basic_shiftP] (case lemma assembling the above): from
   [lower_basic_shift ii mn es = Some (sh, es'')] conclude the
   [BN_basic_shift] sem_sopn on [es''] equals the [BN_basic] sem_sopn on
   [es].  Dispatches to [lower_basic_shift_notP] (unop),
   [lower_basic_shift_addcP]/[lower_basic_shift_subbP] (carry terop), and
   [lower_basic_shift_binopP] (the seven standard binops). *)
Lemma lower_basic_shiftP ii mn fg lvs es sh es'' s0 s1 :
  lower_basic_shift ii mn es = ok (Some (sh, es'')) ->
  sem_sopn (p_globs p) (Oasm (BaseOp (None, BN_basic mn fg))) s0 lvs es = ok s1 ->
  sem_sopn (p_globs p) (Oasm (BaseOp (None, BN_basic_shift mn fg sh))) s0 lvs es''
  = ok s1.
Proof.
move=> hshift hsrc.
case: mn hshift hsrc.
(* BN_NOT (goal 7) - unop *)
7: exact: lower_basic_shift_notP.
(* BN_ADDC (goal 2) - carry terop *)
2: exact: lower_basic_shift_addcP.
(* BN_SUBB (goal 3 after 7+2 closed) - carry terop *)
3: exact: lower_basic_shift_subbP.
(* BN_ADD, BN_SUB, BN_AND, BN_OR, BN_XOR, BN_CMP, BN_CMPB - binop *)
all: move=> hshift hsrc; exact: (lower_basic_shift_binopP hshift hsrc ltac:(by vm_compute)).
Qed.

(* -------------------------------------------------------------------- *)
(* CARRY: [Oaddcarry sz]/[Osubcarry sz] -> [BN_basic (BN_ADD(C)/BN_SUB(B))
   FG1].  Model: ARM.  Mirror arm_lowering_proof.v [lower_add_carryP] and
   the arithmetic lemma [wunsigned_carry], plus [write_Lnone] for the dummy
   flag lvals.

   Call-site context (lower_copnP, carry branch): [sz = xreg_size] (U256),
   guaranteed by the [chk_xreg_ws] guard in [lower_carry_op] (the
   [ok (Some ..)] result means the assert passed); [is_add] selects
   add/sub.  [get_carry_lvals] matched [lvs = [:: cf; r]] (exactly two, as
   the source has two outputs) and produced
   [lvs' = [:: cf; lnoneb; lnoneb; lnoneb; r]].  [get_carry_pexprs] matched
   [es = [:: e0; e1; ecf]] with [ecf] either [Pbool false]
   (has_carry = false -> [BN_ADD]/[BN_SUB], [es' = [:: e0; e1]]) or a [Pvar]
   (has_carry = true -> [BN_ADDC]/[BN_SUBB], [es' = [:: e0; e1; ecf]]).

   Key definitions: [Oaddcarry_instr]/[Osubcarry_instr] (semi =
   [waddcarry]/[wsubcarry]), [desc_bn_basic_carry_binop] /
   [desc_bn_basic_binop] (semi = [semi_carry_binop_cmlz] / [with_cmlz],
   producing [CF_of_Z] then 3 m/l/z flags then the result),
   [get_carry_lvals], [get_carry_pexprs], [carry_op], [current_CF],
   [lnoneb]. *)

(* [lower_carry_opP] (case lemma): the lowered [BN_basic] sem_sopn
   reproduces the source [Oaddcarry]/[Osubcarry].  Idea (cf. ARM
   [lower_add_carryP]): unfold [lower_carry_op] (extract the
   [sz = xreg_size] assert, [get_carry_lvals], [get_carry_pexprs]); unfold
   both [sem_sopn].  Source [semi] is [waddcarry]/[wsubcarry]; target [semi]
   is [semi_carry_binop_cmlz] (has_carry) or [semi_binop_cmlz] (no carry).
   Use [waddsubcarry_cmlzP] to equate the carry flag and the result; the 3
   extra m/l/z flags are written to the [lnoneb] dummies, which are no-ops
   (write to [Lnone_b] is identity, cf. ARM [write_Lnone] / a general
   [write_lval] of [Lnone] lemma).  Split on [has_carry] ([Pvar] vs
   [Pbool false]). *)
Lemma lower_carry_opP ii is_add sz lvs es lvs' op' es' s0 s1 :
  let: op := if is_add then Oaddcarry else Osubcarry in
  lower_carry_op ii is_add sz lvs es = ok (Some (lvs', op', es')) ->
  sem_sopn (p_globs p) (Opseudo_op (op sz)) s0 lvs es
  = ok s1 ->
  sem_sopn (p_globs p) (Oasm op') s0 lvs' es' = ok s1.
Proof.
  rewrite /lower_carry_op /chk_xreg_ws.
  t_xrbindP=> /eqP ? hlvs hc es0 hes0 hli; subst sz.
  move: hc; rewrite /get_carry_lvals /rsnoc2 /rsnoc.
  case: lvs => [//|cf [//|r lvs_rest]] /= hcr.
  move: hcr => [?]; subst hlvs.
  move: hes0; rewrite /get_carry_pexprs /rsnoc3 /rsnoc2 /rsnoc /=.
  case: es => [//|e0 [//|e1 [//|ecf es_rest]]] /=.
  case: ecf => //= [b | g]; first case: b => //=.
  all: move=> [] /esym ?; subst es0.
  all: move: hli; rewrite /li_issue /= => [[<- <- <-]].
  case: is_add => /=.
  3: case: is_add => /=.
  (* ---- BN_ADD: no-carry, add ---- *)
  - move=> hsrc; move: hsrc; rewrite /sem_sopn /=.
    t_xrbindP=> v0 hv0 v1 hv1 hexec hwrite.
    move=> hv1'.
    move=> z4 z5 hz5 <- <- <- hexec2 hwrite2.
    rewrite hv1 hv1' /=.
    move: hexec2; rewrite /exec_sopn /= /sopn_sem /sopn_sem_ /=.
    t_xrbindP=> r1 w0 hw0 w1 hw1.
    case: z5 hz5 => [hz5 | a l hz5] /=.
    + move=> [<-] hres; rewrite -hres in hwrite2.
      move: hwrite2 => /=.
      t_xrbindP=> s_cf hcf s_r hr hlr.
      case: lvs_rest hlr => [[<-] | ? ? //].
      rewrite hw0 hw1.
      have hinner : (Let v := ok w0 in Let v2 := ok w1 in
        @semi_to_atype [:: lword256; lword256] (ty_cmlz ++ [:: lword256])
          (fun x y : u256 =>
            ok (with_cmlz (wadd x y) (wunsigned x + wunsigned y))) v v2)
        = ok (with_cmlz (wadd w0 w1)
            (wunsigned w0 + wunsigned w1)) := erefl.
      rewrite hinner; cbn - [with_cmlz].
      rewrite /with_cmlz /add_tuple /with_mlz.
      cbn [sem_ot eval_ltype ty_mlz ltuple].
      have [hCF hR] := waddsubcarry_cmlzP true w0 w1 false.
      rewrite Z.add_0_r in hCF.
      rewrite wrepr0 GRing.addr0 in hR.
      rewrite hCF /= hcf /= /write_none /=.
      change (word.word.add_word w0 w1) with ((w0 + w1)%w).
      by rewrite add_wordE hR /waddcarry /= hr /=.
    + by move=> //.
  (* ---- BN_SUB: no-carry, sub ---- *)
  - move=> hsrc; move: hsrc; rewrite /sem_sopn /=.
    t_xrbindP=> v0 hv0 v1 hv1 hexec hwrite.
    move=> hv1'; move=> z4 z5 hz5 <- <- <- hexec2 hwrite2.
    rewrite hv1 hv1' /=.
    move: hexec2; rewrite /exec_sopn /= /sopn_sem /sopn_sem_ /=.
    t_xrbindP=> r1 w0 hw0 w1 hw1.
    case: z5 hz5 => [hz5 | a l hz5] /=.
    2: by [].
    move=> [<-] hres; rewrite -hres in hwrite2.
    move: hwrite2 => /=.
    t_xrbindP=> s_cf hcf s_r hr hlr.
    case: lvs_rest hlr => [[<-] | ? ? //].
    rewrite hw0 hw1.
    have hinner : (Let v := ok w0 in Let v2 := ok w1 in
      @semi_to_atype [:: lword256; lword256] (ty_cmlz ++ [:: lword256])
        (fun x y : u256 => ok (with_cmlz (wsub x y)
          (Z.sub (wunsigned x) (wunsigned y)))) v v2)
      = ok (with_cmlz (wsub w0 w1)
          (Z.sub (wunsigned w0) (wunsigned w1))) := erefl.
    rewrite hinner; cbn - [with_cmlz].
    rewrite /with_cmlz /add_tuple /with_mlz.
    cbn [sem_ot eval_ltype ty_mlz ltuple].
    have [hCF hR] := waddsubcarry_cmlzP false w0 w1 false.
    rewrite Z.sub_0_r in hCF.
    rewrite wrepr0 GRing.subr0 in hR.
    rewrite hCF /= hcf /= /write_none /=.
    change (word.word.sub_word w0 w1) with ((w0 - w1)%w).
    change (word.word.add_word w0 (word.word.opp_word w1)) with ((w0 - w1)%R).
    rewrite hR /wsubcarry /= hr /=.
    done.
  (* ---- BN_ADDC: carry, add ---- *)
  - move=> hsrc; move: hsrc; rewrite /sem_sopn /=.
    t_xrbindP=> v0 hv0 v1 hv1 hexec hwrite.
    move=> hv1' hcarry hcarry_proof.
    move=> hv2 z6 hz6 <- <- <- hexec2 hwrite2.
    rewrite hv1 hv1' hv2 /=.
    move: hexec2; rewrite /exec_sopn /= /sopn_sem /sopn_sem_ /=.
    t_xrbindP=> r1 w0 hw0 w1 hw1 b_carry hbcarry.
    case: z6 hz6 => [hz6 | a l hz6] /=.
    2: by move=> //.
    move=> [<-] hres; rewrite -hres in hwrite2.
    move: hwrite2 => /=.
    t_xrbindP=> s_cf hcf s_r hr hlr.
    case: lvs_rest hlr => [[<-] | ? ? //].
    rewrite hw0 hw1 hbcarry.
    have hinner : (Let v := ok w0 in Let v2 := ok w1 in Let v3 := ok b_carry in
      @semi_to_atype [:: lword256; lword256; lbool] (ty_cmlz ++ [:: lword256])
        (semi_carry_binop_cmlz wadd Z.add) v v2 v3)
      = ok (with_cmlz (wadd (wadd w0 w1) (wrepr U256 (Z.b2z b_carry)))
          (Z.add (Z.add (wunsigned w0) (wunsigned w1))
            (Z.b2z b_carry))) := erefl.
    rewrite hinner; cbn - [with_cmlz].
    rewrite /with_cmlz /add_tuple /with_mlz.
    cbn [sem_ot eval_ltype ty_mlz ltuple].
    have [hCF hR] := waddsubcarry_cmlzP true w0 w1 b_carry.
    rewrite hCF /= hcf /= /write_none /=.
    change (word.word.add_word (word.word.add_word w0 w1)
             (wrepr U256 (Z.b2z b_carry)))
      with (((w0 + w1) + wrepr U256 (Z.b2z b_carry))%R).
    by rewrite hR /waddcarry /= hr /=.
  (* ---- BN_SUBB: carry, sub ---- *)
  - move=> hsrc; move: hsrc; rewrite /sem_sopn /=.
    t_xrbindP=> v0 hv0 v1 hv1 hexec hwrite.
    move=> hv1' hcarry hcarry_proof.
    move=> hv2 z6 hz6 <- <- <- hexec2 hwrite2.
    rewrite hv1 hv1' hv2 /=.
    move: hexec2; rewrite /exec_sopn /= /sopn_sem /sopn_sem_ /=.
    t_xrbindP=> r1 w0 hw0 w1 hw1 b_carry hbcarry.
    case: z6 hz6 => [hz6 | a l hz6] /=.
    2: by move=> //.
    move=> [<-] hres; rewrite -hres in hwrite2.
    move: hwrite2 => /=.
    t_xrbindP=> s_cf hcf s_r hr hlr.
    case: lvs_rest hlr => [[<-] | ? ? //].
    rewrite hw0 hw1 hbcarry.
    have hinner : (Let v := ok w0 in Let v2 := ok w1 in Let v3 := ok b_carry in
      @semi_to_atype [:: lword256; lword256; lbool] (ty_cmlz ++ [:: lword256])
        (semi_carry_binop_cmlz wsub Z.sub) v v2 v3)
      = ok (with_cmlz (wsub (wsub w0 w1) (wrepr U256 (Z.b2z b_carry)))
          (Z.sub (Z.sub (wunsigned w0) (wunsigned w1))
            (Z.b2z b_carry))) := erefl.
    rewrite hinner; cbn - [with_cmlz].
    rewrite /with_cmlz /add_tuple /with_mlz.
    cbn [sem_ot eval_ltype ty_mlz ltuple].
    have [hCF hR] := waddsubcarry_cmlzP false w0 w1 b_carry.
    rewrite hCF /= hcf /= /write_none /=.
    change (word.word.add_word
             (word.word.add_word w0 (word.word.opp_word w1))
             (word.word.opp_word (wrepr U256 (Z.b2z b_carry))))
      with (((w0 - w1) - wrepr U256 (Z.b2z b_carry))%R).
    by rewrite hR /wsubcarry /= hr /=.
Qed.

(* -------------------------------------------------------------------- *)
Lemma lower_swapP ii ty lvs es lvs' op' es' s0 s1 :
  lower_swap ii ty lvs es = ok (Some (lvs', op', es')) ->
  sem_sopn (p_globs p) (Opseudo_op (Oswap ty)) s0 lvs es = ok s1 ->
  sem_sopn (p_globs p) (Oasm op') s0 lvs' es' = ok s1.
Proof.
  rewrite /lower_swap.
  case: ty => [| | ws len | sz] //=.
  case: ifP => [/eqP -> | hneq_reg].
    move=> /= [<- <- <-] hsrc.
    by rewrite /sem_sopn /exec_sopn /= in hsrc.
  case: ifP => [/eqP -> | //] /=.
  move=> /= [<- <- <-] hsrc.
  rewrite /sem_sopn.
  move: hsrc; rewrite /sem_sopn.
  move=> hsrc; move: hsrc.
  rewrite /exec_sopn /= /sopn_sem /sopn_sem_ /=.
  t_xrbindP => vs r.
  move=> hr t htexec hvs hw.
  rewrite hr /=.
  move: hr htexec hw.
  case: r.
  - by move=> _ /=.
  move=> a; case.
  - move=> _ htmp _; case: (to_word U256 a) htmp => //.
  move=> a0 l hr; move: hr; case: l.
  - move=> _ hw_exec hw_write.
    move: hw_exec; t_xrbindP => w0 hw0 w1 hw1 ht.
    rewrite hw0 hw1 /= /MF_of_word /LF_of_word /ZF_of_word /=.
    rewrite -ht /swap_semi /= in hvs.
    rewrite -hvs in hw_write.
    exact: hw_write.
  by move=> c rest _ /=;
     case: (to_word U256 a) => //;
     move=> w; case: (to_word U256 a0) => //.
Qed.

(* [lower_copnP]: assemble the case lemmas.  Four cases pass [pre = [::]]
   through unchanged (shift absorption / carry / swap / [RV32 mn]); the
   [ExtOp SELECT] case additionally runs the [BN.CMP] prefix [lower_cmp]
   may produce, landing in an [eq_fv]-related state. *)
Lemma lower_copnP (p' : prog) (hglob : p_globs p' = p_globs p)
  ii tag lvs op es pre lvs' op' es' s0 s1 :
  lower_copn ii lvs op es = ok (Some (pre, lvs', op', es')) ->
  disj_fvars (read_es es) ->
  disj_fvars (vars_lvals lvs) ->
  sem_sopn (p_globs p) op s0 lvs es = ok s1 ->
  exists2 s1',
    esem p' ev (low_cmd_c ii tag (pre, lvs', op', es')) s0 = ok s1'
    & eq_fv s1 s1'.
Proof using atoI dc ev fv fv_correct p pT sCP sc_sem syscall_state wsw.
move=> hlow hdisjes hdisjlvs hsem.
rewrite /lower_copn in hlow.
case: op hsem hlow => [pop | slh | aop] hsem hlow //=.
move: hlow; rewrite /no_pre /lower_pseudo_operator; t_xrbindP=> oa hM ob hli hmatch.
case: pop hsem ob => [so aty | wz z | aty2 | z2 | | sz1 | sz2 | sz3 | ty] hsem ob.
all: try done.
1-5: by move: ob hli hmatch => /= -[<-] -[<-] //.
case: hM ob hli hmatch => [[[lvsX opX] esX]|] ob hli hmatch //=.
have hoa : oa = Some (lvsX, opX, esX) by case: hli.
rewrite hoa in hmatch.
move: hmatch; rewrite /lc_sissue /issue => -[] h1 h2 h3 h4; subst pre lvs' op' es'.
simpl.
have [s1' hsem0 heqfv] := esem_no_pre_of_sem_sopn hglob ii tag (lower_carry_opP ob hsem).
exists s1'; last exact: heqfv.
by move: hsem0; rewrite /low_cmd_c /=.
have hoa : oa = None by case: hli.
by rewrite hoa in hmatch.
case: hM ob hli hmatch => [[[lvsX opX] esX]|] ob hli hmatch //=.
have hoa : oa = Some (lvsX, opX, esX) by case: hli.
rewrite hoa in hmatch.
move: hmatch; rewrite /lc_sissue /issue => -[] h1 h2 h3 h4; subst pre lvs' op' es'.
simpl.
have [s1' hsem0 heqfv] := esem_no_pre_of_sem_sopn hglob ii tag (lower_carry_opP ob hsem).
exists s1'; last exact: heqfv.
by move: hsem0; rewrite /low_cmd_c /=.
have hoa : oa = None by case: hli.
by rewrite hoa in hmatch.
case: hM ob hli hmatch => [[[lvsX opX] esX]|] ob hli hmatch //=.
have hoa : oa = Some (lvsX, opX, esX) by case: hli.
rewrite hoa in hmatch.
move: hmatch; rewrite /lc_sissue /issue => -[] h1 h2 h3 h4; subst pre lvs' op' es'.
simpl.
have [s1' hsem0 heqfv] := esem_no_pre_of_sem_sopn hglob ii tag (lower_swapP ob hsem).
exists s1'; last exact: heqfv.
by move: hsem0; rewrite /low_cmd_c /=.
have hoa : oa = None by case: hli.
by rewrite hoa in hmatch.
case: aop hsem hlow => [[m aop]|eo] hsem hlow //=.
case: m hsem hlow => [cf|] hsem hlow //=.
move: hlow; rewrite /no_pre; t_xrbindP=> o hbop hmatch2.
case: o hbop hmatch2 => [[[lvsX opX] esX]|] hbop hmatch2 //=.
move: hmatch2; rewrite /lc_sissue /issue => -[] h1 h2 h3 h4; subst pre lvs' op' es'.
simpl.
case: aop hbop hsem => //=.
move=> r; rewrite /li_issue /li_sissue /issue => -[] h1 h2 h3 hsem; subst lvsX opX esX.
have [s1' hsem0 heqfv] := esem_no_pre_of_sem_sopn hglob ii tag hsem.
exists s1'; last exact: heqfv.
by move: hsem0; rewrite /low_cmd_c /=.
move=> mn fg; t_xrbindP=> o hshift hli hsem.
case: o hshift hli => [[sh es'']|] hshift hli //=.
move: hli; rewrite /li_issue /li_sissue /issue => -[] h1 h2 h3; subst lvsX opX esX.
simpl.
have [s1' hsem0 heqfv] := esem_no_pre_of_sem_sopn hglob ii tag (lower_basic_shiftP hshift hsem).
exists s1'; last exact: heqfv.
by move: hsem0; rewrite /low_cmd_c /=.
case: eo hsem hlow => [] hsem hlow //=.
case: es hsem hdisjes hlow => [|e0 [|e1 [|econd [|]]]] hsem hdisjes hlow //=.
move: hlow; t_xrbindP=> o hoe hmatch.
case: o hoe hmatch => [[pre0 econd']|] hoe hmatch //=.
move: hmatch; rewrite /lc_xissue /lc_sissue /issue => -[] h1 h2 h3 h4; subst pre lvs' op' es'.
have hdisj3 : disj_fvars (read_e e0) /\ disj_fvars (read_e e1) /\ disj_fvars (read_e econd).
  have e01 := read_es_cons e0 [:: e1; econd].
  have e11 := read_es_cons e1 [:: econd].
  have e21 := read_es_cons econd [::].
  move: hdisjes => hdisjes'.
  split; last split; apply: disjoint_w hdisjes'; SvD.fsetdec.
have [hdisj_e0 [hdisj_e1 hdisj_econd]] := hdisj3.
move: hsem; rewrite /sem_sopn /exec_sopn /= /sopn_sem /sopn_sem_ /=.
t_xrbindP=> zlist zvs v0 hv0 zvs1 v1 hv1 zvs2 vc hvc heq1 heq2 heq3 vres hmatch heq4 hwrite.
subst zvs2 zvs1 zvs zlist.
move: hmatch; t_xrbindP=> w0 hw0 w1 hw1 b hb ?; subst vres.
have [t hsem_t [heqt hval_t]] := lower_cmpP tag hoe (eeq_excR fvars s0) hdisj_econd hvc hb.
rewrite -cats1 map_cat esem_cat (esem_low_instr_i_glob ev ev ii tag pre0 s0 hglob) hsem_t /=.
rewrite hglob.
have he0t := eeq_exc_sem_pexpr hdisj_e0 heqt hv0.
have he1t := eeq_exc_sem_pexpr hdisj_e1 heqt hv1.
rewrite /sem_sopn /exec_sopn /= /sopn_sem /sopn_sem_ /= he0t he1t hval_t /= hw0 hw1 /=.
have [s1' hw' heq'] := eeq_exc_write_lvals hdisjlvs heqt hwrite.
exists s1'; last exact: heq'.
by rewrite /= hw'.
Qed.

Lemma Hopn_esem (p' : prog) (hglob : p_globs p' = p_globs p)
  {ii lvs tag op es s0 s1 lc} :
  disj_fvars (read_es es) ->
  disj_fvars (vars_lvals lvs) ->
  sem_sopn (p_globs p) op s0 lvs es = ok s1 ->
  lower_i (MkI ii (Copn lvs tag op es)) = ok lc ->
  exists2 s1', esem p' ev lc s0 = ok s1' & eq_fv s1 s1'.
Proof using atoI dc ev fv fv_correct p pT sCP sc_sem syscall_state wsw.
move=> hdisjes hdisjlvs hsem hlc.
move: hlc; rewrite /lower_i /=; t_xrbindP=> oargs hoargs <-.
case: oargs hoargs => [[[[pre lvs'] op'] es']|] hoargs.
simpl.
have [s1' hsem0 heqfv] := lower_copnP hglob tag hoargs hdisjes hdisjlvs hsem.
exists s1'; last exact: heqfv.
by move: hsem0; rewrite /low_cmd_c /=.
simpl.
exists s1; last exact: eeq_excR.
by rewrite hglob hsem.
Qed.

(* -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)

Section IT.

Context {E E0: Type -> Type} {wE : with_Error E E0} {rE0 : EventRels E0}.

(* [Pi_]/[Pc_] carry [disj_fvars] hypotheses (the fresh flags are not read or
   written by the source program) and relate states with [eq_fv] rather than
   exact equality, since a lowered [BN.CMP] prefix may set them. *)
#[ local ]
Definition Pi_ (p' : prog) (i : instr) :=
  disj_fvars (vars_I i) ->
  forall lc, lower_i i = ok lc ->
  wequiv_rec p p' ev ev eq_spec eq_fv [:: i] lc eq_fv.

#[ local ]
Definition Pi_r_ (p' : prog) (i : instr_r) := forall ii, Pi_ p' (MkI ii i).

#[ local ]
Definition Pc_ (p' : prog) (c : cmd) :=
  disj_fvars (vars_c c) ->
  forall lc, lower_cmd c = ok lc ->
  wequiv_rec p p' ev ev eq_spec eq_fv c lc eq_fv.

Lemma it_lower_callP fn lp :
  lower_prog p = ok lp ->
  wiequiv_f p lp ev ev (rpreF (eS:= eq_spec)) fn fn (rpostF (eS:=eq_spec)).
Proof using atoI dc ev fv fv_correct p pT sCP sc_sem syscall_state wsw.
move=> hlp.
apply wequiv_fun_ind => {}fn _ fs _ [<- <-] fd hget.
have [_ hfvres hfvc] := disj_fvars_get_fundef fv_correct hget.
move: hlp; rewrite /lower_prog; t_xrbindP=> fns hfns <- /=.
have [fd' hlfd hgetfd'] := get_map_cfprog_gen hfns hget.
rewrite hgetfd'.
eexists; first reflexivity.
move: hlfd; rewrite /lower_fd; t_xrbindP=> body hbody ?; subst fd'.
move=> s.
move=> /(eq_initialize (fd':= with_body fd body))
  -/(_ {| p_funcs := fns; p_globs := p_globs p; p_extra := p_extra p |}
       erefl erefl erefl erefl) hinit.
exists s => //.
exists eq_fv, eq_fv; split => //=; last by apply st_eq_ex_finalize.
have hPc : Pc_ {| p_funcs := fns; p_globs := p_globs p; p_extra := p_extra p |} (f_body fd).
2:{ exact: (hPc hfvc body hbody). }
set lp' := {| p_funcs := fns; p_globs := p_globs p; p_extra := p_extra p |}.
set sip := sip_of_asm_e.
apply (cmd_rect (Pr := Pi_r_ lp') (Pi := Pi_ lp') (Pc := Pc_ lp')) => //;
  rewrite /Pi_r_ /Pi_ /Pc_.
- by move=> _ lc /lower_cmd_nil ->; apply (wequiv_nil (sip:=sip) p lp' ev ev).
- move=> i c hi hc /disj_fvars_vars_c_cons [hdi hdc] lc
    /lower_cmd_cons [li [lc' [hli hlc' ->]]].
  rewrite -cat1s.
  apply (wequiv_cat (sip:=sip)) with eq_fv.
  + exact: hi hdi li hli.
  exact: hc hdc lc' hlc'.
- move=> x tg ty e ii /disj_fvars_vars_I_Cassgn [hfvlv hfve] lc hlc.
  apply (wequiv_assgn_esem (sip:=sip)).
  move=> s0 s0' s1 hs00; rewrite /sem_assgn; t_xrbindP => v hseme v' htrunc hwrite.
  have [s1' hwrite' hs11] := eeq_exc_write_lval hfvlv hs00 hwrite.
  have hassgn : sem_assgn (sip:=sip) p x tg ty e s0' = ok s1'.
  - by rewrite /sem_assgn (eeq_exc_sem_pexpr hfve hs00 hseme) /= htrunc /= hwrite'.
  have [s2' hsem02' hs12'] := Hassgn_esem (erefl : p_globs lp' = p_globs p) hfve hfvlv hassgn hlc.
  exists s2'; last exact: (eeq_excT hs11 hs12').
  exact: hsem02'.
- move=> xs tg o es ii /disj_fvars_vars_I_Copn [hfvlvs hfves] lc hlc.
  apply (wequiv_opn_esem (sip:=sip)).
  move=> s0 s0' s1 hs00; rewrite /sem_sopn; t_xrbindP => ves vs hsemes hexec hwrite.
  have [s1' hwrite' hs11] := eeq_exc_write_lvals hfvlvs hs00 hwrite.
  have hopn : sem_sopn (p_globs p) o s0' xs es = ok s1'.
  - by rewrite /sem_sopn (eeq_exc_sem_pexprs hfves hs00 hsemes) /= hexec /= hwrite'.
  have [s2' hsem02' hs12'] := Hopn_esem (erefl : p_globs lp' = p_globs p) hfves hfvlvs hopn hlc.
  exists s2'; last exact: (eeq_excT hs11 hs12').
  exact: hsem02'.
- move=> xs o es ii; rewrite /disj_fvars vars_I_syscall => /disjoint_union [hdisjx hdisje] lc /= [<-].
  apply (wequiv_syscall_rel_eq (sip:=sip) (d:=fvars) (de:=fvars) (d':=fvars)
    (cu:=checker_st_eq_exP (sip:=sip) (erefl : p_globs p = p_globs lp')) ev ev).
  - by split.
  - by split.
- by move=> a ii _ lc _; exact: (wequiv_noassert (sip:=sip) p lp' ev ev ii a lc eq_fv).
- move=> e c1 c2 hc1 hc2 ii /disj_fvars_vars_I_Cif [hfve hdc1 hdc2] lc.
  rewrite /lower_i /=; t_xrbindP=> c1' hc1' c2' hc2' <-.
  apply (wequiv_if_rel_eq (sip:=sip)
    (cu:=checker_st_eq_exP (sip:=sip) (erefl : p_globs p = p_globs lp'))
    (d:=fvars) (de:=fvars) (d1:=fvars) (d2:=fvars) (d':=fvars) ii ii).
  + by split.
  + by [].
  + by [].
  + exact: hc1 hdc1 c1' hc1'.
  exact: hc2 hdc2 c2' hc2'.
- move=> fi c hc ii /disj_fvars_vars_I_Cfor [hfvfi hfvuc] lc.
  rewrite /lower_i /=; t_xrbindP=> c' hc' <-.
  case: fi hc hfvfi hfvuc c' hc' => [i dir lo hi | e] hc hfvfi hfvuc c' hc'.
  + have hfvlo : disj_fvars (read_e lo).
    - apply: (disjoint_w _ hfvfi); rewrite /read_fi /read_fi_rec /= !read_eE; SvD.fsetdec.
    have hfvhi : disj_fvars (read_e hi).
    - apply: (disjoint_w _ hfvfi); rewrite /read_fi /read_fi_rec /= !read_eE; SvD.fsetdec.
    have hfvw : disj_fvars (Sv.add i (vars_c c)).
    - apply: (disjoint_w _ hfvuc); rewrite /write_fi /write_fi_rec /=; SvD.fsetdec.
    have [_ hdc] := disj_fvars_Cfor_c hfvw.
    apply (wequiv_for_rel_eq (sip:=sip)
      (cu:=checker_st_eq_exP (sip:=sip) (erefl : p_globs p = p_globs lp'))
      (d0:=fvars) (d:=fvars) (dhi:=fvars) (di:=fvars) ii dir ii).
    * split=>//.
      apply: (disjoint_w _ (union_disjoint hfvlo hfvhi)).
      have e1 := read_es_cons lo [:: hi].
      have e2 := read_es_cons hi [::].
      SvD.fsetdec.
    * by [].
    have [hdvi _] := disj_fvars_Cfor_c hfvw.
    split=>//.
    exact: hc hdc c' hc'.
  have hfve : disj_fvars (read_e e).
  - apply: (disjoint_w _ hfvfi); rewrite /read_fi /read_fi_rec /=; SvD.fsetdec.
  have hfvcc : disj_fvars (vars_c c).
  - apply: (disjoint_w _ hfvuc); rewrite /write_fi /write_fi_rec /=; SvD.fsetdec.
  apply (wequiv_for_repeat_rel_eq (sip:=sip)
    (cu:=checker_st_eq_exP (sip:=sip) (erefl : p_globs p = p_globs lp'))
    (d0:=fvars) (d:=fvars) (de:=fvars) ii ii).
  - split=>//.
  - by [].
  exact: hc hfvcc c' hc'.
- move=> a c e info c' hc hc' ii /disj_fvars_vars_I_Cwhile [hdc hfve hdc'] lc.
  rewrite /lower_i /=; t_xrbindP=> c0' hc0' c1' hc1' <-.
  apply (wequiv_while_rel_eq (sip:=sip)
    (cu:=checker_st_eq_exP (sip:=sip) (erefl : p_globs p = p_globs lp'))
    (d:=fvars) (d':=fvars) (de:=fvars) ii a info info a info).
  + by split.
  + exact: hc hdc c0' hc0'.
  exact: hc' hdc' c1' hc1'.
move=> xs f es ii /disj_fvars_vars_I_Ccall [hdxs hfes] lc /= [<-].
apply (wequiv_call_rel_eq (sip:=sip)
  (cu:=checker_st_eq_exP (sip:=sip) (erefl : p_globs p = p_globs lp'))
  (d:=fvars) (de:=fvars) (d':=fvars)).
+ by split.
+ by split.
by move=>???; apply: (wequiv_fun_rec (spec := eq_spec)).
Qed.

End IT.

End PROOF.
