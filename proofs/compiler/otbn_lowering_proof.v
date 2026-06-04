From mathcomp Require Import ssreflect ssrfun ssrbool eqtype order ssralg.
Import
  Order.POrderTheory
  Order.TotalTheory.
From mathcomp Require Import word_ssrZ.

Require Import
  compiler_util
  expr
  lowering
  lowering_lemmas
  psem
  utils.
Require Import
  arch_extra
  sem_params_of_arch_extra.
Require Import
  otbn_decl
  otbn_extra
  otbn_instr_decl
  otbn_lowering.

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
  (options : lowering_options)
  (warning : instr_info -> warning_msg -> instr_info)
  (fv : lowering.fresh_vars).

Notation lower_cmd :=
  (lower_cmd
     (fun _ _ _ => lower_i)
     options
     warning
     fv).
Notation lower_prog :=
  (lower_prog
     (fun _ _ _ => lower_i)
     options
     warning
     fv).

(* -------------------------------------------------------------------- *)
(* Plumbing: the OTBN lowering is genuinely monadic ([lower_i] can fail
   and produces a [cmd]), so [lower_cmd] = [conc_mapM lower_i] and
   [lower_prog] threads through [map_cfprog]. The following lemmas expose
   the structure of a successful lowering. *)

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
  map_cfprog (lower_fd (fun _ _ _ => lower_i) options warning fv) (p_funcs p)
  = ok (p_funcs lp).
Proof. by rewrite /lower_prog; t_xrbindP=> fns hfns <-. Qed.

(* -------------------------------------------------------------------- *)
(* Leaf correctness lemmas, admitted. These are the OTBN analogs of the
   RISC-V [Hassgn_esem] / [Hopn_esem] lemmas: they state that the lowered
   straight-line code for an assignment / [Copn] reproduces the source
   semantics. They decompose further into per-construct lemmas about
   [lower_cassgn_word], [lower_copn], [lower_base_op], [lower_swap],
   [get_arg_shift], ... (TODO_OTBN). *)

Lemma Hassgn_esem (p' : prog) (hglob : p_globs p' = p_globs p)
  {ii lv tag ty e s0 s1 lc} :
  sem_assgn p lv tag ty e s0 = ok s1 ->
  lower_i (MkI ii (Cassgn lv tag ty e)) = ok lc ->
  esem p' ev lc s0 = ok s1.
Proof.
Admitted.

Lemma Hopn_esem (p' : prog) (hglob : p_globs p' = p_globs p)
  {ii lvs tag op es s0 s1 lc} :
  sem_sopn (p_globs p) op s0 lvs es = ok s1 ->
  lower_i (MkI ii (Copn lvs tag op es)) = ok lc ->
  esem p' ev lc s0 = ok s1.
Proof.
Admitted.

(* -------------------------------------------------------------------- *)

Section SEM.

Context (p' : prog) (hp' : lower_prog p = ok p').

Let hglob : p_globs p' = p_globs p := lower_prog_globs hp'.

#[ local ]
Definition Pi (s0 : estate) (i : instr) (s1 : estate) :=
  forall lc, lower_i i = ok lc -> sem p' ev s0 lc s1.

#[ local ]
Definition Pi_r (s0 : estate) (i : instr_r) (s1 : estate) :=
  forall ii, Pi s0 (MkI ii i) s1.

#[ local ]
Definition Pc (s0 : estate) (c : cmd) (s1 : estate) :=
  forall lc, lower_cmd c = ok lc -> sem p' ev s0 lc s1.

#[ local ]
Definition Pfor
  (oi : option var_i) (rng : seq Z) (s0 : estate) (c : cmd) (s1 : estate) :=
  forall lc, lower_cmd c = ok lc -> sem_for p' ev oi rng s0 lc s1.

#[ local ]
Definition Pfun
  scs0 (m0 : mem) (fn : funname) (vargs : seq value) scs1 (m1 : mem)
  (vres : seq value) :=
  sem_call p' ev scs0 m0 fn vargs scs1 m1 vres.

#[ local ]
Lemma Hskip : sem_Ind_nil Pc.
Proof. by move=> s lc /lower_cmd_nil ->; apply: (Eskip p' ev). Qed.

#[ local ]
Lemma Hcons : sem_Ind_cons p ev Pc Pi.
Proof.
  move=> s1 s2 s3 i c _ hpi _ hpc lc /lower_cmd_cons [li [lc' [hli hlc' ->]]].
  exact: (sem_app (hpi _ hli) (hpc _ hlc')).
Qed.

#[ local ]
Lemma HmkI : sem_Ind_mkI p ev Pi_r Pi.
Proof. by move=> ii i s1 s2 _ hi; apply: hi. Qed.

#[ local ]
Lemma Hassgn : sem_Ind_assgn p Pi_r.
Proof.
  move=> s1 s2 x tag ty e v v' he htr hw ii lc hlc.
  apply: esem_sem.
  apply: (Hassgn_esem hglob _ hlc).
  by rewrite /sem_assgn he /= htr /= hw.
Qed.

#[ local ]
Lemma Hopn : sem_Ind_opn p Pi_r.
Proof.
  move=> s0 s1 tag op lvs es hsem01 ii lc hlc.
  apply: esem_sem.
  exact: (Hopn_esem hglob hsem01 hlc).
Qed.

#[ local ]
Lemma Hsyscall : sem_Ind_syscall p Pi_r.
Proof.
  move=> s1 scs m s2 o xs es ves vs hes ho hw ii lc [<-].
  apply: sem_seq_ir.
  apply: Esyscall.
  - rewrite hglob; exact: hes.
  - exact: ho.
  - rewrite hglob; exact: hw.
Qed.

#[ local ]
Lemma Hif_true : sem_Ind_if_true p ev Pc Pi_r.
Proof.
  move=> s0 s1 e c0 c1 hseme _ hc ii lc /=.
  t_xrbindP=> c0' hc0' c1' hc1' <-.
  apply: sem_seq_ir.
  apply: Eif_true; first by rewrite hglob; exact: hseme.
  exact: (hc _ hc0').
Qed.

#[ local ]
Lemma Hif_false : sem_Ind_if_false p ev Pc Pi_r.
Proof.
  move=> s0 s1 e c0 c1 hseme _ hc ii lc /=.
  t_xrbindP=> c0' hc0' c1' hc1' <-.
  apply: sem_seq_ir.
  apply: Eif_false; first by rewrite hglob; exact: hseme.
  exact: (hc _ hc1').
Qed.

#[ local ]
Lemma Hwhile_true : sem_Ind_while_true p ev Pc Pi_r.
Proof.
  move=> s0 s1 s2 s3 al c0 e info c1 _ hc0 hseme _ hc1 _ hwhile ii lc /=.
  t_xrbindP=> c0' hc0' c1' hc1' ?; subst lc.
  apply: sem_seq_ir.
  apply: Ewhile_true.
  - exact: (hc0 _ hc0').
  - rewrite hglob; exact: hseme.
  - exact: (hc1 _ hc1').
  have hrec :
    lower_i (MkI ii (Cwhile al c0 e info c1))
    = ok [:: MkI info (Cwhile al c0' e info c1') ].
  - by rewrite /= hc0' /= hc1'.
  have := hwhile ii _ hrec.
  by move=> /sem_seq1_iff /sem_IE.
Qed.

#[ local ]
Lemma Hwhile_false : sem_Ind_while_false p ev Pc Pi_r.
Proof.
  move=> s0 s1 al c0 e info c1 _ hc0 hseme ii lc /=.
  t_xrbindP=> c0' hc0' c1' hc1' <-.
  apply: sem_seq_ir.
  apply: Ewhile_false; last by rewrite hglob; exact: hseme.
  exact: (hc0 _ hc0').
Qed.

#[ local ]
Lemma Hfor : sem_Ind_for p ev Pi_r Pfor.
Proof.
  move=> s0 s1 fi c rn hfi _ hfor ii lc /=.
  t_xrbindP=> c' hc' <-.
  apply: sem_seq_ir.
  apply: Efor; first by rewrite hglob; exact: hfi.
  exact: (hfor _ hc').
Qed.

#[ local ]
Lemma Hfor_nil : sem_Ind_for_nil Pfor.
Proof. by move=> s0 oi c lc _; apply: EForDone. Qed.

#[ local ]
Lemma Hfor_cons : sem_Ind_for_cons p ev Pc Pfor.
Proof.
  move=> s0 s1 s2 s3 oi v vs c hwrite _ hc _ hfor lc hlc.
  apply: EForOne.
  - exact: hwrite.
  - exact: (hc _ hlc).
  exact: (hfor _ hlc).
Qed.

#[ local ]
Lemma Hcall : sem_Ind_call p ev Pi_r Pfun.
Proof.
  move=> s0 scs0 m0 s1 lvs fn args vargs vs hsemargs _ hfun hwrite ii lc [<-].
  apply: sem_seq_ir.
  apply: Ecall.
  - rewrite hglob; exact: hsemargs.
  - exact: hfun.
  - rewrite hglob; exact: hwrite.
Qed.

#[ local ]
Lemma Hproc : sem_Ind_proc p ev Pc Pfun.
Proof.
  move=> scs0 m0 scs1 m1 fn fd vargs vargs' s0 s1 s2 vres vres'.
  move=> hget htruncargs hinit hwrite _ hc hres htruncres hscs hfin.
  rewrite /Pfun.
  have [fd' hlfd hget'] := get_map_cfprog_gen (lower_prog_funcs hp') hget.
  move: hlfd; rewrite /lower_fd; t_xrbindP=> body hbody ?; subst fd'.
  apply: EcallRun.
  - exact: hget'.
  - exact: htruncargs.
  - rewrite (lower_prog_extra hp'); exact: hinit.
  - exact: hwrite.
  - exact: (hc _ hbody).
  - exact: hres.
  - exact: htruncres.
  - exact: hscs.
  exact: hfin.
Qed.

Lemma lower_callP_total
  (f : funname) scs mem scs' mem' (va vr : seq value) :
  sem_call p ev scs mem f va scs' mem' vr
  -> sem_call p' ev scs mem f va scs' mem' vr.
Proof.
  exact:
    (sem_call_Ind
       Hskip
       Hcons
       HmkI
       Hassgn
       Hopn
       Hsyscall
       Hif_true
       Hif_false
       Hwhile_true
       Hwhile_false
       Hfor
       Hfor_nil
       Hfor_cons
       Hcall
       Hproc).
Qed.

End SEM.

Lemma lower_callP
  (f : funname) scs mem scs' mem' (va vr : seq value) lp :
  lower_prog p = ok lp ->
  sem_call p ev scs mem f va scs' mem' vr
  -> sem_call lp ev scs mem f va scs' mem' vr.
Proof. move=> hlp; exact: (lower_callP_total hlp). Qed.

(* -------------------------------------------------------------------- *)

Section IT.

Context {E E0: Type -> Type} {wE : with_Error E E0} {rE0 : EventRels E0}.

#[ local ]
Definition Pi_ (p' : prog) (i : instr) :=
  forall lc, lower_i i = ok lc ->
  wequiv_rec p p' ev ev eq_spec (st_eq tt) [:: i] lc (st_eq tt).

#[ local ]
Definition Pi_r_ (p' : prog) (i : instr_r) := forall ii, Pi_ p' (MkI ii i).

#[ local ]
Definition Pc_ (p' : prog) (c : cmd) :=
  forall lc, lower_cmd c = ok lc ->
  wequiv_rec p p' ev ev eq_spec (st_eq tt) c lc (st_eq tt).

#[ local ]
Lemma checker_st_eqP_ p' : p_globs p = p_globs p' -> Checker_eq p p' checker_st_eq.
Proof. exact: checker_st_eqP. Qed.

Lemma it_lower_callP fn lp :
  lower_prog p = ok lp ->
  wiequiv_f p lp ev ev (rpreF (eS:= eq_spec)) fn fn (rpostF (eS:=eq_spec)).
Proof.
  move=> hlp.
  have hglob := lower_prog_globs hlp.
  apply wequiv_fun_ind => {}fn _ fs _ [<- <-] fd hget.
  have [fd' hlfd hget'] := get_map_cfprog_gen (lower_prog_funcs hlp) hget.
  move: hlfd; rewrite /lower_fd; t_xrbindP=> body hbody ?; subst fd'.
  rewrite hget' /=.
  eexists; first reflexivity.
  move=> s.
  move=> /(eq_initialize (fd':= with_body fd body))
    -/(_ lp erefl erefl erefl (esym (lower_prog_extra hlp))) hinit.
  exists s => //; exists (st_eq tt), (st_eq tt); split => //=;
    last by apply st_eq_finalize.
  have hck := checker_st_eqP_ (p' := lp) (esym hglob).
  set sip := sip_of_asm_e.
  suff hsuff : forall c, Pc_ lp c by apply: (hsuff _ _ hbody).
  apply (cmd_rect (Pr := Pi_r_ lp) (Pi := Pi_ lp) (Pc := Pc_ lp));
    rewrite /Pi_r_ /Pi_ /Pc_.
  + by move=> i ii hi; apply: hi.
  + by move=> lc /lower_cmd_nil ->; apply (wequiv_nil (sip:=sip)).
  + move=> i c hi hc lc /lower_cmd_cons [li [lc' [hli hlc' ->]]].
    rewrite -cat1s.
    by apply (wequiv_cat (sip:=sip)) with (st_eq tt);
      [apply: (hi _ hli) | apply: (hc _ hlc')].
  (* Cassgn *)
  + move=> x tg ty e ii lc hlc.
    apply (wequiv_assgn_esem (sip:=sip)).
    move=> s0 t s1 /st_relP [-> /= heq] hsem.
    have [vm2 -> ?] :=
      esem_vm_eq (sip:=sip) (erefl (p_globs lp))
        (Hassgn_esem hglob hsem hlc) heq.
    by eexists; first reflexivity.
  (* Copn *)
  + move=> xs t o es ii lc hlc.
    apply (wequiv_opn_esem (sip:=sip)).
    move=> s0 t0 s1 /st_relP [-> /= heq] hsem.
    have [vm2 -> ?] :=
      esem_vm_eq (sip:=sip) (erefl (p_globs lp))
        (Hopn_esem hglob hsem hlc) heq.
    by eexists; first reflexivity.
  (* Csyscall *)
  + move=> xs o es ii lc [<-].
    by apply (wequiv_syscall_rel_eq (sip:=sip)) with checker_st_eq tt => //;
      exact: hck.
  (* Cassert *)
  + by move=> a ii lc [<-]; apply (wequiv_noassert (sip:=sip)) with (ev1:=ev) (ii:=ii).
  (* Cif *)
  + move=> e c1 c2 hc1 hc2 ii lc /=.
    t_xrbindP=> c1' hc1' c2' hc2' <-.
    apply (wequiv_if_rel_eq (sip:=sip)) with checker_st_eq tt tt tt => //.
    - exact: (hc1 _ hc1').
    - exact: (hc2 _ hc2').
  (* Cfor *)
  + move=> fi c hc ii lc /=.
    t_xrbindP=> c' hc' <-.
    case: fi => [x dir lo hi | e] /=.
    - apply (wequiv_for_rel_eq (sip:=sip)) with checker_st_eq tt tt => //.
      exact: (hc _ hc').
    - apply (wequiv_for_repeat_rel_eq (sip:=sip)) with checker_st_eq tt => //.
      exact: (hc _ hc').
  (* Cwhile *)
  + move=> a c e info c' hc hc' ii lc /=.
    t_xrbindP=> cc hcc cc' hcc' <-.
    apply (wequiv_while_rel_eq (sip:=sip)) with checker_st_eq tt => //.
    - exact: (hc _ hcc).
    - exact: (hc' _ hcc').
  (* Ccall *)
  move=> xs f es ii lc [<-].
  apply (wequiv_call_rel_eq (sip:=sip)) with checker_st_eq tt => //.
  by move=> ???; apply: (wequiv_fun_rec (spec := eq_spec)).
Qed.

End IT.

End PROOF.
