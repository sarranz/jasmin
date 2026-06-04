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
  pseudo_operator
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

(* ==================================================================== *)
(* Correctness of [lower_copn].  Each operation [lower_copn] may emit is
   handled by one auxiliary "case" lemma below, then assembled in
   [lower_copnP].  [RV32 mn] is emitted verbatim (identity, discharged
   inline in [lower_copnP]).  The other three transformations each get a
   case lemma plus the helper lemmas it relies on, with an implementation
   plan in a comment.  Every auxiliary/helper lemma is still [Admitted];
   [lower_copnP] (and hence [Hopn_esem]) is proved modulo them. *)

(* -------------------------------------------------------------------- *)
(* SHIFT ABSORPTION: [BN_basic mn fg] -> [BN_basic_shift mn fg sh].
   Model: ARM.  Mirror arm_lowering_proof.v: [get_arg_shiftP] (operand
   shift evaluation), [with_shift_unop]/[with_shift_binop]/
   [with_shift_terop] (shifted-instruction exec vs base exec on the
   shifted operand), and the [arg_shift] branch of [lower_Papp2P] /
   [lower_base_op].

   Call-site context (lower_copnP, BN_basic branch): the source op is
   [Oasm (BaseOp (None, BN_basic mn fg))]; [lower_basic_shift] returned
   [Some (sh, es'')], i.e. the operand it inspected had the form
   [base << sham] / [base >> sham]; [lvs] is unchanged.

   Key definitions (Print/Search them; no need to open other files):
   [get_arg_shift], [reg_shift_of_sop2] (Olsl (Op_w U256) -> RS_left,
   Olsr U256 -> RS_right), [word_shift_of_reg_shift] (RS_left -> wshl,
   RS_right -> wshr), [desc_bn_basic_shift_mnemonic] (built from the base
   desc via [arch_mk_semi1_shifted]/[arch_mk_semi2_2_shifted]/
   [arch_mk_semi3_2_shifted], which apply [word_shift_of_reg_shift] to one
   operand and append the U8 shift amount as the last input), [exec_sopn],
   [app_sopn]. *)

(* [get_arg_shiftP]: if [get_arg_shift] accepts [e] then [e] evaluates to
   the shifted base value.  Idea (cf. ARM [get_arg_shiftP]): [e] must be
   [Papp2 op (Pvar x) (Papp1 (Oword_of_int U8) (Pconst z))] with [op] a
   256-bit [Olsl]/[Olsr]; its typed [sem_sop2] computes exactly
   [word_shift_of_reg_shift sh base (wunsigned sham)].  Destruct [e] to
   that shape, read off [ebase = Pvar x] and [esham], and relate [sem_sop2]
   to [word_shift_of_reg_shift].  Check whether a [zero_extend] to
   xreg_size appears (ARM zero-extends the base; here it is already
   256-bit). *)
Lemma get_arg_shiftP ii ws e ebase sh esham s v :
  get_arg_shift ii ws e = ok (Some (ebase, sh, esham)) ->
  sem_pexpr true (p_globs p) s e = ok v ->
  exists (wb : word ws) (wa : word U8),
    [/\ sem_pexpr true (p_globs p) s ebase = ok (Vword wb)
      , sem_pexpr true (p_globs p) s esham = ok (Vword wa)
      & to_word ws v = ok (word_shift_of_reg_shift sh wb (wunsigned wa)) ].
Proof.
Admitted.

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
    [:: Vword wb, Vword wa & vs] = ok r.
Proof.
Admitted.

Lemma bn_shifted_binopP mn fg sh (wb : word arch_decl.xreg_size) (wa : word U8) x y vs r :
  mn \in [:: BN_ADD; BN_SUB; BN_AND; BN_OR; BN_XOR; BN_CMP; BN_CMPB ] ->
  to_word arch_decl.xreg_size y
  = ok (word_shift_of_reg_shift sh wb (wunsigned wa)) ->
  exec_sopn (Oasm (BaseOp (None, BN_basic mn fg))) [:: x, y & vs] = ok r ->
  exec_sopn (Oasm (BaseOp (None, BN_basic_shift mn fg sh)))
    [:: x, Vword wb, Vword wa & vs] = ok r.
Proof.
Admitted.

Lemma bn_shifted_teropP mn fg sh (wb : word arch_decl.xreg_size) (wa : word U8) x y cf vs r :
  mn \in [:: BN_ADDC; BN_SUBB ] ->
  to_word arch_decl.xreg_size y
  = ok (word_shift_of_reg_shift sh wb (wunsigned wa)) ->
  exec_sopn (Oasm (BaseOp (None, BN_basic mn fg))) [:: x, y, cf & vs] = ok r ->
  exec_sopn (Oasm (BaseOp (None, BN_basic_shift mn fg sh)))
    [:: x, Vword wb, cf, Vword wa & vs] = ok r.
Proof.
Admitted.

(* [lower_basic_shiftP] (case lemma assembling the above): from
   [lower_basic_shift ii mn es = Some (sh, es'')] conclude the
   [BN_basic_shift] sem_sopn on [es''] equals the [BN_basic] sem_sopn on
   [es].  Idea (cf. ARM [lower_Papp2P] arg_shift branch + [lower_base_op]):
   unfold [lower_basic_shift] (it cases [mn] into the three arity groups,
   splits off the inspected operand with [rsnoc]/[rsnoc2]/[rsnoc3], and
   reshuffles to [pre ++ ebase :: pos ++ [:: esham]]); apply [get_arg_shiftP]
   to that operand; dispatch to the matching [bn_shifted_*P].  Unfold
   [sem_sopn] on both sides ([sem_pexprs] of [es] vs [es''] then
   [exec_sopn]); [lvs] is identical, so the [write_lvals] step is shared
   once the exec results agree.  Output type is preserved (cf. ARM
   [sopn_tout_with_shift]). *)
Lemma lower_basic_shiftP ii mn fg lvs es sh es'' s0 s1 :
  lower_basic_shift ii mn es = ok (Some (sh, es'')) ->
  sem_sopn (p_globs p) (Oasm (BaseOp (None, BN_basic mn fg))) s0 lvs es = ok s1 ->
  sem_sopn (p_globs p) (Oasm (BaseOp (None, BN_basic_shift mn fg sh))) s0 lvs es''
  = ok s1.
Proof.
Admitted.

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
  let fw := if is_add then +%R else (fun a b : word arch_decl.xreg_size => a - b)%R in
  CF_of_Z (fZ (fZ (wunsigned x) (wunsigned y)) (Z.b2z c))
  = Some (if is_add then (waddcarry x y c).1 else (wsubcarry x y c).1)
  /\ fw (fw x y) (wrepr arch_decl.xreg_size (Z.b2z c))
     = (if is_add then (waddcarry x y c).2 else (wsubcarry x y c).2).
Proof.
Admitted.

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
Admitted.

(* -------------------------------------------------------------------- *)
(* SWAP: [Oswap (aword sz)] -> [ExtOp (SWAP sz)].  Model: RISC-V, which
   lowers swap to an extra op the same way; mirror the [Oswap] case of
   riscv_lowering_proof.v's [Hopn_esem] (via [lower_swap] -> [SWAP]).

   Call-site context (lower_copnP, swap branch): [ty = aword sz] with [sz]
   in {reg_size, xreg_size} (other sizes make [lower_swap] error, so the
   [ok (Some ..)] branch fixes this); [es] is unchanged.  For
   [sz = reg_size], [lvs' = lvs]; for [sz = xreg_size],
   [lvs' = lnone_mlz ++ lvs] (3 dummy flag lvals prepended).

   Key definitions: [lower_swap], [lnone_mlz] (= [nseq 3 lnoneb]),
   [li_xissue], otbn_extra [get_instr_desc] ([SWAP sz] -> [Oswap_instr
   (aword sz)] when [sz <= reg_size], else [desc_swap_large]),
   [desc_swap_large] (outputs 3 flags then the two swapped words),
   [Oswap_instr]/[swap_semi]. *)

(* [lower_swapP] (case lemma): the [SWAP] extra op reproduces [Oswap].
   Idea: case on [sz].  For [reg_size], otbn_extra's
   [get_instr_desc (SWAP sz)] is [Oswap_instr (aword sz)] (same as the
   source), with [lvs]/[es] unchanged, so [sem_sopn] coincides -- a near
   identity, exactly like RISC-V.  For [xreg_size], the op is
   [desc_swap_large], which emits 3 leading flags (M/L/Z) absorbed by the
   [lnone_mlz] dummies (write to [Lnone] is a no-op) followed by the two
   swapped words. *)
Lemma lower_swapP ii ty lvs es lvs' op' es' s0 s1 :
  lower_swap ii ty lvs es = ok (Some (lvs', op', es')) ->
  sem_sopn (p_globs p) (Opseudo_op (Oswap ty)) s0 lvs es = ok s1 ->
  sem_sopn (p_globs p) (Oasm op') s0 lvs' es' = ok s1.
Proof.
Admitted.

(* [lower_copnP]: assemble the case lemmas.  The dispatch leaves four real
   cases; three are discharged by the case lemmas above (shift absorption /
   carry / swap), and [RV32 mn] is verbatim. *)
Lemma lower_copnP ii lvs op es lvs' op' es' s0 s1 :
  lower_copn ii lvs op es = ok (Some (lvs', op', es')) ->
  sem_sopn (p_globs p) op s0 lvs es = ok s1 ->
  sem_sopn (p_globs p) (Oasm op') s0 lvs' es' = ok s1.
Proof.
  rewrite /lower_copn.
  case: op => [pop | slh | [ [msb aop] | eo ] ] //=.
  - rewrite /lower_pseudo_operator.
    case: pop => //=.
    + move=> sz.
      t_xrbindP=> o Ho.
      case: o Ho => [[[a b] c]|] Ho //= [<- <- <-] hsrc.
      exact: (lower_carry_opP Ho hsrc).
    + move=> sz.
      t_xrbindP=> o Ho.
      case: o Ho => [[[a b] c]|] Ho //= [<- <- <-] hsrc.
      exact: (lower_carry_opP Ho hsrc).
    + move=> ty.
      t_xrbindP=> o Ho.
      case: o Ho => [[[a b] c]|] Ho //= [<- <- <-] hsrc.
      exact: (lower_swapP Ho hsrc).
  case: msb => [m|] //=.
  rewrite /lower_base_op.
  case: aop => //=.
  - by move=> mn [<- <- <-].
  move=> mn fg.
  t_xrbindP=> o Ho.
  case: o Ho => [[sh es'']|] Ho //= [<- <- <-] hsrc.
  exact: (lower_basic_shiftP Ho hsrc).
Qed.

Lemma Hopn_esem (p' : prog) (hglob : p_globs p' = p_globs p)
  {ii lvs tag op es s0 s1 lc} :
  sem_sopn (p_globs p) op s0 lvs es = ok s1 ->
  lower_i (MkI ii (Copn lvs tag op es)) = ok lc ->
  esem p' ev lc s0 = ok s1.
Proof.
  move=> hsem /=.
  t_xrbindP=> oargs hoargs <-.
  rewrite esem1.
  case: oargs hoargs => [[[lvs' op'] es']|] hoargs /=; rewrite hglob;
    last exact: hsem.
  exact: (lower_copnP hoargs hsem).
Qed.

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
