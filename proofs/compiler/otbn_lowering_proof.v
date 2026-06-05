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

Set Uniform Inductive Parameters.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

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
move=> /ok_inj /Some_inj [[<- <-] <-].
move: hrso; rewrite /reg_shift_of_sop2 /chk_xreg_ws /assert.
case: ifP => // /eqP -> hmatcho.
move: hmatcho => /= hmatcho.
case: op hmatcho hsem => //=.
- move=> ws0' hmatcho hsem.
  case: ws0' hmatcho hsem => //= hmatcho hsem.
  move: hmatcho => /ok_inj /Some_inj <-.
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
  move: hmatcho => /ok_inj /Some_inj <-.
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
  by move: htw; rewrite hshift => /ok_inj.
rewrite heq in hmatch.
move: hmatch; rewrite /semi_to_atype /= => /ok_inj <-.
by rewrite /with_mlz /=.
Qed.

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
       by move: hshift; rewrite hwy_eq => /ok_inj <-.
all: rewrite /semi_to_atype /= in hsemi.
1-6: (rewrite hwy_val; move/ok_inj: hsemi => hsemi; rewrite hsemi //).
(* BN_CMPB: vs' is abstract, extract vs'=[] from hsemi *)
case: vs' hsemi => [| ?? ] //= hsemi.
2: by case: (to_bool a) hsemi.
rewrite truncate_word_u /semi_to_atype /= /arch_utils.arch_mk_semi3_2_shifted /= hwy_val.
rewrite hsemi //.
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
       by move: hshift; rewrite hwy_eq => /ok_inj <-.
all: (rewrite hwy_val; move/ok_inj: hsemi => hsemi; rewrite hsemi //).
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
move=> z [x0 rest0] hrsnoc /ok_inj <- hget.
apply: rbindP hget => o hgas.
case: o hgas => [[[ebase sh0] esham] | ] hgas; last by [].
rewrite /issue cat0s => /ok_inj /Some_inj [<- <-].
move: hgas.
case: es hrsnoc hsrc => [| a bs] hrsnoc hsrc //=.
move/ok_inj: hrsnoc => [<- <-].
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
move=> z [[[x_e y_e] cf_e] rest] hrsnoc /ok_inj <- hget.
apply: rbindP hget => o hgas.
case: o hgas => [[[ebase sh0] esham] | ] hgas; last by [].
rewrite /issue => /ok_inj /Some_inj [<- <-].
move: hgas.
case: es hrsnoc hsrc => [| e1 [| e2 [| e3 es3]]] hrsnoc hsrc //=.
move/ok_inj: hrsnoc => [[[<- <-] <-] <-].
move=> hgas.
rewrite /sem_sopn in hsrc |- *.
move: hsrc; t_xrbindP => vs hvs r hexec hw.
move: hexec.
move: r; rewrite /sem_pexprs /=.
apply: rbindP => x_v hx.
apply: rbindP => ys_x hys_x.
move/ok_inj => <-.
move=> hexec.
move: hys_x.
apply: rbindP => y_v hy.
apply: rbindP => ys_y hys_y.
move/ok_inj => heq_x; subst ys_x.
move: hys_y.
apply: rbindP => cf_v hcf.
apply: rbindP => vrest hvrest.
move/ok_inj => heq_y; subst ys_y.
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
move=> z [[[x_e y_e] cf_e] rest] hrsnoc /ok_inj <- hget.
apply: rbindP hget => o hgas.
case: o hgas => [[[ebase sh0] esham] | ] hgas; last by [].
rewrite /issue => /ok_inj /Some_inj [<- <-].
move: hgas.
case: es hrsnoc hsrc => [| e1 [| e2 [| e3 es3]]] hrsnoc hsrc //=.
move/ok_inj: hrsnoc => [[[<- <-] <-] <-].
move=> hgas.
rewrite /sem_sopn in hsrc |- *.
move: hsrc; t_xrbindP => vs hvs r hexec hw.
move: hexec.
move: r; rewrite /sem_pexprs /=.
apply: rbindP => x_v hx.
apply: rbindP => ys_x hys_x.
move/ok_inj => <-.
move=> hexec.
move: hys_x.
apply: rbindP => y_v hy.
apply: rbindP => ys_y hys_y.
move/ok_inj => heq_x; subst ys_x.
move: hys_y.
apply: rbindP => cf_v hcf.
apply: rbindP => vrest hvrest.
move/ok_inj => heq_y; subst ys_y.
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
  (fg : otbn_options.bn_flag_group)
  (sh : otbn_options.bn_register_shift) : Prop :=
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
     move: hshift; t_xrbindP=> z [[x_e y_e] rest] hrsnoc /ok_inj <- hget;
     apply: rbindP hget => o hgas;
     case: o hgas => [[[ebase sh0] esham] | ] hgas; last by [];
     rewrite /issue => /ok_inj /Some_inj [<- <-];
     move: hgas;
     case: es hrsnoc => [| e1 [| e2 es2]] hrsnoc //=;
     move/ok_inj: hrsnoc => [<- <- <-];
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
  move/ok_inj => <-.
  move=> hexec.
  move: hys.
  apply: rbindP => y_v hy.
  apply: rbindP => vrest hvrest.
  move/ok_inj => heq; subst ys.
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
  have ? := ok_inj hcr; subst hlvs.
  move: hes0; rewrite /get_carry_pexprs /rsnoc3 /rsnoc2 /rsnoc /=.
  case: es => [//|e0 [//|e1 [//|ecf es_rest]]] /=.
  case: ecf => //= [b | g]; first case: b => //=.
  all: move=> /ok_inj /esym ?; subst es0.
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
    + move=> /ok_inj <- hres; rewrite -hres in hwrite2.
      move: hwrite2 => /=.
      t_xrbindP=> s_cf hcf s_r hr hlr.
      case: lvs_rest hlr => [/ok_inj <- | ? ? //].
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
    move=> /ok_inj <- hres; rewrite -hres in hwrite2.
    move: hwrite2 => /=.
    t_xrbindP=> s_cf hcf s_r hr hlr.
    case: lvs_rest hlr => [/ok_inj <- | ? ? //].
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
    move=> /ok_inj <- hres; rewrite -hres in hwrite2.
    move: hwrite2 => /=.
    t_xrbindP=> s_cf hcf s_r hr hlr.
    case: lvs_rest hlr => [/ok_inj <- | ? ? //].
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
    move=> /ok_inj <- hres; rewrite -hres in hwrite2.
    move: hwrite2 => /=.
    t_xrbindP=> s_cf hcf s_r hr hlr.
    case: lvs_rest hlr => [/ok_inj <- | ? ? //].
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
      exact: (@lower_carry_opP _ _ _ _ _ _ _ _ _ _ Ho hsrc).
    + move=> sz.
      t_xrbindP=> o Ho.
      case: o Ho => [[[a b] c]|] Ho //= [<- <- <-] hsrc.
      exact: (@lower_carry_opP _ _ _ _ _ _ _ _ _ _ Ho hsrc).
    + move=> ty.
      t_xrbindP=> o Ho.
      case: o Ho => [[[a b] c]|] Ho //= [<- <- <-] hsrc.
      exact: (@lower_swapP _ _ _ _ _ _ _ _ _ Ho hsrc).
  case: msb => [m|] //=.
  rewrite /lower_base_op.
  case: aop => //=.
  - by move=> mn [<- <- <-].
  move=> mn fg.
  t_xrbindP=> o Ho.
  case: o Ho => [[sh es'']|] Ho //= [<- <- <-] hsrc.
  exact: (@lower_basic_shiftP _ _ _ _ _ _ _ _ _ Ho hsrc).
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
  exact: (@lower_copnP _ _ _ _ _ _ _ _ _ hoargs hsem).
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
