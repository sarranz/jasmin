From mathcomp Require Import ssreflect ssrfun ssrbool eqtype order seq ssralg.
Import Order.POrderTheory Order.TotalTheory.
From mathcomp Require Import word_ssrZ.

Require Import compiler_util expr psem.

Section LOWERING.

Definition fresh_vars : Type := string -> atype -> Ident.ident.

Context
  {asm_op : Type}
  {asmop : asmOp asm_op}
  (lower_i0 :
      (instr_info -> warning_msg -> instr_info)
    -> fresh_vars
    -> instr
    -> cexec cmd)
  (warning : instr_info -> warning_msg -> instr_info)
  (fv : fresh_vars)
  {pT : progT}
  (all_fresh_vars : seq Ident.ident)
  (fvars : Sv.t).

Definition disj_fvars (x : Sv.t) : bool := disjoint x fvars.

Definition fvars_correct (fds : fun_decls) : bool :=
  disj_fvars (vars_p fds) && uniq all_fresh_vars.

Definition is_lval_in_memory (x : lval) : bool :=
  match x with
  | Lnone _ _ => false
  | Lvar v => is_var_in_memory v
  | Laset _ _ _ v _ => is_var_in_memory v
  | Lasub _ _ _ v _ => is_var_in_memory v
  | Lmem _ _ _ _ => true
  end.

Notation lower_i :=
  (lower_i0 warning fv).

Definition lower_cmd (c : cmd) : cexec cmd :=
  conc_mapM lower_i c.

Definition lower_fd (fd : fundef) : cexec fundef :=
  Let body := lower_cmd (f_body fd) in
  ok (with_body fd body).

Definition lower_prog (p : prog) : cexec prog :=
  Let funcs := map_cfprog lower_fd (p_funcs p) in
  ok {| p_funcs := funcs; p_globs := p_globs p; p_extra := p_extra p |}.

(* When [lower_i0] never fails, the generic pass is the obvious total map.
   This bridges the architectures whose lowering always succeeds with their
   existing (total) correctness proofs. *)

Lemma lower_cmd_ext (gi : instr -> cmd) (c : cmd) :
  (forall i, lower_i i = ok (gi i)) ->
  lower_cmd c = ok (conc_map gi c).
Proof.
  move=> h; rewrite /lower_cmd /conc_mapM /conc_map.
  have -> : mapM lower_i c = ok (map gi c); last by [].
  by elim: c => //= i c' ih; rewrite h /= ih.
Qed.

Lemma lower_fd_ext (gi : instr -> cmd) (fd : fundef) :
  (forall i, lower_i i = ok (gi i)) ->
  lower_fd fd = ok (with_body fd (conc_map gi (f_body fd))).
Proof. by move=> h; rewrite /lower_fd (lower_cmd_ext _ h). Qed.

Lemma lower_prog_ext (gi : instr -> cmd) (p : prog) :
  (forall i, lower_i i = ok (gi i)) ->
  lower_prog p
  = ok (map_prog (fun fd => with_body fd (conc_map gi (f_body fd))) p).
Proof.
  move=> h; rewrite /lower_prog /map_prog /map_prog_name.
  have -> :
    map_cfprog lower_fd (p_funcs p)
    = ok (map (fun f => (f.1, with_body f.2 (conc_map gi (f_body f.2))))
              (p_funcs p)); last by [].
  rewrite /map_cfprog /map_cfprog_gen /map_cfprog_name_gen.
  by elim: (p_funcs p) => //= -[fn fd] fs ih; rewrite (lower_fd_ext _ h) /= ih.
Qed.

End LOWERING.

(* -------------------------------------------------------------------- *)
(* Generic semantic helpers used by architecture lowering proofs.        *)

Section LOWERING_SEM.

Context
  {wsw : WithSubWord}
  {asm_op : Type}
  {asmop : asmOp asm_op}
  {syscall_state : Type}
  {ep : EstateParams syscall_state}
  {spp : SemPexprParams}
  {gd : glob_decls}.

Lemma to_word_m sz sz' (a : value) (w : word sz) :
  to_word sz a = ok w ->
  (sz' <= sz)%CMP ->
  to_word sz' a = ok (zero_extend sz' w).
Proof.
  case/to_wordI' => n [] m [] sz_le_n ->{a} ->{w} /= sz'_le_sz.
  by rewrite truncate_word_le ?zero_extend_idem //
             (cmp_le_trans sz'_le_sz sz_le_n).
Qed.

Lemma Hassgn_op2_generic s e1 e2 v1 v2 op2 v ws v' lv s1 (op2' : sopn) :
  sem_pexpr true gd s e1 = ok v1 ->
  sem_pexpr true gd s e2 = ok v2 ->
  sem_sop2 op2 v1 v2 = ok v ->
  truncate_val (cword ws) v = ok v' ->
  write_lval true gd lv v' s = ok s1 ->
  i_valid (sopn.get_instr_desc op2') ->
  forall ws1 ws2 ws3 ws1' ws2'
    (eq1 : type_of_op2 op2 = (aword ws1, aword ws2, aword ws3))
    (eq2 : tin (sopn.get_instr_desc op2') = [::aword ws1'; aword ws2'])
    (eq3 : tout (sopn.get_instr_desc op2') = [:: aword ws]),
  (ws <= ws3)%CMP
  /\ exists w1 w2, [/\
      to_word ws1 v1 = ok w1,
      to_word ws2 v2 = ok w2 &
      forall e1' e2' w1' w2'
        (hcmp1 : (ws1' <= ws1)%CMP)
        (hcmp2 : (ws2' <= ws2)%CMP),
        sem_pexpr true gd s e1' >>= to_word ws1 = ok w1' ->
        sem_pexpr true gd s e2' >>= to_word ws2 = ok w2' ->
        Let w := ecast t (let t := t in _) eq1 (sem_sop2_typed op2) w1 w2 in
        ok (zero_extend ws w)
        = ecast l (sem_prod (map eval_atype l) _) eq2
            (ecast l (sem_prod _ (exec (sem_tuple (map eval_atype l)))) eq3
              (semi (sopn.get_instr_desc op2')))
            (zero_extend ws1' w1') (zero_extend ws2' w2') ->
        sem_sopn gd op2' s [::lv] [:: e1'; e2'] = ok s1].
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
  rewrite ok_v1' ok_v2' /= (to_word_m ok_w1' hcmp1) (to_word_m ok_w2' hcmp2) /=.
  by rewrite -eq_sem ok_w /= hwrite.
Qed.

Lemma Hassgn_op2 s e1 e2 v1 v2 op2 v v' lv s1 (op2' : sopn) :
  sem_pexpr true gd s e1 = ok v1 ->
  sem_pexpr true gd s e2 = ok v2 ->
  sem_sop2 op2 v1 v2 = ok v ->
  truncate_val (cword U32) v = ok v' ->
  write_lval true gd lv v' s = ok s1 ->
  i_valid (sopn.get_instr_desc op2') ->
  forall ws
    (eq1 : type_of_op2 op2 = (aword ws, aword ws, aword ws))
    (eq2 : tin (sopn.get_instr_desc op2') = [::aword U32; aword U32])
    (eq3 : tout (sopn.get_instr_desc op2') = [:: aword U32]),
  (U32 <= ws)%CMP
  /\ exists w1 w2, [/\
      to_word ws v1 = ok w1,
      to_word ws v2 = ok w2 &
      Let w := ecast t (let t := t in _) eq1 (sem_sop2_typed op2) w1 w2 in
      ok (zero_extend U32 w)
      = ecast l (sem_prod (map eval_atype l) _) eq2
          (ecast l (sem_prod _ (exec (sem_tuple (map eval_atype l)))) eq3
            (semi (sopn.get_instr_desc op2')))
          (zero_extend U32 w1) (zero_extend U32 w2) ->
      sem_sopn gd op2' s [::lv] [:: e1; e2] = ok s1].
Proof.
  move=> ok_v1 ok_v2 ok_v htrunc hwrite hvalid ws eq1 eq2 eq3.
  have [hcmp [w1 [w2 [ok_w1 ok_w2 sem_correct]]]] :=
    Hassgn_op2_generic ok_v1 ok_v2 ok_v htrunc hwrite hvalid eq1 eq2 eq3.
  split=> //.
  exists w1, w2; split=> //.
  apply sem_correct=> //.
  + by rewrite ok_v1.
  by rewrite ok_v2.
Qed.

Lemma Hassgn_op2_shift s e1 e2 v1 v2 op2 v v' lv s1 (op2' : sopn) :
  sem_pexpr true gd s e1 = ok v1 ->
  sem_pexpr true gd s e2 = ok v2 ->
  sem_sop2 op2 v1 v2 = ok v ->
  truncate_val (cword U32) v = ok v' ->
  write_lval true gd lv v' s = ok s1 ->
  i_valid (sopn.get_instr_desc op2') ->
  forall ws
    (eq1 : type_of_op2 op2 = (aword ws, aword U8, aword ws))
    (eq2 : tin (sopn.get_instr_desc op2') = [::aword U32; aword U8])
    (eq3 : tout (sopn.get_instr_desc op2') = [:: aword U32]),
  (U32 <= ws)%CMP
  /\ exists w1 w2, [/\
      to_word ws v1 = ok w1,
      to_word U8 v2 = ok w2 &
      forall e2' w2',
        sem_pexpr true gd s e2' >>= to_word U8 = ok w2' ->
        Let w := ecast t (let t := t in _) eq1 (sem_sop2_typed op2) w1 w2 in
        ok (zero_extend U32 w)
        = ecast l (sem_prod (map eval_atype l) _) eq2
            (ecast l (sem_prod _ (exec (sem_tuple (map eval_atype l)))) eq3
              (semi (sopn.get_instr_desc op2')))
            (zero_extend U32 w1) w2' ->
        sem_sopn gd op2' s [::lv] [:: e1; e2'] = ok s1].
Proof.
  move=> ok_v1 ok_v2 ok_v htrunc hwrite hvalid ws eq1 eq2 eq3.
  have [hcmp [w1 [w2 [ok_w1 ok_w2 sem_correct]]]] :=
    Hassgn_op2_generic ok_v1 ok_v2 ok_v htrunc hwrite hvalid eq1 eq2 eq3.
  split=> //.
  exists w1, w2; split=> //.
  move=> e2' w2' ok_w2'; rewrite -(zero_extend_u w2').
  apply sem_correct=> //.
  by rewrite ok_v1.
Qed.

End LOWERING_SEM.

Section LOWERING_SEM_ID.

Context
  {wsw : WithSubWord}
  {asm_op syscall_state : Type}
  {ep : EstateParams syscall_state}
  {spp : SemPexprParams}
  {sip : SemInstrParams asm_op syscall_state}
  {pT : progT}
  {sCP : semCallParams}
  (p : prog)
  (ev : extra_val_t).

Lemma Hassgn_id (p' : prog) (hglob : p_globs p' = p_globs p)
  {ii lv tag ty e s0 s1} :
  sem_assgn p lv tag ty e s0 = ok s1 ->
  esem p' ev [:: MkI ii (Cassgn lv tag ty e) ] s0 = ok s1.
Proof. by move=> hsem; rewrite esem1 /= /sem_assgn hglob; exact: hsem. Qed.

End LOWERING_SEM_ID.
