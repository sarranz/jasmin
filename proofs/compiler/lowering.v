From mathcomp Require Import ssreflect ssrfun ssrbool eqtype seq.
Require Import compiler_util expr.

Section LOWERING.

Definition fresh_vars : Type := string -> atype -> Ident.ident.

Context
  {asm_op lowering_options : Type}
  {asmop : asmOp asm_op}
  (lower_i0 :
    lowering_options
    -> (instr_info -> warning_msg -> instr_info)
    -> fresh_vars
    -> instr
    -> cexec cmd)
  (options : lowering_options)
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
  (lower_i0 options warning fv).

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
