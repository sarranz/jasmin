From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssralg.
From mathcomp Require Import word_ssrZ.
From Coq Require Import ZArith.

Require Import expr sem_op_typed compiler_util lea.

Import Utf8.
Import oseq.

Require Import
  arch_decl
  arch_extra
  otbn_instr_decl
  otbn_decl
  otbn
  otbn_extra.

Local Open Scope seq_scope.
Local Open Scope Z_scope.

Module E.

Definition pass_name := "lower_addressing"%string.

Definition error msg := {|
    pel_msg := pp_s msg;
    pel_fn := None;
    pel_fi := None;
    pel_ii := None;
    pel_vi := None;
    pel_pass := Some pass_name;
    pel_internal := true
  |}.

End E.

Section Section.

Context {atoI: arch_toIdent}.

Section TMP.

Context (rip tmp : var_i).

Definition is_one_Pload (es : pexprs) : option (aligned * wsize * pexpr) :=
  if es is [:: Pload al ws e] then Some (al, ws, e) else None.

(* On OTBN the assembler does not accept a global (RIP-relative) operand for a
   load, i.e. [lw rd, glob_data+disp].  A direct (scalar) access to a global
   has the form [rip + disp] (a [lea] with base [rip] and no scaled offset). *)
Definition compute_glob_addr (e : pexpr) : option (seq instr_r * pexpr) :=
  let%opt lea := mk_lea Uptr e in
  let%opt base := lea.(lea_base) in
  let%opt _ :=
    oassert [&& rip.(v_var) == base.(v_var) & ~~ isSome lea.(lea_offset) ]
  in
  Some ([:: Copn [:: Lvar tmp] AT_none (Ootbn (RV32 LA)) [:: e] ], Plvar tmp).

Fixpoint lower_addressing_i (i : instr) :=
  let (ii,ir) := i in
  match ir with
  | Copn xs t o es =>
    if is_one_Pload es is Some (al, ws, e) then
      if compute_glob_addr e is Some (prelude, p) then
        [seq MkI ii i | i <- prelude ++ [:: Copn xs t o [:: Pload al ws p]] ]
      else [:: i]
    else [:: i]
  | Cassgn _ _ _ _
  | Csyscall _ _ _
  | Cassert _
  | Ccall _ _ _ => [:: i]
  | Cif b c1 c2 =>
    let c1 := conc_map lower_addressing_i c1 in
    let c2 := conc_map lower_addressing_i c2 in
    [:: MkI ii (Cif b c1 c2)]
  | Cfor fi c =>
    let c := conc_map lower_addressing_i c in
    [:: MkI ii (Cfor fi c) ]
  | Cwhile a c e ii' c' =>
    let c := conc_map lower_addressing_i c in
    let c' := conc_map lower_addressing_i c' in
    [:: MkI ii (Cwhile a c e ii' c')]
  end.

Definition lower_addressing_c := conc_map lower_addressing_i.

Definition lower_addressing_fd (fd : sfundef) :=
  let body := fd.(f_body) in
  Let _ :=
    assert
      (~~ Sv.mem tmp (read_c body))
      (E.error "fresh variable not fresh (body)")
  in
  Let _ :=
    assert
      (~~ Sv.mem tmp (vars_l fd.(f_res)))
      (E.error "fresh variable not fresh (res)")
  in
  ok (with_body fd (lower_addressing_c body)).

End TMP.

Definition lower_addressing_prog
  (fresh_reg : string -> atype -> Ident.ident) (p : sprog) : cexec sprog :=
  let rip := vid p.(p_extra).(sp_rip) in
  let tmp :=
    {| vtype := aword Uptr; vname := fresh_reg "__tmp__"%string (aword Uptr); |}
  in
  let tmpi := mk_var_i tmp in
  Let funcs := map_cfprog (lower_addressing_fd rip tmpi) p.(p_funcs) in
  ok {| p_extra := p_extra p; p_globs := p_globs p; p_funcs := funcs |}.

End Section.
