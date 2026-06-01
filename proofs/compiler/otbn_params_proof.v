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
Proof. Admitted.

Lemma otbn_immediateP : immediate_correct (ap_sap otbn_params).(sap_immediate).
Proof. Admitted.

Lemma otbn_swapP : swap_correct (ap_sap otbn_params).(sap_swap).
Proof. Admitted.

End STACK_ALLOC.

Definition otbn_hsaparams :
  h_stack_alloc_params (ap_sap otbn_params) :=
  {|
    mov_ofsP := otbn_mov_ofsP;
    sap_immediateP := otbn_immediateP;
    sap_swapP := otbn_swapP;
  |}.

(* ------------------------------------------------------------------------ *)
(* Linearization hypotheses. *)

Section LINEARIZATION.

Lemma otbn_spec_lip_allocate_stack_frame :
  allocate_stack_frame_correct (ap_lip otbn_params).
Proof. Admitted.

Lemma otbn_spec_lip_free_stack_frame :
  free_stack_frame_correct (ap_lip otbn_params).
Proof. Admitted.

Lemma otbn_spec_lip_set_up_sp_register :
  set_up_sp_register_correct (ap_lip otbn_params).
Proof. Admitted.

Lemma otbn_lmove_correct : lmove_correct (ap_lip otbn_params).
Proof. Admitted.

Lemma otbn_lstore_correct : lstore_correct_aux (lip_check_ws (ap_lip otbn_params)) (lip_lstore (ap_lip otbn_params)).
Proof. Admitted.

Lemma otbn_lload_correct : lload_correct_aux (lip_check_ws (ap_lip otbn_params)) (lip_lload (ap_lip otbn_params)).
Proof. Admitted.

Lemma otbn_lstores_correct : lstores_correct (ap_lip otbn_params).
Proof. Admitted.

Lemma otbn_lloads_correct : lloads_correct (ap_lip otbn_params).
Proof. Admitted.

Lemma otbn_tmp_correct :
  lip_tmp (ap_lip otbn_params) <> lip_tmp2 (ap_lip otbn_params).
Proof. Admitted.

Lemma otbn_check_ws_correct : lip_check_ws (ap_lip otbn_params) Uptr.
Proof. Admitted.

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
Proof. Admitted.

Lemma otbn_ok_lip_tmp2 :
  exists r : reg_t, of_ident (lip_tmp2 (ap_lip otbn_params)) = Some r.
Proof. Admitted.

(* ------------------------------------------------------------------------ *)
(* Lowering hypotheses. *)

Definition otbn_hloparams : h_lowering_params (ap_lop otbn_params).
Proof. split=> *; [exact: lower_callP | exact: it_lower_callP]. Qed.

(* ------------------------------------------------------------------------ *)
(* Lowering of complex addressing mode (identity for OTBN). *)

Lemma otbn_hlaparams : h_lower_addressing_params (ap_lap otbn_params).
Proof.
  split=> /=.
  + exact: lower_addressing_prog_invariants.
  + exact: lower_addressing_fd_invariants.
  + exact: lower_addressing_progP.
  by move=> > /it_lower_addressing_progP.
Qed.

(* ------------------------------------------------------------------------ *)
(* Assembly generation hypotheses. *)

Section ASM_GEN.

Lemma otbn_eval_assemble_cond : assemble_cond_spec (ap_agp otbn_params).
Proof. Admitted.

Lemma otbn_assemble_extra_op : forall op, assemble_extra_correct (ap_agp otbn_params) op.
Proof. Admitted.

Lemma otbn_assemble_extra_sz :
  forall ii op lvs args ops,
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
(* Speculative execution. *)

Lemma otbn_hshp : slh_lowering_proof.h_sh_params (ap_shp otbn_params).
Proof. by constructor; move=> ???? []. Qed.

(* ------------------------------------------------------------------------ *)
(* Stack zeroization. *)

Lemma otbn_hszparams :
  stack_zeroization_proof.h_stack_zeroization_params (ap_szp otbn_params).
Proof. Admitted.

(* ------------------------------------------------------------------------ *)
(* Shared hypotheses. *)

Lemma otbn_is_move_opP op vx v :
  ap_is_move_op otbn_params op
  -> exec_sopn (Oasm op) [:: vx ] = ok v
  -> List.Forall2 value_uincl v [:: vx ].
Proof. Admitted.

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
