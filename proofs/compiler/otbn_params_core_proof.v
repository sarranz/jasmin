From Coq Require Import Lia.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype ssralg.
From mathcomp Require Import word_ssrZ.

Require Import
  arch_params
  compiler_util
  expr
  fexpr
  fexpr_sem
  linear
  linear_sem
  linear_facts
  psem.
Require Import
  arch_decl
  arch_extra
  arch_sem.

Require Import
  otbn_decl
  otbn_instr_decl
  otbn_extra
  otbn
  otbn_params_core.

Set SsrOldRewriteGoalsOrder.  (* change Set to Unset when porting the file, then remove the line when requiring MathComp >= 2.6 *)

Module OTBNFopn_coreP.

Section Section.

Context
  {syscall_state : Type}
  {ep : EstateParams syscall_state}
  {atoI : arch_toIdent}.

#[local] Existing Instance withsubword.

Definition sem_fopn_args (p : seq lexpr * otbn_op * seq rexpr) (s : estate) :=
  let: (xs,o,es) := p in
  Let args := sem_rexprs s es in
  let op := instr_desc_op o in
  Let _ := assert (id_valid op) ErrType in
  Let t := app_sopn (map eval_ltype (id_tin op)) (id_semi op) args in
  let res := list_ltuple t in
  write_lexprs xs res s.

Definition sem_fopns_args := foldM sem_fopn_args.

Ltac t_otbn_op :=
  rewrite /sem_fopn_args /get_gvar /=;
  t_simpl_rewrites;
  rewrite /= /with_vm /=;
  repeat rewrite truncate_word_u /=;
  rewrite ?zero_extend_u ?addn1 ?sign_extend_u;
  t_simpl_rewrites.

(* [R[x] := R[y] + R[z]]. *)
Lemma add_sem_fopn_args {s} {xi:var_i} {y} {wy : word Uptr} {z} {wz : word Uptr} :
  convertible xi.(vtype) (aword otbn_reg_size) ->
  get_var true (evm s) (v_var y) >>= to_word Uptr = ok wy ->
  get_var true (evm s) (v_var z) >>= to_word Uptr = ok wz ->
  let: wx' := Vword (s:=reg_size) ((wy + wz : word reg_size)) in
  let: vm' := (evm s).[xi <- wx'] in
  sem_fopn_args (OTBNFopn_core.add xi y z) s = ok (with_vm s vm').
Proof.
  move=> hc.
  rewrite /=; t_xrbindP => *; t_otbn_op.
  by rewrite /= set_var_truncate // (convertible_eval_atype hc).
Qed.

(* [R[x] := R[y] + imm % 2^32]. *)
Lemma addi_sem_fopn_args {s} {xi:var_i} {y imm wy} :
  convertible xi.(vtype) (aword otbn_reg_size) ->
  get_var true (evm s) (v_var y) >>= to_word Uptr = ok wy ->
  let: wx' := Vword (s:=reg_size) ((wy + wrepr reg_size imm : word reg_size)) in
  let: vm' := (evm s).[xi <- wx'] in
  sem_fopn_args (OTBNFopn_core.addi xi y imm) s = ok (with_vm s vm').
Proof.
  move=> hc.
  rewrite /=; t_xrbindP => *; t_otbn_op.
  by rewrite /= set_var_truncate // (convertible_eval_atype hc).
Qed.

(* [R[x] := R[y] - R[z]]. *)
Lemma sub_sem_fopn_args {s} {xi:var_i} {y} {wy : word Uptr} {z} {wz : word Uptr} :
  convertible xi.(vtype) (aword otbn_reg_size) ->
  get_var true (evm s) (v_var y) >>= to_word Uptr = ok wy ->
  get_var true (evm s) (v_var z) >>= to_word Uptr = ok wz ->
  let: wx' := Vword (s:=reg_size) ((wy - wz : word reg_size)) in
  let: vm' := (evm s).[xi <- wx'] in
  sem_fopn_args (OTBNFopn_core.sub xi y z) s = ok (with_vm s vm').
Proof.
  move=> hc.
  rewrite /=; t_xrbindP => *; t_otbn_op.
  by rewrite /= set_var_truncate // (convertible_eval_atype hc).
Qed.

(* [R[x] := R[y] - imm % 2^32]. *)
Lemma subi_sem_fopn_args {s} {xi:var_i} {y imm wy} :
  convertible xi.(vtype) (aword otbn_reg_size) ->
  get_var true (evm s) (v_var y) >>= to_word Uptr = ok wy ->
  let: wx' := Vword (s:=reg_size) ((wy - wrepr reg_size imm : word reg_size)) in
  let: vm' := (evm s).[xi <- wx'] in
  sem_fopn_args (OTBNFopn_core.subi xi y imm) s = ok (with_vm s vm').
Proof.
  move=> hc.
  rewrite /=; t_xrbindP => *; t_otbn_op.
  rewrite wrepr_opp.
  by rewrite /= set_var_truncate // (convertible_eval_atype hc).
Qed.

(* [R[x] := R[y]] (implemented as [addi x y 0]). *)
Lemma mov_sem_fopn_args {s} {xi:var_i} {y} {wy : word Uptr} :
  convertible xi.(vtype) (aword otbn_reg_size) ->
  get_var true (evm s) (v_var y) >>= to_word Uptr = ok wy ->
  let: vm' := (evm s).[xi <- Vword wy] in
  sem_fopn_args (OTBNFopn_core.mov xi y) s = ok (with_vm s vm').
Proof.
  move=> hc.
  rewrite /=; t_xrbindP => *; t_otbn_op.
  (* mov = addi x y 0; need wadd wy (wrepr 0) = wy *)
  by rewrite /= /wadd wrepr0 GRing.addr0
       set_var_truncate // (convertible_eval_atype hc).
Qed.

(* [R[x] := R[y] ^ imm % 2^32]. *)
Lemma xori_sem_fopn_args {s} {xi:var_i} {y imm wy} :
  convertible xi.(vtype) (aword otbn_reg_size) ->
  get_var true (evm s) (v_var y) >>= to_word Uptr = ok wy ->
  let: wx' := Vword (s:=reg_size) (wxor wy (wrepr reg_size imm)) in
  let: vm' := (evm s).[xi <- wx'] in
  sem_fopn_args (OTBNFopn_core.xori xi y imm) s = ok (with_vm s vm').
Proof.
  move=> hc.
  rewrite /=; t_xrbindP => *; t_otbn_op.
  by rewrite /= set_var_truncate // (convertible_eval_atype hc).
Qed.

(* [R[x] := ~ R[y]] (implemented as [XORI x, y, -1]). *)
Lemma not_sem_fopn_args {s} {xi:var_i} {y} {wy : word Uptr} :
  convertible xi.(vtype) (aword otbn_reg_size) ->
  get_var true (evm s) (v_var y) >>= to_word Uptr = ok wy ->
  let: vm' := (evm s).[xi <- Vword (wnot wy)] in
  sem_fopn_args (OTBNFopn_core.not xi y) s = ok (with_vm s vm').
Proof.
  move=> hc hgety.
  have -> : wnot wy = wxor wy (wrepr reg_size (-1)) by rewrite /wnot wrepr_m1.
  exact: xori_sem_fopn_args hc hgety.
Qed.

(* [R[x] := imm] (loaded with the single [LI] instruction). *)
Lemma movi_sem_fopn_args {s imm} {xi:var_i} :
  convertible xi.(vtype) (aword otbn_reg_size) ->
  let: vm' := (evm s).[xi <- Vword (wrepr U32 imm)] in
  sem_fopn_args (OTBNFopn_core.li xi imm) s = ok (with_vm s vm').
Proof.
  move=> hc.
  t_otbn_op.
  by rewrite set_var_truncate // (convertible_eval_atype hc).
Qed.

Opaque OTBNFopn_core.add.
Opaque OTBNFopn_core.addi.
Opaque OTBNFopn_core.mov.
Opaque OTBNFopn_core.li.
Opaque OTBNFopn_core.sub.
Opaque OTBNFopn_core.subi.
Opaque OTBNFopn_core.xori.
Opaque OTBNFopn_core.not.

(* NOTE: The RISC-V proof file additionally contains the word-arithmetic helper
   lemmas [wbit_n_add], [mov_movt_aux], [mov_movt_aux1] and [mov_movt].  These
   justify assembling a 32-bit immediate from two 16-bit halves (the LUI+ADDI
   expansion used to load a constant on RISC-V).  OTBN loads a full 32-bit
   immediate with the single [LI] instruction, so there is no [otbn_params_core]
   definition matching these helpers and hence no OTBN analogue. *)

Lemma smart_mov_sem_fopns_args s (w : wreg) (xi:var_i) y :
  convertible xi.(vtype) (aword otbn_reg_size) ->
  let: lc := OTBNFopn_core.smart_mov xi y in
  get_var true (evm s) y >>= to_word Uptr = ok w ->
  exists vm,
    [/\ sem_fopns_args s lc = ok (with_vm s vm)
      , vm =[\ Sv.singleton xi ] evm s
      & get_var true vm xi >>= to_word Uptr = ok w ].
Proof.
  move=> hc hgety.
  rewrite /OTBNFopn_core.smart_mov /=.
  case: eqP => heq /=.
  - case : y heq hgety=> y yi /= *; subst y.
    rewrite -{1}(with_vm_same s); eexists; split; eauto.
  rewrite (mov_sem_fopn_args hc hgety) /=.
  eexists; split; first reflexivity.
  + by move=> z /Sv.singleton_spec hz; t_vm_get.
  by rewrite /get_var Vm.setP_eq /= (convertible_eval_atype hc) /= truncate_word_u.
Qed.

(* Unlike RISC-V's [gen_smart_opi], the OTBN combinator returns
   [option (seq opn_args)]: it yields [Some lc] exactly when emitting [lc] is
   safe (the immediate is neutral or small, or the source [y] differs from the
   scratch register [tmp]).  This is the analogue of RISC-V's
   [gen_smart_opi_sem_fopn_args]; the RISC-V precondition
   [is_small imm \/ v_var tmp <> v_var y] is replaced by the hypothesis that
   [gen_smart_opi] succeeds with output [lc]. *)
Lemma gen_smart_opi_sem_fopn_args
  (op : word reg_size -> word reg_size -> word reg_size)
  (on_reg : var_i -> var_i -> var_i -> OTBNFopn_core.opn_args)
  (on_imm : var_i -> var_i -> Z -> OTBNFopn_core.opn_args)
  (is_small : Z -> bool)
  (neutral : option Z)
  (op_sem_fopn_args :
    forall {s} {xi:var_i} {y} {wy : word Uptr} {z} {wz : word Uptr},
      convertible xi.(vtype) (aword otbn_reg_size) ->
      get_var true (evm s) (v_var y) >>= to_word Uptr = ok wy
      -> get_var true (evm s) (v_var z) >>= to_word Uptr = ok wz
      -> let: wx' := Vword (op wy wz) in
      let: vm' := (evm s).[xi <- wx'] in
      sem_fopn_args (on_reg xi y z) s = ok (with_vm s vm'))
  (opi_sem_fopn_args :
    forall {s} {xi:var_i} {y imm wy},
      convertible xi.(vtype) (aword otbn_reg_size) ->
      get_var true (evm s) (v_var y) >>= to_word Uptr = ok wy
      -> let: wx' := Vword (op wy (wrepr reg_size imm)) in
     let: vm' := (evm s).[xi <- wx'] in
     sem_fopn_args (on_imm xi y imm) s = ok (with_vm s vm'))
  (neutral_ok : if neutral is Some z then forall w, op w (wrepr _ z) = w else true)
  (tmp : var_i) (xi : var_i) y imm s (w : wreg) lc :
  convertible (vtype tmp) (aword Uptr) ->
  convertible xi.(vtype) (aword otbn_reg_size) ->
  OTBNFopn_core.gen_smart_opi on_reg on_imm is_small neutral tmp xi y imm = Some lc ->
  get_var true (evm s) (v_var y) >>= to_word Uptr = ok w ->
  exists vm',
    [/\ sem_fopns_args s lc = ok (with_vm s vm')
      , vm' =[\ Sv.add xi (Sv.singleton tmp) ] evm s
      & get_var true vm' xi = ok (Vword (op w (wrepr reg_size imm))) ].
Proof.
  move=> hc1 hc2 hlc hgety.
  rewrite /OTBNFopn_core.gen_smart_opi /OTBNFopn_core.gen_unsafe_smart_opi in hlc.
  case hmov : (OTBNFopn_core.is_mov neutral imm).
  - move: hlc; rewrite hmov /= => [[<-]].
    have hop : op w (wrepr reg_size imm) = w.
    { move: neutral_ok; case: neutral hmov => [n |] //= /ZeqbP ->; exact. }
    have [vm [-> hvm hgetx]] := smart_mov_sem_fopns_args hc2 hgety.
    eexists; split; first reflexivity.
    + by apply: eq_exI hvm; clear; SvD.fsetdec.
    rewrite hop; by apply get_var_to_word.
  - move: hlc; rewrite hmov /=.
    case hsmall : (is_small imm) => /=.
    + move=> [<-].
      rewrite /sem_fopns_args /= (opi_sem_fopn_args _ _ _ _ _ hc2 hgety) /=.
      eexists; split; first reflexivity;
        last by t_get_var; rewrite (convertible_eval_atype hc2).
      by move=> z hin; rewrite Vm.setP_neq //; apply/eqP; clear -hin; SvD.fsetdec.
    case hyne : (v_var y != v_var tmp) => /=.
    + move=> [<-].
      rewrite /sem_fopns_args /= movi_sem_fopn_args //=.
      have hne : v_var tmp <> v_var y
        by move: hyne => /negPf; rewrite eq_sym => /eqP.
      rewrite -(@get_var_neq _ _ tmp _ _ (Vword (wrepr U32 imm))) // in hgety.
      rewrite
        (op_sem_fopn_args (with_vm _ _) _ _ _ _ (wrepr reg_size imm) hc2 hgety)
        /with_vm /=;
        last by rewrite get_var_eq /= (convertible_eval_atype hc1) //= truncate_word_u.
      eexists; split; first reflexivity;
        last by t_get_var; rewrite (convertible_eval_atype hc2).
      move=> z hin.
      rewrite Vm.setP_neq; last by apply/eqP; SvD.fsetdec.
      by rewrite Vm.setP_neq; last by apply/eqP; SvD.fsetdec.
    + by [].
Qed.

End Section.

End OTBNFopn_coreP.
