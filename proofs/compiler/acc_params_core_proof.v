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
  arch_sem
  sem_params_of_arch_extra.

Require Import
  acc_decl
  acc_instr_decl
  acc_extra
  acc
  acc_params_core.

Set SsrOldRewriteGoalsOrder.  (* change Set to Unset when porting the file, then remove the line when requiring MathComp >= 2.6 *)

Module ACCFopn_coreP.

Section Section.

Context
  {syscall_state : Type}
  {ep : EstateParams syscall_state}
  {atoI : arch_toIdent}.

#[local] Existing Instance withsubword.

Definition sem_fopn_args (p : seq lexpr * acc_op * seq rexpr) (s : estate) :=
  let: (xs,o,es) := p in
  Let args := sem_rexprs s es in
  let op := instr_desc_op o in
  Let _ := assert (id_valid op) ErrType in
  Let t := app_sopn (map eval_ltype (id_tin op)) (id_semi op) args in
  let res := list_ltuple t in
  write_lexprs xs res s.

Definition sem_fopns_args := foldM sem_fopn_args.

Ltac t_acc_op :=
  rewrite /sem_fopn_args /get_gvar /=;
  t_simpl_rewrites;
  rewrite /= /with_vm /=;
  repeat rewrite truncate_word_u /=;
  rewrite ?zero_extend_u ?addn1 ?sign_extend_u;
  t_simpl_rewrites.

(* [R[x] := R[y] + R[z]]. *)
Lemma add_sem_fopn_args {s} {xi:var_i} {y} {wy : word Uptr} {z} {wz : word Uptr} :
  convertible xi.(vtype) (aword acc_reg_size) ->
  get_var true (evm s) (v_var y) >>= to_word Uptr = ok wy ->
  get_var true (evm s) (v_var z) >>= to_word Uptr = ok wz ->
  let: wx' := Vword (s:=reg_size) ((wy + wz : word reg_size)) in
  let: vm' := (evm s).[xi <- wx'] in
  sem_fopn_args (ACCFopn_core.add xi y z) s = ok (with_vm s vm').
Proof.
  move=> hc.
  rewrite /=; t_xrbindP => *; t_acc_op.
  by rewrite /= set_var_truncate // (convertible_eval_atype hc).
Qed.

(* [R[x] := R[y] + imm % 2^32]. *)
Lemma addi_sem_fopn_args {s} {xi:var_i} {y imm wy} :
  convertible xi.(vtype) (aword acc_reg_size) ->
  get_var true (evm s) (v_var y) >>= to_word Uptr = ok wy ->
  let: wx' := Vword (s:=reg_size) ((wy + wrepr reg_size imm : word reg_size)) in
  let: vm' := (evm s).[xi <- wx'] in
  sem_fopn_args (ACCFopn_core.addi xi y imm) s = ok (with_vm s vm').
Proof.
  move=> hc.
  rewrite /=; t_xrbindP => *; t_acc_op.
  by rewrite /= set_var_truncate // (convertible_eval_atype hc).
Qed.

(* [R[x] := R[y] - R[z]]. *)
Lemma sub_sem_fopn_args {s} {xi:var_i} {y} {wy : word Uptr} {z} {wz : word Uptr} :
  convertible xi.(vtype) (aword acc_reg_size) ->
  get_var true (evm s) (v_var y) >>= to_word Uptr = ok wy ->
  get_var true (evm s) (v_var z) >>= to_word Uptr = ok wz ->
  let: wx' := Vword (s:=reg_size) ((wy - wz : word reg_size)) in
  let: vm' := (evm s).[xi <- wx'] in
  sem_fopn_args (ACCFopn_core.sub xi y z) s = ok (with_vm s vm').
Proof.
  move=> hc.
  rewrite /=; t_xrbindP => *; t_acc_op.
  by rewrite /= set_var_truncate // (convertible_eval_atype hc).
Qed.

(* [R[x] := R[y] - imm % 2^32]. *)
Lemma subi_sem_fopn_args {s} {xi:var_i} {y imm wy} :
  convertible xi.(vtype) (aword acc_reg_size) ->
  get_var true (evm s) (v_var y) >>= to_word Uptr = ok wy ->
  let: wx' := Vword (s:=reg_size) ((wy - wrepr reg_size imm : word reg_size)) in
  let: vm' := (evm s).[xi <- wx'] in
  sem_fopn_args (ACCFopn_core.subi xi y imm) s = ok (with_vm s vm').
Proof.
  move=> hc.
  rewrite /=; t_xrbindP => *; t_acc_op.
  rewrite wrepr_opp.
  by rewrite /= set_var_truncate // (convertible_eval_atype hc).
Qed.

(* [R[x] := R[y]] (implemented as [addi x y 0]). *)
Lemma mov_sem_fopn_args {s} {xi:var_i} {y} {wy : word Uptr} :
  convertible xi.(vtype) (aword acc_reg_size) ->
  get_var true (evm s) (v_var y) >>= to_word Uptr = ok wy ->
  let: vm' := (evm s).[xi <- Vword wy] in
  sem_fopn_args (ACCFopn_core.mov xi y) s = ok (with_vm s vm').
Proof.
  move=> hc.
  rewrite /=; t_xrbindP => *; t_acc_op.
  (* mov = addi x y 0; need wadd wy (wrepr 0) = wy *)
  by rewrite /= /wadd wrepr0 GRing.addr0
       set_var_truncate // (convertible_eval_atype hc).
Qed.

(* [R[x] := R[y] ^ imm % 2^32]. *)
Lemma xori_sem_fopn_args {s} {xi:var_i} {y imm wy} :
  convertible xi.(vtype) (aword acc_reg_size) ->
  get_var true (evm s) (v_var y) >>= to_word Uptr = ok wy ->
  let: wx' := Vword (s:=reg_size) (wxor wy (wrepr reg_size imm)) in
  let: vm' := (evm s).[xi <- wx'] in
  sem_fopn_args (ACCFopn_core.xori xi y imm) s = ok (with_vm s vm').
Proof.
  move=> hc.
  rewrite /=; t_xrbindP => *; t_acc_op.
  by rewrite /= set_var_truncate // (convertible_eval_atype hc).
Qed.

(* [R[x] := ~ R[y]] (implemented as [XORI x, y, -1]). *)
Lemma not_sem_fopn_args {s} {xi:var_i} {y} {wy : word Uptr} :
  convertible xi.(vtype) (aword acc_reg_size) ->
  get_var true (evm s) (v_var y) >>= to_word Uptr = ok wy ->
  let: vm' := (evm s).[xi <- Vword (wnot wy)] in
  sem_fopn_args (ACCFopn_core.not xi y) s = ok (with_vm s vm').
Proof.
  move=> hc hgety.
  have -> : wnot wy = wxor wy (wrepr reg_size (-1)) by rewrite /wnot wrepr_m1.
  exact: xori_sem_fopn_args hc hgety.
Qed.

(* [R[x] := imm] (loaded with the single [LI] instruction). *)
Lemma movi_sem_fopn_args {s imm} {xi:var_i} :
  convertible xi.(vtype) (aword acc_reg_size) ->
  let: vm' := (evm s).[xi <- Vword (wrepr U32 imm)] in
  sem_fopn_args (ACCFopn_core.li xi imm) s = ok (with_vm s vm').
Proof.
  move=> hc.
  t_acc_op.
  by rewrite set_var_truncate // (convertible_eval_atype hc).
Qed.

(* [R[x] := R[y] & imm % 2^32]. *)
Lemma andi_sem_fopn_args {s} {xi:var_i} {y imm wy} :
  convertible xi.(vtype) (aword acc_reg_size) ->
  get_var true (evm s) (v_var y) >>= to_word Uptr = ok wy ->
  let: wx' := Vword (s:=reg_size) (wand wy (wrepr reg_size imm)) in
  let: vm' := (evm s).[xi <- wx'] in
  sem_fopn_args (ACCFopn_core.andi xi y imm) s = ok (with_vm s vm').
Proof.
  move=> hc.
  rewrite /=; t_xrbindP => *; t_acc_op.
  by rewrite /= set_var_truncate // (convertible_eval_atype hc).
Qed.

(* [R[x] := R[y] aligned down to a multiple of [wsize_size al]] (implemented
   as [ANDI x, y, -(wsize_size al)]). *)
Lemma align_sem_fopn_args {s} {xi:var_i} {y al wy} :
  convertible xi.(vtype) (aword acc_reg_size) ->
  get_var true (evm s) (v_var y) >>= to_word Uptr = ok wy ->
  let: wx' := Vword (align_word al wy) in
  let: vm' := (evm s).[xi <- wx'] in
  sem_fopn_args (ACCFopn_core.align xi y al) s = ok (with_vm s vm').
Proof.
  move=> hc hgety.
  by rewrite /ACCFopn_core.align (andi_sem_fopn_args hc hgety).
Qed.

Opaque ACCFopn_core.add.
Opaque ACCFopn_core.addi.
Opaque ACCFopn_core.mov.
Opaque ACCFopn_core.li.
Opaque ACCFopn_core.sub.
Opaque ACCFopn_core.subi.
Opaque ACCFopn_core.xori.
Opaque ACCFopn_core.not.
Opaque ACCFopn_core.andi.
Opaque ACCFopn_core.align.

(* NOTE: The RISC-V proof file additionally contains the word-arithmetic helper
   lemmas [wbit_n_add], [mov_movt_aux], [mov_movt_aux1] and [mov_movt].  These
   justify assembling a 32-bit immediate from two 16-bit halves (the LUI+ADDI
   expansion used to load a constant on RISC-V).  ACC loads a full 32-bit
   immediate with the single [LI] instruction, so there is no [acc_params_core]
   definition matching these helpers and hence no ACC analogue. *)

Lemma smart_mov_sem_fopns_args s (w : wreg) (xi:var_i) y :
  convertible xi.(vtype) (aword acc_reg_size) ->
  let: lc := ACCFopn_core.smart_mov xi y in
  get_var true (evm s) y >>= to_word Uptr = ok w ->
  exists vm,
    [/\ sem_fopns_args s lc = ok (with_vm s vm)
      , vm =[\ Sv.singleton xi ] evm s
      & get_var true vm xi >>= to_word Uptr = ok w ].
Proof.
  move=> hc hgety.
  rewrite /ACCFopn_core.smart_mov /=.
  case: eqP => heq /=.
  - case : y heq hgety=> y yi /= *; subst y.
    rewrite -{1}(with_vm_same s); eexists; split; eauto.
  rewrite (mov_sem_fopn_args hc hgety) /=.
  eexists; split; first reflexivity.
  + by move=> z /Sv.singleton_spec hz; t_vm_get.
  by rewrite /get_var Vm.setP_eq /= (convertible_eval_atype hc) /= truncate_word_u.
Qed.

(* Unlike RISC-V's [gen_smart_opi], the ACC combinator returns
   [option (seq opn_args)]: it yields [Some lc] exactly when emitting [lc] is
   safe (the immediate is neutral or small, or the source [y] differs from the
   scratch register [tmp]).  This is the analogue of RISC-V's
   [gen_smart_opi_sem_fopn_args]; the RISC-V precondition
   [is_small imm \/ v_var tmp <> v_var y] is replaced by the hypothesis that
   [gen_smart_opi] succeeds with output [lc]. *)
Lemma gen_smart_opi_sem_fopn_args
  (op : word reg_size -> word reg_size -> word reg_size)
  (on_reg : var_i -> var_i -> var_i -> ACCFopn_core.opn_args)
  (on_imm : var_i -> var_i -> Z -> ACCFopn_core.opn_args)
  (is_small : Z -> bool)
  (neutral : option Z)
  (op_sem_fopn_args :
    forall {s} {xi:var_i} {y} {wy : word Uptr} {z} {wz : word Uptr},
      convertible xi.(vtype) (aword acc_reg_size) ->
      get_var true (evm s) (v_var y) >>= to_word Uptr = ok wy
      -> get_var true (evm s) (v_var z) >>= to_word Uptr = ok wz
      -> let: wx' := Vword (op wy wz) in
      let: vm' := (evm s).[xi <- wx'] in
      sem_fopn_args (on_reg xi y z) s = ok (with_vm s vm'))
  (opi_sem_fopn_args :
    forall {s} {xi:var_i} {y imm wy},
      convertible xi.(vtype) (aword acc_reg_size) ->
      get_var true (evm s) (v_var y) >>= to_word Uptr = ok wy
      -> let: wx' := Vword (op wy (wrepr reg_size imm)) in
     let: vm' := (evm s).[xi <- wx'] in
     sem_fopn_args (on_imm xi y imm) s = ok (with_vm s vm'))
  (neutral_ok : if neutral is Some z then forall w, op w (wrepr _ z) = w else true)
  (tmp : var_i) (xi : var_i) y imm s (w : wreg) lc :
  convertible (vtype tmp) (aword Uptr) ->
  convertible xi.(vtype) (aword acc_reg_size) ->
  ACCFopn_core.gen_smart_opi on_reg on_imm is_small neutral tmp xi y imm = Some lc ->
  get_var true (evm s) (v_var y) >>= to_word Uptr = ok w ->
  exists vm',
    [/\ sem_fopns_args s lc = ok (with_vm s vm')
      , vm' =[\ Sv.add xi (Sv.singleton tmp) ] evm s
      & get_var true vm' xi = ok (Vword (op w (wrepr reg_size imm))) ].
Proof.
  move=> hc1 hc2 hlc hgety.
  rewrite /ACCFopn_core.gen_smart_opi /ACCFopn_core.gen_unsafe_smart_opi in hlc.
  case hmov : (ACCFopn_core.is_mov neutral imm).
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

Section EVAL_INSTR.

Context
  {atoI : arch_toIdent}
  {syscall_state : Type}
  {sc_sem : syscall_sem syscall_state}
  {call_conv : calling_convention}
  {hwcs_i : hw_call_stack_info}
.

#[local] Existing Instance withsubword.

(* Wraps an [opn_args] triple into a [fopn_args]: mirrors RISC-V's
   [RISCVFopn.to_opn] / ACC's own [acc_params.fopn_args_of_opn_args] (that
   one cannot be mentioned here, see [opn_args_eval_instr]'s comment). *)
Definition to_opn (oa : ACCFopn_core.opn_args) : fopn_args :=
  let '(les, op, res) := oa in (les, Oacc op, res).

(* [linear_sem.sem_fopn_args] over [Oacc op] agrees with our local
   [sem_fopn_args] over [op] directly. *)
Lemma sem_fopn_equiv (les : lexprs) (op : acc_op) (res : rexprs) (s : estate) :
  linear_sem.sem_fopn_args (to_opn (les, op, res)) s =
    ACCFopn_coreP.sem_fopn_args (les, op, res) s.
Proof.
  rewrite /to_opn /linear_sem.sem_fopn_args /ACCFopn_coreP.sem_fopn_args /=.
  case: sem_rexprs => //= >.
  rewrite /exec_sopn /= /sopn_sem /=; case: id_valid => //=.
  rewrite /sopn_sem_ /= /semi_to_atype.
  move: (computational_eq _) (computational_eq _) => e1 e2.
  rewrite <- e1, <- e2.
  by case: app_sopn.
Qed.

(* Bridge from [ACCFopn_coreP.sem_fopn_args] to [eval_instr] on the linear
   instruction that [li_of_opn_args] (in [acc_stack_zeroization.v], which
   cannot be mentioned here, see that file's comment) builds from an
   [opn_args] triple. *)
Lemma opn_args_eval_instr {lp ls ii} oa {s'} :
  ACCFopn_coreP.sem_fopn_args oa (to_estate ls) = ok s' ->
  linear_sem.eval_instr lp (MkLI ii (Lopn oa.1.1 (Oacc oa.1.2) oa.2)) ls
    = ok (lnext_pc (lset_estate' ls s')).
Proof.
  case: oa => -[les op] res h.
  rewrite -sem_fopn_equiv in h.
  exact: sem_fopn_args_eval_instr h.
Qed.

(* [R[x] := R[y]] (implemented as [addi x y 0]). *)
Lemma mov_eval_instr {lp ls ii} {xi:var_i} {y} {wy : word Uptr} :
  convertible xi.(vtype) (aword acc_reg_size) ->
  get_var true (lvm ls) (v_var y) = ok (Vword wy) ->
  let: (les, op, res) := ACCFopn_core.mov xi y in
  let: li := MkLI ii (Lopn les (Oacc op) res) in
  let: vm' := (lvm ls).[xi <- Vword wy] in
  linear_sem.eval_instr lp li ls = ok (lnext_pc (lset_vm ls vm')).
Proof.
  move=> hc hy.
  have h := mov_sem_fopn_args (s := to_estate ls) hc (to_word_get_var hy).
  rewrite -sem_fopn_equiv in h.
  exact: sem_fopn_args_eval_instr h.
Qed.

(* [R[x] := imm] (loaded with the single [LI] instruction). *)
Lemma movi_eval_instr {lp ls ii imm} {xi:var_i} :
  convertible xi.(vtype) (aword acc_reg_size) ->
  let: (les, op, res) := ACCFopn_core.li xi imm in
  let: li := MkLI ii (Lopn les (Oacc op) res) in
  let: vm' := (lvm ls).[xi <- Vword (wrepr U32 imm)] in
  linear_sem.eval_instr lp li ls = ok (lnext_pc (lset_vm ls vm')).
Proof.
  move=> hc.
  have h := movi_sem_fopn_args (s := to_estate ls) (imm := imm) hc.
  rewrite -sem_fopn_equiv in h.
  exact: sem_fopn_args_eval_instr h.
Qed.

(* [R[x] := R[y] aligned down to a multiple of [wsize_size al]]. *)
Lemma align_eval_instr {lp ls ii} {xi:var_i} {y al} {wy : word Uptr} :
  convertible xi.(vtype) (aword acc_reg_size) ->
  get_var true (lvm ls) (v_var y) = ok (Vword wy) ->
  let: (les, op, res) := ACCFopn_core.align xi y al in
  let: li := MkLI ii (Lopn les (Oacc op) res) in
  let: vm' := (lvm ls).[xi <- Vword (align_word al wy)] in
  linear_sem.eval_instr lp li ls = ok (lnext_pc (lset_vm ls vm')).
Proof.
  move=> hc hy.
  have h := align_sem_fopn_args (s := to_estate ls) (al := al) hc
              (to_word_get_var hy).
  rewrite -sem_fopn_equiv in h.
  exact: sem_fopn_args_eval_instr h.
Qed.

(* [R[x] := R[y] - R[z]]. *)
Lemma sub_eval_instr {lp ls ii} {xi:var_i} {y z} {wy wz : word Uptr} :
  convertible xi.(vtype) (aword acc_reg_size) ->
  get_var true (lvm ls) (v_var y) = ok (Vword wy) ->
  get_var true (lvm ls) (v_var z) = ok (Vword wz) ->
  let: (les, op, res) := ACCFopn_core.sub xi y z in
  let: li := MkLI ii (Lopn les (Oacc op) res) in
  let: vm' := (lvm ls).[xi <- Vword (wy - wz)] in
  linear_sem.eval_instr lp li ls = ok (lnext_pc (lset_vm ls vm')).
Proof.
  move=> hc hy hz.
  have h := sub_sem_fopn_args (s := to_estate ls) hc (to_word_get_var hy)
              (to_word_get_var hz).
  rewrite -sem_fopn_equiv in h.
  exact: sem_fopn_args_eval_instr h.
Qed.

(* [R[x] := R[y] - imm % 2^32]. *)
Lemma subi_eval_instr {lp ls ii} {xi:var_i} {y imm} {wy : word Uptr} :
  convertible xi.(vtype) (aword acc_reg_size) ->
  get_var true (lvm ls) (v_var y) = ok (Vword wy) ->
  let: (les, op, res) := ACCFopn_core.subi xi y imm in
  let: li := MkLI ii (Lopn les (Oacc op) res) in
  let: vm' := (lvm ls).[xi <- Vword (wy - wrepr reg_size imm)] in
  linear_sem.eval_instr lp li ls = ok (lnext_pc (lset_vm ls vm')).
Proof.
  move=> hc hy.
  have h := subi_sem_fopn_args (s := to_estate ls) (imm := imm) hc
              (to_word_get_var hy).
  rewrite -sem_fopn_equiv in h.
  exact: sem_fopn_args_eval_instr h.
Qed.

(* [R[x] := R[y] + imm % 2^32]. *)
Lemma addi_eval_instr {lp ls ii} {xi:var_i} {y imm} {wy : word Uptr} :
  convertible xi.(vtype) (aword acc_reg_size) ->
  get_var true (lvm ls) (v_var y) = ok (Vword wy) ->
  let: (les, op, res) := ACCFopn_core.addi xi y imm in
  let: li := MkLI ii (Lopn les (Oacc op) res) in
  let: vm' := (lvm ls).[xi <- Vword (wy + wrepr reg_size imm)] in
  linear_sem.eval_instr lp li ls = ok (lnext_pc (lset_vm ls vm')).
Proof.
  move=> hc hy.
  have h := addi_sem_fopn_args (s := to_estate ls) (imm := imm) hc
              (to_word_get_var hy).
  rewrite -sem_fopn_equiv in h.
  exact: sem_fopn_args_eval_instr h.
Qed.

(* [R[x] := R[y] + R[z]]. *)
Lemma add_eval_instr {lp ls ii} {xi:var_i} {y z} {wy wz : word Uptr} :
  convertible xi.(vtype) (aword acc_reg_size) ->
  get_var true (lvm ls) (v_var y) = ok (Vword wy) ->
  get_var true (lvm ls) (v_var z) = ok (Vword wz) ->
  let: (les, op, res) := ACCFopn_core.add xi y z in
  let: li := MkLI ii (Lopn les (Oacc op) res) in
  let: vm' := (lvm ls).[xi <- Vword (wy + wz)] in
  linear_sem.eval_instr lp li ls = ok (lnext_pc (lset_vm ls vm')).
Proof.
  move=> hc hy hz.
  have h := add_sem_fopn_args (s := to_estate ls) hc (to_word_get_var hy)
              (to_word_get_var hz).
  rewrite -sem_fopn_equiv in h.
  exact: sem_fopn_args_eval_instr h.
Qed.

End EVAL_INSTR.

End ACCFopn_coreP.
