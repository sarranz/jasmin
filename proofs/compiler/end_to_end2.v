From Coq Require Import Lia JMeq.
From HB Require Import structures.

From mathcomp Require Import
  ssreflect
  ssralg
  ssrfun
  ssrbool
  ssrnum
  ssrnat
  choice
  distr
  eqtype
  fintype
  matrix
  order
  reals
  seq
  word
  word_ssrZ
.
From mathcomp Require boolp.

From ITree Require Import
  Basics
  ITree
  ITreeDefinition
  ITreeFacts
  Rutt
  RuttFacts
  Exception
.
Import ITree.

Require Import
  equiv_extras
  rutt_extras
  xrutt
  xrutt_facts
  it_exec
.
Require Import
  it_sems_core
  psem
  psem_facts
  relational_logic
  hoare_logic
  hoare_valid
.
Require Import
  compiler
  core_logics
  distr_extra
  itree_safety_facts
  utils
  values
  word
  wseq
.
Require Import
  arch_decl
  arch_extra
  arch_sem
  arch_params
  asm_invariant
  sem_params_of_arch_extra
.
Require Import
  arch_params_proof
  stack_alloc_proof_1
  stack_alloc_proof_2
  compiler_proof
  it_compiler_proof
  asm_gen_proof
.
Require allocation.

Require Import
  cil
  cil_indcca
  dinterp
.
Require indcca.

Import Order.TTheory.

#[local] Open Scope ring_scope.
#[local] Open Scope Z.
#[local] Open Scope order_scope.

#[local] Coercion Pos.to_nat : positive >-> nat.

#[local] Notation "'let*' p ':=' c1 'in' c2" :=
  (@ITree.bind _ _ _ c1 (fun p => c2))
    (at level 61, p as pattern, c1 at next level, right associativity).

#[local] Notation "x |> f" := (f x) (only parsing, at level 25).

Section MOVE.

Context
  {reg regx xreg rflag cond asm_op extra_op syscall_state : Type}
  {sc_sem : syscall.syscall_sem syscall_state}
  {asm_e : asm_extra reg regx xreg rflag cond asm_op extra_op}
  {call_conv : calling_convention}
  {asm_scsem : asm_syscall_sem}
  {it_asm_scsem : it_asm_syscall_sem}
  {lowering_options : Type}
  (aparams : architecture_params lowering_options)
  (haparams : h_architecture_params aparams)
  (cparams : compiler_params lowering_options)
  (print_uprogP : forall s p, cparams.(print_uprog) s p = p)
  (print_sprogP : forall s p, cparams.(print_sprog) s p = p)
  (print_linearP : forall s p, cparams.(print_linear) s p = p)
.

Definition safe_uprog (p : uprog) (fn : funname) (fs : fstate) : Prop :=
  safe (is_error wE) (isem_unit p fn fs).

Definition val_is_def (v : value) : bool :=
  if v is Varr _ a then arr_is_def a else is_defined v.

Definition res_defined (p : uprog) (fn : funname) (fs : fstate) : Prop :=
  lutt
    (fun T e => True)
    (fun T e r => True)
    (fun fs => all val_is_def (fvals fs))
    (isem_unit p fn fs).

(* The (syntactic) precondition of [fn], taken from its contract,
   holds on [fs]. *)
Definition fun_pre (p : uprog) (fn : funname) (fs : fstate) : bool :=
  is_ok
    (sem_pre
       (wsw := nosubword) (wa := withassert) (dc := indirect_c) (pT := progUnit)
       p fn fs).

Lemma all_drop X p (s : seq X) n :
  all p s ->
  all p (drop n s).
Proof. by rewrite -[in all p _](cat_take_drop n s) all_cat => /andP []. Qed.

Lemma all_take X p (s : seq X) n :
  all p s ->
  all p (take n s).
Proof. by rewrite -[in all p _](cat_take_drop n s) all_cat => /andP []. Qed.

Definition wseq_of_val (t : ctype) (v : value) : wseq :=
  let v' :=
    match t with
    | carr p => Let a := to_arr p v in ok (wseq_of_arr a)
    | cword ws => Let w := to_word ws v in ok (split_vec 8 w)
    | _ => ok [::]
    end
  in
  rdflt [::] v'.

Lemma value_uincl_is_def x y :
  val_is_def x ->
  value_uincl x y ->
  wseq_of_val (type_of_val x) x = wseq_of_val (type_of_val x) y.
Proof.
case: x y => [b1|z1|len1 a1|ws1 w1|t1 ?] [b2|z2|len2 a2|ws2 w2|t2 ?] //=.
- move=> hdef hu; rewrite /wseq_of_val.
  have ? := WArray.uincl_len hu; subst len2.
  rewrite /to_arr !WArray.castK /=.
  have heq :
    forall i : Z,
      i \in ziota 0 len1 ->
      exists2 w, WArray.get8 a1 i = ok w & WArray.get8 a2 i = ok w.
  - move=> i hi.
    have [|w hw] := elimT (valid_getP a1 i).
    + apply/andP; split; last by move: hdef => /allP /(_ _ hi).
      apply/WArray.in_boundP; rewrite in_ziota in hi; lia.
    exists w => //.
    have :=
      WArray.uincl_get (aa := AAdirect) (al := Aligned) (i := i) (ws := U8)
                       (w := w) hu.
    rewrite /WArray.get /=.
    rewrite /read /= is_align8 /= add_0 Z.mul_1_r hw /= decode_u8 => /(_ erefl).
    by t_xrbindP=> w' ? -> <- <-; rewrite decode_u8.
  rewrite /wseq_of_arr; f_equal; elim: ziota heq => //= i zs hi heq.
  move: (heq i); rewrite in_cons eqxx => /(_ isT) [w -> ->] /=.
  by rewrite hi // => j hj; apply: heq; rewrite in_cons hj orbT.
move=> _ hu.
rewrite /wseq_of_val /= truncate_word_u.
by rewrite (word_uincl_truncate (w := w1) hu) // truncate_word_u.
Qed.

Definition cast_vals tys vs := [seq wseq_of_val x.1 x.2 | x <- zip tys vs ].

Definition cast_vals_self vs := cast_vals (map type_of_val vs) vs.

Lemma cast_vals_cat tys1 tys2 vs1 vs2 :
  size tys1 = size vs1 ->
  cast_vals (tys1 ++ tys2) (vs1 ++ vs2)
  = cast_vals tys1 vs1 ++ cast_vals tys2 vs2.
Proof. by move=> h; rewrite /cast_vals zip_cat // map_cat. Qed.

Lemma mapM2_truncate_val_type_of_val tys vs vs' :
  mapM2 ErrType truncate_val tys vs = ok vs' ->
  [seq type_of_val v | v <- vs'] = tys.
Proof.
elim: tys vs vs' => [|ty tys ih] [|v vs] //= vs'; first by move=> [<-].
by t_xrbindP=> v' /truncate_val_has_type <- ? /ih <- <-.
Qed.

(* Types of the results of a function, according to its signature. *)
Definition get_tyout (p : uprog) (fn : funname) : seq ctype :=
  oapp (fun fd => map eval_atype fd.(f_tyout)) [::] (get_fundef p.(p_funcs) fn).

Lemma values_uincl_is_def s s' :
  let: ty := map type_of_val s in
  all val_is_def s ->
  values_uincl s s' ->
  cast_vals ty s = cast_vals ty s'.
Proof.
elim: s s' => [|x xs hi] [|y ys] //=.
- by move=> _ /List_Forall2_inv.
move=> /andP [hx hxs] /List_Forall2_inv [uxy uxys].
rewrite /cast_vals /= (value_uincl_is_def hx uxy).
f_equal.
exact: (hi _ hxs uxys).
Qed.

Let REeq {E : Type -> Type} A1 A2 (e1: E A1) (e2: E A2) :=
  exists h : A2 = A1, e1 = eq_rect A2 E e2 A1 h.

Let RAeq {E : Type -> Type} A1 A2 (e1: E A1) (a1: A1) (e2: E A2) (a2: A2) :=
  JMeq a1 a2.

Definition values_match p fn xfd t s' t' :=
  let argt := get_typed_reg_values t xfd.(asm_fd_arg) in
  let n := get_nb_wptr p fn in
  let mt' := t'.(asm_mem) in
  let ress := s'.(fvals) in
  let rest := get_typed_reg_values t' xfd.(asm_fd_res) in
  let tys := get_tyout p fn in
  [/\ all val_is_def ress
    , [seq type_of_val x | x <- ress] = tys
    , List.Forall2 (value_in_mem mt') (take n ress) (take n argt)
    & cast_vals (drop n tys) (drop n ress) = cast_vals (drop n tys) rest ].

Definition aux_post p q fn xfd s t s' t' :=
  let args := s.(fvals) in
  let ms := s.(fmem) in
  let argt := get_typed_reg_values t xfd.(asm_fd_arg) in
  let mt := t.(asm_mem) in
  let ress := s'.(fvals) in
  let ms' := s'.(fmem) in
  let rest := get_typed_reg_values t' xfd.(asm_fd_res) in
  let mt' := t'.(asm_mem) in
  let n := get_nb_wptr p fn in
  let tys := [seq type_of_val x | x <- drop n ress] in
  [/\ mem_agreement ms' mt' t'.(asm_rip) q.(asm_globs)
    , t'.(asm_scs) = s'.(fscs)
    , zeroized_u cparams p fn args argt ms mt mt'
    , values_match p fn xfd t s' t'
    , mem_equiv ms ms'
    , asmsem_invariant t t'
    & validw mt =3 validw mt' ].

Section LUTT_XRUTT_TRANS_R.

Context
  {E1 E2 : Type -> Type}
  (is_error : forall T, E1 T -> bool)
  (REv : forall A B, E1 A -> E2 B -> Prop)
  (RAns : forall A B, E1 A -> A -> E2 B -> B -> Prop)
  (PEv2 : prepred E2)
  (PAns2 : postpred E2)
  {R1 R2 : Type}
  (RR : R1 -> R2 -> Prop)
  (P2 : R2 -> Prop)
.

Lemma lutt_xrutt_trans_r' t1 t2
  (REv' : forall A B, E1 A -> E2 B -> Prop)
  (RAns' : forall A B, E1 A -> A -> E2 B -> B -> Prop)
  RR' :
  (forall A1 A2 e1 e2,
      PEv2 e2 -> REv e1 e2 -> REv' A1 A2 e1 e2) ->
  (forall A1 A2 e1 a1 e2 a2,
      IsNoCut_ (errcutoff is_error) A1 e1 ->
      IsNoCut_ nocutoff A2 e2 ->
      PEv2 e2 ->
      REv e1 e2 ->
      RAns' A1 A2 e1 a1 e2 a2 ->
      PAns2 e2 a2 /\ RAns e1 a1 e2 a2) ->
  (forall r1 r2, P2 r2 -> RR r1 r2 -> RR' r1 r2) ->
  lutt PEv2 PAns2 P2 t2 ->
  xrutt (errcutoff is_error) nocutoff REv RAns RR t1 t2 ->
  xrutt (errcutoff is_error) nocutoff REv' RAns' RR' t1 t2.
Proof.
move=> he ha hr h1 h2.
apply: xrutt_weaken_v2; [ done | done | | | | exact: lutt_xrutt_trans_r h1 h2 ].
- move=> ???? []; exact: he.
- move=> ???????? []; exact: ha.
move=> ?? []; exact: hr.
Qed.

End LUTT_XRUTT_TRANS_R.

Lemma correct_comp entries p q fn fd :
  compile_prog_to_asm aparams cparams entries p = ok q ->
  fn \in entries ->
  get_fundef p.(p_funcs) fn = Some fd ->
  exists2 xfd,
    get_fundef q.(asm_funcs) fn = Some xfd
    & forall s t,
        lutt (fun _ _ => True) (fun _ _ _ => True)
          (fun t' => validw t.(asm_mem) =3 validw t'.(asm_mem))
          (isem_asm q fn t) ->
        safe_uprog p fn s ->
        res_defined p fn s ->
        full_pre p q fn xfd s t ->
        eutt
          (aux_post p q fn xfd s t)
          (isem_unit p fn s) (isem_asm q fn t).
Proof.
move=> hcomp hfn hfd.
have [xfd [hxfd _ heq]] := [elaborate
  it_compile_prog_to_asmP
    haparams print_uprogP print_sprogP print_linearP hcomp hfn ].
exists xfd; first exact: hxfd.
move=> s t hvalid hsafe hdef hpre.
have hmeq := [elaborate sem_fun_mem_equiv_uprog
  (wa := withassert) (asm_op := extended_op) (ep := ep_of_asm_e)
  (spp := spp_of_asm_e) (sip := sip_of_asm_e) (wsw := nosubword)
  (dc := indirect_c) (wE := wE) p tt (fn := fn)] dummy_instr_info s I.
have hinv := [elaborate iasmsem_exportcall_invariantP (wE := wE) q fn t].
apply/simple_rutt_eutt/(EPreRel_safe_xrutt_rutt hsafe).
apply: (lutt_xrutt_trans_l'
  (REv := EPreRel_safe (is_error wE) REeq)
  (RAns := RAeq)
  (RR := fun s' t' =>
           [/\ all val_is_def (fvals s')
             , mem_equiv (fmem s) (fmem s')
             , asmsem_invariant t t'
             , validw t.(asm_mem) =3 validw t'.(asm_mem)
             & full_post cparams p q fn xfd s t s' t' ]));
  cycle -2.
- exact:
    (isem_fun_finalize (wa := withassert) (scP := sCP_unit) (wE := wE)) hfd.
- apply: lutt_xrutt_trans_l'; cycle -2.
  + exact: hdef.
  + refine (lutt_xrutt_trans_l'
      (RR := fun r1 r2 =>
               [/\ asmsem_invariant t r2
                 , validw t.(asm_mem) =3 validw r2.(asm_mem)
                 & full_post cparams p q fn xfd s t r1 r2 ])
      _ _ _ hmeq
      (lutt_xrutt_trans_r'
        (RR := fun r1 r2 =>
                 validw t.(asm_mem) =3 validw r2.(asm_mem)
                 /\ full_post cparams p q fn xfd s t r1 r2)
        _ _ _ hinv
        (lutt_xrutt_trans_r'
          (RR := full_post cparams p q fn xfd s t)
          _ _ _ hvalid (heq _ _ hpre)))).
  (* [hmeq] layer; [hinv] and [hvalid] layers *)
  + by move=> ???? _ h; exact: h.
  + move=> A1 A2 e1 a1 e2 a2 hne _ _ _ h; split; last exact: h.
    by clear h; case: e1 hne.
  + by move=> r1 r2 hm hr; exact: conj hm hr.
  + by move=> ???? _ h; exact: h.
  + by move=> A1 A2 e1 a1 e2 a2 _ _ _ _ h; split; [exact: I | exact: h].
  + by move=> r1 r2 hi [hv hf]; split.
  + by move=> ???? _ h; exact: h.
  + by move=> A1 A2 e1 a1 e2 a2 _ _ _ _ h; split; [exact: I | exact: h].
  + by move=> r1 r2 hv hf; split.
  + move=> T1 T2 [|[scs1 n1]]; first by left.
    move=> [|[scs2 n2]]; first by left.
    by move=> _ [??]; subst scs2 n2; right; exists erefl.
  + move=> T1 T2 [//|[scs1 n1]] r1 [//|[scs2 n2]] r2 _ _ _ [??]; subst scs2 n2.
    by move=> /(JMeq_eq (x := r1)) <-.
  by move=> r1 r2 hd [hm [hi hv hf]]; split.
- done.
- done.
move=> s' t' [st hfin] [{}hdef hmeq' hinv' hvalid' [hm hscs hz hptr hres]].
split=> //.
have htys : [seq type_of_val v | v <- fvals s'] = get_tyout p fn.
- rewrite /get_tyout hfd /=.
  move: hfin; rewrite /finalize_funcall; t_xrbindP=> vres _ vres' htr <- /=.
  exact: mapM2_truncate_val_type_of_val htr.
split=> //.
rewrite -htys -map_drop; apply: values_uincl_is_def hres.
by rewrite all_drop // hdef.
Qed.

End MOVE.

Section CHOICEOF.

  Context (T : Type).

  Definition choiceof : Type := T.

  Lemma choiceof_comparable : comparable choiceof.
  Proof. by move=> ??; apply/boolp.pselect. Qed.

  #[export] HB.instance Definition choiceof_eqType :=
    hasDecEq.Build choiceof (compareP choiceof_comparable).

  #[export] HB.instance Definition choiceof_choiceType :=
    boolp.gen_choiceMixin choiceof.

End CHOICEOF.

Notation "{ 'choice' T }" := (choiceof T)
  (format "{ 'choice'  T }").

Section WSEQ_EP.

Context {syscall_state : Type} {ep : EstateParams syscall_state}.

Lemma wseq_in_mem m n (a : WArray.array n) p :
  arr_is_def a ->
  value_in_mem m (Varr a) (Vword p) ->
  wseq_of_arr a = read_wseq m p n.
Proof.
move=> hdef [_ [[/= <- h]]].
rewrite /wseq_of_arr /read_wseq.
have {}hdef :
  forall i : Z,
    i \in ziota 0 n ->
    exists2 w,
      WArray.get8 a i = ok w &
      read m Aligned (p + wrepr Uptr i)%R U8 = ok w.
- move=> i hi.
  have [|w hw] := elimT (valid_getP a i).
  + apply/andP; split; last by move: hdef => /allP /(_ _ hi).
    apply/WArray.in_boundP; rewrite in_ziota in hi; lia.
  exists w => //; apply: h.
  by rewrite /read /= is_align8 /= add_0 hw /= decode_u8.
f_equal; elim: ziota hdef => //= x xs hind hdef.
move: (hdef x); rewrite in_cons eqxx /read8 => /(_ erefl) [w -> ->].
rewrite hind // => i hi; apply: hdef; by rewrite in_cons hi orbT.
Qed.

Lemma wseq_word_in_mem m ws (w : word ws) p :
  value_in_mem m (Vword w) (Vword p) ->
  split_vec 8 w = read_wseq m p (Z.to_pos (wsize_size ws)).
Proof.
move=> [_ [[<- h]]].
have {}h :
  forall i, i \in ziota 0 (wsize_size ws) -> read8 m p i = ok (LE.wread8 w i).
- move=> i; rewrite in_ziota !zify => hi.
  by apply: h; rewrite get_val_byte_word //; lia.
have -> :
  read_wseq m p (Z.to_pos (wsize_size ws))
  = [seq LE.wread8 w i | i <- ziota 0 (wsize_size ws)].
- rewrite /read_wseq Z2Pos.id; last exact: wsize_size_pos.
  suff -> :
    mapM (read8 m p) (ziota 0 (wsize_size ws))
    = ok [seq LE.wread8 w i | i <- ziota 0 (wsize_size ws)] by [].
  elim: ziota h => //= i zs ih h.
  rewrite h ?in_cons ?eqxx //= ih // => j hj.
  by apply: h; rewrite in_cons hj orbT.
have -> : split_vec 8 w = LE.encode w by [].
rewrite -{1}(mkseq_nth 0%R (LE.encode w)) /mkseq LE.size_encode.
rewrite /LE.wread8 ziotaE -map_comp.
by apply: eq_map => i /=; rewrite Nat2Z.id.
Qed.

(* Read a result of type [ty] from memory, given the pointer [pv] to it. *)
Definition read_res (m : mem) (ty : ctype) (pv : value) : wseq :=
  if to_pointer pv is Ok ptr then
    match ty with
    | carr len => read_wseq m ptr len
    | cword ws => read_wseq m ptr (Z.to_pos (wsize_size ws))
    | _ => [::]
    end
  else [::].

Lemma value_in_mem_read_res m v pv :
  val_is_def v ->
  value_in_mem m v pv ->
  wseq_of_val (type_of_val v) v = read_res m (type_of_val v) pv.
Proof.
case: v => [b|z|len a|ws w|//] hdef hin; have [p [? h]] := hin; subst pv.
all: rewrite /read_res /= truncate_word_u //=.
- rewrite /wseq_of_val /= /to_arr WArray.castK /=.
  exact: wseq_in_mem hdef hin.
rewrite /wseq_of_val /= truncate_word_u /=.
exact: wseq_word_in_mem hin.
Qed.

Lemma write_wseq_wf_ptr_arg
  {gsz rip ms mt p bytes wptrs vs vt writable ws v p' i} :
  let: mt' := write_wseq mt p bytes in
  wf_arg_pointer gsz rip ms mt wptrs vs vt writable ws v p' i ->
  wf_arg_pointer gsz rip ms mt' wptrs vs vt writable ws v p' i.
Proof.
rewrite /write_wseq; case h: fill_mem => [m'|] //=.
move=> [?? hvalid ???]; split=> // w hw.
by rewrite -(fill_mem_validw_eq h) (hvalid _ hw).
Qed.

Lemma write_wseq_wf_arg {gsz rip ms mt p bytes wptrs vs vt ws i} :
  wf_arg gsz rip ms mt wptrs ws vs vt i ->
  wf_arg gsz rip ms (write_wseq mt p bytes) wptrs ws vs vt i.
Proof.
rewrite /wf_arg; case: nth => // b [p' [-> h]]; exists p'; split=> //.
exact: write_wseq_wf_ptr_arg.
Qed.

Lemma write_wseq_it_wf_args {gsz rip ms mt p bytes wptrs vs vt ws} :
  wf_args gsz rip ms mt wptrs ws vs vt ->
  wf_args gsz rip ms (write_wseq mt p bytes) wptrs ws vs vt.
Proof. move=> h i; exact: write_wseq_wf_arg (h i). Qed.

Lemma write_wseq_extend_mem ms mt rip gd p a :
  let: n := Z.of_nat (size a) in
  n <= wbase Uptr ->
  disjoint_zrange p n rip (Z.of_nat (size gd)) ->
  (forall w, validw ms Aligned w U8 -> disjoint_zrange p n w 1) ->
  extend_mem ms mt rip gd ->
  extend_mem ms (write_wseq mt p a) rip gd.
Proof.
move=> hsz hrip hdisj; rewrite /write_wseq; case hm': fill_mem => [m'|//] /=.
move=> [?? hold ? hv hgd]; split=> //.
- move=> x hx; rewrite (hold _ hx) (fill_mem_disjoint hm') //; exact: hdisj hx.
- move=> x /hv; by rewrite (fill_mem_validw_eq hm').
move=> x hx; rewrite -(hgd _ hx); apply: (fill_mem_disjoint hm').
exact: disjoint_zrange_byte hrip hx.
Qed.

End WSEQ_EP.

Section MAIN.

Context {R : realType}.

Notation distr := (distr R).
Notation Rnd := (Rnd (R := R)).

Instance sc_sem : syscall.syscall_sem unit :=
  {| syscall.get_random := fun _ _ => (tt, [::]); |}.

Notation E := (ErrEvent +' RndEvent unit).

#[local] Existing Instance wE.
#[local] Existing Instance RndE00.

Definition handleE : Handler (RndEvent unit) Rnd :=
  fun _ '(it_sems_core.Rnd _ len) =>
    let* bs := unif_rV (Z.to_nat len) in
    Ret (tt, wseq_of_wvec bs).

Definition to_Rnd : itree (RndEvent unit) ~> itree Rnd :=
  fun _ t => interp handleE t.

Context
  {reg regx xreg rflag cond asm_op extra_op : Type}
  {asm_e : asm_extra reg regx xreg rflag cond asm_op extra_op}
  {call_conv : calling_convention}
  {asm_scsem : asm_syscall_sem}
  {it_asm_scsem : it_asm_syscall_sem}
.

Definition mkfs (m : mem) (vs : values) : fstate :=
  {| fscs := tt; fmem := m; fvals := vs; |}.

(* safe on any memory with the same layout as [m] *)
Definition safe_on p fn m vs :=
  forall m',
    mem_equiv m m' ->
    safe_uprog p fn (mkfs m' vs).

Definition res_defined_on p fn m vs :=
  forall m',
    mem_equiv m m' ->
    res_defined p fn (mkfs m' vs).

Definition pre_on p fn m vs :=
  forall m',
    mem_equiv m m' ->
    fun_pre p fn (mkfs m' vs).

Definition xm_with_mem (mem : mem) (m : asmmem) : asmmem :=
  {|
    asm_rip := m.(asm_rip);
    asm_scs := m.(asm_scs);
    asm_mem := mem;
    asm_reg := m.(asm_reg);
    asm_regx := m.(asm_regx);
    asm_xreg := m.(asm_xreg);
    asm_flag := m.(asm_flag);
  |}.

Definition xm_write
  (x : asm_typed_reg) (v : value) (ptr : pointer) (xm : asmmem) : exec asmmem :=
  match x with
  | ARReg r =>
      if v is Varr _ a then
        let xm' := mem_write_reg MSB_CLEAR r ptr xm in
        let m' := write_wseq xm'.(asm_mem) ptr (wseq_of_arr a) in
        ok (xm_with_mem m' xm')
      else
        Let w := to_word reg_size v in
        ok (mem_write_reg MSB_CLEAR r w xm)
  | ARegX rx =>
      Let w := to_word reg_size v in
      ok (mem_write_regx MSB_CLEAR rx w xm)
  | AXReg xr =>
      Let w := to_word xreg_size v in
      ok (mem_write_xreg MSB_CLEAR xr w xm)
  | ABReg f =>
      Let b := to_bool v in
      ok (mem_write_rflag xm f (Some b))
  end.

Definition xm_writes
  (m : asmmem)
  (xs : seq asm_typed_reg)
  (args : values)
  (ptrs : seq pointer) :
  exec asmmem :=
  foldM (fun x => xm_write x.1.1 x.1.2 x.2) m (zip (zip xs args) ptrs).

Section DEFS.

Class JazzIParams :=
  {
    entries : seq funname; (* API *)
    mS : mem; (* Initial source memory *)
    mT : mem; (* Initial target memory *)
    ripT : pointer; (* Initial target RIP *)
    rmT : regmap; (* Initial target register map *)
    rxmT : regxmap; (* Initial target MMX map *)
    xrmT : xregmap; (* Initial target XMM map *)
    rfmT : rflagmap; (* Initial target flag map *)
  }.

Definition jazz_api_wf (JP : JazzIParams) (p : uprog) : Prop :=
  forall fn, fn \in entries -> isSome (get_fundef p.(p_funcs) fn).

Definition jazz_api_safe (JP : JazzIParams) (p : uprog) : Prop :=
  forall fn fd,
    fn \in entries ->
    get_fundef p.(p_funcs) fn = Some fd ->
    forall vs m,
      let: fs := mkfs m vs in
      mem_equiv m mS -> (* TODO This should be included in safety extraction *)
      fun_pre p fn fs ->
      [/\ safe_uprog p fn fs & res_defined p fn fs ].

Context
  {JP : JazzIParams}
  (p : uprog) (* source program (Jasmin) *)
  (q : asm_prog) (* target program (assembly) *)
  (export_ok : jazz_api_wf JP p)
  (safe_p : jazz_api_safe JP p)
  (* The initial target memory contains the initial source memory and the
     globals. *)
  (init_agree : mem_agreement mS mT ripT q.(asm_globs))
.

(* TODO prove in arch *)
Lemma asm_validw fn xm :
  lutt (fun _ _ => True) (fun _ _ _ => True)
    (fun xm' => validw xm.(asm_mem) =3 validw xm'.(asm_mem))
    (isem_asm q fn xm).
Proof using. Admitted.

Definition xmT : asmmem :=
  {|
    asm_rip := ripT;
    asm_scs := tt;
    asm_mem := mT;
    asm_reg := rmT;
    asm_regx := rxmT;
    asm_xreg := xrmT;
    asm_flag := rfmT;
  |}.

Definition MoS : choiceType := {choice mem}.

Definition MoT : choiceType := {choice asmmem}.

(* The leftover memories keep the structure of the initial ones, and the target
   memory contains the source memory and the globals. *)
Record sim (ms : MoS) (mt : MoT) : Prop :=
  {
    sim_ms : mem_equiv ms mS;
    sim_mt : mem_equiv mt.(asm_mem) mT;
    sim_rip : mt.(asm_rip) = ripT;
    sim_agree : mem_agreement ms mt.(asm_mem) ripT q.(asm_globs);
  }.

(* TODO should take xfd *)
Definition mkxm
  (fn : funname) (xm : asmmem) (args : values) (ptrs : seq pointer) : asmmem :=
  if get_fundef (asm_funcs q) fn is Some xfd then
    let xm' := mem_write_reg MSB_CLEAR ad_rsp (top_stack mS) xm in
    if xm_writes xm' xfd.(asm_fd_arg) args ptrs is Ok xm'' then xm''
    else xmT (* absurd *)
  else xmT. (* absurd *)

(* Oracles are function names from the API. *)
Record export_fn :=
  {
    _fn :> funname; (* function name *)
    efn_export : _fn \in entries; (* the function is in the API *)
  }.

Definition JNo : choiceType := {choice export_fn}.

(* Oracle inputs *)
Record valid_input (o : export_fn) : Type :=
  {
    _args :> values; (* inputs *)
    vi_pre : pre_on p o mS _args; (* inputs satisfy the function's precondition *)
    vi_ptrs : seq pointer; (* pointers for array inputs *)

    (* We only allow inputs where, for any pair of memories in simulation
       (which the adversary does not see), writing the inputs satisfies the
       compiler's precondition:
       - Pointers are valid and fresh
       - There is enough stack space *)
    vi_ptrs_ok :
      forall ms mt xfd,
        sim ms mt ->
        get_fundef q.(asm_funcs) o = Some xfd ->
        full_pre p q o xfd (mkfs ms _args) (mkxm o mt _args vi_ptrs);
  }.

Definition JIn (o : JNo) : choiceType := {choice valid_input o}.

Definition JOut (o : JNo) : choiceType := seq wseq.

Instance JazzI : OracleSystemInterface :=
  {|
    No := JNo;
    In := JIn;
    Out := JOut;
  |}.

(* -------------------------------------------------------------------------- *)
(* Source oracle system *)

(* Source programs take inputs as lists of values *)
Definition unmkfs (fs : fstate) : seq wseq * mem :=
  let: tys := [seq type_of_val v | v <- fs.(fvals) ] in
  (cast_vals tys fs.(fvals), fs.(fmem)).

Definition isem_unit_res
  (o : JNo) (i : JIn o) (m : MoS) : itree E (JOut o * MoS) :=
  let fs := mkfs m i in
  let* fs' := isem_unit p o fs in
  Ret (unmkfs fs').

#[global] Arguments isem_unit_res : clear implicits.

(* Source semantics:
   - Allows assertions
   - Call by value
   - No subword casting
   - Every function call sets a fresh environment with arguments
   - Can sample randomness
   - Allows nontermination *)
Definition OoS (o : JNo) (i : JIn o) (m : MoS) : itree Rnd (JOut o * MoS) :=
  let* ores := to_Rnd (isem_unit_res o i m |> interp_Err) in
  if ores is ESok (rs, m') then Ret (rs, m')
  else Ret ([::], m). (* TODO this case is absurd, how can we rule out this
                         case? for now, returning the input memory keeps
                         [sim] *)

Instance Source : OracleSystem JazzI :=
  {|
    Mo := MoS;
    Oo := OoS;
    mi := mS;
  |}.

(* -------------------------------------------------------------------------- *)
(* Target oracle system *)

(* Reading the results from target states.
   Pointer results are read from memory from the argument pointers.
   The rest from registers. *)
Definition xget_res (fn : funname) (t t' : asmmem) : seq wseq :=
  if get_fundef q.(asm_funcs) fn is Some xfd then
    let n := get_nb_wptr p fn in
    let tys := get_tyout p fn in
    let argt := get_typed_reg_values t xfd.(asm_fd_arg) in
    let rest := get_typed_reg_values t' xfd.(asm_fd_res) in
    [seq read_res t'.(asm_mem) x.1 x.2 | x <- zip (take n tys) (take n argt) ]
    ++ cast_vals (drop n tys) rest
  else [::]. (* absurd *)

Lemma xget_resP xfd fn t fs t' :
  get_fundef q.(asm_funcs) fn = Some xfd ->
  values_match p fn xfd t fs t' ->
  cast_vals (get_tyout p fn) (fvals fs) = xget_res fn t t'.
Proof.
move=> hxfd [hdef htys hmem hreg].
rewrite /xget_res hxfd /= -hreg -htys -map_drop -map_take.
rewrite -[in LHS](cat_take_drop (get_nb_wptr p fn) (fvals fs)).
rewrite map_cat cast_vals_cat ?size_map //; congr (_ ++ _).
move: hmem (all_take (get_nb_wptr p fn) hdef).
elim: (take (get_nb_wptr p fn) (fvals fs))
  (take (get_nb_wptr p fn) (get_typed_reg_values t (asm_fd_arg xfd)))
  => [|v vs ih] [|pv pvs] /List_Forall2_inv //= [hv hvs] /andP [hdv hdvs].
by rewrite -(ih _ hvs hdvs) /cast_vals /= (value_in_mem_read_res hdv hv).
Qed.

Definition isem_asm_res
  (o : JNo) (i : JIn o) (m : MoT) : itree E (JOut o * MoT) :=
  let xm := mkxm o m i (vi_ptrs i) in
  let* xm' := isem_asm q o xm in
  Ret (xget_res o xm xm', xm').
Arguments isem_asm_res : clear implicits.

(* Assembly semantics:
   - Does not allow assertions
   - Share state, call by reference
   - Subword casting
   - Function calls are merely changes to the program counter
   - Can sample randomness
   - Allows nontermination *)
Definition OoT (o : JNo) (i : JIn o) (m : MoT) : itree Rnd (JOut o * MoT) :=
  let* ores := to_Rnd (isem_asm_res o i m |> interp_Err) in
  if ores is ESok res then Ret res
  else Ret ([::], m). (* absurd: returning the input memory keeps [sim] *)

Instance Target : OracleSystem JazzI :=
  {|
    Mo := MoT;
    Oo := OoT;
    mi := xmT;
  |}.

(* -------------------------------------------------------------------------- *)
(* Proof. *)

Context
  {lowering_options : Type}
  (aparams : architecture_params lowering_options)
  (haparams : h_architecture_params aparams)
  (cparams : compiler_params lowering_options)
  (print_uprogP : forall s p, cparams.(print_uprog) s p = p)
  (print_sprogP : forall s p, cparams.(print_sprog) s p = p)
  (print_linearP : forall s p, cparams.(print_linear) s p = p)
  (hcomp : compile_prog_to_asm aparams cparams entries p = ok q)
.

Definition eq_sim {X : Type} : X * MoS -> X * MoT -> Prop :=
  eqR (X := X) sim.

Lemma mem_equiv_refl m : mem_equiv m m.
Proof. by split. Qed.

Lemma mem_equiv_sym m1 m2 : mem_equiv m1 m2 -> mem_equiv m2 m1.
Proof.
move=> [hss hv]; split; first by apply: stack_stable_sym; exact: hss.
by move=> al x ws; rewrite hv.
Qed.

Lemma sim_mS_xmT : sim mS xmT.
Proof.
split; [exact: mem_equiv_refl | exact: mem_equiv_refl | done | exact: init_agree].
Qed.

Lemma sim_mem_equiv_mi ms mt :
  sim ms mt ->
  mem_equiv mS ms.
Proof. by move=> /sim_ms /mem_equiv_sym. Qed.

Lemma sim_mem_equiv_ms ms mt :
  sim ms mt ->
  mem_equiv ms mS.
Proof. exact: sim_ms. Qed.

Lemma xm_write_mem x v ptr xm xm' :
  xm_write x v ptr xm = ok xm' ->
  mem_equiv xm.(asm_mem) xm'.(asm_mem) /\ xm'.(asm_rip) = xm.(asm_rip).
Proof.
rewrite /xm_write; case: x => [r|rx|xr|f].
- case: v => [b|z|len a|ws w|ty ?].
  all: try by t_xrbindP=> ? _ <-; split; [exact: mem_equiv_refl | done].
  move=> [<-] /=; split=> //.
  split; first exact: write_wseq_stack_stable.
  by move=> al x ws; rewrite -write_wseq_validw_eq.
all: by t_xrbindP=> ? _ <-; split; [exact: mem_equiv_refl | done].
Qed.

Lemma xm_writes_mem xm xs args ptrs xm' :
  xm_writes xm xs args ptrs = ok xm' ->
  mem_equiv xm.(asm_mem) xm'.(asm_mem) /\ xm'.(asm_rip) = xm.(asm_rip).
Proof.
rewrite /xm_writes.
elim: (zip (zip xs args) ptrs) xm => /= [|[[x v] ptr] l ih] xm.
- by move=> [<-]; split; [exact: mem_equiv_refl | done].
t_xrbindP=> xm1 /xm_write_mem [h1 e1] /ih [h2 e2].
split; first exact: mem_equiv_trans h1 h2.
by rewrite e2 e1.
Qed.

Lemma mkxm_sim ms mt fn args ptrs :
  sim ms mt ->
  mem_equiv (mkxm fn mt args ptrs).(asm_mem) mT
  /\ (mkxm fn mt args ptrs).(asm_rip) = ripT.
Proof.
move=> hm; rewrite /mkxm.
case: get_fundef => [xfd|].
2: by split; [exact: mem_equiv_refl | done]. (* absurd: [xmT] is related to itself *)
case hw: xm_writes => [xm''|].
2: by split; [exact: mem_equiv_refl | done]. (* absurd: [xmT] is related to itself *)
have [h1 e1] := xm_writes_mem hw.
split.
- exact: mem_equiv_trans (mem_equiv_sym h1) (sim_mt hm).
by rewrite e1; exact: sim_rip hm.
Qed.

Lemma sim_post fn vs ptrs ms mt fs' xm' xfd :
  sim ms mt ->
  aux_post cparams p q fn xfd (mkfs ms vs) (mkxm fn mt vs ptrs) fs' xm' ->
  sim (fmem fs') xm'.
Proof.
move=> hm [hagree _ _ _ hmeq hinv hvalid].
have [hmt hrip] := mkxm_sim fn vs ptrs hm.
have {}hmeq : mem_equiv ms (fmem fs') := hmeq.
have hxrip : xm'.(asm_rip) = ripT.
- by rewrite -(asmsem_invariant_rip hinv).
split.
- exact: mem_equiv_trans (mem_equiv_sym hmeq) (sim_ms hm).
- have hxm : mem_equiv (mkxm fn mt vs ptrs).(asm_mem) xm'.(asm_mem).
  + by split; [exact: asmsem_invariant_stack_stable hinv | exact: hvalid].
  exact: mem_equiv_trans (mem_equiv_sym hxm) hmt.
- exact: hxrip.
by rewrite hxrip in hagree.
Qed.

Definition post_isem
  (fn : funname)
  (vs : values)
  (ptrs : seq pointer)
  (ms : mem)
  (mt : asmmem)
  (fs' : fstate)
  (xm' : asmmem) :
  Prop :=
    let: fs := mkfs ms vs in
    let: xm := mkxm fn mt vs ptrs in
    exists xfd,
      [/\ get_fundef q.(asm_funcs) fn = Some xfd
        , full_pre p q fn xfd fs xm
        & aux_post cparams p q fn xfd fs xm fs' xm' ].

Lemma eutt_isem_post fn fd ms mt (i : valid_input fn) :
  fn.(_fn) \in entries ->
  get_fundef p.(p_funcs) fn = Some fd ->
  safe_uprog p fn (mkfs ms i) ->
  res_defined p fn (mkfs ms i) ->
  sim ms mt ->
  eutt (post_isem fn i (vi_ptrs i) ms mt)
    (isem_unit p fn (mkfs ms i))
    (isem_asm q fn (mkxm fn mt i (vi_ptrs i))).
Proof.
move=> hfn hfd hsafe hdef hm.
have [xfd hxfd heq] :=
  correct_comp haparams print_uprogP print_sprogP print_linearP hcomp hfn hfd.
have hpre := i.(vi_ptrs_ok) hm hxfd.
have := heq _ _ (asm_validw _ _) hsafe hdef hpre.
apply: eutt_subrel.
by move=> fs xm h; exists xfd; split.
Qed.

Lemma eutt_isem_res o i ms mt :
  sim ms mt ->
  eutt eq_sim (isem_unit_res o i ms) (isem_asm_res o i mt).
Proof.
move=> hm.
apply: eutt_clo_bind.
- case ok_fd: get_fundef (export_ok o.(efn_export)) => [fd|//] _.
  have [hsafe hdef] :=
    safe_p o.(efn_export) ok_fd (sim_mem_equiv_ms hm)
      (i.(vi_pre) (sim_mem_equiv_mi hm)).
  exact: eutt_isem_post o.(efn_export) ok_fd hsafe hdef hm.
move=> fs xm [xfd [hxfd hpre hpost]]; apply eutt_Ret.
have [_ _ _ hargs _ _ _] := hpost.
have [_ htys _ _] := hargs.
split=> /=.
- by rewrite htys; exact: xget_resP hxfd hargs.
exact: sim_post hm hpost.
Qed.

(* Security preservation: the source and target oracle systems are in
   simulation *)
Theorem compiler_preserves : simulating Source Target.
Proof.
exists sim; split; first exact: sim_mS_xmT.
move=> o i m1 m2 hm.
have [xfd [hgetq _ heq]] := [elaborate
  it_compile_prog_to_asmP haparams print_uprogP print_sprogP print_linearP
    hcomp (efn_export o)].
apply (eutt_clo_bind _ (UU := exec_rel eq_sim)).
- apply/eutt_interp_RR/interp_exec_eutt_gen/eutt_isem_res/hm.
move=> /= [[rs ms]|?] [[rt mt]|?] //=; last first.
- (* Absurd: both oracles return the input memory, so [sim] is kept by [hm] *)
  by move=> _; apply eutt_Ret; split.
by move=> [/= -> hm']; apply eutt_Ret; split.
Qed.

End DEFS.

(* -------------------------------------------------------------------------- *)
(* Instantiation to KEMs and IND-CCA. *)

Section INSTANTIATION.

(* TODO I would like to build [mS] from [mT] so that the statement is
     forall target state, exists source state,
       forall adversary A,
         Advantage A target = Advantage A source

   But there is no way of building memories right now. We would need to expose
   an operation in the memory module to build
     "a memory restricted to valid addresses X, with frames Y, root Z, and a
     limit W"
    where X would be [validw mT] minus the globals minus [limit, root)
          Y would be [::]
          Z would be [rmT ad_rsp]
          W would be [top_stack mT] *)

Context
  {JP : JazzIParams}
  (pkbytes skbytes ctbytes msgbytes : positive)
  (fn_genkey fn_encap fn_decap : funname)
  (fd_genkey fd_encap fd_decap : ufundef)
  (entriesE : entries = [:: fn_genkey; fn_encap; fn_decap])
  (p : uprog)
  (q : asm_prog)
.

Definition pk0 := mkwvec pkbytes [::].
Definition sk0 := mkwvec skbytes [::].
Definition ct0 := mkwvec ctbytes [::].
Definition msg0 := mkwvec msgbytes [::].

Definition dummyp := WArray.empty pkbytes.
Definition dummys := WArray.empty skbytes.
Definition dummyc := WArray.empty ctbytes.
Definition dummym := WArray.empty msgbytes.

(* ML-KEM's implementation involves the three algorithms.
   The signatures take arrays (readable and writable) and return the writable
   ones.
   As usual, we ask that the source program is safe on valid inputs. *)
Context
  (fd_genkey_ok : get_fundef p.(p_funcs) fn_genkey = Some fd_genkey)
  (fd_encap_ok : get_fundef p.(p_funcs) fn_encap = Some fd_encap)
  (fd_decap_ok : get_fundef p.(p_funcs) fn_decap = Some fd_decap)
  (ppk psk pct pmsg : pointer)
  (genkey_ok :
    forall vs m,
      let: fs := mkfs m vs in
      mem_equiv m mS ->
      fun_pre p fn_genkey fs ->
      safe_uprog p fn_genkey fs /\ res_defined p fn_genkey fs)
  (encap_ok :
    forall vs m,
      let: fs := mkfs m vs in
      mem_equiv m mS ->
      fun_pre p fn_encap fs ->
      safe_uprog p fn_encap fs /\ res_defined p fn_encap fs)
  (decap_ok :
    forall vs m,
      let: fs := mkfs m vs in
      mem_equiv m mS ->
      fun_pre p fn_decap fs ->
      safe_uprog p fn_decap fs /\ res_defined p fn_decap fs)
  (* The initial target memory contains the initial source memory and the
     globals. *)
  (init_agree : mem_agreement mS mT ripT q.(asm_globs))
.

Notation OracleSystem := (OracleSystem (R := R)) (only parsing).

#[local] Instance KEMP_of_JP : KEMParams :=
  {|
    pkey := wvec pkbytes;
    skey := wvec skbytes;
    ctxt := wvec ctbytes;
    msg := wvec msgbytes;
    dummy_ct := ct0;
    dummy_msg := msg0;
  |}.

Lemma export_genkey : fn_genkey \in entries.
Proof. by rewrite entriesE !inE eqxx. Qed.

Lemma export_encap : fn_encap \in entries.
Proof. by rewrite entriesE !inE eqxx orbT. Qed.

Lemma export_decap : fn_decap \in entries.
Proof. by rewrite entriesE !inE eqxx !orbT. Qed.

Definition efn_kg : export_fn := {| efn_export := export_genkey; |}.
Definition efn_encap : export_fn := {| efn_export := export_encap; |}.
Definition efn_decap : export_fn := {| efn_export := export_decap; |}.

Section JKEM.
  (* The KEM induced by a Jasmin program. *)

  Context (J : OracleSystem (JazzI p q)).

  Notation InK := (In (I := KEM)).
  Notation OutK := (Out (I := KEM)).

  (* We parameterize over how the inputs are written to memory, requiring, e.g.,
     that writing with a public key succeeds (i.e., the pointer points to
     allocated memory) *)
  Context
    (mkiGenKey : valid_input p q efn_kg)
    (mkiEncap : InK OEncap -> valid_input p q efn_encap)
    (mkiDecap : InK ODecap -> valid_input p q efn_decap)
  .

  Let Oo_JKEM_GenKey
    (i : InK OGenKey) (m : Mo) : itree Rnd (OutK OGenKey * Mo) :=
    let* (rs, m') := J.(Oo) efn_kg mkiGenKey m in
    if rs is [:: pk; sk ] then Ret ((mkwvec _ pk, mkwvec _ sk), m')
    else Ret ((pk0, sk0), m). (* absurd *)

  Let Oo_JKEM_Encap
    (i : InK OEncap) (m : Mo) : itree Rnd (OutK OEncap * Mo) :=
    let* (rs, m') := J.(Oo) efn_encap (mkiEncap i) m in
    if rs is [:: ct; msg ] then Ret ((mkwvec _ ct, mkwvec _ msg), m')
    else Ret ((ct0, msg0), m). (* absurd *)

  Let Oo_JKEM_Decap
    (i : InK ODecap) (m : Mo) : itree Rnd (OutK ODecap * Mo) :=
    let* (rs, m') := J.(Oo) efn_decap (mkiDecap i) m in
    if rs is [:: msg ] then Ret (mkwvec _ msg, m')
    else Ret (msg0, m). (* absurd *)

  Definition _Oo_KEM
    (o : kem_oracle_name) : InK o -> Mo -> itree Rnd (OutK o * Mo) :=
    match o with
    | OGenKey => Oo_JKEM_GenKey
    | OEncap => Oo_JKEM_Encap
    | ODecap => Oo_JKEM_Decap
    end.

  Instance KEM_of_Jazz : OracleSystem KEM :=
    {|
      Mo := Mo;
      Oo := fun _ i => _Oo_KEM i; (* needs lambda to typecheck *)
      mi := mi;
    |}.

End JKEM.

(* Two programs in simulation induce KEMs in simulation. *)
Lemma simulating_JKEM P Q mkigk mkienc mkidec :
  simulating P Q ->
  simulating
    (KEM_of_Jazz P mkigk mkienc mkidec)
    (KEM_of_Jazz Q mkigk mkienc mkidec).
Proof.
move=> [sim hsim]; exists sim; split; first exact/hsim.(sim_mi).
move=> [[] | pk | [sk ct]] m1 m2 hm.
- apply: eutt_clo_bind; first exact: hsim.(sim_Oo) hm.
  move=> [r m1'] [_ m2'] [/= <-] hm'.
  by case: r => [| pk [| sk [|??]]]; apply eutt_Ret.
- apply: eutt_clo_bind; first exact: hsim.(sim_Oo) hm.
  move=> [r m1'] [_ m2'] [/= <-] hm'.
  by case: r => [| ct [| msg [|??]]]; apply eutt_Ret.
apply: eutt_clo_bind; first exact: hsim.(sim_Oo) hm.
move=> [r m1'] [_ m2'] [/= <-] hm'.
by case: r => [| msg [|??]]; apply eutt_Ret.
Qed.

Context
  {lowering_options : Type}
  (aparams : architecture_params lowering_options)
  (haparams : h_architecture_params aparams)
  (cparams : compiler_params lowering_options)
  (print_uprogP : forall s p, cparams.(print_uprog) s p = p)
  (print_sprogP : forall s p, cparams.(print_sprog) s p = p)
  (print_linearP : forall s p, cparams.(print_linear) s p = p)
  (hcomp : compile_prog_to_asm aparams cparams entries p = ok q)
.

(* The main result for ML-KEM. *)
Theorem mlkem_end_to_end mkigk mkienc mkidec :
  indcca_reduction
    (KEM_of_Jazz (Source p q) mkigk mkienc mkidec)
    (KEM_of_Jazz (Target p q) mkigk mkienc mkidec).
Proof.
apply/sim_indcca_adv/simulating_JKEM.
apply: (compiler_preserves
  _ _ init_agree haparams print_uprogP print_sprogP print_linearP
  hcomp).
- move=> fn; rewrite entriesE !inE => /or3P [] /eqP ->.
  + by rewrite fd_genkey_ok.
  + by rewrite fd_encap_ok.
  by rewrite fd_decap_ok.
move=> fn fd; rewrite entriesE !inE => /or3P [] /eqP -> _ vs m hm hpre.
- exact: genkey_ok hm hpre.
- exact: encap_ok hm hpre.
exact: decap_ok hm hpre.
Qed.

(* The same result for the intended definition of KEM-IND-CCA. *)
Theorem mlkem_end_to_end_game {advmem : Type} mkigk mkienc mkidec :
  indcca.reduction (advmem := advmem)
    (challenger_of_kem (KEM_of_Jazz (Source p q) mkigk mkienc mkidec))
    (challenger_of_kem (KEM_of_Jazz (Target p q) mkigk mkienc mkidec)).
Proof. exact/indcca_reduction_reduction/mlkem_end_to_end. Qed.

End INSTANTIATION.

End MAIN.
