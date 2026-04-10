(* * Denotational Probabilistic Semantics for Jasmin *)

(* ** Imports and settings *)
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssralg.
From mathcomp Require Import choice fintype order seq.
From mathcomp.classical Require Import boolp.
From mathcomp.reals Require Import reals.
From mathcomp.experimental_reals Require Import distr.

Require Import xseq.
Require Import
  array type expr gen_map warray_ sem_type sem_op_typed
  values varmap expr_facts low_memory syscall_sem psem_defs.
Require Import psem_core it_sems_core.
Require Import flag_combination sem_params.

Import Utf8.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope Z_scope.
Local Open Scope seq_scope.

Import GRing.Theory.

(* -------------------------------------------------------------------- *)
Section DPSEM.

Context
  {asm_op : Type}
  {ep : EstateParams unit}
  {spp : SemPexprParams}
  {sip : SemInstrParams asm_op unit}
.

Existing Instance sCP_unit.
Existing Instance nosubword.
Existing Instance indirect_c.
Existing Instance progUnit.

Context {R : realType}.

(* ** State + error type
 * -------------------------------------------------------------------- *)

Inductive dstate :=
| DSok (s : estate)
| DSerr (e : error).

Lemma dstate_comparable : comparable dstate.
Proof. by move=> m1 m2; apply/pselect. Qed.

HB.instance Definition _ :=
  hasDecEq.Build dstate (compareP dstate_comparable).

HB.instance Definition _ := gen_choiceMixin dstate.

Notation Dstate := ({distr dstate / R}).

(* ** Function-state + error type
 * -------------------------------------------------------------------- *)

Inductive dfstate :=
| DFSok (fs : fstate)
| DFSerr (e : error).

Lemma dfstate_comparable : comparable dfstate.
Proof. by move=> m1 m2; apply/pselect. Qed.

HB.instance Definition _ :=
  hasDecEq.Build dfstate (compareP dfstate_comparable).

HB.instance Definition _ := gen_choiceMixin dfstate.

Notation Dfstate := ({distr dfstate / R}).

(* ** Error-distribution monad combinators
 * -------------------------------------------------------------------- *)

Definition dret (s : estate) : Dstate :=
  @dunit R dstate (DSok s).

Definition derr (e : error) : Dstate :=
  @dunit R dstate (DSerr e).

Definition dnone : Dstate :=
  @dnull R dstate.

Definition dbind (mu : Dstate) (f : estate -> Dstate) : Dstate :=
  \dlet_(x <- mu)
    match x with
    | DSok s => f s
    | DSerr e => @dunit R dstate (DSerr e)
    end.

Definition dlift {A : Type} (r : exec A) (f : A -> Dstate) : Dstate :=
  match r with
  | Ok a => f a
  | Error e => derr e
  end.

(* ** Function-state distribution combinators
 * -------------------------------------------------------------------- *)

Definition dfret (fs : fstate) : Dfstate :=
  @dunit R dfstate (DFSok fs).

Definition dferr_f (e : error) : Dfstate :=
  @dunit R dfstate (DFSerr e).

Definition dfnone : Dfstate :=
  @dnull R dfstate.

Definition dlift_f {A : Type} (r : exec A) (f : A -> Dfstate) : Dfstate :=
  match r with
  | Ok a => f a
  | Error e => dferr_f e
  end.

Definition dbind_estate (mu : Dstate) (f : estate -> Dfstate) : Dfstate :=
  \dlet_(x <- mu)
    match x with
    | DSok s => f s
    | DSerr e => @dunit R dfstate (DFSerr e)
    end.

Definition dbind_fstate (mu : Dfstate) (f : fstate -> Dstate) : Dstate :=
  \dlet_(x <- mu)
    match x with
    | DFSok fs => f fs
    | DFSerr e => @dunit R dstate (DSerr e)
    end.

(* ** Random bytes sampling
 * -------------------------------------------------------------------- *)

(* Uniform distribution over all bytes *)
Definition all_bytes : seq u8 := map (wrepr U8) (ziota 0 (wbase U8)).

(* Uniform random byte sequence of length n *)
Fixpoint dunif_bytes (n : nat) : {distr (seq u8) / R} :=
  match n with
  | O => dunit [::]
  | S n' =>
    \dlet_(b <- duni all_bytes)
      \dlet_(bs <- dunif_bytes n')
        dunit (b :: bs)
  end.

(* Random bytes: sample uniformly via exec_syscall_arg / exec_syscall_store,
   matching the ITree version in fexec_syscall (it_sems_core.v). *)
Definition drandom_bytes (gd : glob_decls) (o : syscall_t)
    (xs : lvals) (ves : values) (s : estate) : Dstate :=
  dlift (exec_syscall_arg o ves) (fun len =>
    \dlet_(bytes <- dunif_bytes (Z.to_nat len))
      dlift (exec_syscall_store o tt (emem s) ves bytes) (fun scsmvs =>
        let fs := {| fscs := scsmvs.1.1; fmem := scsmvs.1.2;
                     fvals := scsmvs.2 |} in
        dlift (upd_estate true gd xs fs s) dret)).

(* ** While loop iterator
 * -------------------------------------------------------------------- *)

Section WHILE.
  Variables (run_c1 run_c2 : estate -> Dstate).
  Variable (eval_cond : estate -> exec bool).

  Fixpoint while_n (n : nat) (s : estate) : Dstate :=
    match n with
    | O => dnone
    | S n' =>
      dbind (run_c1 s) (fun s1 =>
        dlift (eval_cond s1) (fun b =>
          if b then dbind (run_c2 s1) (while_n n')
          else dret s1))
    end.
End WHILE.

(* ** For loop combinator
 * -------------------------------------------------------------------- *)

Section FOR.
  Variable (run_c : estate -> Dstate).

  Definition for_sem (x : var_i) (ws : seq Z) : estate -> Dstate :=
    foldr (fun w k s =>
      dlift (write_var true x (Vint w) s) (fun s' =>
        dbind (run_c s') k)) dret ws.
End FOR.

(* ** Instruction and command semantics
 * -------------------------------------------------------------------- *)

Section DSEM_BODY.
  Variables (p : uprog).
  Let gd := p_globs p.
  Variable (call_sem : funname -> fstate -> Dfstate).

  (* Command semantics via foldr *)
  Definition dsem_cmd_aux
    (f : instr -> estate -> Dstate)
    (c : cmd) : estate -> Dstate :=
    foldr (fun i k s => dbind (f i s) k) dret c.

  (* Instruction semantics — structurally recursive on instr *)
  Fixpoint dsem_i (i : instr) (s : estate) {struct i} : Dstate :=
    let: MkI _ii ir := i in
    match ir with
    | Cassgn x tg ty e =>
        dlift (sem_assgn p x tg ty e s) dret

    | Copn xs _tg o es =>
        dlift (sem_sopn gd o s xs es) dret

    | Csyscall xs o es =>
        dlift (sem_pexprs true gd s es) (fun ves =>
          drandom_bytes gd o xs ves s)

    | Cif e c1 c2 =>
        dlift (sem_cond gd e s) (fun b =>
          dsem_cmd_aux dsem_i (if b then c1 else c2) s)

    | Cwhile _al c1 e _ii c2 =>
        @dlim R dstate (fun n =>
          while_n
            (dsem_cmd_aux dsem_i c1)
            (dsem_cmd_aux dsem_i c2)
            (sem_cond gd e) n s)

    | Cfor x (d, lo, hi) c =>
        dlift (sem_bound gd lo hi s) (fun bounds =>
          for_sem (dsem_cmd_aux dsem_i c) x
            (wrange d bounds.1 bounds.2) s)

    | Ccall xs fn args =>
        dlift (sem_pexprs (~~direct_call) gd s args) (fun vargs =>
          dbind_fstate (call_sem fn (mk_fstate vargs s)) (fun fs =>
            dlift (upd_estate (~~direct_call) gd xs fs s) dret))
    end.

  Definition dsem_cmd := dsem_cmd_aux dsem_i.

End DSEM_BODY.

(* ** Global fixpoint for function calls
 * -------------------------------------------------------------------- *)

Section DSEM_CALL.
  Variables (p : uprog).

  Fixpoint dsem_call_n (n : nat)
      (fn : funname) (fs : fstate) : Dfstate :=
    match n with
    | O => dfnone
    | S n' =>
      match get_fundef (p_funcs p) fn with
      | Some fd =>
        dlift_f (initialize_funcall p tt fd fs) (fun s1 =>
          dbind_estate (dsem_cmd p (dsem_call_n n') fd.(f_body) s1) (fun s_callee =>
            dlift_f (finalize_funcall fd s_callee) dfret))
      | None => dferr_f ErrType
      end
    end.

  Definition dsem_call (fn : funname) (fs : fstate) : Dfstate :=
    dlim (fun n => dsem_call_n n fn fs).

  Definition dsem (c : cmd) : estate -> Dstate :=
    dsem_cmd p dsem_call c.

End DSEM_CALL.

End DPSEM.
