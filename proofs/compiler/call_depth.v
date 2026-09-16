(* -------------------------------------------------------------------- *)
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat.
(* ------- *) Require Import expr.
Import Utf8.

(* Syntactic call-graph depth of a source ([uprog]) function: a leaf has
   depth 1, and [depth f = 1 + max over callees g of depth g]; a syscall
   contributes nothing (see PLAN_CALLSTACK.md, Section 3). The recursion
   is bounded by [fuel] instead of following the (possibly cyclic) call
   graph directly: a wrong declaration order, or an actual cycle, only
   lowers the computed value, and the compile-time checks that rely on
   [call_depth] then reject the program. *)

Section ASM_OP.

Context `{asmop : asmOp}.

Fixpoint depth_i (call : funname -> nat) (i : instr) {struct i} : nat :=
  let: MkI _ ir := i in depth_i_r call ir

with depth_i_r (call : funname -> nat) (ir : instr_r) {struct ir} : nat :=
  let fix depth_c (c : cmd) {struct c} :=
    if c is i :: c' then maxn (depth_i call i) (depth_c c') else 0
  in
  match ir with
  | Cassgn _ _ _ _ | Copn _ _ _ _ | Csyscall _ _ _ | Cassert _ => 0
  | Cif    _  c1 c2    => maxn (depth_c c1) (depth_c c2)
  | Cfor   _  c1       => depth_c c1
  | Cwhile _ c1 _ _ c2 => maxn (depth_c c1) (depth_c c2)
  | Ccall  _ g _       => call g
  end.

Definition depth_c (call : funname -> nat) (c : cmd) : nat :=
  foldl (fun acc i => maxn acc (depth_i call i)) 0 c.

Fixpoint depth_fun (p : uprog) (fuel : nat) (fn : funname) {struct fuel} : nat :=
  match fuel with
  | 0 => 0
  | fuel'.+1 =>
    if get_fundef (p_funcs p) fn is Some fd then
      1 + depth_c (depth_fun p fuel') (f_body fd)
    else 0
  end.

Definition call_depth (p : uprog) (fn : funname) : nat :=
  depth_fun p (size (p_funcs p)) fn.

End ASM_OP.
