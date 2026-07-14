(* * Syntax of the linear language *)

From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq eqtype ssralg.
Require Import expr fexpr label sopn.

Section ASM_OP.

Context `{asmop:asmOp}.

(* --------------------------------------------------------------------------- *)
(* Syntax                                                                      *)

Record gen_linstr (A : Type) : Type := MkLI { li_ii : instr_info; li_i : A; }.

Variant lcall_kind :=
  | OnStack
  | InReg of var_i
  | OnHWCallStack.

Inductive linstr_r :=
  | Lopn   : lexprs -> sopn -> rexprs -> linstr_r
  | Lsyscall : syscall_t -> linstr_r
  | Lcall    : lcall_kind -> remote_label -> linstr_r
     (* OnStack: ra on top of data stack; InReg r: ra in r;
        OnHWCallStack: ra pushed to the hardware call stack. *)
  | Lret     : linstr_r
  | Lret_hwcallstack : linstr_r
     (* return using the hardware call stack (OTBN: RET) *)
  | Lalign : linstr_r
  | Llabel : label_kind -> label -> linstr_r
  | Lgoto  : remote_label -> linstr_r
  | Ligoto : rexpr -> linstr_r (* Absolute indirect jump *)
  | LstoreLabel : var -> label -> linstr_r
  | Lcond  : fexpr -> label -> linstr_r
  | Lrepeat_loop : (var_i + Z) -> seq (gen_linstr linstr_r) -> linstr_r
.

Notation linstr := (gen_linstr linstr_r).

Definition lcmd := seq linstr.

Definition is_label (lbl: label) (i: linstr) : bool :=
  match i.(li_i) with
  | Llabel _ lbl' => lbl == lbl'
  | _ => false
  end.

(* -------------------------------------------------------------------- *)
Definition find_label (lbl : label) (c : seq linstr) :=
  let idx := seq.find (is_label lbl) c in
  if idx < size c then ok idx else type_error.

Record lfundef := LFundef {
 lfd_info : fun_info;
 lfd_align : wsize;
 lfd_tyin : seq ltype;
 lfd_arg  : seq var_i;
 lfd_body : lcmd;
 lfd_tyout : seq ltype;
 lfd_res  : seq var_i;  (* /!\ did we really want to have "seq var_i" here *)
 lfd_export: bool;
 lfd_callee_saved: seq var; (* A list of variables that must be initialized before calling this function *)
 lfd_stk_max : Z; (* max amount of stack memory used by this function (and all functions called by this one *)
 lfd_frame_size : Z; (* needed for stack zeroization *)
 lfd_align_args : seq wsize;
}.

(* takes into account the padding due to the alignment of the stack of export functions *)
Definition lfd_total_stack lfd :=
  if lfd.(lfd_export) then
    (lfd.(lfd_stk_max) + wsize_size lfd.(lfd_align) - 1)%Z
  else
    lfd.(lfd_stk_max).

Definition signature_of_lfundef (lfd: lfundef) : function_signature :=
  (map atype_of_ltype (lfd_tyin lfd), map atype_of_ltype (lfd_tyout lfd)).

Record lprog :=
 {  lp_rip   : Ident.ident;
    lp_rsp : Ident.ident;
    lp_globs : seq u8;
    lp_glob_names: seq (var * wsize * Z);
    lp_funcs : seq (funname * lfundef) }.

End ASM_OP.

Notation linstr := (gen_linstr linstr_r).
Notation fopn_args := (lexprs * sopn * rexprs)%type.

Definition li_of_fopn_args
  {asm_op : Type}
  {asmop : asmOp asm_op}
  (ii : instr_info)
  (p : fopn_args) :
  linstr :=
  MkLI ii (Lopn p.1.1 p.1.2 p.2).
