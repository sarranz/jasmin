From mathcomp Require Import ssreflect ssrbool eqtype.
Require Import
  expr
  fexpr
  label
  linear
  stack_zero_strategy
  arch_decl
  arch_extra
  acc_decl
  acc_extra
  acc_instr_decl
  acc_params_core.
Require Import compiler_util.

Module E.

  Definition pass : string := "stack zeroization"%string.

  Definition error (msg : pp_error) : pp_error_loc :=
    {|
      pel_msg := msg;
      pel_fn := None;
      pel_fi := None;
      pel_ii := None;
      pel_vi := None;
      pel_pass := Some pass;
      pel_internal := false;
    |}.

  Definition error_size (ws : wsize) : pp_error_loc :=
    error
      (pp_box
         [:: pp_s "Clear step"; pp_s ("u" ++ string_of_wsize ws)%string;
             pp_s "is not supported on ACC, only u32 and u256 are; set";
             pp_s """stackzerosize""" ]).

  Definition error_range (stk_max max : Z) (ws : wsize) : pp_error_loc :=
    error
      (pp_box
         [:: pp_s "The stack size to zeroize ("; pp_z stk_max;
             pp_s ") is too large for the unrolled strategy on ACC with";
             pp_s "clear step"; pp_s ("u" ++ string_of_wsize ws)%string;
             pp_s "(maximum"; pp_z max;
             pp_s "); use the loop strategy instead" ]).

  Definition error_loop_sct : pp_error_loc :=
    error (pp_s "Strategy ""loop with SCT"" is not supported in ACC"%string).

End E.

Section STACK_ZEROIZATION.

Context {atoI : arch_toIdent}.

Let mkli := @MkLI linstr_r dummy_instr_info.

Section RSP.

Context
  (vrsp : var_i)
  (lbl : label)
  (alignment ws : wsize)
  (stk_max : Z)
.

Let vsaved_sp := mk_var_i (to_var X05).
Let voff := mk_var_i (to_var X06).
Let vzero := mk_var_i (to_var X07).
Let vtmp := mk_var_i (to_var X12).
Let vwzero := mk_var_i (to_var W31).
Let vflags := map (fun f => mk_var_i (to_var f)) [:: MF0; LF0; ZF0 ].

(* [ACCFopn_core.*] return [opn_args] (an [acc_op], not a [sopn]), unlike
   [RISCVFopn.*]/[li_of_fopn_args]; this wraps the operation with [Oacc]. *)
Definition li_of_opn_args
  (ii : instr_info) (oa : ACCFopn_core.opn_args) : linstr :=
  let '(les, op, res) := oa in
  MkLI ii (Lopn les (Oacc op) res).

(* After the clear-step check in [stack_zeroization_cmd], [ws] is [U32] or
   [U256]. *)
Let is_large : bool := ws == U256.

(* -------------------------------------------------------------------- *)
(* For both strategies we need to initialize:
   - [saved_sp] to save [SP]
   - [off] to offset from [SP] to already zeroized region
   - [SP] to align and point to the end of the region to zeroize
   - [zero] to zero
   Since we can't align [SP] directly, we use [zero] as a scratch register.
   This is the implementation:
    saved_sp = sp
    off = stk_max
    zero = saved_sp & - (wsize_size alignment)
    sp = zero
    sp -= off
    zero = 0
   For [ws = u256], [set0_wide] additionally zeroes the wide register used to
   store zeroes. *)
Definition sz_init : lcmd :=
  let args :=
    ACCFopn_core.mov vsaved_sp vrsp
    :: ACCFopn_core.li voff stk_max
    :: ACCFopn_core.align vzero vsaved_sp alignment
    :: ACCFopn_core.mov vrsp vzero
    :: ACCFopn_core.sub vrsp vrsp voff
    :: [:: ACCFopn_core.li vzero 0 ]
  in
  map (li_of_opn_args dummy_instr_info) args.

(* [w31 = #set0_256()], i.e. [bn.xor w31, w31, w31, FG0]. *)
Definition set0_wide : linstr :=
  mkli
    (Lopn
       (map LLvar vflags ++ [:: LLvar vwzero ])
       (Oasm (ExtOp (set0 U256)))
       [::]).

Definition sz_init_ws : lcmd :=
  sz_init ++ (if is_large then [:: set0_wide ] else [::]).

Definition restore_sp : lcmd :=
  [:: li_of_opn_args dummy_instr_info (ACCFopn_core.mov vrsp vsaved_sp) ].

(* -------------------------------------------------------------------- *)
(* (ws)[v + off] = zero, either [sw x7, off(v)] or [bn.sd w31, off(v)]. *)
Definition store_zero (v : var_i) (off : Z) : linstr_r :=
  let addr := faddv Uptr v (fconst reg_size off) in
  if is_large then
    Lopn [:: Store Aligned U256 addr ] (Oacc BN_SD) [:: rvar vwzero ]
  else
    Lopn [:: Store Aligned U32 addr ] (Oacc (RV32 SW)) [:: rvar vzero ].

(* [[tmp], tmp = #BN_SD_INC(w31, tmp)], i.e. [bn.sd w31, 0(tmp++)]; used only
   by the (unverified) [loophw] strategy for [ws = u256]. *)
Definition store_zero_inc : linstr_r :=
  Lopn
    [:: Store Aligned U256 (faddv Uptr vtmp (fconst reg_size 0)); LLvar vtmp ]
    (Oacc BN_SD_INC)
    [:: rvar vwzero; rvar vtmp ].

(* -------------------------------------------------------------------- *)
(* Strategy [loop]. Implementation:
l1:
    off = off - wsize_size ws
    tmp = sp + off
    (ws)[tmp] = zero
    if (off != 0) goto l1
*)
Definition sz_loop : lcmd :=
  let dec_off :=
    let '(r, op, e) := ACCFopn_core.subi voff voff (wsize_size ws) in
    Lopn r (Oacc op) e
  in
  let compute_address :=
    let '(r, op, e) := ACCFopn_core.add vtmp vrsp voff in
    Lopn r (Oacc op) e
  in
  let irs :=
    [:: Llabel InternalLabel lbl
      ; dec_off
      ; compute_address
      ; store_zero vtmp 0
      ; Lcond (Fapp2 (Oneq (Op_w U32)) (Fvar voff) (fconst reg_size 0)) lbl ]
  in
  map mkli irs.

Definition stack_zero_loop : lcmd := sz_init_ws ++ sz_loop ++ restore_sp.

(* -------------------------------------------------------------------- *)
(* Strategy [unrolled]. Implementation:
    (ws)[rsp + (stk_max / wsize_size ws - 1) * wsize_size ws] = zero
    ...
    (ws)[rsp + 0] = zero
*)
Definition sz_unrolled : lcmd :=
  [seq mkli (store_zero vrsp (k * wsize_size ws))
     | k <- rev (ziota 0 (stk_max / wsize_size ws)) ].

Definition stack_zero_unrolled : lcmd :=
  sz_init_ws ++ sz_unrolled ++ restore_sp.

(* -------------------------------------------------------------------- *)
(* Strategy [loophw] (unverified: the hardware [loop] instruction has no
   semantics in the model). Implementation:
    off = stk_max / wsize_size ws  (* the iteration count *)
    tmp = sp
    loop off:
      (ws)[tmp] = zero; tmp += wsize_size ws   (* u32 *)
      [tmp], tmp = #BN_SD_INC(w31, tmp)        (* u256 *)
*)
Definition sz_loophw : lcmd :=
  let count := (stk_max / wsize_size ws)%Z in
  let body :=
    if is_large then [:: mkli store_zero_inc ]
    else
      let inc_tmp :=
        let '(r, op, e) := ACCFopn_core.addi vtmp vtmp (wsize_size ws) in
        Lopn r (Oacc op) e
      in
      [:: mkli (store_zero vtmp 0)
        ; mkli inc_tmp ]
  in
  [:: li_of_opn_args dummy_instr_info (ACCFopn_core.li voff count)
    ; li_of_opn_args dummy_instr_info (ACCFopn_core.mov vtmp vrsp)
    ; mkli (Lrepeat_loop (inl voff) body) ].

Definition stack_zero_loophw : lcmd :=
  sz_init_ws ++ sz_loophw ++ restore_sp.

(* -------------------------------------------------------------------- *)
(* Shared by all three strategies. [vtmp] is unused by [sz_unrolled], but
   included anyway: over-approximation is harmless. *)
Definition stack_zero_vars : Sv.t :=
  sv_of_list v_var
    ([:: vsaved_sp; voff; vzero; vtmp ] ++
     (if is_large then vwzero :: vflags else [::])).

End RSP.

(* The largest [stk_max] for which the unrolled strategy's highest store
   offset ([stk_max - wsize_size ws]) still fits the store's immediate:
   [sw]'s is signed 12-bit ([-2048, 2047]), [bn.sd]'s is a signed 10-bit
   immediate scaled by 32 ([-16384, 16352]). *)
Definition max_stk (ws : wsize) : Z :=
  if ws == U256 then 16384%Z else 2048%Z.

Definition stack_zeroization_cmd
  (szs : stack_zero_strategy)
  (rspn : Ident.ident)
  (lbl : label)
  (ws_align ws : wsize)
  (stk_max : Z) :
  cexec (lcmd * Sv.t) :=
  Let _ := assert ((ws == U32) || (ws == U256)) (E.error_size ws) in
  let rsp := vid rspn in
  match szs with
  | SZSloop =>
    ok (stack_zero_loop rsp lbl ws_align ws stk_max, stack_zero_vars ws)
  | SZSloopSCT =>
    Error E.error_loop_sct
  | SZSunrolled =>
    Let _ :=
      assert
        (stk_max <=? max_stk ws)%Z (E.error_range stk_max (max_stk ws) ws)
    in
    ok (stack_zero_unrolled rsp ws_align ws stk_max, stack_zero_vars ws)
  | SZSloopHW =>
    ok (stack_zero_loophw rsp ws_align ws stk_max, stack_zero_vars ws)
  end.

End STACK_ZEROIZATION.
