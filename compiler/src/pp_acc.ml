open Arch_decl
open Acc_decl
open Acc_instr_decl
open AsmTargetBuilder
open Asm_utils
open Utils
open PrintASM

(* -------------------------------------------------------------------------- *)
(* Errors. *)

module E = struct
  let loc = Lnone
  let kind = "pretty printing"
  let internal = true
  let err s = fun () -> hierror ~loc ~kind ~internal s
  let invalid_address = err "invalid address"
  let invalid_jmpi = err "invalid JMPI"
  let invalid_jcc = err "invalid Jcc"
  let invalid_jal = err "invalid JAL"
  let invalid_call = err "invalid CALL"
  let invalid_poppc = err "invalid POPPC"
  let invalid_args = err "invalid arguments"
  let pp_error = err "found PP_error"
  let invalid_pp_aop_ext = err "invalid pp_aop_ext"
  let malformed_loop_markers =
    err "malformed ACC hardware-loop begin/end markers"
  let not_implemented = hierror ~loc ~kind ~internal "not implemented: %s"

  let address_not_supported base disp off scal =
    let pp =
      Format.pp_print_option
        ~none:(fun fmt () -> Format.fprintf fmt "0")
        (fun fmt -> Format.fprintf fmt "%s")
    in
    hierror ~loc ~kind ~internal:false
      "address not supported in ACC: [%s + %a * %a + %a]" base pp off pp scal
      pp disp
end

(* -------------------------------------------------------------------------- *)

let arch = acc_decl
let imm_pre = ""

let pp_reg_address_aux base disp off scal =
  match (disp, off, scal) with
  | None, None, None -> Format.sprintf "0(%s)" base
  | Some disp, None, None -> Format.sprintf "%s(%s)" disp base
  | _, _, _ -> E.address_not_supported base disp off scal

(* -------------------------------------------------------------------------- *)

let pp_label = string_of_label

let hash_to_string_core (to_string : 'a -> string) =
  let tbl = Hashtbl.create 17 in
  fun r ->
    try Hashtbl.find tbl r
    with Not_found ->
      let s = to_string r in
      Hashtbl.add tbl r s;
      s

let hash_to_string to_string = hash_to_string_core (fun x -> to_string x)
let x0 = "x0" (* TODO_ACC check *)
let ra = "x1" (* TODO_ACC check *)
let pp_register = hash_to_string arch.toS_r.to_string
let pp_oregister = function Some r -> pp_register r | None -> x0
let pp_xregister = hash_to_string arch.toS_x.to_string
let pp_imm imm = Format.sprintf "%s%s" imm_pre (Z.to_string imm)

let pp_flag f =
  match f with
  | CF0 -> "FG0.C"
  | MF0 -> "FG0.M"
  | LF0 -> "FG0.L"
  | ZF0 -> "FG0.Z"
  | CF1 -> "FG1.C"
  | MF1 -> "FG1.M"
  | LF1 -> "FG1.L"
  | ZF1 -> "FG1.Z"

let pp_reg_address addr =
  match addr.ad_base with
  | None -> E.invalid_address ()
  | Some r ->
      let base = pp_register r in
      let disp = Conv.z_of_word (arch_pd arch) addr.ad_disp in
      let disp =
        if Z.equal disp Z.zero then None else Some (Z.to_string disp)
      in
      let off = Option.map pp_register addr.ad_offset in
      let scal = Conv.z_of_nat addr.ad_scale in
      let scal =
        if Z.equal scal Z.zero then None else Some (Z.to_string scal)
      in
      pp_reg_address_aux base disp off scal

let pp_address addr =
  match addr with Areg ra -> pp_reg_address ra | Arip r -> pp_rip_address r

(* TODO_ACC: Some instructions need signedness and some don't accept it.
   Currently the only ones that don't accept signedness are the ones that take
   [U8]s, so this is a hack. *)
let pp_asm_arg (arg : (_, Arch_utils.empty, _, _, _) asm_arg) =
  match arg with
  | Condt (BNcond f) -> Some (pp_flag f)
  | Condt (RVcond _) -> None
  | Imm (ws, w) ->
      let read =
        if ws = Wsize.U8 then Conv.z_unsigned_of_word else Conv.z_of_word
      in
      Some (pp_imm (read ws w))
  | Reg r -> Some (pp_register r)
  | Regx _ -> .
  | Addr addr -> Some (pp_address addr)
  | XReg r -> Some (pp_xregister r)

(* -------------------------------------------------------------------------- *)

let pp_is_eq is_eq = if is_eq then "eq" else "ne"

let pp_mnemonic_ext ext =
  match ext with
  | PP_error -> E.pp_error ()
  | PP_name -> ""
  | _ -> E.invalid_pp_aop_ext ()

(* TODO_ACC: Remove. *)
let indirect_args pp =
  match pp.pp_aop_name with
  | "BN.LID" | "BN.SID" -> List.tl pp.pp_aop_args
  | _ -> pp.pp_aop_args

(* [MOD0W]/[MOD1W] and their [zero] variants are syntax sugar for a CSR
   write that discards the read result (destination [x0]); see
   [Acc_instr_decl.desc_MOD_word32W]/[desc_MOD_word32Wzero]. This translation
   is not verified. *)
let is_MODnW = function
  | MOD0W | MOD0Wzero | MOD1W | MOD1Wzero -> true
  | _ -> false

let dst_of_MODnW = function
  | MOD0W | MOD0Wzero -> "mod0"
  | MOD1W | MOD1Wzero -> "mod1"
  | _ -> E.invalid_args ()

let src_of_MODnW op pp =
  match (op, pp.pp_aop_args) with
  | (MOD0W | MOD1W), [ (_, Reg r) ] -> pp_register r
  | (MOD0Wzero | MOD1Wzero), [] -> x0
  | _ -> E.invalid_args ()

let pp_acc_op op pp =
  if op = RV32 NEG then
    match pp.pp_aop_args with
    | [ (_, Reg r1); (_, Reg r2) ] ->
        ("sub", [ pp_register r1; x0; pp_register r2 ])
    | _ -> E.invalid_args ()
  else if is_MODnW op then
    ("csrrw", [ x0; dst_of_MODnW op; src_of_MODnW op pp ])
  else
    let pp_args = indirect_args pp in
    let name =
      Format.sprintf "%s%s"
        (pp.pp_aop_name |> String.lowercase)
        (pp_mnemonic_ext pp.pp_aop_ext)
    in
    let args = List.filter_map (fun (_, a) -> pp_asm_arg a) pp_args in
    (name, args)

let symbol_of_shift sh =
  match sh with Acc_options.RS_left -> "<<" | RS_right -> ">>"

(* TODO_ACC: This is ugly. *)
(* Return the list of arguments updated with shift notations.
   We need to combine register shifts with the second operand and the shift
   operator. *)
let pp_args_shift op args =
  let pp_shift sh =
    match List.rev args with
    | sham :: r :: rest ->
        let r' = Format.sprintf "%s %s %s" r (symbol_of_shift sh) sham in
        List.rev (r' :: rest)
    | _ -> E.invalid_args ()
  in
  match op with
  | Acc_instr_decl.BN_basic_shift (_, _, sh) -> pp_shift sh
  | BN_RSHI -> pp_shift Acc_options.RS_right
  | BN_SHV (_, sh) -> pp_shift sh
  | _ -> args

let string_of_bn_flag_group fg =
  match fg with Acc_options.FG0 -> "FG0" | FG1 -> "FG1"

let pp_args_flag_group op args =
  let sfg =
    match op with
    | Acc_instr_decl.BN_basic (_, fg)
    | BN_basic_shift (_, fg, _)
    | BN_ADDI fg
    | BN_SUBI fg
    | BN_MULQACC_WO fg
    | BN_MULQACC_WO_Z fg
    | BN_MULQACC_SO (fg, _)
    | BN_MULQACC_SO_Z (fg, _) ->
        [ string_of_bn_flag_group fg ]
    | _ -> []
  in
  args @ sfg

let pp_args_mulqacc_selectors op args =
  let pp_qwsel = Format.sprintf "%s.%s" in
  let pp_hwsel wr hwsel =
    let s = match hwsel with Acc_options.WB_upper -> "U" | WB_lower -> "L" in
    Format.sprintf "%s.%s" wr s
  in
  match op with
  | Acc_instr_decl.BN_MULQACC | BN_MULQACC_Z -> begin
      match args with
      | wrs1 :: qwsel1 :: wrs2 :: qwsel2 :: rest ->
          pp_qwsel wrs1 qwsel1 :: pp_qwsel wrs2 qwsel2 :: rest
      | _ -> E.invalid_args ()
    end
  | BN_MULQACC_WO _ | BN_MULQACC_WO_Z _ -> begin
      match args with
      | wrd :: wrs1 :: qwsel1 :: wrs2 :: qwsel2 :: rest ->
          wrd :: pp_qwsel wrs1 qwsel1 :: pp_qwsel wrs2 qwsel2 :: rest
      | _ -> E.invalid_args ()
    end
  | BN_MULQACC_SO (_, hwsel) | BN_MULQACC_SO_Z (_, hwsel) -> begin
      match args with
      | wrd :: wrs1 :: qwsel1 :: wrs2 :: qwsel2 :: rest ->
          pp_hwsel wrd hwsel :: pp_qwsel wrs1 qwsel1 :: pp_qwsel wrs2 qwsel2
          :: rest
      | _ -> E.invalid_args ()
    end
  | _ -> args

let pp_args op args =
  pp_args_shift op args |> pp_args_flag_group op |> pp_args_mulqacc_selectors op

(* -------------------------------------------------------------------------- *)
(* Hardware-loop body-size counting and end-of-body [nop] elision (Stage 9).

   [BEGINLOOP]/[ENDLOOP] are printed, below in [pp_instr_r], as a
   placeholder-carrying [loop]/[loopi] instruction and a fixed-tag [Comment]
   marker. [print_prog] (at the bottom of this file) walks the flat,
   already-printed [asm_element list] once, with a stack of open loops, to
   patch each placeholder with the real machine-instruction count of its body
   and to resolve each marker into either [Instr ("nop", [])] or nothing. *)

(* A comment string that nothing else in this printer ever produces: it marks
   the position of an [ENDLOOP], to be resolved by [acc_resolve_loops] below
   (replaced by a [nop], or removed) once the whole body it closes has been
   walked. Never reaches [PrintASM.pp_asm]: always consumed first. *)
let acc_endloop_marker = "#ACC_ENDLOOP_MARKER#"

(* The body-size argument of a not-yet-resolved [loop]/[loopi] instruction;
   patched in place by [acc_resolve_loops] once the body's real
   machine-instruction count is known. *)
let acc_loop_size_placeholder = "?"

(* Instructions that cannot be the last instruction of a hardware-loop body
   (the hardware only detects loop-end after a straight-line instruction).
   [loop]/[loopi] themselves are included: nested loops must not share their
   last instruction. [ecall] is never actually emitted by this printer today
   (syscalls print as [jal], see [pp_instr_r] below), kept for robustness. *)
let acc_control_flow_names =
  [ "beq"; "bne"; "jal"; "jalr"; "ret"; "loop"; "loopi"; "ecall" ]

(* Mirrors [hw/ip/acc/util/acc_as.py]'s [expand_li]: [li] assembles to one
   [addi] if its immediate fits 12 signed bits, or one bare [lui] if its low
   12 bits are zero, and to two instructions otherwise. No [li] is emitted by
   this printer today (immediate loads only ever go through [la]), but the
   rule is implemented anyway in case that changes; a parse failure is
   treated conservatively (2 instructions) rather than crashing. *)
let acc_li_instr_count imm_str =
  try
    let imm = Z.of_string imm_str in
    if Z.geq imm (Z.of_int (-2048)) && Z.lt imm (Z.of_int 2048) then 1
    else if Z.equal (Z.logand imm (Z.of_int 0xFFF)) Z.zero then 1
    else 2
  with _ -> 2

(* What a printed [asm_element] leaves behind as "the last thing seen so far"
   in an open loop body, for the elision rule below. *)
type acc_loop_kind =
  | ALK_label (* a label, e.g. an if/else merge point *)
  | ALK_plain (* an ordinary, non-control-flow instruction *)
  | ALK_control (* a control-flow instruction, or a resolved inner loop *)

(* The classification of a single printed element: how much it counts
   towards the body size(s) of every loop currently open around it, and
   what it leaves behind (nothing, for [Dwarf]/[Comment]/[Header]/[Bytes],
   which are transparent to the elision rule). *)
type acc_elt_class = ACC_transparent | ACC_significant of int * acc_loop_kind

let acc_loop_classify : asm_element -> acc_elt_class = function
  | Label _ -> ACC_significant (0, ALK_label)
  | Instr ("la", _) -> ACC_significant (2, ALK_plain)
  | Instr ("li", args) ->
      let imm = match List.rev args with imm :: _ -> imm | [] -> "0" in
      ACC_significant (acc_li_instr_count imm, ALK_plain)
  | Instr (name, _) when List.mem name acc_control_flow_names ->
      ACC_significant (1, ALK_control)
  | Instr (_, _) -> ACC_significant (1, ALK_plain)
  | Dwarf _ | Comment _ | Header _ | Bytes _ ->
      (* [Header]/[Bytes] are not expected inside a loop body (a body is
         straight-line code within one function); treated as transparent
         defensively, like [Dwarf]/an ordinary [Comment]. *)
      ACC_transparent

(* One entry per currently-open loop, innermost last-pushed. *)
type acc_loop_frame = {
  alf_begin_index : int; (* position of its [loop]/[loopi] element *)
  mutable alf_count : int; (* running machine-instruction count of its body *)
  mutable alf_last_kind : acc_loop_kind option;
      (* [None]: nothing significant seen yet (an empty body so far). *)
}

(* Walk the flat, printed program once, patching every [loop]/[loopi]
   placeholder with its body's final machine-instruction count and resolving
   every [ENDLOOP] marker into a [nop] or nothing, per the elision rule:
   walking backwards from the marker over [Dwarf]/[Comment] only, a [nop] is
   required unless the first element found is a plain (non-control-flow)
   instruction inside this loop's own body. Implemented as a single forward
   pass with a mutable stack: every open frame's [alf_last_kind] is kept up
   to date with "the last significant element seen so far", which at the
   moment a marker is reached is exactly what a backward walk would find. *)
let acc_resolve_loops (elts : asm_element list) : asm_element list =
  let arr = Array.of_list (List.map (fun e -> Some e) elts) in
  let n = Array.length arr in
  let stack = ref [] in
  let touch cost kind frames =
    List.iter
      (fun f ->
        f.alf_count <- f.alf_count + cost;
        f.alf_last_kind <- Some kind)
      frames
  in
  for i = 0 to n - 1 do
    match arr.(i) with
    | None -> ()
    | Some (Comment s) when String.equal s acc_endloop_marker -> begin
        match !stack with
        | [] -> E.malformed_loop_markers ()
        | frame :: rest ->
            stack := rest;
            let need_nop =
              match frame.alf_last_kind with
              | None | Some ALK_label | Some ALK_control -> true
              | Some ALK_plain -> false
            in
            arr.(i) <- (if need_nop then Some (Instr ("nop", [])) else None);
            let final_count =
              frame.alf_count + (if need_nop then 1 else 0)
            in
            (match arr.(frame.alf_begin_index) with
            | Some (Instr (name, [ count_arg; _ ])) ->
                arr.(frame.alf_begin_index) <-
                  Some (Instr (name, [ count_arg; string_of_int final_count ]))
            | _ -> E.malformed_loop_markers ());
            (* A resolved inner loop always forces a [nop] on whichever
               enclosing loop it is the last body element of, whether or not
               it needed one itself: nested loops must not share their last
               instruction, and eliding the inner marker would otherwise
               make the outer loop's last instruction identical to the
               inner's own. *)
            touch (if need_nop then 1 else 0) ALK_control !stack
      end
    | Some (Instr (("loop" | "loopi"), _) as e) ->
        (match acc_loop_classify e with
        | ACC_significant (cost, kind) -> touch cost kind !stack
        | ACC_transparent -> ());
        stack :=
          { alf_begin_index = i; alf_count = 0; alf_last_kind = None }
          :: !stack
    | Some e -> (
        match acc_loop_classify e with
        | ACC_transparent -> ()
        | ACC_significant (cost, kind) -> touch cost kind !stack)
  done;
  Array.to_list arr |> List.filter_map identity

module ACCTarget :
  AsmTarget
    with type reg = register
     and type regx = Arch_utils.empty
     and type xreg = wide_register
     and type rflag = Acc_decl.rflag
     and type cond = condition
     and type asm_op = acc_op = struct
  type reg = register
  type regx = Arch_utils.empty
  type xreg = wide_register
  type rflag = Acc_decl.rflag
  type cond = condition
  type asm_op = acc_op

  let headers = []

  (* ACC has a Harvard architecture: instructions live in IMEM and data in
     DMEM. Globals are accessed through DMEM loads/stores (bn.ld/bn.sd, lw/sw),
     so the data segment must go into [.data] (which the ACC linker script maps
     to DMEM) rather than the default [.text] section (mapped to IMEM). *)
  let data_segment_header =
    [
      Header (".data", []);
      Instr (".p2align", [ "5" ]);
      Label global_datas_label;
    ]

  let function_directives = []

  (* TODO_ACC check *)
  let function_header = []

  (* TODO_ACC check *)
  let function_tail = [ Instr ("ret", []) ]

  (* [ret] is syntactic sugar for [JALR x0 ra 0 ]. *)
  let ret r =
    if String.equal r ra then Instr ("ret", [])
    else Instr ("jalr", [ x0; r; pp_imm Z.zero ])

  let pp_instr_r fn _pp_cmd i =
    match i with
    | ALIGN -> E.not_implemented "pp_instr ALIGN"
    | LABEL (_, lbl) -> [ Label (pp_label fn lbl) ]
    | STORELABEL (dst, lbl) ->
        [ Instr ("la", [ pp_register dst; string_of_label fn lbl ]) ]
    | JMP lbl -> [ Instr ("beq", [ x0; x0; pp_remote_label lbl ]) ]
    | JMPI arg ->
        let rlbl = match arg with Reg r -> r | _ -> E.invalid_jmpi () in
        [ ret (pp_register rlbl) ]
    | Jcc (lbl, ct) -> begin
        match ct with
        | RVcond (is_eq, r0, r1) ->
            let iname = "b" ^ pp_is_eq is_eq in
            let args = [ pp_oregister r0; pp_oregister r1; pp_label fn lbl ] in
            [ Instr (iname, args) ]
        | BNcond _ -> E.invalid_jcc ()
      end
    | JAL _ -> E.invalid_jal ()
    | CALL _ -> E.invalid_call ()
    | BEGINLOOP (count, _lbl) ->
        (* Body size is a placeholder, patched in place by [acc_resolve_loops]
           (called from [print_prog] below) once the body's real
           machine-instruction count is known. *)
        let count, name =
          match count with
          | Datatypes.Coq_inl v -> (pp_register v, "loop")
          | Datatypes.Coq_inr cz -> (Z.to_string (Conv.z_of_cz cz), "loopi")
        in
        [ Instr (name, [ count; acc_loop_size_placeholder ]) ]
    | ENDLOOP _lbl ->
        (* Resolved into a [nop] or removed entirely by [acc_resolve_loops]
           (called from [print_prog] below), depending on whether the body
           can safely end without one. *)
        [ Comment acc_endloop_marker ]
    | POPPC -> E.invalid_poppc ()
    | CALL_HWCS lbl -> [ Instr ("jal", [ ra; pp_remote_label lbl ]) ]
    | RET_HWCS -> [ Instr ("ret", []) ]
    | SysCall op -> [ Instr ("jal", [ ra; pp_syscall op ]) ]
    | Declassify_val (lty, a) ->
        declassify_val (fun _lty a -> Option.default "" (pp_asm_arg a)) lty a
    | Declassify_mem (len, a) -> declassify_mem arch len a
    | AsmOp (op, args) ->
        let id = instr_desc acc_decl acc_op_decl (None, op) in
        let pp = id.id_pp_asm args in
        let name, args = pp_acc_op op pp in
        let args = pp_args op args in
        [ Instr (name, args) ]
end

module ACCPrinter = AsmTargetBuilder.Make (ACCTarget)

let print_prog fmt prog =
  PrintASM.pp_asm ~comment_prefix:"#" fmt
    (acc_resolve_loops (ACCPrinter.asm_of_prog prog))
