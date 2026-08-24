open Arch_decl
open Otbn_decl
open Otbn_instr_decl
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
  let not_implemented = hierror ~loc ~kind ~internal "not implemented: %s"

  let address_not_supported base disp off scal =
    let pp =
      Format.pp_print_option
        ~none:(fun fmt () -> Format.fprintf fmt "0")
        (fun fmt -> Format.fprintf fmt "%s")
    in
    hierror ~loc ~kind ~internal:false
      "address not supported in OTBN: [%s + %a * %a + %a]" base pp off pp scal
      pp disp
end

(* -------------------------------------------------------------------------- *)

let arch = otbn_decl
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
let x0 = "x0" (* TODO_OTBN check *)
let ra = "x1" (* TODO_OTBN check *)
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

(* TODO_OTBN: Some instructions need signedness and some don't accept it.
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

(* TODO_OTBN: Remove. *)
let indirect_args pp =
  match pp.pp_aop_name with
  | "BN.LID" | "BN.SID" -> List.tl pp.pp_aop_args
  | _ -> pp.pp_aop_args

(* TODO_OTBN: Is this generic? *)
let pp_otbn_op pp =
  let pp_args = indirect_args pp in
  let name =
    Format.sprintf "%s%s"
      (pp.pp_aop_name |> String.lowercase)
      (pp_mnemonic_ext pp.pp_aop_ext)
  in
  let args = List.filter_map (fun (_, a) -> pp_asm_arg a) pp_args in
  (name, args)

let symbol_of_shift sh =
  match sh with Otbn_options.RS_left -> "<<" | RS_right -> ">>"

(* TODO_OTBN: This is ugly. *)
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
  | Otbn_instr_decl.BN_basic_shift (_, _, sh) -> pp_shift sh
  | BN_RSHI -> pp_shift Otbn_options.RS_right
  | BN_SHV (_, sh) -> pp_shift sh
  | _ -> args

let string_of_bn_flag_group fg =
  match fg with Otbn_options.FG0 -> "FG0" | FG1 -> "FG1"

let pp_args_flag_group op args =
  let sfg =
    match op with
    | Otbn_instr_decl.BN_basic (_, fg)
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
    let s = match hwsel with Otbn_options.WB_upper -> "U" | WB_lower -> "L" in
    Format.sprintf "%s.%s" wr s
  in
  match op with
  | Otbn_instr_decl.BN_MULQACC | BN_MULQACC_Z -> begin
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

let need_nop_i = function
  | LABEL _ | REPEATLOOP _ | JMP _ | JMPI _ | Jcc _ | JAL _ | CALL _
  | CALL_HWCS _ | RET_HWCS | POPPC | SysCall _ ->
      true
  | ALIGN | STORELABEL _ | Declassify_val _ | Declassify_mem _ | AsmOp _ ->
      false

let need_nop c = try need_nop_i (List.last c).asmi_i with Failure _ -> true
let notlbl = function Label _ -> false | _ -> true

module OTBNTarget :
  AsmTarget
    with type reg = register
     and type regx = Arch_utils.empty
     and type xreg = wide_register
     and type rflag = Otbn_decl.rflag
     and type cond = condition
     and type asm_op = otbn_op = struct
  type reg = register
  type regx = Arch_utils.empty
  type xreg = wide_register
  type rflag = Otbn_decl.rflag
  type cond = condition
  type asm_op = otbn_op

  let headers = []

  (* OTBN has a Harvard architecture: instructions live in IMEM and data in
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

  (* TODO_OTBN check *)
  let function_header = []

  (* TODO_OTBN check *)
  let function_tail = [ Instr ("ret", []) ]

  (* [ret] is syntactic sugar for [JALR x0 ra 0 ]. *)
  let ret r =
    if String.equal r ra then Instr ("ret", [])
    else Instr ("jalr", [ x0; r; pp_imm Z.zero ])

  let pp_instr_r fn pp_cmd i =
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
    | REPEATLOOP (count, c) ->
        let count, name =
          match count with
          | Datatypes.Coq_inl v -> (pp_register v, "loop")
          | Datatypes.Coq_inr cz -> (Z.to_string (Conv.z_of_cz cz), "loopi")
        in
        let c' = pp_cmd fn c in
        let c' = if need_nop c then c' @ [ Instr ("nop", []) ] else c' in
        let num_c' = Format.sprintf "%i" (List.count_matching notlbl c') in
        Instr (name, [ count; num_c' ]) :: c'
    | POPPC -> E.invalid_poppc ()
    | CALL_HWCS lbl -> [ Instr ("jal", [ ra; pp_remote_label lbl ]) ]
    | RET_HWCS -> [ Instr ("ret", []) ]
    | SysCall op -> [ Instr ("jal", [ ra; pp_syscall op ]) ]
    | Declassify_val (lty, a) ->
        declassify_val (fun _lty a -> Option.default "" (pp_asm_arg a)) lty a
    | Declassify_mem (len, a) -> declassify_mem arch len a
    | AsmOp (op, args) ->
        let id = instr_desc otbn_decl otbn_op_decl (None, op) in
        let pp = id.id_pp_asm args in
        let name, args = pp_otbn_op pp in
        let args = pp_args op args in
        [ Instr (name, args) ]
end

module OTBNPrinter = AsmTargetBuilder.Make (OTBNTarget)

let print_prog fmt prog =
  PrintASM.pp_asm ~comment_prefix:"#" fmt (OTBNPrinter.asm_of_prog prog)
