open Arch_decl

module SS = Set.Make (String)
module SM = Map.Make (String)

type level = Public | Poly of SS.t | Secret

let lmax (a : level) (b : level) : level =
  match (a, b) with
  | Secret, _ | _, Secret -> Secret
  | Public, l | l, Public -> l
  | Poly s1, Poly s2 -> Poly (SS.union s1 s2)

let lmaxs : level list -> level = List.fold_left lmax Public

type env = level SM.t

let getl (env : env) (x : string) : level =
  Option.value ~default:Public (SM.find_opt x env)

let setl (env : env) (x : string) (l : level) : env = SM.add x l env

type signature = {
  slots : string list;
  pre : env;
  post : env;
}

type analysis = {
  sigs : (string, signature) Hashtbl.t;
  mutable fresh_var_counter : int;
}

let create () : analysis = { sigs = Hashtbl.create 17; fresh_var_counter = 0 }

let fresh (an : analysis) (prefix : string) : level =
  an.fresh_var_counter <- an.fresh_var_counter + 1;
  Poly (SS.singleton (Printf.sprintf "%s%d" prefix an.fresh_var_counter))

(* ============================== pp ====================================== *)

let string_of_level : level -> string = function
  | Public -> "public"
  | Secret -> "secret"
  | Poly s -> "poly{" ^ String.concat "," (SS.elements s) ^ "}"

let pp_slot (s : signature) fmt (slot : string) =
  Format.fprintf fmt "%-4s %-12s -> %s" slot
    (string_of_level (getl s.pre slot))
    (string_of_level (getl s.post slot))

let pp_signature fmt ((name : string), (s : signature)) =
  Format.fprintf fmt "@[<v2>%s:@,%a@]" name
    (Utils.pp_list "@," (pp_slot s))
    s.slots

let pp_result fmt (name, r) =
  match r with
  | Some s -> pp_signature fmt (name, s)
  | None -> Format.fprintf fmt "%s: skipped" name

let pp_signatures fmt results =
  Format.fprintf fmt "@[<v>==== asmCtChecker: signatures ====@,%a@,%s@]@."
    (Utils.pp_list "@," pp_result)
    results "==== end signatures ===="

(* ==================================================================== *)

(* registers and flags (as strings) from the analyzed architecture *)
let slots_of arch : string list =
  List.map arch._arch_decl.toS_r.to_string (Arch_decl.registers arch._arch_decl)
  @ List.map arch._arch_decl.toS_f.to_string (Arch_decl.rflags arch._arch_decl)

exception Unsupported

(* get the string representation from an operand descriptor *)
let slot_of_ad arch args arg_desc : string option =
  match arg_desc with
  | ADImplicit (IArflag f) -> Some (arch._arch_decl.toS_f.to_string f)
  | ADImplicit (IAreg r) -> Some (arch._arch_decl.toS_r.to_string r)
  | ADExplicit (_, n, _) -> (
      match List.nth_opt args (Conv.int_of_nat n) with
      | Some (Reg r) -> Some (arch._arch_decl.toS_r.to_string r)
      | Some (Imm _) | None -> None
      | _ -> raise Unsupported)

let ty_instr arch env intr : env =
  match intr.asmi_i with
  | ALIGN -> env
  | AsmOp (op, args) ->
      let op_desc = arch._asm_op_decl.instr_desc_op op in
      let slots args_desc = List.filter_map (slot_of_ad arch args) args_desc in
      let level = lmaxs (List.map (getl env) (slots op_desc.id_in)) in
      List.fold_left (fun env x -> setl env x level) env (slots op_desc.id_out)
  | _ -> raise Unsupported

let ty_fundef arch analysis (f_name, f_def) =
  let name = f_name.CoreIdent.fn_name in
  let slots = slots_of arch in
  let pre =
    List.fold_left
      (fun env x -> setl env x (fresh analysis (x ^ "_")))
      SM.empty slots
  in
  match List.fold_left (ty_instr arch) pre f_def.asm_fd_body with
  | post ->
      let f_sig = { slots; pre; post } in
      Hashtbl.replace analysis.sigs name f_sig;
      Some f_sig
  | exception Unsupported -> None


let signatures arch prog =
  let an : analysis = create () in
  List.map
    (fun (f_name, f_def) ->
      (f_name.CoreIdent.fn_name, ty_fundef arch an (f_name, f_def)))
    prog.asm_funcs

let chk (a : ('reg, 'regx, 'xreg, 'rflag, 'cond, 'asm_op) Arch_decl.asm)
    (ap : ('reg, 'regx, 'xreg, 'rflag, 'cond, 'asm_op) Arch_decl.asm_prog) :
    unit =
  pp_signatures Format.err_formatter (signatures a ap)
