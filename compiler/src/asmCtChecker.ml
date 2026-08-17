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

let norm (pub : SS.t) (lvl : level) : level =
  match lvl with
  | Poly s ->
      let free = SS.diff s pub in
      if SS.is_empty free then Public else Poly free
  | Public | Secret -> lvl

exception Leak of string
exception Unknown_slot of string

(* Slot standing for memory accesses that carry no array annotation: we
   dont not know which region is accessed, but we interpret it as disjoint from
   every other region. *)
let unknown_mem_slot = "%unknown_mem"

type env = { v : level SM.t; pub : SS.t }

let getl (env : env) (x : string) : level =
  match SM.find_opt x env.v with
  | Some l -> norm env.pub l
  | None -> raise (Unknown_slot x)

let setl (env : env) (x : string) (l : level) : env =
  { env with v = SM.add x (norm env.pub l) env.v }

let use_public (env : env) (x : string) : env =
  match getl env x with
  | Public -> env
  | Secret -> raise (Leak (Printf.sprintf "secret value in %s used as an address" x))
  | Poly s -> { env with pub = SS.union s env.pub }


let write (env : env) ~(strong : bool) (mem : string list) (x : string)
    (l : level) : env =
  if x = unknown_mem_slot then env
  else if strong || not (List.mem x mem) then setl env x l
  else setl env x (lmax (getl env x) l)

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
  Format.fprintf fmt "%-5s %-12s -> %s" slot
    (string_of_level (getl s.pre slot))
    (string_of_level (getl s.post slot))

let pp_signature fmt ((name : string), (s : signature)) =
  Format.fprintf fmt "@[<v2>%s:@,%a@]" name
    (Utils.pp_list "@," (pp_slot s))
    s.slots

let pp_result fmt (name, r) =
  match r with
  | Ok s -> pp_signature fmt (name, s)
  | Error msg -> Format.fprintf fmt "%s: %s" name msg

let pp_signatures fmt results =
  Format.fprintf fmt "@[<v>==== asmCtChecker: signatures ====@,%a@,%s@]@."
    (Utils.pp_list "@," pp_result)
    results "==== end signatures ===="

(* ==================================================================== *)

let reg_name arch r = arch._arch_decl.toS_r.to_string r
let regx_name arch r = arch._arch_decl.toS_rx.to_string r
let xreg_name arch r = arch._arch_decl.toS_x.to_string r
let flag_name arch f = arch._arch_decl.toS_f.to_string f

let slots_of arch : string list =
  List.map (reg_name arch) (Arch_decl.registers arch._arch_decl)
  @ List.map (regx_name arch) (Arch_decl.registerxs arch._arch_decl)
  @ List.map (xreg_name arch) (Arch_decl.xregisters arch._arch_decl)
  @ List.map (flag_name arch) (Arch_decl.rflags arch._arch_decl)

exception Unsupported

let get_mem_annotation intr : string list =
  Option.value ~default:[] (Annot.has_array_annot (snd intr.asmi_ii))

let regs_of_address arch : _ Arch_decl.address -> string list = function
  | Areg { ad_base; ad_offset; _ } ->
      List.filter_map (Option.map (reg_name arch)) [ ad_base; ad_offset ]
  | Arip _ -> []

(* Get the slots the operand descriptors (id_in or id_out) read / write to.
  Addresses must be public, so the env is passed to record that requirement. *)
let process_op_descs arch args mem_annotation env ods : env * string list =
  List.fold_left
    (fun (env, acc) od ->
      match od with
      | ADImplicit (IArflag f) -> (env, flag_name arch f :: acc)
      | ADImplicit (IAreg r) -> (env, reg_name arch r :: acc)
      | ADExplicit (kind, n, _) -> (
          match List.nth_opt args (Conv.int_of_nat n) with
          | Some (Reg r) -> (env, reg_name arch r :: acc)
          | Some (Regx r) -> (env, regx_name arch r :: acc)
          | Some (XReg r) -> (env, xreg_name arch r :: acc)
          | Some (Addr a) -> (
              let addr_regs = regs_of_address arch a in
              match kind with
              | AK_compute -> (env, addr_regs @ acc)
              | AK_mem _ ->
                  let env = List.fold_left use_public env addr_regs in
                  if mem_annotation = [] then (env, unknown_mem_slot :: acc)
                  else (env, mem_annotation @ acc))
          | Some (Imm _) | None -> (env, acc)
          | Some (Condt _) -> raise Unsupported))
    (env, []) ods

let mem_write_size args op_desc : int option =
  List.combine op_desc.id_out op_desc.id_tout
  |> List.find_map (fun (od, ty) ->
         match (od, ty) with
         | ADExplicit (AK_mem _, n, _), Type.Coq_lword ws -> (
             match List.nth_opt args (Conv.int_of_nat n) with
             | Some (Addr _) -> Some (Prog.size_of_ws ws)
             | _ -> None)
         | _ -> None)

let ty_instr arch env intr : env =
  match intr.asmi_i with
  | ALIGN -> env
  | AsmOp (op, args) ->
      let op_desc = arch._asm_op_decl.instr_desc_op op in
      let mem_annotation = get_mem_annotation intr in
      let env_slots = process_op_descs arch args mem_annotation in
      let env, in_slots = env_slots env op_desc.id_in in
      let env, out_slots = env_slots env op_desc.id_out in
      let level = lmaxs (List.map (getl env) in_slots) in
      let strong =
        mem_write_size args op_desc = Some (List.length mem_annotation)
      in
      List.fold_left
        (fun env x -> write env ~strong mem_annotation x level)
        env out_slots
  | _ -> raise Unsupported

let ty_fundef arch analysis (f_name, f_def) =
  let name = f_name.CoreIdent.fn_name in
  let mem_slots =
    List.concat_map get_mem_annotation f_def.asm_fd_body
    |> List.sort_uniq String.compare
  in
  let slots = slots_of arch @ mem_slots in
  let pre =
    List.fold_left
      (fun env x -> setl env x (fresh analysis (x ^ "_")))
      { v = SM.empty; pub = SS.empty } slots
  in
  let pre = setl pre unknown_mem_slot Secret in
  match List.fold_left (ty_instr arch) pre f_def.asm_fd_body with
  | post ->
      let pre = { pre with pub = post.pub } in
      let f_sig = { slots; pre; post } in
      Hashtbl.replace analysis.sigs name f_sig;
      Ok f_sig
  | exception Unsupported -> Error "skipped"
  | exception Leak msg -> Error ("leak: " ^ msg)
  | exception Unknown_slot x -> Error ("unknown slot: " ^ x)


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
