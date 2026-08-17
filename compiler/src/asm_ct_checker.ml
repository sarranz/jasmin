open Arch_decl

module SS = Set.Make (String)
module SM = Map.Make (String)
module LM = Map.Make (struct
  type t = Label.label
  let compare = Stdlib.compare
end)

type level = Public | Poly of SS.t | Secret

let lmax (a : level) (b : level) : level =
  match (a, b) with
  | Secret, _ | _, Secret -> Secret
  | Public, l | l, Public -> l
  | Poly s1, Poly s2 -> Poly (SS.union s1 s2)

let lmaxs : level list -> level = List.fold_left lmax Public

let lle (a : level) (b : level) : bool =
  match (a, b) with
  | Public, _ | _, Secret -> true
  | Poly s1, Poly s2 -> SS.subset s1 s2
  | _ -> false


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
  | Secret -> raise (Leak (Printf.sprintf "secret value in %s leaked" x))
  | Poly s -> { env with pub = SS.union s env.pub }

let joinl (pub : SS.t) (a : level) (b : level) : level =
  lmax (norm pub a) (norm pub b)

let join (e1 : env) (e2 : env) : env =
  let pub = SS.union e1.pub e2.pub in
  let v =
    SM.merge
      (fun _ a b ->
        match (a, b) with
        | None, l | l, None -> l
        | Some a, Some b -> Some (joinl pub a b))
      e1.v e2.v
  in
  { v; pub }

let le (e1 : env) (e2 : env) : bool =
  let held (e : env) (x : string) : level =
    Option.value ~default:Public (SM.find_opt x e.v)
  in
  SS.subset e1.pub e2.pub
  && SM.for_all (fun x l -> lle (norm e1.pub l) (norm e2.pub (held e2 x))) e1.v

let equiv (e1 : env) (e2 : env) : bool = le e1 e2 && le e2 e1

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

module Asm_ct_checker (Arch : Arch_full.Arch) = struct

  let arch = Arch.asm_e._asm
  let arch_decl = arch._arch_decl

  let reg_name r = arch_decl.toS_r.to_string r
  let regx_name r = arch_decl.toS_rx.to_string r
  let xreg_name r = arch_decl.toS_x.to_string r
  let flag_name f = arch_decl.toS_f.to_string f

  let condt_slots c : string list =
    List.map (fun (v : Prog.var) -> v.CoreIdent.v_name) (Arch.vars_of_condt c)

  let arch_slots : string list =
    List.map reg_name (Arch_decl.registers arch_decl)
    @ List.map regx_name (Arch_decl.registerxs arch_decl)
    @ List.map xreg_name (Arch_decl.xregisters arch_decl)
    @ List.map flag_name (Arch_decl.rflags arch_decl)

  exception Unsupported

  let get_mem_annotation intr : string list =
    Option.value ~default:[] (Annot.has_array_annot (snd intr.asmi_ii))

  let regs_of_address : _ Arch_decl.address -> string list = function
    | Areg { ad_base; ad_offset; _ } ->
        List.filter_map (Option.map reg_name) [ ad_base; ad_offset ]
    | Arip _ -> []

  (* Get the slots the operand descriptors (id_in or id_out) read / write to.
    Addresses must be public, so the env is passed to record that requirement. *)
  let process_op_descs args mem_annotation env ods : env * string list =
    List.fold_left
      (fun (env, acc) od ->
        match od with
        | ADImplicit (IArflag f) -> (env, flag_name f :: acc)
        | ADImplicit (IAreg r) -> (env, reg_name r :: acc)
        | ADExplicit (kind, n, _) -> (
            match List.nth_opt args (Conv.int_of_nat n) with
            | Some (Reg r) -> (env, reg_name r :: acc)
            | Some (Regx r) -> (env, regx_name r :: acc)
            | Some (XReg r) -> (env, xreg_name r :: acc)
            | Some (Addr a) -> (
                let addr_regs = regs_of_address a in
                match kind with
                | AK_compute -> (env, addr_regs @ acc)
                | AK_mem _ ->
                    let env = List.fold_left use_public env addr_regs in
                    if mem_annotation = [] then (env, unknown_mem_slot :: acc)
                    else (env, mem_annotation @ acc))
            | Some (Condt c) -> (env, condt_slots c @ acc)
            | Some (Imm _) | None -> (env, acc)))
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

  let ty_asmop env intr op args : env =
    let op_desc = arch._asm_op_decl.instr_desc_op op in
    let mem_annotation = get_mem_annotation intr in
    let env_slots = process_op_descs args mem_annotation in
    let env, in_slots = env_slots env op_desc.id_in in
    let env, out_slots = env_slots env op_desc.id_out in
    let level = lmaxs (List.map (getl env) in_slots) in
    let strong = mem_write_size args op_desc = Some (List.length mem_annotation) in
    List.fold_left
      (fun env x -> write env ~strong mem_annotation x level)
      env out_slots

  let step fn_name labels ~exit env (i : int) intr : (int * env) list =
    let target lbl = LM.find lbl labels in
    match intr.asmi_i with
    | ALIGN | LABEL _ -> [ (i + 1, env) ]
    | AsmOp (op, args) -> [ (i + 1, ty_asmop env intr op args) ]
    | JMP (fn, lbl) ->
        if fn.CoreIdent.fn_name <> fn_name then raise Unsupported
        else [ (target lbl, env) ]
    | Jcc (lbl, c) ->
        let env = List.fold_left use_public env (condt_slots c) in
        [ (target lbl, env); (i + 1, env) ]
    | POPPC -> [ (exit, env) ]
    | _ -> raise Unsupported

  let label_map body : int LM.t =
    let m = ref LM.empty in
    Array.iteri
      (fun i intr ->
        match intr.asmi_i with
        | LABEL (_, lbl) -> m := LM.add lbl i !m
        | _ -> ())
      body;
    !m

  let ty_body fn_name body (pre : env) : SS.t * env option =
    let labels = label_map body in
    let exit = Array.length body in
    let envs : env option array = Array.make (exit + 1) None in
    let changed = ref true in
    let flow (j, env) =
      let new_env = match envs.(j) with None -> env | Some old -> join old env in
      if not (Option.equal equiv envs.(j) (Some new_env)) then begin
        envs.(j) <- Some new_env;
        changed := true
      end
    in
    flow (0, pre);
    while !changed do
      changed := false;
      Array.iteri
        (fun i intr ->
          match envs.(i) with
          | None -> ()
          | Some env -> List.iter flow (step fn_name labels ~exit env i intr))
        body
    done;
    let pub =
      Array.fold_left
        (fun pub -> function Some (e : env) -> SS.union pub e.pub | None -> pub)
        SS.empty envs
    in
    (pub, envs.(exit))

  let ty_fundef analysis (f_name, f_def) =
    let name = f_name.CoreIdent.fn_name in
    let mem_slots =
      List.concat_map get_mem_annotation f_def.asm_fd_body
      |> List.sort_uniq String.compare
    in
    let slots = arch_slots @ mem_slots in
    let pre =
      List.fold_left
        (fun env x -> setl env x (fresh analysis (x ^ "_")))
        { v = SM.empty; pub = SS.empty } slots
    in
    let pre = setl pre unknown_mem_slot Secret in
    let body = Array.of_list f_def.asm_fd_body in
    match ty_body name body pre with
    | _, None -> Error "no path returns"
    | pub, Some post ->
        let pre = { pre with pub } in
        let post = { post with pub } in
        let f_sig = { slots; pre; post } in
        Hashtbl.replace analysis.sigs name f_sig;
        Ok f_sig
    | exception Unsupported -> Error "skipped"
    | exception Leak msg -> Error ("leak: " ^ msg)
    | exception Unknown_slot x -> Error ("unknown slot: " ^ x)


  let signatures prog =
    let an : analysis = create () in
    List.map
      (fun (f_name, f_def) ->
        (f_name.CoreIdent.fn_name, ty_fundef an (f_name, f_def)))
      prog.asm_funcs

  let chk
      (ap :
        (Arch.reg, Arch.regx, Arch.xreg, Arch.rflag, Arch.cond, Arch.asm_op) Arch_decl.asm_prog)
      : unit =
    pp_signatures Format.err_formatter (signatures ap)
end
