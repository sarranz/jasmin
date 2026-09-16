open Arch_decl

module SS = Set.Make (String)
module SM = Map.Make (String)
module LM = Map.Make (struct
  type t = Label.label
  let compare = Stdlib.compare
end)

module Level = struct
  type t = Public | Poly of SS.t | Secret

  let join (a : t) (b : t) : t =
    match (a, b) with
    | Secret, _ | _, Secret -> Secret
    | Public, l | l, Public -> l
    | Poly s1, Poly s2 -> Poly (SS.union s1 s2)

  let join_list : t list -> t = List.fold_left join Public

  let le (a : t) (b : t) : bool =
    match (a, b) with
    | Public, _ | _, Secret -> true
    | Poly s1, Poly s2 -> SS.subset s1 s2
    | _ -> false

  let norm (public : SS.t) (level : t) : t =
    match level with
    | Poly s ->
        let free = SS.diff s public in
        if SS.is_empty free then Public else Poly free
    | Public | Secret -> level

  let subst (inst : t SM.t) (level : t) : t =
    match level with
    | Public | Secret -> level
    | Poly type_variables ->
        join_list
          (List.map
            (fun type_variable ->
              Option.value ~default:Secret (SM.find_opt type_variable inst))
            (SS.elements type_variables))
end

exception CtTypeError of (Format.formatter -> unit)

let error fmt =
  Format.kdprintf (fun msg -> raise (CtTypeError msg)) fmt

(* Slot standing for memory accesses that carry no array annotation: we
   dont know which region is accessed, but we interpret it as disjoint from
   every other region. *)
let unknown_mem_slot = "%unknown_mem"

module Env = struct
  type t = {
    levels : Level.t SM.t;
    public : SS.t;
  }

  let get (env : t) (slot : string) : Level.t =
    match SM.find_opt slot env.levels with
    | Some level -> Level.norm env.public level
    | None -> error "unknown slot: %s" slot

  let set (env : t) (slot : string) (level : Level.t) : t =
    { env with levels = SM.add slot (Level.norm env.public level) env.levels }

  let use_public (env : t) (slot : string) : t =
    match get env slot with
    | Level.Public -> env
    | Level.Secret -> error "leak: secret value in %s leaked" slot
    | Level.Poly variables ->
        { env with public = SS.union variables env.public }

  let join (first : t) (second : t) : t =
    let public = SS.union first.public second.public in
    let levels =
      SM.merge
        (fun _ first_level second_level ->
          match (first_level, second_level) with
          | None, level | level, None -> level
          | Some first_level, Some second_level ->
              Some (Level.join (Level.norm public first_level)
                      (Level.norm public second_level)))
        first.levels second.levels
    in
    { levels; public }

  let le (first : t) (second : t) : bool =
    let held (env : t) (slot : string) : Level.t =
      Option.value ~default:Level.Public (SM.find_opt slot env.levels)
    in
    SS.subset first.public second.public
    && SM.for_all
         (fun slot level ->
           Level.le (Level.norm first.public level)
             (Level.norm second.public (held second slot)))
         first.levels

  let write (env : t) ~(strong_write : bool) (memory_slots : SS.t) (slot : string)
      (level : Level.t) : t =
    if slot = unknown_mem_slot then env
    else if strong_write || not (SS.mem slot memory_slots) then set env slot level
    else set env slot (Level.join (get env slot) level)
end

type signature = {
  slots : string list;
  pre : Env.t;
  post : Env.t;
}

type memory_instantiation = string list SM.t

type analysis = {
  signatures : (string, signature) Hashtbl.t;
  mutable fresh_var_counter : int;
}

let create () : analysis =
  { signatures = Hashtbl.create 17; fresh_var_counter = 0 }

let fresh an prefix =
  an.fresh_var_counter <- an.fresh_var_counter + 1;
  Level.Poly (SS.singleton (Printf.sprintf "%s%d" prefix an.fresh_var_counter))

let string_of_level = function
  | Level.Public -> "public"
  | Level.Secret -> "secret"
  | Level.Poly s -> "poly{" ^ String.concat "," (SS.elements s) ^ "}"

let pp_slot s fmt slot =
  Format.fprintf fmt "%-5s %-12s -> %s" slot
    (string_of_level (Env.get s.pre slot))
    (string_of_level (Env.get s.post slot))

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

module Asm_ct_checker (Arch : Arch_full.Arch) = struct

  module Arch_utils = struct
    let arch = Arch.asm_e._asm
    let arch_decl = arch._arch_decl

    let reg_name r = arch_decl.toS_r.to_string r
    let regx_name r = arch_decl.toS_rx.to_string r
    let xreg_name r = arch_decl.toS_x.to_string r
    let flag_name f = arch_decl.toS_f.to_string f
    let rsp = reg_name arch_decl.ad_rsp

    let condt_slots c : string list =
      List.map (fun (v : Prog.var) -> v.CoreIdent.v_name) (Arch.vars_of_condt c)

    let arch_slots : string list =
      List.map reg_name (Arch_decl.registers arch_decl)
      @ List.map regx_name (Arch_decl.registerxs arch_decl)
      @ List.map xreg_name (Arch_decl.xregisters arch_decl)
      @ List.map flag_name (Arch_decl.rflags arch_decl)

    let arch_slots_set = SS.of_list arch_slots

    let instr_desc op = arch._asm_op_decl.instr_desc_op op

    let get_mem_annotation instr : string list =
      Option.value ~default:[] (Annot.has_array_annot (snd instr.asmi_ii))

    let get_instr_annotation instr : memory_instantiation =
      let add_instantiation m (callee, caller) =
        SM.update callee
          (fun xs -> Some (caller :: Option.value ~default:[] xs)) m
      in
      match Annot.has_instantiation_annot (snd instr.asmi_ii) with
      | None -> SM.empty
      | Some annots -> List.fold_left add_instantiation SM.empty annots

    let inst_image instr : string list =
      match instr.asmi_i with
      | CALL _ ->
          SM.fold
            (fun _ callers acc -> callers @ acc)
            (get_instr_annotation instr) []
      | _ -> []

    let regs_of_address : _ Arch_decl.address -> string list = function
      | Areg { ad_base; ad_offset; _ } ->
          List.filter_map (Option.map reg_name) [ ad_base; ad_offset ]
      | Arip _ -> []
  end

  module Instruction = struct
    let implicit_slot = function
      | IArflag f -> Arch_utils.flag_name f
      | IAreg r -> Arch_utils.reg_name r

    let process_address env mem_annotation kind address =
      let address_slots = Arch_utils.regs_of_address address in
      match kind with
      | AK_compute -> env, address_slots
      | AK_mem _ ->
          let env = List.fold_left Env.use_public env address_slots in
          if mem_annotation = [] then env, [ unknown_mem_slot ]
          else env, mem_annotation

    let process_explicit_arg args mem_annotation env kind n =
      match List.nth_opt args (Conv.int_of_nat n) with
      | Some (Reg r) -> env, [ Arch_utils.reg_name r ]
      | Some (Regx r) -> env, [ Arch_utils.regx_name r ]
      | Some (XReg r) -> env, [ Arch_utils.xreg_name r ]
      | Some (Addr address) -> process_address env mem_annotation kind address
      | Some (Condt c) -> env, Arch_utils.condt_slots c
      | Some (Imm _) | None -> env, []

    (* Get the slots the operand descriptors (id_in or id_out) read / write to.
       Addresses must be public, so the env is passed to record that requirement. *)
    let process_op_descs args mem_annotation env op_descs =
      List.fold_left
        (fun (env, slots) op_desc ->
          match op_desc with
          | ADImplicit implicit -> env, implicit_slot implicit :: slots
          | ADExplicit (kind, n, _) ->
              let env, new_slots =
                process_explicit_arg args mem_annotation env kind n
              in
              env, new_slots @ slots)
        (env, []) op_descs

    let mem_write_size args op_desc =
      List.combine op_desc.id_out op_desc.id_tout
      |> List.find_map (fun (od, ty) ->
             match (od, ty) with
             | ADExplicit (AK_mem _, n, _), Type.Coq_lword ws -> (
                 match List.nth_opt args (Conv.int_of_nat n) with
                 | Some (Addr _) -> Some (Prog.size_of_ws ws)
                 | _ -> None)
             | _ -> None)

    let ty_asmop env instr op args =
      let op_desc = Arch_utils.instr_desc op in
      let mem_annotation = Arch_utils.get_mem_annotation instr in
      let memory_slots = SS.of_list mem_annotation in
      let env_slots = process_op_descs args mem_annotation in
      let env, in_slots = env_slots env op_desc.id_in in
      let env, out_slots = env_slots env op_desc.id_out in
      let level = Level.join_list (List.map (Env.get env) in_slots) in
      let strong_write =
        mem_write_size args op_desc = Some (List.length mem_annotation)
      in
      List.fold_left
        (fun env x -> Env.write env ~strong_write memory_slots x level)
        env out_slots

    let step fn_name labels ~exit env i instr signatures call_env =
      let target lbl = LM.find lbl labels in
      match instr.asmi_i with
      | ALIGN | LABEL _ -> [ (i + 1, env) ]
      | AsmOp (op, args) ->
          [ (i + 1, ty_asmop env instr op args) ]
      | JMP (fn, lbl) ->
          if fn.CoreIdent.fn_name <> fn_name then
            error "jump to another function is not supported"
          else [ (target lbl, env) ]
      | Jcc (lbl, c) ->
          let env =
            List.fold_left Env.use_public env (Arch_utils.condt_slots c)
          in
          [ (target lbl, env); (i + 1, env) ]
      | POPPC -> [ (exit, env) ]
      | CALL (fn, _) -> (
          match Hashtbl.find_opt signatures fn.CoreIdent.fn_name with
          | Some callee ->
              let env = Env.use_public env Arch_utils.rsp in
              [
                (i + 1,
                 call_env env callee
                   (Arch_utils.get_instr_annotation instr));
              ]
          | None ->
              error "signature not available for %s" fn.CoreIdent.fn_name)
      | _ -> error "unsupported instruction"
  end

  module Calls = struct
    let join_into map key level =
      SM.update key
        (function None -> Some level | Some prev -> Some (Level.join level prev))
        map

    let infer_type_substitution caller callee bindings =
      let infer (env, substitution) (callee_slot, caller_slots) =
        match Env.get callee.pre callee_slot with
        | Level.Public ->
            if caller_slots = [] then
              error "leak: caller has no instantiation for callee's public array %s"
              callee_slot;
            (List.fold_left Env.use_public env caller_slots, substitution)
        | Level.Secret -> env, substitution
        | Level.Poly variables ->
            let actual_level =
              if caller_slots = [] then Level.Secret
              else Level.join_list (List.map (Env.get env) caller_slots)
            in
            let substitution' =
              SS.fold
                (fun variable acc ->
                  join_into acc variable actual_level)
                variables substitution
            in
            env, substitution'
      in
      List.fold_left infer (caller, SM.empty) bindings

    let apply_postconditions caller callee substitution bindings =
      let apply posts (callee_slot, caller_slots) =
        let return_level =
          Level.subst substitution (Env.get callee.post callee_slot)
        in
        List.fold_left
          (fun acc slot -> join_into acc slot return_level)
          posts caller_slots
      in
      let post_updates = List.fold_left apply SM.empty bindings in
      SM.fold (fun slot level env -> Env.set env slot level)
        post_updates caller

    let slot_bindings callee_sig inst =
      let is_array slot = not (SS.mem callee_slot Arch_utils.arch_slots_set) in
      List.map
        (fun callee_slot ->
          if is_array then
            callee_slot,
            Option.value ~default:[] (SM.find_opt callee_slot inst))
          else
            callee_slot, [ callee_slot ]
        callee_sig.slots

    let call_env caller callee inst =
      let bindings = slot_bindings callee inst in
      let caller, substitution =
        infer_type_substitution caller callee bindings
      in
      apply_postconditions caller callee substitution bindings
  end

  module Dataflow = struct
    let label_map body =
      let m = ref LM.empty in
      Array.iteri
        (fun i instr ->
          match instr.asmi_i with
          | LABEL (_, lbl) -> m := LM.add lbl i !m
          | _ -> ())
        body;
      !m

    let fixpoint fn_name body pre signatures =
      let labels = label_map body in
      let exit = Array.length body in
      let envs : Env.t option array = Array.make (exit + 1) None in
      let changed = ref false in

      let flow (instr_i, new_env) =
        match envs.(instr_i) with
        | None ->
            envs.(instr_i) <- Some new_env;
            if instr_i < exit then changed := true
        | Some old_env ->
            let joined = Env.join old_env new_env in
            if not (Env.le joined old_env) then begin
              envs.(instr_i) <- Some joined;
              if instr_i < exit then changed := true
            end
      in

      flow (0, pre);
      while !changed do
        changed := false;
        Array.iteri
          (fun i instr ->
            match envs.(i) with
            | None -> ()
            | Some env ->
                List.iter flow
                  (Instruction.step fn_name labels ~exit env i instr
                     signatures Calls.call_env))
          body
      done;

      let public_levels =
        Array.fold_left
          (fun public ->
            function Some (e : Env.t) ->
              SS.union public e.public
            | None -> public)
          SS.empty envs
      in
      (public_levels, envs.(exit))
  end

  let collect_slots body inst_images =
    let mem_slots =
      List.concat_map Arch_utils.get_mem_annotation body @ inst_images
      |> List.sort_uniq String.compare
      |> List.filter (fun s -> not (SS.mem s Arch_utils.arch_slots_set))
    in
    Arch_utils.arch_slots @ mem_slots

  let init_pre_env analysis slots =
    let env =
      List.fold_left
        (fun env s -> Env.set env s (fresh analysis (s ^ "_")))
        { levels = SM.empty; public = SS.empty }
        slots
    in
    Env.set env unknown_mem_slot Level.Secret

  let ty_fundef analysis (f_name, f_def) =
    let name = f_name.CoreIdent.fn_name in
    let inst_images = List.concat_map Arch_utils.inst_image f_def.asm_fd_body in
    let slots = collect_slots f_def.asm_fd_body inst_images in
    let pre = init_pre_env analysis slots in
    let body = Array.of_list f_def.asm_fd_body in

    match Dataflow.fixpoint name body pre analysis.signatures with
    | _, None ->
        Utils.hierror ~loc:Utils.Lnone ~funname:name
          ~kind:"constant-time checker" "no path returns"
    | public_levels, Some post ->
        let f_sig =
          { slots;
            pre = { pre with public = public_levels };
            post = { post with public = public_levels } }
        in
        Hashtbl.replace analysis.signatures name f_sig;
        Some f_sig

  let callees f_def : string list =
    List.filter_map
      (fun instr ->
        match instr.asmi_i with
        | CALL (fn, _) -> Some fn.CoreIdent.fn_name
        | _ -> None)
      f_def.asm_fd_body

  (* Post-order DFS of the call graph, so that every callee
     is typed before its callers. *)
  let callees_first funcs =
    let by_name = Hashtbl.create 17 in
    List.iter
      (fun ((f_name : CoreIdent.funname), f_def) ->
        Hashtbl.replace by_name f_name.CoreIdent.fn_name (f_name, f_def))
      funcs;
    let seen = Hashtbl.create 17 in
    let acc = ref [] in
    let rec visit ((f_name : CoreIdent.funname), f_def) =
      if not (Hashtbl.mem seen f_name.CoreIdent.fn_name) then begin
        Hashtbl.replace seen f_name.CoreIdent.fn_name ();
        List.iter
          (fun c -> Option.iter visit (Hashtbl.find_opt by_name c))
          (callees f_def);
        acc := (f_name, f_def) :: !acc
      end
    in
    List.iter visit funcs;
    List.rev !acc

  let signatures prog =
    let analysis = create () in
    let status =
      match
        List.iter
          (fun (name, def) -> ignore (ty_fundef analysis (name, def)))
          (callees_first prog.asm_funcs)
      with
      | () -> None
      | exception CtTypeError msg -> Some msg
    in
    let results =
      List.map
        (fun (name, _) ->
          (name.CoreIdent.fn_name,
           Hashtbl.find_opt analysis.signatures name.CoreIdent.fn_name))
        prog.asm_funcs
    in
    results, status

  let chk
      (ap :
        ( Arch.reg,
          Arch.regx,
          Arch.xreg,
          Arch.rflag,
          Arch.cond,
          Arch.asm_op )
        Arch_decl.asm_prog)
      : unit =
    let results, status = signatures ap in
    pp_signatures Format.err_formatter results;
    Option.iter
      (fun msg ->
        Utils.hierror ~loc:Utils.Lnone ~kind:"constant-time checker" "%t" msg)
      status
end
