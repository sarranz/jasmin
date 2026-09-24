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

  let write (env : t) ~(strong_write : bool) (memory_slots : string list)
      (slot : string) (level : Level.t) : t =
    if slot = unknown_mem_slot then env
    else if strong_write || not (List.mem slot memory_slots) then
      set env slot level
    else set env slot (Level.join (get env slot) level)
end

module OffsetSet = Set.Make (Z)

module Region = struct
  type t = { mem_slot : string; offset : Z.t; size : Z.t }

  let limit (region : t) : Z.t = Z.add region.offset region.size

  let parse_array_index (name : string) : (string * Z.t) option =
    let name_length = String.length name in
    if name_length = 0 || name.[name_length - 1] <> ']' then None
    else
      match String.rindex_opt name '[' with
      | None -> None
      | Some bracket_idx -> (
          let digits =
            String.sub name (bracket_idx + 1) (name_length - bracket_idx - 2)
          in
          match Z.of_string digits with
          | index -> Some (String.sub name 0 bracket_idx, index)
          | exception _ -> None)

  let of_annot (annot_region : Annotations.region) : t =
    let name = annot_region.Annotations.r_name in
    let size = annot_region.Annotations.r_size in
    match parse_array_index name with
    | None -> { mem_slot = name; offset = Z.zero; size }
    | Some (mem_slot, element_index) ->
        { mem_slot; offset = Z.mul element_index size; size }

  let translation (callee : t) (caller : t) : (t -> t) option =
    if Z.equal caller.size callee.size then
      Some (fun callee_subreg -> {
        mem_slot = caller.mem_slot;
        offset = Z.add caller.offset (Z.sub callee_subreg.offset callee.offset);
        size = callee_subreg.size })
    else None
end

module Annots = struct
  type t =
    | Access of Region.t list
    | Call of { callee : string; inst : (Region.t * Region.t list) list }

  let of_instr instr : t =
    match instr.asmi_i with
    | CALL (fn, _) ->
        let inst =
          Option.value ~default:[]
            (Annot.has_instantiation_annot (snd instr.asmi_ii))
          |> List.map (fun (annot_callee, annot_callers) ->
                 (Region.of_annot annot_callee,
                  List.map Region.of_annot annot_callers))
        in
        Call { callee = fn.CoreIdent.fn_name; inst }
    | _ ->
        Access
          (Option.value ~default:[] (Annot.has_array_annot (snd instr.asmi_ii))
           |> List.map Region.of_annot)

  let of_body body : t array = Array.map of_instr body
end

module MemLayout = struct
  
  module Boundaries = struct
    type t = OffsetSet.t SM.t

    let empty : t = SM.empty
    
    let cut (boundaries : t) (region : Region.t) : t =
      SM.update region.mem_slot
      (fun offsets ->
        let offsets = Option.value ~default:OffsetSet.empty offsets in
        Some
        (OffsetSet.add region.offset
        (OffsetSet.add (Region.limit region) offsets)))
        boundaries
        
    let cut_all (boundaries : t) (regions : Region.t list) : t =
      List.fold_left cut boundaries regions

  end

  module Block = struct
    type t = { start : Z.t; limit : Z.t; slot : string }

    let size (block : t) : Z.t = Z.sub block.limit block.start
  end
        
  type t = Block.t list SM.t

  let of_boundaries (boundaries : Boundaries.t) : t =
    let rec consecutive_pairs = function
      | x :: (y :: _ as rest) -> (x, y) :: consecutive_pairs rest
      | _ -> []
    in
    let make_block ~mem_slot (start, limit) =
      let slot =
        Printf.sprintf "%s[%s..%s)" mem_slot (Z.to_string start)
          (Z.to_string limit)
      in
      { Block.start; limit; slot }
    in
    let to_blocks mem_slot offsets =
      match consecutive_pairs (OffsetSet.elements offsets) with
      | [ (start, limit) ] -> [ { Block.start; limit; slot = mem_slot } ]
      | ranges -> List.map (make_block ~mem_slot) ranges
    in
    SM.mapi to_blocks boundaries

  let overlapping_blocks (layout : t) (region : Region.t) : Block.t list =
    match SM.find_opt region.mem_slot layout with
    | None -> []
    | Some blocks ->
        let overlaps (block : Block.t) =
          Z.lt block.start (Region.limit region) && Z.lt region.offset block.limit
        in
        List.filter overlaps blocks

  let blocks_of_regions (layout : t) (regions : Region.t list) : Block.t list =
    match regions with
    | [] -> []
    | _ ->
        let seen = Hashtbl.create 17 in
        let is_new (block : Block.t) =
          if Hashtbl.mem seen block.slot then false
          else begin
            Hashtbl.add seen block.slot (); true
          end
        in
        regions
        |> List.concat_map (overlapping_blocks layout)
        |> List.filter is_new

  let block_slots (blocks : Block.t list) : string list =
    List.map (fun (block : Block.t) -> block.slot) blocks

  let slots (layout : t) : string list =
    layout
    |> SM.bindings
    |> List.concat_map (fun (_, blocks) -> block_slots blocks)
    |> List.sort_uniq String.compare

  let total_bytes (blocks : Block.t list) : Z.t =
    List.fold_left (fun acc block -> Z.add acc (Block.size block)) Z.zero blocks

  type translated_block = {
    callee_block : Block.t;
    caller_region : Region.t;
  }

  let translate_blocks (callee_layout : t) (callee_reg : Region.t)
      (caller_reg : Region.t) : translated_block list option =
    match Region.translation callee_reg caller_reg with
    | None -> None
    | Some translate ->
        let subregion (block : Block.t) : Region.t =
          { Region.mem_slot = callee_reg.mem_slot;
            offset = block.start;
            size = Block.size block }
        in
        Some
          (List.map
             (fun block ->
               { callee_block = block;
                 caller_region = translate (subregion block) })
             (overlapping_blocks callee_layout callee_reg))

  let of_annots layout_of_callee annots : t =
    let cut_inst_entry callee_layout boundaries (callee_reg, caller_regs) =
      let boundaries = Boundaries.cut_all boundaries caller_regs in
      match callee_layout, caller_regs with
      | Some callee_layout, [ caller_reg ] ->
          translate_blocks callee_layout callee_reg caller_reg
          |> Option.value ~default:[]
          |> List.map (fun (b : translated_block) -> b.caller_region)
          |> Boundaries.cut_all boundaries
      | _ -> boundaries
    in
    let cut_annot boundaries = function
      | Annots.Access regions -> Boundaries.cut_all boundaries regions
      | Annots.Call { callee; inst } ->
          List.fold_left (cut_inst_entry (layout_of_callee callee)) boundaries inst
    in
    let collect_boundaries = Array.fold_left cut_annot Boundaries.empty in
    annots |> collect_boundaries |> of_boundaries
end

module MemoryInstantiation = struct
  type caller_block = string * bool

  type t = caller_block list SM.t

  let empty : t = SM.empty

  type binding = {
    bd_callee : string;
    bd_callers : MemLayout.Block.t list;
    bd_covers : bool;
  }

  let bindings_of_entry caller_layout callee_layout
      (callee_region, caller_regions) : binding list =
    let translated_bindings translated =
      List.map
        (fun ({ callee_block; caller_region } : MemLayout.translated_block) ->
          { bd_callee = callee_block.slot;
            bd_callers =
              MemLayout.overlapping_blocks caller_layout caller_region;
            bd_covers = true })
        translated
    in
    let cover_bindings () =
      let caller_blocks = MemLayout.blocks_of_regions caller_layout caller_regions in
      let caller_bytes = MemLayout.total_bytes caller_blocks in
      List.map
        (fun (callee_block : MemLayout.Block.t) ->
          { bd_callee = callee_block.slot;
            bd_callers = caller_blocks;
            bd_covers =
              Z.equal caller_bytes (MemLayout.Block.size callee_block) })
        (MemLayout.overlapping_blocks callee_layout callee_region)
    in
    match caller_regions with
    | [ caller_region ] -> (
        match
          MemLayout.translate_blocks callee_layout callee_region caller_region
        with
        | Some translated -> translated_bindings translated
        | None -> cover_bindings ())
    | _ -> cover_bindings ()

  let of_entries caller_layout callee_layout entries : t =
    let add mapping { bd_callee; bd_callers; bd_covers } =
      let images =
        List.map
          (fun (block : MemLayout.Block.t) -> (block.slot, bd_covers))
          bd_callers
      in
      SM.update bd_callee
        (fun previous ->
          Some (List.rev_append images (Option.value ~default:[] previous)))
        mapping
    in
    List.concat_map (bindings_of_entry caller_layout callee_layout) entries
    |> List.fold_left add empty
end

type signature = {
  slots : string list;
  layout : MemLayout.t;
  pre : Env.t;
  post : Env.t;
}

module MemoryAccess = struct
  type t = {
    ac_slots : string list; (* The slots the instruction reads or writes *)
    ac_bytes : Z.t; (* How many bytes the instruction reads or writes. *)
    ac_unannotated : bool; (* True if the instruction has no array annotation. *)
    ac_inst : MemoryInstantiation.t;
        (* On a CALL, the caller/callee correspondence; empty otherwise. *)
  }

  let resolve signatures layout : Annots.t -> t = function
    | Annots.Access regions ->
        let blocks = MemLayout.blocks_of_regions layout regions in
        { ac_slots = MemLayout.block_slots blocks;
          ac_bytes = MemLayout.total_bytes blocks;
          ac_unannotated = regions = [];
          ac_inst = MemoryInstantiation.empty }
    | Annots.Call { callee; inst } ->
        let inst =
          match Hashtbl.find_opt signatures callee with
          | Some callee ->
              MemoryInstantiation.of_entries layout callee.layout inst
          | None -> MemoryInstantiation.empty
        in
        { ac_slots = []; ac_bytes = Z.zero; ac_unannotated = true;
          ac_inst = inst }

  let resolve_all signatures layout (annots : Annots.t array) : t array =
    Array.map (resolve signatures layout) annots
end

type arch_slots = { names : string list; set : SS.t }

module Calls = struct
  let join_into map key level : Level.t SM.t =
    SM.update key
      (function None -> Some level | Some prev -> Some (Level.join level prev))
      map

  let infer_type_substitution caller callee bindings : Env.t * Level.t SM.t =
    let infer (env, substitution) (callee_slot, caller_slots) =
      let caller_slots = List.map fst caller_slots in
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

  let apply_postconditions caller callee substitution bindings : Env.t =
    let apply posts (callee_slot, caller_slots) : Level.t SM.t =
      let return_level =
        Level.subst substitution (Env.get callee.post callee_slot)
      in
      List.fold_left
        (fun acc (slot, covers) ->
          let level =
            if covers then return_level
            else Level.join (Env.get caller slot) return_level
          in
          join_into acc slot level)
        posts caller_slots
    in
    let post_updates = List.fold_left apply SM.empty bindings in
    SM.fold (fun slot level env -> Env.set env slot level)
      post_updates caller

  type slot_binding = string * MemoryInstantiation.caller_block list

  let slot_bindings ~arch_slots callee_sig inst : slot_binding list =
    let is_array slot : bool = not (SS.mem slot arch_slots.set) in
    List.map
      (fun callee_slot ->
        if is_array callee_slot then
          (callee_slot,
           Option.value ~default:[] (SM.find_opt callee_slot inst))
        else (callee_slot, [ (callee_slot, true) ]))
      callee_sig.slots

  (* The caller slots that more than one binding reaches. *)
  let shared_slots (bindings : slot_binding list) : SS.t =
    List.concat_map (fun (_, callers) -> List.map fst callers) bindings
    |> List.fold_left
         (fun (seen, shared) slot ->
           if SS.mem slot seen then (seen, SS.add slot shared)
           else (SS.add slot seen, shared))
         (SS.empty, SS.empty)
    |> snd

  let weaken_shared (bindings : slot_binding list) : slot_binding list =
    let shared = shared_slots bindings in
    List.map
      (fun (callee_slot, callers) ->
        (callee_slot,
         List.map
           (fun (slot, covers) -> (slot, covers && not (SS.mem slot shared)))
           callers))
      bindings

  let call_env ~arch_slots caller callee inst : Env.t =
    let bindings = weaken_shared (slot_bindings ~arch_slots callee inst) in
    let caller, substitution =
      infer_type_substitution caller callee bindings
    in
    apply_postconditions caller callee substitution bindings
end

module Dataflow = struct
  let label_map body : int LM.t =
    let m = ref LM.empty in
    Array.iteri
      (fun i instr ->
        match instr.asmi_i with
        | LABEL (_, lbl) -> m := LM.add lbl i !m
        | _ -> ())
      body;
    !m

  let fixpoint ~step body pre : SS.t * Env.t option =
    let labels = label_map body in
    let exit = Array.length body in
    let envs : Env.t option array = Array.make (exit + 1) None in
    let changed = ref false in

    let flow (instr_i, new_env) : unit =
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
              let next =
                try step ~labels ~exit i env instr
                with CtTypeError msg ->
                  error "%a:@ %t" Location.pp_iloc (fst instr.asmi_ii) msg
              in
              List.iter flow next)
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

let collect_slots arch_slots (layout : MemLayout.t) : string list =
  arch_slots.names
  @ List.filter
      (fun s -> not (SS.mem s arch_slots.set))
      (MemLayout.slots layout)

let stack_frame_blocks (layout : MemLayout.t) f_def : SS.t =
  match
    Annotations.get_stack_frame_annot (FInfo.user_annot f_def.asm_fd_info)
  with
  | None -> SS.empty
  | Some stack_frame ->
      List.concat_map
        (fun (mem_slot, _) ->
          MemLayout.block_slots
            (Option.value ~default:[] (SM.find_opt mem_slot layout)))
        stack_frame
      |> SS.of_list

let callees f_def : string list =
  List.filter_map
    (fun instr ->
      match instr.asmi_i with
      | CALL (fn, _) -> Some fn.CoreIdent.fn_name
      | _ -> None)
    f_def.asm_fd_body

(* Post-order DFS of the call graph, so that every callee
   is typed before its callers. *)
let callees_first funcs :
    (CoreIdent.funname * (_, _, _, _, _, _) Arch_decl.asm_fundef) list =
  let by_name = Hashtbl.create 17 in
  List.iter
    (fun ((f_name : CoreIdent.funname), f_def) ->
      Hashtbl.replace by_name f_name.CoreIdent.fn_name (f_name, f_def))
    funcs;
  let seen = Hashtbl.create 17 in
  let acc = ref [] in
  let rec visit ((f_name : CoreIdent.funname), f_def) : unit =
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


type analysis = {
  signatures : (string, signature) Hashtbl.t;
  mutable fresh_var_counter : int;
}

let create () : analysis =
  { signatures = Hashtbl.create 17; fresh_var_counter = 0 }

let callee_layout analysis fn : MemLayout.t option =
  Option.map (fun s -> s.layout) (Hashtbl.find_opt analysis.signatures fn)

let fresh an prefix : Level.t =
  an.fresh_var_counter <- an.fresh_var_counter + 1;
  Level.Poly (SS.singleton (Printf.sprintf "%s%d" prefix an.fresh_var_counter))

let init_pre_env analysis ~stack_frame_blocks slots : Env.t =
  let env =
    List.fold_left
      (fun env s ->
        Env.set env s
          (if SS.mem s stack_frame_blocks then Level.Secret
           else fresh analysis (s ^ "_")))
      { levels = SM.empty; public = SS.empty }
      slots
  in
  Env.set env unknown_mem_slot Level.Secret

let string_of_level : Level.t -> string = function
  | Level.Public -> "public"
  | Level.Secret -> "secret"
  | Level.Poly s -> "poly{" ^ String.concat "," (SS.elements s) ^ "}"

let pp_slot s fmt slot : unit =
  Format.fprintf fmt "%-5s %-12s -> %s" slot
    (string_of_level (Env.get s.pre slot))
    (string_of_level (Env.get s.post slot))

let pp_signature fmt ((name : string), (s : signature)) : unit =
  Format.fprintf fmt "@[<v2>%s:@,%a@]" name
    (Utils.pp_list "@," (pp_slot s))
    s.slots

let pp_result fmt (name, r) : unit =
  match r with
  | Some s -> pp_signature fmt (name, s)
  | None -> Format.fprintf fmt "%s: skipped" name

let pp_signatures fmt results : unit =
  Format.fprintf fmt "@[<v>==== asmCtChecker: signatures ====@,%a@,%s@]@."
    (Utils.pp_list "@," pp_result)
    results "==== end signatures ===="

module Asm_ct_checker (Arch : Arch_full.Arch) = struct

  module Arch_utils = struct
    let arch = Arch.asm_e._asm
    let arch_decl = arch._arch_decl

    let reg_name r : string = arch_decl.toS_r.to_string r
    let regx_name r : string = arch_decl.toS_rx.to_string r
    let xreg_name r : string = arch_decl.toS_x.to_string r
    let flag_name f : string = arch_decl.toS_f.to_string f
    let rsp = reg_name arch_decl.ad_rsp

    let condt_slots c : string list =
      List.map (fun (v : Prog.var) -> v.CoreIdent.v_name) (Arch.vars_of_condt c)

    let arch_slots : string list =
      List.map reg_name (Arch_decl.registers arch_decl)
      @ List.map regx_name (Arch_decl.registerxs arch_decl)
      @ List.map xreg_name (Arch_decl.xregisters arch_decl)
      @ List.map flag_name (Arch_decl.rflags arch_decl)

    let arch_slots_set = SS.of_list arch_slots

    let callee_saved_slots : string list =
      List.map
        (function
          | ARReg r -> reg_name r
          | ARegX r -> regx_name r
          | AXReg r -> xreg_name r
          | ABReg f -> flag_name f)
        Arch.call_conv.callee_saved

    let instr_desc op : _ Arch_decl.instr_desc_t =
      arch._asm_op_decl.instr_desc_op op

    let regs_of_address : _ Arch_decl.address -> string list = function
      | Areg { ad_base; ad_offset; _ } ->
          List.filter_map (Option.map reg_name) [ ad_base; ad_offset ]
      | Arip _ -> []
  end

  module Syscall_clobber = struct
    let all_but_rsp : string list =
      List.filter (fun s -> s <> Arch_utils.rsp) Arch_utils.arch_slots

    let syscall_kill : string list =
      let saved = SS.of_list Arch_utils.callee_saved_slots in
      List.filter (fun s -> not (SS.mem s saved)) Arch_utils.arch_slots

    let slots : string list = syscall_kill (* change to `all_but_rsp` for only preserving rsp *)
  end

  module Instruction = struct
    let implicit_slot : _ Arch_decl.implicit_arg -> string = function
      | IArflag f -> Arch_utils.flag_name f
      | IAreg r -> Arch_utils.reg_name r

    let process_address env mem_slots kind address : Env.t * string list =
      let address_slots = Arch_utils.regs_of_address address in
      match kind with
      | AK_compute -> env, address_slots
      | AK_mem _ ->
          let env = List.fold_left Env.use_public env address_slots in
          if mem_slots = [] then env, [ unknown_mem_slot ]
          else env, mem_slots

    let process_explicit_arg args mem_slots env kind n :
        Env.t * string list =
      match List.nth_opt args (Conv.int_of_nat n) with
      | Some (Reg r) -> env, [ Arch_utils.reg_name r ]
      | Some (Regx r) -> env, [ Arch_utils.regx_name r ]
      | Some (XReg r) -> env, [ Arch_utils.xreg_name r ]
      | Some (Addr address) -> process_address env mem_slots kind address
      | Some (Condt c) -> env, Arch_utils.condt_slots c
      | Some (Imm _) | None -> env, []

    (* Get the slots the operand descriptors (id_in or id_out) read / write to.
       Addresses must be public, so the env is passed to record that requirement. *)
    let process_op_descs args mem_slots env op_descs : Env.t * string list =
      List.fold_left
        (fun (env, slots) op_desc ->
          match op_desc with
          | ADImplicit implicit -> env, implicit_slot implicit :: slots
          | ADExplicit (kind, n, _) ->
              let env, new_slots =
                process_explicit_arg args mem_slots env kind n
              in
              env, new_slots @ slots)
        (env, []) op_descs

    let mem_write_size args op_desc : int option =
      List.combine op_desc.id_out op_desc.id_tout
      |> List.find_map (fun (od, ty) ->
             match (od, ty) with
             | ADExplicit (AK_mem _, n, _), Type.Coq_lword ws -> (
                 match List.nth_opt args (Conv.int_of_nat n) with
                 | Some (Addr _) -> Some (Prog.size_of_ws ws)
                 | _ -> None)
             | _ -> None)

    let size_of_ltype : Type.ltype -> int = function
      | Type.Coq_lword ws -> Prog.size_of_ws ws
      | Type.Coq_lbool -> 1

    let declassify_slots env slots : Env.t =
      List.fold_left (fun env slot -> Env.set env slot Level.Public) env slots

    let declassify_region env (access : MemoryAccess.t) instr size : Env.t =
      let loc = fst instr.asmi_ii in
      if access.ac_unannotated then begin
        Utils.warning Utils.Always loc
          "asmCtChecker: ignore declassify of an unannotated memory region";
        env
      end
      else if Z.equal access.ac_bytes (Z.of_int size) then
        declassify_slots env access.ac_slots
      else begin
        Utils.warning Utils.Always loc
          "asmCtChecker: ignore declassify of %d byte(s), the annotation \
           only locates them within a region of %s byte(s)"
          size (Z.to_string access.ac_bytes);
        env
      end

    let ty_declassify_val env (access : MemoryAccess.t) instr lty arg : Env.t =
      match arg with
      | Reg r -> declassify_slots env [ Arch_utils.reg_name r ]
      | Regx r -> declassify_slots env [ Arch_utils.regx_name r ]
      | XReg r -> declassify_slots env [ Arch_utils.xreg_name r ]
      | Condt c -> declassify_slots env (Arch_utils.condt_slots c)
      | Addr _ -> declassify_region env access instr (size_of_ltype lty)
      | Imm _ -> env

    let ty_declassify_mem env (access : MemoryAccess.t) instr len : Env.t =
      declassify_region env access instr (Conv.int_of_cz len)

    let ty_asmop env (access : MemoryAccess.t) op args : Env.t =
      let op_desc = Arch_utils.instr_desc op in
      let env_slots = process_op_descs args access.ac_slots in
      let env, in_slots = env_slots env op_desc.id_in in
      let env, out_slots = env_slots env op_desc.id_out in
      let level = Level.join_list (List.map (Env.get env) in_slots) in
      (* A write is strong when it overwrites every block it touches. *)
      let strong_write =
        match mem_write_size args op_desc with
        | Some written_bytes ->
            access.ac_slots <> []
            && Z.equal (Z.of_int written_bytes) access.ac_bytes
        | None -> false
      in
      List.fold_left
        (fun env x -> Env.write env ~strong_write access.ac_slots x level)
        env out_slots

    (* which registers a syscall touches *)
    let convention_slots tys regs : string list =
      List.take (List.length tys) regs |> List.map Arch_utils.reg_name

    let syscall_arg_slots o : string list =
      convention_slots
        (Syscall.syscall_sig_s Arch.reg_size o).Syscall.scs_tin
        Arch.call_conv.call_reg_args

    let syscall_ret_slots o : string list =
      convention_slots
        (Syscall.syscall_sig_s Arch.reg_size o).Syscall.scs_tout
        Arch.call_conv.call_reg_ret

    let syscall_writes_memory : _ Syscall_t.syscall_t -> bool = function
      | Syscall_t.RandomBytes _ -> true

    let syscall_ret_level : _ Syscall_t.syscall_t -> Level.t = function
      | Syscall_t.RandomBytes _ -> Level.Public

    let ty_syscall env (access : MemoryAccess.t) o : Env.t =
      let env =
        List.fold_left Env.use_public env
          (Arch_utils.rsp :: syscall_arg_slots o)
      in
      let regions = access.ac_slots in
      if syscall_writes_memory o && access.ac_unannotated then
        error "no annotation names the region this syscall fills";
      let env = List.fold_left Env.use_public env regions in
      let clobbered =
        Syscall_clobber.slots @ syscall_ret_slots o @ regions
      in
      let env =
        List.fold_left
          (fun env slot -> Env.set env slot Level.Secret) env clobbered
      in
      List.fold_left
        (fun env slot -> Env.set env slot (syscall_ret_level o))
        env (syscall_ret_slots o)

    let step fn_name labels ~exit accesses env i instr signatures call_env :
        (int * Env.t) list =
      let target lbl : int = LM.find lbl labels in
      let access : MemoryAccess.t = accesses.(i) in
      match instr.asmi_i with
      | ALIGN | LABEL _ -> [ (i + 1, env) ]
      | AsmOp (op, args) ->
          [ (i + 1, ty_asmop env access op args) ]
      | Declassify_val (lty, arg) ->
          [ (i + 1, ty_declassify_val env access instr lty arg) ]
      | Declassify_mem (len, _) ->
          [ (i + 1, ty_declassify_mem env access instr len) ]
      | SysCall o -> [ (i + 1, ty_syscall env access o) ]
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
              [ (i + 1, call_env env callee access.ac_inst) ]
          | None ->
              error "signature not available for %s" fn.CoreIdent.fn_name)
      | _ -> error "unsupported instruction"
  end

  let arch_slots : arch_slots =
    { names = Arch_utils.arch_slots; set = Arch_utils.arch_slots_set }

  let ty_fundef analysis (f_name, f_def) : signature option =
    let name = f_name.CoreIdent.fn_name in
    let body = Array.of_list f_def.asm_fd_body in
    let annots = Annots.of_body body in
    let layout = MemLayout.of_annots (callee_layout analysis) annots in
    let accesses = MemoryAccess.resolve_all analysis.signatures layout annots in
    let slots = collect_slots arch_slots layout in
    let pre =
      init_pre_env analysis
        ~stack_frame_blocks:(stack_frame_blocks layout f_def) slots
    in
    let step ~labels ~exit i env instr =
      Instruction.step name labels ~exit accesses env i instr
        analysis.signatures (Calls.call_env ~arch_slots)
    in

    match Dataflow.fixpoint ~step body pre with
    | _, None ->
        Utils.hierror ~loc:Utils.Lnone ~funname:name
          ~kind:"constant-time checker" "no path returns"
    | public_levels, Some post ->
        let f_sig =
          { slots;
            layout;
            pre = { pre with public = public_levels };
            post = { post with public = public_levels } }
        in
        Hashtbl.replace analysis.signatures name f_sig;
        Some f_sig

  let signatures prog :
      (string * signature option) list * (Format.formatter -> unit) option =
    let analysis = create () in
    let status =
      match
        List.iter
          (fun ((name : CoreIdent.funname), def) ->
            try ignore (ty_fundef analysis (name, def))
            with CtTypeError msg ->
              error "@[<v>in function %s:@,%t@]" name.CoreIdent.fn_name msg)
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
