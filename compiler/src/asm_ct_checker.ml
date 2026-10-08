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

(* Cell standing for memory accesses that carry no array annotation: we
   dont know which region is accessed, but we interpret it as disjoint from
   every other region. *)
let unknown_mem_cell = "%unknown_mem"

(* Abstract region standing for global data: we assume globals are read-only
   and public and globals are not mentioned in call instantiation
   annotations. *)
let global_mem_region = "%global"

module Env = struct
  type t = {
    levels : Level.t SM.t;
    public : SS.t;
  }

  let empty : t = { levels = SM.empty; public = SS.empty }

  let get (env : t) (cell : string) : Level.t =
    match SM.find_opt cell env.levels with
    | Some level -> Level.norm env.public level
    | None -> error "unknown slot: %s" cell

  let set (env : t) (cell : string) (level : Level.t) : t =
    { env with
      levels = SM.add cell (Level.norm env.public level) env.levels }

  (* A weak update: the cell may keep what it held. *)
  let weaken (env : t) (cell : string) (level : Level.t) : t =
    set env cell (Level.join (get env cell) level)

  let keys (env : t) : string list = List.map fst (SM.bindings env.levels)

  let public (env : t) : SS.t = env.public

  let with_public (env : t) (public : SS.t) : t = { env with public }

  let use_public (env : t) (cell : string) : t =
    match get env cell with
    | Level.Public -> env
    | Level.Secret -> error "leak: secret value in %s leaked" cell
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
    let held (env : t) (cell : string) : Level.t =
      Option.value ~default:Level.Public (SM.find_opt cell env.levels)
    in
    SS.subset first.public second.public
    && SM.for_all
         (fun cell level ->
           Level.le (Level.norm first.public level)
             (Level.norm second.public (held second cell)))
         first.levels
end

module Region = struct
  type t = { mem_slot : string; offset : Z.t; size : Z.t }

  let limit (region : t) : Z.t = Z.add region.offset region.size

  let is_global (region : t) : bool = region.mem_slot = global_mem_region

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

  let access_region ~globals annot : Region.t =
    let region = Region.of_annot annot in
    if SS.mem region.mem_slot globals then
      { region with mem_slot = global_mem_region }
    else region

  let of_instr ~globals instr : t =
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
           |> List.map (access_region ~globals))

  let of_body ~globals body : t array = Array.map (of_instr ~globals) body
end

module Partition = struct
  type block = {
    location : string;
    start : Z.t;
    limit : Z.t;
    full : bool; (* the block covers its whole location *)
  }

  let block_size (block : block) : Z.t = Z.sub block.limit block.start

  let blocks_size (blocks : block list) : Z.t =
    List.fold_left (fun acc block -> Z.add acc (block_size block)) Z.zero blocks

  let block_as_cell (block : block) : string =
    if block.full then block.location
    else
      Printf.sprintf "%s[%s..%s)" block.location (Z.to_string block.start)
        (Z.to_string block.limit)

  let blocks_as_cells (blocks : block list) : string list =
    List.map block_as_cell blocks

  let blocks_of_offsets (location : string) (offsets : Z.t list) : block list =
    (* [offsets] must be sorted and contain the boundaries of the blocks. *)

    let rec consecutive_pairs = function
      | x :: (y :: _ as rest) -> (x, y) :: consecutive_pairs rest
      | _ -> []
    in
    match consecutive_pairs offsets with
    | [ (start, limit) ] -> [ { location; start; limit; full = true } ]
    | ranges ->
        List.map
          (fun (start, limit) -> { location; start; limit; full = false })
          ranges

  let block_overlaps ~(start : Z.t) ~(limit : Z.t) (block : block) : bool =
    Z.lt block.start limit && Z.lt start block.limit

  let block_within ~(start : Z.t) ~(limit : Z.t) (block : block) : bool =
    Z.leq start block.start && Z.leq block.limit limit

  module OffsetSet = Set.Make (Z)

  (* The offsets at which each location is cut: the bounds of the ranges of
     it that are accessed. *)
  type boundaries = OffsetSet.t SM.t

  let cut (boundaries : boundaries) ~(location : string) ~(start : Z.t)
      ~(limit : Z.t) : boundaries =
    SM.update location
      (fun offsets ->
        let offsets = Option.value ~default:OffsetSet.empty offsets in
        Some (OffsetSet.add start (OffsetSet.add limit offsets)))
      boundaries

  type t = block list SM.t

  let of_boundaries (boundaries : boundaries) : t =
    SM.mapi
      (fun location offsets ->
        blocks_of_offsets location (OffsetSet.elements offsets))
      boundaries
end

module MemLayout = struct
  type t = Partition.t

  let overlapping_blocks (layout : t) (region : Region.t) :
      Partition.block list =
    match SM.find_opt region.mem_slot layout with
    | None -> []
    | Some blocks ->
        List.filter
          (Partition.block_overlaps ~start:region.offset
             ~limit:(Region.limit region))
          blocks

  let blocks_of_regions (layout : t) (regions : Region.t list) :
      Partition.block list =
    match regions with
    | [] -> []
    | _ ->
        let seen = Hashtbl.create 17 in
        let is_new (block : Partition.block) =
          if Hashtbl.mem seen (Partition.block_as_cell block) then false
          else begin
            Hashtbl.add seen (Partition.block_as_cell block) (); true
          end
        in
        regions
        |> List.concat_map (overlapping_blocks layout)
        |> List.filter is_new

  let slots (layout : t) : string list =
    layout
    |> SM.bindings
    |> List.concat_map (fun (_, blocks) -> Partition.blocks_as_cells blocks)
    |> List.sort_uniq String.compare

  let stack_frame_cells (layout : t) f_def : SS.t =
    match
      Annotations.get_stack_frame_annot (FInfo.user_annot f_def.asm_fd_info)
    with
    | None -> SS.empty
    | Some stack_frame ->
        List.concat_map
          (fun (mem_slot, _) ->
            Partition.blocks_as_cells
              (Option.value ~default:[] (SM.find_opt mem_slot layout)))
          stack_frame
        |> SS.of_list

  type translated_block = {
    callee_block : Partition.block;
    caller_region : Region.t;
  }

  let translate_blocks (callee_layout : t) (callee_reg : Region.t)
      (caller_reg : Region.t) : translated_block list option =
    match Region.translation callee_reg caller_reg with
    | None -> None
    | Some translate ->
        let subregion (block : Partition.block) : Region.t =
          { Region.mem_slot = callee_reg.mem_slot;
            offset = block.start;
            size = Partition.block_size block }
        in
        Some
          (List.map
             (fun block ->
               { callee_block = block;
                 caller_region = translate (subregion block) })
             (overlapping_blocks callee_layout callee_reg))

  let of_annots layout_of_callee annots : t =
    let cut_regions boundaries regions =
      List.fold_left
        (fun boundaries (region : Region.t) ->
          Partition.cut boundaries ~location:region.mem_slot
            ~start:region.offset ~limit:(Region.limit region))
        boundaries regions
    in
    let cut_inst_entry callee_layout boundaries (callee_reg, caller_regs) =
      let boundaries = cut_regions boundaries caller_regs in
      match callee_layout, caller_regs with
      | Some callee_layout, [ caller_reg ] ->
          translate_blocks callee_layout callee_reg caller_reg
          |> Option.value ~default:[]
          |> List.map (fun (b : translated_block) -> b.caller_region)
          |> cut_regions boundaries
      | _ -> boundaries
    in
    let cut_annot boundaries = function
      | Annots.Access regions ->
          List.filter (fun r -> not (Region.is_global r)) regions
          |> cut_regions boundaries
      | Annots.Call { callee; inst } ->
          List.fold_left (cut_inst_entry (layout_of_callee callee)) boundaries inst
    in
    let collect_boundaries = Array.fold_left cut_annot SM.empty in
    annots |> collect_boundaries |> Partition.of_boundaries

  (* The caller cell that a callee block represents.
   [covers] is true when the caller cell is covered exactly. *)
  type caller_cell = { cell : string; covers : bool }

  type instantiation = caller_cell list SM.t

  let caller_cells covers (blocks : Partition.block list) : caller_cell list =
    List.map (fun block -> { cell = Partition.block_as_cell block; covers }) blocks

  let instantiate_entry caller_layout callee_layout
      (callee_region, caller_regions) : (string * caller_cell list) list =
    let translated_bindings translated =
      List.map
        (fun { callee_block; caller_region } ->
          ( Partition.block_as_cell callee_block,
            caller_cells true
              (overlapping_blocks caller_layout caller_region) ))
        translated
    in
    let cover_bindings () =
      let caller_blocks = blocks_of_regions caller_layout caller_regions in
      let caller_bytes = Partition.blocks_size caller_blocks in
      List.map
        (fun callee_block ->
          ( Partition.block_as_cell callee_block,
            caller_cells
              (Z.equal caller_bytes (Partition.block_size callee_block))
              caller_blocks ))
        (overlapping_blocks callee_layout callee_region)
    in
    match caller_regions with
    | [ caller_region ] -> (
        match translate_blocks callee_layout callee_region caller_region with
        | Some translated -> translated_bindings translated
        | None -> cover_bindings ())
    | _ -> cover_bindings ()

  let instantiate caller_layout callee_layout entries : instantiation =
    let add inst (callee_cell, cells) =
      SM.update callee_cell
        (fun previous ->
          Some (List.rev_append cells (Option.value ~default:[] previous)))
        inst
    in
    List.concat_map (instantiate_entry caller_layout callee_layout) entries
    |> List.fold_left add SM.empty
end

type signature = {
  layout : MemLayout.t;
  pre : Env.t;
  post : Env.t option; (* [None] if no exit *)
}

module MemoryAccess = struct
  type caller_cell = MemLayout.caller_cell = { cell : string; covers : bool }

  type binding = { callee_cell : string; caller_cells : caller_cell list }

  type t = {
    ac_cells : string list; (* The slots the instruction reads or writes *)
    ac_bytes : Z.t; (* How many bytes the instruction reads or writes. *)
    ac_unannotated : bool; (* True if the instruction has no array annotation. *)
    ac_bindings : binding list; (* On a CALL; empty otherwise. *)
  }

  let cell_bindings callee_sig (inst : MemLayout.instantiation) :
      binding list =
    let memory = SS.of_list (MemLayout.slots callee_sig.layout) in
    List.map
      (fun callee_cell ->
        let caller_cells =
          if SS.mem callee_cell memory then
            Option.value ~default:[] (SM.find_opt callee_cell inst)
          else [ { cell = callee_cell; covers = true } ]
        in
        { callee_cell; caller_cells })
      (Env.keys callee_sig.pre)

  let shared_cells (bindings : binding list) : SS.t =
    List.concat_map
      (fun b -> List.map (fun c -> c.cell) b.caller_cells)
      bindings
    |> List.fold_left
         (fun (seen, shared) cell ->
           if SS.mem cell seen then (seen, SS.add cell shared)
           else (SS.add cell seen, shared))
         (SS.empty, SS.empty)
    |> snd

  let weaken_shared (bindings : binding list) : binding list =
    let shared = shared_cells bindings in
    List.map
      (fun b ->
        { b with
          caller_cells =
            List.map
              (fun c ->
                { c with covers = c.covers && not (SS.mem c.cell shared) })
              b.caller_cells })
      bindings

  let resolve signatures layout : Annots.t -> t = function
    | Annots.Access regions ->
        let blocks = MemLayout.blocks_of_regions layout regions in
        let global = List.exists Region.is_global regions in
        { ac_cells =
            (if global then [ global_mem_region ]
             else Partition.blocks_as_cells blocks);
          ac_bytes = Partition.blocks_size blocks;
          ac_unannotated = regions = [];
          ac_bindings = [] }
    | Annots.Call { callee; inst } ->
        let bindings =
          match Hashtbl.find_opt signatures callee with
          | Some callee_sig ->
              MemLayout.instantiate layout callee_sig.layout inst
              |> cell_bindings callee_sig
              |> weaken_shared
          | None -> []
        in
        { ac_cells = []; ac_bytes = Z.zero; ac_unannotated = true;
          ac_bindings = bindings }

  let resolve_all signatures layout (annots : Annots.t array) : t array =
    Array.map (resolve signatures layout) annots
end

type arch_cells = { names : string list; set : SS.t }

module Calls = struct
  let join_into map key level : Level.t SM.t =
    SM.update key
      (function None -> Some level | Some prev -> Some (Level.join level prev))
      map

  let infer_type_substitution caller callee
      (bindings : MemoryAccess.binding list) : Env.t * Level.t SM.t =
    let infer (env, substitution)
        ({ callee_cell; caller_cells } : MemoryAccess.binding) =
      let caller_cells =
        List.map (fun (c : MemoryAccess.caller_cell) -> c.cell) caller_cells
      in
      match Env.get callee.pre callee_cell with
      | Level.Public ->
          if caller_cells = [] then
            error "leak: caller has no instantiation for callee's public array %s"
            callee_cell;
          (List.fold_left Env.use_public env caller_cells, substitution)
      | Level.Secret -> env, substitution
      | Level.Poly variables ->
          let actual_level =
            if caller_cells = [] then Level.Secret
            else Level.join_list (List.map (Env.get env) caller_cells)
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

  let apply_postconditions caller callee_post substitution
      (bindings : MemoryAccess.binding list) : Env.t =
    let apply env ({ callee_cell; caller_cells } : MemoryAccess.binding) :
        Env.t =
      let return_level =
        Level.subst substitution (Env.get callee_post callee_cell)
      in
      List.fold_left
        (fun env ({ cell; covers } : MemoryAccess.caller_cell) ->
          if covers then Env.set env cell return_level
          else Env.weaken env cell return_level)
        env caller_cells
    in
    List.fold_left apply caller bindings

  let call_env caller callee bindings : Env.t * Env.t option =
    let demanded, substitution =
      infer_type_substitution caller callee bindings
    in
    match callee.post with
    | None -> (demanded, None)
    | Some callee_post ->
        ( demanded,
          Some (apply_postconditions demanded callee_post substitution bindings)
        )
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
        (fun public -> function
          | Some env -> SS.union public (Env.public env)
          | None -> public)
        SS.empty envs
    in
    (public_levels, envs.(exit))
end

let collect_cells arch_cells (layout : MemLayout.t) : string list =
  arch_cells.names
  @ List.filter
      (fun s -> not (SS.mem s arch_cells.set))
      (MemLayout.slots layout)

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
  globals : SS.t;
  mutable fresh_var_counter : int;
}

let create ~globals () : analysis =
  { signatures = Hashtbl.create 17; globals; fresh_var_counter = 0 }

let callee_layout analysis fn : MemLayout.t option =
  Option.map (fun s -> s.layout) (Hashtbl.find_opt analysis.signatures fn)

let fresh an prefix : Level.t =
  an.fresh_var_counter <- an.fresh_var_counter + 1;
  Level.Poly (SS.singleton (Printf.sprintf "%s%d" prefix an.fresh_var_counter))

let init_pre_env analysis ~stack_frame_cells cells : Env.t =
  let env =
    List.fold_left
      (fun env s ->
        Env.set env s
          (if SS.mem s stack_frame_cells then Level.Secret
           else fresh analysis (s ^ "_")))
      Env.empty cells
  in
  let env = Env.set env unknown_mem_cell Level.Secret in
  Env.set env global_mem_region Level.Public

let string_of_level : Level.t -> string = function
  | Level.Public -> "public"
  | Level.Secret -> "secret"
  | Level.Poly s -> "poly{" ^ String.concat "," (SS.elements s) ^ "}"

let shown_cells (cells : string list) (s : signature) :
    string list * int =
  let uses = Hashtbl.create 97 in
  let count : Level.t -> unit = function
    | Level.Poly vars ->
        SS.iter
          (fun v ->
            Hashtbl.replace uses v
              (1 + Option.value ~default:0 (Hashtbl.find_opt uses v)))
          vars
    | Level.Public | Level.Secret -> ()
  in
  List.iter
    (fun cell ->
      count (Env.get s.pre cell);
      Option.iter (fun post -> count (Env.get post cell)) s.post)
    cells;
  let occurrences v = Option.value ~default:0 (Hashtbl.find_opt uses v) in
  let shown cell =
    match
      (Env.get s.pre cell, Option.map (fun p -> Env.get p cell) s.post)
    with
    | Level.Poly pre, Some (Level.Poly post) when SS.equal pre post ->
        SS.exists (fun v -> occurrences v > 2) pre
    | Level.Poly pre, None -> SS.exists (fun v -> occurrences v > 1) pre
    | _ -> true
  in
  let shown = List.filter shown cells in
  (shown, List.length cells - List.length shown)

let pp_cell ~cell_width ~pre_width s fmt cell : unit =
  let pad width text =
    text ^ String.make (max 0 (width - String.length text)) ' '
  in
  match s.post with
  | Some post ->
      Format.fprintf fmt "%s %s -> %s" (pad cell_width cell)
        (pad pre_width (string_of_level (Env.get s.pre cell)))
        (string_of_level (Env.get post cell))
  | None ->
      Format.fprintf fmt "%s %s" (pad cell_width cell)
        (string_of_level (Env.get s.pre cell))

let pp_signature arch_cells fmt ((name : string), (s : signature)) : unit =
  let cells, omitted =
    shown_cells (collect_cells arch_cells s.layout) s
  in
  let width f =
    List.fold_left (fun w x -> max w (String.length (f x))) 0 cells
  in
  let pp_cell =
    pp_cell
      ~cell_width:(width (fun cell -> cell))
      ~pre_width:
        (width (fun cell -> string_of_level (Env.get s.pre cell)))
      s
  in
  let pp_omitted fmt n =
    Format.fprintf fmt "(%d slot%s preserved, named nowhere else, omitted)" n
      (if n = 1 then "" else "s")
  in
  let header = if s.post = None then name ^ ": does not return" else name ^ ":" in
  match (cells, omitted) with
  | [], 0 -> Format.fprintf fmt "%s" header
  | [], n -> Format.fprintf fmt "@[<v2>%s@,%a@]" header pp_omitted n
  | cells, 0 ->
      Format.fprintf fmt "@[<v2>%s@,%a@]" header
        (Utils.pp_list "@," pp_cell) cells
  | cells, n ->
      Format.fprintf fmt "@[<v2>%s@,%a@,%a@]" header
        (Utils.pp_list "@," pp_cell) cells pp_omitted n

let pp_result arch_cells fmt (name, r) : unit =
  match r with
  | Some s -> pp_signature arch_cells fmt (name, s)
  | None -> Format.fprintf fmt "%s: rejected" name

let pp_signatures arch_cells fmt results : unit =
  Format.fprintf fmt "@[<v>==== asmCtChecker: signatures ====@,%a@,%s@]@."
    (Utils.pp_list "@," (pp_result arch_cells))
    results "==== end signatures ===="

module Asm_ct_checker
    (Arch : Arch_full.Arch)
    (Program : sig
       val prog :
         ( Arch.reg,
           Arch.regx,
           Arch.xreg,
           Arch.rflag,
           Arch.cond,
           Arch.asm_op )
         Arch_decl.asm_prog
     end) =
struct

  module Arch_utils = struct
    let arch = Arch.asm_e._asm
    let arch_decl = arch._arch_decl

    let reg_name r : string = arch_decl.toS_r.to_string r
    let regx_name r : string = arch_decl.toS_rx.to_string r
    let xreg_name r : string = arch_decl.toS_x.to_string r
    let flag_name f : string = arch_decl.toS_f.to_string f

    let rsp = reg_name arch_decl.ad_rsp

    let arch_names : string list =
      List.map reg_name (Arch_decl.registers arch_decl)
      @ List.map regx_name (Arch_decl.registerxs arch_decl)
      @ List.map xreg_name (Arch_decl.xregisters arch_decl)
      @ List.map flag_name (Arch_decl.rflags arch_decl)

    let condt_names c : string list =
      List.map (fun (v : Prog.var) -> v.CoreIdent.v_name) (Arch.vars_of_condt c)

    let instr_desc op : _ Arch_decl.instr_desc_t =
      arch._asm_op_decl.instr_desc_op op

    (* Whether all outputs are input-independent constants: XOR r,r and
       VPXOR x,y,y. Note that this level affects the set flags too (VPXOR
       sets none). *)
    let constant_output op args : bool =
      match (instr_desc op).id_str_jas (), args with
      | ("XOR_32" | "XOR_64"), [ Reg r1; Reg r2 ] -> r1 = r2
      | ("VPXOR_128" | "VPXOR_256"), [ _; XReg r1; XReg r2 ] -> r1 = r2
      | _ -> false

    let size_of_ltype : Type.ltype -> int = function
      | Type.Coq_lword ws -> Prog.size_of_ws ws
      | Type.Coq_lbool -> 1

    let register_of_arg : _ Arch_decl.asm_arg -> string option = function
      | Reg r -> Some (reg_name r)
      | Regx r -> Some (regx_name r)
      | XReg r -> Some (xreg_name r)
      | Condt _ | Addr _ | Imm _ -> None

    (* The register an operand reads or writes, and how many of its bytes. *)
    let operand_register args (op_desc, ty) : (string * int) option =
      let register =
        match op_desc with
        | ADImplicit (IAreg r) -> Some (reg_name r)
        | ADImplicit (IArflag _) -> None
        | ADExplicit (_, n, _) ->
            Option.bind (List.nth_opt args (Conv.int_of_nat n)) register_of_arg
      in
      Option.map (fun reg -> (reg, size_of_ltype ty)) register

    (* The range [start, limit) of its register that an operand of [bytes]
       bytes is its lowest bytes. *)
    let operand_range (bytes : int) : Z.t * Z.t = (Z.zero, Z.of_int bytes)

    let convention_registers tys regs : string list =
      List.map reg_name (List.take (List.length tys) regs)

    let syscall_arg_registers o : string list =
      convention_registers
        (Syscall.syscall_sig_s Arch.reg_size o).Syscall.scs_tin
        Arch.call_conv.call_reg_args

    let syscall_ret_registers o : string list =
      convention_registers
        (Syscall.syscall_sig_s Arch.reg_size o).Syscall.scs_tout
        Arch.call_conv.call_reg_ret

    let callee_saved : string list =
      List.map
        (function
          | ARReg r -> reg_name r
          | ARegX r -> regx_name r
          | AXReg r -> xreg_name r
          | ABReg f -> flag_name f)
        Arch.call_conv.callee_saved
  end

  (* The registers of [Program.prog], cut into blocks where it accesses them
     partially, and the cells they give. *)
  module Registers = struct
    open Arch_utils

    let access_widths prog : int list SM.t =
      let accesses instr : (string * int) list =
        match instr.asmi_i with
        | AsmOp (op, args) ->
            let desc = instr_desc op in
            List.combine desc.id_in desc.id_tin
            @ List.combine desc.id_out desc.id_tout
            |> List.filter_map (operand_register args)
        | Declassify_val (lty, arg) -> (
            match register_of_arg arg with
            | Some reg -> [ (reg, size_of_ltype lty) ]
            | None -> [])
        | _ -> []
      in
      let add widths (reg, bytes) =
        SM.update reg
          (fun known -> Some (bytes :: Option.value ~default:[] known))
          widths
      in
      prog.asm_funcs
      |> List.concat_map (fun (_, f_def) ->
             List.concat_map accesses f_def.asm_fd_body)
      |> List.fold_left add SM.empty

    let registers : Partition.t =
      let widths = access_widths Program.prog in
      let cut width boundaries name =
        let width = Z.of_int width in
        let boundaries =
          Partition.cut boundaries ~location:name ~start:Z.zero
            ~limit:width
        in
        List.fold_left
          (fun boundaries bytes ->
            let start, limit = operand_range bytes in
            if Z.leq limit width then
              Partition.cut boundaries ~location:name ~start ~limit
            else boundaries)
          boundaries
          (Option.value ~default:[] (SM.find_opt name widths))
      in
      let cut_all width names boundaries =
        List.fold_left (cut width) boundaries names
      in
      let reg_bytes = Prog.size_of_ws arch_decl.reg_size in
      let xreg_bytes = Prog.size_of_ws arch_decl.xreg_size in
      SM.empty
      |> cut_all reg_bytes (List.map reg_name (Arch_decl.registers arch_decl))
      |> cut_all reg_bytes (List.map regx_name (Arch_decl.registerxs arch_decl))
      |> cut_all xreg_bytes
           (List.map xreg_name (Arch_decl.xregisters arch_decl))
      |> Partition.of_boundaries

    let blocks (reg : string) : Partition.block list =
      match SM.find_opt reg registers with
      | Some blocks -> blocks
      | None -> error "unknown register: %s" reg

    let is_register (name : string) : bool = SM.mem name registers

    type coverage = {
      within : string list;
      straddling : string list;
      outside : string list;
    }

    let coverage (reg : string) (bytes : int) : coverage =
      let start, limit = operand_range bytes in
      let within, rest =
        List.partition (Partition.block_within ~start ~limit) (blocks reg)
      in
      let straddling, outside =
        List.partition (Partition.block_overlaps ~start ~limit) rest
      in
      { within = Partition.blocks_as_cells within;
        straddling = Partition.blocks_as_cells straddling;
        outside = Partition.blocks_as_cells outside }

    (* The cells of a whole register; any other cell stands for itself. *)
    let whole (name : string) : string list =
      match SM.find_opt name registers with
      | Some blocks -> Partition.blocks_as_cells blocks
      | None -> [ name ]

    let rsp = whole Arch_utils.rsp

    let condt_cells c : string list = List.concat_map whole (condt_names c)

    let regs_of_address : _ Arch_decl.address -> string list = function
      | Areg { ad_base; ad_offset; _ } ->
          List.concat_map whole
            (List.filter_map (Option.map reg_name) [ ad_base; ad_offset ])
      | Arip _ -> []
  end

  module Syscall_clobber = struct
    let syscall_kill : string list =
      let saved = SS.of_list Arch_utils.callee_saved in
      List.filter (fun s -> not (SS.mem s saved)) Arch_utils.arch_names

    let names : string list = syscall_kill
  end

  module Instruction = struct
    let process_address env mem_cells kind address : Env.t * string list =
      let address_cells = Registers.regs_of_address address in
      match kind with
      | AK_compute -> env, address_cells
      | AK_mem _ ->
          let env = List.fold_left Env.use_public env address_cells in
          if mem_cells = [] then env, [ unknown_mem_cell ]
          else env, mem_cells

    let operand_cells args mem_cells env op_desc : Env.t * string list =
      match op_desc with
      | ADImplicit (IArflag f) -> env, [ Arch_utils.flag_name f ]
      | ADImplicit (IAreg _) -> env, []
      | ADExplicit (kind, n, _) -> (
          match List.nth_opt args (Conv.int_of_nat n) with
          | Some (Addr address) -> process_address env mem_cells kind address
          | Some (Condt c) -> env, Registers.condt_cells c
          | _ -> env, [])

    let input_cells args mem_cells env operand : Env.t * string list =
      match Arch_utils.operand_register args operand with
      | Some (reg, bytes) ->
          let { Registers.within; straddling; _ } =
            Registers.coverage reg bytes
          in
          env, within @ straddling
      | None -> operand_cells args mem_cells env (fst operand)

    (* What an output operand writes, a register or cells, and how many
       bytes. *)
    let outputs args mem_cells env ((op_desc, ty) as operand) :
        Env.t * (string * int) list =
      match Arch_utils.operand_register args operand with
      | Some (reg, bytes) -> env, [ (reg, bytes) ]
      | None ->
          let env, cells = operand_cells args mem_cells env op_desc in
          let bytes = Arch_utils.size_of_ltype ty in
          env, List.map (fun cell -> (cell, bytes)) cells

    let fold_operands f env descs tys =
      List.fold_left
        (fun (env, acc) operand ->
          let env, xs = f env operand in
          env, xs @ acc)
        (env, []) (List.combine descs tys)

    let write_register env msb reg bytes level : Env.t =
      let { Registers.within; straddling; outside } =
        Registers.coverage reg bytes
      in
      let set level env cell = Env.set env cell level in
      let env = List.fold_left (set level) env within in
      match msb with
      | MSB_CLEAR ->
          let env = List.fold_left (set Level.Public) env outside in
          List.fold_left (set level) env straddling
      | MSB_MERGE ->
          List.fold_left (fun env cell -> Env.weaken env cell level) env straddling

    let write_cell env (access : MemoryAccess.t) cell bytes level : Env.t =
      if cell = unknown_mem_cell then env
      else if
        (not (List.mem cell access.ac_cells))
        || Z.equal (Z.of_int bytes) access.ac_bytes
      then Env.set env cell level
      else Env.weaken env cell level

    let write_output msb (access : MemoryAccess.t) level env (name, bytes) :
        Env.t =
      if Registers.is_register name then write_register env msb name bytes level
      else write_cell env access name bytes level

    let declassify_cells env cells : Env.t =
      List.fold_left
        (fun env cell -> Env.set env cell Level.Public)
        env cells

    let declassify_region env (access : MemoryAccess.t) instr size : Env.t =
      let loc = fst instr.asmi_ii in
      if access.ac_unannotated then begin
        Utils.warning Utils.Always loc
          "asmCtChecker: ignore declassify of an unannotated memory region";
        env
      end
      else if Z.equal access.ac_bytes (Z.of_int size) then
        declassify_cells env access.ac_cells
      else begin
        Utils.warning Utils.Always loc
          "asmCtChecker: ignore declassify of %d byte(s), the annotation \
           only locates them within a region of %s byte(s)"
          size (Z.to_string access.ac_bytes);
        env
      end

    (* Only the cells the declassified operand covers whole. *)
    let declassify_register env instr reg bytes : Env.t =
      let { Registers.within; straddling; _ } = Registers.coverage reg bytes in
      List.iter
        (fun cell ->
          Utils.warning Utils.Always (fst instr.asmi_ii)
            "asmCtChecker: ignore declassify of the bytes of %s in %s, they \
             share the cell with bytes above"
            reg cell)
        straddling;
      declassify_cells env within

    let ty_declassify_val env (access : MemoryAccess.t) instr lty arg : Env.t =
      let bytes = Arch_utils.size_of_ltype lty in
      match Arch_utils.register_of_arg arg with
      | Some reg -> declassify_register env instr reg bytes
      | None -> (
          match arg with
          | Condt c -> declassify_cells env (Registers.condt_cells c)
          | Addr _ -> declassify_region env access instr bytes
          | _ -> env)

    let ty_declassify_mem env (access : MemoryAccess.t) instr len : Env.t =
      declassify_region env access instr (Conv.int_of_cz len)

    let ty_asmop env (access : MemoryAccess.t) op args : Env.t =
      let op_desc = Arch_utils.instr_desc op in
      let env, in_cells =
        fold_operands (input_cells args access.ac_cells) env op_desc.id_in
          op_desc.id_tin
      in
      let env, outs =
        fold_operands (outputs args access.ac_cells) env op_desc.id_out
          op_desc.id_tout
      in
      let level =
        if Arch_utils.constant_output op args then Level.Public
        else Level.join_list (List.map (Env.get env) in_cells)
      in
      List.fold_left (write_output op_desc.id_msb_flag access level) env outs

    let syscall_arg_cells o : string list =
      List.concat_map Registers.whole (Arch_utils.syscall_arg_registers o)

    let syscall_ret_cells o : string list =
      List.concat_map Registers.whole (Arch_utils.syscall_ret_registers o)

    let syscall_writes_memory : _ Syscall_t.syscall_t -> bool = function
      | Syscall_t.RandomBytes _ -> true

    let syscall_ret_level : _ Syscall_t.syscall_t -> Level.t = function
      | Syscall_t.RandomBytes _ -> Level.Public

    let ty_syscall env (access : MemoryAccess.t) o : Env.t =
      let env =
        List.fold_left Env.use_public env
          (Registers.rsp @ syscall_arg_cells o)
      in
      let regions = access.ac_cells in
      if syscall_writes_memory o && access.ac_unannotated then
        error "no annotation names the region this syscall fills";
      let clobbered =
        List.concat_map Registers.whole Syscall_clobber.names
        @ syscall_ret_cells o @ regions
      in
      let env =
        List.fold_left
          (fun env cell -> Env.set env cell Level.Secret) env clobbered
      in
      List.fold_left
        (fun env cell -> Env.set env cell (syscall_ret_level o))
        env (syscall_ret_cells o)

    let step fn_name labels ~exit accesses env i instr signatures :
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
            List.fold_left Env.use_public env
              (Registers.condt_cells c)
          in
          [ (target lbl, env); (i + 1, env) ]
      | POPPC -> [ (exit, env) ]
      | CALL (fn, _) -> (
          match Hashtbl.find_opt signatures fn.CoreIdent.fn_name with
          | Some callee -> (
              let env = List.fold_left Env.use_public env Registers.rsp in
              match Calls.call_env env callee access.ac_bindings with
              | _, Some after -> [ (i + 1, after) ]
              | demanded, None -> [ (i, demanded) ]) (* callee does not return *)
          | None ->
              error "signature not available for %s" fn.CoreIdent.fn_name)
      | _ -> error "unsupported instruction"
  end

  let arch_cells : arch_cells =
    let names = List.concat_map Registers.whole Arch_utils.arch_names in
    { names; set = SS.of_list names }

  let ty_fundef analysis (f_name, f_def) : signature option =
    let name = f_name.CoreIdent.fn_name in
    let body = Array.of_list f_def.asm_fd_body in
    let annots = Annots.of_body ~globals:analysis.globals body in
    let layout = MemLayout.of_annots (callee_layout analysis) annots in
    let accesses = MemoryAccess.resolve_all analysis.signatures layout annots in
    let cells = collect_cells arch_cells layout in
    let pre =
      init_pre_env analysis
        ~stack_frame_cells:(MemLayout.stack_frame_cells layout f_def) cells
    in
    let step ~labels ~exit i env instr =
      Instruction.step name labels ~exit accesses env i instr
        analysis.signatures
    in

    let public_levels, post = Dataflow.fixpoint ~step body pre in
    let f_sig =
      { layout;
        pre = Env.with_public pre public_levels;
        post =
          Option.map (fun post -> Env.with_public post public_levels) post }
    in
    Hashtbl.replace analysis.signatures name f_sig;
    Some f_sig

  let signatures () : analysis * (Format.formatter -> unit) list =
    let globals =
      List.fold_left
        (fun globals ((x, _), _) -> SS.add (IInfo.slot_name x) globals)
        SS.empty Program.prog.asm_glob_names
    in
    let analysis = create ~globals () in
    let errors = ref [] in
    let in_function (name : CoreIdent.funname) msg fmt : unit =
      Format.fprintf fmt "@[<v>in function %s:@,%t@]" name.CoreIdent.fn_name msg
    in
    List.iter
      (fun ((name : CoreIdent.funname), def) ->
        try ignore (ty_fundef analysis (name, def))
        with CtTypeError msg -> errors := in_function name msg :: !errors)
      (callees_first Program.prog.asm_funcs);
    (analysis, List.rev !errors)

  let chk () : unit =
    let analysis, errors = signatures () in
    let results =
      List.map
        (fun (name, _) ->
          (name.CoreIdent.fn_name,
           Hashtbl.find_opt analysis.signatures name.CoreIdent.fn_name))
        Program.prog.asm_funcs
    in
    pp_signatures arch_cells Format.err_formatter results;
    match errors with
    | [] -> ()
    | [ msg ] ->
        Utils.hierror ~loc:Utils.Lnone ~kind:"constant-time checker" "%t" msg
    | _ ->
        Utils.hierror ~loc:Utils.Lnone ~kind:"constant-time checker"
          "@[<v>%d functions rejected:@,%a@]" (List.length errors)
          (Utils.pp_list "@," (fun fmt msg -> msg fmt))
          errors
end
