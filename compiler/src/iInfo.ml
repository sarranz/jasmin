open Iinfo_types

type t = Location.i_loc * Annotations.annotations
let dummy = Location.i_dummy, []
let with_location (l, _) = (l, [])
let is_inline (_, annot) = Annotations.has_symbol "inline" annot
let var_info_of_ii (l, _) = Location.(l.base_loc)

let slot_name : Var0.Var.var -> string =
  (* Short display names for slot variables: a variable is printed as its
     source name when possible; distinct variables sharing a source name get
     [name.1], [name.2], ... in order of first appearance. *)
  let slot_name_tbl : (string, string) Hashtbl.t = Hashtbl.create 17 in
  let seen_slot_names : (string, unit) Hashtbl.t = Hashtbl.create 17 in
  fun x ->
    let name = x.Var0.Var.vname in
    let key = CoreIdent.string_of_uid name.v_id in
    try Hashtbl.find slot_name_tbl key
    with Not_found ->
      let rec fresh i =
        let cand =
          if i = 0 then name.v_name
          else Format.sprintf "%s.%d" name.v_name i
        in
        if Hashtbl.mem seen_slot_names cand then fresh (i + 1) else cand
      in
      let s = fresh 0 in
      Hashtbl.add seen_slot_names s ();
      Hashtbl.add slot_name_tbl key s;
      s

(* A whole slot is the region [(name, size)]; element [i] of a fine-grained
   array slot is the region [(name[i], element size)]. *)
let process_si (si : ii_slot_info) : Annotations.region =
  match si with
  | SIregion (x, size) ->
      { Annotations.r_name = slot_name x; r_size = CoreConv.z_of_cz size }
  | SIelem (x, i, size) ->
      let name =
        Format.sprintf "%s[%s]" (slot_name x) (Z.to_string (CoreConv.z_of_cz i))
      in
      { Annotations.r_name = name; r_size = CoreConv.z_of_cz size }

let add_array_annot (rs : ii_mem_annot) ((l, annot) : t) : t =
  let regions = List.map process_si rs in
  if regions = [] then (l, annot)
  else (l, Annotations.add_array_annot ~loc:Location.(l.base_loc) regions annot)

let add_instantiation_annot (inst : ii_inst_annot) ((l, annot) : t) : t =
  let inst =
    List.map
      (fun i -> (process_si i.inst_callee, List.map process_si i.inst_caller))
      inst
  in
  (l, Annotations.add_instantiation_annot ~loc:Location.(l.base_loc) inst annot)

let allocate_stack_frame ((l, annot) : t) : t =
  (l, Annotations.remove_symbol Annotations.instantiation_annot annot)
