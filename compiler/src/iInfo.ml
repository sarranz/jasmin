type t = Location.i_loc * Annotations.annotations
let dummy = Location.i_dummy, []
let with_location (l, _) = (l, [])
let is_inline (_, annot) = Annotations.has_symbol "inline" annot
let var_info_of_ii (l, _) = Location.(l.base_loc)

(* Short display names for slot variables: a variable is printed as its
   source name when possible; distinct variables sharing a source name get
   [name.1], [name.2], ... in order of first appearance. *)
let slot_name_tbl : (string, string) Hashtbl.t = Hashtbl.create 17
let seen_slot_names : (string, unit) Hashtbl.t = Hashtbl.create 17

let slot_name (x : Var0.Var.var) : string =
  let name = x.Var0.Var.vname in
  let key = CoreIdent.string_of_uid name.v_id in
  match Hashtbl.find_opt slot_name_tbl key with
  | Some s -> s
  | None ->
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

(* Expand each accessed byte range [ofs, ofs + len) of a slot [s] into the
   per-byte names [s[ofs]], ..., [s[ofs+len-1]]. *)
let add_array_annot
    (rs : (Var0.Var.var * (BinNums.coq_Z * BinNums.coq_Z)) list)
    ((l, annot) : t) : t =
  let bytes (x, (ofs, len)) =
    let len = Z.max Z.zero (CoreConv.z_of_cz len) in
    if len > Z.of_int 10000 then failwith "slot too large"
    else
      let base = slot_name x in
      let ofs = CoreConv.z_of_cz ofs in
      List.init (Z.to_int len) (fun i -> (base, Z.add ofs (Z.of_int i)))
  in
  let names =
    List.concat_map bytes rs
    |> List.sort_uniq (fun (b1, o1) (b2, o2) ->
           match String.compare b1 b2 with 0 -> Z.compare o1 o2 | c -> c)
    |> List.map (fun (b, o) -> Format.sprintf "%s[%s]" b (Z.to_string o))
  in
  if names = [] then (l, annot)
  else (l, Annotations.add_array_annot ~loc:Location.(l.base_loc) names annot)
