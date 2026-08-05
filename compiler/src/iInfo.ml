type t = Location.i_loc * Annotations.annotations
let dummy = Location.i_dummy, []
let with_location (l, _) = (l, [])
let is_inline (_, annot) = Annotations.has_symbol "inline" annot
let var_info_of_ii (l, _) = Location.(l.base_loc)

let add_array_annot (x : Var0.Var.var) ((l, annot) : t) : t =
  let name = x.Var0.Var.vname in
  let arr = name.v_name ^ "_" ^ CoreIdent.string_of_uid name.v_id in
  (l, Annotations.add_array_annot ~loc:Location.(l.base_loc) arr annot)
