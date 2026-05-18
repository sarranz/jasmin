type t = Location.i_loc * Annotations.annotations
let dummy = Location.i_dummy, []
let with_location (l, _) = (l, [])
let is_inline (_, annot) = Annotations.has_symbol "inline" annot
let var_info_of_ii (l, _) = Location.(l.base_loc)

let instance : (VInfo.t, t) Info.coq_InstrInfo =
  {
    Info.dummy_instr_info = dummy;
    Info.ii_with_location = with_location;
    Info.ii_is_inline = is_inline;
    Info.var_info_of_ii;
  }
