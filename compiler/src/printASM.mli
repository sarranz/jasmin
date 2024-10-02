type asm_line =
  | LLabel of string
  | LInstr of string * string list
  | LByte of string

val print_asm_lines : Format.formatter -> asm_line list -> unit

val byte_label : string -> Z.t -> string

val format_glob_data :
  string ->
  Obj.t list ->
  ((Var0.Var.var * 'a) * BinNums.coq_Z) list ->
  asm_line list

val string_of_label : string -> Label.label -> string
