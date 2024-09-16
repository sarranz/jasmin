type data_kind = DKWord | DKByte

type asm_line =
  | LLabel of string
  | LInstr of string * string list
  | LData of data_kind * string

val lbyte : string -> asm_line
val lword : string -> asm_line

val print_asm_lines : Format.formatter -> asm_line list -> unit

val format_glob_data_entry :
  string -> int -> string option -> data_kind -> string -> asm_line list

val format_glob_data :
  string ->
  Obj.t list ->
  ((Var0.Var.var * 'a) * BinNums.coq_Z) list ->
  asm_line list

val string_of_label : string -> Label.label -> string
