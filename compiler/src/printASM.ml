open Utils
open Prog
open PrintCommon

type data_kind = DKWord | DKByte

let pp_data_kind fmt = function
  | DKWord -> Format.fprintf fmt "word"
  | DKByte -> Format.fprintf fmt "byte"

(** Assembly code lines. *)
type asm_line =
  | LLabel of string
  | LInstr of string * string list
  | LData of data_kind * string

let lbyte b = LData(DKByte, b)
let lword w = LData(DKWord, w)

let iwidth = 4

let print_asm_line fmt ln =
  match ln with
  | LLabel lbl -> Format.fprintf fmt "%s:" lbl
  | LInstr (s, []) -> Format.fprintf fmt "\t%s" s
  | LInstr (s, args) ->
      Format.fprintf fmt "\t%-*s\t%s" iwidth s (String.concat ", " args)
  | LData(k, n) -> Format.fprintf fmt "\t.%a\t%s" pp_data_kind k n

let print_asm_lines fmt lns =
  List.iter (Format.fprintf fmt "%a\n%!" print_asm_line) lns

(* -------------------------------------------------------------------- *)
let string_of_label name p =
  Format.asprintf "L%s$%d" (escape name) (Conv.int_of_pos p)

let string_of_glob x =
  Format.asprintf "G$%s" (escape x.v_name)

let byte_label global_datas i =
  Format.asprintf "%s_%s" global_datas (string_of_int i)

(* -------------------------------------------------------------------- *)
let format_glob_data_entry global_datas i olabel dk b =
  let lbl =
    match olabel with
    | Some x -> [ LLabel x ]
    | None -> []
  in
  lbl @ [ LLabel(byte_label global_datas i); LData(dk, b) ]

let format_glob_data global_datas globs names =
  let names =
    List.map (fun ((x, _), p) -> (Conv.var_of_cvar x, Conv.z_of_cz p)) names
  in
  let doit i b =
    let olabel =
      match List.find (fun (_, p) -> Z.equal p (Z.of_int i)) names with
      | x, _ -> Some (string_of_glob x)
      | exception Not_found -> None
    in
    let b = Conv.z_of_int8 b |> Z.to_string in
    format_glob_data_entry global_datas i olabel DKByte b
  in
  List.flatten (List.mapi doit globs)
