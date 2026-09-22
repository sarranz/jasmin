open Utils

type asm_element =
| Header of string * string list
| Label of string
| Dwarf of string (* Debug info in std dwarf format*)
| Instr of string * string list
| Comment of string
| Bytes of string list
| ArrAnnot of Annotations.region list
| InstAnnot of (Annotations.region * Annotations.region list) list

let iwidth = 4

type asm = asm_element list

let pp_header fmt name params =
  match params with
  | [] -> Format.fprintf fmt "\t%s" name
  | _ ->  Format.fprintf fmt "\t%-*s\t%s" iwidth name (String.concat ", " params)

let pp_label fmt name =
  Format.fprintf fmt "%s:" name

let pp_instr fmt name params =
  match params with
  | [] -> Format.fprintf fmt "\t%s" name (* In case there is no params, we do not print a tab*)
  | _ ->  Format.fprintf fmt "\t%-*s\t%s" iwidth name (String.concat ", " params)

let pp_comment fmt comment =
  Format.fprintf fmt "// %s" comment

let pp_bytes fmt =
  List.iteri (fun i byte ->
      let pfx = i mod 16 == 0 in
      Format.fprintf fmt "%s%s%s"
        (if pfx && i > 0 then "\n" else "")
        (if pfx then "\t.byte\t" else ", ")
        byte
    )

let pp_dwarf fmt (dwarf: string) =
  Format.fprintf fmt "\t%s" dwarf

(* A memory region annotation: [(name, size in bytes)]. *)
let string_of_region (r : Annotations.region) =
  Printf.sprintf "(%s, %s)" r.Annotations.r_name (Z.to_string r.Annotations.r_size)

let pp_asm_element fmt asm_element =
  match asm_element with
  | Header (name, params) ->
    pp_header fmt name params
  | Label name ->
    pp_label fmt name
  | Dwarf locs ->
    pp_dwarf fmt locs
  | Instr (name, params) ->
    pp_instr fmt name params
  | Comment content ->
    pp_comment fmt content
  | Bytes data ->
    pp_bytes fmt data
  | ArrAnnot regions ->
    pp_comment fmt (String.concat " " (List.map string_of_region regions))
  | InstAnnot insts ->
    let string_of_callers = function
      | [ caller ] -> string_of_region caller
      | callers ->
        Printf.sprintf "{%s}"
          (String.concat " " (List.map string_of_region callers))
    in
    let inst_str =
      List.map
        (fun (callee, callers) ->
          Printf.sprintf "%s<-%s" (string_of_region callee)
            (string_of_callers callers))
        insts
    in
    pp_comment fmt (String.concat ", " inst_str)

let needs_newline = function
  | ArrAnnot _ | InstAnnot _ -> false
  | _ -> true

let pp_asm_line fmt l =
  let nl = if needs_newline l then "\n" else " " in
  Format.fprintf fmt "%s%a%!" nl pp_asm_element l

let pp_asm fmt asm =
  List.iter (pp_asm_line fmt) asm;
  Format.fprintf fmt "\n%!"

