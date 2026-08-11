(* -------------------------------------------------------------------- *)
type symbol = string
type pident = symbol Location.located

(* -------------------------------------------------------------------- *)
type wsize = Wsize.wsize

let int_of_ws = function
  | Wsize.U8 -> 8
  | U16  -> 16
  | U32  -> 32
  | U64  -> 64
  | U128 -> 128
  | U256 -> 256

let string_of_ws ws = Format.sprintf "u%i" (int_of_ws ws)

(* -------------------------------------------------------------------- *)
type simple_attribute =
  | Aint    of Z.t
  | Aid     of symbol
  | Astring of string
  | Aws     of wsize
  | Astruct of annotations

and attribute = simple_attribute Location.located

and annotation = pident * attribute option

and annotations = annotation list

let get (s: string) (annot: annotations) =
  match
    List.find_opt (fun (k, _) -> String.equal (Location.unloc k) s) annot
  with
  | Some (_, a) -> Some a
  | None -> None

let has_symbol s annot =
  List.exists (fun (k, _) -> String.equal (Location.unloc k) s) annot

let add_symbol ~loc s annot =
  if has_symbol s annot
  then annot
  else (Location.mk_loc loc s, None) :: annot

(* -------------------------------------------------------------------- *)
(* Records, on an instruction built by the stack allocation pass out of a
   memory access, the set of per-byte names of the slot bytes the access
   uses: a slot [s] of N bytes yields the names [s_0], ..., [s_(N-1)]. *)
let array_annot = "Internal::array"

let has_array_annot annot = has_symbol array_annot annot

let add_array_annot ~loc (names : string list) annot =
  if has_array_annot annot
  then annot
  else
    let mk d = Location.mk_loc loc d in
    (mk array_annot,
     Some (mk (Astruct (List.map (fun n -> (mk n, None)) names))))
    :: annot

let get_array_annot (annot : annotations) : string list option =
  match get array_annot annot with
  | Some (Some { Location.pl_desc = Astruct l; _ }) ->
      Some (List.map (fun (k, _) -> Location.unloc k) l)
  | _ -> None

(* -------------------------------------------------------------------- *)
(* Records, on a function, the layout of its stack frame as computed by the
   stack allocation pass: each stack slot (local variable, local stack array,
   stack-pointer cell) is mapped to the range [offset, offset + size) it
   occupies relative to the stack pointer. *)
let stack_frame_annot = "Internal::stack_frame"

let has_stack_frame_annot annot = has_symbol stack_frame_annot annot

let add_stack_frame_annot ~loc (slots : (string * (Z.t * Z.t)) list) annot =
  if has_stack_frame_annot annot
  then annot
  else
    let mk d = Location.mk_loc loc d in
    let mk_int z = Some (mk (Aint z)) in
    let mk_slot (name, (ofs, size)) =
      (mk name,
       Some (mk (Astruct [ (mk "offset", mk_int ofs);
                           (mk "size", mk_int size) ])))
    in
    (mk stack_frame_annot, Some (mk (Astruct (List.map mk_slot slots))))
    :: annot

let get_stack_frame_annot (annot : annotations) :
    (string * (Z.t * Z.t)) list option =
  let get_int a k =
    match get k a with
    | Some (Some { Location.pl_desc = Aint z; _ }) -> Some z
    | _ -> None
  in
  let decode_slot (k, a) =
    match a with
    | Some { Location.pl_desc = Astruct s; _ } ->
      (match get_int s "offset", get_int s "size" with
       | Some ofs, Some size -> Some (Location.unloc k, (ofs, size))
       | _ -> None)
    | _ -> None
  in
  match get stack_frame_annot annot with
  | Some (Some { Location.pl_desc = Astruct slots; _ }) ->
    Some (List.filter_map decode_slot slots)
  | _ -> None

(* -------------------------------------------------------------------- *)
let sint = "Internal::wint::signed"
let uint = "Internal::wint::unsigned"

let has_sint annot = has_symbol sint annot
let has_uint annot = has_symbol uint annot

let is_wint (k, _) =
  let s = Location.unloc k in
  String.equal s sint || String.equal s uint

let remove_wint annot = List.filter (fun x -> not (is_wint x)) annot

let has_wint annot =
  BatList.find_map_opt (fun (k, _) ->
    let s = Location.unloc k in
    if String.equal s sint then Some Wsize.Signed
    else if String.equal s uint then Some Unsigned
    else None) annot
