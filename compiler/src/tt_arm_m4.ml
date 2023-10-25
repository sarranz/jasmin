open Utils

module L = Location
module S = Syntax

(* -------------------------------------------------------------------- *)
(* ARM parsing. *)

let get_set_flags s =
  if String.ends_with s "S" then (true, String.drop_end 1 s) else (false, s)

let get_is_conditional s =
  if String.ends_with s "cc" then (true, String.drop_end 2 s) else (false, s)

let get_arm_prim s =
  let is_conditional, s = get_is_conditional s in
  let set_flags, s = get_set_flags s in
  (s, set_flags, is_conditional)

let tt_prim ~unknown ps s sa =
  if Option.is_some sa then raise unknown;
  let name, set_flags, is_conditional = get_arm_prim s in
  match List.assoc name ps with
  | Sopn.PrimARM pr -> pr set_flags is_conditional
  | _ | exception Not_found -> raise unknown
