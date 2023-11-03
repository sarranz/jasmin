open Otbn_options

open Utils

module L = Location
module S = Syntax

(* -------------------------------------------------------------------- *)
(* OTBN parsing. *)

let get_flag_group s =
  if String.ends_with s "_FG0"
  then (Some FG0, String.drop_end 4 s)
  else
    if String.ends_with s "_FG1"
    then (Some FG1, String.drop_end 4 s)
    else (None, s)

let get_hw_writeback s =
  if String.ends_with s "_L"
  then (Some WB_lower, String.drop_end 2 s)
  else
    if String.ends_with s "_U"
    then (Some WB_upper, String.drop_end 2 s)
    else (None, s)

let get_otbn_opts s =
  let fg, s = get_flag_group s in
  let wb, s = get_hw_writeback s in
  (s, fg, wb)

let tt_prim ~unknown ps s sa =
  let name, ofg, owb, ows =
    match sa with
    | None -> let name, ofg, owb = get_otbn_opts s in name, ofg, owb, None
    | Some (Sopn.PVp ws) -> s, None, None, Some ws
    | _ -> raise unknown
  in
  let fg = Option.default FG0 ofg in
  match List.assoc name ps with
  | Sopn.PrimOTBN_none op -> op
  | PrimOTBN_ws pr -> pr (oget ~exn:unknown ows)
  | PrimOTBN_fg pr -> pr fg
  | PrimOTBN_mulqacc_so pr -> pr fg (oget ~exn:unknown owb)
  | _ | exception Not_found -> raise unknown
