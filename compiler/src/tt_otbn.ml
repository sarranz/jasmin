open Otbn_options
open Utils
module L = Location
module S = Syntax

(* -------------------------------------------------------------------- *)
(* OTBN parsing. *)

let end_flag_group s =
  if String.ends_with s "_FG0" then Some FG0
  else if String.ends_with s "_FG1" then Some FG1
  else None

let get_flag_group s =
  match end_flag_group s with
  | Some fg -> (Some fg, String.drop_end 4 s)
  | None -> (None, s)

let end_hw_writeback s =
  if String.ends_with s "_L" then Some WB_lower
  else if String.ends_with s "_U" then Some WB_upper
  else None

let get_hw_writeback s =
  match end_hw_writeback s with
  | Some wb -> (Some wb, String.drop_end 2 s)
  | None -> (None, s)

let get_otbn_opts s =
  let fg, s = get_flag_group s in
  let wb, s = get_hw_writeback s in
  (s, fg, wb)

let tt_prim err ps s sa =
  let name, ofg, owb, ows =
    match sa with
    | None ->
        let name, ofg, owb = get_otbn_opts s in
        (name, ofg, owb, None)
    | Some (Sopn.PVp ws) -> (s, None, None, Some ws)
    | _ -> raise (err "internal error in Tt_otbn.tt_prim sa")
  in
  let pv =
    match (ows, owb, ofg) with
    | Some ws, None, None -> Sopn.PV_otbn_ws ws
    | None, Some wb, None -> PV_otbn_mulqacc_so (FG0, wb)
    | None, Some wb, Some fg -> PV_otbn_mulqacc_so (fg, wb)
    | None, None, Some fg -> PV_otbn_fg fg
    | None, None, None -> PV_otbn_none
    | _, _, _ -> raise (err "internal error in Tt_otbn.tt_prim opts")
  in
  match List.assoc name ps with
  | Sopn.PrimOTBN pr -> begin
      match pr pv with
      | Ok op -> op
      | Error msg -> raise (err (String.concat "" [ " ("; msg; ")" ]))
    end
  | _ | (exception Not_found) ->
      raise (err "internal error in Tt_otbn.tt_prim assoc")
