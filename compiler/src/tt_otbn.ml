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
    | _ -> raise (err "unsupported size suffix")
  in
  match List.assoc name ps with
  | Sopn.PrimOTBN pr -> begin
      let pv =
        { Sopn.otbn_suff_ws = ows; otbn_suff_fg = ofg; otbn_suff_wb = owb }
      in
      match pr pv with
      | Ok op -> op
      | Error msg -> raise (err msg)
    end
  | _ | (exception Not_found) ->
      raise (err "unknown mnemonic or invalid suffix")
