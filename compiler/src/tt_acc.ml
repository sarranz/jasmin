open Acc_options
open Utils
module L = Location
module S = Syntax

(* -------------------------------------------------------------------- *)
(* ACC parsing. *)

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

let get_wreg s =
  let n = String.length s in
  if n >= 4 && s.[n-4] = '_' && s.[n-3] = 'w' then
    let c1 = Char.code s.[n-2] - Char.code '0' in
    let c2 = Char.code s.[n-1] - Char.code '0' in
    if c1 >= 0 && c1 <= 3 && c2 >= 0 && c2 <= 9 then
      let idx = c1 * 10 + c2 in
      if idx <= 31 then (Some idx, String.sub s 0 (n-4))
      else (None, s)
    else (None, s)
  else (None, s)

let get_acc_opts s =
  let fg, s = get_flag_group s in
  let wb, s = get_hw_writeback s in
  let wr, s = get_wreg s in
  (s, fg, wb, wr)

let tt_prim err ps s sa =
  let name, ofg, owb, ows, owr =
    match sa with
    | None ->
        let name, ofg, owb, owr = get_acc_opts s in
        (name, ofg, owb, None, owr)
    | Some (Sopn.PVp ws) -> (s, None, None, Some ws, None)
    | _ -> raise (err "unsupported size suffix") (* TODO_OTBN: should be an error *)
  in
  match List.assoc name ps with
  | Sopn.PrimACC pr -> begin
      let pv =
        match ows, ofg, owb, owr with
        | Some ws, None,    None,    None    -> Sopn.PrimACCws ws
        | None,    _,       Some wb, None    -> Sopn.PrimACCwb (ofg, wb)
        | None,    Some fg, None,    None    -> Sopn.PrimACCfg fg
        | None,    None,    None,    Some i  -> Sopn.PrimACCwreg (Conv.nat_of_int i)
        | None,    None,    None,    None    -> Sopn.PrimACCnone
        | _ -> raise (err "invalid combination of suffixes") (* TODO_OTBN: should be an error *)
      in
      match pr pv with
      | Ok op -> op
      | Error msg -> raise (err msg)
    end
  | _ | (exception Not_found) ->
      raise (err "unknown mnemonic or invalid suffix") (* TODO_OTBN: should be an error *)
