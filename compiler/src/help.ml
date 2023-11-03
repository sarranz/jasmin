open Pretyping

let show_intrinsics asmOp fmt =
  let index =
    let open Sopn in
    function
    | PrimX86 (sfx, _) ->
      begin match sfx with
      | [] -> 0
      | PVp _ :: _ -> 1
      | PVx _ :: _ -> 2
      | (PVv _ | PVsv _) :: _ -> 3
      | PVvv _ :: _ -> 4
      end
    | PrimARM _ -> 5
    | PrimOTBN_none _ -> 0
    | PrimOTBN_ws _ -> 1
    | PrimOTBN_fg _ -> 6
    | PrimOTBN_mulqacc_so _ -> 7
  in
  let headers = [|
      "no size suffix";
      "one optional size suffix, e.g., “_64”";
      "a zero/sign extend suffix, e.g., “_u32u16”";
      "one vector description suffix, e.g., “_4u64”";
      "two vector description suffixes, e.g., “_2u16_2u64”";
      "a flag setting suffix (i.e. “S”) and a condition suffix (i.e. “cc”)";
      "a flag group (i.e. \"_FG0\" or \"_FG1\")";
      "a halfword selector (i.e. \"_L\" or \"_U\") and then a flag group";
    |] in
  let intrinsics = Array.make (Array.length headers) [] in
  List.iter (fun (n, i) ->
      let j = index i in
      intrinsics.(j) <- n :: intrinsics.(j))
    (prim_string asmOp);
  Array.iter2 (fun h m ->
      Format.fprintf fmt "Intrinsics accepting %s:@." h;
      m |>
      List.sort String.compare |>
      List.iter (Format.fprintf fmt " - %s@.");
      Format.fprintf fmt "@."
    ) headers intrinsics

let show_intrinsics asmOp () =
  show_intrinsics asmOp Format.std_formatter
