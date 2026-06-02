(* -------------------------------------------------------------------------- *)
(* OTBN  has two fixed-size hardware stacks that must not overflow:
   - a loop stack of depth 8, used by the LOOP/LOOPI instructions that
     implement [repeat] loops; and
   - a call stack of depth 8, used by JAL/return to save return addresses.

   This pass rejects programs whose nesting of [repeat] loops or whose depth of
   (non-inlined) calls would exceed those limits.
   It is an overapproximation in some cases, so it may fail for valid programs.
   It is an underapproximation for system calls: it assumes that they don't make
   further calls or have loops. *)

open Utils
open Prog

let max_depth = 8

(* -------------------------------------------------------------------------- *)
let check_loops funcs =
  let depths = Hf.create 17 in
  let callee_depth fn =
    try Hf.find depths fn
    with Not_found ->
      hierror ~loc:Lnone ~kind:"compilation error" ~internal:true
        "callee %s has not been analysed before its caller; the function list \
         is not ordered callees-before-callers"
        fn.fn_name
  in
  let rec usage_c c = List.fold_left (fun acc i -> max acc (usage_i i)) 0 c
  and usage_i i =
    match i.i_desc with
    | Cfor (FIrepeat _, c) -> 1 + usage_c c
    | Cfor (FIrange _, c) -> usage_c c
    | Cif (_, c1, c2) | Cwhile (_, c1, _, _, c2) ->
        max (usage_c c1) (usage_c c2)
    | Ccall (_, fn, _) -> callee_depth fn
    | Cassgn _ | Copn _ | Csyscall _ | Cassert _ -> 0
  in
  List.iter
    (fun fd ->
      let d = usage_c fd.f_body in
      if d > max_depth then
        hierror ~loc:(Lone fd.f_loc) ~funname:fd.f_name.fn_name
          ~kind:"OTBN hardware limit"
          "repeat loops reach a nesting depth of %d, but the OTBN hardware \
           loop stack only supports a nesting depth of %d"
          d max_depth;
      Hf.add depths fd.f_name d)
    funcs

(* -------------------------------------------------------------------------- *)
let check_calls funcs =
  let depths = Hf.create 17 in
  let callee_depth fn =
    try Hf.find depths fn
    with Not_found ->
      hierror ~loc:Lnone ~kind:"compilation error" ~internal:true
        "callee %s has not been analysed before its caller; the function list \
         is not ordered callees-before-callers"
        fn.fn_name
  in
  let rec usage_c c = List.fold_left (fun acc i -> max acc (usage_i i)) 0 c
  and usage_i i =
    match i.i_desc with
    | Ccall (_, fn, _) -> 1 + callee_depth fn
    | Csyscall _ -> 1
    | Cif (_, c1, c2) | Cwhile (_, c1, _, _, c2) ->
        max (usage_c c1) (usage_c c2)
    | Cfor (_, c) -> usage_c c
    | Cassgn _ | Copn _ | Cassert _ -> 0
  in
  List.iter
    (fun fd ->
      let d = usage_c fd.f_body in
      if d > max_depth then
        hierror ~loc:(Lone fd.f_loc) ~funname:fd.f_name.fn_name
          ~kind:"OTBN hardware limit"
          "calls are nested %d deep, but the OTBN hardware call stack only \
           supports a nesting depth of %d"
          d max_depth;
      Hf.add depths fd.f_name d)
    funcs

(* -------------------------------------------------------------------------- *)
let check_prog ((funcs, _) : (_, _) sprog) =
  let funcs = List.rev funcs |> List.map snd in
  check_loops funcs;
  check_calls funcs
