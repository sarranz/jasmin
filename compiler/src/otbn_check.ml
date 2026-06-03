(* -------------------------------------------------------------------------- *)
(* OTBN  has two fixed-size hardware stacks that must not overflow:
   - a loop stack of depth 8, used by the LOOP/LOOPI instructions that
     implement [repeat] loops; and
   - a call stack of depth 8, used by JAL/return to save return addresses.

   This pass rejects programs whose nesting of [repeat] loops or whose depth of
   (non-inlined) calls would exceed those limits.
   It is an overapproximation in some cases, so it may fail for valid programs.
   It is an underapproximation for system calls: it assumes that they don't make
   further calls or have loops.

   The analysis can be tuned with annotations:
   - [assume_loop_depth=N] / [assume_call_depth=N], on a function or on an
     instruction, make the analysis use [N] directly, without inspecting the
     body of the function or the components of the instruction.  They are a way
     to work around the overapproximation, or to account for behaviour that the
     analysis cannot see.
   - [check_max_loop_depth=N] / [check_max_call_depth=N], on a function,
     replace -- for that function only -- the default maximum of 8 by [N]. *)

open Utils
open Prog

let max_depth = 8

(* -------------------------------------------------------------------------- *)
(* [check] is shared by the loop-stack and the call-stack analyses; they only
   differ in the annotation keys, the per-instruction contribution [usage], and
   the error message.

   [usage usage_c callee_depth i] is the depth contributed by instruction [i],
   given [usage_c] (the depth of a sub-command) and [callee_depth] (the depth
   already computed for a callee). *)
let check ~assume_key ~max_key ~error ~usage funcs =
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
    Annot.get_pos_int_annot assume_key i.i_annot
    |> Option.default (usage usage_c callee_depth i)
  in
  let check_fd fd =
    let annot = fd.f_annot.f_user_annot in
    let d =
      Annot.get_pos_int_annot assume_key annot
      |> Option.default (usage_c fd.f_body)
    in
    let limit =
      Annot.get_pos_int_annot max_key annot |> Option.default max_depth
    in
    if d > limit then
      hierror ~loc:(Lone fd.f_loc) ~funname:fd.f_name.fn_name
        ~kind:"OTBN hardware limit" "%s" (error d limit);
    Hf.add depths fd.f_name d
  in
  List.iter check_fd funcs

(* -------------------------------------------------------------------------- *)
let check_loops funcs =
  let usage usage_c callee_depth i =
    match i.i_desc with
    | Cfor (FIrepeat _, c) -> 1 + usage_c c
    | Cfor (FIrange _, c) -> usage_c c
    | Cif (_, c1, c2) | Cwhile (_, c1, _, _, c2) ->
        max (usage_c c1) (usage_c c2)
    | Ccall (_, fn, _) -> callee_depth fn
    | Cassgn _ | Copn _ | Csyscall _ | Cassert _ -> 0
  in
  let error d limit =
    Printf.sprintf
      "repeat loops reach a nesting depth of %d, but the maximum loop nesting \
       depth is %d"
      d limit
  in
  check ~assume_key:"assume_loop_depth" ~max_key:"check_max_loop_depth" ~error
    ~usage funcs

(* -------------------------------------------------------------------------- *)
let check_calls funcs =
  let usage usage_c callee_depth i =
    match i.i_desc with
    | Ccall (_, fn, _) -> 1 + callee_depth fn
    | Csyscall _ -> 1
    | Cif (_, c1, c2) | Cwhile (_, c1, _, _, c2) ->
        max (usage_c c1) (usage_c c2)
    | Cfor (_, c) -> usage_c c
    | Cassgn _ | Copn _ | Cassert _ -> 0
  in
  let error d limit =
    Printf.sprintf "calls are nested %d deep, but the maximum call depth is %d"
      d limit
  in
  check ~assume_key:"assume_call_depth" ~max_key:"check_max_call_depth" ~error
    ~usage funcs

(* -------------------------------------------------------------------------- *)
let check_prog ((funcs, _) : (_, _) sprog) =
  let funcs = List.rev funcs |> List.map snd in
  check_loops funcs;
  check_calls funcs
