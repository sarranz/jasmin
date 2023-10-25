open Prog
open Utils

let hierror = hierror ~kind:"compilation error" ~sub_kind:"SSA"

type names = var Mv.t

let rename_expr (m: names) (e: expr) : expr = Subst.vsubst_e m e

let fresh_name ~dloc (m: names) (x: var) : var * names =
  let y = V.clone ~dloc x in
  y, Mv.add x y m

let rename_lval (allvars: bool) ((m, xs): names * lval list) : lval -> names * lval list =
  function
  | Lvar x when allvars || is_reg_kind (L.unloc x).v_kind ->
    let y, m = fresh_name ~dloc:(L.loc x) m (L.unloc x) in
    m, Lvar (L.mk_loc (L.loc x) y) :: xs
  | x -> m, Subst.vsubst_lval m x :: xs

let rename_lvals allvars (m: names) (xs: lval list) : names * lval list =
  let m, ys = List.fold_left (rename_lval allvars) (m, []) xs in
  m, List.rev ys

let written_vars_lvar allvars (w: Sv.t) =
  function
  | Lvar x when allvars || is_reg_kind (L.unloc x).v_kind ->
    Sv.add (L.unloc x) w
  | _ -> w

let written_vars_lvars allvars = List.fold_left (written_vars_lvar allvars)

let rec written_vars_instr_r allvars w =
  function
  | Cfor (FIrepeat _, s) -> written_vars_stmt allvars w s
  | Cfor (FIrange _, _) -> assert false
  | Cassgn (x, _, _, _) -> written_vars_lvar allvars w x
  | Copn (xs, _, _, _)
  | Csyscall(xs,_,_)
  | Ccall (_, xs, _, _)
    -> written_vars_lvars allvars w xs
  | Cif (_, s1, s2)
  | Cwhile (_, s1, _, s2)
    -> written_vars_stmt allvars (written_vars_stmt allvars w s1) s2
and written_vars_instr allvars w { i_desc } = written_vars_instr_r allvars w i_desc
and written_vars_stmt allvars w s = List.fold_left (written_vars_instr allvars) w s

(* Adds rename intruction y = m[x] *)
let ir (m: names) (x: var) (y: var) : (unit, 'asm) instr =
  let x = Mv.find_default x x m in
  let v u = L.mk_loc L._dummy u in
  let i_desc = Cassgn (Lvar (v y), AT_phinode, y.v_ty, Pvar (gkvar (v x))) in
  { i_desc ; i_info = () ; i_loc = L.i_dummy ; i_annot = [] }

(* Issue assignments [x = m[x]] for each [x] in both [written] and [needed]. *)
let slr_tail written needed m m' =
  let f x acc =
    if Sv.mem x needed
    then let y = Mv.find_default x x m in ir m' x y :: acc
    else acc
  in
  Sv.fold f written []

let split_live_ranges (allvars: bool) (f: ('info, 'asm) func) : (unit, 'asm) func =
  let f = Liveness.live_fd false f in
  let rec instr_r i_loc (li: Sv.t) (lo: Sv.t) (m: names) =
    function
    | Cassgn (x, tg, ty, e) ->
      let e = rename_expr m e in
      let m, y = rename_lval allvars (m, []) x in
      m, Cassgn (List.hd y, tg, ty, e)
    | Copn (xs, tg, op, es) ->
      let es = List.map (rename_expr m) es in
      let m, ys = rename_lvals allvars m xs in
      m, Copn (ys, tg, op, es)
    | Csyscall (xs, op, es) ->
      let es = List.map (rename_expr m) es in
      let m, ys = rename_lvals allvars m xs in
      m, Csyscall(ys, op, es)
    | Ccall (ii, xs, n, es) ->
      let es = List.map (rename_expr m) es in
      let m, ys = rename_lvals allvars m xs in
      m, Ccall (ii, ys, n, es)
    | Cif (e, s1, s2) ->
      let os = written_vars_stmt allvars (written_vars_stmt allvars Sv.empty s1) s2 in
      let e = rename_expr m e in
      let m1, s1 = stmt m s1 in
      let m2, s2 = stmt m s2 in
      let m, tl1, tl2 =
        Sv.fold (fun x ((m, tl1, tl2) as n) ->
            if Sv.mem x lo
            then
              let y, m = fresh_name ~dloc:i_loc.L.base_loc m x in
              m, ir m1 x y :: tl1, ir m2 x y :: tl2
            else n
          ) os (m, [], [])
      in
      m, Cif (e, s1 @ tl1, s2 @ tl2)
    | Cfor (FIrepeat e, c) ->
      let os = written_vars_stmt allvars Sv.empty c in
      let e = rename_expr m e in
      let m', c = stmt m c in
      let tl = slr_tail os li m m' in
      m, Cfor (FIrepeat e, c @ tl)
    | Cfor (FIrange _, _) -> assert false
    | Cwhile (a, s1, e, s2) ->
      let os = written_vars_stmt allvars (written_vars_stmt allvars Sv.empty s1) s2 in
      let m1, s1 = stmt m s1 in
      let e = rename_expr m1 e in
      let m2, s2 = stmt m1 s2 in
      let tl2 = slr_tail os li m m2 in
      m1, Cwhile (a, s1, e, s2 @ tl2)
  and instr (m, tl) i =
    let { i_desc ; i_info = (li, lo) ; i_loc ; _ } = i in
    let m, i_desc = instr_r i_loc li lo m i_desc in
    m, { i with i_info = () ; i_desc } :: tl
  and stmt m s =
    let m, s = List.fold_left instr (m, []) s in
    m, List.rev s
  in
  let m, f_body = stmt Mv.empty f.f_body in
  let f_ret = List.map (Subst.vsubst_vi m) f.f_ret in
  { f with f_body ; f_ret }

let remove_phi_nodes (f: ('info, 'asm) func) : ('info, 'asm) func =
  let rec instr_r =
    function
    | Cassgn (x, tg, _, e) as i ->
      (match tg with
       | AT_phinode ->
         (match x, e with
          | Lvar v, Pvar v' when is_gkvar v' ->
            if L.unloc v = L.unloc v'.gv then None else
              let pv = Printer.pp_var ~debug:true in
              hierror ~loc:Lnone ~funname:f.f_name.fn_name ~internal:true
                "cannot remove assignment %a = %a"
                pv (L.unloc v) pv (L.unloc v'.gv)
          | _, _ -> Some i)
       | _ -> Some i)
    | Cif (b, s1, s2) -> Some (Cif (b, stmt s1, stmt s2))
    | Cwhile (a, s1, b, s2) -> Some (Cwhile (a, stmt s1, b, stmt s2))
    | Cfor (fi, c) -> Some (Cfor (fi, stmt c))
    | (Copn _ | Csyscall _ | Ccall _) as i -> Some i
  and instr i =
    try Option.map (fun i_desc -> { i with i_desc }) (instr_r i.i_desc)
    with HiError e -> raise (HiError (add_iloc e i.i_loc))
  and stmt s = List.filter_map instr s in
  let f_body = stmt f.f_body in
  { f with f_body }
