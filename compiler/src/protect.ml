open Prog

let protect_loc (mk_protect : 'a Slh_gen.mk_protectT) (p : (unit, 'asm) prog)
    (loc : Location.t) : (unit, 'asm) prog =
  let globals, fns = p in
  let rec process_fbody (func : (unit, _) func) (fname : funname)
      (f_body : (unit, _) stmt) : (unit, _) stmt =
    match f_body with
    | [] -> f_body
    | hd :: tl ->
        if fst loc.loc_start == fst hd.i_loc.base_loc.loc_start then
          let _ =
            Format.printf "locyayy: %a %a@." Location.pp_loc loc Location.pp_loc
              hd.i_loc.base_loc
          in
          match hd.i_desc with
          | Cassgn (Laset (_, _, wsize, _, expr), _, ty, e) ->
              Format.printf "index : %a@." (Printer.pp_expr ~debug:false) expr;
              let dumm = Sv.to_list (vars_e expr) in
              let print var =
                Format.printf "var1: %a@." (Printer.pp_var ~debug:false) var
              in
              let _ = List.map print dumm in
              let protect_var v : (unit, _) stmt =
                gkvar (L.mk_loc L._dummy v)
                |> mk_protect fname (L.refresh_i_loc hd.i_loc)
              in
              let append_protect = List.concat_map protect_var dumm in
              append_protect @ (hd :: tl)
          | _ -> f_body
        else hd :: process_fbody func fname tl
  in
  let protect_fun f = { f with f_body = process_fbody f f.f_name f.f_body } in
  (globals, List.map protect_fun fns)

let protect_gen is_ct_sopn (mk_protect : 'a Slh_gen.mk_protectT)
    (p : (unit, 'asm) prog) (entries : Name.t list) : (unit, 'asm) prog =
  let rec doit n p =
    if n < 0 then p
    else
      try
        ignore (Sct_checker_forward.ty_prog is_ct_sopn p entries);
        Format.eprintf "Done.@.";
        p
      with Sct_checker_forward.sct_error e -> (
        Format.eprintf "Found error: %a\n@." Utils.pp_hierror e;
        match e.err.err_loc with
        | Lone loc -> protect_loc mk_protect p loc e.info |> doit (n - 1)
        | _ -> assert false)
  in
  doit 1000 p
