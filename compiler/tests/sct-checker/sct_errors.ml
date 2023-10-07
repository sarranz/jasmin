open Jasmin
open Common

let path = "error-messages"

let check p fn =
  match ty_prog p [ fn ] with
  | exception Annot.AnnotationError (loc, msg) ->
      Format.printf "Annotation error in %s: %a %t@." fn Location.pp_loc loc msg
  | exception Utils.HiError e ->
      Format.printf "Failed as expected %s: %a@." fn Utils.pp_hierror e
  | _ -> failwith ("Did not fail as expected: " ^ fn)

let load_and_check fname =
  Format.printf "File %s:@." fname;
  let p = load_file (Filename.concat path fname) in
  check p (Filename.remove_extension fname)

let () =
  let cases = Sys.readdir path in
  Array.sort String.compare cases;
  Array.iter load_and_check cases
