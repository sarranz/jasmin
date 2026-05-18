open Wsize
(* -------------------------------------------------------------------- *)
exception InvalidRegSize of wsize

val print_prog  :
  Format.formatter -> (VInfo.t, IInfo.t) X86_instr_decl.x86_prog -> unit
