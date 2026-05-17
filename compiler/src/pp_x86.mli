open Wsize
(* -------------------------------------------------------------------- *)
exception InvalidRegSize of wsize

val print_prog  :
  Format.formatter -> IInfo.t X86_instr_decl.x86_prog -> unit
