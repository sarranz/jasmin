open Prog

type ty_fun

type sct_error = {
  err : Utils.hierror;
  info : Sv.t;
}
exception SCTError of sct_error

val pp_sct_error : Format.formatter -> sct_error -> unit

val pp_funty : Format.formatter -> Name.t * ty_fun -> unit
val ty_prog : ('asm -> bool) -> ('info, 'asm) prog -> Name.t list -> (Name.t * ty_fun) list

val compile_infer_msf :
  ('info, 'asm) prog -> (Slh_lowering.slh_t list * Slh_lowering.slh_t list) Hf.t
