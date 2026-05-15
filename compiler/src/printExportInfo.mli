open Prog

val pp_export_info_json :
  Format.formatter ->
  (FInfo.t, 'reg, 'regx, 'xreg, 'rglag, 'cond, 'asm_op, 'extra_op) Arch_extra.extended_op
  Pretyping.Env.env ->
  ( unit,
    ( FInfo.t,
      'reg,
      'regx,
      'xreg,
      'rflag,
      'cond,
      'asm_op,
      'extra_op )
    Arch_extra.extended_op )
  prog ->
  ('reg, 'regx, 'xreg, 'rflag, 'cond, 'asm_op) Arch_decl.asm_prog ->
  unit
