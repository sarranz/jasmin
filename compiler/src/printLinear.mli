val pp_prog :
  Wsize.wsize ->
  Wsize.wsize ->
  ('iinfo, 'finfo, 'reg, 'regx, 'xreg, 'rflag, 'cond, 'asm_op,
   'extra_op) Arch_extra.extended_op Sopn.asmOp ->
  Format.formatter ->
  ('iinfo, 'finfo,
   ('iinfo, 'finfo, 'reg, 'regx, 'xreg, 'rflag, 'cond, 'asm_op,
    'extra_op) Arch_extra.extended_op) Linear.lprog ->
  unit
