val pp_prog :
  Wsize.wsize ->
  Wsize.wsize ->
  ('vinfo, 'iinfo, 'finfo, 'reg, 'regx, 'xreg, 'rflag, 'cond, 'asm_op,
   'extra_op) Arch_extra.extended_op Sopn.asmOp ->
  Format.formatter ->
  ('vinfo, 'iinfo, 'finfo,
   ('vinfo, 'iinfo, 'finfo, 'reg, 'regx, 'xreg, 'rflag, 'cond, 'asm_op,
    'extra_op) Arch_extra.extended_op) Linear.lprog ->
  unit
