module StackAlloc (Arch: Arch_full.Arch) : sig

  val memory_analysis :
    (Stack_alloc.sub_region -> (IInfo.t, FInfo.t) Compiler_util.pp_error) ->
    (Format.formatter -> (IInfo.t, FInfo.t) Compiler_util.pp_error -> unit) ->
    debug:bool ->
    (IInfo.t, FInfo.t,
     (IInfo.t, FInfo.t, Arch.reg, Arch.regx, Arch.xreg, Arch.rflag, Arch.cond,
      Arch.asm_op, Arch.extra_op) Arch_extra.extended_op) Expr._uprog ->
    Compiler.stack_alloc_oracles

end
