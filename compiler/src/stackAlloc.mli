module StackAlloc (Arch: Arch_full.Arch) : sig

  val memory_analysis :
    (Stack_alloc.sub_region -> FInfo.t Compiler_util.pp_error) ->
    (Format.formatter -> FInfo.t Compiler_util.pp_error -> unit) ->
    debug:bool ->
    ((FInfo.t, Arch.reg, Arch.regx, Arch.xreg, Arch.rflag, Arch.cond, Arch.asm_op, Arch.extra_op) Arch_extra.extended_op, FInfo.t) Expr._uprog -> Compiler.stack_alloc_oracles

end
