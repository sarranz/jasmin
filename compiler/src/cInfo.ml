let instance : (VInfo.t, IInfo.t, FInfo.t) Info.coq_CompilerInfo =
  {
    Info.ci_var_info = VInfo.instance;
    Info.ci_instr_info = IInfo.instance;
    Info.ci_fun_info = FInfo.instance;
  }
