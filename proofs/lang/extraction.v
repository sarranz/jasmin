Require jasmin_compiler.
(* Do not “Require” other modules from Jasmin here:
   expand the jasmin_compiler module instead. *)

From Coq Require ExtrOcamlBasic.
From Coq Require ExtrOcamlNativeString.
From Coq Require ExtrOCamlInt63.

(* This is a hack to force the extraction to keep the singleton here,
   This need should be removed if we add more constructor to syscall_t *)
Extract Inductive syscall.syscall_t => "(Wsize.wsize * BinNums.positive) Syscall_t.syscall_t" ["Syscall_t.RandomBytes"].
Set Extraction File Comment "This prelude is added at extraction time. See lang/extraction.v. *) [@@@ocaml.warning ""-9-20-27-32-33-34-37-39-50-67""] (* End of prelude. ".

Extraction Inline ssrbool.is_left.
Extraction Inline ssrbool.predT ssrbool.pred_of_argType.
Extraction Inline ssrbool.idP.

Extraction Inline utils.assert.
Extraction Inline utils.Result.bind.
Extraction Inline Datatypes.implb.

Extract Constant strings.ascii_eqb => "Char.equal".
Extract Constant strings.ascii_cmp =>
  "(fun x y -> let c = Char.compare x y in if c = 0 then Datatypes.Eq else if c < 0 then Datatypes.Lt else Datatypes.Gt)".

Extract Constant info.VarInfo.t => "Location.t".
Extract Constant info.VarInfo.witness => "Location._dummy".
Extract Constant info.var_info => "Location.t".
Extract Constant waes.MixColumns => "(fun _ -> failwith ""MixColumns is not implemented"")".
Extract Constant waes.InvMixColumns => "(fun _ -> failwith ""InvMixColumns not implemented"")".

(* The match function and the field projections [c_tag], [c_name], [c_kind]
   could all be extracted soundly (via
   [fun fmk x -> fmk (CoreIdent.Cident.tag x) ...] and the corresponding OCaml
   accessors). This means that the extracted OCaml needs no [failwith].

   However, I deliberately fail in this cases: we want to use only [tag],
   [id_name], [id_kind]. Anything that tries to pattern-match on [mkCident] or
   read [c_tag]/[c_name]/[c_kind] is a bug. *)
Extract Inductive ident.Cident.t =>
  "CoreIdent.Cident.t"
  [ "(fun _ _ _ -> failwith ""Cident.mkCident not callable "")" ]
  "(fun _ _ -> failwith ""Cident.t match not callable "")".
Extract Constant ident.Cident.c_tag =>
  "(fun _ -> failwith ""Cident.c_tag not callable "")".
Extract Constant ident.Cident.c_name =>
  "(fun _ -> failwith ""Cident.c_name not callable "")".
Extract Constant ident.Cident.c_kind =>
  "(fun _ -> failwith ""Cident.c_kind not callable "")".

Extract Constant ident.Cident.tag => "CoreIdent.Cident.tag".
Extract Constant ident.Cident.id_name => "CoreIdent.Cident.id_name".
Extract Constant ident.Cident.id_kind => "CoreIdent.Cident.id_kind".
Extract Constant ident.Cident.eqb => "CoreIdent.eqb".
Extract Constant ident.Cident.cmp => "CoreIdent.cmp".

(* Similar to [Cident]. *)
Extract Inductive funname.FunName.t =>
  "CoreIdent.funname"
  [ "(fun _ _ -> failwith ""FunName.mkFunname not callable "")" ]
  "(fun _ _ -> failwith ""FunName.t match not callable "")".
Extract Constant funname.FunName.fn_tag  =>
  "(fun _ -> failwith ""FunName.fn_tag not callable "")".
Extract Constant funname.FunName.fn_name =>
  "(fun _ -> failwith ""FunName.fn_name not callable "")".

Extract Constant funname.FunName.tag => "CoreIdent.funname_tag".
Extract Constant funname.FunName.eqb => "CoreIdent.funname_eqb".
Extract Constant funname.FunName.cmp => "CoreIdent.funname_cmp".


Set Extraction Output Directory "lang/ocaml".

Extraction Blacklist String List Nat Uint63 Utils Var Array.

Separate Extraction
  utils
  warray_
  sem_type
  sopn
  expr
  stack_zero_strategy
  lower_spill.spill_uprog
  psem_defs
  sem_params
  sem_params_of_arch_extra
  arch_decl
  arch_extra
  x86_decl
  x86_instr_decl
  x86_extra
  x86_params
  arm_decl
  arm_instr_decl
  arm_extra
  arm_params
  riscv_decl
  riscv_instr_decl
  riscv_extra
  riscv_params
  compiler
  wint_int
.
