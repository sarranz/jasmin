type returnaddress_kind =
  | OnStack
  | OnReg

type f_annot = {
    retaddr_kind          : returnaddress_kind option;
    stack_allocation_size : Z.t option;
    stack_size            : Z.t option;
    stack_align           : Annotations.wsize option;
    max_call_depth        : Z.t option;
    stack_zero_strategy   : (Stack_zero_strategy.stack_zero_strategy * Annotations.wsize option) option;
    f_user_annot          : Annotations.annotations;
}

type call_conv =
  | Export
  | Subroutine
  | Internal

type return_info = {
    ret_annot : Annotations.annotations list;
    ret_loc   : Location.t;
  }

type t = Location.t * f_annot * call_conv * return_info

val f_annot_empty : f_annot
val is_export    : call_conv -> bool
val is_subroutine : call_conv -> bool
val instance : (VInfo.t, IInfo.t, t) Info.coq_FunInfo
