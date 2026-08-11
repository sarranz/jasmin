open Annotations

type returnaddress_kind =
  | OnStack
  | OnReg

type f_annot = {
    retaddr_kind          : returnaddress_kind option;
    stack_allocation_size : Z.t option;
    stack_size            : Z.t option;
    stack_align           : wsize option;
    max_call_depth        : Z.t option;
    stack_zero_strategy   : (Stack_zero_strategy.stack_zero_strategy * wsize option) option;
    f_user_annot          : annotations;
}

let f_annot_empty = {
    retaddr_kind          = None;
    stack_allocation_size = None;
    stack_size            = None;
    stack_align           = None;
    max_call_depth        = None;
    stack_zero_strategy   = None;
    f_user_annot          = [];
  }

type call_conv =
  | Export  (** The function should be exported to the outside word *)
  | Subroutine (** internal function that should not be inlined *)
  | Internal  (** internal function that should be inlined *)

let is_subroutine = function
  | Subroutine -> true
  | _            -> false

let is_export = function
  | Export -> true
  | _ -> false

(* ------------------------------------------------------------------------ *)
type return_info = {
    ret_annot : Annotations.annotations list;
    (* annotation attached to return type *)
    ret_loc : Location.t; (* location of the return statement *)
  }

(* ------------------------------------------------------------------------ *)
type t =
  Location.t * f_annot * call_conv * return_info

let entry_info (fi: t) : IInfo.t =
  let (fl, _, _, _) = fi in (Location.i_loc0 fl, [])

let ret_info (fi: t) : IInfo.t =
  let (_, _, _, ri) = fi in (Location.i_loc0 ri.ret_loc, [])

let user_annot ((_, fa, _, _) : t) : annotations = fa.f_user_annot

let add_stack_frame_annot
    (slots : (Var0.Var.var * (BinNums.coq_Z * BinNums.coq_Z)) list)
    ((fl, fa, cc, ri) : t) : t =
  let doit (x, (ofs, size)) =
    (IInfo.slot_name x,
     (CoreConv.z_of_cz ofs, CoreConv.z_of_cz size))
  in
  let slots =
    List.sort
      (fun (_, (o1, _)) (_, (o2, _)) -> Z.compare o1 o2)
      (List.map doit slots)
  in
  let fa =
    { fa with
      f_user_annot =
        Annotations.add_stack_frame_annot ~loc:fl slots fa.f_user_annot }
  in
  (fl, fa, cc, ri)
