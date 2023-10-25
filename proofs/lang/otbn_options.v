From mathcomp Require Import
  all_ssreflect
  all_algebra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Variant bn_flag_group :=
  | FG0
  | FG1
.

Variant bn_register_shift :=
  | RS_left
  | RS_right
.

Variant bn_halfword_writeback :=
  | WB_upper
  | WB_lower
.
