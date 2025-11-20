From elpi.apps Require Import derive.std.
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.
From Coq Require Import ZArith.
Require Import utils.

#[only(eqbOK)] derive
Variant bn_flag_group :=
| FG0
| FG1
.

HB.instance Definition _ := hasDecEq.Build bn_flag_group bn_flag_group_eqb_OK.

#[only(eqbOK)] derive
Variant bn_register_shift :=
| RS_left
| RS_right
.

HB.instance Definition _ :=
  hasDecEq.Build bn_register_shift bn_register_shift_eqb_OK.

#[only(eqbOK)] derive
Variant bn_halfword_writeback :=
| WB_upper
| WB_lower
.

HB.instance Definition _ :=
  hasDecEq.Build bn_halfword_writeback bn_halfword_writeback_eqb_OK.
