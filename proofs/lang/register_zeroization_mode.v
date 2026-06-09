From Coq Require Import Strings.String.

Record rzmode :=
  {
    rzm_flags      : bool;
    rzm_registers  : bool;
    rzm_xregisters : bool;
  }.

Definition rzm_none : rzmode :=
  {| rzm_flags := false; rzm_registers := false; rzm_xregisters := false; |}.

Definition rzm_all : rzmode :=
  {| rzm_flags := true; rzm_registers := true; rzm_xregisters := true; |}.

Definition rzm_regs : rzmode :=
  {| rzm_flags := false; rzm_registers := true; rzm_xregisters := false; |}.

Definition rzm_xregs : rzmode :=
  {| rzm_flags := false; rzm_registers := false; rzm_xregisters := true; |}.

Definition rzm_regs_flags : rzmode :=
  {| rzm_flags := true; rzm_registers := true; rzm_xregisters := false; |}.

Definition string_of_rzm (m : rzmode) : string :=
  match rzm_flags m, rzm_registers m, rzm_xregisters m with
  | true,  true,  true  => "all"
  | false, false, false => "none"
  | false, true,  false => "regs"
  | true,  true,  false => "regs-flags"
  | false, false, true  => "xregs"
  | _,     _,     _     => ""
  end.

Definition rzmode_list : list rzmode :=
  rzm_all :: rzm_none :: rzm_regs :: rzm_regs_flags :: rzm_xregs :: nil.
