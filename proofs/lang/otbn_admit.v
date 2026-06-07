Require Import strings.

Axiom OTBN_ADMIT : forall {A : Type}, string -> A.
Definition OTBN_ADMIT_PROOF {A : Prop} : A := OTBN_ADMIT "proof".
