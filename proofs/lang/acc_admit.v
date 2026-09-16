Require Import strings.

Axiom ACC_ADMIT : forall {A : Type}, string -> A.
Definition ACC_ADMIT_PROOF {A : Prop} : A := ACC_ADMIT "proof".
