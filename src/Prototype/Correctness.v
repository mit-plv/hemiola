Require Import List String Peano_dec.
Require Import FnMap Language SingleValue.

Ltac inv H := inversion H; subst; clear H.
Ltac dest_in :=
  repeat
    match goal with
    | [H: In _ _ |- _] => inv H
    end.

Theorem impl_linear: ExtLinear impl implIndices.
Proof.
  apply linear_extLinear.
  apply linear_local.

  intros; dest_in.

  - (* parent *)
    admit.
  - (* child1 *)
    admit.
  - (* child2 *)
    admit.
  
Admitted.



