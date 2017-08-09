Require Import Bool Ascii String List Eqdep Omega.
Require Import Logic.FunctionalExtensionality.

Ltac inv H := inversion H; subst; clear H.
Ltac dest :=
  repeat (match goal with
            | H: _ /\ _ |- _ => destruct H
            | H: exists _, _ |- _ => destruct H
          end).
Ltac dest_in :=
  repeat
    match goal with
    | [H: In _ _ |- _] => inv H
    end.
Ltac find_if_inside :=
  match goal with
    | [ |- context[if ?X then _ else _] ] => destruct X
    | [ H : context[if ?X then _ else _] |- _ ]=> destruct X
  end.

Definition ocons {A} (oa: option A) (l: list A) :=
  match oa with
  | Some a => a :: l
  | None => l
  end.
Infix "::>" := ocons (at level 0).

Definition o2l {A} (oa: option A): list A := ocons oa nil.
Definition ol2l {A} (oa: option (list A)): list A :=
  match oa with
  | Some l => l
  | None => nil
  end.

Infix "==n" := eq_nat_dec (at level 30).
Infix "?<n" := (in_dec eq_nat_dec) (at level 30).

Definition bind {A B} (oa: option A) (f: A -> option B): option B :=
  match oa with
  | Some a => f a
  | None => None
  end.
Infix ">>=" := bind (at level 0).
  
Axiom cheat: forall t, t.

