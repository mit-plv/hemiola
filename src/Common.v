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

Ltac is_equal t1 t2 :=
  let Heq := fresh "Heq" in
  assert (Heq: t1 = t2) by reflexivity;
  clear Heq.

Ltac is_pure_const t :=
  tryif is_var t
  then fail
  else lazymatch t with
       | ?t1 ?t2 =>
         tryif is_pure_const t1
         then is_pure_const t2 else fail
       | _ => idtac
       end.

Ltac not_pure_const t :=
  tryif is_var t
  then idtac
  else lazymatch t with
       | ?t1 ?t2 =>
         tryif not_pure_const t1
         then idtac else not_pure_const t2
       | _ => fail
       end.

Ltac collect_of_type_helper ty ls :=
  match goal with
  | [v: ty |- _]
    => lazymatch ls with
       | context[cons v _] => fail
       | _ => collect_of_type_helper ty (cons v ls)
       end
  | _ => ls
  end.
Ltac collect_of_type ty := collect_of_type_helper ty (@nil ty).

Definition ocons {A} (oa: option A) (l: list A) :=
  match oa with
  | Some a => a :: l
  | None => l
  end.
Infix "::>" := ocons (at level 0, right associativity).

Definition o2l {A} (oa: option A): list A := ocons oa nil.
Definition ol2l {A} (oa: option (list A)): list A :=
  match oa with
  | Some l => l
  | None => nil
  end.

Infix "==n" := eq_nat_dec (at level 30).
Infix "<=n" := le_dec (at level 30).
Infix "<n" := lt_dec (at level 30).
Infix ">=n" := ge_dec (at level 30).
Infix ">n" := gt_dec (at level 30).
Infix "?<n" := (in_dec eq_nat_dec) (at level 30).

Definition bind {A B} (oa: option A) (f: A -> option B): option B :=
  match oa with
  | Some a => f a
  | None => None
  end.
Infix ">>=" := bind (at level 0).

Definition tbind {A B} (nb: B) (oa: option A) (f: A -> B): B :=
  match oa with
  | Some a => f a
  | None => nb
  end.
Notation "OA >>=[ NB ] F" :=
  (tbind NB OA F) (at level 0, format "OA  '>>=[' NB ] '/' F").

Fixpoint replicate {A} (a: A) (sz: nat): list A :=
  match sz with
  | O => nil
  | S sz' => a :: replicate a sz'
  end.

Definition trues (sz: nat) := replicate true sz.
Definition falses (sz: nat) := replicate false sz.

Fixpoint findAt (v: nat) (l: list nat) :=
  match l with
  | nil => None
  | n :: l' =>
    if v ==n n then Some O
    else (findAt v l') >>=[None] (fun o => Some (S o))
  end.

Axiom cheat: forall t, t.

