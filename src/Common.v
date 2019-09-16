Require Import Bool Ascii String List Vector Eqdep Omega.
Require Export ProofIrrelevance.

Set Implicit Arguments.

Include ListNotations.
Include VectorNotations.

Ltac ssplit :=
  match goal with
  | [ |- _ /\ _] => split
  end.

Ltac isNew P :=
  match goal with
    | [ _: ?P' |- _] => assert (P = P') by reflexivity; fail 1
    | _ => idtac
  end.

Lemma neq_sym:
  forall {A} (a1 a2: A), a1 <> a2 -> a2 <> a1.
Proof.
  auto.
Qed.

Definition option_dec {A}
           (eq_dec: forall a1 a2: A, {a1 = a2} + {a1 <> a2}):
  forall oa1 oa2: option A, {oa1 = oa2} + {oa1 <> oa2}.
Proof.
  decide equality.
Defined.

Theorem tautology_0:
  forall (P Q: Prop), (P -> Q) -> P -> Q.
Proof.
  tauto.
Qed.

Inductive xor (A B: Prop): Prop :=
| Xor1: A -> ~B -> xor A B
| Xor2: ~A -> B -> xor A B.

Ltac xleft := apply Xor1.
Ltac xright := apply Xor2.

Lemma xor_inv_left:
  forall A B, xor A B -> A -> ~ B.
Proof.
  intros; firstorder.
Qed.

Lemma xor_inv_right:
  forall A B, xor A B -> B -> ~ A.
Proof.
  intros; firstorder.
Qed.

Inductive xor3 (A B C: Prop): Prop :=
| Xor31: A -> ~B -> ~C -> xor3 A B C
| Xor32: ~A -> B -> ~C -> xor3 A B C
| Xor33: ~A -> ~B -> C -> xor3 A B C.

Ltac xfst := apply Xor31.
Ltac xsnd := apply Xor32.
Ltac xthd := apply Xor33.

Lemma xor3_inv_1:
  forall A B C, xor3 A B C -> A -> ~B /\ ~C.
Proof.
  intros; firstorder.
Qed.

Lemma xor3_inv_2:
  forall A B C, xor3 A B C -> B -> ~A /\ ~C.
Proof.
  intros; firstorder.
Qed.

Lemma xor3_inv_3:
  forall A B C, xor3 A B C -> C -> ~A /\ ~B.
Proof.
  intros; firstorder.
Qed.

Ltac xor3_inv1 H :=
  match type of H with
  | xor3 ?P _ _ => eapply xor3_inv_1 with (A:= P) in H
  end.
  
Ltac xor3_inv2 H :=
  match type of H with
  | xor3 _ ?P _ => eapply xor3_inv_2 with (B:= P) in H
  end.

Ltac xor3_inv3 H :=
  match type of H with
  | xor3 _ _ ?P => eapply xor3_inv_3 with (C:= P) in H
  end.

Lemma xor3_False_1:
  forall A B C, xor3 A B C -> A -> B -> False.
Proof.
  intros; firstorder.
Qed.

Lemma xor3_False_2:
  forall A B C, xor3 A B C -> A -> C -> False.
Proof.
  intros; firstorder.
Qed.

Lemma xor3_False_3:
  forall A B C, xor3 A B C -> B -> C -> False.
Proof.
  intros; firstorder.
Qed.

Ltac xor3_contra1 H :=
  match type of H with
  | xor3 ?PA ?PB ?PC =>
    exfalso; apply xor3_False_1 with (A:= PA) (B:= PB) (C:= PC) in H; auto
  end.

Ltac xor3_contra2 H :=
  match type of H with
  | xor3 ?PA ?PB ?PC =>
    exfalso; apply xor3_False_2 with (A:= PA) (B:= PB) (C:= PC) in H; auto
  end.

Ltac xor3_contra3 H :=
  match type of H with
  | xor3 ?PA ?PB ?PC =>
    exfalso; apply xor3_False_3 with (A:= PA) (B:= PB) (C:= PC) in H; auto
  end.

Ltac nothing := idtac.

Ltac assert_later asrt :=
  apply tautology_0 with (P:= asrt); [intros|].

Ltac inv H := inversion H; subst; clear H.
Ltac dest :=
  repeat (match goal with
            | H: _ /\ _ |- _ => destruct H
            | H: exists _, _ |- _ => destruct H
          end).
Ltac dest_in :=
  repeat
    match goal with
    | [H: List.In _ _ |- _] => inv H
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

Definition nat_eq (n1 n2: nat) :=
  if eq_nat_dec n1 n2 then true else false.

Definition nat_in (n: nat) (ns: list nat) :=
  if in_dec eq_nat_dec n ns then true else false.

Infix "==n" := nat_eq (at level 30).
Infix "?<n" := nat_in (at level 30).

Definition bind {A B} (oa: option A) (f: A -> option B): option B :=
  match oa with
  | Some a => f a
  | None => None
  end.
Infix ">>=" := bind (at level 0).

Definition lift {A B} (f: A -> B): option A -> option B :=
  fun oa =>
    match oa with
    | Some a => Some (f a)
    | None => None
    end.

Lemma lift_hd_error:
  forall {A B} (f: A -> B) (l: list A),
    lift f (hd_error l) = hd_error (List.map f l).
Proof.
  induction l; simpl; intros; auto.
Qed.

Definition tbind {A B} (nb: B) (oa: option A) (f: A -> B): B :=
  match oa with
  | Some a => f a
  | None => nb
  end.
Notation "OA >>=[ NB ] F" :=
  (tbind NB OA F) (at level 0, format "OA  '>>=[' NB ] '/' F").

Module MonadNotations.
  Notation "A <-- OA ; CONT" :=
    (OA >>= (fun A => CONT)) (at level 84, right associativity): monad_scope.
  Open Scope monad_scope.
End MonadNotations.

Module PropMonadNotations.
  Notation "A <-- OA ; CONT" :=
    (OA >>=[False] (fun A => CONT)) (at level 84, right associativity): monad_scope.
  Notation "A <+- OA ; CONT" :=
    (OA >>=[True] (fun A => CONT)) (at level 84, right associativity): monad_scope.
  Notation "! OA ; CONT" :=
    (OA = None -> CONT) (at level 84, right associativity): monad_scope.
  Open Scope monad_scope.
End PropMonadNotations.

Inductive PHide: Prop -> Prop :=
| PHideIntro: forall P:Prop, P -> PHide P.

Ltac phide H := pose proof (PHideIntro H); clear H.
Ltac preveal H :=
  match type of H with
  | PHide _ => inv H
  end.
Ltac phide_clear :=
  repeat
    match goal with
    | [H: PHide _ |- _] => clear H
    end.

Inductive PMarker2: Prop -> Prop -> Prop :=
| PMarkerIntro2: forall P1 P2: Prop, P1 -> P2 -> PMarker2 P1 P2.

Ltac pmark2 H1 H2 := pose proof (PMarkerIntro2 H1 H2).
Ltac pmarked2 H1 H2 :=
  match type of H1 with
  | ?P1 =>
    match type of H2 with
    | ?P2 => isNew (PMarker2 P1 P2)
    end
  end.
Ltac is_pmark2 H :=
  match type of H with
  | PMarker2 _ _ => idtac
  end.
Ltac is_not_pmark2 H :=
  lazymatch type of H with
  | PMarker2 _ _ => fail
  | _ => idtac
  end.

Ltac pmark_clear :=
  repeat
    match goal with
    | [H: PMarker2 _ _ |- _] => clear H
    end.

