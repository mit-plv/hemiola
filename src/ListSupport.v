Require Import Common List.

Set Implicit Arguments.

Lemma tl_app:
  forall {A} (l1 l2: list A),
    l1 <> nil -> tl (l1 ++ l2) = (tl l1) ++ l2.
Proof.
  destruct l1; intuition idtac.
Qed.

Lemma cons_app:
  forall {A} (a: A) (l: list A),
    a :: l = (a :: nil) ++ l.
Proof.
  reflexivity.
Qed.

Lemma Forall_app:
  forall {A} (l1 l2: list A) P,
    Forall P l1 -> Forall P l2 -> Forall P (l1 ++ l2).
Proof.
  induction l1; simpl; intros; auto.
  inv H; constructor; auto.
Qed.

Lemma Forall_remove:
  forall {A} dec P (a: A) (l: list A),
    Forall P l -> Forall P (remove dec a l).
Proof.
  induction l; simpl; intros; auto.
  inv H; destruct (dec a a0); auto.
Qed.

Lemma Forall_filter:
  forall {A} P f (l: list A),
    Forall P l -> Forall P (filter f l).
Proof.
  induction l; simpl; intros; auto.
  inv H.
  destruct (f a); auto.
Qed.

Lemma filter_app:
  forall {A} f (l1 l2: list A),
    filter f (l1 ++ l2) = filter f l1 ++ filter f l2.
Proof.
  induction l1; simpl; intros; [reflexivity|].
  rewrite IHl1; destruct (f a); auto.
Qed.

Lemma in_remove:
  forall {A} (eq_dec : forall x y : A, {x = y} + {x <> y})
         (a x: A) (l: list A),
    In a (remove eq_dec x l) -> In a l.
Proof.
  induction l; simpl; intros; auto.
  destruct (eq_dec _ _); subst; auto.
  destruct H; auto.
Qed.

Lemma map_id:
  forall {A} (l: list A), map id l = l.
Proof.
  induction l; simpl; auto.
  rewrite IHl; reflexivity.
Qed.

Lemma map_trans:
  forall {A B C} (l: list A) (p: A -> B) (q: B -> C),
    map q (map p l) = map (fun a => q (p a)) l.
Proof.
  induction l; simpl; intros; auto.
  rewrite IHl; reflexivity.
Qed.

