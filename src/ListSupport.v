Require Import Common List.

Set Implicit Arguments.

Fixpoint removeOnce {A} (eq_dec: forall x y: A, {x = y} + {x <> y})
         (a: A) (l: list A) :=
  match l with
  | nil => nil
  | h :: t => if eq_dec a h then t else h :: removeOnce eq_dec a t
  end.

Fixpoint removeL {A} (eq_dec: forall x y: A, {x = y} + {x <> y})
         (l1 l2: list A) :=
  match l2 with
  | nil => l1
  | h :: t => removeL eq_dec (removeOnce eq_dec h l1) t
  end.

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

Lemma Forall_app_inv:
  forall {A} (l1 l2: list A) P,
    Forall P (l1 ++ l2) -> Forall P l1 /\ Forall P l2.
Proof.
  induction l1; simpl; intros; auto.
  inv H; specialize (IHl1 _ _ H3); dest; auto.
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

Lemma remove_cons:
  forall {A} (eq_dec : forall x y : A, {x = y} + {x <> y})
         (a: A) (l: list A),
    remove eq_dec a (a :: l) = remove eq_dec a l.
Proof.
  intros; simpl.
  destruct (eq_dec _ _); auto.
  elim n; auto.
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

Lemma NoDup_filter:
  forall {A} (l: list A),
    NoDup l ->
    forall f,
      NoDup (filter f l).
Proof.
  induction l; simpl; intros; [constructor|].
  inv H.
  destruct (f a); auto.
  constructor; auto.
  intro Hx; elim H2.
  apply filter_In in Hx; dest; auto.
Qed.

Lemma NoDup_map_filter:
  forall {A B} (l: list A) (p: A -> B) (f: A -> bool),
    NoDup (map p l) ->
    NoDup (map p (filter f l)).
Proof.
  induction l; simpl; intros; [constructor|].
  inv H.
  destruct (f a); simpl; auto.
  constructor; auto.
  intro Hx; elim H2; clear -Hx.
  induction l; [elim Hx|].
  simpl in *.
  destruct (f a0); auto.
  inv Hx; auto.
Qed.

Fixpoint noDup {A} (eq_dec : forall x y : A, {x = y} + {x <> y})
         (l: list A) :=
  match l with
  | nil => nil
  | a :: l' => if in_dec eq_dec a l' then noDup eq_dec l' else a :: noDup eq_dec l'
  end.

Lemma noDup_In:
  forall {A} (eq_dec : forall x y : A, {x = y} + {x <> y}) (a: A) (l: list A),
    In a (noDup eq_dec l) -> In a l.
Proof.
  induction l; simpl; intros; auto.
  destruct (in_dec eq_dec a0 l); auto.
  inv H; auto.
Qed.

Lemma noDup_NoDup:
  forall {A} (eq_dec : forall x y : A, {x = y} + {x <> y}) (l: list A),
    NoDup (noDup eq_dec l).
Proof.
  induction l; simpl; intros; [constructor|].
  destruct (in_dec eq_dec a l); auto.
  constructor; auto.
  intro Hx; elim n; eapply noDup_In; eauto.
Qed.

