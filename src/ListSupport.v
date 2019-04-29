Require Import Common List Omega.

Set Implicit Arguments.

Definition ocons {A} (oa: option A) (l: list A) :=
  match oa with
  | Some a => a :: l
  | None => l
  end.
Infix "::>" := ocons (at level 0, right associativity).

Fixpoint oll {A} (ol: list (option A)) :=
  match ol with
  | nil => nil
  | oa :: ol' => oa ::> (oll ol')
  end.

Definition oapp {A} (l: list A) (ol: list (option A)) :=
  l ++ oll ol.

Definition o2l {A} (oa: option A): list A := ocons oa nil.
Definition ol2l {A} (oa: option (list A)): list A :=
  match oa with
  | Some l => l
  | None => nil
  end.

Definition list_dec_eq_nil {A}: forall (l: list A), {l = nil} + {l <> nil}.
Proof.
  intros.
  destruct l.
  - left; reflexivity.
  - right; discriminate.
Defined.

Fixpoint lift_each {A} (l: list A): list (list A) :=
  match l with
  | nil => nil
  | a :: l' => [a] :: lift_each l'
  end.

Lemma lift_each_app:
  forall {A} (l1 l2: list A),
    lift_each (l1 ++ l2) = lift_each l1 ++ lift_each l2.
Proof.
  induction l1; simpl; intros; auto.
  rewrite IHl1; reflexivity.
Qed.

Lemma lift_each_concat:
  forall {A} (l: list A),
    l = List.concat (lift_each l).
Proof.
  induction l; simpl; intros; auto.
  rewrite IHl at 1; reflexivity.
Qed.

Section SubDisjEquiv.
  Context {A: Type}.
  
  Definition SubList (l1 l2: list A) := forall e, In e l1 -> In e l2.
  Definition DisjList (l1 l2: list A) := forall e, ~ In e l1 \/ ~ In e l2.
  Definition EquivList (l1 l2: list A) := SubList l1 l2 /\ SubList l2 l1.

  Lemma SubList_nil: forall l, SubList nil l.
  Proof. unfold SubList; intros; inv H. Qed.

  Lemma SubList_nil_inv: forall l, SubList l nil -> l = nil.
  Proof.
    unfold SubList; intros; destruct l; auto.
    specialize (H a (or_introl eq_refl)); inv H.
  Qed.
  
  Lemma SubList_cons: forall a l1 l2, In a l2 -> SubList l1 l2 -> SubList (a :: l1) l2.
  Proof. unfold SubList; intros; inv H1; auto. Qed.

  Lemma SubList_cons_inv: forall a l1 l2, SubList (a :: l1) l2 -> In a l2 /\ SubList l1 l2.
  Proof. unfold SubList; intros; split; intuition. Qed.

  Lemma SubList_cons_right: forall a l1 l2, SubList l1 l2 -> SubList l1 (a :: l2).
  Proof. unfold SubList; intros; right; auto. Qed.

  Lemma SubList_forall:
    forall P l1,
      Forall P l1 ->
      forall l2, SubList l2 l1 -> Forall P l2.
  Proof.
    unfold SubList; intros.
    rewrite Forall_forall in H.
    rewrite Forall_forall; intros; auto.
  Qed.
  
  Lemma SubList_refl: forall l, SubList l l.
  Proof. unfold SubList; intros; auto. Qed.

  Lemma SubList_refl': forall l1 l2, l1 = l2 -> SubList l1 l2.
  Proof. intros; subst; apply SubList_refl. Qed.
  
  Lemma SubList_trans:
    forall l1 l2 l3, SubList l1 l2 -> SubList l2 l3 -> SubList l1 l3.
  Proof. unfold SubList; intros; auto. Qed.

  Lemma SubList_singleton:
    forall a1 a2, SubList [a1] [a2] -> a1 = a2.
  Proof.
    intros.
    specialize (H a1 (or_introl eq_refl)).
    firstorder.
  Qed.

  Lemma SubList_singleton_In:
    forall a l, SubList [a] l -> In a l.
  Proof.
    intros; firstorder.
  Qed.

  Lemma SubList_singleton_NoDup:
    forall l a,
      SubList l [a] -> NoDup l -> l = nil \/ l = [a].
  Proof.
    intros.
    destruct l; [auto|].
    right.
    apply SubList_cons_inv in H; dest.
    inv H0; dest_in.
    destruct l; [auto|].
    apply SubList_cons_inv in H1; dest.
    inv H5; dest_in.
    elim H4; left; reflexivity.
  Qed.
  
  Lemma SubList_app_1: forall l1 l2 l3, SubList l1 l2 -> SubList l1 (l2 ++ l3).
  Proof.
    unfold SubList; intros; apply in_or_app; left; auto.
  Qed.

  Lemma SubList_app_2: forall l1 l2 l3, SubList l1 l3 -> SubList l1 (l2 ++ l3).
  Proof.
    unfold SubList; intros; apply in_or_app; right; auto.
  Qed.

  Lemma SubList_app_3: forall l1 l2 l3, SubList l1 l3 -> SubList l2 l3 -> SubList (l1 ++ l2) l3.
  Proof.
    unfold SubList; intros.
    apply in_app_or in H1; destruct H1; intuition.
  Qed.

  Lemma SubList_app_4: forall l1 l2 l3, SubList (l1 ++ l2) l3 -> SubList l1 l3.
  Proof.
    unfold SubList; intros; apply H; apply in_or_app; left; auto.
  Qed.

  Lemma SubList_app_5: forall l1 l2 l3, SubList (l1 ++ l2) l3 -> SubList l2 l3.
  Proof.
    unfold SubList; intros; apply H; apply in_or_app; right; auto.
  Qed.

  Lemma SubList_app_6:
    forall l1 l2 l3 l4, SubList l1 l2 -> SubList l3 l4 -> SubList (l1 ++ l3) (l2 ++ l4).
  Proof.
    intros; apply SubList_app_3.
    - apply SubList_app_1; auto.
    - apply SubList_app_2; auto.
  Qed.

  Lemma SubList_app_7:
    forall l1 l2 l3, SubList (l1 ++ l2) l3 -> SubList l1 l3 /\ SubList l2 l3.
  Proof.
    intros; split.
    - eapply SubList_app_4; eauto.
    - eapply SubList_app_5; eauto.
  Qed.

  Lemma SubList_app_comm:
    forall l1 l2 l3, SubList l1 (l2 ++ l3) -> SubList l1 (l3 ++ l2).
  Proof.
    unfold SubList; intros.
    apply in_or_app.
    specialize (H e H0); apply in_app_or in H; intuition.
  Qed.

  Lemma SubList_app_idempotent:
    forall l1 l2, SubList l1 (l2 ++ l2) -> SubList l1 l2.
  Proof.
    unfold SubList; intros.
    specialize (H e H0).
    apply in_app_or in H; intuition.
  Qed.

  Lemma EquivList_nil: EquivList nil nil.
  Proof. split; unfold SubList; intros; inv H. Qed.

  Lemma EquivList_nil_inv_1: forall l, EquivList l nil -> l = nil.
  Proof. intros; inv H; apply SubList_nil_inv; auto. Qed.

  Lemma EquivList_nil_inv_2: forall l, EquivList nil l -> l = nil.
  Proof. intros; inv H; apply SubList_nil_inv; auto. Qed.

  Lemma EquivList_cons:
    forall a1 a2 l1 l2,
      EquivList l1 l2 -> a1 = a2 -> EquivList (a1 :: l1) (a2 :: l2).
  Proof.
    intros; inv H; subst; split;
      try (apply SubList_cons; [left; auto|apply SubList_cons_right; auto]).
  Qed.

  Lemma EquivList_refl: forall l, EquivList l l.
  Proof. intros; split; apply SubList_refl. Qed.
  
  Lemma EquivList_comm: forall l1 l2, EquivList l1 l2 -> EquivList l2 l1.
  Proof. unfold EquivList; intros; dest; split; auto. Qed.

  Lemma EquivList_trans:
    forall l1 l2 l3, EquivList l1 l2 -> EquivList l2 l3 -> EquivList l1 l3.
  Proof. intros; inv H; inv H0; split; eapply SubList_trans; eauto. Qed.

  Lemma EquivList_app:
    forall l1 l2 l3 l4,
      EquivList l1 l2 -> EquivList l3 l4 ->
      EquivList (l1 ++ l3) (l2 ++ l4).
  Proof.
    unfold EquivList; intros; dest; split.
    - apply SubList_app_3.
      + apply SubList_app_1; auto.
      + apply SubList_app_2; auto.
    - apply SubList_app_3.
      + apply SubList_app_1; auto.
      + apply SubList_app_2; auto.
  Qed.

  Lemma EquivList_app_comm: forall l1 l2, EquivList (l1 ++ l2) (l2 ++ l1).
  Proof.
    unfold EquivList; intros; split.
    - apply SubList_app_3.
      + apply SubList_app_2, SubList_refl; auto.
      + apply SubList_app_1, SubList_refl; auto.
    - apply SubList_app_3.
      + apply SubList_app_2, SubList_refl; auto.
      + apply SubList_app_1, SubList_refl; auto.
  Qed.

  Lemma EquivList_app_idempotent:
    forall l1 l2, EquivList l1 (l2 ++ l2) -> EquivList l1 l2.
  Proof.
    unfold EquivList; intros; dest; split.
    - apply SubList_app_idempotent; auto.
    - eapply SubList_app_4; eauto.
  Qed.

  Lemma DisjList_false_spec:
    forall (deceqA : forall x y: A, sumbool (x = y) (x <> y))
           l1 l2,
      (forall a, In a l1 -> In a l2 -> False) ->
      DisjList l1 l2.
  Proof.
    intros; red; intros.
    destruct (in_dec deceqA e l1); auto.
    destruct (in_dec deceqA e l2); auto.
    exfalso; eauto.
  Qed.
  
  Lemma DisjList_nil_1: forall l, DisjList nil l.
  Proof. unfold DisjList; auto. Qed.

  Lemma DisjList_nil_2: forall l, DisjList l nil.
  Proof. unfold DisjList; auto. Qed.

  Lemma DisjList_cons:
    forall a l1 l2, DisjList (a :: l1) l2 ->
                    ~ In a l2 /\ DisjList l1 l2.
  Proof.
    unfold DisjList; intros.
    split.
    - specialize (H a); intuition.
    - intros; specialize (H e); intuition.
  Qed.

  Lemma DisjList_cons_inv:
    forall (deceqA : forall x y: A, sumbool (x = y) (x <> y))
           a l1 l2,
      DisjList l1 l2 -> ~ In a l2 -> DisjList (a :: l1) l2.
  Proof.
    unfold DisjList; intros.
    specialize (H e); destruct H; auto.
    destruct (deceqA a e); subst; auto.
    left; intro Hx; elim H.
    inv Hx; auto.
    exfalso; auto.
  Qed.

  Lemma DisjList_In_1:
    forall a l1 l2,
      DisjList l1 l2 -> In a l2 -> ~ In a l1.
  Proof.
    unfold DisjList; intros.
    specialize (H a); destruct H; auto.
  Qed.
    
  Lemma DisjList_In_2:
    forall a l1 l2,
      DisjList l1 l2 -> In a l1 -> ~ In a l2.
  Proof.
    unfold DisjList; intros.
    specialize (H a); destruct H; auto.
  Qed.

  Lemma DisjList_In_neq:
    forall a1 a2 l1 l2,
      DisjList l1 l2 -> In a1 l1 -> In a2 l2 -> a1 <> a2.
  Proof.
    unfold DisjList; intros.
    intro Hx; subst.
    specialize (H a2); destruct H; auto.
  Qed.
  
  Lemma DisjList_comm: forall l1 l2, DisjList l1 l2 -> DisjList l2 l1.
  Proof. 
    intros. unfold DisjList in *. intros e. specialize (H e). intuition.
  Qed.

  Lemma DisjList_SubList: forall sl1 l1 l2, SubList sl1 l1 -> DisjList l1 l2 -> DisjList sl1 l2.
  Proof. 
    intros. unfold SubList, DisjList in *. intros e. 
    specialize (H e). specialize (H0 e). intuition.
  Qed.

  Lemma NoDup_DisjList:
    forall l1 l2,
      NoDup l1 -> NoDup l2 -> DisjList l1 l2 ->
      NoDup (l1 ++ l2).
  Proof.
    induction l1; simpl; intros; auto.
    inv H; constructor.
    - intro Hx; apply in_app_or in Hx; destruct Hx; [auto|].
      specialize (H1 a); destruct H1; auto.
      elim H1; simpl; tauto.
    - apply IHl1; auto.
      eapply DisjList_cons; eauto.
  Qed.

  Lemma DisjList_NoDup:
    forall (deceqA : forall x y: A, sumbool (x = y) (x <> y))
           l1 l2,
      NoDup (l1 ++ l2) -> DisjList l1 l2.
  Proof.
    induction l1; simpl; intros.
    - apply DisjList_nil_1.
    - inv H.
      apply DisjList_cons_inv; auto.
      intro Hx; elim H2.
      apply in_or_app; auto.
  Qed.

  Lemma DisjList_app_1: forall l1 l2 l3, DisjList l1 (l2 ++ l3) -> DisjList l1 l2.
  Proof. 
    intros. unfold DisjList in *. intros e.
    destruct (H e); [left | right].
    - assumption.
    - intuition.
  Qed.

  Lemma DisjList_app_2: forall l1 l2 l3, DisjList l1 (l2 ++ l3) -> DisjList l1 l3.
  Proof. 
    intros. unfold DisjList in *. intros e.
    destruct (H e); [left | right].
    - assumption.
    - intuition.
  Qed.

  Lemma DisjList_app_3:
    forall l1 l2 l3, DisjList (l1 ++ l2) l3 -> DisjList l1 l3 /\ DisjList l2 l3.
  Proof.
    intros; unfold DisjList in *; split.
    - intros; destruct (H e).
      + left; intuition.
      + right; intuition.
    - intros; destruct (H e).
      + left; intuition.
      + right; intuition.
  Qed.

  Lemma DisjList_app_4:
    forall l1 l2 l3,
      DisjList l1 l3 -> DisjList l2 l3 -> DisjList (l1 ++ l2) l3.
  Proof.
    intros; unfold DisjList in *; intros.
    specialize (H e); specialize (H0 e).
    destruct H; auto.
    destruct H0; auto.
    left; intro Hx.
    apply in_app_or in Hx; destruct Hx; auto.
  Qed.

  Lemma DisjList_singleton_1:
    forall (deceqA : forall x y: A, sumbool (x = y) (x <> y)) a1 l2,
      ~ In a1 l2 ->
      DisjList [a1] l2.
  Proof.
    unfold DisjList; intros.
    destruct (deceqA e a1); subst; firstorder.
  Qed.
    
  Lemma DisjList_singleton_2:
    forall (deceqA : forall x y: A, sumbool (x = y) (x <> y)) l1 a2,
      ~ In a2 l1 ->
      DisjList l1 [a2].
  Proof.
    unfold DisjList; intros.
    destruct (deceqA e a2); subst; firstorder.
  Qed.
  
  Lemma DisjList_singletons:
    forall (deceqA : forall x y: A, sumbool (x = y) (x <> y)) a1 a2,
      a1 <> a2 -> DisjList [a1] [a2].
  Proof.
    unfold DisjList; intros.
    destruct (deceqA e a1); subst; firstorder.
  Qed.

  Definition subList_dec:
    forall (deceqA : forall x y: A, sumbool (x = y) (x <> y))
           l1 l2,
      {SubList l1 l2} + {~ SubList l1 l2}.
  Proof.
    induction l1; intros.
    - left; apply SubList_nil.
    - destruct (IHl1 l2).
      + destruct (in_dec deceqA a l2).
        * left; apply SubList_cons; assumption.
        * right; intro Hx; elim n.
          apply SubList_cons_inv in Hx.
          destruct Hx.
          assumption.
      + right; intro Hx; elim n.
        apply SubList_cons_inv in Hx.
        destruct Hx.
        assumption.
  Defined.
  
End SubDisjEquiv.

Lemma SubList_map: forall {A B} (l1 l2: list A) (f: A -> B),
                     SubList l1 l2 -> SubList (map f l1) (map f l2).
Proof.
  induction l1; intros; simpl; unfold SubList in *; intros; inv H0.
  - apply in_map; apply H; left; reflexivity.
  - apply IHl1; auto.
    intros; specialize (H e0); apply H; right; assumption.
Qed.

Section Removal.
  Context {A: Type}.
  Hypothesis (eq_dec: forall x y: A, {x = y} + {x <> y}).
  
  Fixpoint removeOnce (a: A) (l: list A) :=
    match l with
    | nil => nil
    | h :: t => if eq_dec a h then t else h :: removeOnce a t
    end.

  Fixpoint removeL (l1 l2: list A) :=
    match l2 with
    | nil => l1
    | h :: t => removeL (removeOnce h l1) t
    end.

  Lemma removeL_nil:
    forall l, removeL l l = nil.
  Proof.
    induction l; simpl; intros; [reflexivity|].
    destruct (eq_dec a a); auto.
    elim n; reflexivity.
  Qed.

  Lemma removeOnce_In_1:
    forall a1 a2,
      a1 <> a2 ->
      forall l,
        In a1 l ->
        In a1 (removeOnce a2 l).
  Proof.
    induction l; simpl; intros; auto.
    destruct H0; subst.
    - destruct (eq_dec a2 a1); subst.
      + elim H; reflexivity.
      + left; reflexivity.
    - destruct (eq_dec a2 a); subst; auto.
      right; auto.
  Qed.

  Lemma removeOnce_In_2:
    forall a1 a2 l,
      In a1 (removeOnce a2 l) ->
      In a1 l.
  Proof.
    induction l; simpl; intros; auto.
    destruct (eq_dec a2 a); subst; auto.
    inv H; auto.
  Qed.

  Lemma removeOnce_NoDup:
    forall a l,
      NoDup l -> NoDup (removeOnce a l).
  Proof.
    induction l; simpl; intros; auto.
    inv H; destruct (eq_dec a a0); auto.
    constructor; auto.
    intro Hx; elim H2.
    eapply removeOnce_In_2; eauto.
  Qed.

  Lemma removeOnce_In_NoDup:
    forall a1 a2 l,
      NoDup l -> In a1 (removeOnce a2 l) ->
      a1 <> a2 /\ In a1 l.
  Proof.
    induction l; simpl; intros; auto.
    inv H.
    destruct (eq_dec a2 a); [subst|].
    - split; [|auto].
      intro Hx; subst; auto.
    - inv H0; auto.
      specialize (IHl H4 H); dest; auto.
  Qed.

  Lemma removeL_In_1:
    forall a l2 l1,
      In a l1 -> ~ In a l2 ->
      In a (removeL l1 l2).
  Proof.
    induction l2; simpl; intros; auto.
    apply IHl2; try (firstorder; fail).
    apply removeOnce_In_1; auto.
  Qed.

  Lemma removeL_In_2:
    forall a l2 l1,
      In a (removeL l1 l2) ->
      In a l1.
  Proof.
    induction l2; simpl; intros; auto.
    specialize (IHl2 _ H).
    eapply removeOnce_In_2; eauto.
  Qed.
  
  Lemma forall_removeOnce:
    forall a l P,
      Forall P l ->
      Forall P (removeOnce a l).
  Proof.
    induction l; simpl; intros; auto.
    inv H.
    destruct (eq_dec a a0); auto.
  Qed.
  
  Lemma forall_removeL:
    forall l2 l1 P,
      Forall P l1 ->
      Forall P (removeL l1 l2).
  Proof.
    induction l2; simpl; intros; auto.
    apply IHl2.
    apply forall_removeOnce.
    auto.
  Qed.

  Lemma removeOnce_app_1:
    forall a (l1 l2: list A),
      In a l1 ->
      removeOnce a (l1 ++ l2) =
      removeOnce a l1 ++ l2.
  Proof.
    induction l1; simpl; intros; [elim H|].
    destruct H; subst.
    - destruct (eq_dec a a); auto.
      elim n; reflexivity.
    - destruct (eq_dec a a0); auto.
      rewrite IHl1 by assumption.
      reflexivity.
  Qed.

  Lemma removeOnce_app_2:
    forall a (l1 l2: list A),
      ~ In a l1 ->
      removeOnce a (l1 ++ l2) =
      l1 ++ removeOnce a l2.
  Proof.
    induction l1; simpl; intros; auto.
    destruct (eq_dec a a0); subst.
    - elim H; left; reflexivity.
    - rewrite IHl1; [reflexivity|].
      intro Hx; elim H; auto.
  Qed.

  Lemma removeOnce_SubList_1:
    forall l1 l2,
      SubList l1 l2 ->
      forall a,
        ~ In a l1 ->
        SubList l1 (removeOnce a l2).
  Proof.
    unfold SubList; intros.
    destruct (eq_dec a e); subst.
    - elim H0; assumption.
    - apply removeOnce_In_1; auto.
  Qed.

  Lemma removeOnce_SubList_2:
    forall a l2,
      SubList (removeOnce a l2) l2.
  Proof.
    unfold SubList; intros.
    eapply removeOnce_In_2; eauto.
  Qed.

  Lemma removeOnce_SubList_3:
    forall a l2,
      SubList l2 (a :: removeOnce a l2).
  Proof.
    unfold SubList; intros.
    destruct (eq_dec a e); subst.
    - intuition.
    - right; apply removeOnce_In_1; auto.
  Qed.

  Lemma removeOnce_length:
    forall a l,
      In a l ->
      length l > 0 /\ length (removeOnce a l) = length l - 1.
  Proof.
    induction l; simpl; intros; [exfalso; auto|].
    destruct H; subst.
    - destruct (eq_dec a a); [clear e|exfalso; auto].
      split; omega.
    - destruct (eq_dec a a0); [subst|].
      + split; omega.
      + simpl.
        specialize (IHl H); destruct IHl.
        split; omega.
  Qed.
  
  Lemma removeL_SubList_1:
    forall l1 l2,
      SubList l1 l2 ->
      forall l3,
        DisjList l1 l3 ->
        SubList l1 (removeL l2 l3).
  Proof.
    intros.
    generalize dependent l2.
    generalize dependent l1.
    induction l3; simpl; intros; auto.
    apply DisjList_comm, DisjList_cons in H0; dest.
    apply DisjList_comm in H1.
    apply IHl3; auto.
    apply removeOnce_SubList_1; auto.
  Qed.

  Lemma removeL_SubList_2:
    forall l1 l2,
      SubList (removeL l1 l2) l1.
  Proof.
    intros.
    generalize dependent l1.
    induction l2; simpl; intros.
    - apply SubList_refl.
    - eapply SubList_trans.
      + eapply IHl2.
      + apply removeOnce_SubList_2.
  Qed.

  Lemma removeL_SubList_3:
    forall l1 l2,
      SubList l1 (l2 ++ removeL l1 l2).
  Proof.
    intros.
    generalize dependent l1.
    induction l2; simpl; intros.
    - apply SubList_refl.
    - specialize (IHl2 (removeOnce a l1)).
      eapply SubList_trans.
      + apply removeOnce_SubList_3 with (a:= a).
      + apply SubList_cons.
        * intuition.
        * apply SubList_cons_right; auto.
  Qed.

  Lemma removeL_DisjList:
    forall l1 l2 l3,
      DisjList l1 l3 ->
      DisjList (removeL l1 l2) l3.
  Proof.
    intros.
    eapply DisjList_SubList.
    - apply removeL_SubList_2.
    - assumption.
  Qed.
  
  Lemma removeL_app_1:
    forall (l1 l2 l3: list A),
      removeL l1 (l2 ++ l3) =
      removeL (removeL l1 l2) l3.
  Proof.
    intros.
    generalize dependent l1.
    generalize dependent l3.
    induction l2; simpl; intros; auto.
  Qed.

  Lemma removeL_app_2:
    forall (l1 l2: list A),
      removeL (l1 ++ l2) l1 = l2.
  Proof.
    induction l1; simpl; intros; auto.
    destruct (eq_dec a a); auto.
    elim n; reflexivity.
  Qed.

  Lemma removeL_app_3:
    forall (l1 l2 l3: list A),
      SubList l3 l1 -> NoDup l3 ->
      removeL (l1 ++ l2) l3 =
      removeL l1 l3 ++ l2.
  Proof.
    intros.
    generalize dependent l2.
    generalize dependent l1.
    induction l3; simpl; intros; auto.
    apply SubList_cons_inv in H; dest.
    inv H0.
    rewrite <-IHl3.
    - rewrite removeOnce_app_1 by assumption.
      reflexivity.
    - assumption.
    - apply removeOnce_SubList_1; assumption.
  Qed.

  Lemma removeL_app_4:
    forall (l1 l2 l3: list A),
      DisjList l1 l3 ->
      removeL (l1 ++ l2) l3 =
      l1 ++ removeL l2 l3.
  Proof.
    intros.
    generalize dependent l2.
    generalize dependent l1.
    induction l3; simpl; intros; auto.
    apply DisjList_comm, DisjList_cons in H; dest.
    apply DisjList_comm in H0.
    rewrite removeOnce_app_2; auto.
  Qed.

  Lemma removeL_In_NoDup:
    forall a l2 l1,
      NoDup l1 -> In a (removeL l1 l2) ->
      ~ In a l2 /\ In a l1.
  Proof.
    induction l2; simpl; intros; auto.
    specialize (IHl2 _ (removeOnce_NoDup a0 H) H0); dest.
    split.
    - intro Hx; destruct Hx; subst; auto.
      apply removeOnce_In_NoDup in H2; [|assumption].
      dest; auto.
    - apply removeOnce_In_NoDup in H2; [|assumption].
      dest; auto.
  Qed.

End Removal.

Lemma removeOnce_idsOf_In:
  forall {A} (eq_dec: forall x y: A, {x = y} + {x <> y}) il iv i,
    In i (idsOf (removeOnce (id_dec eq_dec) iv il)) ->
    In i (idsOf il).
Proof.
  induction il; simpl; intros; auto.
  destruct (id_dec eq_dec iv a); subst; auto.
  simpl in H; destruct H; subst; eauto.
Qed.

Lemma removeL_idsOf_In:
  forall {A} (eq_dec: forall x y: A, {x = y} + {x <> y}) il2 il1 i,
    In i (idsOf (removeL (id_dec eq_dec) il1 il2)) ->
    In i (idsOf il1).
Proof.
  induction il2; simpl; intros; auto.
  eapply removeOnce_idsOf_In; eauto.
Qed.

Lemma removeOnce_idsOf_NoDup:
  forall {A} (eq_dec: forall x y: A, {x = y} + {x <> y}) il iv,
    NoDup (idsOf il) ->
    NoDup (idsOf (removeOnce (id_dec eq_dec) iv il)).
Proof.
  induction il; simpl; intros; auto.
  inv H.
  destruct (id_dec eq_dec iv a); subst; auto.
  simpl; constructor; eauto.
  intro Hx; elim H2.
  eapply removeOnce_idsOf_In; eauto.
Qed.

Lemma removeL_idsOf_NoDup:
  forall {A} (eq_dec: forall x y: A, {x = y} + {x <> y}) il2 il1,
    NoDup (idsOf il1) ->
    NoDup (idsOf (removeL (id_dec eq_dec) il1 il2)).
Proof.
  induction il2; simpl; intros; auto.
  eapply IHil2, removeOnce_idsOf_NoDup; eauto.
Qed.

Lemma SubList_NoDup_removeL_nil:
  forall {A} (eq_dec: forall x y: A, {x = y} + {x <> y})
         (l1 l2: list A),
    SubList l2 l1 -> NoDup l2 ->
    removeL eq_dec l2 l1 = nil.
Proof.
  induction l1; simpl; intros;
    [apply SubList_nil_inv in H; auto|].
  eapply IHl1; [|apply removeOnce_NoDup; assumption].
  clear IHl1.
  generalize dependent l1.
  induction l2; simpl; intros; [apply SubList_nil|].
  destruct (eq_dec a a0); subst.
  - apply SubList_cons_inv in H; dest.
    red; intros.
    pose proof (H1 _ H2).
    inv H3; auto.
    exfalso; inv H0; auto.
  - apply SubList_cons.
    + apply SubList_cons_inv in H; dest.
      inv H; [exfalso; auto|auto].
    + eapply IHl2.
      * inv H0; auto.
      * apply SubList_cons_inv in H; dest; auto.
Qed.

Lemma SubList_NoDup_length_eq_removeL_nil:
  forall {A} (eq_dec: forall x y: A, {x = y} + {x <> y})
         (l1 l2: list A),
    SubList l1 l2 -> NoDup l1 ->
    length l1 = length l2 ->
    removeL eq_dec l2 l1 = nil.
Proof.
  induction l1; simpl; intros;
    [destruct l2; [reflexivity|discriminate]|].
  apply SubList_cons_inv in H; dest; inv H0.
  destruct l2; [exfalso; auto|].
  inv H1.
  destruct (eq_dec a0 a).
  - subst; simpl; destruct (eq_dec a a) as [Heq|Hneq]; [clear Heq|exfalso; auto].
    eapply IHl1; eauto.
    red; intros; specialize (H2 _ H0).
    inv H2; intuition.
  - inv H; [exfalso; auto|].
    simpl; destruct (eq_dec a a0) as [Heq|Hneq]; [exfalso; auto|clear Hneq].
    eapply IHl1.
    + red; intros; specialize (H2 _ H).
      inv H2; [left; reflexivity|].
      right; eapply removeOnce_In_1.
      * intro Hx; subst; auto.
      * assumption.
    + assumption.
    + simpl; pose proof (removeOnce_length eq_dec _ _ H0); dest.
      omega.
Qed.

Section SSubList.
  Context {A: Type}.

  Inductive SSubList: list A -> list A -> Prop :=
  | SSLnil: SSubList nil nil
  | SSLcons1:
      forall l1 l2 a,
        SSubList l1 l2 ->
        SSubList l1 (a :: l2)
  | SSLcons2:
      forall l1 l2 a,
        SSubList l1 l2 ->
        SSubList (a :: l1) (a :: l2).

  Lemma SSubList_refl:
    forall l, SSubList l l.
  Proof.
    induction l; simpl; intros.
    - constructor.
    - eapply SSLcons2; auto.
  Qed.

  Lemma SSubList_app_1:
    forall l1 l2,
      SSubList l2 (l1 ++ l2).
  Proof.
    induction l1; simpl; intros.
    - apply SSubList_refl.
    - eapply SSLcons1; auto.
  Qed.

  Lemma SSubList_app_2:
    forall l1 l2,
      SSubList l1 l2 ->
      forall l3,
        SSubList (l1 ++ l3) (l2 ++ l3).
  Proof.
    induction 1; simpl; intros.
    - apply SSubList_refl.
    - apply SSLcons1; auto.
    - apply SSLcons2; auto.
  Qed.

  Lemma SSubList_SubList:
    forall l1 l2,
      SSubList l1 l2 -> SubList l1 l2.
  Proof.
    induction 1; simpl; intros.
    - apply SubList_nil.
    - apply SubList_cons_right; auto.
    - apply SubList_cons.
      + left; reflexivity.
      + apply SubList_cons_right; auto.
  Qed.

  Lemma SSubList_removeOnce_1:
    forall (eq_dec: forall x y: A, {x = y} + {x <> y}) l1 l2,
      SSubList l1 l2 ->
      forall a,
        SSubList (removeOnce eq_dec a l1) l2.
  Proof.
    induction 1; simpl; intros.
    - apply SSubList_refl.
    - apply SSLcons1; auto.
    - destruct (eq_dec a0 a); subst.
      + apply SSLcons1; auto.
      + apply SSLcons2; auto.
  Qed.

  Lemma SSubList_removeOnce_2:
    forall (eq_dec: forall x y: A, {x = y} + {x <> y}) l1 l2,
      SSubList l1 l2 ->
      forall a,
        SSubList (removeOnce eq_dec a l1) (removeOnce eq_dec a l2).
  Proof.
    induction 1; simpl; intros.
    - apply SSubList_refl.
    - destruct (eq_dec a0 a); subst.
      + apply SSubList_removeOnce_1; auto.
      + apply SSLcons1; auto.
    - destruct (eq_dec a0 a); subst; auto.
      apply SSLcons2; auto.
  Qed.

  Lemma SSubList_removeL_1:
    forall (eq_dec: forall x y: A, {x = y} + {x <> y}) l1 l2,
      SSubList l1 l2 ->
      forall l3,
        SSubList (removeL eq_dec l1 l3) l2.
  Proof.
    intros.
    generalize dependent l2.
    generalize dependent l1.
    induction l3; simpl; intros; auto.
    apply IHl3.
    apply SSubList_removeOnce_1; auto.
  Qed.

  Lemma SSubList_removeL_2:
    forall (eq_dec: forall x y: A, {x = y} + {x <> y}) l1 l2,
      SSubList l1 l2 ->
      forall l3,
        SSubList (removeL eq_dec l1 l3) (removeL eq_dec l2 l3).
  Proof.
    intros.
    generalize dependent l2.
    generalize dependent l1.
    induction l3; simpl; intros; auto.
    apply IHl3.
    apply SSubList_removeOnce_2; auto.
  Qed.

End SSubList.

Section Distribution.
  Context {A: Type}.

  Inductive Distribution: list A -> list A -> list A -> Prop :=
  | DistrNil: Distribution nil nil nil
  | DistrL:
      forall l ll1 ll2 rl a,
        Distribution l (ll1 ++ ll2) rl ->
        Distribution (a :: l) (ll1 ++ a :: ll2) rl
  | DistrR:
      forall l ll rl1 rl2 a,
        Distribution l ll (rl1 ++ rl2) ->
        Distribution (a :: l) ll (rl1 ++ a :: rl2).

  Lemma distribution_left:
    forall l, Distribution l l nil.
  Proof.
    induction l; simpl; intros.
    - constructor; auto.
    - change (a :: l) with ([] ++ a :: l) at 2.
      constructor; auto.
  Qed.

  Lemma distribution_right:
    forall l, Distribution l nil l.
  Proof.
    induction l; simpl; intros.
    - constructor; auto.
    - change (a :: l) with ([] ++ a :: l) at 2.
      constructor; auto.
  Qed.

  Lemma distribution_add_left_head:
    forall l1 l2 dl1 dl2,
      Distribution (l1 ++ l2) dl1 dl2 ->
      forall a,
        Distribution (l1 ++ a :: l2) (a :: dl1) dl2.
  Proof.
    induction l1; simpl; intros.
    - change (a :: dl1) with ([] ++ a :: dl1).
      constructor; auto.
    - inv H.
      + change (a0 :: ll1 ++ a :: ll2) with ((a0 :: ll1) ++ a :: ll2).
        apply DistrL.
        simpl; auto.
      + apply DistrR; auto.
  Qed.

  Lemma distribution_add_right_head:
    forall l1 l2 dl1 dl2,
      Distribution (l1 ++ l2) dl1 dl2 ->
      forall a,
        Distribution (l1 ++ a :: l2) dl1 (a :: dl2).
  Proof.
    induction l1; simpl; intros.
    - change (a :: dl2) with ([] ++ a :: dl2).
      constructor; auto.
    - inv H.
      + apply DistrL; auto.
      + change (a0 :: rl1 ++ a :: rl2) with ((a0 :: rl1) ++ a :: rl2).
        apply DistrR.
        simpl; auto.
  Qed.
  
End Distribution.

Lemma tl_In:
  forall {A} (a: A) (l: list A),
    In a (tl l) ->
    In a l.
Proof.
  intros.
  destruct l; [elim H|simpl in H].
  right; assumption.
Qed.

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

Lemma NoDup_app_comm:
  forall {A} (l1 l2: list A),
    NoDup (l2 ++ l1) ->
    NoDup (l1 ++ l2).
Proof.
  induction l1; simpl; intros.
  - rewrite app_nil_r in H; auto.
  - constructor.
    + apply NoDup_remove_2 in H.
      intro Hx; elim H; clear H.
      apply in_or_app; apply in_app_or in Hx.
      destruct Hx; auto.
    + apply IHl1.
      eapply NoDup_remove_1; eauto.
Qed.

Lemma NoDup_app_weakening_1:
  forall {A} (l1 l2: list A),
    NoDup (l1 ++ l2) ->
    NoDup l1.
Proof.
  induction l1; simpl; intros; [constructor|].
  inv H; constructor; eauto.
  intro Hx; elim H2.
  apply in_or_app; auto.
Qed.

Lemma NoDup_app_weakening_2:
  forall {A} (l1 l2: list A),
    NoDup (l1 ++ l2) ->
    NoDup l2.
Proof.
  intros.
  apply NoDup_app_comm in H.
  eauto using NoDup_app_weakening_1.
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

Lemma NoDup_map_In:
  forall {A B} (p: A -> B) (l: list A),
    NoDup (map p l) ->
    forall a1 a2,
      In a1 l -> In a2 l ->
      p a1 = p a2 ->
      a1 = a2.
Proof.
  induction l; simpl; intros; [elim H0|].
  inv H.
  destruct H0, H1; subst; auto.
  - rewrite H2 in H5; elim H5.
    apply in_map; auto.
  - rewrite <-H2 in H5; elim H5.
    apply in_map; auto.
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

Lemma hd_error_In:
  forall {A} (l: list A) v,
    hd_error l = Some v ->
    In v l.
Proof.
  induction l; simpl; intros; [discriminate|].
  inv H; auto.
Qed.

Lemma hd_error_Some_app:
  forall {A} (l1: list A) v,
    hd_error l1 = Some v ->
    forall l2,
      hd_error (l1 ++ l2) = Some v.
Proof.
  destruct l1; intros; [discriminate|].
  simpl in H; inv H.
  reflexivity.
Qed.

Lemma idsOf_app:
  forall {A} (ias1 ias2: list (Id A)),
    idsOf (ias1 ++ ias2) = idsOf ias1 ++ idsOf ias2.
Proof.
  intros; apply map_app.
Qed.

Lemma valsOf_app:
  forall {A} (ias1 ias2: list (Id A)),
    valsOf (ias1 ++ ias2) = valsOf ias1 ++ valsOf ias2.
Proof.
  intros; apply map_app.
Qed.

Lemma idsOf_NoDup:
  forall {A} (ias: list (Id A)),
    NoDup (idsOf ias) -> NoDup ias.
Proof.
  unfold idsOf; intros.
  eapply NoDup_map_inv; eauto.
Qed.

Lemma valsOf_NoDup:
  forall {A} (ias: list (Id A)),
    NoDup (valsOf ias) -> NoDup ias.
Proof.
  unfold valsOf; intros.
  eapply NoDup_map_inv; eauto.
Qed.

Lemma idsOf_NoDup_In_value_eq:
  forall {A} (ias: list (Id A)) i a1 a2,
    NoDup (idsOf ias) ->
    In (i, a1) ias -> In (i, a2) ias ->
    a1 = a2.
Proof.
  induction ias as [|[i a] ias]; simpl; intros; [exfalso; auto|].
  inv H.
  destruct H0.
  - inv H.
    destruct H1.
    + inv H; reflexivity.
    + elim H4; apply in_map_iff; exists (i0, a2); auto.
  - destruct H1.
    + inv H0; elim H4; apply in_map_iff; exists (i0, a1); auto.
    + eapply IHias; eauto.
Qed.

Lemma idsOf_DisjList:
  forall {A} (ias1 ias2: list (Id A)),
    DisjList (idsOf ias1) (idsOf ias2) ->
    DisjList ias1 ias2.
Proof.
  unfold DisjList; intros.
  destruct e as [idx a].
  specialize (H idx); destruct H.
  - left; intro Hx; elim H.
    eapply in_map with (f:= idOf) in Hx; auto.
  - right; intro Hx; elim H.
    eapply in_map with (f:= idOf) in Hx; auto.
Qed.

Lemma valsOf_DisjList:
  forall {A} (ias1 ias2: list (Id A)),
    DisjList (valsOf ias1) (valsOf ias2) ->
    DisjList ias1 ias2.
Proof.
  unfold DisjList; intros.
  destruct e as [idx a].
  specialize (H a); destruct H.
  - left; intro Hx; elim H.
    eapply in_map with (f:= valOf) in Hx; auto.
  - right; intro Hx; elim H.
    eapply in_map with (f:= valOf) in Hx; auto.
Qed.

Lemma count_occ_app:
  forall {A} (eq_dec : forall x y : A, {x = y} + {x <> y})
         (a: A) (l1 l2: list A),
    count_occ eq_dec (l1 ++ l2) a =
    count_occ eq_dec l1 a + count_occ eq_dec l2 a.
Proof.
  induction l1; simpl; intros; auto.
  destruct (eq_dec a0 a); subst; auto.
  rewrite IHl1; reflexivity.
Qed.

Lemma count_occ_removeOnce_eq:
  forall {A} (eq_dec : forall x y : A, {x = y} + {x <> y})
         (a: A) (l: list A),
    In a l ->
    S (count_occ eq_dec (removeOnce eq_dec a l) a) =
    count_occ eq_dec l a.
Proof.
  induction l; simpl; intros; [exfalso; auto|].
  destruct (eq_dec a a0); subst.
  - destruct (eq_dec a0 a0); [reflexivity|exfalso; auto].
  - simpl.
    destruct (eq_dec a0 a); [exfalso; auto|].
    destruct H; [exfalso; auto|].
    auto.
Qed.

Lemma count_occ_removeOnce_neq:
  forall {A} (eq_dec : forall x y : A, {x = y} + {x <> y})
         (ra a: A) (l: list A),
    a <> ra ->
    count_occ eq_dec (removeOnce eq_dec ra l) a =
    count_occ eq_dec l a.
Proof.
  induction l; simpl; intros; [reflexivity|].
  destruct (eq_dec ra a0); subst.
  - destruct (eq_dec a0 a); auto.
    exfalso; auto.
  - simpl.
    destruct (eq_dec a0 a); subst; auto.
Qed.

Lemma count_occ_removeL:
  forall {A} (eq_dec : forall x y : A, {x = y} + {x <> y})
         (a: A) (rl l: list A),
    SubList rl l -> NoDup rl ->
    count_occ eq_dec (removeL eq_dec l rl) a +
    count_occ eq_dec rl a =
    count_occ eq_dec l a.
Proof.
  induction rl; simpl; intros; [omega|].
  apply SubList_cons_inv in H; dest.
  inv H0.
  destruct (eq_dec a0 a); subst.
  - rewrite Nat.add_succ_r.
    rewrite IHrl.
    + apply count_occ_removeOnce_eq; auto.
    + apply removeOnce_SubList_1; auto.
    + assumption.
  - rewrite IHrl.
    + apply count_occ_removeOnce_neq; auto.
    + apply removeOnce_SubList_1; auto.
    + assumption.
Qed.

(** Some other ways of induction for lists *)

Lemma list_picker:
  forall (A: Type) (P: list A -> Prop) (f: P nil)
         (Q0: A -> Prop) (Q1: A -> Prop)
         (f0: forall l, Forall Q0 l -> P l)
         (f1: forall a l0 l1,
             Forall Q0 l0 -> Q1 a ->
             P (l0 ++ l1) -> P (l0 ++ a :: l1)),
  forall l, Forall (fun a => Q0 a \/ Q1 a) l ->
            (Forall Q0 l \/
             exists a l0 l1, l = l0 ++ a :: l1 /\ Forall Q0 l0 /\ Q1 a).
Proof.
  induction l; simpl; intros; auto.
  inv H; destruct H2.
  - specialize (IHl H3).
    destruct IHl.
    + left; constructor; auto.
    + destruct H0 as [a0 [l0 [l1 ?]]]; dest; subst.
      right; exists a0, (a :: l0), l1.
      repeat split; auto.
  - right; exists a, nil, l; repeat split; auto.
Qed.

Lemma list_ind_pick:
  forall (A: Type) (P: list A -> Prop) (f: P nil)
         (Q0: A -> Prop) (Q1: A -> Prop)
         (f0: forall l, Forall Q0 l -> P l)
         (f1: forall a l0 l1,
             Forall Q0 l0 -> Q1 a ->
             P (l0 ++ l1) -> P (l0 ++ a :: l1)),
  forall l, Forall (fun a => Q0 a \/ Q1 a) l -> P l.
Proof.
  intros.
  remember (List.length l) as n.
  generalize dependent l.

  induction n; intros;
    [apply eq_sym, length_zero_iff_nil in Heqn; subst; auto|].

  pose proof H.
  eapply list_picker in H0; eauto.
  destruct H0; auto.
  destruct H0 as [a0 [l0 [l1 ?]]]; dest; subst.
  eapply f1; eauto.
  eapply IHn.
  - apply Forall_app_inv in H; dest; inv H0.
    apply Forall_app; auto.
  - rewrite app_length in Heqn; simpl in Heqn.
    rewrite app_length; omega.
Qed.

Lemma list_not_nil_exists_tail:
  forall (A: Type) (l: list A),
    l <> nil ->
    exists l' a, l = l' ++ [a].
Proof.
  induction l; intros; [elim H; reflexivity|].
  destruct l as [|a' l'].
  - exists nil, a; reflexivity.
  - specialize (IHl (ltac:(discriminate))).
    destruct IHl as [rl [ra ?]].
    exists (a :: rl), ra.
    rewrite H0.
    reflexivity.
Qed.

Lemma list_ind_rev:
  forall (A: Type) (P: list A -> Prop) (f: P nil)
         (f0: forall a l, P l -> P (l ++ [a])),
  forall l, P l.
Proof.
  intros.
  remember (List.length l) as n.
  generalize dependent l.

  induction n; intros;
    [apply eq_sym, length_zero_iff_nil in Heqn; subst; auto|].

  destruct l; [inv Heqn|].
  pose proof (@list_not_nil_exists_tail _ (a :: l) (ltac:(discriminate))).
  destruct H as [rl [ra ?]]; rewrite H; rewrite H in Heqn.

  apply f0.
  apply IHn.
  rewrite app_length in Heqn; simpl in Heqn.
  omega.
Qed.

