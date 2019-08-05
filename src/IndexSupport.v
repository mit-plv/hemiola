Require Import Bool Ascii List Omega.
Require Import Common.
Require Export Index ListSupport.

Set Implicit Arguments.

Local Open Scope list.

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

Lemma liftInds_In:
  forall n ns,
    In (natToIdx n) (liftInds ns) ->
    In n ns.
Proof.
  induction ns; simpl; intros; auto.
  destruct H; auto.
  inv H; auto.
Qed.

Lemma liftInds_NoDup:
  forall inds,
    NoDup inds ->
    NoDup (liftInds inds).
Proof.
  induction inds; simpl; intros; [constructor|].
  inv H; constructor; auto.
  intro Hx; elim H2.
  apply liftInds_In; assumption.
Qed.

Lemma idx_DisjList_head:
  forall (inds1 inds2: list IdxT),
    DisjList (map idxHd inds1) (map idxHd inds2) ->
    DisjList inds1 inds2.
Proof.
  induction inds1; simpl; intros; [apply DisjList_nil_1|].
  apply DisjList_cons in H; dest.
  apply (DisjList_cons_inv idx_dec); auto.
  intro Hx; elim H.
  apply in_map; assumption.
Qed.

Lemma extendIdx_inv:
  forall ext idx1 idx2,
    extendIdx ext idx1 = extendIdx ext idx2 ->
    idx1 = idx2.
Proof.
  unfold extendIdx; intros.
  inv H; reflexivity.
Qed.

Lemma extendIdx_In:
  forall ext idx inds,
    In (extendIdx ext idx) (extendInds ext inds) ->
    In idx inds.
Proof.
  induction inds; simpl; intros; auto.
  destruct H; auto.
  apply extendIdx_inv in H; auto.
Qed.

Lemma extendIdx_NoDup:
  forall ext inds,
    NoDup inds -> NoDup (extendInds ext inds).
Proof.
  induction inds; simpl; intros; auto.
  inv H; constructor; auto.
  intro Hx; elim H2.
  eapply extendIdx_In; eauto.
Qed.

Lemma extendInds_idxHd_SubList:
  forall ext inds,
    SubList (map idxHd (extendInds ext inds)) [ext].
Proof.
  induction inds; simpl; intros; [apply SubList_nil|].
  apply SubList_cons.
  - left; reflexivity.
  - assumption.
Qed.

Lemma extendIdx_not_IdxPrefix:
  forall i e, ~ i~>e ~< i.
Proof.
  unfold extendIdx, IdxPrefix; intros.
  intro Hx; dest.
  replace (x ++ e :: i) with ((x ++ [e]) ++ i) in H
    by (rewrite <-app_assoc; reflexivity).
  remember (x ++ [e]) as l.
  assert (l <> nil) by (intro Hx; subst; destruct x; discriminate).
  clear Heql x e.
  generalize dependent l.
  induction i; simpl; intros.
  - rewrite app_nil_r in H; auto.
  - destruct l; [auto|].
    inv H.
    eapply IHi with (l:= l ++ [n]).
    + rewrite <-app_assoc; assumption.
    + destruct l; discriminate.
Qed.

Lemma IdxPrefix_refl: forall i, i ~< i.
Proof.
  unfold IdxPrefix; intros.
  exists nil; reflexivity.
Qed.

Lemma IdxPrefix_trans:
  forall i1 i2, i1 ~< i2 -> forall i3, i2 ~< i3 -> i1 ~< i3.
Proof.
  unfold IdxPrefix; intros; dest; subst.
  eexists; rewrite app_assoc; reflexivity.
Qed.

Lemma IdxPrefix_common:
  forall i1 i2 i, i1 ~< i -> i2 ~< i -> i1 ~< i2 \/ i2 ~< i1.
Proof.
  unfold IdxPrefix; intros; dest; subst.
  apply app_eq_compare in H0.
  destruct H0 as [p ?]; destruct H; dest; subst; eauto.
Qed.

Lemma IdxPrefix_disj_1:
  forall i1 i2, i1 ~*~ i2 -> forall ei1, i1 ~< ei1 -> ei1 ~*~ i2.
Proof.
  unfold IdxDisj; intros; dest.
  split.
  - intro Hx; elim H.
    eapply IdxPrefix_trans; eauto.
  - intro Hx.
    pose proof (IdxPrefix_common H0 Hx).
    destruct H2; auto.
Qed.

Lemma IdxPrefix_disj_2:
  forall i1 i2, i1 ~*~ i2 -> forall ei2, i2 ~< ei2 -> i1 ~*~ ei2.
Proof.
  unfold IdxDisj; intros; dest.
  split.
  - intro Hx.
    pose proof (IdxPrefix_common H0 Hx).
    destruct H2; auto.
  - intro Hx; elim H1.
    eapply IdxPrefix_trans; eauto.
Qed.

Lemma IdxDisj_not_eq:
  forall i1 i2, i1 ~*~ i2 -> i1 <> i2.
Proof.
  intros; intro Hx; subst.
  red in H; dest.
  elim H; apply IdxPrefix_refl.
Qed.

Lemma extendIdx_IdxDisj:
  forall bidx ext1 ext2,
    ext1 <> ext2 -> bidx~>ext1 ~*~ bidx~>ext2.
Proof.
  unfold extendIdx, IdxDisj, IdxPrefix; intros.
  split; intro; dest.
  - destruct x; [inv H0; auto|].
    apply (f_equal (@List.length _)) in H0.
    rewrite app_length in H0; simpl in H0.
    omega.
  - destruct x; [inv H0; auto|].
    apply (f_equal (@List.length _)) in H0.
    rewrite app_length in H0; simpl in H0.
    omega.
Qed.

Lemma IdxDisj_base_IndsDisj:
  forall bidx1 bidx2,
    bidx1 ~*~ bidx2 ->
    forall inds1 inds2,
      Forall (fun idx => bidx1 ~< idx) inds1 ->
      Forall (fun idx => bidx2 ~< idx) inds2 ->
      IndsDisj inds1 inds2.
Proof.
  intros.
  rewrite Forall_forall in H0, H1.
  red; intros.
  specialize (H0 _ H2); specialize (H1 _ H3).
  eapply IdxPrefix_disj_1; [|eassumption].
  eapply IdxPrefix_disj_2; [|eassumption].
  assumption.
Qed.

Lemma IndsDisj_DisjList:
  forall inds1 inds2, IndsDisj inds1 inds2 -> DisjList inds1 inds2.
Proof.
  unfold IndsDisj, DisjList; intros.
  destruct (in_dec idx_dec e inds1); [|auto].
  destruct (in_dec idx_dec e inds2); [|auto].
  specialize (H _ _ i i0).
  exfalso; eapply IdxDisj_not_eq; eauto.
Qed.

