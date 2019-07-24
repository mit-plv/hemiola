Require Import Bool Vector List String Peano_dec Omega.
Require Import Common FMap HVector ListSupport Syntax Topology Semantics.
Require Import RqRsLang.

Require Import Ex.Spec Ex.SpecSv Ex.ImplTemplate Ex.Mesi.
Require Import Ex.Mesi.Mesi.

Set Implicit Arguments.

Local Open Scope list.
Local Open Scope hvec.
Local Open Scope fmap.

(** TODO: move to [RqRsLang.v] *)
Lemma initORqs_GoodORqsInit: forall oinds, GoodORqsInit (initORqs oinds).
Proof.
  red; intros.
  unfold initORqs.
  remember (M.empty (M.t (RqInfo Msg))) as m.
  assert (forall oidx, m@[oidx] >>=[True] (fun orq => orq = []))
    by (intros; subst; mred).
  clear Heqm.
  generalize dependent m.
  induction oinds; simpl; intros; [auto|].
  apply IHoinds.
  intros.
  mred; auto.
Qed.

(** TODO: move to [ListSupport.v] *)
Lemma collect_forall:
  forall {A B} P (f: A -> list B) al,
    (forall a, In a al -> Forall P (f a)) ->
    Forall P (collect f al).
Proof.
  induction al; intros; [constructor|].
  simpl; apply Forall_app.
  - apply H; left; reflexivity.
  - apply IHal; intros.
    apply H; right; assumption.
Qed.

Lemma collect_In:
  forall {A B} (f: A -> list B) al b,
    In b (collect f al) ->
    exists a, In a al /\ In b (f a).
Proof.
  induction al; intros; [dest_in|].
  simpl in H; apply in_app_or in H; destruct H.
  - eexists; split; [left; reflexivity|assumption].
  - specialize (IHal _ H).
    destruct IHal as [na [? ?]].
    eexists; split; [right; eassumption|assumption].
Qed.

Lemma incMap_In:
  forall {A B} (f: A -> IdxT -> B) al base ext b,
    In b (incMap f al base ext) ->
    exists a extb, In a al /\ b = f a (base~>extb).
Proof.
  induction al; simpl; intros; [exfalso; auto|].
  destruct H; subst; eauto.
  specialize (IHal _ _ _ H).
  destruct IHal as [pa [extb ?]]; dest; subst; eauto.
Qed.

Lemma app_eq_compare:
  forall {A} (l m n o: list A),
    l ++ m = n ++ o ->
    exists p, (l = n ++ p /\ o = p ++ m) \/
              (n = l ++ p /\ m = p ++ o).
Proof.
  induction l; simpl; intros.
  - subst; eexists; right; eauto.
  - destruct n as [|b n].
    + simpl in *; subst.
      eexists; left; eauto.
    + simpl in H; inv H.
      specialize (IHl _ _ _ H2).
      destruct IHl as [p ?]; destruct H; dest; subst; [|eauto].
      eexists; left; split; reflexivity.
Qed.

(** TODO: move to [Index.v] *)
Definition IdxPrefix (i1 i2: IdxT) :=
  exists ri, i2 = ri ++ i1.
Infix "~<" := IdxPrefix (at level 8).

Definition IdxDisj (i1 i2: IdxT) :=
  ~ IdxPrefix i1 i2 /\ ~ IdxPrefix i2 i1.
Infix "~*~" := IdxDisj (at level 8).

Definition IndsDisj (is1 is2: list IdxT) :=
  forall i1 i2, In i1 is1 -> In i2 is2 -> i1 ~*~ i2.

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

Lemma IdxDisj_not_eq:
  forall i1 i2, i1 ~*~ i2 -> i1 <> i2.
Proof.
  intros; intro Hx; subst.
  red in H; dest.
  elim H; apply IdxPrefix_refl.
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

(** TODO: move to [ImplTemplate.v] *)
Lemma singletonDNode_inds_prefix_base:
  forall bidx,
    Forall (fun idx => bidx ~< idx)
           (indsOf (fst (singletonDNode bidx))).
Proof.
  intros; simpl.
  repeat constructor.
  - apply IdxPrefix_refl.
  - exists [0]; reflexivity.
Qed.

Lemma tree2Topo_inds_prefix_base:
  forall tr bidx,
    Forall (fun idx => bidx ~< idx)
           (indsOf (fst (tree2Topo tr bidx))).
Proof.
  induction tr using tree_ind_l.
  intros; simpl.
  destruct l.
  - apply singletonDNode_inds_prefix_base.
  - inv H.
    simpl; constructor.
    + apply IdxPrefix_refl.
    + apply Forall_app.
      * specialize (H2 bidx~>0).
        eapply Forall_impl; [|eassumption].
        simpl; intros.
        eapply IdxPrefix_trans; [|eassumption].
        exists [0]; reflexivity.
      * apply collect_forall.
        intros dstr ?.
        apply in_map_iff in H.
        destruct H as [[dtr sifc] [? ?]]; simpl in *; subst.
        apply incMap_In in H0.
        destruct H0 as [str [extb ?]]; dest.
        rewrite Forall_forall in H3; specialize (H3 _ H bidx~>extb).
        rewrite <-H0 in H3; simpl in H3.
        eapply Forall_impl; [|eassumption].
        simpl; intros.
        eapply IdxPrefix_trans; [|eassumption].
        exists [extb]; reflexivity.
Qed.

Lemma tree2Topo_disj_inds:
  forall tr1 bidx1 tr2 bidx2,
    bidx1 ~*~ bidx2 ->
    DisjList (indsOf (fst (tree2Topo tr1 bidx1)))
             (indsOf (fst (tree2Topo tr2 bidx2))).
Proof.
  intros.
  apply IndsDisj_DisjList.
  eapply IdxDisj_base_IndsDisj; [eassumption|..];
    apply tree2Topo_inds_prefix_base.
Qed.

Lemma l1ExtOf_not_eq:
  forall bidx, l1ExtOf bidx <> bidx.
Proof.
  intros; induction bidx; [discriminate|].
  intro Hx; inv Hx; auto.
Qed.

Lemma singletonDNode_WfDTree:
  forall bidx, WfDTree (fst (singletonDNode bidx)).
Proof.
  intros; split.
  - red; simpl.
    repeat constructor; intro Hx; dest_in.
    unfold l1ExtOf, extendIdx in H.
    eapply l1ExtOf_not_eq; eauto.
  - red; simpl.
    match goal with
    | |- NoDup (?i1 :: ?i2 :: ?i3 :: ?inds) =>
      change (i1 :: i2 :: i3 :: inds) with ([i1; i2; i3] ++ inds)
    end.
    apply NoDup_DisjList.
    + solve_NoDup.
    + solve_NoDup.
    + match goal with
      | |- DisjList ?ll _ =>
        let e := fresh "e" in
        red; intro e; destruct (in_dec idx_dec e ll); [right|auto]; dest_in;
          intro Hx; dest_in; try discriminate
      end.
      * inv H; eapply l1ExtOf_not_eq; eauto.
      * inv H0; eapply l1ExtOf_not_eq; eauto.
      * inv H; eapply l1ExtOf_not_eq; eauto.
Qed.

Lemma tree2Topo_WfDTree:
  forall tr bidx, WfDTree (fst (tree2Topo tr bidx)).
Proof.
  induction tr using tree_ind_l.
  intros; simpl.
  destruct l.
  - apply singletonDNode_WfDTree.
  - remember (t :: l) as strs; clear Heqstrs t l.
    simpl; split.
    + red; simpl.
      constructor.
      * intro Hx; apply collect_In in Hx.
        destruct Hx as [a [? ?]].
        apply in_map_iff in H0; destruct H0 as [[dtr cifc] [? ?]].
        simpl in *; subst.
        apply incMap_In in H2.
        destruct H2 as [str [extb ?]]; dest.
        pose proof (tree2Topo_inds_prefix_base str bidx~>extb).
        rewrite <-H2 in H3; simpl in H3.
        rewrite Forall_forall in H3; specialize (H3 _ H1).
        eapply extendIdx_not_IdxPrefix; eassumption.
      * admit.
    + red; simpl.
      match goal with
      | |- NoDup (?i1 :: ?i2 :: ?i3 :: ?inds) =>
        change (i1 :: i2 :: i3 :: inds) with ([i1; i2; i3] ++ inds)
      end.
      apply NoDup_DisjList.
      * solve_NoDup.
      * admit.
      * admit.
Admitted.

Section System.
  Variable tr: tree.

  Local Definition topo := fst (tree2Topo tr 0).
  Local Definition cifc := snd (tree2Topo tr 0).

  Lemma mesi_impl_ORqsInit: GoodORqsInit (initsOf (impl tr)).
  Proof.
    apply initORqs_GoodORqsInit.
  Qed.

  Lemma mesi_topo_wf: WfDTree topo.
  Proof.
    apply tree2Topo_WfDTree.
  Qed.

End System.

