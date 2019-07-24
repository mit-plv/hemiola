Require Import Bool Vector List String Peano_dec Omega.
Require Import Common FMap HVector ListSupport IndexSupport.
Require Import Syntax Topology Semantics.
Require Import RqRsLang.

Require Import Ex.Spec Ex.SpecSv Ex.ImplTemplate Ex.Mesi.
Require Import Ex.Mesi.Mesi.

Set Implicit Arguments.

Local Open Scope list.
Local Open Scope hvec.
Local Open Scope fmap.

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

Lemma singletonDNode_chns_prefix_base:
  forall bidx,
    Forall (fun idx => bidx ~< idx /\ List.length bidx < List.length idx)
           (chnsOf (fst (singletonDNode bidx))).
Proof.
  intros; simpl.
  repeat constructor;
    try (eexists [_]; reflexivity);
    try (eexists [_; _]; reflexivity).
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
        destruct H0 as [str [ofs ?]]; dest.
        apply nth_error_In in H.
        rewrite Forall_forall in H3; specialize (H3 _ H bidx~>(1 + ofs)).
        rewrite <-H0 in H3; simpl in H3.
        eapply Forall_impl; [|eassumption].
        simpl; intros.
        eapply IdxPrefix_trans; [|eassumption].
        eexists [_]; reflexivity.
Qed.

Lemma tree2Topo_chns_prefix_base:
  forall tr bidx,
    Forall (fun idx => bidx ~< idx /\ List.length bidx < List.length idx)
           (chnsOf (fst (tree2Topo tr bidx))).
Proof.
  induction tr using tree_ind_l.
  intros; simpl.
  destruct l.
  - apply singletonDNode_chns_prefix_base.
  - inv H.
    simpl; repeat constructor.
    1-3: (eexists [_]; reflexivity).
    apply Forall_app.
    + specialize (H2 bidx~>0).
      eapply Forall_impl; [|eassumption].
      simpl; intros; dest.
      split; [|omega].
      eapply IdxPrefix_trans; [|eassumption].
      exists [0]; reflexivity.
    + apply collect_forall.
      intros dstr ?.
      apply in_map_iff in H.
      destruct H as [[dtr sifc] [? ?]]; simpl in *; subst.
      apply incMap_In in H0.
      destruct H0 as [str [ofs ?]]; dest.
      apply nth_error_In in H.
      rewrite Forall_forall in H3; specialize (H3 _ H bidx~>(1 + ofs)).
      rewrite <-H0 in H3; simpl in H3.
      eapply Forall_impl; [|eassumption].
      simpl; intros; dest.
      split; [|omega].
      eapply IdxPrefix_trans; [|eassumption].
      eexists [_]; reflexivity.
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

Lemma tree2Topo_disj_chns:
  forall tr1 bidx1 tr2 bidx2,
    bidx1 ~*~ bidx2 ->
    DisjList (chnsOf (fst (tree2Topo tr1 bidx1)))
             (chnsOf (fst (tree2Topo tr2 bidx2))).
Proof.
  intros.
  apply IndsDisj_DisjList.
  eapply IdxDisj_base_IndsDisj; [eassumption|..].
  - eapply Forall_impl; [|apply tree2Topo_chns_prefix_base].
    simpl; intros; dest; auto.
  - eapply Forall_impl; [|apply tree2Topo_chns_prefix_base].
    simpl; intros; dest; auto.
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
  find_if_inside; subst.
  - apply singletonDNode_WfDTree.
  - simpl; split.
    + red; simpl.
      constructor.
      * intro Hx; apply collect_in_exist in Hx.
        destruct Hx as [a [? ?]].
        apply in_map_iff in H0; destruct H0 as [[dtr cifc] [? ?]].
        simpl in *; subst.
        apply incMap_In in H2.
        destruct H2 as [str [ofs ?]]; dest; simpl in *.
        apply nth_error_In in H0.
        pose proof (tree2Topo_inds_prefix_base str bidx~>ofs).
        rewrite <-H2 in H3; simpl in H3.
        rewrite Forall_forall in H3; specialize (H3 _ H1).
        eapply extendIdx_not_IdxPrefix; eassumption.

      * apply collect_NoDup.
        { intros.
          apply in_map_iff in H0; destruct H0 as [[dtr cifc] [? ?]].
          simpl in *; subst.
          apply incMap_In in H1.
          destruct H1 as [str [extb ?]]; dest; simpl in *.
          apply nth_error_In in H0.
          rewrite Forall_forall in H; specialize (H _ H0 bidx~>extb).
          rewrite <-H1 in H.
          apply H.
        }
        { intros.
          apply nth_error_map_iff in H1; destruct H1 as [[dtr1 cifc1] [? ?]].
          apply nth_error_map_iff in H2; destruct H2 as [[dtr2 cifc2] [? ?]].
          simpl in *; subst.
          apply incMap_nth_error in H3; destruct H3 as [str1 [? ?]]. 
          apply incMap_nth_error in H4; destruct H4 as [str2 [? ?]].
          simpl in *.
          replace a1 with (fst (tree2Topo str1 bidx~>n1))
            by (rewrite <-H2; reflexivity).
          replace a2 with (fst (tree2Topo str2 bidx~>n2))
            by (rewrite <-H4; reflexivity).
          apply tree2Topo_disj_inds.
          apply extendIdx_IdxDisj; auto.
        }

    + red; simpl.
      match goal with
      | |- NoDup (?i1 :: ?i2 :: ?i3 :: ?inds) =>
        change (i1 :: i2 :: i3 :: inds) with ([i1; i2; i3] ++ inds)
      end.
      apply NoDup_DisjList.
      * solve_NoDup.
      * apply collect_NoDup.
        { intros.
          apply in_map_iff in H0; destruct H0 as [[dtr cifc] [? ?]].
          simpl in *; subst.
          apply incMap_In in H1.
          destruct H1 as [str [extb ?]]; dest; simpl in *.
          apply nth_error_In in H0.
          rewrite Forall_forall in H; specialize (H _ H0 bidx~>extb).
          rewrite <-H1 in H.
          apply H.
        }
        { intros.
          apply nth_error_map_iff in H1; destruct H1 as [[dtr1 cifc1] [? ?]].
          apply nth_error_map_iff in H2; destruct H2 as [[dtr2 cifc2] [? ?]].
          simpl in *; subst.
          apply incMap_nth_error in H3; destruct H3 as [str1 [? ?]]. 
          apply incMap_nth_error in H4; destruct H4 as [str2 [? ?]].
          simpl in *.
          replace a1 with (fst (tree2Topo str1 bidx~>n1))
            by (rewrite <-H2; reflexivity).
          replace a2 with (fst (tree2Topo str2 bidx~>n2))
            by (rewrite <-H4; reflexivity).
          apply tree2Topo_disj_chns.
          apply extendIdx_IdxDisj; auto.
        }
      * apply DisjList_map with (f:= @List.length _).
        apply (DisjList_spec_1 eq_nat_dec).
        intros.
        assert (a = S (List.length bidx)) by (dest_in; reflexivity).
        clear H0; subst.
        intro Hx; apply in_map_iff in Hx.
        destruct Hx as [idx ?]; dest.
        apply collect_in_exist in H1; destruct H1 as [sdtr [? ?]].
        apply in_map_iff in H1; destruct H1 as [[dtr sifc] [? ?]].
        simpl in *; subst.
        apply incMap_In in H3; destruct H3 as [str [ofs [? ?]]].
        simpl in *.
        replace sdtr with (fst (tree2Topo str bidx~>ofs)) in H2
          by (rewrite <-H3; reflexivity).
        pose proof (tree2Topo_chns_prefix_base str bidx~>ofs).
        rewrite Forall_forall in H4; specialize (H4 _ H2); dest.
        simpl in H5; omega.
Qed.

Lemma tree2Topo_RqRsChnsOnDTree_root:
  forall str bidx droot dstrs,
    fst (tree2Topo str bidx) = DNode droot dstrs ->
    exists rqUp rsUp down : IdxT,
      dmc_ups droot = [rqUp; rsUp] /\ dmc_downs droot = [down].
Proof.
  destruct str; simpl; intros.
  find_if_inside; inv H; simpl; eauto.
Qed.
                                                        
Lemma tree2Topo_RqRsChnsOnDTree:
  forall tr bidx, RqRsChnsOnDTree (fst (tree2Topo tr bidx)).
Proof.
  induction tr using tree_ind_l; intros.
  red; intros.
  simpl in H0.
  destruct (nil_dec l); subst.
  - simpl in H0.
    destruct (hasIdx _ _) eqn:Hoidx; [|discriminate].
    destruct d; inv H0.
    apply hasIdx_Some in Hoidx; simpl in Hoidx; dest; subst.
    inv H0; simpl in *; eauto.
  - simpl in H0.
    destruct (find_some _ _) eqn:Hfs.
    + clear H.
      destruct d; inv H0.
      apply find_some_exist in Hfs.
      destruct Hfs as [sdtr [? ?]].
      apply hasIdx_Some in H0; dest; subst.
      apply in_map_iff in H; destruct H as [[dtr sifc] [? ?]].
      simpl in *; subst.
      apply incMap_In in H0; destruct H0 as [str [ofs [? ?]]].
      eapply tree2Topo_RqRsChnsOnDTree_root.
      rewrite <-H0; reflexivity.
    + apply find_some_exist in H0.
      destruct H0 as [sdtr [? ?]].
      apply in_map_iff in H0; destruct H0 as [[dtr sifc] [? ?]].
      simpl in *; subst.
      apply incMap_In in H2; destruct H2 as [str [ofs [? ?]]].
      apply nth_error_In in H0.
      rewrite Forall_forall in H; specialize (H _ H0).
      specialize (H bidx~>ofs); simpl in H2; rewrite <-H2 in H; simpl in H.
      eapply H; eauto.
Qed.
    
Section System.
  Variable tr: tree.

  Local Definition topo := fst (tree2Topo tr 0).
  Local Definition cifc := snd (tree2Topo tr 0).

  Lemma mesi_GoodORqsInit: GoodORqsInit (initsOf (impl tr)).
  Proof.
    apply initORqs_GoodORqsInit.
  Qed.

  Lemma mesi_WfDTree: WfDTree topo.
  Proof.
    apply tree2Topo_WfDTree.
  Qed.

  Lemma mesi_RqRsChnsOnDTree: RqRsChnsOnDTree topo.
  Proof.
    apply tree2Topo_RqRsChnsOnDTree.
  Qed.

End System.

