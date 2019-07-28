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

(** TODO: move to [Topology.v] *)
Lemma root_parentChnsOf_None:
  forall dtr oidx,
    WfDTree dtr ->
    oidx = rootOf dtr ->
    parentChnsOf oidx dtr = None.
Proof.
  intros; subst.
  destruct (parentChnsOf _ _) as [[dmc pidx]|] eqn:Hp; [|reflexivity].
  exfalso.
  apply parentChnsOf_case in Hp.
  destruct Hp as [ctr [? ?]].
  destruct H1; dest; subst.
  - eapply parent_child_not_eq; eauto.
  - apply parent_not_in_children in H0; [|assumption].
    apply parentChnsOf_child_indsOf in H1; auto.
Qed.

Lemma parentChnsOf_subtree:
  forall dtr (Hwf: WfDTree dtr) oidx root pidx,
    parentChnsOf oidx dtr = Some (root, pidx) ->
    exists odtr,
      subtree oidx dtr = Some odtr /\
      dmcOf odtr = root.
Proof.
  intros.
  apply parentChnsOf_Subtree in H.
  destruct H as [ctr [ptr ?]]; dest; subst.
  exists ctr.
  split; [|reflexivity].
  eapply Subtree_child_Subtree in H3; [|eassumption].
  rewrite <-rootOf_dmcOf.
  apply Subtree_subtree; auto.
Qed.

Lemma fold_left_base_c_minds_In:
  forall ifc ifcs bifc,
    SubList (c_minds ifc) (c_minds bifc) ->
    SubList (c_minds ifc) (c_minds (fold_left mergeCIfc ifcs bifc)).
Proof.
  induction ifcs as [|hifc ifcs]; simpl; intros; [assumption|].
  apply IHifcs.
  simpl; apply SubList_app_1; assumption.
Qed.

Lemma mergeCIfc_fold_left_c_minds_In:
  forall ifc ifcs,
    In ifc ifcs ->
    forall bifc,
      SubList (c_minds ifc) (c_minds (fold_left mergeCIfc ifcs bifc)).
Proof.
  induction ifcs; simpl; intros; [exfalso; auto|].
  destruct H; subst; [|auto].
  apply fold_left_base_c_minds_In.
  simpl; apply SubList_app_2, SubList_refl.
Qed.

Lemma in_app_or_4:
  forall {A} (a: A) (l1 l2 l3 l4: list A),
    In a ((l1 ++ l2) ++ (l3 ++ l4)) ->
    In a (l1 ++ l3) \/ In a (l2 ++ l4).
Proof.
  intros.
  apply in_app_or in H; destruct H.
  - apply in_app_or in H; destruct H.
    + left; apply in_or_app; auto.
    + right; apply in_or_app; auto.
  - apply in_app_or in H; destruct H.
    + left; apply in_or_app; auto.
    + right; apply in_or_app; auto.
Qed.    

Lemma tree2Topo_children_oidx_In:
  forall oidx bidx ctrs oss bcifc,
    In oidx ((c_li_indices (fold_left mergeCIfc (map snd (incMap tree2Topo ctrs bidx oss)) bcifc))
               ++ (c_l1_indices (fold_left mergeCIfc (map snd (incMap tree2Topo ctrs bidx oss)) bcifc))) ->
    In oidx (c_li_indices bcifc ++ c_l1_indices bcifc) \/
    exists ctr ofs,
      nth_error ctrs ofs = Some ctr /\
      In (fst (tree2Topo ctr bidx~>(oss + ofs)))
         (map fst (incMap tree2Topo ctrs bidx oss)) /\
      In (snd (tree2Topo ctr bidx~>(oss + ofs)))
         (map snd (incMap tree2Topo ctrs bidx oss)) /\
      In oidx ((c_li_indices (snd (tree2Topo ctr bidx~>(oss + ofs))))
                 ++ (c_l1_indices (snd (tree2Topo ctr bidx~>(oss + ofs))))).
Proof.
  induction ctrs as [|ctr ctrs]; simpl; intros;
    [left; assumption|].

  specialize (IHctrs _ _ H).
  destruct IHctrs.
  - simpl in H0; apply in_app_or_4 in H0; destruct H0.
    + left; assumption.
    + right; exists ctr, 0.
      rewrite Nat.add_0_r; auto.
  - destruct H0 as [nctr [ofs ?]]; dest.
    right; exists nctr, (S ofs).
    rewrite Nat.add_succ_r; auto.
Qed.

Lemma tree2Topo_children_ext_rq_In:
  forall erq bidx ctrs oss bcifc,
    In erq (c_merqs (fold_left mergeCIfc (map snd (incMap tree2Topo ctrs bidx oss)) bcifc)) ->
    In erq (c_merqs bcifc) \/
    exists ctr ofs,
      nth_error ctrs ofs = Some ctr /\
      In (fst (tree2Topo ctr bidx~>(oss + ofs)))
         (map fst (incMap tree2Topo ctrs bidx oss)) /\
      In (snd (tree2Topo ctr bidx~>(oss + ofs)))
         (map snd (incMap tree2Topo ctrs bidx oss)) /\
      In erq (c_merqs (snd (tree2Topo ctr bidx~>(oss + ofs)))).
Proof.
  induction ctrs as [|ctr ctrs]; simpl; intros;
    [left; assumption|].

  specialize (IHctrs _ _ H).
  destruct IHctrs.
  - simpl in H0; apply in_app_or in H0; destruct H0.
    + left; assumption.
    + right; exists ctr, 0.
      rewrite Nat.add_0_r; auto.
  - destruct H0 as [nctr [ofs ?]]; dest.
    right; exists nctr, (S ofs).
    rewrite Nat.add_succ_r; auto.
Qed.

Lemma tree2Topo_children_ext_rs_In:
  forall ers bidx ctrs oss bcifc,
    In ers (c_merss (fold_left mergeCIfc (map snd (incMap tree2Topo ctrs bidx oss)) bcifc)) ->
    In ers (c_merss bcifc) \/
    exists ctr ofs,
      nth_error ctrs ofs = Some ctr /\
      In (fst (tree2Topo ctr bidx~>(oss + ofs)))
         (map fst (incMap tree2Topo ctrs bidx oss)) /\
      In (snd (tree2Topo ctr bidx~>(oss + ofs)))
         (map snd (incMap tree2Topo ctrs bidx oss)) /\
      In ers (c_merss (snd (tree2Topo ctr bidx~>(oss + ofs)))).
Proof.
  induction ctrs as [|ctr ctrs]; simpl; intros;
    [left; assumption|].

  specialize (IHctrs _ _ H).
  destruct IHctrs.
  - simpl in H0; apply in_app_or in H0; destruct H0.
    + left; assumption.
    + right; exists ctr, 0.
      rewrite Nat.add_0_r; auto.
  - destruct H0 as [nctr [ofs ?]]; dest.
    right; exists nctr, (S ofs).
    rewrite Nat.add_succ_r; auto.
Qed.

(** TODO: move to [Topology.v] *)
Lemma subtree_indsOf:
  forall idx dtr str,
    subtree idx dtr = Some str ->
    In idx (indsOf dtr).
Proof.
  intros.
  pose proof (subtree_Subtree _ _ H).
  apply subtree_rootOf in H; subst.
  apply Subtree_indsOf in H0.
  apply H0.
  apply indsOf_root_in.
Qed.

Lemma subtree_collect_NoDup_find_some:
  forall trs,
    NoDup (collect indsOf trs) ->
    forall tr,
      In tr trs ->
      forall oidx otr,
        subtree oidx tr = Some otr ->
        find_some (subtree oidx) trs = Some otr.
Proof.
  induction trs as [|str trs]; simpl; intros; [exfalso; auto|].
  destruct H0; subst; [rewrite H1; reflexivity|].
  destruct (subtree oidx str) eqn:Hstr.
  - exfalso.
    apply subtree_indsOf in H1.
    apply subtree_indsOf in Hstr.
    apply (DisjList_NoDup idx_dec) in H.
    specialize (H oidx).
    destruct H; auto.
    elim H; eapply collect_in; eauto.
  - eapply IHtrs; eauto.
    eapply NoDup_app_weakening_2; eauto.
Qed.

Lemma parentChnsOf_child_Some_eq:
  forall dtr (Hwf: WfDTree dtr) ctr,
    In ctr (childrenOf dtr) ->
    forall oidx rp,
      parentChnsOf oidx ctr = Some rp ->
      parentChnsOf oidx dtr = Some rp.
Proof.
  intros.
  destruct rp as [root pidx].
  pose proof (parentChnsOf_child_indsOf _ _ H0).
  rewrite parentChnsOf_child_eq with (ctr:= ctr); try assumption.
  intro Hx; subst.
  rewrite root_parentChnsOf_None in H0.
  - discriminate.
  - destruct dtr; simpl in *; eapply wfDTree_child; eauto.
  - reflexivity.
Qed.

Lemma rqEdgeUpFrom_child_Some_eq:
  forall dtr (Hwf: WfDTree dtr) ctr,
    In ctr (childrenOf dtr) ->
    forall oidx rqUp,
      rqEdgeUpFrom ctr oidx = Some rqUp ->
      rqEdgeUpFrom dtr oidx = Some rqUp.
Proof.
  unfold rqEdgeUpFrom, upEdgesFrom; intros.
  destruct (parentChnsOf oidx ctr) as [rp|] eqn:Hrp; [|discriminate].
  apply parentChnsOf_child_Some_eq with (dtr:= dtr) in Hrp; auto.
  rewrite Hrp; assumption.
Qed.

Lemma rsEdgeUpFrom_child_Some_eq:
  forall dtr (Hwf: WfDTree dtr) ctr,
    In ctr (childrenOf dtr) ->
    forall oidx rqUp,
      rsEdgeUpFrom ctr oidx = Some rqUp ->
      rsEdgeUpFrom dtr oidx = Some rqUp.
Proof.
  unfold rsEdgeUpFrom, upEdgesFrom; intros.
  destruct (parentChnsOf oidx ctr) as [rp|] eqn:Hrp; [|discriminate].
  apply parentChnsOf_child_Some_eq with (dtr:= dtr) in Hrp; auto.
  rewrite Hrp; assumption.
Qed.

Lemma edgeDownTo_child_Some_eq:
  forall dtr (Hwf: WfDTree dtr) ctr,
    In ctr (childrenOf dtr) ->
    forall oidx rqUp,
      edgeDownTo ctr oidx = Some rqUp ->
      edgeDownTo dtr oidx = Some rqUp.
Proof.
  unfold edgeDownTo, downEdgesTo; intros.
  destruct (parentChnsOf oidx ctr) as [rp|] eqn:Hrp; [|discriminate].
  apply parentChnsOf_child_Some_eq with (dtr:= dtr) in Hrp; auto.
  rewrite Hrp; assumption.
Qed.

Lemma tree2Topo_RqRsChnsOnSystem_unfolded:
  forall tr bidx topo cifc oinds minds,
    tree2Topo tr bidx = (topo, cifc) ->
    oinds = cifc.(c_li_indices) ++ cifc.(c_l1_indices) ->
    minds = cifc.(c_minds) ->
    (* body of [RqRsChnsOnDTree] *)
    forall oidx,
      In oidx oinds ->
      exists odtr,
        subtree oidx topo = Some odtr /\
        SubList (dmcOf odtr).(dmc_ups) minds /\
        SubList (dmcOf odtr).(dmc_downs) minds.
Proof.
  induction tr using tree_ind_l.
  intros; subst.
  pose proof (tree2Topo_WfDTree (Node l) bidx) as Hwf.
  simpl in *; find_if_inside; subst.
  - inv H0.
    destruct H3; [subst|exfalso; auto].
    eexists; repeat ssplit.
    + unfold subtree, dmc_me.
      destruct (idx_dec _ _); [|exfalso; auto].
      reflexivity.
    + simpl; solve_SubList.
    + simpl; solve_SubList.

  - inv H0.
    simpl in H3.
    destruct (idx_dec bidx oidx); subst.
    1: {
      eexists; repeat ssplit.
      { unfold subtree, dmc_me.
        destruct (idx_dec _ _); [|exfalso; auto].
        reflexivity.
      }
      { simpl; solve_SubList. }
      { simpl; solve_SubList. }
    }
    destruct H3; [exfalso; auto|].
    simpl; destruct (idx_dec bidx oidx); [exfalso; auto|clear n1].

    apply tree2Topo_children_oidx_In in H0.
    destruct H0; [dest_in|].
    destruct H0 as [ctr [ofs ?]]; dest; simpl in *.

    destruct (tree2Topo ctr bidx~>ofs) as [cdtr cifc] eqn:Hchd; simpl in *.
    pose proof (nth_error_In _ _ H0).
    rewrite Forall_forall in H; specialize (H _ H4); clear H4.
    specialize (H _ _ _ _ _ Hchd eq_refl eq_refl _ H3).
    destruct H as [odtr ?]; dest.

    exists odtr; repeat ssplit.
    + eapply subtree_collect_NoDup_find_some; try eassumption.
      destruct Hwf.
      red in H6; simpl in H6; inv H6.
      assumption.
    + do 3 apply SubList_cons_right.
      eapply SubList_trans; [eassumption|].
      apply mergeCIfc_fold_left_c_minds_In; assumption.
    + do 3 apply SubList_cons_right.
      eapply SubList_trans; [eassumption|].
      apply mergeCIfc_fold_left_c_minds_In; assumption.
Qed.

Lemma tree2Topo_RqRsChnsOnSystem:
  forall {OStateIfc} tr bidx topo cifc (impl: System OStateIfc),
    tree2Topo tr bidx = (topo, cifc) ->
    map (@obj_idx _) impl.(sys_objs) = cifc.(c_li_indices) ++ cifc.(c_l1_indices) ->
    impl.(sys_minds) = cifc.(c_minds) ->
    RqRsChnsOnSystem topo impl.
Proof.
  intros.
  red; intros.
  eapply tree2Topo_RqRsChnsOnSystem_unfolded in H2; eauto.
  destruct H2 as [odtr ?]; dest.
  replace topo with (fst (tree2Topo tr bidx)) in * by (rewrite H; reflexivity).
  pose proof (parentChnsOf_subtree (tree2Topo_WfDTree tr bidx) _ H3).
  destruct H6 as [rodtr ?]; dest; subst.
  rewrite H6 in H2; inv H2.
  split; assumption.
Qed.

Lemma tree2Topo_ExtsOnDTree_unfolded:
  forall tr bidx topo cifc,
    tree2Topo tr bidx = (topo, cifc) ->
    (forall erq,
        In erq cifc.(c_merqs) ->
        exists eoidx, rqEdgeUpFrom topo eoidx = Some erq) /\
    (forall ers,
        In ers cifc.(c_merss) ->
        exists eoidx, edgeDownTo topo eoidx = Some ers).
Proof.
  induction tr using tree_ind_l; intros.
  pose proof (tree2Topo_WfDTree (Node l) bidx) as Hwf.
  simpl in *; find_if_inside; subst.
  - inv H0; clear; simpl.
    split; intros.
    + destruct H; [subst|exfalso; auto].
      exists (l1ExtOf bidx).
      cbv [rqEdgeUpFrom upEdgesFrom parentChnsOf]; simpl.
      cbv [hasIdx]; destruct (idx_dec _ _); [reflexivity|exfalso; auto].
    + destruct H; [subst|exfalso; auto].
      exists (l1ExtOf bidx).
      cbv [edgeDownTo downEdgesTo parentChnsOf]; simpl.
      cbv [hasIdx]; destruct (idx_dec _ _); [reflexivity|exfalso; auto].
    
  - inv H0; simpl; split; intros.
    + apply tree2Topo_children_ext_rq_In in H0.
      destruct H0; [dest_in|].
      destruct H0 as [ctr [ofs ?]]; dest; simpl in *.
      destruct (tree2Topo ctr bidx~>ofs) as [cdtr cifc] eqn:Hchd; simpl in *.
      pose proof (nth_error_In _ _ H0).
      rewrite Forall_forall in H; specialize (H _ H4); clear H4.
      specialize (H _ _ _ Hchd); dest.
      specialize (H _ H3).
      destruct H as [eoidx ?].
      exists eoidx.
      eapply rqEdgeUpFrom_child_Some_eq; eauto.

    + apply tree2Topo_children_ext_rs_In in H0.
      destruct H0; [dest_in|].
      destruct H0 as [ctr [ofs ?]]; dest; simpl in *.
      destruct (tree2Topo ctr bidx~>ofs) as [cdtr cifc] eqn:Hchd; simpl in *.
      pose proof (nth_error_In _ _ H0).
      rewrite Forall_forall in H; specialize (H _ H4); clear H4.
      specialize (H _ _ _ Hchd); dest.
      specialize (H4 _ H3).
      destruct H4 as [eoidx ?].
      exists eoidx.
      eapply edgeDownTo_child_Some_eq; eauto.
Qed.

Lemma tree2Topo_ExtsOnDTree:
  forall {OStateIfc} tr bidx topo cifc (impl: System OStateIfc),
    tree2Topo tr bidx = (topo, cifc) ->
    impl.(sys_merqs) = cifc.(c_merqs) -> impl.(sys_merss) = cifc.(c_merss) ->
    ExtsOnDTree topo impl.
Proof.
  intros.
  apply tree2Topo_ExtsOnDTree_unfolded in H; dest.
  split; red; intros.
  - rewrite H0 in H3; auto.
  - rewrite H1 in H3; auto.
Qed.

Section System.
  Variable tr: tree.

  Local Definition topo := fst (tree2Topo tr 0).
  Local Definition cifc := snd (tree2Topo tr 0).
  Local Definition impl := impl tr.

  Lemma mesi_GoodORqsInit: GoodORqsInit (initsOf impl).
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

  Lemma mesi_RqRsChnsOnSystem: RqRsChnsOnSystem topo impl.
  Proof.
    eapply tree2Topo_RqRsChnsOnSystem with (tr0:= tr) (bidx:= [0]); try reflexivity.
    - unfold topo, Mesi.cifc; destruct (tree2Topo _ _); reflexivity.
    - simpl; rewrite map_app; f_equal.
      + induction (c_li_indices (Mesi.cifc tr)); [reflexivity|].
        simpl; congruence.
      + induction (c_l1_indices (Mesi.cifc tr)); [reflexivity|].
        simpl; congruence.
  Qed.

  Lemma mesi_ExtsOnDTree: ExtsOnDTree topo impl.
  Proof.
    eapply tree2Topo_ExtsOnDTree with (tr0:= tr) (bidx:= [0]); try reflexivity.
    unfold topo, Mesi.cifc; destruct (tree2Topo _ _); reflexivity.
  Qed.
  
  Lemma mesi_impl_RqRsDTree: RqRsDTree topo impl.
  Proof.
    red; repeat ssplit.
    - auto using mesi_WfDTree.
    - auto using mesi_RqRsChnsOnDTree.
    - auto using mesi_RqRsChnsOnSystem.
    - auto using mesi_ExtsOnDTree.
  Qed.

End System.

