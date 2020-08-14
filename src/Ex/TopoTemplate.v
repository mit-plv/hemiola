Require Import PeanoNat List FMap Lia.
Require Import Common Topology IndexSupport Syntax Semantics.
Require Import RqRsLang.

Set Implicit Arguments.

Local Open Scope list.
Local Open Scope fmap.

Inductive tree :=
| Node: list tree -> tree.

Section tree_ind_l.
  Variables (P: tree -> Prop)
            (f: forall l, Forall P l -> P (Node l)).

  Fixpoint tree_ind_l (t: tree): P t :=
    match t with
    | Node sts =>
      f (list_ind (Forall P) (Forall_nil P)
                  (fun st _ IHl => Forall_cons st (tree_ind_l st) IHl)
                  sts)
    end.
End tree_ind_l.

Definition rqUpIdx: nat := 0.
Definition rsUpIdx: nat := 1.
Definition downIdx: nat := 2.

Section IncMap.
  Context {A B: Type}.
  Variable f: A -> IdxT -> B.

  Fixpoint incMap (avs: list A) (baseIdx: IdxT) (ext: nat): list B :=
    match avs with
    | nil => nil
    | av :: avs' =>
      f av (baseIdx~>ext) :: incMap avs' baseIdx (S ext)
    end.

  Lemma incMap_In:
    forall al ofs a,
      nth_error al ofs = Some a ->
      forall base ext,
        In (f a (base~>(ext + ofs))) (incMap al base ext).
  Proof.
    induction al; simpl; intros; [destruct ofs; discriminate|].
    destruct ofs; simpl in *.
    - inv H; left; rewrite Nat.add_0_r; reflexivity.
    - right.
      specialize (IHal _ _ H base (S ext)).
      rewrite Nat.add_succ_r.
      assumption.
  Qed.

  Lemma incMap_In_implies:
    forall al base ext b,
      In b (incMap al base ext) ->
      exists a ofs,
        nth_error al ofs = Some a /\ b = f a (base~>(ext + ofs)).
  Proof.
    induction al; simpl; intros; [exfalso; auto|].
    destruct H; subst.
    - exists a, 0; split; [reflexivity|].
      rewrite Nat.add_0_r; reflexivity.
    - specialize (IHal _ _ _ H).
      destruct IHal as [pa [ofs ?]]; dest; subst.
      exists pa, (S ofs); split; [assumption|].
      rewrite Nat.add_succ_r; reflexivity.
  Qed.

  Lemma incMap_nth_error:
    forall al base ext n b,
      nth_error (incMap al base ext) n = Some b ->
      exists a, nth_error al n = Some a /\ b = f a (base~>(ext + n)).
  Proof.
    induction al; simpl; intros; [destruct n; discriminate|].
    destruct n.
    - inv H; exists a; rewrite Nat.add_0_r; auto.
    - specialize (IHal _ _ _ _ H).
      destruct IHal as [na [? ?]]; subst.
      exists na; split; [assumption|].
      rewrite Nat.add_succ_r; reflexivity.
  Qed.

End IncMap.

(* NOTE: [c_li_indices] contains the root which is a main memory.
 * In order to access the main memory index, just use [rootOf].
 *
 * [tree] is general enough to represent memory structures that have an LLC
 * (last-level cache) just before the main memory. In this case the root will
 * have a single child that reflects to the LLC.
 *)
Record CIfc :=
  { c_li_indices: list IdxT;
    c_l1_indices: list IdxT;
    c_minds: list IdxT;
    c_merqs: list IdxT;
    c_merss: list IdxT
  }.

Definition emptyCIfc :=
  {| c_li_indices := nil; c_l1_indices := nil;
     c_minds := nil; c_merqs := nil; c_merss := nil |}.

Definition mergeCIfc (ci1 ci2: CIfc) :=
  {| c_li_indices := ci1.(c_li_indices) ++ ci2.(c_li_indices);
     c_l1_indices := ci1.(c_l1_indices) ++ ci2.(c_l1_indices);
     c_minds := ci1.(c_minds) ++ ci2.(c_minds);
     c_merqs := ci1.(c_merqs) ++ ci2.(c_merqs);
     c_merss := ci1.(c_merss) ++ ci2.(c_merss) |}.

Definition l1ExtOf (idx: IdxT): IdxT :=
  idx~>0.

Definition singletonDNode (idx: IdxT): DTree * CIfc :=
  let eidx := l1ExtOf idx in
  (DNode {| dmc_me := idx;
            dmc_ups := [idx~>rqUpIdx; idx~>rsUpIdx];
            dmc_downs := [idx~>downIdx] |}
         [DNode {| dmc_me := eidx;
                   dmc_ups := [eidx~>rqUpIdx; eidx~>rsUpIdx];
                   dmc_downs := [eidx~>downIdx] |} nil],
   {| c_li_indices := nil;
      c_l1_indices := [idx];
      c_minds := [idx~>rqUpIdx; idx~>rsUpIdx; idx~>downIdx];
      c_merqs := [eidx~>rqUpIdx];
      c_merss := [eidx~>downIdx] |}).

Fixpoint tree2Topo (tr: tree) (curIdx: IdxT): DTree * CIfc :=
  match tr with
  | Node ctrs =>
    if nil_dec ctrs then singletonDNode curIdx
    else
      let stp := incMap tree2Topo ctrs curIdx 0 in
      let strs := map fst stp in
      let sci := fold_left mergeCIfc (map snd stp) emptyCIfc in
      (DNode {| dmc_me := curIdx;
                dmc_ups := [curIdx~>rqUpIdx; curIdx~>rsUpIdx];
                dmc_downs := [curIdx~>downIdx] |} strs,
       mergeCIfc
         {| c_li_indices := [curIdx];
            c_l1_indices := nil;
            c_minds := [curIdx~>rqUpIdx; curIdx~>rsUpIdx; curIdx~>downIdx];
            c_merqs := nil;
            c_merss := nil |}
         sci)
  end.

Definition rqUpFrom (cidx: IdxT): IdxT :=
  cidx~>rqUpIdx.
Definition rsUpFrom (cidx: IdxT): IdxT :=
  cidx~>rsUpIdx.
Definition downTo (cidx: IdxT): IdxT :=
  cidx~>downIdx.
Definition objIdxOf (midx: IdxT) := idxTl midx.

Definition TreeTopoNode (dtr: DTree) :=
  forall cidx oidx,
    parentIdxOf dtr cidx = Some oidx ->
    rqEdgeUpFrom dtr cidx = Some (rqUpFrom cidx) /\
    rsEdgeUpFrom dtr cidx = Some (rsUpFrom cidx) /\
    edgeDownTo dtr cidx = Some (downTo cidx).

Definition TreeTopoEdge (dtr: DTree) :=
  forall oidx midx,
    (rqEdgeUpFrom dtr oidx = Some midx \/
     rsEdgeUpFrom dtr oidx = Some midx \/
     edgeDownTo dtr oidx = Some midx) ->
    oidx = objIdxOf midx.

Definition TreeTopoChildrenInds (dtr: DTree) :=
  forall sidx str,
    subtree sidx dtr = Some str ->
    NoPrefix (childrenIndsOf str).

Definition TreeTopo (dtr: DTree) :=
  (TreeTopoNode dtr /\ TreeTopoEdge dtr) /\
  TreeTopoChildrenInds dtr.

Section TreeTopo.

  Lemma l1ExtOf_not_eq:
    forall bidx, l1ExtOf bidx <> bidx.
  Proof.
    intros; induction bidx; [discriminate|].
    intro Hx; inv Hx; auto.
  Qed.

  Lemma tree2Topo_root_idx:
    forall tr bidx,
      rootOf (fst (tree2Topo tr bidx)) = bidx.
  Proof.
    destruct tr; simpl; intros.
    find_if_inside; reflexivity.
  Qed.

  Lemma tree2Topo_root_edges:
    forall tr bidx dtr ifc,
      tree2Topo tr bidx = (dtr, ifc) ->
      hd_error (dmc_ups (dmcOf dtr)) = Some (rqUpFrom (rootOf dtr)) /\
      hd_error (tl (dmc_ups (dmcOf dtr))) = Some (rsUpFrom (rootOf dtr)) /\
      hd_error (dmc_downs (dmcOf dtr)) = Some (downTo (rootOf dtr)).
  Proof.
    destruct tr; simpl; intros; find_if_inside;
      try (inv H; simpl; auto; fail).
  Qed.

  Lemma singletonDNode_TreeTopoNode:
    forall bidx, TreeTopoNode (fst (singletonDNode bidx)).
  Proof.
    intros; red; intros.
    pose proof (parentIdxOf_child_indsOf _ _ H).
    cbv [rqEdgeUpFrom rsEdgeUpFrom edgeDownTo
                      upEdgesFrom downEdgesTo parentChnsOf]; cbn.
    dest_in; simpl in *.
    - exfalso.
      cbv [parentIdxOf parentChnsOf] in H; cbn in H.
      destruct (hasIdx _ _) eqn:Hhi; [|discriminate].
      unfold hasIdx in Hhi.
      destruct (idx_dec _ _); [|discriminate].
      simpl in e; eapply l1ExtOf_not_eq; eauto.
    - clear.
      unfold hasIdx.
      destruct (idx_dec _ _); [auto|].
      exfalso; simpl in n; auto.
  Qed.

  Lemma tree2Topo_TreeTopoNode:
    forall tr bidx, TreeTopoNode (fst (tree2Topo tr bidx)).
  Proof.
    induction tr using tree_ind_l; simpl; intros.
    find_if_inside; [apply singletonDNode_TreeTopoNode|].
    simpl; red; intros.
    cbv [parentIdxOf rqEdgeUpFrom rsEdgeUpFrom edgeDownTo
                     upEdgesFrom downEdgesTo] in *.
    destruct (parentChnsOf _ _) as [[croot pidx]|] eqn:Hp;
      [inv H0; simpl|discriminate].
    apply parentChnsOf_case in Hp.
    destruct Hp as [cdtr ?]; dest; simpl in *.
    destruct H1; dest; subst.

    - apply in_map_iff in H0.
      destruct H0 as [[ctr cifc] [? ?]]; simpl in *; subst.
      apply incMap_In_implies in H1.
      destruct H1 as [ctr [ofs [? ?]]]; simpl in *.
      apply nth_error_In in H0.
      eapply tree2Topo_root_edges; eauto.

    - apply in_map_iff in H0.
      destruct H0 as [[ctr cifc] [? ?]]; simpl in *; subst.
      apply incMap_In_implies in H2.
      destruct H2 as [ctr [ofs [? ?]]]; simpl in *.
      apply nth_error_In in H0.
      rewrite Forall_forall in H; specialize (H _ H0 bidx~>ofs).
      rewrite <-H2 in H; simpl in H.
      specialize (H cidx oidx).
      cbv [parentIdxOf rqEdgeUpFrom rsEdgeUpFrom edgeDownTo
                       upEdgesFrom downEdgesTo] in H.
      rewrite H1 in H; simpl in H; auto.
  Qed.

  Lemma singletonDNode_TreeTopoEdge:
    forall bidx, TreeTopoEdge (fst (singletonDNode bidx)).
  Proof.
    intros; red; intros.
    cbv [rqEdgeUpFrom rsEdgeUpFrom edgeDownTo upEdgesFrom downEdgesTo] in H.
    destruct (parentChnsOf oidx _) as [[croot pidx]|] eqn:Hp; simpl in H;
      [|destruct H as [|[|]]; discriminate].
    pose proof (parentChnsOf_child_indsOf _ _ Hp).
    dest_in; simpl in *.
    - exfalso.
      destruct (hasIdx _ _) eqn:Hhi; [|discriminate].
      unfold hasIdx in Hhi.
      destruct (idx_dec _ _); [|discriminate].
      simpl in e; eapply l1ExtOf_not_eq; eauto.
    - unfold hasIdx in Hp.
      destruct (idx_dec _ _).
      + inv Hp; simpl in *.
        destruct H as [|[|]]; inv H; reflexivity.
      + exfalso; simpl in n; auto.
  Qed.

  Lemma tree2Topo_TreeTopoEdge:
    forall tr bidx, TreeTopoEdge (fst (tree2Topo tr bidx)).
  Proof.
    induction tr using tree_ind_l; simpl; intros.
    find_if_inside; [apply singletonDNode_TreeTopoEdge|].
    simpl; red; intros.
    cbv [parentIdxOf rqEdgeUpFrom rsEdgeUpFrom edgeDownTo
                     upEdgesFrom downEdgesTo] in H0.
    destruct (parentChnsOf _ _) as [[croot pidx]|] eqn:Hp;
      simpl in H0; [|destruct H0 as [|[|]]; discriminate].
    apply parentChnsOf_case in Hp.
    destruct Hp as [cdtr ?]; dest; simpl in *.
    destruct H2; dest; subst.

    - apply in_map_iff in H1.
      destruct H1 as [[ctr cifc] [? ?]]; simpl in *; subst.
      apply incMap_In_implies in H2.
      destruct H2 as [ctr [ofs [? ?]]]; simpl in *.
      pose proof (tree2Topo_root_edges _ _ (eq_sym H2)); dest.
      destruct H0 as [|[|]].
      + rewrite H0 in H3; inv H3; reflexivity.
      + rewrite H0 in H4; inv H4; reflexivity.
      + rewrite H0 in H5; inv H5; reflexivity.

    - apply in_map_iff in H1.
      destruct H1 as [[ctr cifc] [? ?]]; simpl in *; subst.
      apply incMap_In_implies in H3.
      destruct H3 as [ctr [ofs [? ?]]]; simpl in *.
      apply nth_error_In in H1.
      rewrite Forall_forall in H; specialize (H _ H1 bidx~>ofs).
      rewrite <-H3 in H; simpl in H.
      specialize (H oidx midx).
      cbv [parentIdxOf rqEdgeUpFrom rsEdgeUpFrom edgeDownTo
                       upEdgesFrom downEdgesTo] in H.
      rewrite H2 in H; simpl in H; auto.
  Qed.

  Lemma singletonDNode_TreeTopoChildrenInds:
    forall bidx, TreeTopoChildrenInds (fst (singletonDNode bidx)).
  Proof.
    intros; red; intros.
    cbv [singletonDNode fst subtree dmc_me find_some] in H.
    destruct (idx_dec bidx sidx).
    - inv H; cbn.
      apply NoPrefix_singleton.
    - destruct (idx_dec _ _).
      + inv H; cbn.
        apply NoPrefix_nil.
      + discriminate.
  Qed.

  Lemma tree2Topo_children_NoPrefix:
    forall ctrs base ofs,
      NoPrefix (map rootOf (map fst (incMap tree2Topo ctrs base ofs))).
  Proof.
    induction ctrs as [|ctr ctrs]; simpl; intros; [apply NoPrefix_nil|].
    apply NoPrefix_cons; [apply IHctrs|].
    intros.
    apply in_map_iff in H; destruct H as [cdtr [? ?]]; subst.
    apply in_map_iff in H0; destruct H0 as [[rcdtr cifc] [? ?]].
    simpl in *; subst.
    apply incMap_In_implies in H0; destruct H0 as [rctr [rofs [? ?]]].
    replace cdtr with (fst (tree2Topo rctr base~>(S ofs + rofs)))
      by (rewrite <-H0; reflexivity).
    do 2 rewrite tree2Topo_root_idx.
    apply extendIdx_IdxDisj.
    lia.
  Qed.

  Lemma tree2Topo_TreeTopoChildrenInds:
    forall tr bidx, TreeTopoChildrenInds (fst (tree2Topo tr bidx)).
  Proof.
    induction tr using tree_ind_l; simpl; intros.
    find_if_inside; [apply singletonDNode_TreeTopoChildrenInds|].
    simpl; red; intros.
    simpl in H0; find_if_inside; subst.
    - inv H0.
      unfold childrenIndsOf; simpl.
      apply tree2Topo_children_NoPrefix.
    - apply find_some_exist in H0.
      destruct H0 as [sdtr [? ?]].
      apply in_map_iff in H0; destruct H0 as [[dtr cifc] [? ?]].
      simpl in *; subst.
      apply incMap_In_implies in H2.
      destruct H2 as [ctr [ofs [? ?]]]; simpl in *.
      apply nth_error_In in H0.
      rewrite Forall_forall in H; specialize (H _ H0 bidx~>ofs).
      rewrite <-H2 in H; simpl in H.
      eapply H; eauto.
  Qed.

  Lemma tree2Topo_TreeTopo:
    forall tr bidx, TreeTopo (fst (tree2Topo tr bidx)).
  Proof.
    intros; red; repeat ssplit.
    - apply tree2Topo_TreeTopoNode.
    - apply tree2Topo_TreeTopoEdge.
    - apply tree2Topo_TreeTopoChildrenInds.
  Qed.

End TreeTopo.

Definition WfCIfc (cifc: CIfc) :=
  NoDup (c_li_indices cifc ++ c_l1_indices cifc) /\
  NoDup (c_minds cifc ++ c_merqs cifc ++ c_merss cifc).

Section Facts.

  Lemma c_merqs_l1_rqUpFrom:
    forall tr bidx,
      c_merqs (snd (tree2Topo tr bidx)) =
      map (fun cidx => rqUpFrom (l1ExtOf cidx)) (c_l1_indices (snd (tree2Topo tr bidx))).
  Proof.
    induction tr using tree_ind_l; simpl; intros.
    find_if_inside; [reflexivity|].
    simpl.
    clear n.

    assert (c_merqs emptyCIfc =
            map (fun cidx => rqUpFrom (l1ExtOf cidx)) (c_l1_indices emptyCIfc))
      by reflexivity.
    generalize H0; clear H0.
    generalize emptyCIfc as bcifc.
    generalize 0 as ofs.
    induction l; simpl; intros; [assumption|].
    inv H; apply IHl; auto.
    simpl; rewrite map_app; congruence.
  Qed.

  Lemma c_merss_l1_downTo:
    forall tr bidx,
      c_merss (snd (tree2Topo tr bidx)) =
      map (fun cidx => downTo (l1ExtOf cidx)) (c_l1_indices (snd (tree2Topo tr bidx))).
  Proof.
    induction tr using tree_ind_l; simpl; intros.
    find_if_inside; [reflexivity|].
    simpl.
    clear n.

    assert (c_merss emptyCIfc =
            map (fun cidx => downTo (l1ExtOf cidx)) (c_l1_indices emptyCIfc))
      by reflexivity.
    generalize H0; clear H0.
    generalize emptyCIfc as bcifc.
    generalize 0 as ofs.
    induction l; simpl; intros; [assumption|].
    inv H; apply IHl; auto.
    simpl; rewrite map_app; congruence.
  Qed.

  Lemma c_l1_indices_fold_collect_SubList:
    forall ctrs,
      Forall
        (fun ctr =>
           forall bidx,
             SubList (c_l1_indices (snd (tree2Topo ctr bidx)))
                     (indsOf (fst (tree2Topo ctr bidx)))) ctrs ->
      forall bidx oss bcifc,
        SubList (c_l1_indices (fold_left mergeCIfc (map snd (incMap tree2Topo ctrs bidx oss))
                                         bcifc))
                ((collect indsOf (map fst (incMap tree2Topo ctrs bidx oss)))
                   ++ c_l1_indices bcifc).
  Proof.
    induction ctrs; simpl; intros; [apply SubList_refl|].
    inv H; specialize (IHctrs H3); clear H3.
    eapply SubList_trans; [apply IHctrs|].
    apply SubList_app_3.
    - apply SubList_app_1, SubList_app_2, SubList_refl.
    - simpl; apply SubList_app_3.
      + apply SubList_app_2, SubList_refl.
      + apply SubList_app_1, SubList_app_1; auto.
  Qed.

  Lemma c_li_indices_fold_collect_SubList:
    forall ctrs,
      Forall
        (fun ctr =>
           forall bidx,
             SubList (c_li_indices (snd (tree2Topo ctr bidx)))
                     (indsOf (fst (tree2Topo ctr bidx)))) ctrs ->
      forall bidx oss bcifc,
        SubList (c_li_indices (fold_left mergeCIfc (map snd (incMap tree2Topo ctrs bidx oss))
                                         bcifc))
                ((collect indsOf (map fst (incMap tree2Topo ctrs bidx oss)))
                   ++ c_li_indices bcifc).
  Proof.
    induction ctrs; simpl; intros; [apply SubList_refl|].
    inv H; specialize (IHctrs H3); clear H3.
    eapply SubList_trans; [apply IHctrs|].
    apply SubList_app_3.
    - apply SubList_app_1, SubList_app_2, SubList_refl.
    - simpl; apply SubList_app_3.
      + apply SubList_app_2, SubList_refl.
      + apply SubList_app_1, SubList_app_1; auto.
  Qed.

  Lemma c_l1_indices_inds_SubList:
    forall tr bidx,
      SubList (c_l1_indices (snd (tree2Topo tr bidx)))
              (indsOf (fst (tree2Topo tr bidx))).
  Proof.
    induction tr using tree_ind_l; simpl; intros.
    find_if_inside; [solve_SubList|].
    simpl; apply SubList_cons_right.
    eapply c_l1_indices_fold_collect_SubList
      with (bidx:= bidx) (oss:= 0) (bcifc:= emptyCIfc) in H.
    simpl in H; rewrite app_nil_r in H.
    assumption.
  Qed.

  Lemma c_li_indices_inds_SubList:
    forall tr bidx,
      SubList (c_li_indices (snd (tree2Topo tr bidx)))
              (indsOf (fst (tree2Topo tr bidx))).
  Proof.
    induction tr using tree_ind_l; simpl; intros.
    find_if_inside; [apply SubList_nil|].
    simpl; apply SubList_cons; [left; reflexivity|].
    apply SubList_cons_right.
    eapply c_li_indices_fold_collect_SubList
      with (bidx:= bidx) (oss:= 0) (bcifc:= emptyCIfc) in H.
    simpl in H; rewrite app_nil_r in H.
    assumption.
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

  Lemma fold_left_base_c_l1_indices_In:
    forall ifc ifcs bifc,
      SubList (c_l1_indices ifc) (c_l1_indices bifc) ->
      SubList (c_l1_indices ifc) (c_l1_indices (fold_left mergeCIfc ifcs bifc)).
  Proof.
    induction ifcs as [|hifc ifcs]; simpl; intros; [assumption|].
    apply IHifcs.
    simpl; apply SubList_app_1; assumption.
  Qed.

  Lemma fold_left_base_c_li_indices_In:
    forall ifc ifcs bifc,
      SubList (c_li_indices ifc) (c_li_indices bifc) ->
      SubList (c_li_indices ifc) (c_li_indices (fold_left mergeCIfc ifcs bifc)).
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

  Lemma mergeCIfc_fold_left_c_l1_indices_In:
    forall ifc ifcs,
      In ifc ifcs ->
      forall bifc,
        SubList (c_l1_indices ifc) (c_l1_indices (fold_left mergeCIfc ifcs bifc)).
  Proof.
    induction ifcs; simpl; intros; [exfalso; auto|].
    destruct H; subst; [|auto].
    apply fold_left_base_c_l1_indices_In.
    simpl; apply SubList_app_2, SubList_refl.
  Qed.

  Lemma mergeCIfc_fold_left_c_li_indices_In:
    forall ifc ifcs,
      In ifc ifcs ->
      forall bifc,
        SubList (c_li_indices ifc) (c_li_indices (fold_left mergeCIfc ifcs bifc)).
  Proof.
    induction ifcs; simpl; intros; [exfalso; auto|].
    destruct H; subst; [|auto].
    apply fold_left_base_c_li_indices_In.
    simpl; apply SubList_app_2, SubList_refl.
  Qed.

  Lemma tree2Topo_l1_oidx_In:
    forall oidx bidx ctrs oss bcifc,
      In oidx (c_l1_indices
                 (fold_left mergeCIfc (map snd (incMap tree2Topo ctrs bidx oss)) bcifc)) ->
      In oidx (c_l1_indices bcifc) \/
      exists ctr ofs,
        nth_error ctrs ofs = Some ctr /\
        In (fst (tree2Topo ctr bidx~>(oss + ofs)))
           (map fst (incMap tree2Topo ctrs bidx oss)) /\
        In (snd (tree2Topo ctr bidx~>(oss + ofs)))
           (map snd (incMap tree2Topo ctrs bidx oss)) /\
        In oidx (c_l1_indices (snd (tree2Topo ctr bidx~>(oss + ofs)))).
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

  Lemma tree2Topo_li_oidx_In:
    forall oidx bidx ctrs oss bcifc,
      In oidx (c_li_indices
                 (fold_left mergeCIfc (map snd (incMap tree2Topo ctrs bidx oss)) bcifc)) ->
      In oidx (c_li_indices bcifc) \/
      exists ctr ofs,
        nth_error ctrs ofs = Some ctr /\
        In (fst (tree2Topo ctr bidx~>(oss + ofs)))
           (map fst (incMap tree2Topo ctrs bidx oss)) /\
        In (snd (tree2Topo ctr bidx~>(oss + ofs)))
           (map snd (incMap tree2Topo ctrs bidx oss)) /\
        In oidx (c_li_indices (snd (tree2Topo ctr bidx~>(oss + ofs)))).
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

  Lemma tree2Topo_children_chns_In:
    forall erq bidx ctrs oss bcifc,
      let cifc := fold_left mergeCIfc (map snd (incMap tree2Topo ctrs bidx oss)) bcifc in
      In erq (c_minds cifc ++ c_merqs cifc ++ c_merss cifc) ->
      In erq (c_minds bcifc ++ c_merqs bcifc ++ c_merss bcifc) \/
      exists ctr ofs,
        nth_error ctrs ofs = Some ctr /\
        In (fst (tree2Topo ctr bidx~>(oss + ofs)))
           (map fst (incMap tree2Topo ctrs bidx oss)) /\
        In (snd (tree2Topo ctr bidx~>(oss + ofs)))
           (map snd (incMap tree2Topo ctrs bidx oss)) /\
        let ccifc := snd (tree2Topo ctr bidx~>(oss + ofs)) in
        In erq (c_minds ccifc ++ c_merqs ccifc ++ c_merss ccifc).
  Proof.
    induction ctrs as [|ctr ctrs]; simpl; intros;
      [left; assumption|].

    specialize (IHctrs _ _ H).
    destruct IHctrs.
    - simpl in H0; apply in_app_or in H0; destruct H0.
      + simpl in H0; apply in_app_or in H0; destruct H0.
        * left; apply in_or_app; auto.
        * right; exists ctr, 0.
          rewrite Nat.add_0_r; auto.
          repeat split; auto.
          apply in_or_app; auto.
      + simpl in H0; apply in_app_or in H0; destruct H0.
        * simpl in H0; apply in_app_or in H0; destruct H0.
          { left; apply in_or_app.
            right; apply in_or_app; auto.
          }
          { right; exists ctr, 0.
            rewrite Nat.add_0_r; auto.
            repeat split; auto.
            apply in_or_app.
            right; apply in_or_app; auto.
          }
        * simpl in H0; apply in_app_or in H0; destruct H0.
          { left; apply in_or_app.
            right; apply in_or_app; auto.
          }
          { right; exists ctr, 0.
            rewrite Nat.add_0_r; auto.
            repeat split; auto.
            apply in_or_app.
            right; apply in_or_app; auto.
          }

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

  Lemma singletonDNode_cifc_inds_prefix_base:
    forall bidx,
      Forall (fun idx => bidx ~< idx)
             ((c_li_indices (snd (singletonDNode bidx)))
                ++ (c_l1_indices (snd (singletonDNode bidx)))).
  Proof.
    intros; simpl.
    repeat constructor.
    apply IdxPrefix_refl.
  Qed.

  Lemma singletonDNode_cifc_chns_prefix_base:
    forall bidx,
      Forall (fun idx => bidx ~< idx /\ List.length bidx < List.length idx)
             ((c_minds (snd (singletonDNode bidx)))
                ++ (c_merqs (snd (singletonDNode bidx)))
                ++ (c_merss (snd (singletonDNode bidx)))).
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
          apply incMap_In_implies in H0.
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
        split; [|lia].
        eapply IdxPrefix_trans; [|eassumption].
        exists [0]; reflexivity.
      + apply collect_forall.
        intros dstr ?.
        apply in_map_iff in H.
        destruct H as [[dtr sifc] [? ?]]; simpl in *; subst.
        apply incMap_In_implies in H0.
        destruct H0 as [str [ofs ?]]; dest.
        apply nth_error_In in H.
        rewrite Forall_forall in H3; specialize (H3 _ H bidx~>(1 + ofs)).
        rewrite <-H0 in H3; simpl in H3.
        eapply Forall_impl; [|eassumption].
        simpl; intros; dest.
        split; [|lia].
        eapply IdxPrefix_trans; [|eassumption].
        eexists [_]; reflexivity.
  Qed.

  Lemma tree2Topo_cifc_inds_prefix_base:
    forall tr bidx,
      Forall (fun idx => bidx ~< idx)
             ((c_li_indices (snd (tree2Topo tr bidx)))
                ++ (c_l1_indices (snd (tree2Topo tr bidx)))).
  Proof.
    induction tr using tree_ind_l.
    intros; simpl.
    find_if_inside.
    - apply singletonDNode_cifc_inds_prefix_base.
    - simpl; constructor.
      + apply IdxPrefix_refl.
      + apply Forall_forall; intros idx ?.
        apply tree2Topo_children_oidx_In in H0.
        destruct H0; [dest_in|].
        destruct H0 as [ctr [ofs ?]]; dest; simpl in *.
        pose proof (nth_error_In _ _ H0).
        rewrite Forall_forall in H; specialize (H _ H4 bidx~>ofs); clear H4.
        destruct (tree2Topo ctr bidx~>ofs) as [cdtr cifc] eqn:Hchd; simpl in *.
        rewrite Forall_forall in H; specialize (H _ H3).
        eapply IdxPrefix_trans; [|eassumption].
        eexists [_]; reflexivity.
  Qed.

  Lemma tree2Topo_cifc_chns_prefix_base:
    forall tr bidx,
      Forall (fun idx => bidx ~< idx /\ List.length bidx < List.length idx)
             ((c_minds (snd (tree2Topo tr bidx)))
                ++ (c_merqs (snd (tree2Topo tr bidx)))
                ++ (c_merss (snd (tree2Topo tr bidx)))).
  Proof.
    induction tr using tree_ind_l.
    intros; simpl.
    find_if_inside.
    - apply singletonDNode_cifc_chns_prefix_base.
    - simpl; repeat constructor.
      1-3: (eexists [_]; reflexivity).
      rewrite Forall_forall; intros idx ?.
      apply tree2Topo_children_chns_In in H0.
      destruct H0; [dest_in|].
      destruct H0 as [ctr [ofs ?]]; dest; simpl in *.
      pose proof (nth_error_In _ _ H0).
      rewrite Forall_forall in H; specialize (H _ H4 bidx~>ofs); clear H4.
      destruct (tree2Topo ctr bidx~>ofs) as [cdtr cifc] eqn:Hchd; simpl in *.
      rewrite Forall_forall in H; specialize (H _ H3); dest.
      split.
      + eapply IdxPrefix_trans; [|eassumption].
        eexists [_]; reflexivity.
      + lia.
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
          apply incMap_In_implies in H2.
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
            apply incMap_In_implies in H1.
            destruct H1 as [str [extb ?]]; dest; simpl in *.
            apply nth_error_In in H0.
            rewrite Forall_forall in H; specialize (H _ H0 bidx~>extb).
            rewrite <-H1 in H.
            apply H.
          }
          { intros.
            apply map_nth_error_inv in H1; destruct H1 as [[dtr1 cifc1] [? ?]].
            apply map_nth_error_inv in H2; destruct H2 as [[dtr2 cifc2] [? ?]].
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
            apply incMap_In_implies in H1.
            destruct H1 as [str [extb ?]]; dest; simpl in *.
            apply nth_error_In in H0.
            rewrite Forall_forall in H; specialize (H _ H0 bidx~>extb).
            rewrite <-H1 in H.
            apply H.
          }
          { intros.
            apply map_nth_error_inv in H1; destruct H1 as [[dtr1 cifc1] [? ?]].
            apply map_nth_error_inv in H2; destruct H2 as [[dtr2 cifc2] [? ?]].
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
          apply (DisjList_spec_1 Nat.eq_dec).
          intros.
          assert (a = S (List.length bidx)) by (dest_in; reflexivity).
          clear H0; subst.
          intro Hx; apply in_map_iff in Hx.
          destruct Hx as [idx ?]; dest.
          apply collect_in_exist in H1; destruct H1 as [sdtr [? ?]].
          apply in_map_iff in H1; destruct H1 as [[dtr sifc] [? ?]].
          simpl in *; subst.
          apply incMap_In_implies in H3; destruct H3 as [str [ofs [? ?]]].
          simpl in *.
          replace sdtr with (fst (tree2Topo str bidx~>ofs)) in H2
            by (rewrite <-H3; reflexivity).
          pose proof (tree2Topo_chns_prefix_base str bidx~>ofs).
          rewrite Forall_forall in H4; specialize (H4 _ H2); dest.
          simpl in H5; lia.
  Qed.

  Lemma singletonDNode_WfCIfc:
    forall bidx, WfCIfc (snd (singletonDNode bidx)).
  Proof.
    intros; split.
    - simpl; solve_NoDup.
    - simpl.
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
  Qed.

  Lemma tree2Topo_cifc_inds_fold_left_NoDup:
    forall bidx ctrs oss bcifc,
      NoDup (c_li_indices bcifc ++ c_l1_indices bcifc) ->
      (forall ctr ofs,
          nth_error ctrs ofs = Some ctr ->
          NoDup ((c_li_indices (snd (tree2Topo ctr bidx~>(oss + ofs))))
                   ++ (c_l1_indices (snd (tree2Topo ctr bidx~>(oss + ofs))))) /\
          DisjList (c_li_indices bcifc ++ c_l1_indices bcifc)
                   ((c_li_indices (snd (tree2Topo ctr bidx~>(oss + ofs))))
                      ++ (c_l1_indices (snd (tree2Topo ctr bidx~>(oss + ofs)))))) ->
      let mcifc := fold_left mergeCIfc (map snd (incMap tree2Topo ctrs bidx oss)) bcifc in
      NoDup (c_li_indices mcifc ++ c_l1_indices mcifc).
  Proof.
    induction ctrs; simpl; intros; auto.
    apply IHctrs.
    - simpl; apply (NoDup_app_comm_4 idx_dec).
      replace oss with (oss + 0) by lia.
      apply NoDup_DisjList; auto; apply H0; auto.
    - intros; split.
      + replace (S oss + ofs) with (oss + S ofs) by lia.
        apply H0; assumption.
      + simpl.
        apply DisjList_SubList
          with (l1 := ((c_li_indices bcifc ++ c_l1_indices bcifc)
                         ++ ((c_li_indices (snd (tree2Topo a bidx~>oss)))
                               ++ c_l1_indices (snd (tree2Topo a bidx~>oss))))).
        * repeat apply SubList_app_3.
          { do 2 apply SubList_app_1; apply SubList_refl. }
          { apply SubList_app_2, SubList_app_1, SubList_refl. }
          { apply SubList_app_1, SubList_app_2, SubList_refl. }
          { do 2 apply SubList_app_2; apply SubList_refl. }
        * apply DisjList_app_4.
          { replace (S (oss + ofs)) with (oss + S ofs) by lia.
            apply H0; assumption.
          }
          { apply IndsDisj_DisjList.
            eapply IdxDisj_base_IndsDisj with (bidx1:= bidx~>oss) (bidx2:= bidx~>(S oss + ofs)).
            { apply extendIdx_IdxDisj; lia. }
            { apply tree2Topo_cifc_inds_prefix_base. }
            { apply tree2Topo_cifc_inds_prefix_base. }
          }
  Qed.

  Lemma tree2Topo_cifc_chns_fold_left_NoDup:
    forall bidx ctrs oss bcifc,
      NoDup (c_minds bcifc ++ c_merqs bcifc ++ c_merss bcifc) ->
      (forall ctr ofs,
          nth_error ctrs ofs = Some ctr ->
          NoDup ((c_minds (snd (tree2Topo ctr bidx~>(oss + ofs))))
                   ++ (c_merqs (snd (tree2Topo ctr bidx~>(oss + ofs))))
                   ++ (c_merss (snd (tree2Topo ctr bidx~>(oss + ofs))))) /\
          DisjList (c_minds bcifc ++ c_merqs bcifc ++ c_merss bcifc)
                   ((c_minds (snd (tree2Topo ctr bidx~>(oss + ofs))))
                      ++ (c_merqs (snd (tree2Topo ctr bidx~>(oss + ofs))))
                      ++ (c_merss (snd (tree2Topo ctr bidx~>(oss + ofs)))))) ->
      let mcifc := fold_left mergeCIfc (map snd (incMap tree2Topo ctrs bidx oss)) bcifc in
      NoDup (c_minds mcifc ++ c_merqs mcifc ++ c_merss mcifc).
  Proof.
    induction ctrs; simpl; intros; auto.
    apply IHctrs.
    - simpl; apply (NoDup_app_comm_6 idx_dec).
      replace oss with (oss + 0) by lia.
      apply NoDup_DisjList; auto; apply H0; auto.
    - intros; split.
      + replace (S oss + ofs) with (oss + S ofs) by lia.
        apply H0; assumption.
      + simpl.
        apply DisjList_SubList
          with (l1 := ((c_minds bcifc ++ c_merqs bcifc ++ c_merss bcifc)
                         ++ ((c_minds (snd (tree2Topo a bidx~>oss)))
                               ++ c_merqs (snd (tree2Topo a bidx~>oss))
                               ++ c_merss (snd (tree2Topo a bidx~>oss))))).
        * repeat apply SubList_app_3.
          { do 2 apply SubList_app_1; apply SubList_refl. }
          { apply SubList_app_2, SubList_app_1, SubList_refl. }
          { apply SubList_app_1, SubList_app_2, SubList_app_1, SubList_refl. }
          { apply SubList_app_2, SubList_app_2, SubList_app_1, SubList_refl. }
          { apply SubList_app_1; do 2 apply SubList_app_2; apply SubList_refl. }
          { do 3 apply SubList_app_2; apply SubList_refl. }
        * apply DisjList_app_4.
          { replace (S (oss + ofs)) with (oss + S ofs) by lia.
            apply H0; assumption.
          }
          { apply IndsDisj_DisjList.
            eapply IdxDisj_base_IndsDisj with (bidx1:= bidx~>oss) (bidx2:= bidx~>(S oss + ofs)).
            { apply extendIdx_IdxDisj; lia. }
            { eapply Forall_impl; [|apply tree2Topo_cifc_chns_prefix_base].
              simpl; intros; dest; assumption.
            }
            { eapply Forall_impl; [|apply tree2Topo_cifc_chns_prefix_base].
              simpl; intros; dest; assumption.
            }
          }
  Qed.

  Lemma tree2Topo_WfCIfc:
    forall tr bidx, WfCIfc (snd (tree2Topo tr bidx)).
  Proof.
    induction tr using tree_ind_l.
    intros; simpl.
    find_if_inside; subst.
    - apply singletonDNode_WfCIfc.
    - simpl; split.
      + simpl.
        constructor.
        * intro Hx.
          apply tree2Topo_children_oidx_In in Hx.
          destruct Hx; [dest_in|].
          destruct H0 as [ctr [ofs ?]]; dest; simpl in *.
          pose proof (tree2Topo_cifc_inds_prefix_base ctr bidx~>ofs).
          rewrite Forall_forall in H4; specialize (H4 _ H3).
          eapply extendIdx_not_IdxPrefix; eassumption.
        * apply tree2Topo_cifc_inds_fold_left_NoDup; [constructor|].
          simpl; intros.
          split; [|apply DisjList_nil_1].
          apply nth_error_In in H0.
          rewrite Forall_forall in H.
          apply H; auto.

      + simpl.
        match goal with
        | |- NoDup (?i1 :: ?i2 :: ?i3 :: ?inds) =>
          change (i1 :: i2 :: i3 :: inds) with ([i1; i2; i3] ++ inds)
        end.
        apply NoDup_DisjList.
        * solve_NoDup.
        * apply tree2Topo_cifc_chns_fold_left_NoDup; [constructor|].
          simpl; intros.
          split; [|apply DisjList_nil_1].
          apply nth_error_In in H0.
          rewrite Forall_forall in H.
          apply H; auto.
        * apply DisjList_map with (f:= @List.length _).
          apply (DisjList_spec_1 Nat.eq_dec).
          intros.
          assert (a = S (List.length bidx)) by (dest_in; reflexivity).
          clear H0; subst.
          intro Hx; apply in_map_iff in Hx.
          destruct Hx as [idx ?]; dest.
          apply tree2Topo_children_chns_In in H1.
          destruct H1; [dest_in|].
          destruct H1 as [ctr [ofs ?]]; dest; simpl in *.
          pose proof (tree2Topo_cifc_chns_prefix_base ctr bidx~>ofs).
          rewrite Forall_forall in H5; specialize (H5 _ H4).
          simpl in H5; dest; lia.
  Qed.

  Corollary tree2Topo_minds_merqs_disj:
    forall tr bidx,
      DisjList (c_minds (snd (tree2Topo tr bidx)))
               (c_merqs (snd (tree2Topo tr bidx))).
  Proof.
    intros.
    pose proof (tree2Topo_WfCIfc tr bidx) as [_ ?].
    apply (DisjList_NoDup idx_dec) in H.
    apply DisjList_app_1 in H; assumption.
  Qed.

  Corollary tree2Topo_minds_merss_disj:
    forall tr bidx,
      DisjList (c_minds (snd (tree2Topo tr bidx)))
               (c_merss (snd (tree2Topo tr bidx))).
  Proof.
    intros.
    pose proof (tree2Topo_WfCIfc tr bidx) as [_ ?].
    apply (DisjList_NoDup idx_dec) in H.
    apply DisjList_app_2 in H; assumption.
  Qed.

  Corollary tree2Topo_merqs_merss_disj:
    forall tr bidx,
      DisjList (c_merqs (snd (tree2Topo tr bidx)))
               (c_merss (snd (tree2Topo tr bidx))).
  Proof.
    intros.
    pose proof (tree2Topo_WfCIfc tr bidx) as [_ ?].
    apply NoDup_app_weakening_2 in H.
    apply (DisjList_NoDup idx_dec) in H.
    assumption.
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
        apply incMap_In_implies in H0; destruct H0 as [str [ofs [? ?]]].
        eapply tree2Topo_RqRsChnsOnDTree_root.
        rewrite <-H0; reflexivity.
      + apply find_some_exist in H0.
        destruct H0 as [sdtr [? ?]].
        apply in_map_iff in H0; destruct H0 as [[dtr sifc] [? ?]].
        simpl in *; subst.
        apply incMap_In_implies in H2; destruct H2 as [str [ofs [? ?]]].
        apply nth_error_In in H0.
        rewrite Forall_forall in H; specialize (H _ H0).
        specialize (H bidx~>ofs); simpl in H2; rewrite <-H2 in H; simpl in H.
        eapply H; eauto.
  Qed.

  Lemma tree2Topo_RqRsChnsOnSystem_unfolded:
    forall tr bidx topo cifc oinds minds,
      tree2Topo tr bidx = (topo, cifc) ->
      oinds = cifc.(c_li_indices) ++ cifc.(c_l1_indices) ->
      minds = cifc.(c_minds) ->
      (* body of [RqRsChnsOnDTree] *)
      forall oidx,
        In oidx oinds ->
        exists odtr otr obidx,
          subtree oidx topo = Some odtr /\
          odtr = fst (tree2Topo otr obidx) /\
          SubList (dmcOf odtr).(dmc_ups) minds /\
          SubList (dmcOf odtr).(dmc_downs) minds.
  Proof.
    induction tr using tree_ind_l.
    intros; subst.
    pose proof (tree2Topo_WfDTree (Node l) bidx) as Hwf.
    simpl in *; find_if_inside; subst.
    - inv H0.
      destruct H3; [subst|exfalso; auto].
      eexists; exists (Node nil), oidx; repeat ssplit.
      + unfold subtree, dmc_me.
        destruct (idx_dec _ _); [|exfalso; auto].
        reflexivity.
      + reflexivity.
      + simpl; solve_SubList.
      + simpl; solve_SubList.

    - inv H0.
      simpl in H3.
      destruct (idx_dec bidx oidx); subst.
      1: {
        eexists; exists (Node l), oidx; repeat ssplit.
        { unfold subtree, dmc_me.
          destruct (idx_dec _ _); [|exfalso; auto].
          reflexivity.
        }
        { simpl; find_if_inside; [exfalso; auto|]; reflexivity. }
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
      destruct H as [odtr [otr [obidx ?]]]; dest.

      exists odtr, otr, obidx; repeat ssplit.
      + eapply subtree_collect_NoDup_find_some; try eassumption.
        destruct Hwf.
        red in H7; simpl in H7; inv H7.
        assumption.
      + assumption.
      + do 3 apply SubList_cons_right.
        eapply SubList_trans; [eassumption|].
        apply mergeCIfc_fold_left_c_minds_In; assumption.
      + do 3 apply SubList_cons_right.
        eapply SubList_trans; [eassumption|].
        apply mergeCIfc_fold_left_c_minds_In; assumption.
  Qed.

  Lemma tree2Topo_RqRsChnsOnSystem:
    forall `{dv: DecValue} `{oifc: OStateIfc} tr bidx topo cifc (impl: System),
      tree2Topo tr bidx = (topo, cifc) ->
      map obj_idx impl.(sys_objs) = cifc.(c_li_indices) ++ cifc.(c_l1_indices) ->
      impl.(sys_minds) = cifc.(c_minds) ->
      RqRsChnsOnSystem topo impl.
  Proof.
    intros.
    red; intros.
    eapply tree2Topo_RqRsChnsOnSystem_unfolded in H2; eauto.
    destruct H2 as [odtr [otr [obidx ?]]]; dest.
    replace topo with (fst (tree2Topo tr bidx)) in * by (rewrite H; reflexivity).
    pose proof (parentChnsOf_subtree (tree2Topo_WfDTree tr bidx) _ H3).
    destruct H7 as [rodtr ?]; dest; subst.
    rewrite H7 in H2; inv H2.
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
    forall `{dv: DecValue} `{oifc: OStateIfc} tr bidx topo cifc (impl: System),
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

  Lemma TreeTopo_children_inds_disj:
    forall topo,
      TreeTopo topo ->
      forall sidx n1 i1 n2 i2,
        n1 <> n2 ->
        nth_error (subtreeChildrenIndsOf topo sidx) n1 = Some i1 ->
        nth_error (subtreeChildrenIndsOf topo sidx) n2 = Some i2 ->
        i1 ~*~ i2.
  Proof.
    unfold subtreeChildrenIndsOf; intros.
    destruct (subtree sidx topo) as [str|] eqn:Hstr;
      [|simpl in *; destruct n1; discriminate].
    simpl in *.
    destruct H as [_ ?]; eapply H with (sidx:= sidx); eauto.
  Qed.

  Lemma c_li_l1_indices_inds_SubList:
    forall tr bidx,
      SubList ((c_li_indices (snd (tree2Topo tr bidx)))
                 ++ c_l1_indices (snd (tree2Topo tr bidx)))
              (indsOf (fst (tree2Topo tr bidx))).
  Proof.
    intros.
    apply SubList_app_3.
    - apply c_li_indices_inds_SubList.
    - apply c_l1_indices_inds_SubList.
  Qed.

  Lemma c_li_indices_head_rootOf:
    forall tr bidx,
      tr <> Node nil ->
      c_li_indices (snd (tree2Topo tr bidx)) =
      rootOf (fst (tree2Topo tr bidx)) :: tl (c_li_indices (snd (tree2Topo tr bidx))).
  Proof.
    destruct tr; simpl; intros.
    find_if_inside; [subst; exfalso; auto|].
    reflexivity.
  Qed.

  Lemma c_li_l1_indices_has_parent:
    forall tr (Htr: tr <> Node nil) bidx oidx,
      In oidx ((tl (c_li_indices (snd (tree2Topo tr bidx))))
                 ++ c_l1_indices (snd (tree2Topo tr bidx))) ->
      exists pidx,
        parentIdxOf (fst (tree2Topo tr bidx)) oidx = Some pidx.
  Proof.
    intros.
    assert (In oidx ((c_li_indices (snd (tree2Topo tr bidx)))
                       ++ c_l1_indices (snd (tree2Topo tr bidx)))).
    { apply in_app_or in H; destruct H.
      { apply in_or_app; left; apply tl_In; assumption. }
      { apply in_or_app; right; assumption. }
    }
    assert (oidx <> rootOf (fst (tree2Topo tr bidx))).
    { pose proof (tree2Topo_WfCIfc tr bidx).
      destruct H1 as [? _].
      rewrite c_li_indices_head_rootOf in H0, H1 by assumption.
      inv H1; inv H0.
      { exfalso; auto. }
      { intro Hx; subst; auto. }
    }
    apply c_li_l1_indices_inds_SubList in H0.
    pose proof (indsOf_parentChnsOf_not_None _ H0 H1).
    destruct (parentChnsOf _ _) as [[dmc pidx]|] eqn:Hpc; [|exfalso; auto].
    exists pidx.
    unfold parentIdxOf; rewrite Hpc; reflexivity.
  Qed.

  Lemma tree2Topo_li_l1_parent_li:
    forall tr bidx oidx pidx,
      In oidx ((c_li_indices (snd (tree2Topo tr bidx)))
                 ++ c_l1_indices (snd (tree2Topo tr bidx))) ->
      parentIdxOf (fst (tree2Topo tr bidx)) oidx = Some pidx ->
      In pidx (c_li_indices (snd (tree2Topo tr bidx))).
  Proof.
    induction tr using tree_ind_l; simpl; intros.
    pose proof (tree2Topo_WfDTree (Node l) bidx) as Hwf; simpl in Hwf.
    find_if_inside; simpl in *.
    1: {
      destruct H0; subst; auto.
      unfold parentIdxOf in H1; simpl in H1.
      unfold hasIdx in H1.
      find_if_inside; [eapply l1ExtOf_not_eq; eauto|].
      discriminate.
    }

    destruct H0; subst;
      [exfalso; apply parentIdxOf_child_not_root in H1; [|assumption]; auto|].
    apply tree2Topo_children_oidx_In in H0.
    destruct H0; [dest_in|].
    destruct H0 as [ctr [ofs ?]]; simpl in *; dest.

    destruct (idx_dec oidx (rootOf (fst (tree2Topo ctr bidx~>ofs)))); [subst|].
    - rewrite parentIdxOf_childrenOf in H1 by assumption.
      inv H1; left; reflexivity.
    - erewrite parentIdxOf_Subtree_eq in H1; try eassumption;
        [|apply childrenOf_Subtree; assumption
         |apply c_li_l1_indices_inds_SubList; assumption].
      apply nth_error_In in H0.
      rewrite Forall_forall in H; specialize (H _ H0).
      specialize (H _ _ _ H4 H1).
      right.
      eapply mergeCIfc_fold_left_c_li_indices_In; eassumption.
  Qed.

  Lemma tree2Topo_child_in:
    forall tr bidx oidx cidx,
      parentIdxOf (fst (tree2Topo tr bidx)) cidx = Some oidx ->
      (In oidx (c_l1_indices (snd (tree2Topo tr bidx))) /\ cidx = l1ExtOf oidx) \/
      (In oidx (c_li_indices (snd (tree2Topo tr bidx))) /\
       In cidx ((c_li_indices (snd (tree2Topo tr bidx)))
                  ++ c_l1_indices (snd (tree2Topo tr bidx)))).
  Proof.
    induction tr using tree_ind_l; simpl; intros.
    pose proof (tree2Topo_WfDTree (Node l) bidx) as Hwf; simpl in Hwf.
    find_if_inside; simpl in *.

    - left.
      unfold parentIdxOf in H0; simpl in H0.
      destruct (hasIdx _ _) eqn:Hhi; [|discriminate].
      destruct d; inv H0.
      apply hasIdx_Some in Hhi; simpl in Hhi; dest; subst.
      auto.

    - unfold parentIdxOf in H0.
      destruct (parentChnsOf _ _) as [[croot pidx]|] eqn:Hp;
        simpl in H0; [inv H0|discriminate].
      apply parentChnsOf_case in Hp.
      destruct Hp as [cdtr ?]; dest.
      destruct H1.

      + dest; subst; simpl in *.
        apply in_map_iff in H0; destruct H0 as [[cdtr' cifc] [? ?]]; simpl in *; subst.
        apply incMap_In_implies in H1.
        destruct H1 as [ctr [ofs [? ?]]]; simpl in *.

        right; split; [left; reflexivity|].
        right; apply in_or_app.
        destruct ctr as [cl].
        destruct (nil_dec cl); subst.
        * simpl in H1; unfold singletonDNode in H1; inv H1; simpl in *.
          right.
          eapply mergeCIfc_fold_left_c_l1_indices_In.
          { apply in_map; apply incMap_In; eassumption. }
          { left; reflexivity. }
        * left.
          eapply mergeCIfc_fold_left_c_li_indices_In with (ifc:= cifc).
          { replace cifc with (snd (tree2Topo (Node cl) bidx~>ofs))
              by (rewrite <-H1; reflexivity).
            apply in_map.
            change ofs with (0 + ofs).
            apply incMap_In; assumption.
          }
          { replace cifc with (snd (tree2Topo (Node cl) bidx~>ofs))
              by (rewrite <-H1; reflexivity).
            rewrite c_li_indices_head_rootOf by (intro Hx; inv Hx; auto).
            left; rewrite <-H1; reflexivity.
          }

      + simpl in H0.
        apply in_map_iff in H0; destruct H0 as [[cdtr' cifc] [? ?]]; simpl in *; subst.
        apply incMap_In_implies in H2.
        destruct H2 as [ctr [ofs [? ?]]]; simpl in *.
        pose proof (nth_error_In _ _ H0).
        rewrite Forall_forall in H; specialize (H _ H3).
        assert (parentIdxOf (fst (tree2Topo ctr bidx~>ofs)) cidx = Some oidx).
        { rewrite <-H2; simpl.
          unfold parentIdxOf; rewrite H1; reflexivity.
        }

        specialize (H _ _ _ H4).
        destruct H; dest; [left|right].
        * split; [|assumption].
          eapply mergeCIfc_fold_left_c_l1_indices_In; [|eassumption].
          apply in_map.
          change ofs with (0 + ofs).
          apply incMap_In; assumption.
        * split.
          { right.
            eapply mergeCIfc_fold_left_c_li_indices_In; [|eassumption].
            apply in_map.
            change ofs with (0 + ofs).
            apply incMap_In; assumption.
          }
          { right.
            apply in_or_app; apply in_app_or in H5; destruct H5; [left|right].
            { eapply mergeCIfc_fold_left_c_li_indices_In; [|eassumption].
              apply in_map.
              change ofs with (0 + ofs).
              apply incMap_In; assumption.
            }
            { eapply mergeCIfc_fold_left_c_l1_indices_In; [|eassumption].
              apply in_map.
              change ofs with (0 + ofs).
              apply incMap_In; assumption.
            }
          }
  Qed.

  Lemma tree2Topo_li_child_li_l1:
    forall tr bidx oidx cidx,
      In oidx (c_li_indices (snd (tree2Topo tr bidx))) ->
      parentIdxOf (fst (tree2Topo tr bidx)) cidx = Some oidx ->
      In cidx ((c_li_indices (snd (tree2Topo tr bidx)))
                 ++ c_l1_indices (snd (tree2Topo tr bidx))).
  Proof.
    intros.
    apply tree2Topo_child_in in H0.
    destruct H0; dest; auto.
    exfalso.
    pose proof (tree2Topo_WfCIfc tr bidx).
    destruct H2 as [? _].
    apply (DisjList_NoDup idx_dec) in H2.
    eapply DisjList_In_1; eauto.
  Qed.

  Corollary c_l1_indices_has_parent:
    forall tr (Htr: tr <> Node nil) bidx oidx,
      In oidx (c_l1_indices (snd (tree2Topo tr bidx))) ->
      exists pidx,
        In pidx (c_li_indices (snd (tree2Topo tr bidx))) /\
        parentIdxOf (fst (tree2Topo tr bidx)) oidx = Some pidx.
  Proof.
    intros.
    assert (In oidx ((tl (c_li_indices (snd (tree2Topo tr bidx))))
                       ++ c_l1_indices (snd (tree2Topo tr bidx))))
      by (apply in_or_app; auto).
    apply c_li_l1_indices_has_parent in H0; [|assumption].
    destruct H0 as [pidx ?].
    exists pidx; split; [|assumption].
    eapply tree2Topo_li_l1_parent_li; [|eassumption].
    apply in_or_app; right; assumption.
  Qed.

  Corollary c_li_indices_tail_has_parent:
    forall tr (Htr: tr <> Node nil) bidx oidx,
      In oidx (tl (c_li_indices (snd (tree2Topo tr bidx)))) ->
      exists pidx,
        In pidx (c_li_indices (snd (tree2Topo tr bidx))) /\
        parentIdxOf (fst (tree2Topo tr bidx)) oidx = Some pidx.
  Proof.
    intros.
    assert (In oidx ((tl (c_li_indices (snd (tree2Topo tr bidx))))
                       ++ c_l1_indices (snd (tree2Topo tr bidx))))
      by (apply in_or_app; auto).
    apply c_li_l1_indices_has_parent in H0; [|assumption].
    destruct H0 as [pidx ?].
    exists pidx; split; [|assumption].
    eapply tree2Topo_li_l1_parent_li; [|eassumption].
    apply in_or_app; left.
    apply tl_In; assumption.
  Qed.

  Lemma tree2Topo_obj_chns_minds_SubList:
    forall tr bidx oidx,
      In oidx ((c_li_indices (snd (tree2Topo tr bidx)))
                 ++ (c_l1_indices (snd (tree2Topo tr bidx)))) ->
      SubList [rqUpFrom oidx; rsUpFrom oidx; downTo oidx]
              (c_minds (snd (tree2Topo tr bidx))).
  Proof.
    intros.
    destruct (tree2Topo tr bidx) as [topo cifc] eqn:Htc.
    simpl in *.
    eapply tree2Topo_RqRsChnsOnSystem_unfolded in H;
      try reflexivity; try eassumption.
    destruct H as [odtr [otr [obidx ?]]]; dest.
    destruct (tree2Topo otr obidx) as [rodtr ocifc] eqn:Hotc; simpl in *; subst.
    apply tree2Topo_root_edges in Hotc; dest.
    apply subtree_rootOf in H; subst.
    red; intros; dest_in.
    - apply H1; apply hd_error_In in H0; assumption.
    - apply H1; apply hd_error_In, tl_In in H3; assumption.
    - apply H2; apply hd_error_In in H4; assumption.
  Qed.

  Lemma tree2Topo_internal_chns_not_exts:
    forall tr bidx oidx,
      let cifc := snd (tree2Topo tr bidx) in
      In oidx (c_li_indices cifc ++ c_l1_indices cifc) ->
      DisjList [rqUpFrom oidx; rsUpFrom oidx; downTo oidx]
               ((map (fun cidx => rqUpFrom (l1ExtOf cidx)) (c_l1_indices cifc))
                  ++ map (fun cidx => downTo (l1ExtOf cidx)) (c_l1_indices cifc)).
  Proof.
    intros.
    eapply DisjList_SubList.
    - apply tree2Topo_obj_chns_minds_SubList; eassumption.
    - subst cifc; rewrite <-c_merqs_l1_rqUpFrom, <-c_merss_l1_downTo.
      apply DisjList_comm, DisjList_app_4.
      + apply DisjList_comm, tree2Topo_minds_merqs_disj.
      + apply DisjList_comm, tree2Topo_minds_merss_disj.
  Qed.

  Lemma tree2Topo_internal_rqUp_exts_disj:
    forall tr bidx cinds,
      let cifc := snd (tree2Topo tr bidx) in
      SubList cinds (c_li_indices cifc ++ c_l1_indices cifc) ->
      DisjList (map rqUpFrom cinds)
               ((map (fun cidx => rqUpFrom (l1ExtOf cidx)) (c_l1_indices cifc))
                  ++ map (fun cidx => downTo (l1ExtOf cidx)) (c_l1_indices cifc)).
  Proof.
    intros.
    eapply DisjList_SubList with (l1:= c_minds cifc).
    - red; intros.
      apply in_map_iff in H0; dest; subst.
      apply tree2Topo_obj_chns_minds_SubList with (oidx:= x); [auto|].
      simpl; tauto.
    - subst cifc; rewrite <-c_merqs_l1_rqUpFrom, <-c_merss_l1_downTo.
      apply DisjList_comm, DisjList_app_4.
      + apply DisjList_comm, tree2Topo_minds_merqs_disj.
      + apply DisjList_comm, tree2Topo_minds_merss_disj.
  Qed.

  Lemma tree2Topo_internal_rsUp_exts_disj:
    forall tr bidx cinds,
      let cifc := snd (tree2Topo tr bidx) in
      SubList cinds (c_li_indices cifc ++ c_l1_indices cifc) ->
      DisjList (map rsUpFrom cinds)
               ((map (fun cidx => rqUpFrom (l1ExtOf cidx)) (c_l1_indices cifc))
                  ++ map (fun cidx => downTo (l1ExtOf cidx)) (c_l1_indices cifc)).
  Proof.
    intros.
    eapply DisjList_SubList with (l1:= c_minds cifc).
    - red; intros.
      apply in_map_iff in H0; dest; subst.
      apply tree2Topo_obj_chns_minds_SubList with (oidx:= x); [auto|].
      simpl; tauto.
    - subst cifc; rewrite <-c_merqs_l1_rqUpFrom, <-c_merss_l1_downTo.
      apply DisjList_comm, DisjList_app_4.
      + apply DisjList_comm, tree2Topo_minds_merqs_disj.
      + apply DisjList_comm, tree2Topo_minds_merss_disj.
  Qed.

  Lemma tree2Topo_internal_down_exts_disj:
    forall tr bidx cinds,
      let cifc := snd (tree2Topo tr bidx) in
      SubList cinds (c_li_indices cifc ++ c_l1_indices cifc) ->
      DisjList (map downTo cinds)
               ((map (fun cidx => rqUpFrom (l1ExtOf cidx)) (c_l1_indices cifc))
                  ++ map (fun cidx => downTo (l1ExtOf cidx)) (c_l1_indices cifc)).
  Proof.
    intros.
    eapply DisjList_SubList with (l1:= c_minds cifc).
    - red; intros.
      apply in_map_iff in H0; dest; subst.
      apply tree2Topo_obj_chns_minds_SubList with (oidx:= x); [auto|].
      simpl; tauto.
    - subst cifc; rewrite <-c_merqs_l1_rqUpFrom, <-c_merss_l1_downTo.
      apply DisjList_comm, DisjList_app_4.
      + apply DisjList_comm, tree2Topo_minds_merqs_disj.
      + apply DisjList_comm, tree2Topo_minds_merss_disj.
  Qed.

  Lemma tree2Topo_li_children_li_l1:
    forall tr bidx oidx,
      In oidx (c_li_indices (snd (tree2Topo tr bidx))) ->
      SubList (subtreeChildrenIndsOf (fst (tree2Topo tr bidx)) oidx)
              (c_li_indices (snd (tree2Topo tr bidx)) ++ c_l1_indices (snd (tree2Topo tr bidx))).
  Proof.
    intros; red; intros.
    apply subtreeChildrenIndsOf_parentIdxOf in H0; [|apply tree2Topo_WfDTree].
    eapply tree2Topo_li_child_li_l1; eauto.
  Qed.

  Lemma tree2Topo_li_RqRsDownMatch_children:
    forall `{dv: DecValue} tr bidx oidx,
      In oidx (c_li_indices (snd (tree2Topo tr bidx))) ->
      forall (rss: list (Id Msg)) rqTos rssFrom P,
        idsOf rss = map fst rssFrom ->
        RqRsDownMatch (fst (tree2Topo tr bidx)) oidx rqTos rssFrom P ->
        exists cinds,
          idsOf rss = map rsUpFrom cinds /\
          SubList cinds ((c_li_indices (snd (tree2Topo tr bidx)))
                           ++ c_l1_indices (snd (tree2Topo tr bidx))).
  Proof.
    intros.
    pose proof (tree2Topo_TreeTopo tr bidx).
    destruct H2 as [[? _] _].
    pose proof (RqRsDownMatch_rs_rq H1); clear H1.
    rewrite <-H0 in H3; clear H0 rssFrom.
    rewrite <-Forall_forall in H3.
    induction rss; [exists nil; split; [reflexivity|apply SubList_nil]|].
    inv H3; destruct H4 as [cidx [down ?]].
    specialize (IHrss H5); destruct IHrss as [cinds ?]; dest.
    pose proof (tree2Topo_li_child_li_l1 _ _ _ H H3).
    specialize (H2 _ _ H3); dest.
    disc_rule_conds_ex.
    exists (cidx :: cinds).
    split.
    - simpl; congruence.
    - apply SubList_cons; assumption.
  Qed.

  Lemma tree2Topo_l1_child_ext:
    forall tr bidx oidx cidx,
      In oidx (c_l1_indices (snd (tree2Topo tr bidx))) ->
      parentIdxOf (fst (tree2Topo tr bidx)) cidx = Some oidx ->
      cidx = l1ExtOf oidx.
  Proof.
    intros.
    apply tree2Topo_child_in in H0.
    destruct H0; dest; auto.
    exfalso.
    pose proof (tree2Topo_WfCIfc tr bidx).
    destruct H2 as [? _].
    apply (DisjList_NoDup idx_dec) in H2.
    eapply DisjList_In_1; eauto.
  Qed.

  Lemma tree2Topo_l1_child_ext_not_in:
    forall tr bidx oidx,
      In oidx (c_l1_indices (snd (tree2Topo tr bidx))) ->
      ~ In (l1ExtOf oidx) ((c_li_indices (snd (tree2Topo tr bidx)))
                             ++ c_l1_indices (snd (tree2Topo tr bidx))).
  Proof.
    intros.
    assert (In (rqUpFrom (l1ExtOf oidx)) (c_merqs (snd (tree2Topo tr bidx)))).
    { rewrite c_merqs_l1_rqUpFrom.
      apply in_map_iff.
      eexists; repeat split.
      assumption.
    }
    intro Hx.
    assert (In (rqUpFrom (l1ExtOf oidx)) (c_minds (snd (tree2Topo tr bidx)))).
    { eapply tree2Topo_obj_chns_minds_SubList; [eassumption|].
      left; reflexivity.
    }
    eapply DisjList_In_1; [apply tree2Topo_minds_merqs_disj| |]; eauto.
  Qed.

  Lemma tree2Topo_l1_NoPrefix:
    forall tr bidx,
      NoPrefix (c_l1_indices (snd (tree2Topo tr bidx))).
  Proof.
    induction tr using tree_ind_l; simpl; intros.
    find_if_inside; simpl in *; [apply NoPrefix_singleton|].

    clear n.
    assert (NoPrefix (c_l1_indices emptyCIfc)) by apply NoPrefix_nil.
    assert (forall str n,
               nth_error l n = Some str ->
               IndsDisj (c_l1_indices emptyCIfc)
                        (c_l1_indices (snd (tree2Topo str bidx~>(0 + n)))))
      by (simpl; intros; red; intros; dest_in).
    generalize dependent bidx.
    generalize 0 as ofs.
    generalize dependent H0.
    generalize emptyCIfc as bcifc.
    induction l; intros; [assumption|].

    inv H.
    specialize (IHl H5); clear H5.
    simpl; apply IHl.
    - simpl; apply NoPrefix_IndsDisj; auto.
      replace ofs with (ofs + 0) by lia.
      apply H1; reflexivity.
    - simpl; intros; apply IndsDisj_app_1.
      + replace (S (ofs + n)) with (ofs + S n) by lia.
        apply H1; assumption.
      + eapply IndsDisj_SubList_1; [|apply c_l1_indices_inds_SubList].
        eapply IndsDisj_SubList_2; [|apply c_l1_indices_inds_SubList].
        eapply IdxDisj_base_IndsDisj;
          [|apply tree2Topo_inds_prefix_base
           |apply tree2Topo_inds_prefix_base].
        apply extendIdx_IdxDisj; lia.
  Qed.

  Lemma tree2Topo_root_not_in_tl_li:
    forall tr (Htr: tr <> Node nil) bidx,
      ~ In (rootOf (fst (tree2Topo tr bidx)))
        (tl (c_li_indices (snd (tree2Topo tr bidx)))).
  Proof.
    intros.
    pose proof (tree2Topo_WfCIfc tr bidx).
    destruct H as [? _].
    rewrite c_li_indices_head_rootOf in H by assumption.
    inv H.
    intro Hx; elim H2.
    apply in_or_app; left; assumption.
  Qed.

  Lemma tree2Topo_root_not_in_l1:
    forall tr (Htr: tr <> Node nil) bidx,
      ~ In (rootOf (fst (tree2Topo tr bidx)))
        (c_l1_indices (snd (tree2Topo tr bidx))).
  Proof.
    intros.
    pose proof (tree2Topo_WfCIfc tr bidx).
    destruct H as [? _].
    rewrite c_li_indices_head_rootOf in H by assumption.
    inv H.
    intro Hx; elim H2.
    apply in_or_app; right; assumption.
  Qed.

  Lemma tree2Topo_root_not_l1ExtOf:
    forall tr bidx oidx,
      In oidx (c_l1_indices (snd (tree2Topo tr bidx))) ->
      l1ExtOf oidx <> rootOf (fst (tree2Topo tr bidx)).
  Proof.
    intros.
    destruct tr as [l]; destruct (nil_dec l); subst.
    - simpl in *.
      destruct H; subst.
      + apply l1ExtOf_not_eq.
      + exfalso; auto.

    - assert (In (rqUpFrom (l1ExtOf oidx)) (c_merqs (snd (tree2Topo (Node l) bidx)))).
      { rewrite c_merqs_l1_rqUpFrom.
        apply in_map_iff.
        eexists; repeat split.
        assumption.
      }
      assert (In (rqUpFrom (rootOf (fst (tree2Topo (Node l) bidx))))
                 (c_minds (snd (tree2Topo (Node l) bidx)))).
      { eapply tree2Topo_obj_chns_minds_SubList.
        { rewrite c_li_indices_head_rootOf by (intro Hx; inv Hx; auto).
          left; reflexivity.
        }
        { simpl; tauto. }
      }
      intro Hx; rewrite Hx in H0.
      eapply DisjList_In_1; [apply tree2Topo_minds_merqs_disj| |]; eauto.
  Qed.

  Lemma tree2Topo_l1_ext_parent:
    forall tr bidx oidx,
      In oidx (c_l1_indices (snd (tree2Topo tr bidx))) ->
      parentIdxOf (fst (tree2Topo tr bidx)) (l1ExtOf oidx) = Some oidx.
  Proof.
    induction tr using tree_ind_l; intros.
    pose proof (tree2Topo_WfDTree (Node l) bidx) as Hwf.
    simpl in *.
    find_if_inside; simpl in *.

    - destruct H0; [subst|exfalso; auto].
      unfold parentIdxOf; simpl.
      destruct (hasIdx _ _) eqn:Hhi; simpl.
      + apply hasIdx_Some in Hhi; simpl in Hhi; dest; subst.
        reflexivity.
      + unfold hasIdx in Hhi; simpl in Hhi.
        find_if_inside; [discriminate|exfalso; auto].

    - apply tree2Topo_l1_oidx_In in H0.
      destruct H0; [dest_in|].
      simpl in H0; destruct H0 as [ctr [ofs ?]]; dest.
      rewrite Forall_forall in H; specialize (H _ (nth_error_In _ _ H0) _ _ H3).
      rewrite <-H.
      eapply parentIdxOf_Subtree_eq; [assumption|..].
      + apply childrenOf_Subtree; simpl.
        apply in_map.
        change ofs with (0 + ofs).
        apply incMap_In; assumption.
      + apply tree2Topo_root_not_l1ExtOf; assumption.
      + eapply parentIdxOf_child_indsOf; eassumption.
  Qed.

  Lemma tree2Topo_l1_subtreeIndsOf:
    forall tr bidx oidx,
      In oidx (c_l1_indices (snd (tree2Topo tr bidx))) ->
      subtreeIndsOf (fst (tree2Topo tr bidx)) oidx = [oidx; l1ExtOf oidx].
  Proof.
    induction tr using tree_ind_l; intros.
    pose proof (tree2Topo_WfDTree (Node l) bidx) as Hwf.
    simpl in *.
    find_if_inside; simpl in *.

    - destruct H0; [subst|exfalso; auto].
      cbv [subtreeIndsOf subtree dmc_me].
      find_if_inside; [clear e|exfalso; auto].
      reflexivity.

    - apply tree2Topo_l1_oidx_In in H0.
      destruct H0; [dest_in|].
      simpl in H0; destruct H0 as [ctr [ofs ?]]; dest.
      rewrite Forall_forall in H; specialize (H _ (nth_error_In _ _ H0) _ _ H3).

      assert (subtree oidx (DNode {| dmc_me := bidx;
                                     dmc_ups := [bidx~>rqUpIdx; bidx~>rsUpIdx];
                                     dmc_downs := [bidx~>downIdx] |}
                                  (map fst (incMap tree2Topo l bidx 0))) =
              subtree oidx (fst (tree2Topo ctr bidx~>ofs))).
      { apply eq_sym, subtree_child_subtree_eq; [assumption|..].
        { simpl; apply in_map.
          change ofs with (0 + ofs).
          eapply incMap_In; assumption.
        }
        { apply c_l1_indices_inds_SubList; assumption. }
      }

      unfold subtreeIndsOf in *.
      rewrite H4.
      assumption.
  Qed.

  Lemma tree2Topo_obj_rqUpFrom_not_in_merss:
    forall tr bidx oidx,
      In oidx ((c_li_indices (snd (tree2Topo tr bidx)))
                 ++ c_l1_indices (snd (tree2Topo tr bidx))) ->
      ~ In (rqUpFrom oidx) (c_merss (snd (tree2Topo tr bidx))).
  Proof.
    intros.
    pose proof (tree2Topo_obj_chns_minds_SubList tr bidx H).
    pose proof (tree2Topo_minds_merss_disj tr bidx).
    intro Hx.
    eapply DisjList_In_1; [eapply H1|..]; eauto.
    apply H0; simpl; tauto.
  Qed.

  Lemma tree2Topo_obj_rsUpFrom_not_in_merss:
    forall tr bidx oidx,
      In oidx ((c_li_indices (snd (tree2Topo tr bidx)))
                 ++ c_l1_indices (snd (tree2Topo tr bidx))) ->
      ~ In (rsUpFrom oidx) (c_merss (snd (tree2Topo tr bidx))).
  Proof.
    intros.
    pose proof (tree2Topo_obj_chns_minds_SubList tr bidx H).
    pose proof (tree2Topo_minds_merss_disj tr bidx).
    intro Hx.
    eapply DisjList_In_1; [eapply H1|..]; eauto.
    apply H0; simpl; tauto.
  Qed.

  Lemma tree2Topo_obj_downTo_not_in_merss:
    forall tr bidx oidx,
      In oidx ((c_li_indices (snd (tree2Topo tr bidx)))
                 ++ c_l1_indices (snd (tree2Topo tr bidx))) ->
      ~ In (downTo oidx) (c_merss (snd (tree2Topo tr bidx))).
  Proof.
    intros.
    pose proof (tree2Topo_obj_chns_minds_SubList tr bidx H).
    pose proof (tree2Topo_minds_merss_disj tr bidx).
    intro Hx.
    eapply DisjList_In_1; [eapply H1|..]; eauto.
    apply H0; simpl; tauto.
  Qed.

  Lemma rqEdgeUpFrom_rqUpFrom:
    forall tr bidx oidx midx,
      rqEdgeUpFrom (fst (tree2Topo tr bidx)) oidx = Some midx ->
      midx = rqUpFrom oidx.
  Proof.
    intros.
    pose proof H.
    eapply rqEdgeUpFrom_Some in H; [|apply tree2Topo_RqRsChnsOnDTree].
    dest.
    pose proof (tree2Topo_TreeTopoNode tr bidx).
    specialize (H3 _ _ H2); dest.
    repeat disc_rule_minds; auto.
  Qed.

  Lemma rsEdgeUpFrom_rsUpFrom:
    forall tr bidx oidx midx,
      rsEdgeUpFrom (fst (tree2Topo tr bidx)) oidx = Some midx ->
      midx = rsUpFrom oidx.
  Proof.
    intros.
    pose proof H.
    eapply rsEdgeUpFrom_Some in H; [|apply tree2Topo_RqRsChnsOnDTree].
    dest.
    pose proof (tree2Topo_TreeTopoNode tr bidx).
    specialize (H3 _ _ H2); dest.
    repeat disc_rule_minds; auto.
  Qed.

  Lemma edgeDownTo_downTo:
    forall tr bidx oidx midx,
      edgeDownTo (fst (tree2Topo tr bidx)) oidx = Some midx ->
      midx = downTo oidx.
  Proof.
    intros.
    pose proof H.
    eapply edgeDownTo_Some in H; [|apply tree2Topo_RqRsChnsOnDTree].
    dest.
    pose proof (tree2Topo_TreeTopoNode tr bidx).
    specialize (H3 _ _ H2); dest.
    repeat disc_rule_minds; auto.
  Qed.

End Facts.

Ltac solve_in_l1_li :=
  repeat
    match goal with
    | [H: In ?oidx ?l |- In ?oidx ?l] => assumption
    | [H: In ?oidx ?l |- In ?oidx (?l ++ _) ] => apply in_or_app; auto
    | [H: In ?oidx ?l |- In ?oidx (_ ++ ?l) ] => apply in_or_app; auto
    | [H: In ?oidx (tl ?l) |- In ?oidx ?l ] => apply tl_In; assumption
    | [H: In ?oidx (tl ?l) |- In ?oidx (?l ++ _) ] =>
      apply tl_In in H; apply in_or_app; auto
    end.

Ltac solve_not_in_ext_chns :=
  match goal with
  | |- ~ In (_ ?idx) _ =>
    eapply DisjList_In_2;
    [eapply tree2Topo_internal_chns_not_exts with (oidx:= idx);
     solve_in_l1_li; fail
    |simpl; tauto]
  end.

Ltac solve_ext_chns_disj :=
  repeat
    match goal with
    | |- context [idsOf (map _ _)] =>
      unfold idsOf; rewrite map_trans; simpl
    | |- context[fun x => ?f x] => change (fun x => f x) with f
    | |- DisjList (map rqUpFrom _) (map _ (c_l1_indices _) ++ map _ (c_l1_indices _)) =>
      apply tree2Topo_internal_rqUp_exts_disj
    | |- DisjList (map rsUpFrom _) (map _ (c_l1_indices _) ++ map _ (c_l1_indices _)) =>
      apply tree2Topo_internal_rsUp_exts_disj
    | |- DisjList (map downTo _) (map _ (c_l1_indices _) ++ map _ (c_l1_indices _)) =>
      apply tree2Topo_internal_down_exts_disj
    | |- SubList (remove _ _ _) _ => eapply SubList_trans; [apply remove_SubList|]
    | [H: SubList ?inds _ |- SubList ?inds _] =>
      first [assumption|eapply SubList_trans; [eassumption|]]
    | |- SubList (subtreeChildrenIndsOf _ _) (c_li_indices _ ++ c_l1_indices _) =>
      apply tree2Topo_li_children_li_l1; solve_in_l1_li; fail
    end.

Ltac solve_chn_contra :=
  repeat
    match goal with
    | [H: rqUpFrom _ = rqUpFrom _ |- _] => inv H
    | [H: rsUpFrom _ = rsUpFrom _ |- _] => inv H
    | [H: downTo _ = downTo _ |- _] => inv H
    | [H: ?oidx = l1ExtOf ?oidx |- _] =>
      exfalso; eapply l1ExtOf_not_eq; eauto
    | [H:parentIdxOf _ ?oidx = Some ?oidx |- _] =>
      exfalso; eapply parentIdxOf_not_eq with (idx:= oidx) (pidx:= oidx); eauto
    end; auto.

Ltac solve_chn_neq :=
  intro; solve_chn_contra.

Ltac solve_chn_not_in :=
  intro; dest_in; try discriminate; simpl in *;
  solve_chn_contra.

Ltac disc_responses_from :=
  repeat
    match goal with
    | [H: ValidMsgsIn _ _ |- _] => destruct H
    | [Hrr: RqRsDownMatch _ _ _ ?rss _, Hrrs: _ = map fst ?rss |- _] =>
      let cidx := fresh "cidx" in
      let down := fresh "down" in
      eapply RqRsDownMatch_rs_rq in Hrr; [|rewrite <-Hrrs; left; reflexivity];
      destruct Hrr as [cidx [down ?]]; dest
    | [Hrr: RqRsDownMatch _ ?oidx _ ?rss _,
            Hrrs: idsOf _ = map fst ?rss,
                  Hin: In ?oidx (tl (c_li_indices _)) |- _] =>
      let Hc := fresh "H" in
      pose proof (tree2Topo_li_RqRsDownMatch_children _ _ (tl_In _ _ Hin) _ Hrrs Hrr) as Hc;
      let Hic := fresh "H" in
      destruct Hc as [cinds [Hic ?]]; try (rewrite <-Hrrs, Hic)
    | [Hrr: RqRsDownMatch _ ?oidx _ ?rss _,
            Hrrs: idsOf _ = map fst ?rss,
                  Hin: In ?oidx (c_li_indices _) |- _] =>
      let Hc := fresh "H" in
      pose proof (tree2Topo_li_RqRsDownMatch_children _ _ Hin _ Hrrs Hrr) as Hc;
      let Hic := fresh "H" in
      destruct Hc as [cinds [Hic ?]]; try (rewrite <-Hrrs, Hic)
    end.

Ltac derive_child_chns cidx :=
  match goal with
  | [Htn: TreeTopoNode _, H: parentIdxOf _ cidx = Some ?oidx |- _] =>
    pose proof (Htn _ _ H); dest
  end;
  (* For L1 caches derive some more information about "the" child. *)
  try match goal with
      | [H1: In ?oidx (c_l1_indices _), H2: parentIdxOf _ _ = Some ?oidx |- _] =>
        apply tree2Topo_l1_child_ext in H2; [|assumption]; subst
      end.

Ltac derive_child_idx_in cidx :=
  let idx := fresh "idx" in
  remember cidx as idx;
  try
    match goal with
    | [H: In idx (subtreeChildrenIndsOf _ _) |- _] =>
      apply subtreeChildrenIndsOf_parentIdxOf in H; [|auto; fail]
    end;
  match goal with
  | [Hin: In ?oidx (c_li_indices _), Hp: parentIdxOf _ idx = Some ?oidx |- _] =>
    pose proof (tree2Topo_li_child_li_l1 _ _ _ Hin Hp)
  | [Hin: In ?oidx (tl (c_li_indices _)), Hp: parentIdxOf _ idx = Some ?oidx |- _] =>
    pose proof (tree2Topo_li_child_li_l1 _ _ _ (tl_In _ _ Hin) Hp)
  end; subst.
