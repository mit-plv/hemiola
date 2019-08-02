Require Import List FMap Omega.
Require Import Common Topology Syntax IndexSupport.
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

(** TODO: move to [ListSupport.v] *)
Definition nil_dec {A}: forall l: list A, {l = nil} + {l <> nil}.
Proof.
  intros; destruct l; [left; reflexivity|right; discriminate].
Defined.

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

Definition TreeTopo (dtr: DTree) :=
  TreeTopoNode dtr /\ TreeTopoEdge dtr.

Section TreeTopo.

  Lemma l1ExtOf_not_eq:
    forall bidx, l1ExtOf bidx <> bidx.
  Proof.
    intros; induction bidx; [discriminate|].
    intro Hx; inv Hx; auto.
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
      apply incMap_In in H1.
      destruct H1 as [ctr [ofs [? ?]]]; simpl in *.
      apply nth_error_In in H0.
      eapply tree2Topo_root_edges; eauto.

    - apply in_map_iff in H0.
      destruct H0 as [[ctr cifc] [? ?]]; simpl in *; subst.
      apply incMap_In in H2.
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
      apply incMap_In in H2.
      destruct H2 as [ctr [ofs [? ?]]]; simpl in *.
      pose proof (tree2Topo_root_edges _ _ (eq_sym H2)); dest.
      destruct H0 as [|[|]].
      + rewrite H0 in H3; inv H3; reflexivity.
      + rewrite H0 in H4; inv H4; reflexivity.
      + rewrite H0 in H5; inv H5; reflexivity.

    - apply in_map_iff in H1.
      destruct H1 as [[ctr cifc] [? ?]]; simpl in *; subst.
      apply incMap_In in H3.
      destruct H3 as [ctr [ofs [? ?]]]; simpl in *.
      apply nth_error_In in H1.
      rewrite Forall_forall in H; specialize (H _ H1 bidx~>ofs).
      rewrite <-H3 in H; simpl in H.
      specialize (H oidx midx).
      cbv [parentIdxOf rqEdgeUpFrom rsEdgeUpFrom edgeDownTo
                       upEdgesFrom downEdgesTo] in H.
      rewrite H2 in H; simpl in H; auto.
  Qed.

  Lemma tree2Topo_TreeTopo:
    forall tr bidx, TreeTopo (fst (tree2Topo tr bidx)).
  Proof.
    intros; split.
    - apply tree2Topo_TreeTopoNode.
    - apply tree2Topo_TreeTopoEdge.
  Qed.

End TreeTopo.

Section Facts.

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
    forall `{oifc: OStateIfc} tr bidx topo cifc (impl: System),
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
    forall {oifc: OStateIfc} tr bidx topo cifc (impl: System),
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

End Facts.

