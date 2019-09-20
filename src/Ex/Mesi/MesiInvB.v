Require Import Bool List String Peano_dec Lia.
Require Import Common FMap IndexSupport HVector Syntax Topology Semantics SemFacts StepM.
Require Import Invariant TrsInv Simulation Serial SerialFacts.
Require Import RqRsLang RqRsCorrect.

Require Import Ex.Spec Ex.SpecInds Ex.Template.
Require Import Ex.Mesi Ex.Mesi.Mesi Ex.Mesi.MesiTopo.

Set Implicit Arguments.

Import PropMonadNotations.
Import CaseNotations.

Local Open Scope list.
Local Open Scope hvec.
Local Open Scope fmap.

Existing Instance Mesi.ImplOStateIfc.

Lemma mesi_RsDownConflicts:
  forall tr (Htr: tr <> Node nil)
         (Hrcinv: InvReachable (impl Htr) step_m (RootChnInv tr 0)),
    InvReachable (impl Htr) step_m (MsgConflictsInv tr 0).
Proof.
  intros.
  apply tree2Topo_MsgConflicts_inv_ok; auto.
  simpl; unfold mem, li, l1.
  rewrite map_app.
  do 2 rewrite map_trans.
  do 2 rewrite map_id.
  rewrite app_comm_cons.
  rewrite <-c_li_indices_head_rootOf by assumption.
  apply SubList_refl.
Qed.

Section Footprints.
  Variable topo: DTree.

  Definition DownLockFromChild (oidx: IdxT) (rqid: RqInfo Msg) :=
    exists cidx,
      rqid.(rqi_midx_rsb) = Some (downTo cidx) /\
      parentIdxOf topo cidx = Some oidx.

  Definition DownLockFromParent (oidx: IdxT) (rqid: RqInfo Msg) :=
    rqid.(rqi_midx_rsb) = Some (rsUpFrom oidx).

  Definition MesiFootprintsInv (st: MState): Prop :=
    forall oidx,
      orq <+- (bst_orqs st)@[oidx];
        rqid <+- orq@[downRq];
        rmsg <+- rqid.(rqi_msg);
        match case rmsg.(msg_id) on idx_dec default True with
        | mesiRqS: DownLockFromChild oidx rqid
        | mesiRqM: DownLockFromChild oidx rqid
        | mesiDownRqS: DownLockFromParent oidx rqid
        | mesiDownRqI: DownLockFromParent oidx rqid
        end.

End Footprints.

Section FootprintsOk.
  Variable (tr: tree).
  Hypothesis (Htr: tr <> Node nil).

  Let topo: DTree := fst (tree2Topo tr 0).
  Let cifc: CIfc := snd (tree2Topo tr 0).
  Let impl: System := impl Htr.

  Lemma mesi_footprints_init:
    Invariant.InvInit impl (MesiFootprintsInv topo).
  Proof.
    do 2 (red; simpl).
    intros.
    destruct (implORqsInit tr)@[oidx] as [orq|] eqn:Horq; simpl; auto.
    unfold implORqsInit in Horq.
    destruct (in_dec idx_dec oidx ((c_li_indices (snd (tree2Topo tr 0)))
                                     ++ c_l1_indices (snd (tree2Topo tr 0)))).
    - rewrite initORqs_value in Horq by assumption.
      inv Horq.
      mred.
    - rewrite initORqs_None in Horq by assumption.
      discriminate.
  Qed.

  Lemma MesiFootprintsInv_update_None:
    forall poss orqs pmsgs,
      MesiFootprintsInv topo {| bst_oss := poss;
                                bst_orqs := orqs;
                                bst_msgs := pmsgs |} ->
      forall noss oidx norq nmsgs,
        norq@[downRq] = None ->
        MesiFootprintsInv topo {| bst_oss := noss;
                                  bst_orqs := orqs +[oidx <- norq];
                                  bst_msgs := nmsgs |}.
  Proof.
    unfold MesiFootprintsInv; simpl; intros.
    mred; auto.
    simpl; rewrite H0; simpl; auto.
  Qed.

  Lemma MesiFootprintsInv_no_update:
    forall poss orqs pmsgs,
      MesiFootprintsInv topo {| bst_oss := poss;
                                bst_orqs := orqs;
                                bst_msgs := pmsgs |} ->
      forall noss oidx porq norq nmsgs,
        orqs@[oidx] = Some porq ->
        norq@[downRq] = porq@[downRq] ->
        MesiFootprintsInv topo {| bst_oss := noss;
                                  bst_orqs := orqs +[oidx <- norq];
                                  bst_msgs := nmsgs |}.
  Proof.
    unfold MesiFootprintsInv; simpl; intros.
    mred; auto.
    simpl; rewrite H1.
    specialize (H oidx).
    rewrite H0 in H; simpl in H.
    assumption.
  Qed.

  Lemma MesiFootprintsInv_case_from_child:
    forall poss orqs pmsgs,
      MesiFootprintsInv topo {| bst_oss := poss;
                                bst_orqs := orqs;
                                bst_msgs := pmsgs |} ->
      forall noss oidx norq rqid rmsg cidx nmsgs,
        norq@[downRq] = Some rqid ->
        rqid.(rqi_msg) = Some rmsg ->
        (rmsg.(msg_id) = mesiRqS \/ rmsg.(msg_id) = mesiRqM) ->
        In cidx (c_li_indices cifc ++ c_l1_indices cifc) ->
        parentIdxOf topo cidx = Some oidx ->
        edgeDownTo topo cidx = rqid.(rqi_midx_rsb) ->
        MesiFootprintsInv topo {| bst_oss := noss;
                                  bst_orqs := orqs +[oidx <- norq];
                                  bst_msgs := nmsgs |}.
  Proof.
    unfold MesiFootprintsInv; simpl; intros.
    mred; auto.
    simpl; rewrite H0; simpl.
    rewrite H1; simpl.
    destruct H2.
    - rewrite H2; simpl.
      exists cidx; split; [|assumption].
      rewrite <-H5.
      pose proof (tree2Topo_TreeTopoNode tr 0).
      specialize (H6 _ _ H4); dest; assumption.
    - rewrite H2; simpl.
      exists cidx; split; [|assumption].
      rewrite <-H5.
      pose proof (tree2Topo_TreeTopoNode tr 0).
      specialize (H6 _ _ H4); dest; assumption.
  Qed.

  Lemma MesiFootprintsInv_case_from_parent:
    forall poss orqs pmsgs,
      MesiFootprintsInv topo {| bst_oss := poss;
                                bst_orqs := orqs;
                                bst_msgs := pmsgs |} ->
      forall noss oidx pidx norq rqid rmsg nmsgs,
        parentIdxOf topo oidx = Some pidx ->
        norq@[downRq] = Some rqid ->
        rqid.(rqi_msg) = Some rmsg ->
        (rmsg.(msg_id) = mesiDownRqS \/ rmsg.(msg_id) = mesiDownRqI) ->
        rsEdgeUpFrom topo oidx = rqid.(rqi_midx_rsb) ->
        MesiFootprintsInv topo {| bst_oss := noss;
                                  bst_orqs := orqs +[oidx <- norq];
                                  bst_msgs := nmsgs |}.
  Proof.
    unfold MesiFootprintsInv; simpl; intros.
    mred; auto.
    simpl; rewrite H1; simpl.
    rewrite H2; simpl.
    destruct H3.
    - rewrite H3; simpl.
      red; rewrite <-H4.
      pose proof (tree2Topo_TreeTopoNode tr 0).
      specialize (H5 _ _ H0); dest; assumption.
    - rewrite H3; simpl.
      red; rewrite <-H4.
      pose proof (tree2Topo_TreeTopoNode tr 0).
      specialize (H5 _ _ H0); dest; assumption.
  Qed.
  
  Lemma mesi_footprints_step:
    Invariant.InvStep impl step_m (MesiFootprintsInv topo).
  Proof.
    red; intros.
    pose proof (tree2Topo_TreeTopoNode tr 0) as Htn.
    pose proof (footprints_ok
                  (mesi_GoodORqsInit Htr)
                  (mesi_GoodRqRsSys Htr) H) as Hftinv.
    inv H1; [assumption..|].

    simpl in H2; destruct H2; [subst|apply in_app_or in H1; destruct H1].

    - (*! Cases for the main memory *)

      (** Abstract the root. *)
      assert (In (rootOf (fst (tree2Topo tr 0)))
                 (c_li_indices (snd (tree2Topo tr 0)))).
      { rewrite c_li_indices_head_rootOf by assumption.
        left; reflexivity.
      }
      remember (rootOf (fst (tree2Topo tr 0))) as oidx; clear Heqoidx.
      simpl in *.

      (** Do case analysis per a rule. *)
      apply in_app_or in H3; destruct H3.

      1: { (** Rules per a child *)
        apply concat_In in H2; destruct H2 as [crls [? ?]].
        apply in_map_iff in H2; destruct H2 as [cidx [? ?]]; subst.

        (** Derive that the child has the parent. *)
        assert (parentIdxOf (fst (tree2Topo tr 0)) cidx = Some oidx)
          by (apply subtreeChildrenIndsOf_parentIdxOf; auto).
        
        dest_in; disc_rule_conds_ex.
        all: try (eapply MesiFootprintsInv_update_None; eauto; fail).
        all: try (derive_child_chns cidx;
                  derive_child_idx_in cidx;
                  eapply MesiFootprintsInv_case_from_child with (rmsg:= rmsg);
                  [|mred|..]; eauto).
      }

      dest_in; disc_rule_conds_ex.
      all: try (eapply MesiFootprintsInv_update_None; eauto; mred).

    - (*! Cases for Li caches *)

      (** Derive some necessary information: each Li has a parent. *)
      apply in_map_iff in H1; destruct H1 as [oidx [? ?]]; subst; simpl in *.
      pose proof (c_li_indices_tail_has_parent Htr _ _ H2).
      destruct H1 as [pidx [? ?]].
      pose proof (Htn _ _ H4); dest.
      
      (** Do case analysis per a rule. *)
      apply in_app_or in H3; destruct H3.

      1: { (** Rules per a child *)
        apply concat_In in H3; destruct H3 as [crls [? ?]].
        apply in_map_iff in H3; destruct H3 as [cidx [? ?]]; subst.

        (** Derive that the child has the parent. *)
        assert (parentIdxOf (fst (tree2Topo tr 0)) cidx = Some oidx)
          by (apply subtreeChildrenIndsOf_parentIdxOf; auto).

        dest_in; disc_rule_conds_ex.
        all: try (eapply MesiFootprintsInv_update_None; eauto; fail).
        all: try (eapply MesiFootprintsInv_no_update; eauto; mred; fail).
        all: try (derive_child_chns cidx;
                  derive_child_idx_in cidx;
                  eapply MesiFootprintsInv_case_from_child with (rmsg:= rmsg);
                  [|mred|..]; eauto).
      }

      dest_in; disc_rule_conds_ex.
      all: try (eapply MesiFootprintsInv_update_None; eauto; mred; fail).
      all: try (eapply MesiFootprintsInv_no_update; eauto;
                unfold addRqS; mred; fail).
      all: try (eapply MesiFootprintsInv_case_from_parent with (rmsg:= rmsg);
                [| |mred|..]; eauto; fail).
      { derive_footprint_info_basis oidx.
        derive_child_idx_in cidx.
        eapply MesiFootprintsInv_case_from_child with (rmsg:= msg);
          [|mred|..]; eauto.
      }

    - (*! Cases for L1 caches *)

      (** Do case analysis per a rule. *)
      apply in_map_iff in H1; destruct H1 as [oidx [? ?]]; subst.
      dest_in; disc_rule_conds_ex.
      all: try (eapply MesiFootprintsInv_update_None; eauto; mred; fail).
      all: try (eapply MesiFootprintsInv_no_update; eauto;
                unfold addRqS; mred; fail).
  Qed.

  Theorem mesi_footprints_ok:
    InvReachable impl step_m (MesiFootprintsInv topo).
  Proof.
    apply inv_reachable.
    - apply mesi_footprints_init.
    - apply mesi_footprints_step.
  Qed.

End FootprintsOk.

Ltac disc_mesi_footprints_inv oidx Hinv :=
  specialize (Hinv oidx); simpl in Hinv;
  disc_rule_conds_ex;
  repeat
    match goal with
    | [Hrqi: rqi_msg _ = Some ?msg, Hmsg: msg_id ?msg = _ |- _] =>
      rewrite Hmsg in Hinv; simpl in Hinv
    | [Hdfc: DownLockFromChild _ _ _ |- _] =>
      red in Hdfc; dest; disc_rule_conds_ex
    | [Hdfp: DownLockFromParent _ _ |- _] =>
      red in Hdfp; dest; disc_rule_conds_ex; solve_midx_false
    end.

Section InvProof.
  Variable (tr: tree).
  Hypothesis (Htr: tr <> Node nil).

  Let topo: DTree := fst (tree2Topo tr 0).
  Let cifc: CIfc := snd (tree2Topo tr 0).
  Let impl: System := impl Htr.

  Lemma mesi_RootChnInv_init:
    Invariant.InvInit impl (RootChnInv tr 0).
  Proof.
    do 2 (red; simpl).
    intros.
    intro Hx; do 2 (red in Hx).
    dest_in.
  Qed.

  Ltac disc_RootChnInv :=
    intros;
    let Hx := fresh "H" in
    intro Hx;
    repeat
      match goal with
      | [H: In _ (subtreeChildrenIndsOf _ _) |- _] =>
        apply subtreeChildrenIndsOf_parentIdxOf in H; auto
      | [Hm: InMPI (enqMsgs _ _) _ |- _] =>
        apply InMP_enqMsgs_or in Hm; destruct Hm
      | [Hinv: _ -> _ -> ~ InMPI _ _,  Hm: InMP _ _ (deqMsgs _ _) |- _] =>
        apply InMP_deqMsgs in Hm; eapply Hinv; eauto
      | [H: In (idOf ?idm, valOf ?idm) _ |- _] =>
        let midx := fresh "midx" in
        let msg := fresh "msg" in
        destruct idm as [midx msg]; simpl in *
      end;
    disc_rule_conds_ex.

  Ltac solve_RootChnInv :=
    repeat
      match goal with
      | [H1: In _ ?l, H2: SubList ?l (subtreeChildrenIndsOf _ _) |- _] =>
        apply H2 in H1
      | [H: In _ (subtreeChildrenIndsOf _ _) |- _] =>
        apply subtreeChildrenIndsOf_parentIdxOf in H; auto
      | [H: In _ (map _ _) |- _] => apply in_map_iff in H; dest
      | [H: (_, _) = (_, _) |- _] => inv H
      | [H: _ \/ _ \/ _ |- _] => destruct H as [|[|]]; try discriminate
      | [H: rqUpFrom _ = rqUpFrom _ |- _] => inv H
      | [H: rsUpFrom _ = rsUpFrom _ |- _] => inv H
      | [H: downTo _ = downTo _ |- _] => inv H

      | [H: parentIdxOf _ ?oidx = Some ?oidx |- _] =>
        exfalso; eapply parentIdxOf_not_eq; eauto
      | [H1: ?oidx = rootOf _, H2: parentIdxOf _ ?oidx = Some _ |- _] => rewrite H1 in H2
      | [H: parentIdxOf _ (rootOf _) = Some ?idx |- _] =>
        eapply parentIdxOf_child_not_root with (pidx:= idx); eauto
      | [H: In (rootOf _) (tl (c_li_indices _)) |- _] =>
        exfalso; eapply tree2Topo_root_not_in_tl_li; eauto
      | [H: In (rootOf _) (c_l1_indices _) |- _] =>
        exfalso; eapply tree2Topo_root_not_in_l1; eauto
      | [H1: In ?oidx (c_l1_indices _), H2: l1ExtOf ?oidx = rootOf _ |- _] =>
        eapply tree2Topo_root_not_l1ExtOf; eauto
      end.

  Lemma mesi_RootChnInv_step:
    Invariant.InvStep impl step_m (RootChnInv tr 0).
  Proof.
    red; intros.
    pose proof (tree2Topo_TreeTopoNode tr 0) as Htn.
    pose proof (footprints_ok
                  (mesi_GoodORqsInit Htr)
                  (mesi_GoodRqRsSys Htr) H) as Hftinv.
    pose proof (mesi_footprints_ok H) as Hmftinv.
    inv H1; [assumption|..].

    1: {
      red; simpl; intros.
      intro Hx; apply InMP_enqMsgs_or in Hx.
      destruct Hx; [|eapply H0; eauto].
      apply in_map with (f:= idOf) in H4; simpl in H4.
      apply H3 in H4; simpl in H4.
      eapply DisjList_In_1.
      + apply tree2Topo_minds_merqs_disj.
      + eassumption.
      + eapply tree2Topo_obj_chns_minds_SubList.
        * rewrite c_li_indices_head_rootOf by assumption.
          left; reflexivity.
        * destruct H1 as [|[|]]; rewrite H1; simpl; tauto.
    }

    1: {
      red; simpl; intros.
      intro Hx; apply InMP_deqMsgs in Hx.
      eapply H0; eauto.
    }

    simpl in H2; destruct H2; [subst|apply in_app_or in H1; destruct H1].

    - (*! Cases for the main memory *)

      (** Abstract the root. *)
      unfold RootChnInv in *; simpl in *.
      remember (rootOf (fst (tree2Topo tr 0))) as oidx; clear Heqoidx.

      (** Do case analysis per a rule. *)
      apply in_app_or in H3; destruct H3.

      1: { (** Rules per a child *)
        apply concat_In in H1; destruct H1 as [crls [? ?]].
        apply in_map_iff in H1; destruct H1 as [cidx [? ?]]; subst.
        dest_in; try (disc_RootChnInv; solve_RootChnInv; fail).
      }

      dest_in.
      all: try (disc_RootChnInv;
                disc_mesi_footprints_inv oidx Hmftinv;
                solve_RootChnInv).

    - (*! Cases for Li caches *)
      unfold RootChnInv in *; simpl in *.

      (** Derive some necessary information: each Li has a parent. *)
      apply in_map_iff in H1; destruct H1 as [oidx [? ?]]; subst; simpl in *.
      pose proof (c_li_indices_tail_has_parent Htr _ _ H2).
      destruct H1 as [pidx [? ?]].
      pose proof (Htn _ _ H4); dest.
      
      (** Do case analysis per a rule. *)
      apply in_app_or in H3; destruct H3.

      1: { (** Rules per a child *)
        apply concat_In in H3; destruct H3 as [crls [? ?]].
        apply in_map_iff in H3; destruct H3 as [cidx [? ?]]; subst.
        dest_in; try (disc_RootChnInv; solve_RootChnInv; fail).
      }

      dest_in.
      all: try (disc_RootChnInv; solve_RootChnInv; fail).
      all: try (disc_RootChnInv;
                derive_footprint_info_basis oidx;
                derive_child_chns cidx;
                disc_rule_conds_ex;
                solve_RootChnInv;
                fail).
      all: try (disc_RootChnInv;
                derive_footprint_info_basis oidx;
                [|disc_mesi_footprints_inv oidx Hmftinv];
                derive_child_chns upCIdx;
                disc_rule_conds_ex;
                solve_RootChnInv;
                fail).
      all: try (disc_RootChnInv;
                derive_footprint_info_basis oidx;
                [disc_mesi_footprints_inv oidx Hmftinv|];
                disc_rule_conds_ex;
                solve_RootChnInv).

    - (*! Cases for L1 caches *)
      unfold RootChnInv in *; simpl in *.

      (** Do case analysis per a rule. *)
      apply in_map_iff in H1; destruct H1 as [oidx [? ?]]; subst.
      dest_in.
      all: try (disc_RootChnInv; solve_RootChnInv; fail).
      all: try (disc_RootChnInv;
                derive_footprint_info_basis oidx;
                derive_child_chns cidx;
                disc_rule_conds_ex;
                solve_RootChnInv).

      Unshelve.
      all: assumption.
  Qed.

  Theorem mesi_RootChnInv_ok:
    InvReachable impl step_m (RootChnInv tr 0).
  Proof.
    apply inv_reachable.
    - apply mesi_RootChnInv_init.
    - apply mesi_RootChnInv_step.
  Qed.
  
End InvProof.

