Require Import Bool List String Peano_dec Lia.
Require Import Common FMap IndexSupport HVector Syntax Topology Semantics SemFacts StepM.
Require Import Invariant TrsInv Simulation Serial SerialFacts.
Require Import RqRsLang RqRsCorrect.

Require Import Ex.Spec Ex.SpecInds Ex.Template.
Require Import Ex.Mesi Ex.Mesi.Mesi Ex.Mesi.MesiObjInv Ex.Mesi.MesiTopo.

Set Implicit Arguments.

Import PropMonadNotations.
Import CaseNotations.

Local Open Scope list.
Local Open Scope hvec.
Local Open Scope fmap.

Existing Instance Mesi.ImplOStateIfc.

Lemma mesi_InObjInds:
  forall tr (Htr: tr <> Node nil),
    InvReachable (impl Htr) step_m (InObjInds tr 0).
Proof.
  intros.
  apply tree2Topo_InObjInds_inv_ok.
  - red; simpl; intros.
    destruct ((implOStatesInit tr)@[oidx]) as [ost|] eqn:Host; simpl; auto.
    destruct (in_dec idx_dec oidx ((c_li_indices (snd (tree2Topo tr 0)))
                                     ++ c_l1_indices (snd (tree2Topo tr 0)))); auto.
    rewrite implOStatesInit_None in Host by assumption.
    discriminate.
  - simpl; rewrite c_li_indices_head_rootOf by assumption.
    apply SubList_cons; [left; reflexivity|].
    simpl; apply SubList_cons_right.
    rewrite map_app.
    do 2 rewrite map_map.
    apply SubList_app_6.
    all: simpl; rewrite map_id; apply SubList_refl.
Qed.

Lemma mesi_OstInds:
  forall tr (Htr: tr <> Node nil),
    InvReachable (impl Htr) step_m (OstInds tr 0).
Proof.
  intros.
  apply tree2Topo_OstInds_inv_ok.
  red; simpl; intros.
  split.
  - rewrite c_li_indices_head_rootOf in H by assumption.
    inv H.
    + rewrite implOStatesInit_value_root by assumption; eauto.
    + rewrite implOStatesInit_value_non_root by assumption; eauto.
  - rewrite implORqsInit_value by assumption; eauto.
Qed.

Lemma mesi_MsgConflictsInv:
  forall tr (Htr: tr <> Node nil)
         (Hrcinv: InvReachable (impl Htr) step_m (RootChnInv tr 0)),
    InvReachable (impl Htr) step_m (MsgConflictsInv tr 0).
Proof.
  intros.
  apply tree2Topo_MsgConflicts_inv_ok
    with (oinvs:= MesiObjInvs (fst (tree2Topo tr 0))); auto.
  simpl; unfold mem, li, l1.
  rewrite map_app.
  do 2 rewrite map_trans.
  do 2 rewrite map_id.
  rewrite app_comm_cons.
  rewrite <-c_li_indices_head_rootOf by assumption.
  apply SubList_refl.
Qed.

Section ObjInvOk.
  Variable (tr: tree).
  Hypothesis (Htr: tr <> Node nil).

  Let topo: DTree := fst (tree2Topo tr 0).
  Let cifc: CIfc := snd (tree2Topo tr 0).
  Let impl: System := impl Htr.

  Definition MesiUpLockInv (st: State): Prop :=
    liftObjInvs MesiUpLockObjInv st.

  Definition MesiDownLockInv (st: State): Prop :=
    liftObjInvs (MesiDownLockObjInv topo) st.

  (*! [MesiUpLockInv] *)

  Lemma MesiUpLockInv_init:
    Invariant.InvInit impl MesiUpLockInv.
  Proof.
    do 3 (red; simpl); intros; red; simpl.
    destruct (implOStatesInit tr)@[oidx] as [ost|] eqn:Host; simpl; auto.
    destruct (implORqsInit tr)@[oidx] as [orq|] eqn:Horq; simpl; auto.
    red; simpl.
    unfold implORqsInit in Horq.
    destruct (in_dec idx_dec oidx ((c_li_indices (snd (tree2Topo tr 0)))
                                     ++ c_l1_indices (snd (tree2Topo tr 0)))).
    - rewrite initORqs_value in Horq by assumption.
      inv Horq.
      mred.
    - rewrite initORqs_None in Horq by assumption.
      discriminate.
  Qed.

  Lemma MesiUpLockInv_update_None:
    forall oss orqs pmsgs,
      MesiUpLockInv {| st_oss := oss;
                       st_orqs := orqs;
                       st_msgs := pmsgs |} ->
      forall oidx nost norq nmsgs,
        norq@[upRq] = None ->
        MesiUpLockInv {| st_oss := oss +[oidx <- nost];
                         st_orqs := orqs +[oidx <- norq];
                         st_msgs := nmsgs |}.
  Proof.
    cbv [MesiUpLockInv liftObjInvs liftObjInv MesiUpLockObjInv]; simpl; intros.
    specialize (H oidx0).
    mred; simpl.
    rewrite H0; simpl; auto.
  Qed.

  Lemma MesiUpLockInv_no_update:
    forall oss orqs pmsgs,
      MesiUpLockInv {| st_oss := oss;
                       st_orqs := orqs;
                       st_msgs := pmsgs |} ->
      forall oidx post porq nost norq nmsgs,
        oss@[oidx] = Some post ->
        nost#[owned] = post#[owned] ->
        nost#[status] = post#[status] ->
        nost#[dir].(dir_st) = post#[dir].(dir_st) ->
        orqs@[oidx] = Some porq ->
        norq@[upRq] = porq@[upRq] ->
        MesiUpLockInv {| st_oss := oss +[oidx <- nost];
                         st_orqs := orqs +[oidx <- norq];
                         st_msgs := nmsgs |}.
  Proof.
    cbv [MesiUpLockInv liftObjInvs liftObjInv MesiUpLockObjInv]; simpl; intros.
    mred; auto.
    simpl; rewrite H1, H2, H3, H5.
    specialize (H oidx).
    rewrite H0, H4 in H; simpl in H.
    assumption.
  Qed.

  Ltac disc_MesiUpLockInv_internal oidx :=
    repeat
      match goal with
      | [Hdl: MesiUpLockInv _ |- _] =>
        (specialize (Hdl oidx); do 2 red in Hdl; simpl in Hdl)
      | [Hmv: ?m@[?i] = Some ?v, H: context [?m@[?i]] |- _] =>
        rewrite Hmv in H; simpl in H
      end;
    disc_mesi_obj_invs; dest.

  Ltac disc_MesiDownLockInv_internal oidx :=
    repeat
      match goal with
      | [Hdl: MesiDownLockInv _ |- _] =>
        (specialize (Hdl oidx); do 2 red in Hdl; simpl in Hdl)
      | [Hmv: ?m@[?i] = Some ?v, H: context [?m@[?i]] |- _] =>
        rewrite Hmv in H; simpl in H
      end;
    disc_mesi_obj_invs; dest.

  Ltac solve_MesiUpLockInv oidx :=
    try match goal with
        | [Hul: MesiUpLockInv _ |- _] =>
          let noidx := fresh "oidx" in
          do 2 red; simpl; intro noidx;
          red; simpl;
          repeat (mred; simpl); [|apply Hul; fail]
        end;
    disc_MesiUpLockInv_internal oidx;
    red; mred; simpl;
    repeat
      match goal with
      | [H: _ <+- ?ov; _ |- _ <+- ?ov; _] =>
        let Hov := fresh "H" in
        let v := fresh "v" in
        destruct ov as [v|] eqn:Hov; simpl in *; [|auto; fail]
      | [H: msg_id ?rmsg = _ |- context [msg_id ?rmsg] ] =>
        rewrite H; simpl
      end;
    repeat (find_if_inside;
            [dest; try congruence; repeat split; intuition solve_mesi|]);
    auto.

  Lemma MesiUpLockInv_mutual_step:
    Invariant.MutualInvStep1 impl step_m MesiUpLockInv MesiDownLockInv.
  Proof. (* SKIP_PROOF_ON
    red; intros.
    pose proof (tree2Topo_TreeTopoNode tr 0) as Htn.
    pose proof (footprints_ok
                  (mesi_GoodORqsInit Htr)
                  (mesi_GoodRqRsSys Htr) H) as Hftinv.
    inv H2; [assumption..|].

    simpl in H3; destruct H3; [subst|apply in_app_or in H2; destruct H2].

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
      apply in_app_or in H4; destruct H4.

      1: { (** Rules per a child *)
        apply concat_In in H3; destruct H3 as [crls [? ?]].
        apply in_map_iff in H3; destruct H3 as [cidx [? ?]]; subst.

        (** Derive that the child has the parent. *)
        assert (parentIdxOf (fst (tree2Topo tr 0)) cidx = Some oidx)
          by (apply subtreeChildrenIndsOf_parentIdxOf; auto).

        dest_in; disc_rule_conds_ex.
        all: try (eapply MesiUpLockInv_update_None; eauto; fail).
        all: try (eapply MesiUpLockInv_no_update; eauto; mred; fail).
      }

      dest_in; disc_rule_conds_ex.

      { disc_MesiDownLockInv_internal oidx.
        solve_MesiUpLockInv oidx.
      }
      { disc_MesiDownLockInv_internal oidx.
        destruct H17; dest.
        all: solve_MesiUpLockInv oidx.
      }
      { disc_MesiDownLockInv_internal oidx.
        destruct H17; dest.
        all: solve_MesiUpLockInv oidx.
      }

    - (*! Cases for Li caches *)

      (** Derive some necessary information: each Li has a parent. *)
      apply in_map_iff in H2; destruct H2 as [oidx [? ?]]; subst; simpl in *.
      pose proof (c_li_indices_tail_has_parent Htr _ _ H3).
      destruct H2 as [pidx [? ?]].
      pose proof (Htn _ _ H5); dest.

      (** Do case analysis per a rule. *)
      apply in_app_or in H4; destruct H4.

      1: { (** Rules per a child *)
        apply concat_In in H4; destruct H4 as [crls [? ?]].
        apply in_map_iff in H4; destruct H4 as [cidx [? ?]]; subst.

        (** Derive that the child has the parent. *)
        assert (parentIdxOf (fst (tree2Topo tr 0)) cidx = Some oidx)
          by (apply subtreeChildrenIndsOf_parentIdxOf; auto).

        dest_in; disc_rule_conds_ex.
        all: try (eapply MesiUpLockInv_update_None; eauto; fail).
        all: try (eapply MesiUpLockInv_no_update; eauto; mred; fail).
        { solve_MesiUpLockInv oidx. }
        { solve_MesiUpLockInv oidx. }
      }

      dest_in; disc_rule_conds_ex.
      all: try (eapply MesiUpLockInv_update_None; eauto; mred; fail).
      all: try (eapply MesiUpLockInv_no_update; eauto;
                unfold addRqS; mred; fail).
      all: try (solve_MesiUpLockInv oidx; fail).
      all: try (solve_MesiUpLockInv oidx; unfold addRqS; mred; fail).
      all: try (disc_MesiDownLockInv_internal oidx; solve_MesiUpLockInv oidx; fail).
      { disc_MesiDownLockInv_internal oidx.
        destruct H22; dest.
        all: solve_MesiUpLockInv oidx.
      }
      { disc_MesiDownLockInv_internal oidx.
        destruct H22; dest.
        all: solve_MesiUpLockInv oidx.
      }

    - (*! Cases for L1 caches *)

      (** Do case analysis per a rule. *)
      apply in_map_iff in H2; destruct H2 as [oidx [? ?]]; subst.
      dest_in; disc_rule_conds_ex.
      all: try (eapply MesiUpLockInv_update_None; eauto; mred; fail).
      all: try (solve_MesiUpLockInv oidx; fail).
      all: solve_MesiUpLockInv oidx; unfold addRqS; mred.

      END_SKIP_PROOF_ON *) admit.
  Qed.

  (*! [MesiDownLockInv] *)

  Lemma MesiDownLockInv_init:
    Invariant.InvInit impl MesiDownLockInv.
  Proof.
    do 3 (red; simpl); intros; red; simpl.
    destruct (implOStatesInit tr)@[oidx] as [ost|] eqn:Host; simpl; auto.
    destruct (implORqsInit tr)@[oidx] as [orq|] eqn:Horq; simpl; auto.
    red; simpl.
    unfold implORqsInit in Horq.
    destruct (in_dec idx_dec oidx ((c_li_indices (snd (tree2Topo tr 0)))
                                     ++ c_l1_indices (snd (tree2Topo tr 0)))).
    - rewrite initORqs_value in Horq by assumption.
      inv Horq.
      mred.
    - rewrite initORqs_None in Horq by assumption.
      discriminate.
  Qed.

  Lemma MesiDownLockInv_update_None:
    forall oss orqs pmsgs,
      MesiDownLockInv {| st_oss := oss; st_orqs := orqs; st_msgs := pmsgs |} ->
      forall oidx nost norq nmsgs,
        norq@[downRq] = None ->
        MesiDownLockInv {| st_oss := oss +[oidx <- nost];
                           st_orqs := orqs +[oidx <- norq];
                           st_msgs := nmsgs |}.
  Proof.
    cbv [MesiDownLockInv liftObjInvs liftObjInv MesiDownLockObjInv]; simpl; intros.
    specialize (H oidx0).
    mred; simpl.
    rewrite H0; simpl; auto.
  Qed.

  Lemma MesiDownLockInv_no_update:
    forall oss orqs pmsgs,
      MesiDownLockInv {| st_oss := oss; st_orqs := orqs; st_msgs := pmsgs |} ->
      forall oidx post porq nost norq nmsgs,
        oss@[oidx] = Some post ->
        nost#[owned] = post#[owned] ->
        nost#[status] = post#[status] ->
        nost#[dir] = post#[dir] ->
        orqs@[oidx] = Some porq ->
        norq@[downRq] = porq@[downRq] ->
        MesiDownLockInv {| st_oss := oss +[oidx <- nost];
                           st_orqs := orqs +[oidx <- norq];
                           st_msgs := nmsgs |}.
  Proof.
    cbv [MesiDownLockInv liftObjInvs liftObjInv MesiDownLockObjInv]; simpl; intros.
    mred; auto.
    simpl; rewrite H1, H2, H3, H5.
    specialize (H oidx).
    rewrite H0, H4 in H; simpl in H.
    assumption.
  Qed.

  Ltac solve_MesiDownLockInv oidx :=
    try match goal with
        | [Hdl: MesiDownLockInv _ |- _] =>
          let noidx := fresh "oidx" in
          do 2 red; simpl; intro noidx;
          red; simpl;
          repeat (mred; simpl); [|apply Hdl; fail]
        end;
    disc_MesiDownLockInv_internal oidx;
    red; mred; simpl;
    repeat
      match goal with
      | [H: _ <+- ?ov; _ |- _ <+- ?ov; _] =>
        let Hov := fresh "H" in
        let v := fresh "v" in
        destruct ov as [v|] eqn:Hov; simpl in *; [|auto; fail]
      | [H: msg_id ?rmsg = _ |- context [msg_id ?rmsg] ] =>
        rewrite H; simpl
      end;
    repeat split;
    repeat match goal with
           | |- DownLockFromChild _ _ _ => red; simpl; eauto; fail
           | |- context [map _ (map _ _)] => rewrite rqi_rss_map_map
           | |- _ => repeat split; intuition solve_mesi
           end.

  Lemma MesiDownLockInv_mutual_step:
    Invariant.MutualInvStep2 impl step_m MesiUpLockInv MesiDownLockInv.
  Proof. (* SKIP_PROOF_ON
    red; intros.
    pose proof (tree2Topo_TreeTopoNode tr 0) as Htn.
    pose proof (footprints_ok
                  (mesi_GoodORqsInit Htr)
                  (mesi_GoodRqRsSys Htr) H) as Hftinv.
    inv H2; [assumption..|].

    simpl in H3; destruct H3; [subst|apply in_app_or in H2; destruct H2].

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
      apply in_app_or in H4; destruct H4.

      1: { (** Rules per a child *)
        apply concat_In in H3; destruct H3 as [crls [? ?]].
        apply in_map_iff in H3; destruct H3 as [cidx [? ?]]; subst.

        (** Derive that the child has the parent. *)
        assert (parentIdxOf (fst (tree2Topo tr 0)) cidx = Some oidx)
          by (apply subtreeChildrenIndsOf_parentIdxOf; auto).

        dest_in; disc_rule_conds_ex.
        all: try (eapply MesiDownLockInv_update_None; eauto; fail).
        all: try (derive_child_chns cidx; derive_child_idx_in cidx;
                  solve_MesiDownLockInv oidx; fail).
      }

      dest_in; disc_rule_conds_ex.
      all: try (eapply MesiDownLockInv_update_None; eauto; mred).

    - (*! Cases for Li caches *)

      (** Derive some necessary information: each Li has a parent. *)
      apply in_map_iff in H2; destruct H2 as [oidx [? ?]]; subst; simpl in *.
      pose proof (c_li_indices_tail_has_parent Htr _ _ H3).
      destruct H2 as [pidx [? ?]].
      pose proof (Htn _ _ H5); dest.

      (** Do case analysis per a rule. *)
      apply in_app_or in H4; destruct H4.

      1: { (** Rules per a child *)
        apply concat_In in H4; destruct H4 as [crls [? ?]].
        apply in_map_iff in H4; destruct H4 as [cidx [? ?]]; subst.

        (** Derive that the child has the parent. *)
        assert (parentIdxOf (fst (tree2Topo tr 0)) cidx = Some oidx)
          by (apply subtreeChildrenIndsOf_parentIdxOf; auto).

        dest_in; disc_rule_conds_ex.
        all: try (eapply MesiDownLockInv_update_None; eauto; fail).
        all: try (eapply MesiDownLockInv_no_update; eauto; mred; fail).
        all: try (derive_child_chns cidx; derive_child_idx_in cidx;
                  solve_MesiDownLockInv oidx).
      }

      dest_in; disc_rule_conds_ex.
      all: try (eapply MesiDownLockInv_update_None; eauto; mred; fail).
      all: try (eapply MesiDownLockInv_no_update; eauto;
                unfold addRqS; mred; fail).
      all: try (solve_MesiDownLockInv oidx; fail).
      { disc_MesiUpLockInv_internal oidx.
        derive_footprint_info_basis oidx.
        derive_child_chns cidx.
        derive_child_idx_in cidx.
        disc_rule_conds_ex.
        solve_MesiDownLockInv oidx.
      }

    - (*! Cases for L1 caches *)

      (** Do case analysis per a rule. *)
      apply in_map_iff in H2; destruct H2 as [oidx [? ?]]; subst.
      dest_in; disc_rule_conds_ex.
      all: try (eapply MesiDownLockInv_update_None; eauto; mred; fail).
      all: try (eapply MesiDownLockInv_no_update; eauto;
                unfold addRqS; mred; fail).

      END_SKIP_PROOF_ON *) admit.
  Qed.

  Theorem MesiLockInv_ok:
    InvReachable impl step_m (fun st => MesiUpLockInv st /\ MesiDownLockInv st).
  Proof.
    eapply mutual_inv_reachable.
    - typeclasses eauto.
    - apply MesiUpLockInv_init.
    - apply MesiDownLockInv_init.
    - apply MesiUpLockInv_mutual_step.
    - apply MesiDownLockInv_mutual_step.
  Qed.

  Corollary MesiObjInvs_ok:
    InvReachable impl step_m (liftObjInvs (MesiObjInvs topo)).
  Proof.
    red; intros.
    apply MesiLockInv_ok in H; dest.
    red; intros.
    specialize (H oidx); specialize (H0 oidx).
    red; red in H, H0.
    destruct (st_oss ist)@[oidx] as [ost|]; simpl in *; [|auto].
    destruct (st_orqs ist)@[oidx] as [orq|]; simpl in *; [|auto].
    split; assumption.
  Qed.

  Corollary MesiUpLockInv_ok:
    InvReachable impl step_m MesiUpLockInv.
  Proof.
    red; intros.
    apply MesiLockInv_ok; assumption.
  Qed.

  Corollary MesiDownLockInv_ok:
    InvReachable impl step_m MesiDownLockInv.
  Proof.
    red; intros.
    apply MesiLockInv_ok; assumption.
  Qed.

End ObjInvOk.

Ltac disc_MesiUpLockInv oidx :=
  repeat
    match goal with
    | [Hdl: MesiUpLockInv _ |- _] =>
      (specialize (Hdl oidx); do 2 red in Hdl; simpl in Hdl)
    | [Hmv: ?m@[?i] = Some ?v, H: context [?m@[?i]] |- _] =>
      rewrite Hmv in H; simpl in H
    end;
  disc_mesi_obj_invs; dest.

Ltac disc_MesiDownLockInv oidx Hinv :=
  specialize (Hinv oidx); do 2 red in Hinv; simpl in Hinv;
  disc_rule_conds_ex; disc_mesi_obj_invs; dest;
  repeat
    match goal with
    | [Hrqi: rqi_msg _ = Some ?msg, Hmsg: msg_id ?msg = _ |- _] =>
      rewrite Hmsg in Hinv; simpl in Hinv
    | [H: DownLockFromChild _ _ _ /\ _ |- _] => destruct H
    | [H: DownLockFromParent _ _ /\ _ |- _] => destruct H
    | [Hdfc: DownLockFromChild _ _ _ |- _] =>
      red in Hdfc; dest; disc_rule_conds_ex
    | [Hdfp: DownLockFromParent _ _ |- _] =>
      red in Hdfp; dest; disc_rule_conds_ex; solve_midx_false
    end.

Section RootChnInv.
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
      | [H: In _ (remove _ _ (dir_sharers _)) |- _] => apply in_remove in H
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
        exfalso; eapply parentIdxOf_not_eq in H; eauto
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
  Proof. (* SKIP_PROOF_ON
    red; intros.
    pose proof (tree2Topo_TreeTopoNode tr 0) as Htn.
    pose proof (footprints_ok
                  (mesi_GoodORqsInit Htr)
                  (mesi_GoodRqRsSys Htr) H) as Hftinv.
    pose proof (MesiDownLockInv_ok H) as Hmftinv.
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
                disc_MesiDownLockInv oidx Hmftinv;
                solve_RootChnInv; fail).

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
                [|disc_MesiDownLockInv oidx Hmftinv];
                derive_child_chns upCIdx;
                disc_rule_conds_ex;
                solve_RootChnInv;
                fail).
      all: try (disc_RootChnInv;
                derive_footprint_info_basis oidx;
                [disc_MesiDownLockInv oidx Hmftinv|];
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

      END_SKIP_PROOF_ON *) admit.
  Qed.

  Theorem mesi_RootChnInv_ok:
    InvReachable impl step_m (RootChnInv tr 0).
  Proof.
    eapply inv_reachable.
    - typeclasses eauto.
    - apply mesi_RootChnInv_init.
    - apply mesi_RootChnInv_step.
  Qed.

End RootChnInv.
