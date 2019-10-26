Require Import Peano_dec Omega List.
Require Import Common FMap IndexSupport.
Require Import Syntax Semantics SemFacts StepM Invariant Serial SerialFacts.
Require Import Reduction Commutativity QuasiSeq Topology.
Require Import RqRsTopo RqRsFacts RqRsInvLock RqRsInvAtomic.

Set Implicit Arguments.

Open Scope list.
Open Scope fmap.

Definition StatesPred `{OStateIfc} :=
  OStates -> ORqs Msg -> MessagePool Msg -> Prop.
Definition MsgOutPred `{OStateIfc} := Id Msg -> StatesPred.

Section PerOStateIfc.
  Context `{oifc: OStateIfc}.
  Variable (dtr: DTree).

  Definition MsgsEquiv (oidx: IdxT)
             (msgs1 msgs2: MessagePool Msg): Prop :=
    (forall rqUp,
        rqEdgeUpFrom dtr oidx = Some rqUp -> findQ rqUp msgs1 = findQ rqUp msgs2) /\
    (forall rsUp,
        rsEdgeUpFrom dtr oidx = Some rsUp -> findQ rsUp msgs1 = findQ rsUp msgs2) /\
    (forall down,
        edgeDownTo dtr oidx = Some down -> findQ down msgs1 = findQ down msgs2).
  
  Definition StatesEquivR (oinds: list IdxT)
             (oss1: OStates) (orqs1: ORqs Msg) (msgs1: MessagePool Msg)
             (oss2: OStates) (orqs2: ORqs Msg) (msgs2: MessagePool Msg): Prop :=
    forall oidx,
      In oidx oinds ->
      oss1@[oidx] = oss2@[oidx] /\
      orqs1@[oidx] = orqs2@[oidx] /\
      MsgsEquiv oidx msgs1 msgs2.

  Definition StatesEquivC (oinds: list IdxT)
             (oss1: OStates) (orqs1: ORqs Msg) (msgs1: MessagePool Msg)
             (oss2: OStates) (orqs2: ORqs Msg) (msgs2: MessagePool Msg): Prop :=
    forall oidx,
      ~ In oidx oinds ->
      oss1@[oidx] = oss2@[oidx] /\
      orqs1@[oidx] = orqs2@[oidx] /\
      MsgsEquiv oidx msgs1 msgs2.

  Definition StatesPredR (oinds: list IdxT) (P: StatesPred) :=
    forall oss1 orqs1 msgs1 oss2 orqs2 msgs2,
      P oss1 orqs1 msgs1 ->
      StatesEquivR oinds oss1 orqs1 msgs1 oss2 orqs2 msgs2 ->
      P oss2 orqs2 msgs2.

  Definition StatesPredC (oinds: list IdxT) (P: StatesPred) :=
    forall oss1 orqs1 msgs1 oss2 orqs2 msgs2,
      P oss1 orqs1 msgs1 ->
      StatesEquivC oinds oss1 orqs1 msgs1 oss2 orqs2 msgs2 ->
      P oss2 orqs2 msgs2.

End PerOStateIfc.

Definition DisjMInds (dtr: DTree) (oinds: list IdxT) (minds: list IdxT): Prop :=
  forall oidx,
    In oidx oinds ->
    (forall rqUp, rqEdgeUpFrom dtr oidx = Some rqUp -> ~ In rqUp minds) /\
    (forall rsUp, rsEdgeUpFrom dtr oidx = Some rsUp -> ~ In rsUp minds) /\
    (forall down, edgeDownTo dtr oidx = Some down -> ~ In down minds).

Lemma OStatesEquivR_add:
  forall `{oifc: OStateIfc} dtr oinds (oss: OStates) orqs msgs oidx nost norq nmsgs rminds,
    ~ In oidx oinds ->
    DisjMInds dtr oinds (idsOf nmsgs) ->
    DisjMInds dtr oinds rminds ->
      StatesEquivR
        dtr oinds oss orqs msgs
        (oss +[oidx <- nost]) (orqs +[oidx <- norq])
        (enqMsgs nmsgs (deqMsgs rminds msgs)).
Proof.
  intros; red; intros.
  repeat ssplit; [mred..|].
  red; repeat ssplit.
  - intros.
    specialize (H0 _ H2); specialize (H1 _ H2); dest.
    specialize (H0 _ H3); specialize (H1 _ H3).
    rewrite findQ_not_In_enqMsgs by assumption.
    rewrite findQ_not_In_deqMsgs by assumption.
    reflexivity.
  - intros.
    specialize (H0 _ H2); specialize (H1 _ H2); dest.
    specialize (H6 _ H3); specialize (H4 _ H3).
    rewrite findQ_not_In_enqMsgs by assumption.
    rewrite findQ_not_In_deqMsgs by assumption.
    reflexivity.
  - intros.
    specialize (H0 _ H2); specialize (H1 _ H2); dest.
    specialize (H7 _ H3); specialize (H5 _ H3).
    rewrite findQ_not_In_enqMsgs by assumption.
    rewrite findQ_not_In_deqMsgs by assumption.
    reflexivity.
Qed.

Section PredMsg.
  Context `{oifc: OStateIfc}.
  Variables (dtr: DTree)
            (sys: System).
  Hypotheses (Hiorqs: GoodORqsInit (initsOf sys))
             (Hrrs: RqRsSys dtr sys).

  Definition GoodRqDownPred (rqDown: Id Msg) (P: StatesPred) :=
    forall oidx,
      RqDownMsgTo dtr oidx rqDown ->
      forall pidx,
        parentIdxOf dtr oidx = Some pidx ->
        StatesPredR dtr [pidx] P.

  Definition GoodRsUpPred (rsUp: Id Msg) (P: StatesPred) :=
    forall oidx,
      RsUpMsgFrom dtr oidx rsUp ->
      StatesPredR dtr (subtreeIndsOf dtr oidx) P.

  Definition GoodMsgOutPred (P: MsgOutPred) :=
    forall eout: Id Msg,
      GoodRqDownPred eout (P eout) /\
      GoodRsUpPred eout (P eout).

  Section Facts.

    Ltac disc_rule_custom ::=
      try disc_msg_case.

    Lemma atomic_rqUp_singleton:
      forall inits ins hst outs eouts,
        Atomic msg_dec inits ins hst outs eouts ->
        forall s1 s2,
          Reachable (steps step_m) sys s1 ->
          steps step_m sys s1 hst s2 ->
          forall oidx rqUp,
            In rqUp eouts ->
            RqUpMsgFrom dtr oidx rqUp ->
            eouts = [rqUp].
    Proof.
      destruct Hrrs as [? [? ?]]; intros.
      eapply atomic_msg_outs_ok in H2; eauto.
      inv H2.
      - dest_in; reflexivity.
      - dest_in; reflexivity.
      - dest_in; reflexivity.
      - exfalso.
        eapply rqDown_rsUp_inv_msg in H8.
        rewrite Forall_forall in H8; specialize (H8 _ H5).
        destruct H8 as [roidx ?].
        destruct H2.
        + disc_rule_conds; solve_midx_false.
        + disc_rule_conds.
    Qed.

    Lemma atomic_rsDown_singleton:
      forall inits ins hst outs eouts,
        Atomic msg_dec inits ins hst outs eouts ->
        forall s1 s2,
          Reachable (steps step_m) sys s1 ->
          steps step_m sys s1 hst s2 ->
          forall oidx rsDown,
            In rsDown eouts ->
            RsDownMsgTo dtr oidx rsDown ->
            eouts = [rsDown].
    Proof.
      destruct Hrrs as [? [? ?]]; intros.
      eapply atomic_msg_outs_ok in H2; eauto.
      inv H2.
      - dest_in; reflexivity.
      - dest_in; reflexivity.
      - dest_in; reflexivity.
      - exfalso.
        eapply rqDown_rsUp_inv_msg in H8.
        rewrite Forall_forall in H8; specialize (H8 _ H5).
        destruct H8 as [roidx ?].
        destruct H2.
        + disc_rule_conds.
        + disc_rule_conds; solve_midx_false.
    Qed.

    Lemma rsUps_preserves_msg_out_preds:
      forall eouts,
        RqDownRsUpDisj dtr eouts ->
        Forall (fun eout =>
                  exists oidx, RqDownRsUpIdx dtr oidx eout) eouts ->
        forall oidx rqTos rsUps Rp,
          SubList rsUps eouts ->
          RqRsDownMatch dtr oidx rqTos (idsOf rsUps) Rp ->
          (* No RqUp messages in the subtree for the RsUp messages *)
          Forall (fun eout =>
                    forall cidx,
                      RqDownMsgTo dtr cidx eout ->
                      parentIdxOf dtr cidx <> Some oidx) eouts ->
          forall P oss orqs msgs nost norq orsUp rsum,
            GoodMsgOutPred P ->
            Forall (fun eout => P eout oss orqs msgs) eouts ->
            rsEdgeUpFrom dtr oidx = Some orsUp ->
            Forall (fun eout => P eout (oss +[oidx <- nost])
                                  (orqs +[oidx <- norq])
                                  (enqMP orsUp rsum (deqMsgs (idsOf rsUps) msgs)))
                   (removeL (id_dec msg_dec) eouts rsUps).
    Proof.
      destruct Hrrs as [? [? ?]]; intros.
      apply Forall_forall; intros [midx msg] ?.
      apply removeL_In_NoDup in H10;
        [|apply idsOf_NoDup; eapply rqDownRsUpDisj_NoDup; eauto].
      dest.
      specialize (H7 (midx, msg)); dest.
      rewrite Forall_forall in H8; specialize (H8 _ H11).
      rewrite Forall_forall in H3; pose proof (H3 _ H11).
      destruct H13 as [cidx ?].
      destruct H13.

      - specialize (H7 _ H13).
        rewrite Forall_forall in H6; specialize (H6 _ H11 _ H13).
        red in H13; simpl in *; dest.
        pose proof (edgeDownTo_Some H _ H14).
        destruct H15 as [rqUp [rsUp [pidx ?]]]; dest.
        specialize (H7 _ H17).
        eapply H7; [eassumption|].
        apply OStatesEquivR_add with (nmsgs:= [(orsUp, rsum)]).
        + intro Hx; dest_in; auto.

        + simpl; red; intros; dest_in.
          repeat ssplit.
          * intros; intro Hx; dest_in; solve_midx_false.
          * intros; intro Hx; dest_in; disc_rule_conds.
          * intros; intro Hx; dest_in; solve_midx_false.

        + red; intros; dest_in.
          rename oidx0 into pidx.
          repeat ssplit.
          * intros; intro Hx.
            eapply RqRsDownMatch_rs_rq in H5; [|eassumption].
            destruct H5 as [rcidx [rdown ?]]; dest.
            solve_midx_false.
          * intros; intro Hx.
            apply in_map_iff in Hx; destruct Hx as [[rrsUp rrsum] [? ?]].
            simpl in *; subst.
            pose proof (H3 _ (H4 _ H20)).
            destruct H19 as [rpidx ?]; destruct H19;
              [destruct H19; simpl in *; solve_midx_false|].
            destruct H19; simpl in *.
            disc_rule_conds.
            eapply rqDownRsUpDisj_in_spec
              with (eout1:= (midx, msg)) (eout2:= (rsUp0, rrsum)); eauto.
            { intro Hx; inv Hx; solve_midx_false. }
            { left; red; eauto. }
            { right; red; eauto. }
            { apply subtreeIndsOf_child_in; auto; apply Hrrs. }
            
          * intros; intro Hx.
            eapply RqRsDownMatch_rs_rq in H5; [|eassumption].
            destruct H5 as [rcidx [rdown ?]]; dest.
            solve_midx_false.

      - specialize (H12 _ H13).
        eapply H12; [eassumption|].

        assert (exists rcidx rsUp,
                   parentIdxOf dtr rcidx = Some oidx /\
                   In rsUp rsUps /\
                   RsUpMsgFrom dtr rcidx rsUp).
        { destruct rsUps as [|rsUp rsUps].
          { exfalso; red in H5; dest.
            destruct rqTos; [|discriminate]; auto.
          }
          { pose proof (H4 _ (or_introl eq_refl)).
            eapply RqRsDownMatch_rs_rq in H5; [|left; reflexivity].
            destruct H5 as [rcidx [down ?]]; dest.
            specialize (H3 _ H14).
            destruct H3 as [rcidx0 ?].
            destruct H3; [destruct H3; exfalso; solve_midx_false|].
            destruct H3; disc_rule_conds.
            exists rcidx, rsUp.
            repeat ssplit; auto.
            red; auto.
          }
        }
        destruct H14 as [rcidx [rsUp ?]]; dest.

        apply OStatesEquivR_add with (nmsgs:= [(orsUp, rsum)]).
        + destruct (id_dec msg_dec rsUp (midx, msg)); subst.
          * disc_rule_conds.
            eapply parent_not_in_subtree; [apply Hrrs|assumption].
          * eapply outside_parent_out; [apply Hrrs| |eassumption].
            eapply rqDownRsUpDisj_in_spec
              with (oidx1:= rcidx) (oidx2:= cidx) in n; eauto;
              try (right; red; eauto).

        + simpl; red; intros.
          repeat ssplit.
          * intros; intro Hx; dest_in; solve_midx_false.
          * intros; intro Hx; dest_in; disc_rule_conds.
            eapply rqDownRsUpDisj_in_spec
              with (eout1:= rsUp) (eout2:= (midx, msg)) (oidx1:= rcidx) (oidx2:= cidx); eauto.
            { intro Hx; subst; simpl in *; disc_rule_conds.
              eapply parent_not_in_subtree with (oidx:= rcidx) (pidx:= oidx0); eauto.
              apply Hrrs.
            }
            { right; red; eauto. }
            { right; red; eauto. }
            { eapply inside_child_in; eauto; apply Hrrs. }
          * intros; intro Hx; dest_in; solve_midx_false.

        + red; intros.
          repeat ssplit.
          * intros; intro Hx.
            eapply RqRsDownMatch_rs_rq in H5; [|eassumption].
            destruct H5 as [fcidx [fdown ?]]; dest.
            solve_midx_false.

          * intros; intro Hx.
            apply in_map_iff in Hx; destruct Hx as [[rrsUp rrsum] [? ?]].
            simpl in *; subst.
            pose proof (H3 _ (H4 _ H20)).
            destruct H19 as [roidx ?]; destruct H19;
              [destruct H19; simpl in *; solve_midx_false|].
            destruct H19; simpl in *.
            disc_rule_conds.
            eapply rqDownRsUpDisj_in_spec
              with (eout1:= (rsUp0, rrsum)) (eout2:= (midx, msg))
                   (oidx1:= roidx) (oidx2:= cidx); eauto.
            { intro Hx; inv Hx; auto. }
            { right; red; eauto. }
            { right; red; eauto. }
            
          * intros; intro Hx.
            eapply RqRsDownMatch_rs_rq in H5; [|eassumption].
            destruct H5 as [fcidx [fdown ?]]; dest.
            solve_midx_false.

    Qed.

    Corollary atomic_rsUps_preserves_msg_out_preds:
      forall inits ins hst outs eouts,
        Atomic msg_dec inits ins hst outs eouts ->
        forall s1 s2,
          Reachable (steps step_m) sys s1 ->
          steps step_m sys s1 hst s2 ->
          forall obj oidx rqTos rsUps Rp,
            In obj (sys_objs sys) ->
            obj.(obj_idx) = oidx ->
            NoDup (idsOf rsUps) ->
            SubList rsUps eouts ->
            RqRsDownMatch dtr oidx rqTos (idsOf rsUps) Rp ->
            forall orq rqid,
              s2.(bst_orqs)@[oidx] = Some orq ->
              orq@[downRq] = Some rqid ->
              rqid.(rqi_minds_rss) = idsOf rsUps ->
              forall P oss orqs msgs nost norq orsUp rsum,
                GoodMsgOutPred P ->
                Forall (fun eout => P eout oss orqs msgs) eouts ->
                rsEdgeUpFrom dtr oidx = Some orsUp ->
                Forall (fun eout => P eout (oss +[oidx <- nost])
                                      (orqs +[oidx <- norq])
                                      (enqMP orsUp rsum (deqMsgs (idsOf rsUps) msgs)))
                       (removeL (id_dec msg_dec) eouts rsUps).
    Proof.
      destruct Hrrs as [? [? [? ?]]]; intros.
      pose proof H3.
      eapply atomic_msg_outs_ok in H17; eauto.
      inv H17.
      - apply SubList_nil_inv in H9; subst; constructor.
      - exfalso; destruct rqUp as [rqUp rqm].
        apply SubList_singleton_NoDup in H9; [|apply idsOf_NoDup; assumption].
        destruct H9; subst;
          [red in H10; dest; destruct rqTos; [auto|discriminate]|].
        eapply RqRsDownMatch_rs_rq in H10; [|left; reflexivity].
        destruct H10 as [cidx [down ?]]; dest.
        destruct H18.
        simpl in *; solve_midx_false.
      - exfalso; destruct rsDown as [rsDown rsm].
        apply SubList_singleton_NoDup in H9; [|apply idsOf_NoDup; assumption].
        destruct H9; subst;
          [red in H10; dest; destruct rqTos; [auto|discriminate]|].
        eapply RqRsDownMatch_rs_rq in H10; [|left; reflexivity].
        destruct H10 as [cidx [down ?]]; dest.
        destruct H18.
        simpl in *; solve_midx_false.
      - eapply rsUps_preserves_msg_out_preds; eauto.
        + eapply rqDown_rsUp_inv_msg; eauto.
        + apply Forall_forall.
          intros [rqDown rqdm]; intros.
          intro Hx.

          (* The proof idea: if such a RqDown message exists, then the 
           * corresponding RsUp channel should exist and belong to
           * [rqid.(rqi_minds_rss)]. We also know every RsUp channel is ready,
           * i.e., there exists an RsUp message. The existence of RqDown and 
           * RsUp messages contradicts the fact that they cannot exist at the
           * same time.
           *)
          destruct H17; simpl in *.
          pose proof (edgeDownTo_Some H _ H22).
          destruct H23 as [rqUp [rsUp [pidx ?]]]; dest.
          disc_rule_conds.
          pose proof (downLockInv_ok Hiorqs H0 H H2 (reachable_steps H4 H5)).
          good_locking_get obj.

          assert (length (rqsQ (bst_msgs s2) rqDown) >= 1).
          { eapply rqsQ_length_ge_one; eauto.
            eapply atomic_messages_eouts_in in H3; [|eassumption].
            rewrite Forall_forall in H3.
            specialize (H3 _ H7); assumption.
          }

          pose proof H26.
          eapply downLockInvORq_down_rqsQ_length_one_locked in H26; eauto.
          destruct H26 as [rrqid ?]; dest.
          disc_rule_conds.
          eapply downLockInvORq_down_rqsQ_rsUp_False in H27; eauto.
          apply in_map_iff with (f:= idOf) in H31.
          destruct H31 as [[rsUp rrsum] [? ?]].
          simpl in *; subst.
          apply H9 in H30.
          eapply atomic_messages_eouts_in in H3; [|eassumption].
          rewrite Forall_forall in H3.
          specialize (H3 _ H30).
          eapply findQ_length_ge_one; eauto.
    Qed.

  End Facts.
  
End PredMsg.

Ltac disc_GoodMsgOutPred :=
  repeat
    match goal with
    | [H: sigOf ?eout = (_, (_, _)) |- _] =>
      let midx := fresh "midx" in
      let msg := fresh "msg" in
      destruct eout as [midx msg]; inv H

    | [H: RsUpMsgFrom _ _ (_, _) |- _] =>
      let H1 := fresh "H" in
      let H2 := fresh "H" in
      destruct H as [H1 H2]; simpl in H1, H2
    | [H: RsDownMsgTo _ _ (_, _) |- _] =>
      let H1 := fresh "H" in
      let H2 := fresh "H" in
      destruct H as [H1 H2]; simpl in H1, H2
    | [H: RqUpMsgFrom _ _ (_, _) |- _] =>
      let H1 := fresh "H" in
      let H2 := fresh "H" in
      destruct H as [H1 H2]; simpl in H1, H2
    | [H: RqDownMsgTo _ _ (_, _) |- _] =>
      let H1 := fresh "H" in
      let H2 := fresh "H" in
      destruct H as [H1 H2]; simpl in H1, H2

    | [H: ~ In ?midx (sys_merqs _) |- _] =>
      elim H; simpl; tauto
    | [H1: msg_type ?msg = MRq, H2: msg_type ?msg = MRs |- _] =>
      rewrite H1 in H2; discriminate
    | [H: rsEdgeUpFrom _ ?oidx = Some ?rsUp |- _] =>
      is_var oidx;
      is_const rsUp;
      pose proof (rsEdgeUpFrom_indsOf _ _ H);
      dest_in; try discriminate
    | [H: edgeDownTo _ ?oidx = Some ?down |- _] =>
      is_var oidx;
      is_const down;
      pose proof (edgeDownTo_indsOf _ _ H);
      dest_in; try discriminate
    | [H: parentIdxOf _ ?oidx = Some ?pidx |- _] => progress simpl in H
    | [H: parentIdxOf _ ?oidx = Some ?pidx |- _] =>
      is_const oidx; is_var pidx; inv H
    end.

Close Scope list.
Close Scope fmap.

