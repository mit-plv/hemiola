Require Import Peano_dec Omega List ListSupport.
Require Import Common FMap.
Require Import Syntax Semantics SemFacts StepM Invariant Serial SerialFacts.
Require Import Reduction Commutativity QuasiSeq Topology.
Require Import RqRsTopo RqRsFacts RqRsInvAtomic.

Set Implicit Arguments.

Open Scope list.
Open Scope fmap.

Definition OstPred oifc := IdxT -> OState oifc -> Prop.
Definition OssPred oifc := OStates oifc -> Prop.

Definition OStatesEquivR (oinds: list IdxT) {oifc} (oss1 oss2: OStates oifc) :=
  forall oidx,
    In oidx oinds ->
    oss1@[oidx] = oss2@[oidx].

Definition OStatesEquivC (oinds: list IdxT) {oifc} (oss1 oss2: OStates oifc) :=
  forall oidx,
    ~ In oidx oinds ->
    oss1@[oidx] = oss2@[oidx].

Definition OssPredR {oifc} (oinds: list IdxT) (P: OssPred oifc) :=
  forall oss1 oss2,
    P oss1 ->
    OStatesEquivR oinds oss1 oss2 ->
    P oss2.

Definition OssPredC {oifc} (oinds: list IdxT) (P: OssPred oifc) :=
  forall oss1 oss2,
    P oss1 ->
    OStatesEquivC oinds oss1 oss2 ->
    P oss2.

Definition MsgOutPred oifc := Id Msg -> OssPred oifc.

Lemma OStatesEquivR_add:
  forall {oifc} oinds (oss: OStates oifc) oidx nost,
    ~ In oidx oinds ->
    OStatesEquivR oinds oss (oss +[oidx <- nost]).
Proof.
  intros; red; intros; mred.
Qed.

Section PredLock.
  Context {oifc: OStateIfc}.
  Variables (dtr: DTree)
            (sys: System oifc).
  Hypothesis (Hrrs: RqRsSys dtr sys).

  Lemma extAtomic_rsUp_acceptor_visited:
    forall inits hst eouts,
      ExtAtomic sys msg_dec inits hst eouts ->
      forall s1 s2,
        Reachable (steps step_m) sys s1 ->
        steps step_m sys s1 hst s2 ->
        forall cidx rsUp pidx,
          In rsUp eouts ->
          RsUpMsgFrom dtr cidx rsUp ->
          parentIdxOf dtr cidx = Some pidx ->
          In pidx (oindsOf hst).
  Proof.
  Admitted.

  Lemma extAtomic_rsDown_acceptor_visited:
    forall inits hst eouts,
      ExtAtomic sys msg_dec inits hst eouts ->
      forall s1 s2,
        Reachable (steps step_m) sys s1 ->
        steps step_m sys s1 hst s2 ->
        forall oidx rsDown,
          In rsDown eouts ->
          RsDownMsgTo dtr oidx rsDown ->
          In oidx (oindsOf hst).
  Proof.
  Admitted.

End PredLock.

Section PredMsg.
  Context {oifc: OStateIfc}.
  Variables (dtr: DTree)
            (sys: System oifc).
  Hypothesis (Hrrs: RqRsSys dtr sys).

  Definition GoodRsUpPred (rsUp: Id Msg) (P: OssPred oifc) :=
    forall oidx,
      RsUpMsgFrom dtr oidx rsUp ->
      OssPredR (subtreeIndsOf dtr oidx) P.

  Definition GoodRsDownPred (rsDown: Id Msg) (P: OssPred oifc) :=
    forall oidx,
      RsDownMsgTo dtr oidx rsDown ->
      OssPredC (subtreeIndsOf dtr oidx) P.

  Definition GoodRqPred (rq: Id Msg) (P: OssPred oifc) :=
    forall oidx,
      (RqUpMsgFrom dtr oidx rq \/ RqDownMsgTo dtr oidx rq) ->
      forall oss, P oss.

  Definition GoodMsgOutPred (P: MsgOutPred oifc) :=
    forall eout: Id Msg,
      GoodRsUpPred eout (P eout) /\
      GoodRsDownPred eout (P eout) /\
      GoodRqPred eout (P eout).

  Section Facts.

    Lemma rqDown_preserves_msg_out_preds:
      forall eouts,
        RqDownRsUpDisj dtr eouts ->
        Forall (fun eout =>
                  exists oidx, RqDownRsUpIdx dtr oidx eout) eouts ->
        forall oidx rqDown,
          In rqDown eouts ->
          RqDownMsgTo dtr oidx rqDown ->
          forall P oss nost,
            GoodMsgOutPred P ->
            Forall (fun eout => P eout oss) eouts ->
            Forall (fun eout => P eout (oss +[oidx <- nost])) eouts.
    Proof.
      destruct Hrrs as [? [? ?]]; intros.
      apply Forall_forall; intros [midx msg] ?.
      specialize (H6 (midx, msg)); dest.
      rewrite Forall_forall in H7; specialize (H7 _ H8).
      rewrite Forall_forall in H3.
      pose proof (H3 _ H8).
      destruct H11 as [cidx ?].
      destruct H11; [eapply H10; eauto|].

      specialize (H6 _ H11).
      eapply H6; [eassumption|].
      apply OStatesEquivR_add.

      eapply rqDownRsUpDisj_in_spec
        with (eout1:= rqDown) (eout2:= (midx, msg)); eauto.
      - intro Hx; subst.
        destruct H5, H11.
        disc_rule_conds.
      - left; assumption.
      - right; assumption.
    Qed.

    Corollary atomic_rqDown_preserves_msg_out_preds:
      forall inits ins hst outs eouts,
        Atomic msg_dec inits ins hst outs eouts ->
        forall s1 s2,
          Reachable (steps step_m) sys s1 ->
          steps step_m sys s1 hst s2 ->
          forall oidx rqDown,
            In rqDown eouts ->
            RqDownMsgTo dtr oidx rqDown ->
            forall P oss nost,
              GoodMsgOutPred P ->
              Forall (fun eout => P eout oss) eouts ->
              Forall (fun eout => P eout (oss +[oidx <- nost])) eouts.
    Proof.
      destruct Hrrs as [? [? ?]]; intros.
      eapply atomic_msg_outs_ok in H2; eauto.
      inv H2.
      - exfalso; dest_in.
        destruct H6, H9.
        solve_midx_false.
      - exfalso; dest_in.
        destruct H6, H9.
        disc_rule_conds.
      - eapply rqDown_preserves_msg_out_preds; eauto.
        eapply rqDown_rsUp_inv_msg; eauto.
    Qed.

    Lemma rsUps_preserves_msg_out_preds:
      forall eouts,
        RqDownRsUpDisj dtr eouts ->
        Forall (fun eout =>
                  exists oidx, RqDownRsUpIdx dtr oidx eout) eouts ->
        forall oidx rqTos rsUps Rp,
          SubList rsUps eouts ->
          RqRsDownMatch dtr oidx rqTos (idsOf rsUps) Rp ->
          forall P oss nost,
            GoodMsgOutPred P ->
            Forall (fun eout => P eout oss) eouts ->
            Forall (fun eout => P eout (oss +[oidx <- nost])) eouts.
    Proof.
      destruct Hrrs as [? [? ?]]; intros.
      apply Forall_forall; intros [midx msg] ?.
      specialize (H6 (midx, msg)); dest.
      rewrite Forall_forall in H7; specialize (H7 _ H8).
      rewrite Forall_forall in H3.
      pose proof (H3 _ H8).
      destruct H11 as [cidx ?].
      destruct H11; [eapply H10; eauto|].

      specialize (H6 _ H11).
      eapply H6; [eassumption|].
      apply OStatesEquivR_add.

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
          specialize (H3 _ H12).
          destruct H3 as [rcidx0 ?].
          destruct H3; [destruct H3; exfalso; solve_midx_false|].
          destruct H3; disc_rule_conds.
          exists rcidx, rsUp.
          repeat ssplit; auto.
          red; auto.
        }
      }
      destruct H12 as [rcidx [rsUp ?]]; dest.

      destruct (id_dec msg_dec rsUp (midx, msg)); subst.
      - destruct H11, H14; simpl in *.
        disc_rule_conds.
        eapply parent_not_in_subtree; [apply Hrrs|assumption].
      - eapply outside_parent_out; [apply Hrrs| |eassumption].
        eapply rqDownRsUpDisj_in_spec
          with (oidx1:= rcidx) (oidx2:= cidx) in n; eauto;
          try (red; right; red; eauto).
    Qed.

    Corollary atomic_rsUps_preserves_msg_out_preds:
      forall inits ins hst outs eouts,
        Atomic msg_dec inits ins hst outs eouts ->
        forall s1 s2,
          Reachable (steps step_m) sys s1 ->
          steps step_m sys s1 hst s2 ->
          forall oidx rqTos rsUps Rp,
            NoDup (idsOf rsUps) ->
            SubList rsUps eouts ->
            RqRsDownMatch dtr oidx rqTos (idsOf rsUps) Rp ->
            forall P oss nost,
              GoodMsgOutPred P ->
              Forall (fun eout => P eout oss) eouts ->
              Forall (fun eout => P eout (oss +[oidx <- nost])) eouts.
    Proof.
      destruct Hrrs as [? [? ?]]; intros.
      eapply atomic_msg_outs_ok in H2; eauto.
      inv H2.
      - exfalso; destruct rqUp as [rqUp rqm].
        apply SubList_singleton_NoDup in H6; [|apply idsOf_NoDup; assumption].
        destruct H6; subst;
          [red in H7; dest; destruct rqTos; [auto|discriminate]|].
        eapply RqRsDownMatch_rs_rq in H7; [|left; reflexivity].
        destruct H7 as [cidx [down ?]]; dest.
        destruct H10.
        simpl in *; solve_midx_false.
      - exfalso; destruct rsDown as [rsDown rsm].
        apply SubList_singleton_NoDup in H6; [|apply idsOf_NoDup; assumption].
        destruct H6; subst;
          [red in H7; dest; destruct rqTos; [auto|discriminate]|].
        eapply RqRsDownMatch_rs_rq in H7; [|left; reflexivity].
        destruct H7 as [cidx [down ?]]; dest.
        destruct H10.
        simpl in *; solve_midx_false.
      - eapply rsUps_preserves_msg_out_preds; eauto.
        eapply rqDown_rsUp_inv_msg; eauto.
    Qed.

  End Facts.
  
End PredMsg.

Close Scope list.
Close Scope fmap.

