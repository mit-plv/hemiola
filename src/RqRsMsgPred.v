Require Import Peano_dec Omega List ListSupport.
Require Import Common FMap.
Require Import Syntax Semantics SemFacts StepM Invariant Serial SerialFacts.
Require Import Reduction Commutativity QuasiSeq Topology.
Require Import RqRsTopo RqRsFacts RqRsInvAtomic.

Set Implicit Arguments.

Open Scope list.
Open Scope fmap.

Definition StatesPred oifc := OStates oifc -> ORqs Msg -> Prop.
Definition MsgOutPred oifc := Id Msg -> StatesPred oifc.

Section PerOStateIfc.
  Context {oifc: OStateIfc}.
  
  Definition StatesEquivR (oinds: list IdxT)
             (oss1: OStates oifc) (orqs1: ORqs Msg)
             (oss2: OStates oifc) (orqs2: ORqs Msg): Prop :=
    forall oidx,
      In oidx oinds ->
      oss1@[oidx] = oss2@[oidx] /\
      orqs1@[oidx] = orqs2@[oidx].

  Definition StatesEquivC (oinds: list IdxT)
             (oss1: OStates oifc) (orqs1: ORqs Msg)
             (oss2: OStates oifc) (orqs2: ORqs Msg) :=
    forall oidx,
      ~ In oidx oinds ->
      oss1@[oidx] = oss2@[oidx] /\
      orqs1@[oidx] = orqs2@[oidx].

  Definition StatesPredR (oinds: list IdxT) (P: StatesPred oifc) :=
    forall oss1 orqs1 oss2 orqs2,
      P oss1 orqs1 ->
      StatesEquivR oinds oss1 orqs1 oss2 orqs2 ->
      P oss2 orqs2.

  Definition StatesPredC (oinds: list IdxT) (P: StatesPred oifc) :=
    forall oss1 orqs1 oss2 orqs2,
      P oss1 orqs1 ->
      StatesEquivC oinds oss1 orqs1 oss2 orqs2 ->
      P oss2 orqs2.

End PerOStateIfc.

Lemma OStatesEquivR_add:
  forall {oifc} oinds (oss: OStates oifc) orqs oidx nost norq,
    ~ In oidx oinds ->
    StatesEquivR oinds oss orqs (oss +[oidx <- nost]) (orqs +[oidx <- norq]).
Proof.
  intros; red; intros; mred.
Qed.

Section PredLock.
  Context {oifc: OStateIfc}.
  Variables (dtr: DTree)
            (sys: System oifc).
  Hypotheses (Hiorqs: GoodORqsInit (initsOf sys))
             (Hrrs: RqRsSys dtr sys).

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
  Hypotheses (Hiorqs: GoodORqsInit (initsOf sys))
             (Hrrs: RqRsSys dtr sys).

  Definition GoodRsUpPred (rsUp: Id Msg) (P: StatesPred oifc) :=
    forall oidx,
      RsUpMsgFrom dtr oidx rsUp ->
      StatesPredR (subtreeIndsOf dtr oidx) P.

  Definition GoodRsDownPred (rsDown: Id Msg) (P: StatesPred oifc) :=
    forall oidx,
      RsDownMsgTo dtr oidx rsDown ->
      StatesPredC (subtreeIndsOf dtr oidx) P.

  Definition GoodRqUpPred (rqUp: Id Msg) (P: StatesPred oifc) :=
    forall oidx,
      RqUpMsgFrom dtr oidx rqUp ->
      (In (idOf rqUp) sys.(sys_merqs) \/
       forall oss orqs, P oss orqs).

  Definition GoodRqDownPred (rqDown: Id Msg) (P: StatesPred oifc) :=
    forall oidx,
      RqDownMsgTo dtr oidx rqDown ->
      forall oss orqs, P oss orqs.

  Definition GoodMsgOutPred (P: MsgOutPred oifc) :=
    forall eout: Id Msg,
      GoodRsUpPred eout (P eout) /\
      GoodRsDownPred eout (P eout) /\
      GoodRqUpPred eout (P eout) /\
      GoodRqDownPred eout (P eout).

  Section Facts.

    Ltac disc_rule_custom ::=
      try disc_msg_case.

    Lemma atomic_rqUp_preserves_msg_out_preds:
      forall inits ins hst outs eouts,
        Atomic msg_dec inits ins hst outs eouts ->
        forall s1 s2,
          Reachable (steps step_m) sys s1 ->
          steps step_m sys s1 hst s2 ->
          forall oidx rqUp pidx,
            In rqUp eouts ->
            ~ In (idOf rqUp) sys.(sys_merqs) ->
            RqUpMsgFrom dtr oidx rqUp ->
            parentIdxOf dtr oidx = Some pidx ->
            forall P oss orqs nost norq,
              GoodMsgOutPred P ->
              Forall (fun eout => P eout oss orqs) eouts ->
              Forall (fun eout => P eout (oss +[pidx <- nost]) (orqs +[pidx <- norq])) eouts.
    Proof.
      destruct Hrrs as [? [? ?]]; intros.
      eapply atomic_msg_outs_ok in H2; eauto.
      inv H2.
      - dest_in.
        repeat constructor.
        specialize (H9 rqUp); dest.
        specialize (H9 _ H7).
        destruct H9.
        + exfalso; auto.
        + apply H9.
      - exfalso; dest_in.
        disc_rule_conds.
      - exfalso.
        eapply rqDown_rsUp_inv_msg in H12.
        rewrite Forall_forall in H12; specialize (H12 _ H5).
        destruct H12 as [roidx ?].
        destruct H2.
        + disc_rule_conds; solve_midx_false.
        + disc_rule_conds.
    Qed.

    Lemma rqDown_preserves_msg_out_preds:
      forall eouts,
        RqDownRsUpDisj dtr eouts ->
        Forall (fun eout =>
                  exists oidx, RqDownRsUpIdx dtr oidx eout) eouts ->
        forall oidx rqDown,
          In rqDown eouts ->
          RqDownMsgTo dtr oidx rqDown ->
          forall P oss orqs nost norq,
            GoodMsgOutPred P ->
            Forall (fun eout => P eout oss orqs) eouts ->
            Forall (fun eout => P eout (oss +[oidx <- nost]) (orqs +[oidx <- norq])) eouts.
    Proof.
      destruct Hrrs as [? [? ?]]; intros.
      apply Forall_forall; intros [midx msg] ?.
      specialize (H6 (midx, msg)); dest.
      rewrite Forall_forall in H7; specialize (H7 _ H8).
      rewrite Forall_forall in H3.
      pose proof (H3 _ H8).
      destruct H12 as [cidx ?].
      destruct H12; [eapply H11; eauto|].

      specialize (H6 _ H12).
      eapply H6; [eassumption|].
      apply OStatesEquivR_add.

      eapply rqDownRsUpDisj_in_spec
        with (eout1:= rqDown) (eout2:= (midx, msg)); eauto.
      - intro Hx; subst.
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
            forall P oss orqs nost norq,
              GoodMsgOutPred P ->
              Forall (fun eout => P eout oss orqs) eouts ->
              Forall (fun eout => P eout (oss +[oidx <- nost]) (orqs +[oidx <- norq])) eouts.
    Proof.
      destruct Hrrs as [? [? ?]]; intros.
      eapply atomic_msg_outs_ok in H2; eauto.
      inv H2.
      - exfalso; dest_in.
        disc_rule_conds.
        solve_midx_false.
      - exfalso; dest_in.
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
          forall P oss orqs nost norq,
            GoodMsgOutPred P ->
            Forall (fun eout => P eout oss orqs) eouts ->
            Forall (fun eout => P eout (oss +[oidx <- nost]) (orqs +[oidx <- norq])) eouts.
    Proof.
      destruct Hrrs as [? [? ?]]; intros.
      apply Forall_forall; intros [midx msg] ?.
      specialize (H6 (midx, msg)); dest.
      rewrite Forall_forall in H7; specialize (H7 _ H8).
      rewrite Forall_forall in H3.
      pose proof (H3 _ H8).
      destruct H12 as [cidx ?].
      destruct H12; [eapply H11; eauto|].

      specialize (H6 _ H12).
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
          specialize (H3 _ H13).
          destruct H3 as [rcidx0 ?].
          destruct H3; [destruct H3; exfalso; solve_midx_false|].
          destruct H3; disc_rule_conds.
          exists rcidx, rsUp.
          repeat ssplit; auto.
          red; auto.
        }
      }
      destruct H13 as [rcidx [rsUp ?]]; dest.

      destruct (id_dec msg_dec rsUp (midx, msg)); subst.
      - disc_rule_conds.
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
            forall P oss orqs nost norq,
              GoodMsgOutPred P ->
              Forall (fun eout => P eout oss orqs) eouts ->
              Forall (fun eout => P eout (oss +[oidx <- nost]) (orqs +[oidx <- norq])) eouts.
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

    Lemma atomic_rsDown_preserves_msg_out_preds:
      forall inits ins hst outs eouts,
        Atomic msg_dec inits ins hst outs eouts ->
        forall s1 s2,
          Reachable (steps step_m) sys s1 ->
          steps step_m sys s1 hst s2 ->
          forall oidx rsDown,
            In rsDown eouts ->
            RsDownMsgTo dtr oidx rsDown ->
            forall P oss orqs nost norq,
              GoodMsgOutPred P ->
              Forall (fun eout => P eout oss orqs) eouts ->
              Forall (fun eout => P eout (oss +[oidx <- nost]) (orqs +[oidx <- norq])) eouts.
    Proof.
      destruct Hrrs as [? [? ?]]; intros.
      eapply atomic_msg_outs_ok in H2; eauto.
      inv H2.
      - exfalso; dest_in.
        disc_rule_conds.
      - dest_in.
        specialize (H7 rsDown); dest.
        specialize (H5 _ H6).
        disc_rule_conds.
        repeat constr_rule_conds.
        eapply H5; [eassumption|].
        red; intros; mred.
        elim H9.
        apply edgeDownTo_subtreeIndsOf_self_in; [apply Hrrs|].
        congruence.
      - exfalso.
        apply rqDown_rsUp_inv_msg in H10.
        rewrite Forall_forall in H10; specialize (H10 _ H5).
        destruct H10 as [cidx ?].
        destruct H2.
        + disc_rule_conds.
        + disc_rule_conds; solve_midx_false.
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
    end.

Close Scope list.
Close Scope fmap.

