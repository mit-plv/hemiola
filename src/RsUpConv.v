Require Import Peano_dec Omega List ListSupport.
Require Import Common FMap.
Require Import Syntax Semantics SemFacts StepM Invariant Serial SerialFacts.
Require Import Reduction Commutativity QuasiSeq Topology.
Require Import RqRsTopo RqRsFacts RqRsInvAtomic.

Set Implicit Arguments.

Local Open Scope list.
Local Open Scope fmap.

Section RsUpConv.
  Context {oifc: OStateIfc}.
  Variables (dtr: DTree)
            (sys: System oifc).
  Hypotheses (Hiorqs: GoodORqsInit (initsOf sys))
             (Hrrs: RqRsSys dtr sys).

  Section LockStatus.
    Variables (orqs1 orqs2: ORqs Msg).

    Definition DownLockedNew (oidx: IdxT) :=
      orqs2@[oidx] >>=[False]
           (fun orq2 =>
              orq2@[downRq] <> None /\
              orqs1@[oidx] >>=[True] (fun orq1 => orq1@[downRq] = None)).

    Definition RqDownDLNew (eouts: list (Id Msg)) :=
      forall oidx rqDown pidx,
        RqDownMsgTo dtr oidx rqDown ->
        parentIdxOf dtr oidx = Some pidx ->
        In rqDown eouts ->
        DownLockedNew pidx.

    Definition DLDLNew :=
      forall oidx orq rqid,
        DownLockedNew oidx ->
        orqs2@[oidx] = Some orq -> orq@[downRq] = Some rqid ->
        forall pidx,
          parentIdxOf dtr oidx = Some pidx ->
          rsEdgeUpFrom dtr oidx = Some rqid.(rqi_midx_rsb) ->
          DownLockedNew pidx.

    Definition RsUpDLNew (eouts: list (Id Msg)) :=
      forall oidx rsUp pidx,
        RsUpMsgFrom dtr oidx rsUp ->
        parentIdxOf dtr oidx = Some pidx ->
        In rsUp eouts ->
        DownLockedNew pidx.

    Definition DLNewOuts (eouts: list (Id Msg)) :=
      RqDownDLNew eouts /\ DLDLNew /\ RsUpDLNew eouts.

    Definition DLOldPreserved :=
      forall oidx rqid,
        DownLocked orqs1 oidx rqid ->
        DownLocked orqs2 oidx rqid.

    Definition DLNewInits (inits: list (Id Msg)) :=
      forall oidx idm,
        (RqDownMsgTo dtr oidx idm \/ RsUpMsgFrom dtr oidx idm) ->
        ~ In idm inits.

    Definition DLNewInv (inits eouts: list (Id Msg)) :=
      DLNewInits inits -> DLNewOuts eouts /\ DLOldPreserved.
    
  End LockStatus.

  Hint Unfold DownLockedNew RqDownDLNew DLDLNew RsUpDLNew DLNewOuts
       DLOldPreserved DLNewInits DLNewInv: RuleConds.

  Lemma downLocked_not_DownLockedNew:
    forall orqs1 rqid orqs2 oidx,
      DownLocked orqs1 oidx rqid ->
      ~ DownLockedNew orqs1 orqs2 oidx.
  Proof.
    unfold DownLocked, DownLockedNew; intros.
    intro Hx.
    destruct (orqs1@[oidx]) as [orq1|]; simpl in *; auto.
    destruct (orqs2@[oidx]) as [orq2|]; simpl in *; auto.
    dest; congruence.
  Qed.

  Lemma downLockedNew_DownLocked:
    forall orqs1 orqs2 oidx,
      DownLockedNew orqs1 orqs2 oidx ->
      exists rqid, DownLocked orqs2 oidx rqid.
  Proof.
    unfold DownLocked, DownLockedNew; intros.
    destruct (orqs2@[oidx]) as [orq2|]; simpl in *; [|exfalso; auto].
    dest.
    destruct (orq2@[downRq]); eauto.
    exfalso; auto.
  Qed.

  Ltac disc_rule_custom ::=
    try disc_msg_case.

  Lemma step_rsUp_DownLockedNew:
    forall st1,
      Reachable (steps step_m) sys st1 ->
      forall oidx ridx rins routs st2,
        step_m sys st1 (RlblInt oidx ridx rins routs) st2 ->
        DLNewInv (bst_orqs st1) (bst_orqs st2) rins routs.
  Proof.
  Admitted.

  Lemma atomic_rsUp_DownLockedNew:
    forall inits ins hst outs eouts,
      Atomic msg_dec inits ins hst outs eouts ->
      forall st1 st2,
        Reachable (steps step_m) sys st1 ->
        steps step_m sys st1 hst st2 ->
        DLNewInv st1.(bst_orqs) st2.(bst_orqs) inits eouts.
  Proof.
    destruct Hrrs as [? [? ?]].
    induction 1; simpl; intros; subst;
      [inv_steps; eapply step_rsUp_DownLockedNew; eauto|].
    inv_steps.
    specialize (IHAtomic _ _ H8 H10).

    (* assert (Reachable (steps step_m) sys st2) by eauto. *)
    (* pose proof (footprints_ok Hiorqs H0 H5) as Hftinv. *)
    (* pose proof (downLockInv_ok Hiorqs H0 H H1 H5) as Hdlinv. *)
    (* clear H5. *)
    
    inv_step.
    good_rqrs_rule_get rule.
    good_rqrs_rule_cases rule.

  Admitted.

End RsUpConv.

Section Corollaries.
  Context {oifc: OStateIfc}.
  Variables (dtr: DTree)
            (sys: System oifc).
  Hypotheses (Hiorqs: GoodORqsInit (initsOf sys))
             (Hrrs: RqRsSys dtr sys).

  Lemma extAtomic_DLNewInits:
    forall inits trs eouts,
      ExtAtomic sys msg_dec inits trs eouts ->
      DLNewInits dtr inits.
  Proof.
    destruct Hrrs as [? [? ?]]; intros.
    inv H2.
    red; intros.
    intro Hx.
    apply in_map with (f:= idOf) in Hx.
    apply H3 in Hx.
    apply Hrrs in Hx.
    destruct Hx as [eoidx ?].
    destruct H2.
    - disc_msg_case; solve_midx_false.
    - disc_msg_case; solve_midx_false.
  Qed.

  Corollary extAtomic_rsUp_DownLockedNew:
    forall st1,
      Reachable (steps step_m) sys st1 ->
      forall trs st2,
        steps step_m sys st1 trs st2 ->
        forall inits eouts,
          ExtAtomic sys msg_dec inits trs eouts ->
          forall cidx rsUp pidx,
            RsUpMsgFrom dtr cidx rsUp ->
            parentIdxOf dtr cidx = Some pidx ->
            In rsUp eouts ->
            DownLockedNew st1.(bst_orqs) st2.(bst_orqs) pidx.
  Proof.
    intros.
    pose proof (extAtomic_DLNewInits H1).
    inv H1.
    eapply atomic_rsUp_DownLockedNew in H7; eauto.
    specialize (H7 H5); dest.
    red in H1; dest.
    eapply H9; eauto.
  Qed.

  Corollary extAtomic_rsUp_down_lock_preserved:
    forall st1,
      Reachable (steps step_m) sys st1 ->
      forall trs st2,
        steps step_m sys st1 trs st2 ->
        forall inits eouts,
          ExtAtomic sys msg_dec inits trs eouts ->
          forall oidx rqid,
            DownLocked st1.(bst_orqs) oidx rqid ->
            DownLocked st2.(bst_orqs) oidx rqid.
  Proof.
    intros.
    pose proof (extAtomic_DLNewInits H1).
    inv H1.
    eapply atomic_rsUp_DownLockedNew in H5; eauto.
    specialize (H5 H3); dest.
    apply H5; assumption.
  Qed.

  Lemma extAtomic_multi_rsUps_not_diverged_sub:
    forall st1,
      Reachable (steps step_m) sys st1 ->
      forall inits1 trs1 eouts1,
        ExtAtomic sys msg_dec inits1 trs1 eouts1 ->
        forall trss inits2 trs2 eouts2 st2,
          steps step_m sys st1 (trs2 ++ List.concat trss ++ trs1) st2 ->
          ExtAtomic sys msg_dec inits2 trs2 eouts2 ->
          Forall (AtomicEx msg_dec) trss ->
          Forall (Transactional sys msg_dec) trss ->
          forall cidx1 rsUp1 cidx2 rsUp2 pidx,
            RsUpMsgFrom dtr cidx1 rsUp1 ->
            parentIdxOf dtr cidx1 = Some pidx ->
            RsUpMsgFrom dtr cidx2 rsUp2 ->
            parentIdxOf dtr cidx2 = Some pidx ->
            In rsUp1 eouts1 -> In rsUp2 eouts2 -> False.
  Proof.
    intros.
    rewrite app_assoc in H1.
    eapply steps_split in H1; [|reflexivity].
    destruct H1 as [sti1 [? ?]].
    eapply extAtomic_rsUp_DownLockedNew with (rsUp:= rsUp1) in H0; eauto.
    apply downLockedNew_DownLocked in H0.
    destruct H0 as [rqid ?].

    eapply steps_split in H11; [|reflexivity].
    destruct H11 as [sti2 [? ?]].
    assert (DownLocked (bst_orqs sti2) pidx rqid).
    { assert (Reachable (steps step_m) sys sti1) by eauto.
      clear -Hiorqs Hrrs H0 H3 H4 H11 H13.
      generalize dependent sti2.
      generalize dependent trss.
      induction trss as [|trs trss]; simpl; intros; [inv_steps; assumption|].
      inv H3; inv H4.
      eapply steps_split in H11; [|reflexivity].
      destruct H11 as [stii [? ?]].
      specialize (IHtrss H5 H6 _ H).
      pose proof (atomic_Transactional_ExtAtomic H2 H3).
      destruct H4 as [einits [eouts ?]].
      eapply extAtomic_rsUp_down_lock_preserved with (st1:= stii); eauto.
    }

    eapply extAtomic_rsUp_DownLockedNew
      with (rsUp:= rsUp2) (st1:= sti2) (st2:= st2) in H2; eauto;
      [|eapply reachable_steps; [|eassumption]; eauto].
    eapply downLocked_not_DownLockedNew; eauto.
  Qed.

  Lemma extAtomic_multi_rsUps_not_diverged_gt:
    forall st1,
      Reachable (steps step_m) sys st1 ->
      forall trss st2,
        steps step_m sys st1 (List.concat trss) st2 ->
        Forall (AtomicEx msg_dec) trss ->
        Forall (Transactional sys msg_dec) trss ->
        forall n1 inits1 trs1 eouts1 n2 inits2 trs2 eouts2,
          n1 > n2 ->
          nth_error trss n1 = Some trs1 ->
          nth_error trss n2 = Some trs2 ->
          ExtAtomic sys msg_dec inits1 trs1 eouts1 ->
          ExtAtomic sys msg_dec inits2 trs2 eouts2 ->
          forall cidx1 rsUp1 cidx2 rsUp2 pidx,
            RsUpMsgFrom dtr cidx1 rsUp1 ->
            parentIdxOf dtr cidx1 = Some pidx ->
            RsUpMsgFrom dtr cidx2 rsUp2 ->
            parentIdxOf dtr cidx2 = Some pidx ->
            In rsUp1 eouts1 -> In rsUp2 eouts2 -> False.
  Proof.
    intros.
    assert (exists ptrss itrss ntrss,
               trss = ntrss ++ trs2 :: itrss ++ trs1 :: ptrss) as Htrss.
    { apply nth_error_split in H5.
      destruct H5 as [ntrss [ptrss2 ?]]; dest; subst.
      rewrite nth_error_app2 in H4; [|omega].
      apply nth_error_split in H4.
      destruct H4 as [ntrss1 [ptrss ?]]; dest; subst.
      destruct ntrss1; [simpl in *; omega|].
      simpl in *; inv H4.
      do 3 eexists; reflexivity.
    }
    destruct Htrss as [ptrss [itrss [ntrss ?]]]; subst.

    repeat (rewrite concat_app in H0; simpl in H0).
    eapply steps_split in H0; [|reflexivity].
    destruct H0 as [sti2 [? ?]].
    do 2 rewrite app_assoc in H0.
    eapply steps_split in H0; [|reflexivity].
    destruct H0 as [sti1 [? ?]].
    rewrite <-app_assoc in H15.

    eapply extAtomic_multi_rsUps_not_diverged_sub
      with (trs1:= trs1) (trs2:= trs2) (rsUp1:= rsUp1) (rsUp2:= rsUp2)
           (st1:= sti1) (st2:= sti2); eauto.
    - apply Forall_app_inv in H1; dest.
      inv H16.
      apply Forall_app_inv in H20; dest.
      assumption.
    - apply Forall_app_inv in H2; dest.
      inv H16.
      apply Forall_app_inv in H20; dest.
      assumption.
  Qed.

  Lemma extAtomic_multi_rsUps_not_diverged:
    forall st1,
      Reachable (steps step_m) sys st1 ->
      forall trss st2,
        steps step_m sys st1 (List.concat trss) st2 ->
        Forall (AtomicEx msg_dec) trss ->
        Forall (Transactional sys msg_dec) trss ->
        forall n1 inits1 trs1 eouts1 n2 inits2 trs2 eouts2,
          n1 <> n2 ->
          nth_error trss n1 = Some trs1 ->
          nth_error trss n2 = Some trs2 ->
          ExtAtomic sys msg_dec inits1 trs1 eouts1 ->
          ExtAtomic sys msg_dec inits2 trs2 eouts2 ->
          forall cidx1 rsUp1 cidx2 rsUp2 pidx,
            RsUpMsgFrom dtr cidx1 rsUp1 ->
            parentIdxOf dtr cidx1 = Some pidx ->
            RsUpMsgFrom dtr cidx2 rsUp2 ->
            parentIdxOf dtr cidx2 = Some pidx ->
            In rsUp1 eouts1 -> In rsUp2 eouts2 -> False.
  Proof.
    intros.
    destruct (lt_eq_lt_dec n1 n2) as [[|]|]; [|auto|].
    - eapply extAtomic_multi_rsUps_not_diverged_gt
        with (trs1:= trs2) (trs2:= trs1) (rsUp1:= rsUp2) (rsUp2:= rsUp1); eauto.
    - eapply extAtomic_multi_rsUps_not_diverged_gt
        with (trs1:= trs1) (trs2:= trs2) (rsUp1:= rsUp1) (rsUp2:= rsUp2); eauto.
  Qed.

End Corollaries.

