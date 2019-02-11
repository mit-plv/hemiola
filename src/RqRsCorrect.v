Require Import Peano_dec Omega List ListSupport.
Require Import Common FMap.
Require Import Syntax Semantics SemFacts StepM Invariant.
Require Import Serial SerialFacts.
Require Import Reduction Commutativity QuasiSeq Topology.
Require Import RqRsTopo RqRsFacts.
Require Import RqRsInvMsg RqRsInvLock RqRsInvAtomic.
Require Import RqRsRed RqUpRed RsUpRed RqDownRed RsDownRed.

Set Implicit Arguments.

Open Scope list.
Open Scope fmap.

Section Pushable.
  Context {oifc: OStateIfc}.
  Variables (dtr: DTree)
            (sys: System oifc).

  Hypothesis (Hrrs: RqRsSys dtr sys).

  Variables (phst: MHistory)
            (oidx ridx: IdxT)
            (rins routs: list (Id Msg)).
  Hypothesis (Hcont: ExtContinuousL sys phst (RlblInt oidx ridx rins routs)).

  Local Definition nlbl := (RlblInt oidx ridx rins routs).

  Section RqUp.
    Hypothesis (Hru: RqUpMsgs dtr oidx rins).

    Lemma rqUp_lpush_unit:
      forall hst,
        AtomicEx msg_dec hst ->
        Discontinuous phst hst ->
        Reducible sys (hst ++ phst) (phst ++ hst).
    Proof.
      intros.
      destruct H as [inits [ins [outs [eouts ?]]]].
      destruct Hcont as [peouts [oidx' [ridx' [rins' [routs' ?]]]]]; dest.
      apply eq_sym in H2; inv H2.
      destruct H1 as [pinits pins phst pouts peouts].
      red in H0; dest.
      pose proof (atomic_unique H0 H2); dest; subst.
      pose proof (atomic_unique H5 H); dest; subst.
      eapply rqUp_lpush_unit_reducible; eauto.
    Qed.
    
    Lemma rqUp_LPushableHst: LPushableHst sys phst nlbl.
    Proof.
      intros; red; intros.
      inv H1; clear H8.
      generalize dependent st3.
      induction hsts; simpl; intros; [constructor|].
      inv H0; inv H2.
      rewrite <-app_assoc in H6.
      eapply steps_split in H6; [|reflexivity].
      destruct H6 as [sti [? ?]].
      constructor; eauto.
      intros; eapply rqUp_lpush_unit; eauto.
    Qed.

    Lemma rqUp_WellInterleavedHst: WellInterleavedHst sys phst nlbl.
    Proof.
      apply LPushableHst_WellInterleavedHst; auto.
      eauto using rqUp_LPushableHst.
    Qed.
    
  End RqUp.

  Section RsUp.
    Hypothesis (Hru: RsUpMsgs dtr oidx rins).

    Definition RsUpP: MState oifc -> Prop :=
      fun st => Forall (InMPI st.(bst_msgs)) rins.

    Lemma rsUp_PInitializing:
      PInitializing sys RsUpP phst.
    Proof.
      intros; red; intros.
      destruct Hcont as [eouts [oidx' [ridx' [rins' [routs' ?]]]]]; dest.
      apply eq_sym in H1; inv H1.
      inv H0.
      red; eapply SubList_forall; [|eassumption].
      eapply (atomic_messages_eouts_in msg_dec); eauto.
    Qed.

    Lemma rsUp_PPreserving:
      forall hst,
        Discontinuous phst hst ->
        PPreserving sys RsUpP hst.
    Proof.
      intros.
      destruct Hcont as [eouts [oidx' [ridx' [rins' [routs' ?]]]]]; dest.
      apply eq_sym in H1; inv H1.
      inv H0.
      destruct H as [inits1 [ins1 [outs1 [eouts1 [inits2 [ins2 [outs2 [eouts2 ?]]]]]]]].
      dest.
      eapply atomic_unique in H; [|eassumption]; dest; subst.

      red; intros.
      eapply (atomic_messages_ins_ins msg_dec).
      - eapply H0.
      - eassumption.
      - assumption.
      - eapply DisjList_comm, DisjList_SubList; eauto.
    Qed.

    Lemma rsUp_rpush_unit:
      forall hst,
        AtomicEx msg_dec hst ->
        Discontinuous phst hst ->
        ReducibleP sys RsUpP (nlbl :: hst) (hst ++ [nlbl]).
    Proof.
      intros.
      destruct H as [inits [ins [outs [eouts ?]]]].
      destruct Hcont as [peouts [oidx' [ridx' [rins' [routs' ?]]]]]; dest.
      apply eq_sym in H2; inv H2.
      destruct H1 as [pinits pins phst pouts peouts].
      red in H0; dest.
      pose proof (atomic_unique H0 H2); dest; subst.
      pose proof (atomic_unique H5 H); dest; subst.
      eapply rsUp_rpush_unit_reducible; eauto.
      eapply DisjList_SubList; eauto.
    Qed.
    
    Lemma rsUp_RPushableHst:
      RPushableHst sys RsUpP phst nlbl.
    Proof.
      intros; red; intros.
      inv H1.
      eapply steps_split in H6; [|reflexivity].
      destruct H6 as [st4 [? ?]]; clear H1.
      generalize dependent st4.
      induction hsts as [|hst hsts] using list_ind_rev;
        simpl; intros; [constructor|].

      apply Forall_app_inv in H0; dest.
      inv H1; clear H7.
      apply Forall_app_inv in H2; dest.
      inv H2; clear H9.

      rewrite concat_app in H3; simpl in H3.
      rewrite app_nil_r in H3.
      eapply steps_split in H3; [|reflexivity].
      destruct H3 as [sti [? ?]].

      apply Forall_app; eauto.
      constructor; auto.
      split.
      - apply rsUp_PPreserving; auto.
      - intros; eapply rsUp_rpush_unit; eauto.
    Qed.

    Lemma rsUp_WellInterleavedHst:
      WellInterleavedHst sys phst nlbl.
    Proof.
      apply RPushableHst_WellInterleavedHst with (P:= RsUpP); auto.
      - eauto using rsUp_PInitializing.
      - eauto using rsUp_RPushableHst.
    Qed.

  End RsUp.

  Section RqDown.
    Hypothesis (Hrd: RqDownMsgs dtr sys oidx rins).

    Definition RqDownLPush (hst: MHistory) :=
      exists loidx,
        lastOIdxOf hst = Some loidx /\
        In loidx (subtreeIndsOf dtr oidx).

    Definition RqDownRPush (hst: MHistory) :=
      exists loidx,
        lastOIdxOf hst = Some loidx /\
        ~ In loidx (subtreeIndsOf dtr oidx).

    Lemma rqDown_PInitializing:
      PInitializing sys (RqDownP rins) phst.
    Proof.
      intros; red; intros.
      destruct Hcont as [eouts [oidx' [ridx' [rins' [routs' ?]]]]]; dest.
      apply eq_sym in H1; inv H1.
      inv H0.
      red; eapply SubList_forall; [|eassumption].
      eapply (atomic_messages_eouts_in msg_dec); eauto.
    Qed.

    Lemma rqDown_discontinuous_PPreserving:
      forall hst,
        Discontinuous phst hst ->
        PPreserving sys RsUpP hst.
    Proof.
      intros.
      destruct Hcont as [eouts [oidx' [ridx' [rins' [routs' ?]]]]]; dest.
      apply eq_sym in H1; inv H1.

      inv H0.
      destruct H as [inits1 [ins1 [outs1 [eouts1 [inits2 [ins2 [outs2 [eouts2 ?]]]]]]]].
      dest.
      eapply atomic_unique in H; [|eassumption]; dest; subst.

      red; intros.
      eapply (atomic_messages_ins_ins msg_dec).
      - eapply H0.
      - eassumption.
      - assumption.
      - eapply DisjList_comm, DisjList_SubList; eauto.
    Qed.

    Lemma rqDown_PPreserving:
      forall st1,
        Reachable (steps step_m) sys st1 ->
        forall hsts st2,
          Forall (AtomicEx msg_dec) hsts ->
          steps step_m sys st1 (nlbl :: List.concat hsts ++ phst) st2 ->
          Forall (fun hst => Discontinuous phst hst) hsts ->
          Forall (PPreserving sys (RqDownP rins)) hsts.
    Proof.
      intros.
      eapply Forall_impl; [|eapply H2].
      simpl; intros hst ?.
      eapply rqDown_discontinuous_PPreserving; assumption.
    Qed.

    Lemma rqDown_lpush_or_rpush:
      forall st1,
        Reachable (steps step_m) sys st1 ->
        forall hsts st2,
          Forall (AtomicEx msg_dec) hsts ->
          steps step_m sys st1 (nlbl :: List.concat hsts ++ phst) st2 ->
          Forall (fun hst => Discontinuous phst hst) hsts ->
          Forall (fun hst => RqDownLPush hst \/ RqDownRPush hst) hsts.
    Proof.
      intros; clear -H0.
      rewrite Forall_forall in H0.
      apply Forall_forall.
      intros hst ?.
      specialize (H0 _ H).
      destruct H0 as [inits [ints [outs [eouts ?]]]].
      apply atomic_lastOIdxOf in H0.
      destruct H0 as [loidx ?].
      destruct (in_dec eq_nat_dec loidx (subtreeIndsOf dtr oidx)).
      - left; red; eauto.
      - right; red; eauto.
    Qed.

    Lemma rqDown_lpush_unit:
      forall hst,
        AtomicEx msg_dec hst ->
        Discontinuous phst hst ->
        RqDownLPush hst ->
        Reducible sys (hst ++ phst) (phst ++ hst).
    Proof.
      intros.
      destruct Hcont as [peouts [oidx' [ridx' [rins' [routs' ?]]]]]; dest.
      apply eq_sym in H3; inv H3.
      inv H2.
      destruct H0 as [inits1 [ins1 [outs1 [eouts1 ?]]]].
      destruct H0 as [inits2 [ins2 [outs2 [eouts2 ?]]]]; dest.
      pose proof (atomic_unique H6 H0); dest; subst; clear H0.
      destruct H1 as [loidx [? ?]].
      eapply rqDown_lpush_unit_reducible; eauto.
      apply rqDown_PInitializing.
    Qed.
    
    Lemma rqDown_lpush_reducible:
      forall st1,
        Reachable (steps step_m) sys st1 ->
        forall hsts st2,
          Forall (AtomicEx msg_dec) hsts ->
          steps step_m sys st1 (nlbl :: List.concat hsts ++ phst) st2 ->
          Forall (fun hst => Discontinuous phst hst) hsts ->
          Forall (fun hst => RqDownLPush hst ->
                             Reducible sys (hst ++ phst) (phst ++ hst)) hsts.
    Proof.
      intros.
      inv_steps.
      eapply steps_split in H6; [|reflexivity].
      destruct H6 as [sti [? ?]].
      clear H8.
      generalize dependent st3.
      induction hsts as [|hst hsts]; simpl; intros; [constructor|].
      inv H0; inv H2.
      eapply steps_split in H3; [|reflexivity].
      destruct H3 as [hsti [? ?]].
      specialize (IHhsts H7 H8 _ H0).
      constructor; [|assumption].
      intros; apply rqDown_lpush_unit; auto.
    Qed.

    Lemma rqDown_rpush_unit:
      forall hst,
        RqDownRPush hst ->
        AtomicEx msg_dec hst ->
        Discontinuous phst hst ->
        ReducibleP sys (RqDownP rins) (nlbl :: hst) (hst ++ [nlbl]).
    Proof.
      intros.
      destruct H0 as [inits [ins [outs [eouts ?]]]].
      destruct Hcont as [peouts [oidx' [ridx' [rins' [routs' ?]]]]]; dest.
      apply eq_sym in H3; inv H3.
      destruct H2 as [pinits pins phst pouts peouts].
      red in H1; dest.
      pose proof (atomic_unique H1 H3); dest; subst; clear H3.
      pose proof (atomic_unique H6 H0); dest; subst; clear H6.
      destruct H as [loidx [? ?]].
      eapply rqDown_rpush_unit_reducible; eauto.
      eapply DisjList_SubList; eauto.
    Qed.

    Lemma rqDown_rpush_reducible:
      forall st1,
        Reachable (steps step_m) sys st1 ->
        forall hsts st2,
          Forall (AtomicEx msg_dec) hsts ->
          steps step_m sys st1 (nlbl :: List.concat hsts ++ phst) st2 ->
          Forall (fun hst => Discontinuous phst hst) hsts ->
          Forall (fun hst => RqDownRPush hst ->
                             ReducibleP sys (RqDownP rins) (nlbl :: hst) (hst ++ [nlbl])) hsts.
    Proof.
      intros.
      clear H1.
      induction hsts as [|hst hsts]; simpl; intros; [constructor|].
      inv H0; inv H2.
      constructor; eauto.
      intros; eapply rqDown_rpush_unit; eauto.
    Qed.

    Lemma rqDown_LRPushable:
      forall st1,
        Reachable (steps step_m) sys st1 ->
        forall hsts st2,
          Forall (AtomicEx msg_dec) hsts ->
          steps step_m sys st1 (nlbl :: List.concat hsts ++ phst) st2 ->
          Forall (fun hst => Discontinuous phst hst) hsts ->
          LRPushable sys (RqDownP rins) RqDownLPush RqDownRPush hsts.
    Proof.
      intros; red; intros; subst.
      apply Forall_app_inv in H0; dest.
      inv H3; destruct H8 as [inits1 [ins1 [outs1 [eouts1 ?]]]].
      apply Forall_app_inv in H9; dest.
      inv H7; destruct H10 as [inits2 [ins2 [outs2 [eouts2 ?]]]].
      destruct H4 as [lloidx [? ?]].
      destruct H5 as [rloidx [? ?]].

      assert (DisjList rins inits1 /\ DisjList rins inits2).
      { destruct Hcont as [peouts [oidx' [ridx' [rins' [routs' ?]]]]]; dest.
        apply eq_sym in H12; inv H12.
        apply Forall_app_inv in H2; dest.
        inv H12; apply Forall_app_inv in H18; dest.
        inv H15.
        red in H17, H19; dest.
        pose proof (atomic_unique H19 H3); dest; subst; clear H19.
        pose proof (atomic_unique H16 H7); dest; subst; clear H16.
        inv H10.
        pose proof (atomic_unique H17 H19); dest; subst; clear H17.
        pose proof (atomic_unique H15 H19); dest; subst; clear H15.
        split; eapply DisjList_SubList; eassumption.
      }
      destruct H10.
      eapply rqDown_LRPushable_unit_reducible; try eassumption.
    Qed.

    Lemma rqDown_WellInterleavedHst:
      WellInterleavedHst sys phst nlbl.
    Proof.
      apply PushableHst_WellInterleavedHst with (P:= RqDownP rins); auto.
      - eauto using rqDown_PInitializing.
      - exists RqDownLPush, RqDownRPush.
        intros; repeat split.
        + eauto using rqDown_PPreserving.
        + eauto using rqDown_lpush_or_rpush.
        + eauto using rqDown_lpush_reducible.
        + eauto using rqDown_rpush_reducible.
        + eauto using rqDown_LRPushable.
    Qed.

  End RqDown.

  Section RsDown.
    Hypothesis (Hrd: RsDownMsgs dtr sys oidx rins).

    Definition RsDownLPush (hst: MHistory) :=
      exists loidx,
        lastOIdxOf hst = Some loidx /\
        In loidx (subtreeIndsOf dtr oidx).

    Definition RsDownRPush (hst: MHistory) :=
      exists loidx,
        lastOIdxOf hst = Some loidx /\
        ~ In loidx (subtreeIndsOf dtr oidx).

    Lemma rsDown_PInitializing:
      PInitializing sys (RsDownP rins) phst.
    Proof.
      intros; red; intros.
      destruct Hcont as [eouts [oidx' [ridx' [rins' [routs' ?]]]]]; dest.
      apply eq_sym in H1; inv H1.
      inv H0.
      red; eapply SubList_forall; [|eassumption].
      eapply (atomic_messages_eouts_in msg_dec); eauto.
    Qed.

    Lemma rsDown_discontinuous_PPreserving:
      forall hst,
        Discontinuous phst hst ->
        PPreserving sys RsUpP hst.
    Proof.
      intros.
      destruct Hcont as [eouts [oidx' [ridx' [rins' [routs' ?]]]]]; dest.
      apply eq_sym in H1; inv H1.

      inv H0.
      destruct H as [inits1 [ins1 [outs1 [eouts1 [inits2 [ins2 [outs2 [eouts2 ?]]]]]]]].
      dest.
      eapply atomic_unique in H; [|eassumption]; dest; subst.

      red; intros.
      eapply (atomic_messages_ins_ins msg_dec).
      - eapply H0.
      - eassumption.
      - assumption.
      - eapply DisjList_comm, DisjList_SubList; eauto.
    Qed.

    Lemma rsDown_PPreserving:
      forall st1,
        Reachable (steps step_m) sys st1 ->
        forall hsts st2,
          Forall (AtomicEx msg_dec) hsts ->
          steps step_m sys st1 (nlbl :: List.concat hsts ++ phst) st2 ->
          Forall (fun hst => Discontinuous phst hst) hsts ->
          Forall (PPreserving sys (RsDownP rins)) hsts.
    Proof.
      intros.
      eapply Forall_impl; [|eapply H2].
      simpl; intros hst ?.
      eapply rsDown_discontinuous_PPreserving; assumption.
    Qed.

    Lemma rsDown_lpush_or_rpush:
      forall st1,
        Reachable (steps step_m) sys st1 ->
        forall hsts st2,
          Forall (AtomicEx msg_dec) hsts ->
          steps step_m sys st1 (nlbl :: List.concat hsts ++ phst) st2 ->
          Forall (fun hst => Discontinuous phst hst) hsts ->
          Forall (fun hst => RsDownLPush hst \/ RsDownRPush hst) hsts.
    Proof.
      intros; clear -H0.
      rewrite Forall_forall in H0.
      apply Forall_forall.
      intros hst ?.
      specialize (H0 _ H).
      destruct H0 as [inits [ints [outs [eouts ?]]]].
      apply atomic_lastOIdxOf in H0.
      destruct H0 as [loidx ?].
      destruct (in_dec eq_nat_dec loidx (subtreeIndsOf dtr oidx)).
      - left; red; eauto.
      - right; red; eauto.
    Qed.

    Lemma rsDown_lpush_unit:
      forall hst,
        AtomicEx msg_dec hst ->
        Discontinuous phst hst ->
        RsDownLPush hst ->
        Reducible sys (hst ++ phst) (phst ++ hst).
    Proof.
      intros.
      destruct Hcont as [peouts [oidx' [ridx' [rins' [routs' ?]]]]]; dest.
      apply eq_sym in H3; inv H3.
      inv H2.
      destruct H0 as [inits1 [ins1 [outs1 [eouts1 ?]]]].
      destruct H0 as [inits2 [ins2 [outs2 [eouts2 ?]]]]; dest.
      pose proof (atomic_unique H6 H0); dest; subst; clear H0.
      destruct H1 as [loidx [? ?]].
      eapply rsDown_lpush_unit_reducible; eauto.
      apply rsDown_PInitializing.
    Qed.
    
    Lemma rsDown_lpush_reducible:
      forall st1,
        Reachable (steps step_m) sys st1 ->
        forall hsts st2,
          Forall (AtomicEx msg_dec) hsts ->
          steps step_m sys st1 (nlbl :: List.concat hsts ++ phst) st2 ->
          Forall (fun hst => Discontinuous phst hst) hsts ->
          Forall (fun hst => RsDownLPush hst ->
                             Reducible sys (hst ++ phst) (phst ++ hst)) hsts.
    Proof.
      intros.
      inv_steps.
      eapply steps_split in H6; [|reflexivity].
      destruct H6 as [sti [? ?]].
      clear H8.
      generalize dependent st3.
      induction hsts as [|hst hsts]; simpl; intros; [constructor|].
      inv H0; inv H2.
      eapply steps_split in H3; [|reflexivity].
      destruct H3 as [hsti [? ?]].
      specialize (IHhsts H7 H8 _ H0).
      constructor; [|assumption].
      intros; apply rsDown_lpush_unit; auto.
    Qed.

    Lemma rsDown_rpush_unit:
      forall hst,
        RsDownRPush hst ->
        AtomicEx msg_dec hst ->
        Discontinuous phst hst ->
        ReducibleP sys (RsDownP rins) (nlbl :: hst) (hst ++ [nlbl]).
    Proof.
      intros.
      destruct H0 as [inits [ins [outs [eouts ?]]]].
      destruct Hcont as [peouts [oidx' [ridx' [rins' [routs' ?]]]]]; dest.
      apply eq_sym in H3; inv H3.
      destruct H2 as [pinits pins phst pouts peouts].
      red in H1; dest.
      pose proof (atomic_unique H1 H3); dest; subst; clear H3.
      pose proof (atomic_unique H6 H0); dest; subst; clear H6.
      destruct H as [loidx [? ?]].
      eapply rsDown_rpush_unit_reducible; eauto.
      eapply DisjList_SubList; eauto.
    Qed.

    Lemma rsDown_rpush_reducible:
      forall st1,
        Reachable (steps step_m) sys st1 ->
        forall hsts st2,
          Forall (AtomicEx msg_dec) hsts ->
          steps step_m sys st1 (nlbl :: List.concat hsts ++ phst) st2 ->
          Forall (fun hst => Discontinuous phst hst) hsts ->
          Forall (fun hst => RsDownRPush hst ->
                             ReducibleP sys (RsDownP rins) (nlbl :: hst) (hst ++ [nlbl])) hsts.
    Proof.
      intros.
      clear H1.
      induction hsts as [|hst hsts]; simpl; intros; [constructor|].
      inv H0; inv H2.
      constructor; eauto.
      intros; eapply rsDown_rpush_unit; eauto.
    Qed.

    Lemma rsDown_LRPushable:
      forall st1,
        Reachable (steps step_m) sys st1 ->
        forall hsts st2,
          Forall (AtomicEx msg_dec) hsts ->
          steps step_m sys st1 (nlbl :: List.concat hsts ++ phst) st2 ->
          Forall (fun hst => Discontinuous phst hst) hsts ->
          LRPushable sys (RsDownP rins) RsDownLPush RsDownRPush hsts.
    Proof.
      intros; red; intros; subst.
      apply Forall_app_inv in H0; dest.
      inv H3; destruct H8 as [inits1 [ins1 [outs1 [eouts1 ?]]]].
      apply Forall_app_inv in H9; dest.
      inv H7; destruct H10 as [inits2 [ins2 [outs2 [eouts2 ?]]]].
      destruct H4 as [lloidx [? ?]].
      destruct H5 as [rloidx [? ?]].

      assert (DisjList rins inits1 /\ DisjList rins inits2).
      { destruct Hcont as [peouts [oidx' [ridx' [rins' [routs' ?]]]]]; dest.
        apply eq_sym in H12; inv H12.
        apply Forall_app_inv in H2; dest.
        inv H12; apply Forall_app_inv in H18; dest.
        inv H15.
        red in H17, H19; dest.
        pose proof (atomic_unique H19 H3); dest; subst; clear H19.
        pose proof (atomic_unique H16 H7); dest; subst; clear H16.
        inv H10.
        pose proof (atomic_unique H17 H19); dest; subst; clear H17.
        pose proof (atomic_unique H15 H19); dest; subst; clear H15.
        split; eapply DisjList_SubList; eassumption.
      }
      destruct H10.
      eapply rsDown_LRPushable_unit_reducible; try eassumption.
    Qed.

    Lemma rsDown_WellInterleavedHst:
      WellInterleavedHst sys phst nlbl.
    Proof.
      apply PushableHst_WellInterleavedHst with (P:= RqDownP rins); auto.
      - eauto using rsDown_PInitializing.
      - exists RqDownLPush, RqDownRPush.
        intros; repeat split.
        + eauto using rsDown_PPreserving.
        + eauto using rsDown_lpush_or_rpush.
        + eauto using rsDown_lpush_reducible.
        + eauto using rsDown_rpush_reducible.
        + eauto using rsDown_LRPushable.
    Qed.
    
  End RsDown.
  
End Pushable.

Theorem rqrs_WellInterleaved:
  forall {oifc} (sys: System oifc) (dtr: DTree),
    RqRsSys dtr sys ->
    WellInterleaved sys.
Proof.
  intros; red; intros.
  red; intros.

  assert (exists oidx ridx rins routs,
             l2 = RlblInt oidx ridx rins routs /\
             (RqUpMsgs dtr oidx rins \/
              RqDownMsgs dtr sys oidx rins \/
              RsUpMsgs dtr oidx rins \/
              RsDownMsgs dtr sys oidx rins)) as Hnlbl.
  { destruct H as [? [? ?]].
    red in H0.
    destruct H0 as [eouts [oidx [ridx [rins [routs ?]]]]]; dest; subst.
    inv H2.
    eapply messages_in_cases in H14; eauto.
    eauto 6.
  }
  destruct Hnlbl as [oidx [ridx [rins [routs ?]]]]; dest; subst.

  destruct H6 as [|[|[|]]].
  - eapply rqUp_WellInterleavedHst; eauto.
  - eapply rqDown_WellInterleavedHst; eauto.
  - eapply rsUp_WellInterleavedHst; eauto.
  - eapply rsDown_WellInterleavedHst; eauto.
Qed.

Corollary rqrs_Serializable:
  forall {oifc} (sys: System oifc) (dtr: DTree),
    RqRsSys dtr sys ->
    SerializableSys sys.
Proof.
  intros.
  apply well_interleaved_serializable.
  eapply rqrs_WellInterleaved; eauto.
Qed.

Close Scope list.
Close Scope fmap.

