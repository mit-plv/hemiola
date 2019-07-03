Require Import Peano_dec Omega List ListSupport.
Require Import Common FMap.
Require Import Syntax Semantics SemFacts StepM Invariant.
Require Import Serial SerialFacts.
Require Import Reduction Commutativity QuasiSeq Topology.
Require Import RqRsTopo RqRsFacts.
Require Import RqRsInvMsg RqRsInvLock RqRsInvAtomic RqRsInvSep.
Require Import RqRsRed RqUpRed RsUpRed RqDownRed RsDownRed.

Set Implicit Arguments.

Open Scope list.
Open Scope fmap.

Section Pushable.
  Context {oifc: OStateIfc}.
  Variables (dtr: DTree)
            (sys: System oifc).

  Hypotheses (Hiorqs: GoodORqsInit (initsOf sys))
             (Hrrs: RqRsSys dtr sys).

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
      eapply atomic_messages_eouts_in; eauto.
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
      eapply atomic_messages_ins_ins.
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
    Variable pobj: Object oifc.
    Hypothesis (Hrd: RqDownMsgs dtr sys oidx rins)
               (Hpobj: In pobj sys.(sys_objs))
               (Hcp: parentIdxOf dtr oidx = Some (obj_idx pobj)).

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
      eapply atomic_messages_eouts_in; eauto.
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
      eapply atomic_messages_ins_ins.
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
      destruct (in_dec idx_dec loidx (subtreeIndsOf dtr oidx)).
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
    Variable pobj: Object oifc.
    Hypothesis (Hrd: RsDownMsgs dtr sys oidx rins)
               (Hpobj: In pobj sys.(sys_objs))
               (Hcp: parentIdxOf dtr oidx = Some (obj_idx pobj)).
    
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
      eapply atomic_messages_eouts_in; eauto.
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
      eapply atomic_messages_ins_ins.
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
      destruct (in_dec idx_dec loidx (subtreeIndsOf dtr oidx)).
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

  Lemma rqDown_ExtContinuousL_parent_in_system:
    RqDownMsgs dtr sys oidx rins ->
    forall st1,
      Reachable (steps step_m) sys st1 ->
      forall st2,
        steps step_m sys st1 phst st2 ->
        exists pobj,
          In pobj (sys_objs sys) /\
          parentIdxOf dtr oidx = Some (obj_idx pobj).
  Proof.
    destruct Hrrs as [? [? ?]]; intros.
    destruct Hcont as [eouts [oidx' [ridx' [rins' [routs' ?]]]]]; dest.
    apply eq_sym in H6; inv H6.
    destruct H5 as [pinits pins phst pouts peouts].
    destruct H2 as [cobj [rqDown ?]]; dest; subst.
    pose proof (edgeDownTo_Some H _ H10).
    destruct H2 as [rqUp [rsUp [pidx ?]]]; dest.
    eapply atomic_down_out_in_history in H6; eauto.
    - eapply steps_object_in_system in H6; eauto.
      destruct H6 as [pobj [? ?]]; subst.
      exists pobj; auto.
    - apply SubList_singleton_In in H8.
      apply in_map; assumption.
  Qed.

  Lemma rsDown_ExtContinuousL_parent_in_system:
    RsDownMsgs dtr sys oidx rins ->
    forall st1,
      Reachable (steps step_m) sys st1 ->
      forall st2,
        steps step_m sys st1 phst st2 ->
        exists pobj,
          In pobj (sys_objs sys) /\
          parentIdxOf dtr oidx = Some (obj_idx pobj).
  Proof.
    destruct Hrrs as [? [? ?]]; intros.
    destruct Hcont as [eouts [oidx' [ridx' [rins' [routs' ?]]]]]; dest.
    apply eq_sym in H6; inv H6.
    destruct H5 as [pinits pins phst pouts peouts].
    destruct H2 as [cobj [rsDown ?]]; dest; subst.
    pose proof (edgeDownTo_Some H _ H10).
    destruct H2 as [rqUp [rsUp [pidx ?]]]; dest.
    eapply atomic_down_out_in_history in H6; eauto.
    - eapply steps_object_in_system in H6; eauto.
      destruct H6 as [pobj [? ?]]; subst.
      exists pobj; auto.
    - apply SubList_singleton_In in H8.
      apply in_map; assumption.
  Qed.
  
End Pushable.

Theorem rqrs_WellInterleaved:
  forall {oifc} (sys: System oifc) (Hiorqs: GoodORqsInit (initsOf sys))
         (dtr: DTree),
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
  - assert (exists sti, steps step_m sys st1 hst1 sti).
    { inv_steps.
      eapply steps_split in H9; [|reflexivity].
      destruct H9 as [sti [? ?]]; eauto.
    }
    destruct H6 as [sti ?].
    destruct (rqDown_ExtContinuousL_parent_in_system Hiorqs H H0 H5 H1 H6)
      as [pobj [? ?]].
    eapply rqDown_WellInterleavedHst; eauto.
  - eapply rsUp_WellInterleavedHst; eauto.
  - assert (exists sti, steps step_m sys st1 hst1 sti).
    { inv_steps.
      eapply steps_split in H9; [|reflexivity].
      destruct H9 as [sti [? ?]]; eauto.
    }
    destruct H6 as [sti ?].
    destruct (rsDown_ExtContinuousL_parent_in_system Hiorqs H H0 H5 H1 H6)
      as [pobj [? ?]].
    eapply rsDown_WellInterleavedHst; eauto.
Qed.

(*! TODO: move to [SerialFacts.v] *)

Lemma atomic_Transactional_ExtAtomic:
  forall {oifc} (sys: System oifc) trs,
    AtomicEx msg_dec trs ->
    Transactional sys msg_dec trs ->
    exists einits eouts,
      ExtAtomic sys msg_dec einits trs eouts.
Proof.
  intros.
  destruct H as [inits [ins [outs [eouts ?]]]].
  inv H0; try (inv H; fail).
  eauto.
Qed.

Lemma extAtomic_Discontinuous:
  forall {oifc} (sys: System oifc) st1 trss st2,
    steps step_m sys st1 (List.concat trss) st2 ->
    Forall (AtomicEx msg_dec) trss ->
    Forall (Transactional sys msg_dec) trss ->
    forall trs1 trs2,
      In trs1 trss -> In trs2 trss ->
      Discontinuous trs1 trs2.
Proof.
  intros.
  rewrite Forall_forall in H0, H1.
  pose proof (H0 _ H2).
  pose proof (H1 _ H2).
  pose proof (H0 _ H3).
  pose proof (H1 _ H3).
  eapply atomic_Transactional_ExtAtomic in H5; [|eassumption].
  destruct H5 as [einits1 [eouts1 ?]]; inv H5.
  eapply atomic_Transactional_ExtAtomic in H7; [|eassumption].
  destruct H7 as [einits2 [eouts2 ?]]; inv H5.

  assert (exists st11 st12, steps step_m sys st11 trs1 st12).
  { apply in_split in H2.
    destruct H2 as [ptrss [ntrss ?]]; subst.
    rewrite concat_app in H; simpl in H.
    eapply steps_split in H; [|reflexivity].
    destruct H as [sti1 [? ?]].
    eapply steps_split in H; [|reflexivity].
    destruct H as [sti2 [? ?]].
    eauto.
  }
  destruct H5 as [st11 [st12 ?]].
  eapply atomic_eouts_not_erqs in H5; [|eassumption].

  do 8 eexists.
  repeat ssplit; try eassumption.
  red; intros idm.
  destruct (in_dec (id_dec msg_dec) idm eouts1); [|auto].
  rewrite Forall_forall in H5.
  specialize (H5 _ i).
  right; intro Hx.
  apply in_map with (f:= idOf) in Hx.
  apply H7 in Hx; auto.
Qed.

Lemma atomic_non_inits_InMPI_or:
  forall inits ins hst outs eouts,
    Atomic msg_dec inits ins hst outs eouts ->
    forall {oifc} (sys: System oifc) st1 st2,
      steps step_m sys st1 hst st2 ->
      forall idm,
        ~ In idm inits ->
        InMPI st2.(bst_msgs) idm ->
        InMPI st1.(bst_msgs) idm \/ In idm eouts.
Proof.
  intros.
  eapply atomic_messages_non_inits_count_eq in H; [|eassumption..].
  apply (countMsg_InMPI msg_dec) in H2.
  assert (countMsg msg_dec idm st1.(bst_msgs) > 0 \/
          count_occ (id_dec msg_dec) eouts idm > 0) by omega.
  destruct H3.
  - left; apply (countMsg_InMPI msg_dec); assumption.
  - right; apply (count_occ_In (id_dec msg_dec)); assumption.
Qed.

Lemma extAtomic_non_inits_InMPI_or:
  forall {oifc} (sys: System oifc) inits hst eouts,
    ExtAtomic sys msg_dec inits hst eouts ->
    forall st1 st2,
      steps step_m sys st1 hst st2 ->
      forall idm,
        ~ In (idOf idm) (sys_merqs sys) ->
        InMPI st2.(bst_msgs) idm ->
        InMPI st1.(bst_msgs) idm \/ In idm eouts.
Proof.
  intros.
  inv H.
  eapply atomic_non_inits_InMPI_or; try eassumption.
  intro Hx.
  apply in_map with (f:= idOf) in Hx.
  apply H3 in Hx; auto.
Qed.

Lemma extAtomic_multi_non_inits_InMPI_or:
  forall {oifc} (sys: System oifc) st1,
    Reachable (steps step_m) sys st1 ->
    forall trss st2,
      steps step_m sys st1 (List.concat trss) st2 ->
      Forall (AtomicEx msg_dec) trss ->
      Forall (Transactional sys msg_dec) trss ->
      forall idm,
        ~ In (idOf idm) (sys_merqs sys) ->
        InMPI st2.(bst_msgs) idm ->
        InMPI st1.(bst_msgs) idm \/
        exists einits trs eouts,
          In trs trss /\
          ExtAtomic sys msg_dec einits trs eouts /\
          In idm eouts.
Proof.
  induction trss as [|trs trss]; simpl; intros; [inv_steps; auto|].

  eapply steps_split in H0; [|reflexivity].
  destruct H0 as [sti [? ?]].
  inv H1; inv H2.
  pose proof (atomic_Transactional_ExtAtomic H8 H7).
  destruct H1 as [einits [eouts ?]].

  eapply extAtomic_non_inits_InMPI_or in H5; try eassumption.
  destruct H5; [|eauto 8].

  specialize (IHtrss _ H0 H9 H10 _ H3 H2).
  destruct IHtrss; [auto|].
  destruct H5 as [teinits [ttrs [teouts ?]]]; dest.
  right; eauto 7.
Qed.

Corollary extAtomic_multi_IntMsgsEmpty_non_inits_InMPI:
  forall {oifc} (sys: System oifc) st1,
    Reachable (steps step_m) sys st1 ->
    IntMsgsEmpty sys st1.(bst_msgs) ->
    forall trss st2,
      steps step_m sys st1 (List.concat trss) st2 ->
      Forall (AtomicEx msg_dec) trss ->
      Forall (Transactional sys msg_dec) trss ->
      forall idm,
        In (idOf idm) (sys_minds sys) ->
        InMPI st2.(bst_msgs) idm ->
        exists einits trs eouts,
          In trs trss /\
          ExtAtomic sys msg_dec einits trs eouts /\
          In idm eouts.
Proof.
  intros.
  eapply extAtomic_multi_non_inits_InMPI_or in H1; try eassumption.
  - destruct H1; [|assumption].
    exfalso.
    specialize (H0 _ H4).
    apply findQ_length_ge_one in H1.
    rewrite H0 in H1; simpl in H1; omega.
  - eapply DisjList_In_2.
    + eapply sys_minds_sys_merqs_DisjList.
    + assumption.
Qed.

Section NonMergeable.
  Context {oifc: OStateIfc}.
  Variables (dtr: DTree)
            (sys: System oifc).
  Hypothesis (Hrrs: RqRsSys dtr sys)
             (Hiorqs: GoodORqsInit (initsOf sys)).

  Lemma extAtomic_IntMsgsEmpty_next_ins:
    forall st1,
      Reachable (steps step_m) sys st1 ->
      IntMsgsEmpty sys st1.(bst_msgs) ->
      forall trss st2,
        steps step_m sys st1 (List.concat trss) st2 ->
        Forall (AtomicEx msg_dec) trss ->
        Forall (Transactional sys msg_dec) trss ->
        forall oidx ridx rins routs st3,
          step_m sys st2 (RlblInt oidx ridx rins routs) st3 ->
          exists einits trs eouts,
            In trs trss /\
            ExtAtomic sys msg_dec einits trs eouts /\
            SubList rins eouts.
  Proof.
    intros.
    pose proof H4.
    eapply messages_in_cases in H5;
      try apply Hiorqs; try apply Hrrs;
        [|eapply reachable_steps; eassumption].
    assert (Forall (InMPI st2.(bst_msgs)) rins /\
            SubList (idsOf rins) (sys_minds sys)).
    { inv_step.
      split.
      { apply FirstMPI_Forall_InMP; assumption. }
      { destruct H16.
        admit.
      }
    }
    clear H4. (* clear [step_m] *)

    (* destruct H5 as [|[|[|]]]. *)
    (* - disc_messages_in. *)
    
  Admitted.

  Theorem rqrs_NonMergeable:
    RqRsSys dtr sys -> NonMergeable sys.
  Proof.
    intros.
    red; intros.
    eapply steps_split in H2; [|reflexivity].
    destruct H2 as [stt [? ?]].

    inv H5.
    pose proof H8.
    apply atomic_beginning_label in H5.
    destruct H5 as [ttrs [oidx [ridx [routs ?]]]]; subst.
    eapply steps_split in H6; [|reflexivity].
    destruct H6 as [sti [? ?]].
    inv_steps.

    eapply extAtomic_IntMsgsEmpty_next_ins in H14; eauto.
    destruct H14 as [pinits [ptrs [peouts ?]]]; dest.

    apply in_split in H5.
    destruct H5 as [hsts2 [hsts1 ?]]; subst.

    exists ptrs; eexists.
    exists hsts1, hsts2, nil; simpl.
    repeat ssplit.
    - reflexivity.
    - red; eauto 10.
    - apply Forall_forall.
      intros hst ?.
      eapply extAtomic_Discontinuous
        with (trss:= hsts2 ++ ptrs :: hsts1); try eassumption.
      + apply in_or_app; right.
        left; reflexivity.
      + apply in_or_app; left; assumption.
  Qed.

End NonMergeable.

Corollary rqrs_Serializable:
  forall {oifc} (sys: System oifc) (Hiorqs: GoodORqsInit (initsOf sys))
         (dtr: DTree),
    RqRsSys dtr sys ->
    SerializableSys sys.
Proof.
  intros.
  apply well_interleaved_serializable.
  - eapply rqrs_NonMergeable; eauto.
  - eapply rqrs_WellInterleaved; eauto.
Qed.

Close Scope list.
Close Scope fmap.

