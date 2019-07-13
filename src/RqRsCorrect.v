Require Import Peano_dec Omega List ListSupport.
Require Import Common FMap.
Require Import Syntax Semantics SemFacts StepM Invariant.
Require Import Serial SerialFacts.
Require Import Reduction Commutativity QuasiSeq Topology.
Require Import RqRsTopo RqRsFacts.
Require Import RqRsInvMsg RqRsInvLock RqRsInvAtomic RqRsInvSep.

(* Required to prove serializability *)
Require Import RqRsRed RqUpRed RsUpRed RqDownRed RsDownRed.
(* Required to prove nonmergeability *)
Require Import RqRsInvLockEx.

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

Section NonMergeable.
  Context {oifc: OStateIfc}.
  Variables (dtr: DTree)
            (sys: System oifc).
  Hypothesis (Hrrs: RqRsSys dtr sys)
             (Hiorqs: GoodORqsInit (initsOf sys)).

  Lemma rqrs_step_ins_or:
    forall st1,
      Reachable (steps step_m) sys st1 ->
      forall oidx ridx rins routs st2,
        step_m sys st1 (RlblInt oidx ridx rins routs) st2 ->
        SubList (idsOf rins) (sys_merqs sys) \/
        SubList (idsOf rins) (sys_minds sys).
  Proof.
    intros.
    pose proof H0.
    eapply messages_in_cases in H1;
      try apply Hiorqs; try apply Hrrs; [|assumption].
    destruct H1 as [|[|[|]]]; disc_messages_in.
    - inv_step.
      destruct H14; simpl in *.
      apply SubList_singleton_In in H0.
      apply in_app_or in H0.
      destruct H0.
      + right; apply SubList_cons; [assumption|apply SubList_nil].
      + left; apply SubList_cons; [assumption|apply SubList_nil].
    - inv_step.
      destruct H14; simpl in *.
      apply SubList_singleton_In in H0.
      apply in_app_or in H0.
      destruct H0.
      + right; apply SubList_cons; [assumption|apply SubList_nil].
      + left; apply SubList_cons; [assumption|apply SubList_nil].
    - inv_step.
      destruct H13.
      right.
      red; intros midx ?.
      rewrite Forall_forall in H2; specialize (H2 _ H4).
      destruct H2 as [cidx [? ?]].
      apply H0 in H4.
      apply in_app_or in H4; destruct H4; [assumption|].
      exfalso.
      apply Hrrs in H4.
      destruct H4 as [eoidx ?].
      eapply rqrsDTree_rqUp_rsUp_not_eq in H4; [|apply Hrrs|eassumption].
      auto.
    - inv_step.
      destruct H14; simpl in *.
      apply SubList_singleton_In in H0.
      apply in_app_or in H0.
      destruct H0.
      + right; apply SubList_cons; [assumption|apply SubList_nil].
      + left; apply SubList_cons; [assumption|apply SubList_nil].
  Qed.

  Lemma extAtomic_IntMsgsEmpty_next_ins:
    forall st1,
      Reachable (steps step_m) sys st1 ->
      IntMsgsEmpty sys st1.(bst_msgs) ->
      forall trss st2,
        steps step_m sys st1 (List.concat trss) st2 ->
        Forall (AtomicEx msg_dec) trss ->
        Forall (Transactional sys msg_dec) trss ->
        forall oidx ridx rins routs st3,
          ~ SubList (idsOf rins) (sys_merqs sys) ->
          step_m sys st2 (RlblInt oidx ridx rins routs) st3 ->
          exists einits trs eouts,
            In trs trss /\
            ExtAtomic sys msg_dec einits trs eouts /\
            SubList rins eouts.
  Proof.
    intros.
    pose proof H5.
    eapply messages_in_cases in H6;
      try apply Hiorqs; try apply Hrrs;
        [|eapply reachable_steps; eassumption].
    assert (Forall (InMPI st2.(bst_msgs)) rins /\
            SubList (idsOf rins) (sys_minds sys)).
    { pose proof H5.
      apply rqrs_step_ins_or in H7; [|eapply reachable_steps; eassumption].
      inv_step.
      split.
      { apply FirstMPI_Forall_InMP; assumption. }
      { destruct H7; [exfalso; auto|auto]. }
    }
    clear H5; dest. (* clear [step_m] *)

    destruct H6 as [|[|[|]]]; disc_messages_in.
    - apply SubList_singleton_In in H7.
      inv H5; clear H13.
      eapply extAtomic_multi_IntMsgsEmpty_non_inits_InMPI in H12;
        try eassumption.
      destruct H12 as [einits [trs [eouts ?]]]; dest.
      exists einits, trs, eouts.
      repeat ssplit; [assumption..|].
      apply SubList_cons; [assumption|apply SubList_nil].

    - apply SubList_singleton_In in H7.
      inv H5; clear H13.
      eapply extAtomic_multi_IntMsgsEmpty_non_inits_InMPI in H12;
        try eassumption.
      destruct H12 as [einits [trs [eouts ?]]]; dest.
      exists einits, trs, eouts.
      repeat ssplit; [assumption..|].
      apply SubList_cons; [assumption|apply SubList_nil].

    - (* Pick a single [RsUp] message to get the previous transaction. *)
      destruct rins as [|[rsUp1 rsm1] rins];
        [exfalso; elim H4; apply SubList_nil|].
      simpl in *.
      apply SubList_cons_inv in H7; dest.
      inv H5; inv H6; inv H8.
      destruct H10 as [cidx1 [? ?]]; simpl in *.

      eapply extAtomic_multi_IntMsgsEmpty_non_inits_InMPI in H12;
        try eassumption.
      destruct H12 as [einits1 [trs1 [eouts1 ?]]]; dest.
      exists einits1, trs1, eouts1.

      (* Now prove all the other [RsUp] messages are from
       * this transaction as well. *)
      repeat ssplit; try assumption.
      red. intros [rsUp2 rsm2] ?.
      inv H16; [inv H17; assumption|].

      rewrite Forall_forall in H13, H14, H15.
      specialize (H13 _ H17).
      specialize (H14 _ H17).
      apply in_map with (f:= idOf) in H17.
      specialize (H15 _ H17).
      destruct H15 as [cidx2 [? ?]].
      simpl in *.
      eapply extAtomic_multi_IntMsgsEmpty_non_inits_InMPI in H13;
        try eassumption; [|apply H9 in H17; assumption].
      destruct H13 as [einits2 [trs2 [eouts2 ?]]]; dest.

      (* Prove two different [RsUp] messages are from the same transaction,
       * by deriving a contradiction; if [trs1 <> trs2] then ..
       *)
      apply In_nth_error in H8; destruct H8 as [n1 ?].
      apply In_nth_error in H13; destruct H13 as [n2 ?].
      destruct (eq_nat_dec n1 n2).
      + subst; rewrite H8 in H13; inv H13.
        pose proof (extAtomic_unique H10 H18); dest; subst.
        assumption.
      + exfalso.
        eapply extAtomic_multi_rsUps_not_diverged
          with (n3:= n1) (n4:= n2) (rsUp1:= (rsUp1, rsm1)) (rsUp2:= (rsUp2, rsm2))
               (cidx1:= cidx1) (cidx2:= cidx2); eauto.
        * assumption.
        * red; auto.
        * red; auto.
      
    - apply SubList_singleton_In in H7.
      inv H5; clear H13.
      eapply extAtomic_multi_IntMsgsEmpty_non_inits_InMPI in H12;
        try eassumption.
      destruct H12 as [einits [trs [eouts ?]]]; dest.
      exists einits, trs, eouts.
      repeat ssplit; [assumption..|].
      apply SubList_cons; [assumption|apply SubList_nil].
  Qed.

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

