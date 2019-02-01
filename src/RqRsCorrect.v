Require Import Peano_dec Omega List ListSupport.
Require Import Common FMap.
Require Import Syntax Semantics SemFacts StepM Invariant.
Require Import Serial SerialFacts.
Require Import Reduction Commutativity QuasiSeq Topology.
Require Import RqRsTopo RqRsFacts.
Require Import RqRsInvMsg RqRsInvLock RqRsInvAtomic.
Require Import RqUpRed RsUpRed.

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

    Lemma rqUp_LPushable_unit:
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
      eapply rqUp_lpush_unit_ok_ind; eauto.
      apply DisjList_comm; assumption.
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
      intros; eapply rqUp_LPushable_unit; eauto.
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

    Lemma rsUp_rpush_unit_ok:
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
      eapply rsUp_rpush_unit_ok_ind; eauto.
      eapply DisjList_SubList.
      - eassumption.
      - apply DisjList_comm; assumption.
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
      - eapply DisjList_comm, DisjList_SubList; [eassumption|].
        apply DisjList_comm; assumption.
    Qed.
    
    Lemma rsUp_RPushableP:
      RPushableP sys RsUpP phst nlbl.
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
      - intros; eapply rsUp_rpush_unit_ok; eauto.
    Qed.

  End RsUp.

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
              RqDownMsgs dtr oidx rins \/
              RsUpMsgs dtr oidx rins \/
              RsDownMsgs dtr oidx rins)) as Hnlbl.
  { destruct H as [? [? ?]].
    red in H0.
    destruct H0 as [eouts [oidx [ridx [rins [routs ?]]]]]; dest; subst.
    inv H2.
    eapply messages_in_cases in H14; eauto.
    eauto 6.
  }
  destruct Hnlbl as [oidx [ridx [rins [routs ?]]]]; dest; subst.

  destruct H6 as [|[|[|]]].
  - apply LPushableHst_WellInterleavedHst; auto.
    eauto using rqUp_LPushableHst.
  - admit.
  - apply RPushableP_WellInterleavedHst with (P:= RsUpP rins); auto.
    + eauto using rsUp_PInitializing.
    + eauto using rsUp_RPushableP.
  - admit.
Admitted.

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

