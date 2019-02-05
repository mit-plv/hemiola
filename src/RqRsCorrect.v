Require Import Peano_dec Omega List ListSupport.
Require Import Common FMap.
Require Import Syntax Semantics SemFacts StepM Invariant.
Require Import Serial SerialFacts.
Require Import Reduction Commutativity QuasiSeq Topology.
Require Import RqRsTopo RqRsFacts.
Require Import RqRsInvMsg RqRsInvLock RqRsInvAtomic.
Require Import RqRsRed RqUpRed RsUpRed RqDownRed.

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
      - intros; eapply rsUp_rpush_unit_ok; eauto.
    Qed.

  End RsUp.

  (** Generally we need to prove:
   * a) [oinds(hst1) -*- oinds(hst2) -> Reducible (hst2 ++ hst1) (hst1 ++ hst2)]
   *
   ** Proof sketch for the reducibility of downward-request labels:
   * 1) [phst] ⊆ tr(nlbl)^{-1}
   * 2) Let [olast(hst)] be the last object index of an [Atomic] history [hst].
   * 2-1) [olast(hst) ∈ tr(nlbl) -> oinds(hst) ⊆ tr(nlbl)]
   * 2-2) [olast(hst) ∈ tr(nlbl)^{-1} -> 
   *       exists preh posth, 
   *         hst = posth ++ preh /\
   *         ("preh" just consists of RqUp labels) /\
   *         oinds(posth) ⊆ tr(nlbl)^{-1}]
   * 3) Now define [LPush] and [RPush] as follows:
   *    [LPush hst ≜ olast(hst) ∈ tr(nlbl)]
   *    [RPush hst ≜ olast(hst) ∈ tr(nlbl)^{-1}]
   * 4) To check each condition in [PushableHst]:
   * 4-1) Left-or-right: [olast(hst)] is a single object index, 
   *      thus [in_dec eq_nat_dec olast(hst) tr(nlbl)] provides enough
   *      information.
   * 4-2) Left-push-reducibility: if [hst] is left-pushable, then by 2-1) and 3)
   *      we get [oinds(hst) ⊆ tr(nlbl)]. Now by 1) and a) we exactly get the
   *      reducibility.
   * 4-3) Right-push-reducibility: if [hst] is right-pushable, then by 2-2) 
   *      and 3) we have [preh] and [posth] that satisfy the conditions in 2-2).
   * 4-3-1) [preh] and [nlbl] are commutative since [preh] only consists of 
   *        RqUp labels.
   * 4-3-2) [posth] and [nlbl] are commutative by applying a).
   * 4-4) [LRPushable]: if [RPush hst1 /\ LPush hst2], then by 2-1), 2-2), 
   *      and 3) for [hst1] we have [preh1] and [posth1] that satisfy the
   *      conditions in 2-2). Now reasoning very similarly to 4-2) and 4-3):
   * 4-4-1) [preh1] and [hst2] are commutative since [preh1] only consists of
   *        RqUp labels.
   * 4-4-2) [posth1] and [hst2] are commutative by applying a).
   *
   ** Proof sketch for the reducibility of downward-response labels:
   * 1) [exists preh posth, 
   *       phst = posth ++ preh /\
   *       ("preh" just consists of RqUp labels) /\
   *       oinds(posth) ⊆ tr(nlbl)^{-1}]
   * 2) Let [olast(hst)] be the last object index of an [Atomic] history [hst].
   * 2-1) [olast(hst) ∈ tr(nlbl) -> oinds(hst) ⊆ tr(nlbl)]
   * 2-2) [olast(hst) ∈ tr(nlbl)^{-1} -> oinds(hst) ⊆ tr(nlbl)^{-1}]
   *      This part differs from the one for downward-requests since both upward
   *      requests and upward responses cannot happen when a downward-response label is
   *      in the message pool.
   * 3) Define [LPush] and [RPush] as follows:
   *    [LPush hst ≜ olast(hst) ∈ tr(nlbl)]
   *    [RPush hst ≜ olast(hst) ∈ tr(nlbl)^{-1}]
   * 4) Conditions of [PushableHst] are easier to prove, mostly by a).
   *)

  Section RqDown.
    Hypothesis (Hrd: RqDownMsgs dtr oidx rins).

    Definition RqDownP (st: MState oifc) :=
      Forall (InMPI st.(bst_msgs)) rins.
    
    Definition RqDownLPush (hst: MHistory) :=
      exists loidx,
        lastOIdxOf hst = Some loidx /\
        In loidx (subtreeIndsOf dtr oidx).

    Definition RqDownRPush (hst: MHistory) :=
      exists loidx,
        lastOIdxOf hst = Some loidx /\
        ~ In loidx (subtreeIndsOf dtr oidx).

    Lemma rqDown_PInitializing:
      PInitializing sys RqDownP phst.
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
      - eapply DisjList_comm, DisjList_SubList; [eassumption|].
        apply DisjList_comm; assumption.
    Qed.

    Lemma rqDown_PPreserving:
      forall st1,
        Reachable (steps step_m) sys st1 ->
        forall hsts st2,
          Forall (AtomicEx msg_dec) hsts ->
          steps step_m sys st1 (nlbl :: List.concat hsts ++ phst) st2 ->
          Forall (fun hst => Discontinuous phst hst) hsts ->
          Forall (PPreserving sys RqDownP) hsts.
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
    Admitted.

    Lemma rqDown_rpush_reducible:
      forall st1,
        Reachable (steps step_m) sys st1 ->
        forall hsts st2,
          Forall (AtomicEx msg_dec) hsts ->
          steps step_m sys st1 (nlbl :: List.concat hsts ++ phst) st2 ->
          Forall (fun hst => Discontinuous phst hst) hsts ->
          Forall (fun hst => RqDownRPush hst ->
                             ReducibleP sys RqDownP (nlbl :: hst) (hst ++ [nlbl])) hsts.
    Proof.
    Admitted.

    Lemma rqDown_LRPushable:
      forall st1,
        Reachable (steps step_m) sys st1 ->
        forall hsts st2,
          Forall (AtomicEx msg_dec) hsts ->
          steps step_m sys st1 (nlbl :: List.concat hsts ++ phst) st2 ->
          Forall (fun hst => Discontinuous phst hst) hsts ->
          LRPushable sys RqDownP RqDownLPush RqDownRPush hsts.
    Proof.
    Admitted.
    
  End RqDown.
  
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
  - apply PushableHst_WellInterleavedHst with (P:= RqDownP rins); auto.
    + eauto using rqDown_PInitializing.
    + exists (RqDownLPush dtr oidx), (RqDownRPush dtr oidx).
      intros; repeat split.
      * eauto using rqDown_PPreserving.
      * eauto using rqDown_lpush_or_rpush.
      * eauto using rqDown_lpush_reducible.
      * eauto using rqDown_rpush_reducible.
      * eauto using rqDown_LRPushable.
  - apply RPushableHst_WellInterleavedHst with (P:= RsUpP rins); auto.
    + eauto using rsUp_PInitializing.
    + eauto using rsUp_RPushableHst.
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

