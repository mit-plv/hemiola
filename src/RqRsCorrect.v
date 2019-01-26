Require Import Peano_dec Omega List ListSupport.
Require Import Common FMap.
Require Import Syntax Semantics SemFacts StepM Invariant.
Require Import Serial SerialFacts.
Require Import Reduction Commutativity QuasiSeq Topology.
Require Import RqRsTopo RqRsFacts.
Require Import RqRsInvMsg RqRsInvLock RqRsInvAtomic.
Require Import RqUpRed.

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
  Hypothesis (Hcont: ValidExtContinuousL
                       sys phst (RlblInt oidx ridx rins routs)).

  Local Definition nlbl := (RlblInt oidx ridx rins routs).

  Section RqUp.
    Hypothesis (Hru: RqUpMsgs dtr oidx rins).

    Definition RqUpLPush (hst: MHistory): Prop :=
      True. (* always left-pushable *)

    Definition RqUpRPush (hst: MHistory): Prop :=
      False. (* no right-pushable histories *)

    Lemma rqUp_lpush_or_rpush:
      forall st1,
        Reachable (steps step_m) sys st1 ->
        forall hsts st2,
          Forall (AtomicEx msg_dec) hsts ->
          steps step_m sys st1 (nlbl :: List.concat hsts ++ phst) st2 ->
          Forall (fun hst => Discontinuous phst hst) hsts ->
          Forall (fun hst => RqUpLPush hst \/ RqUpRPush hst) hsts.
    Proof.
      intros; clear.
      apply Forall_forall; intros.
      left; red; auto.
    Qed.
    
    Lemma rqUp_lpush_unit_ok:
      forall hst,
        AtomicEx msg_dec hst ->
        Discontinuous phst hst ->
        Reducible sys (hst ++ phst) (phst ++ hst).
    Proof.
      intros.
      destruct H as [inits [ins [outs [eouts ?]]]].
      destruct Hcont; clear H2.
      destruct H1 as [peouts [oidx' [ridx' [rins' [routs' ?]]]]]; dest.
      apply eq_sym in H2; inv H2.
      destruct H1 as [pinits pins phst pouts peouts].
      red in H0; dest.
      pose proof (atomic_unique H0 H2); dest; subst.
      pose proof (atomic_unique H5 H); dest; subst.
      eapply rqUp_lpush_unit_ok_ind; eauto.
      apply DisjList_comm; assumption.
    Qed.
    
    Lemma rqUp_lpush_ok:
      forall st1,
        Reachable (steps step_m) sys st1 ->
        forall hsts st2,
          Forall (AtomicEx msg_dec) hsts ->
          steps step_m sys st1 (nlbl :: List.concat hsts ++ phst) st2 ->
          Forall (fun hst => Discontinuous phst hst) hsts ->
          Forall (fun hst =>
                    RqUpLPush hst ->
                    Reducible sys (hst ++ phst) (phst ++ hst)) hsts.
    Proof.
      intros.
      inv H1; clear H8.
      generalize dependent st3.
      induction hsts; simpl; intros; [constructor|].

      inv H0; inv H2.
      rewrite <-app_assoc in H6.
      eapply steps_split in H6; [|reflexivity].
      destruct H6 as [sti [? ?]].

      constructor; eauto.
      intros; eapply rqUp_lpush_unit_ok; eauto.
    Qed.

    Lemma rqUp_rpush_ok:
      forall st1,
        Reachable (steps step_m) sys st1 ->
        forall hsts st2,
          Forall (AtomicEx msg_dec) hsts ->
          steps step_m sys st1 (nlbl :: List.concat hsts ++ phst) st2 ->
          Forall (fun hst => Discontinuous phst hst) hsts ->
          Forall (fun hst =>
                    RqUpRPush hst ->
                    Reducible sys (nlbl :: hst) (hst ++ [nlbl])) hsts.
    Proof.
      intros; clear.
      apply Forall_forall; intros.
      red in H0; elim H0.
    Qed.

    Lemma rqUp_LRPushable:
      forall st1,
        Reachable (steps step_m) sys st1 ->
        forall hsts st2,
          Forall (AtomicEx msg_dec) hsts ->
          steps step_m sys st1 (nlbl :: List.concat hsts ++ phst) st2 ->
          Forall (fun hst => Discontinuous phst hst) hsts ->
          LRPushable sys RqUpLPush RqUpRPush hsts.
    Proof.
      intros; red; intros; subst.
      red in H5; elim H5.
    Qed.

  End RqUp.

  Section RsUp.
    Hypothesis (Hru: RsUpMsgs dtr oidx rins).

    Definition RsUpLPush (hst: MHistory): Prop :=
      False. (* no left-pushable histories *)

    Definition RsUpRPush (hst: MHistory): Prop :=
      True. (* always right-pushable *)

    Lemma rsUp_lpush_or_rpush:
      forall st1,
        Reachable (steps step_m) sys st1 ->
        forall hsts st2,
          Forall (AtomicEx msg_dec) hsts ->
          steps step_m sys st1 (nlbl :: List.concat hsts ++ phst) st2 ->
          Forall (fun hst => Discontinuous phst hst) hsts ->
          Forall (fun hst => RsUpLPush hst \/ RsUpRPush hst) hsts.
    Proof.
      intros; clear.
      apply Forall_forall; intros.
      right; red; auto.
    Qed.

    Lemma rsUp_lpush_ok:
      forall st1,
        Reachable (steps step_m) sys st1 ->
        forall hsts st2,
          Forall (AtomicEx msg_dec) hsts ->
          steps step_m sys st1 (nlbl :: List.concat hsts ++ phst) st2 ->
          Forall (fun hst => Discontinuous phst hst) hsts ->
          Forall (fun hst =>
                    RsUpLPush hst ->
                    Reducible sys (hst ++ phst) (phst ++ hst)) hsts.
    Proof.
      intros; clear.
      apply Forall_forall; intros.
      red in H0; elim H0.
    Qed.

    Lemma rsUp_rpush_ok:
      forall st1,
        Reachable (steps step_m) sys st1 ->
        forall hsts st2,
          Forall (AtomicEx msg_dec) hsts ->
          steps step_m sys st1 (nlbl :: List.concat hsts ++ phst) st2 ->
          Forall (fun hst => Discontinuous phst hst) hsts ->
          Forall (fun hst =>
                    RsUpRPush hst ->
                    Reducible sys (nlbl :: hst) (hst ++ [nlbl])) hsts.
    Proof.
    Admitted.

    Lemma rsUp_LRPushable:
      forall st1,
        Reachable (steps step_m) sys st1 ->
        forall hsts st2,
          Forall (AtomicEx msg_dec) hsts ->
          steps step_m sys st1 (nlbl :: List.concat hsts ++ phst) st2 ->
          Forall (fun hst => Discontinuous phst hst) hsts ->
          LRPushable sys RsUpLPush RsUpRPush hsts.
    Proof.
      intros; red; intros; subst.
      red in H4; elim H4.
    Qed.
    
  End RsUp.

End Pushable.

Theorem rqrs_pushable:
  forall {oifc} (sys: System oifc) (dtr: DTree),
    RqRsSys dtr sys ->
    Pushable sys.
Proof.
  intros; red; intros.

  assert (exists oidx ridx rins routs,
             l2 = RlblInt oidx ridx rins routs /\
             (RqUpMsgs dtr oidx rins \/
              RqDownMsgs dtr oidx rins \/
              RsUpMsgs dtr oidx rins \/
              RsDownMsgs dtr oidx rins)) as Hnlbl.
  { inv H0; inv H1.
    destruct H0 as [oidx [ridx [rins [routs ?]]]]; dest; subst.
    do 4 eexists; split; auto.
    destruct H as [? [? ?]].
    inv H5.
    eapply messages_in_cases.
    { eassumption. }
    { eapply reachable_steps; eassumption. }
    { eassumption. }
  }
  destruct Hnlbl as [oidx [ridx [rins [routs ?]]]]; dest; subst.

  destruct H2 as [|[|[|]]].

  - exists RqUpLPush, RqUpRPush.
    repeat split.
    + eauto using rqUp_lpush_or_rpush.
    + eauto using rqUp_lpush_ok.
    + eauto using rqUp_rpush_ok.
    + eauto using rqUp_LRPushable.

  - admit.

  - exists RsUpLPush, RsUpRPush.
    repeat split.
    + eauto using rsUp_lpush_or_rpush.
    + eauto using rsUp_lpush_ok.
    + eauto using rsUp_rpush_ok.
    + eauto using rsUp_LRPushable.

  - admit.
      
Admitted.

Corollary rqrs_serializable:
  forall {oifc} (sys: System oifc) (dtr: DTree),
    RqRsSys dtr sys ->
    SerializableSys sys.
Proof.
  intros.
  apply well_interleaved_serializable.
  apply well_interleaved_push_ok.
  eapply rqrs_pushable; eauto.
Qed.

Close Scope list.
Close Scope fmap.

