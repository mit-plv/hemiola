Require Import Bool List String Peano_dec.
Require Import Common ListSupport FMap.
Require Import Syntax Semantics SemFacts StepM Serial Invariant.

Require Import Omega.
Require Import Program.Equality.

Set Implicit Arguments.

Section MsgParam.
  Variable MsgT: Type.

  Lemma atomic_emptyILabel_not_in:
    forall rq hst mouts,
      Atomic rq hst mouts ->
      ~ In (RlblEmpty MsgT) hst.
  Proof.
    induction 1; simpl; intros.
    - intro Hx; destruct Hx; [discriminate|auto].
    - intro Hx; destruct Hx; auto.
      inv H2; elim H0; reflexivity.
  Qed.

  Lemma atomic_iLblIn_not_in:
    forall rq hst mouts,
      Atomic rq hst mouts ->
      forall msg: Id MsgT,
        ~ In (RlblIns [msg]) hst.
  Proof.
    induction 1; simpl; intros; [auto|];
      try (intro Hx; destruct Hx;
           [discriminate|firstorder]).
  Qed.

  Lemma atomic_ins_outs_unique:
    forall (hst: History MsgT) ins1 outs1,
      Atomic ins1 hst outs1 ->
      forall ins2 outs2,
        Atomic ins2 hst outs2 ->
        ins1 = ins2 /\ outs1 = outs2.
  Proof.
    induction 1; simpl; intros.
    - inv H; [auto|inv H6].
    - inv H2; [inv H|].
      specialize (IHAtomic _ _ H9); dest; subst; auto.
  Qed.

  Lemma atomic_app:
    forall (hst1: History MsgT) ins1 outs1,
      Atomic ins1 hst1 outs1 ->
      forall hst2 ins2 outs2,
        ins2 <> nil ->
        Atomic ins2 hst2 outs2 ->
        Forall (InMPI outs1) ins2 ->
        exists mouts,
          Atomic ins1 (hst2 ++ hst1) mouts /\
          (forall msgs, Forall (InMPI outs2) msgs -> Forall (InMPI mouts) msgs).
  Proof.
    induction 3; simpl; intros.
    - eexists; split.
      + econstructor; eauto.
      + intros.
        admit.
    - specialize (IHAtomic H0 H4).
      destruct IHAtomic as [mouts1 [? ?]].
      eexists; split.
      + econstructor; eauto.
      + intros.
        admit.
  Admitted.

  Lemma extAtomic_preserved:
    forall impl1 (rq: Id MsgT) hst mouts,
      ExtAtomic impl1 rq hst mouts ->
      forall impl2,
        merqsOf impl1 = merqsOf impl2 ->
        ExtAtomic impl2 rq hst mouts.
  Proof.
    intros.
    inv H; constructor; auto.
    rewrite <-H0; assumption.
  Qed.

  Lemma sequential_nil:
    forall sys, Sequential (MsgT:= MsgT) sys nil nil.
  Proof.
    intros; hnf; intros.
    split.
    - constructor.
    - reflexivity.
  Qed.

  Lemma sequential_silent:
    forall sys ll trss,
      Sequential (MsgT:= MsgT) sys ll trss ->
      Sequential (MsgT:= MsgT) sys (RlblEmpty _ :: ll) ([RlblEmpty _] :: trss).
  Proof.
    intros.
    hnf; hnf in H; dest.
    split.
    - constructor; [|eassumption].
      constructor.
    - subst; reflexivity.
  Qed.

  Lemma sequential_msg_ins:
    forall sys ll trss eins,
      Sequential (MsgT:= MsgT) sys ll trss ->
      Sequential (MsgT:= MsgT) sys (RlblIns eins :: ll) ([RlblIns eins] :: trss).
  Proof.
    intros.
    hnf; hnf in H; dest.
    split.
    - constructor; [|eassumption].
      eapply TrsIns; reflexivity.
    - subst; reflexivity.
  Qed.

  Lemma sequential_msg_outs:
    forall sys ll trss eouts,
      Sequential (MsgT:= MsgT) sys ll trss ->
      Sequential (MsgT:= MsgT) sys (RlblOuts eouts :: ll) ([RlblOuts eouts] :: trss).
  Proof.
    intros.
    hnf; hnf in H; dest.
    split.
    - constructor; [|eassumption].
      eapply TrsOuts; reflexivity.
    - subst; reflexivity.
  Qed.

  Lemma sequential_app:
    forall sys ll1 trss1 ll2 trss2,
      Sequential (MsgT:= MsgT) sys ll1 trss1 ->
      Sequential (MsgT:= MsgT) sys ll2 trss2 ->
      Sequential (MsgT:= MsgT) sys (ll1 ++ ll2) (trss1 ++ trss2).
  Proof.
    unfold Sequential; intros.
    destruct H, H0; subst.
    split.
    - apply Forall_app; auto.
    - apply eq_sym, concat_app.
  Qed.

  Lemma atomic_singleton:
    forall rqr rqs houts,
      Atomic rqs [RlblInt rqr rqs houts] (enqMsgs houts (emptyMP MsgT)).
  Proof.
    intros; constructor.
  Qed.

  Lemma sequential_serializable:
    forall sys hst trss st,
      steps step_m sys (initsOf sys) hst st ->
      Sequential sys hst trss ->
      Serializable sys hst.
  Proof.
    intros; red; intros.
    do 2 eexists; split.
    - split; eauto.
    - congruence.
  Qed.

  Lemma stransactional_default:
    forall lbl,
    exists tty ins outs,
      STransactional (MsgT:= MsgT) tty ins [lbl] outs.
  Proof.
    destruct lbl; intros; do 3 eexists.
    - eapply STrsSlt.
    - eapply STrsIns; eauto.
    - eapply STrsAtomic.
      eapply atomic_singleton.
    - eapply STrsOuts; eauto.
  Qed.

  Lemma stransactional_trsType_ins_outs_unique:
    forall (hst: History MsgT) tty1 ins1 outs1,
      STransactional tty1 ins1 hst outs1 ->
      forall tty2 ins2 outs2,
        STransactional tty2 ins2 hst outs2 ->
        tty1 = tty2 /\ ins1 = ins2 /\ outs1 = outs2.
  Proof.
    intros; inv H.
    - inv H0; auto; try discriminate.
      inv H.
    - inv H0; auto; try discriminate.
      + inv H3; auto.
      + inv H.
    - inv H0; auto; try discriminate.
      + inv H3; auto.
      + inv H.
    - inv H0; try (inv H1; fail).
      eapply atomic_ins_outs_unique in H; eauto.
  Qed.

  Lemma stransactional_cons_inv:
    forall tty ins lbl (hst: History MsgT) outs,
      STransactional tty ins (lbl :: hst) outs ->
      hst = nil \/
      exists pouts, STransactional tty ins hst pouts.
  Proof.
    intros.
    inv H; auto.
    inv H0; auto.
    right; eexists; econstructor; eauto.
  Qed.

  Lemma ssequential_default:
    forall hst, exists n, SSequential (MsgT:= MsgT) hst n.
  Proof.
    induction hst; simpl; intros; [repeat econstructor; eauto|].
    destruct IHhst as [n ?].
    destruct H; subst.
    exists (S (List.length trss)).
    econstructor.
    - instantiate (1:= [a] :: _); reflexivity.
    - reflexivity.
    - constructor; auto.
      apply stransactional_default.
  Qed.

End MsgParam.

Lemma bequivalent_refl:
  forall sys {LabelT} `{HasLabel LabelT} (hst: list LabelT),
    BEquivalent sys hst hst.
Proof.
  congruence.
Qed.

Lemma bequivalent_sym:
  forall sys {LabelT} `{HasLabel LabelT} (hst1 hst2: list LabelT),
    BEquivalent sys hst1 hst2 ->
    BEquivalent sys hst2 hst1.
Proof.
  congruence.
Qed.

Lemma bequivalent_trans:
  forall sys {LabelT} `{HasLabel LabelT} (hst1 hst2 hst3: list LabelT),
    BEquivalent sys hst1 hst2 ->
    BEquivalent sys hst2 hst3 ->
    BEquivalent sys hst1 hst3.
Proof.
  congruence.
Qed.

Theorem serializable_seqSteps_refines:
  forall sys,
    SerializableSys sys ->
    steps step_m # seqStepsM |-- sys ⊑ sys.
Proof.
  unfold SerializableSys, Refines; intros.
  inv H0; rename ll0 into ill.
  specialize (H _ _ H1).
  unfold Serializable in H.
  destruct H as [sll [sst [? ?]]].
  unfold MLabel; rewrite H0.
  econstructor; eauto.
Qed.

Lemma serializable_nil:
  forall sys, Serializable sys nil.
Proof.
  intros; hnf; intros.
  exists nil; eexists.
  split.
  - split.
    + constructor.
    + eexists; eapply sequential_nil.
  - reflexivity.
Qed.

Lemma serializable_silent:
  forall sys ll,
    Serializable sys ll ->
    Serializable sys (RlblEmpty _ :: ll).
Proof.
  intros.
  hnf; hnf in H; intros; dest.
  do 2 eexists; split.
  - destruct H; split; dest.
    + eapply StepsCons.
      * eassumption.
      * eapply SmSlt.
    + eexists; eapply sequential_silent; eauto.
  - assumption.
Qed.

Lemma serializable_msg_ins:
  forall sys ll eins,
    Serializable sys ll ->
    eins <> nil ->
    ValidMsgsExtIn sys eins ->
    Serializable sys (RlblIns eins :: ll).
Proof.
  intros.
  hnf; hnf in H; intros; dest.
  destruct x0 as [oss orqs msgs].
  exists (RlblIns eins :: x); eexists; split.
  - destruct H; split; dest.
    + econstructor.
      * eassumption.
      * econstructor; eauto.
    + eexists; eapply sequential_msg_ins; eauto.
  - hnf; cbn; rewrite H2; reflexivity.
Qed.

Lemma serializable_steps_no_rules:
  forall sys,
    sys_rules sys = nil ->
    forall st1,
      st1 = initsOf sys ->
      forall ll st2,
        steps step_m sys st1 ll st2 ->
        Serializable sys ll.
Proof.
  induction 3; simpl; intros.
  - apply serializable_nil.
  - specialize (IHsteps H0); subst.
    inv H2.
    + apply serializable_silent; auto.
    + apply serializable_msg_ins; auto.
    + exfalso.
      eapply behavior_no_rules_NoExtOuts in H1; eauto.
      red in H1; simpl in H1.
      destruct eouts as [|eout eouts]; auto.
      inv H3.
      destruct H4.
      simpl in H2; apply SubList_cons_inv in H2; dest.
      apply FirstMP_InMP in H6.
      eapply ForallMP_InMP in H1; eauto.
    + exfalso.
      rewrite H in H10.
      elim H10.
Qed.
                           
Lemma serializable_no_rules:
  forall sys,
    sys_rules sys = nil ->
    SerializableSys sys.
Proof.
  intros; hnf; intros.
  eapply serializable_steps_no_rules; eauto.
Qed.

