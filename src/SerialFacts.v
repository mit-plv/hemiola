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
    forall sys, Sequential (MsgT:= MsgT) sys nil.
  Proof.
    intros; hnf; intros.
    exists nil.
    split.
    - constructor.
    - reflexivity.
  Qed.

  Lemma sequential_silent:
    forall sys ll,
      Sequential (MsgT:= MsgT) sys ll ->
      Sequential (MsgT:= MsgT) sys (RlblEmpty _ :: ll).
  Proof.
    intros.
    hnf; hnf in H; dest.
    eexists ([RlblEmpty _] :: _); split.
    - constructor; [|eassumption].
      constructor.
    - subst; reflexivity.
  Qed.

  Lemma sequential_msg_ins:
    forall sys ll eins,
      Sequential (MsgT:= MsgT) sys ll ->
      Sequential (MsgT:= MsgT) sys (RlblIns eins :: ll).
  Proof.
    intros.
    hnf; hnf in H; dest.
    eexists ([RlblIns eins] :: _); split.
    - constructor; [|eassumption].
      eapply TrsIns; reflexivity.
    - subst; reflexivity.
  Qed.

  Lemma sequential_msg_outs:
    forall sys ll eouts,
      Sequential (MsgT:= MsgT) sys ll ->
      Sequential (MsgT:= MsgT) sys (RlblOuts eouts :: ll).
  Proof.
    intros.
    hnf; hnf in H; dest.
    eexists ([RlblOuts eouts] :: _); split.
    - constructor; [|eassumption].
      eapply TrsOuts; reflexivity.
    - subst; reflexivity.
  Qed.

  Lemma sequential_app:
    forall sys ll1 ll2,
      Sequential (MsgT:= MsgT) sys ll1 ->
      Sequential (MsgT:= MsgT) sys ll2 ->
      Sequential (MsgT:= MsgT) sys (ll1 ++ ll2).
  Proof.
    unfold Sequential; intros.
    destruct H as [trss1 [? ?]].
    destruct H0 as [trss2 [? ?]]; subst.
    exists (trss1 ++ trss2); split.
    - apply Forall_app; auto.
    - apply eq_sym, concat_app.
  Qed.

  Lemma atomic_singleton:
    forall rqr rqs houts,
      Atomic rqs [RlblInt rqr rqs houts] (enqMsgs houts (emptyMP MsgT)).
  Proof.
    intros; constructor.
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
    + apply sequential_nil.
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
  - destruct H; split.
    + eapply StepsCons.
      * eassumption.
      * eapply SmSlt.
    + apply sequential_silent; auto.
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
  - destruct H; split.
    + econstructor.
      * eassumption.
      * econstructor; eauto.
    + apply sequential_msg_ins; auto.
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

